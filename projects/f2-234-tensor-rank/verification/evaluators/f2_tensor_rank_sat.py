#!/usr/bin/env python3
r"""Exact SAT encoding for binary matrix-multiplication tensor rank.

For ``rank`` nonzero terms ``u_s (x) v_s (x) w_s``, the encoder introduces
one conjunction variable per term/coefficient and a Tseitin XOR chain enforcing
that their parity equals the exact matrix-multiplication tensor.  A SAT model is
decoded and replayed through ``f2_234_tensor_rank_eval``; an UNSAT claim is
acceptable only with a checked DRAT/LRAT proof.

For the target F2 <2,3,4> rank-19 query, two symmetry branches are exhaustive:

* ``rank1-u0``: some 2x3 U factor has matrix rank one; tensor symmetry maps it
  to e_00 and term permutation places it first.
* ``all-u-rank2``: every nonzero 2x3 U factor has rank two; symmetry maps one to
  [I_2 | 0] and places it first.

The remaining terms are lexicographically sorted in each branch.  Thus the
union removes GL(2,2) x GL(3,2) and term-permutation symmetry without excluding
any rank-19 decomposition.

For a fixed U profile, right GL(4,2) has four orbits on a distinguished
nonzero 2-by-4 W factor.  In row-major masks their canonical representatives
are 1, 16, 17, and 33.  Solving all four fixed-W0 subcases is exhaustive;
fixing W0 to 1 alone is not.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import shutil
import subprocess
import sys
import tempfile
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from evaluators.f2_234_tensor_rank_eval import (  # noqa: E402
    SCHEMA as DECOMPOSITION_SCHEMA,
    TensorRankEvaluationError,
    strassen_rank_7,
    target_tensor,
    verify_rank_decomposition,
)

ENCODING_SCHEMA = "f2-tensor-rank-cnf-v1"
TARGET_SHAPE = (2, 3, 4)
TARGET_FORMAT = "2x3-by-3x4"
PROOF_CHECKERS = ROOT / "tmp" / "upstream" / "sat-proof-checkers"
BRANCHES = ("none", "rank1-u0", "all-u-rank2")
TARGET_W0_ORBIT_REPRESENTATIVES = (1, 16, 17, 33)


class SATEncodingError(RuntimeError):
    """The encoding, model, proof tool, or exact replay failed."""


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


@dataclass
class CNFBuilder:
    clauses: list[tuple[int, ...]] = field(default_factory=list)
    variable_count: int = 0

    def new_var(self) -> int:
        self.variable_count += 1
        return self.variable_count

    def add(self, *literals: int) -> None:
        if not literals or any(literal == 0 for literal in literals):
            raise ValueError("CNF clauses must be nonempty and contain no zero")
        self.clauses.append(tuple(literals))


@dataclass
class TensorRankCNF:
    shape: tuple[int, int, int]
    rank: int
    branch: str
    builder: CNFBuilder
    factors: list[tuple[list[int], list[int], list[int]]]
    products: list[list[int]]
    product_terms: list[list[int]]
    parity_prefixes: list[list[int]]
    xor_constraints: list[tuple[tuple[int, ...], bool]]
    order_prefixes: list[list[int]]
    native_xor: bool = False
    fixed_u_masks: tuple[int, ...] | None = None
    fixed_w0_mask: int | None = None
    canonicalize_w_top_glc: bool = False
    w_top_echelon_states: list[list[int]] = field(default_factory=list)
    output_contraction_support: bool = False
    output_contraction_parities: dict[tuple[int, int], int] = field(
        default_factory=dict
    )
    output_contraction_xor_gates: list[tuple[int, int, int]] = field(
        default_factory=list
    )
    output_contraction_clause_count: int = 0
    projected_slice_span: bool = False
    projected_slice_parities: dict[tuple[int, int], int] = field(
        default_factory=dict
    )
    projected_slice_xor_gates: list[tuple[int, int, int]] = field(
        default_factory=list
    )
    projected_slice_clause_count: int = 0
    middle_projected_slice_span: bool = False
    middle_projected_slice_parities: dict[tuple[int, int], int] = field(
        default_factory=dict
    )
    middle_projected_slice_xor_gates: list[tuple[int, int, int]] = field(
        default_factory=list
    )
    middle_projected_slice_clause_count: int = 0
    column_diagonal_vw_coordinate_support: bool = False
    column_diagonal_vw_coordinate_clause_count: int = 0

    @property
    def dims(self) -> tuple[int, int, int]:
        a, b, c = self.shape
        return a * b, b * c, a * c

    @property
    def coefficient_count(self) -> int:
        du, dv, dw = self.dims
        return du * dv * dw


def _validate_shape(shape: Sequence[int]) -> tuple[int, int, int]:
    if len(shape) != 3 or any(
        not isinstance(value, int) or isinstance(value, bool) or value < 1
        for value in shape
    ):
        raise SATEncodingError(f"shape must be three positive integers, got {shape!r}")
    return tuple(shape)  # type: ignore[return-value]


def _xor_gate(builder: CNFBuilder, left: int, right: int, output: int) -> None:
    """Encode output <-> left XOR right with four clauses."""

    builder.add(left, right, -output)
    builder.add(-left, -right, -output)
    builder.add(left, -right, output)
    builder.add(-left, right, output)


def _lex_leq(
    builder: CNFBuilder, left: Sequence[int], right: Sequence[int]
) -> list[int]:
    """Encode the bit word ``left <=lex right`` (0 < 1)."""

    if len(left) != len(right) or not left:
        raise ValueError("lex words must have the same positive width")
    equal_prefix = [builder.new_var() for _ in range(len(left) + 1)]
    builder.add(equal_prefix[0])
    for index, (x, y) in enumerate(zip(left, right, strict=True)):
        previous = equal_prefix[index]
        following = equal_prefix[index + 1]
        # If all earlier bits agree, x=1,y=0 is the sole forbidden order.
        builder.add(-previous, -x, y)
        # following <-> previous AND (x == y).
        builder.add(-following, previous)
        builder.add(-following, -x, y)
        builder.add(-following, x, -y)
        builder.add(-previous, -x, -y, following)
        builder.add(-previous, x, y, following)
    return equal_prefix


def _rank_one_2x3_masks() -> tuple[int, ...]:
    """The 21 nonzero rank-one row-major 2x3 binary matrices."""

    masks = {
        sum(((left >> i) & 1) * ((right >> j) & 1) << (3 * i + j)
            for i in range(2) for j in range(3))
        for left in range(1, 1 << 2)
        for right in range(1, 1 << 3)
    }
    if len(masks) != 21:
        raise AssertionError(f"expected 21 rank-one masks, got {len(masks)}")
    return tuple(sorted(masks))


def matrix_rank_2x3(mask: int) -> int:
    if mask < 0 or mask >= 1 << 6:
        raise ValueError("2x3 mask must fit six bits")
    if mask == 0:
        return 0
    return 1 if mask in _rank_one_2x3_masks() else 2


def canonical_w_right_orbit_2xc(mask: int, c: int) -> int:
    """Canonical orbit of a nonzero 2-by-c matrix under right GL(c,2).

    Right multiplication preserves which of the two rows are zero/equal in
    rank one, while all ordered independent row pairs form one rank-two orbit.
    """

    if c < 2 or mask < 1 or mask >= 1 << (2 * c):
        raise ValueError("W mask must be a nonzero 2-by-c matrix with c >= 2")
    row_mask = (1 << c) - 1
    first = mask & row_mask
    second = mask >> c
    if second == 0:
        return 1
    if first == 0:
        return 1 << c
    if first == second:
        return 1 | (1 << c)
    return 1 | (1 << (c + 1))


def w_top_sequence_is_canonical(w_masks: Sequence[int], c: int) -> bool:
    """Whether first-row projections use the first-basis echelon convention."""

    if c < 1:
        raise ValueError("column dimension must be positive")
    rank_so_far = 0
    row_mask = (1 << c) - 1
    for w_mask in w_masks:
        top = w_mask & row_mask
        if rank_so_far < c and top >> rank_so_far:
            if top != 1 << rank_so_far:
                return False
            rank_so_far += 1
    return rank_so_far == c


def order_fixed_u_for_w_top(u_masks: Sequence[int], b: int) -> tuple[int, ...]:
    """Term-permutation order placing first-row U contributors first."""

    if b < 1:
        raise ValueError("middle dimension must be positive")
    masks = tuple(int(mask) for mask in u_masks)
    row_mask = (1 << b) - 1
    return tuple(sorted(masks, key=lambda mask: (not bool(mask & row_mask), mask)))


def orient_fixed_u_for_w_top(
    u_masks: Sequence[int], b: int, c: int = 4
) -> tuple[int, ...]:
    """Choose a GL(2,2) orientation and term order for projected quotients."""

    if b < 1 or c < 1:
        raise ValueError("middle and column dimensions must be positive")
    row_mask = (1 << b) - 1
    parsed = tuple(int(mask) for mask in u_masks)
    # Ordered independent row combinations; these are all six GL(2,2) maps.
    row_maps = ((1, 2), (1, 3), (2, 1), (2, 3), (3, 1), (3, 2))
    candidates: list[tuple[int, int, tuple[int, ...]]] = []
    for first_map, second_map in row_maps:
        transformed = []
        for mask in parsed:
            rows = (mask & row_mask, (mask >> b) & row_mask)
            first = (rows[0] if first_map & 1 else 0) ^ (
                rows[1] if first_map & 2 else 0
            )
            second = (rows[0] if second_map & 1 else 0) ^ (
                rows[1] if second_map & 2 else 0
            )
            transformed.append(first | (second << b))
        subspaces = _all_binary_subspaces(b)
        lines = [space for space, dimension in subspaces if dimension == 1]
        hyperplanes = [
            space for space, dimension in subspaces if dimension == b - 1
        ]
        flag_orders = [order_fixed_u_for_w_top(transformed, b)]
        if b >= 2:
            for line in lines:
                for hyperplane in hyperplanes:
                    if not line <= hyperplane:
                        continue
                    flag_orders.append(
                        tuple(
                            sorted(
                                transformed,
                                key=lambda mask: (
                                    0
                                    if (mask & row_mask) not in hyperplane
                                    else 1
                                    if (mask & row_mask) not in line
                                    else 2
                                    if mask & row_mask
                                    else 3,
                                    mask,
                                ),
                            )
                        )
                    )
        for ordered in flag_orders:
            contributors = sum(bool(mask & row_mask) for mask in ordered)
            score = _projected_state_exclusion_score(ordered, b, c)
            candidates.append((-score, contributors, ordered))
    return min(candidates)[2]


def _binary_basis(vectors: Sequence[int]) -> tuple[int, ...]:
    basis: dict[int, int] = {}
    for vector in vectors:
        value = vector
        while value:
            pivot = value.bit_length() - 1
            if pivot in basis:
                value ^= basis[pivot]
            else:
                basis[pivot] = value
                break
    return tuple(basis.values())


def _xor_selected(vectors: Sequence[int], selection: int) -> int:
    result = 0
    for index, vector in enumerate(vectors):
        if (selection >> index) & 1:
            result ^= vector
    return result


def _all_binary_subspaces(width: int) -> tuple[tuple[frozenset[int], int], ...]:
    subspaces: set[frozenset[int]] = set()
    nonzero = tuple(range(1, 1 << width))
    for dimension in range(width + 1):
        for generators in itertools.combinations(nonzero, dimension):
            basis = _binary_basis(generators)
            if len(basis) != dimension:
                continue
            subspaces.add(
                frozenset(
                    _xor_selected(basis, selection)
                    for selection in range(1 << dimension)
                )
            )
    result = tuple(
        sorted(
            (
                (space, len(space).bit_length() - 1)
                for space in subspaces
            ),
            key=lambda item: (item[1], tuple(item[0])),
        )
    )
    expected = {2: 5, 3: 16}.get(width)
    if expected is not None and len(result) != expected:
        raise SATEncodingError(
            f"expected {expected} subspaces of F2^{width}, got {len(result)}"
        )
    return result


def _projected_state_exclusion_score(
    u_masks: Sequence[int], b: int, c: int
) -> int:
    row_mask = (1 << b) - 1
    projected = tuple(mask & row_mask for mask in u_masks)
    return sum(
        any(
            sum(mask not in vectors for mask in projected[position:])
            < (b - dimension) * (c - rank_so_far)
            for vectors, dimension in _all_binary_subspaces(b)
        )
        for position in range(len(projected) + 1)
        for rank_so_far in range(c + 1)
    )


def _insert_binary_basis(basis: dict[int, int], vector: int) -> bool:
    value = vector
    while value:
        pivot = value.bit_length() - 1
        if pivot in basis:
            value ^= basis[pivot]
        else:
            basis[pivot] = value
            return True
    return False


def _invert_binary_matrix(rows: Sequence[int], width: int) -> tuple[int, ...]:
    if len(rows) != width:
        raise SATEncodingError("binary matrix inverse requires a square matrix")
    work = [int(row) | (1 << (width + index)) for index, row in enumerate(rows)]
    for pivot in range(width):
        selected = next(
            (row for row in range(pivot, width) if (work[row] >> pivot) & 1),
            None,
        )
        if selected is None:
            raise SATEncodingError("binary matrix is singular")
        work[pivot], work[selected] = work[selected], work[pivot]
        for row in range(width):
            if row != pivot and ((work[row] >> pivot) & 1):
                work[row] ^= work[pivot]
    mask = (1 << width) - 1
    if tuple(row & mask for row in work) != tuple(1 << index for index in range(width)):
        raise SATEncodingError("binary matrix inverse failed to reach identity")
    return tuple((row >> width) & mask for row in work)


def _transpose_binary_matrix(rows: Sequence[int], width: int) -> tuple[int, ...]:
    return tuple(
        sum(((rows[row] >> column) & 1) << row for row in range(width))
        for column in range(width)
    )


def _row_times_binary_matrix(row: int, matrix: Sequence[int], width: int) -> int:
    result = 0
    for index in range(width):
        if (row >> index) & 1:
            result ^= matrix[index]
    return result


def canonicalize_w_top_terms(
    terms: Sequence[Mapping[str, Sequence[int]]], shape: Sequence[int]
) -> list[dict[str, list[int]]]:
    """Apply the exact GL(c,2) action used by W-top canonicalization."""

    shape_tuple = _validate_shape(shape)
    a, b, c = shape_tuple
    parsed = []
    for term in terms:
        triple = {
            name: [int(bit) for bit in term[name]] for name in ("u", "v", "w")
        }
        if tuple(len(triple[name]) for name in ("u", "v", "w")) != (
            a * b,
            b * c,
            a * c,
        ):
            raise SATEncodingError("term dimensions do not match shape")
        parsed.append(triple)
    basis: dict[int, int] = {}
    ordered_basis = []
    for term in parsed:
        top = sum(term["w"][index] << index for index in range(c))
        if _insert_binary_basis(basis, top):
            ordered_basis.append(top)
            if len(ordered_basis) == c:
                break
    if len(ordered_basis) != c:
        raise SATEncodingError("first-row W projections do not span F2^c")
    q_matrix = _invert_binary_matrix(ordered_basis, c)
    v_matrix = _transpose_binary_matrix(ordered_basis, c)  # Q^{-T}.
    transformed = []
    for term in parsed:
        v_bits: list[int] = []
        for middle in range(b):
            row = sum(term["v"][middle * c + k] << k for k in range(c))
            image = _row_times_binary_matrix(row, v_matrix, c)
            v_bits.extend((image >> k) & 1 for k in range(c))
        w_bits: list[int] = []
        for output_row in range(a):
            row = sum(term["w"][output_row * c + k] << k for k in range(c))
            image = _row_times_binary_matrix(row, q_matrix, c)
            w_bits.extend((image >> k) & 1 for k in range(c))
        transformed.append({"u": term["u"], "v": v_bits, "w": w_bits})
    if not w_top_sequence_is_canonical(
        [sum(bit << index for index, bit in enumerate(term["w"])) for term in transformed],
        c,
    ):
        raise SATEncodingError("GL(c) transform did not reach W-top canonical form")
    return transformed


def _contraction_u_support(h_mask: int, shape: tuple[int, int, int]) -> tuple[int, ...]:
    a, b, c = shape
    columns = [
        sum(((h_mask >> (i * c + k)) & 1) << i for i in range(a))
        for k in range(c)
    ]
    return tuple(
        sum(((column >> i) & 1) << (i * b + middle) for i in range(a))
        for middle in range(b)
        for column in _binary_basis(columns)
    )


def _forbid_assignment(builder: CNFBuilder, variables: Sequence[int], mask: int) -> None:
    builder.add(
        *( -variable if (mask >> index) & 1 else variable
           for index, variable in enumerate(variables) )
    )


def add_w_top_echelon_canonicalization(
    builder: CNFBuilder,
    w_variables: Sequence[Sequence[int]],
    c: int,
    minimum_terms_per_missing_dimension: int = 0,
    contributes_to_projected_u: Sequence[bool] | None = None,
    projected_u_masks: Sequence[int] | None = None,
) -> list[list[int]]:
    """Canonicalize first-row W projections under right GL(c,2)."""

    rank = len(w_variables)
    states = [[builder.new_var() for _ in range(c + 1)] for _ in range(rank + 1)]
    for row in states:
        builder.add(*row)
        for left in range(c + 1):
            for right in range(left + 1, c + 1):
                builder.add(-row[left], -row[right])
    builder.add(states[0][0])
    builder.add(states[-1][c])
    if minimum_terms_per_missing_dimension:
        # If the first-row W projections seen so far span dimension r, quotient
        # by that subspace leaves <1,b,c-r>, whose V-flattening rank is b(c-r).
        # Every surviving term lies in the unread suffix.
        if projected_u_masks is not None:
            projected = tuple(int(mask) for mask in projected_u_masks)
            if len(projected) != rank or any(
                mask < 0 or mask >= 1 << minimum_terms_per_missing_dimension
                for mask in projected
            ):
                raise SATEncodingError("projected-U masks have the wrong shape")
            subspaces = _all_binary_subspaces(
                minimum_terms_per_missing_dimension
            )
        else:
            contributors = (
                tuple(bool(value) for value in contributes_to_projected_u)
                if contributes_to_projected_u is not None
                else (True,) * rank
            )
            if len(contributors) != rank:
                raise SATEncodingError(
                    "projected-U contributor mask has the wrong length"
                )
            projected = tuple(int(value) for value in contributors)
            subspaces = ((frozenset({0}), 0),)
        for position, row in enumerate(states):
            for rank_so_far in range(c + 1):
                missing_w = c - rank_so_far
                if any(
                    sum(mask not in vectors for mask in projected[position:])
                    < (minimum_terms_per_missing_dimension - dimension) * missing_w
                    for vectors, dimension in subspaces
                ):
                    builder.add(-row[rank_so_far])
    for term in range(rank):
        top_row = list(w_variables[term][:c])
        current = states[term]
        following = states[term + 1]
        for rank_so_far in range(c + 1):
            state = current[rank_so_far]
            if rank_so_far == c:
                builder.add(-state, following[c])
                continue
            pivot_bit = top_row[rank_so_far]
            for higher_bit in top_row[rank_so_far + 1 :]:
                builder.add(-state, -higher_bit)
            for lower_bit in top_row[:rank_so_far]:
                builder.add(-state, -pivot_bit, -lower_bit)
            builder.add(-state, pivot_bit, following[rank_so_far])
            builder.add(-state, -pivot_bit, following[rank_so_far + 1])
    return states


def build_encoding(
    shape: Sequence[int],
    rank: int,
    branch: str = "none",
    native_xor: bool = False,
    fixed_u_masks: Sequence[int] | None = None,
    fixed_w0_mask: int | None = None,
    canonicalize_w_top_glc: bool = False,
    output_contraction_support: bool = False,
    projected_slice_span: bool = False,
    middle_projected_slice_span: bool = False,
    column_diagonal_vw_coordinate_support: bool = False,
) -> TensorRankCNF:
    shape_tuple = _validate_shape(shape)
    if not isinstance(rank, int) or isinstance(rank, bool) or rank < 1:
        raise SATEncodingError(f"rank must be positive, got {rank!r}")
    if branch not in BRANCHES:
        raise SATEncodingError(f"branch must be one of {BRANCHES}, got {branch!r}")
    if branch != "none" and shape_tuple != TARGET_SHAPE:
        raise SATEncodingError("rank-class symmetry branches are target-specific")
    fixed_u = tuple(fixed_u_masks) if fixed_u_masks is not None else None
    if fixed_u is not None:
        if branch != "none":
            raise SATEncodingError("fixed U factors and rank-class branches are exclusive")
        if len(fixed_u) != rank:
            raise SATEncodingError(f"fixed U profile has {len(fixed_u)} masks, expected {rank}")
        u_width = shape_tuple[0] * shape_tuple[1]
        if any(
            not isinstance(mask, int)
            or isinstance(mask, bool)
            or mask < 1
            or mask >= 1 << u_width
            for mask in fixed_u
        ):
            raise SATEncodingError("fixed U masks must be nonzero and fit the U dimension")
    if fixed_w0_mask is not None:
        w_width = shape_tuple[0] * shape_tuple[2]
        if (
            not isinstance(fixed_w0_mask, int)
            or isinstance(fixed_w0_mask, bool)
            or fixed_w0_mask < 1
            or fixed_w0_mask >= 1 << w_width
        ):
            raise SATEncodingError("fixed W0 mask must be nonzero and fit W")
    if canonicalize_w_top_glc:
        if fixed_u is None:
            raise SATEncodingError("W-top GL(c) canonicalization requires fixed U factors")
        if fixed_w0_mask is not None:
            raise SATEncodingError("fixed W0 and W-top GL(c) canonicalization are exclusive")
    if output_contraction_support and fixed_u is None:
        raise SATEncodingError("output-contraction strengthening requires fixed U factors")
    if projected_slice_span and fixed_u is None:
        raise SATEncodingError("projected-slice strengthening requires fixed U factors")
    if middle_projected_slice_span and fixed_u is None:
        raise SATEncodingError(
            "middle-projected-slice strengthening requires fixed U factors"
        )
    if column_diagonal_vw_coordinate_support and fixed_u is None:
        raise SATEncodingError(
            "column-diagonal V/W coordinate support requires fixed U factors"
        )

    a, b, c = shape_tuple
    if projected_slice_span and a != 2:
        raise SATEncodingError(
            "projected-slice strengthening currently requires first dimension 2"
        )
    dims = (a * b, b * c, a * c)
    builder = CNFBuilder()
    factors: list[tuple[list[int], list[int], list[int]]] = []
    for _ in range(rank):
        triple = tuple([builder.new_var() for _ in range(width)] for width in dims)
        factors.append(triple)  # type: ignore[arg-type]
        for factor in triple:
            builder.add(*factor)  # Every rank-one term has three nonzero factors.

    # When U is fixed, v_s[j] AND w_s[k] is the same Boolean product in every
    # U slice where term s participates.  Share those 19*12*8 products instead
    # of rebuilding six copies.  This is an exact variable elimination, not an
    # added assumption or symmetry restriction.
    shared_vw_products: list[list[list[int]]] | None = None
    if fixed_u is not None:
        shared_vw_products = []
        for _, v, w in factors:
            term_products: list[list[int]] = []
            for j in range(dims[1]):
                row: list[int] = []
                for k in range(dims[2]):
                    product = builder.new_var()
                    builder.add(-product, v[j])
                    builder.add(-product, w[k])
                    builder.add(-v[j], -w[k], product)
                    row.append(product)
                term_products.append(row)
            shared_vw_products.append(term_products)

    products: list[list[int]] = []
    product_terms: list[list[int]] = []
    parity_prefixes: list[list[int]] = []
    xor_constraints: list[tuple[tuple[int, ...], bool]] = []
    target = target_tensor(shape_tuple)
    for i in range(dims[0]):
        for j in range(dims[1]):
            for k in range(dims[2]):
                coefficient_products: list[int] = []
                coefficient_terms: list[int] = []
                for term in range(rank):
                    if fixed_u is not None:
                        if not ((fixed_u[term] >> i) & 1):
                            continue
                        assert shared_vw_products is not None
                        product = shared_vw_products[term][j][k]
                    else:
                        product = builder.new_var()
                        u, v, w = factors[term]
                        # product <-> u_i AND v_j AND w_k.
                        builder.add(-product, u[i])
                        builder.add(-product, v[j])
                        builder.add(-product, w[k])
                        builder.add(-u[i], -v[j], -w[k], product)
                    coefficient_products.append(product)
                    coefficient_terms.append(term)
                if not coefficient_products:
                    raise SATEncodingError(
                        f"fixed U profile leaves target slice {i} unsupported"
                    )
                products.append(coefficient_products)
                product_terms.append(coefficient_terms)
                prefix: list[int] = []
                if native_xor:
                    xor_constraints.append(
                        (tuple(coefficient_products), bool(target[i][j][k]))
                    )
                else:
                    parity = coefficient_products[0]
                    for product in coefficient_products[1:]:
                        next_parity = builder.new_var()
                        _xor_gate(builder, parity, product, next_parity)
                        prefix.append(next_parity)
                        parity = next_parity
                    builder.add(parity if target[i][j][k] else -parity)
                parity_prefixes.append(prefix)

    if branch == "rank1-u0":
        canonical = 1  # e_00.
        for index, variable in enumerate(factors[0][0]):
            builder.add(variable if (canonical >> index) & 1 else -variable)
    elif branch == "all-u-rank2":
        for u, _, _ in factors:
            for rank_one in _rank_one_2x3_masks():
                _forbid_assignment(builder, u, rank_one)
        canonical = (1 << 0) | (1 << 4)  # [I_2 | 0].
        for index, variable in enumerate(factors[0][0]):
            builder.add(variable if (canonical >> index) & 1 else -variable)

    if fixed_u is not None:
        for term, mask in enumerate(fixed_u):
            for index, variable in enumerate(factors[term][0]):
                builder.add(variable if (mask >> index) & 1 else -variable)
    if fixed_w0_mask is not None:
        for index, variable in enumerate(factors[0][2]):
            builder.add(variable if (fixed_w0_mask >> index) & 1 else -variable)

    # The W-support of matrix multiplication is all a*c dimensions, hence the
    # projections of {w_s} onto the first output row span F2^c.  Right GL(c,2)
    # can therefore map their first ordered independent basis to e_0,...,e_{c-1}.
    # The deterministic scan below enforces exactly that canonical echelon form.
    w_top_echelon_states: list[list[int]] = []
    if canonicalize_w_top_glc:
        w_top_echelon_states = add_w_top_echelon_canonicalization(
            builder,
            [factor[2] for factor in factors],
            c,
            minimum_terms_per_missing_dimension=b,
            contributes_to_projected_u=[
                bool(mask & ((1 << b) - 1)) for mask in fixed_u
            ],
            projected_u_masks=[mask & ((1 << b) - 1) for mask in fixed_u],
        )

    projected_slice_parities: dict[tuple[int, int], int] = {}
    projected_slice_xor_gates: list[tuple[int, int, int]] = []
    projected_slice_clauses: set[tuple[int, ...]] = set()
    if projected_slice_span:
        assert fixed_u is not None

        def projected_parity(term: int, h_mask: int) -> int:
            key = (term, h_mask)
            if key in projected_slice_parities:
                return projected_slice_parities[key]
            w_variables = factors[term][2]
            indices = [index for index in range(a * c) if (h_mask >> index) & 1]
            if len(indices) == 1:
                parity = w_variables[indices[0]]
            elif native_xor:
                parity = builder.new_var()
                xor_constraints.append(
                    (
                        tuple(
                            [*(w_variables[index] for index in indices), parity]
                        ),
                        False,
                    )
                )
            else:
                parity = w_variables[indices[0]]
                for index in indices[1:]:
                    following = builder.new_var()
                    _xor_gate(builder, parity, w_variables[index], following)
                    projected_slice_xor_gates.append(
                        (parity, w_variables[index], following)
                    )
                    parity = following
            projected_slice_parities[key] = parity
            return parity

        row_mask = (1 << b) - 1
        row_pairings = ((1, 1), (1, 3), (2, 2), (2, 3), (3, 1), (3, 2))
        for w_row_map, u_row_map in row_pairings:
            for dual in range(1, 1 << (b * c)):
                literals = []
                for term, u_mask in enumerate(fixed_u):
                    u_rows = (
                        u_mask & row_mask,
                        (u_mask >> b) & row_mask,
                    )
                    projected_u = (u_rows[0] if u_row_map & 1 else 0) ^ (
                        u_rows[1] if u_row_map & 2 else 0
                    )
                    projected_w_dual = 0
                    for k in range(c):
                        bit = 0
                        for middle in range(b):
                            if (projected_u >> middle) & 1:
                                bit ^= (dual >> (c * middle + k)) & 1
                        if bit:
                            if w_row_map & 1:
                                projected_w_dual |= 1 << k
                            if w_row_map & 2:
                                projected_w_dual |= 1 << (c + k)
                    if projected_w_dual:
                        literals.append(
                            projected_parity(term, projected_w_dual)
                        )
                if not literals:
                    raise SATEncodingError(
                        "fixed U cannot span a projected slice dual"
                    )
                projected_slice_clauses.add(tuple(literals))
        for clause in sorted(projected_slice_clauses):
            builder.add(*clause)

    # Project along the shared middle index in U and V.  For every pair
    # alpha,beta in F2^b with alpha·beta=1, matrix multiplication contracts to
    # the identity flattening between F2^a x F2^c and W.  Consequently the
    # vectors (U_s beta) tensor (alpha V_s) must span all a*c dimensions.
    # This is complementary to projected_slice_span: it constrains V alone
    # once U is fixed, while the earlier strengthening constrains W alone.
    middle_projected_slice_parities: dict[tuple[int, int], int] = {}
    middle_projected_slice_xor_gates: list[tuple[int, int, int]] = []
    middle_projected_slice_clauses: set[tuple[int, ...]] = set()
    if middle_projected_slice_span:
        assert fixed_u is not None

        def middle_projected_parity(term: int, v_mask: int) -> int:
            key = (term, v_mask)
            if key in middle_projected_slice_parities:
                return middle_projected_slice_parities[key]
            v_variables = factors[term][1]
            indices = [index for index in range(b * c) if (v_mask >> index) & 1]
            if len(indices) == 1:
                parity = v_variables[indices[0]]
            elif native_xor:
                parity = builder.new_var()
                xor_constraints.append(
                    (
                        tuple(
                            [*(v_variables[index] for index in indices), parity]
                        ),
                        False,
                    )
                )
            else:
                parity = v_variables[indices[0]]
                for index in indices[1:]:
                    following = builder.new_var()
                    _xor_gate(builder, parity, v_variables[index], following)
                    middle_projected_slice_xor_gates.append(
                        (parity, v_variables[index], following)
                    )
                    parity = following
            middle_projected_slice_parities[key] = parity
            return parity

        middle_pairings = tuple(
            (v_middle_map, u_middle_map)
            for v_middle_map in range(1, 1 << b)
            for u_middle_map in range(1, 1 << b)
            if (v_middle_map & u_middle_map).bit_count() & 1
        )
        for v_middle_map, u_middle_map in middle_pairings:
            for dual in range(1, 1 << (a * c)):
                literals = []
                for term, u_mask in enumerate(fixed_u):
                    projected_u = 0
                    for output_row in range(a):
                        u_row = (u_mask >> (output_row * b)) & ((1 << b) - 1)
                        if (u_row & u_middle_map).bit_count() & 1:
                            projected_u |= 1 << output_row
                    projected_v_dual = 0
                    for k in range(c):
                        coefficient = 0
                        for output_row in range(a):
                            if (projected_u >> output_row) & 1:
                                coefficient ^= (dual >> (output_row * c + k)) & 1
                        if coefficient:
                            for middle in range(b):
                                if (v_middle_map >> middle) & 1:
                                    projected_v_dual |= 1 << (middle * c + k)
                    if projected_v_dual:
                        literals.append(
                            middle_projected_parity(term, projected_v_dual)
                        )
                if not literals:
                    raise SATEncodingError(
                        "fixed U cannot span a middle-projected slice dual"
                    )
                middle_projected_slice_clauses.add(tuple(literals))
        for clause in sorted(middle_projected_slice_clauses):
            builder.add(*clause)

    # Fix one shared matrix-product column k. Contracting both C-index factors
    # against e_k turns the target into the identity flattening between U and
    # F2^a tensor F2^b. Hence the a*b-vectors
    #
    #     (v_s[0,k],...,v_s[b-1,k]) tensor
    #     (w_s[0,k],...,w_s[a-1,k])
    #
    # span the whole U-dual space. As the cheapest cross-coupled propagation
    # test, expose only its coordinate-dual consequences: every coordinate is
    # nonzero in at least one term. These clauses use the already shared
    # v_s[j] AND w_s[i] products and introduce no new variables or XORs.
    column_diagonal_vw_coordinate_clauses: set[tuple[int, ...]] = set()
    if column_diagonal_vw_coordinate_support:
        assert shared_vw_products is not None
        for column in range(c):
            for output_row in range(a):
                for middle in range(b):
                    column_diagonal_vw_coordinate_clauses.add(
                        tuple(
                            shared_vw_products[term][middle * c + column][
                                output_row * c + column
                            ]
                            for term in range(rank)
                        )
                    )
        for clause in sorted(column_diagonal_vw_coordinate_clauses):
            builder.add(*clause)

    output_contraction_parities: dict[tuple[int, int], int] = {}
    output_contraction_xor_gates: list[tuple[int, int, int]] = []
    output_contraction_clauses: set[tuple[int, ...]] = set()
    if output_contraction_support:
        assert fixed_u is not None
        for h_mask in range(1, 1 << (a * c)):
            indices = [index for index in range(a * c) if (h_mask >> index) & 1]
            for term, (_, _, w_variables) in enumerate(factors):
                if native_xor:
                    parity = builder.new_var()
                    xor_constraints.append(
                        (tuple([*(w_variables[index] for index in indices), parity]), False)
                    )
                else:
                    parity = w_variables[indices[0]]
                    for index in indices[1:]:
                        following = builder.new_var()
                        _xor_gate(builder, parity, w_variables[index], following)
                        output_contraction_xor_gates.append(
                            (parity, w_variables[index], following)
                        )
                        parity = following
                output_contraction_parities[(h_mask, term)] = parity
            required = _contraction_u_support(h_mask, shape_tuple)
            for dual in range(1, 1 << (a * b)):
                if not any((dual & vector).bit_count() & 1 for vector in required):
                    continue
                terms = tuple(
                    term
                    for term, u_mask in enumerate(fixed_u)
                    if (dual & u_mask).bit_count() & 1
                )
                if not terms:
                    raise SATEncodingError(
                        f"fixed U analytically fails contraction h={h_mask}, dual={dual}"
                    )
                output_contraction_clauses.add(
                    tuple(output_contraction_parities[(h_mask, term)] for term in terms)
                )
        for clause in sorted(output_contraction_clauses):
            builder.add(*clause)

    # With term 0 distinguished by the rank-class branch, sort terms 1..r-1.
    # Without a branch, sort every term.
    order_start = 1 if branch != "none" else 0
    order_prefixes: list[list[int]] = []
    if fixed_u is None:
        for term in range(order_start, rank - 1):
            left = [*factors[term][0], *factors[term][1], *factors[term][2]]
            right = [*factors[term + 1][0], *factors[term + 1][1], *factors[term + 1][2]]
            order_prefixes.append(_lex_leq(builder, left, right))

    return TensorRankCNF(
        shape=shape_tuple,
        rank=rank,
        branch=branch,
        builder=builder,
        factors=factors,
        products=products,
        product_terms=product_terms,
        parity_prefixes=parity_prefixes,
        xor_constraints=xor_constraints,
        order_prefixes=order_prefixes,
        native_xor=native_xor,
        fixed_u_masks=fixed_u,
        fixed_w0_mask=fixed_w0_mask,
        canonicalize_w_top_glc=canonicalize_w_top_glc,
        w_top_echelon_states=w_top_echelon_states,
        output_contraction_support=output_contraction_support,
        output_contraction_parities=output_contraction_parities,
        output_contraction_xor_gates=output_contraction_xor_gates,
        output_contraction_clause_count=len(output_contraction_clauses),
        projected_slice_span=projected_slice_span,
        projected_slice_parities=projected_slice_parities,
        projected_slice_xor_gates=projected_slice_xor_gates,
        projected_slice_clause_count=len(projected_slice_clauses),
        middle_projected_slice_span=middle_projected_slice_span,
        middle_projected_slice_parities=middle_projected_slice_parities,
        middle_projected_slice_xor_gates=middle_projected_slice_xor_gates,
        middle_projected_slice_clause_count=len(middle_projected_slice_clauses),
        column_diagonal_vw_coordinate_support=column_diagonal_vw_coordinate_support,
        column_diagonal_vw_coordinate_clause_count=len(
            column_diagonal_vw_coordinate_clauses
        ),
    )


def canonicalize_terms(encoding: TensorRankCNF, terms: Sequence[Any]) -> list[dict]:
    dims = encoding.dims
    parsed: list[dict] = []
    for raw in terms:
        if isinstance(raw, Mapping):
            factors = (raw["u"], raw["v"], raw["w"])
        else:
            factors = raw
        triple: list[list[int]] = []
        for values, width in zip(factors, dims, strict=True):
            bits = [int(value) for value in values]
            if len(bits) != width or set(bits) - {0, 1} or not any(bits):
                raise SATEncodingError("term has malformed or zero factor")
            triple.append(bits)
        parsed.append({"u": triple[0], "v": triple[1], "w": triple[2]})
    if len(parsed) != encoding.rank:
        raise SATEncodingError(
            f"encoding rank {encoding.rank} but received {len(parsed)} terms"
        )
    if encoding.fixed_u_masks is not None:
        actual_masks = tuple(
            sum(bit << index for index, bit in enumerate(term["u"])) for term in parsed
        )
        if actual_masks != encoding.fixed_u_masks:
            raise SATEncodingError(
                f"terms do not match fixed U profile: {actual_masks} != {encoding.fixed_u_masks}"
            )
    else:
        start = 1 if encoding.branch != "none" else 0
        parsed[start:] = sorted(
            parsed[start:], key=lambda term: tuple(term["u"] + term["v"] + term["w"])
        )
    return parsed


def assignment_for_terms(encoding: TensorRankCNF, terms: Sequence[Any]) -> dict[int, bool]:
    canonical = canonicalize_terms(encoding, terms)
    assignment: dict[int, bool] = {}
    for term_index, term in enumerate(canonical):
        for variables, name in zip(encoding.factors[term_index], ("u", "v", "w"), strict=True):
            for variable, bit in zip(variables, term[name], strict=True):
                assignment[variable] = bool(bit)

    coefficient = 0
    for i in range(encoding.dims[0]):
        for j in range(encoding.dims[1]):
            for k in range(encoding.dims[2]):
                values: list[bool] = []
                for term_index, product in zip(
                    encoding.product_terms[coefficient],
                    encoding.products[coefficient],
                    strict=True,
                ):
                    u, v, w = canonical[term_index]["u"], canonical[term_index]["v"], canonical[term_index]["w"]
                    value = bool(u[i] and v[j] and w[k])
                    assignment[product] = value
                    values.append(value)
                if not encoding.native_xor:
                    parity = values[0]
                    for product_value, prefix_var in zip(
                        values[1:], encoding.parity_prefixes[coefficient], strict=True
                    ):
                        parity ^= product_value
                        assignment[prefix_var] = parity
                coefficient += 1

    start = 1 if encoding.branch != "none" else 0
    for pair_index, term_index in enumerate(
        range(start, encoding.rank - 1) if encoding.fixed_u_masks is None else ()
    ):
        left = canonical[term_index]["u"] + canonical[term_index]["v"] + canonical[term_index]["w"]
        right = canonical[term_index + 1]["u"] + canonical[term_index + 1]["v"] + canonical[term_index + 1]["w"]
        prefix_equal = True
        prefix_vars = encoding.order_prefixes[pair_index]
        assignment[prefix_vars[0]] = True
        for index, (x, y) in enumerate(zip(left, right, strict=True)):
            prefix_equal = prefix_equal and x == y
            assignment[prefix_vars[index + 1]] = prefix_equal
    if encoding.canonicalize_w_top_glc:
        c = encoding.shape[2]
        rank_so_far = 0
        for term in range(encoding.rank + 1):
            for state_index, variable in enumerate(
                encoding.w_top_echelon_states[term]
            ):
                assignment[variable] = state_index == rank_so_far
            if term == encoding.rank:
                break
            top_mask = sum(
                canonical[term]["w"][index] << index for index in range(c)
            )
            if rank_so_far < c:
                high = top_mask >> rank_so_far
                if high == 0:
                    continue
                if top_mask != 1 << rank_so_far:
                    raise SATEncodingError(
                        "terms do not satisfy canonical W-top echelon form"
                    )
                rank_so_far += 1
        if rank_so_far != c:
            raise SATEncodingError("W-top projections do not span the column dimension")
    if encoding.output_contraction_support:
        for left, right, output in encoding.output_contraction_xor_gates:
            assignment[output] = assignment[left] ^ assignment[right]
        if encoding.native_xor:
            for (h_mask, term), parity in encoding.output_contraction_parities.items():
                w = canonical[term]["w"]
                assignment[parity] = bool(
                    sum(
                        w[index]
                        for index in range(len(w))
                        if (h_mask >> index) & 1
                    )
                    & 1
                )
    if encoding.projected_slice_span:
        for left, right, output in encoding.projected_slice_xor_gates:
            assignment[output] = assignment[left] ^ assignment[right]
        if encoding.native_xor:
            width = encoding.shape[0] * encoding.shape[2]
            for (term, h_mask), parity in encoding.projected_slice_parities.items():
                w = canonical[term]["w"]
                assignment[parity] = bool(
                    sum(
                        w[index]
                        for index in range(width)
                        if (h_mask >> index) & 1
                    )
                    & 1
                )
    if encoding.middle_projected_slice_span:
        for left, right, output in encoding.middle_projected_slice_xor_gates:
            assignment[output] = assignment[left] ^ assignment[right]
        if encoding.native_xor:
            for (term, v_mask), parity in (
                encoding.middle_projected_slice_parities.items()
            ):
                v = canonical[term]["v"]
                assignment[parity] = bool(
                    sum(
                        v[index]
                        for index in range(len(v))
                        if (v_mask >> index) & 1
                    )
                    & 1
                )
    return assignment


def first_unsatisfied_clause(
    clauses: Sequence[Sequence[int]], assignment: Mapping[int, bool]
) -> int | None:
    for index, clause in enumerate(clauses):
        if not any(
            assignment.get(abs(literal)) is (literal > 0) for literal in clause
        ):
            return index
    return None


def first_unsatisfied_xor(
    constraints: Sequence[tuple[Sequence[int], bool]], assignment: Mapping[int, bool]
) -> int | None:
    for index, (variables, expected) in enumerate(constraints):
        parity = False
        for variable in variables:
            if variable not in assignment:
                return index
            parity ^= assignment[variable]
        if parity != expected:
            return index
    return None


def decode_terms(
    encoding: TensorRankCNF, assignment: Mapping[int, bool]
) -> list[dict]:
    terms: list[dict] = []
    for u, v, w in encoding.factors:
        if any(variable not in assignment for variable in (*u, *v, *w)):
            raise SATEncodingError("model omits a factor variable")
        terms.append(
            {
                "u": [int(assignment[variable]) for variable in u],
                "v": [int(assignment[variable]) for variable in v],
                "w": [int(assignment[variable]) for variable in w],
            }
        )
    verify_rank_decomposition(terms, encoding.shape, encoding.rank)
    return terms


def dimacs_bytes(encoding: TensorRankCNF) -> bytes:
    if encoding.native_xor:
        raise SATEncodingError("native-XOR encoding requires xor_dimacs_bytes")
    lines = [
        f"p cnf {encoding.builder.variable_count} {len(encoding.builder.clauses)}"
    ]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in encoding.builder.clauses)
    return ("\n".join(lines) + "\n").encode()


def xor_dimacs_bytes(encoding: TensorRankCNF) -> bytes:
    if not encoding.native_xor:
        raise SATEncodingError("encoding does not use native XOR constraints")
    total_constraints = len(encoding.builder.clauses) + len(encoding.xor_constraints)
    lines = [f"p cnf {encoding.builder.variable_count} {total_constraints}"]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in encoding.builder.clauses)
    for variables, expected in encoding.xor_constraints:
        literals = list(variables)
        # CryptoMiniSat's x-line means XOR(literals) = true. One negation flips
        # the right-hand side, so a false target negates the first literal.
        if not expected:
            literals[0] = -literals[0]
        lines.append("x" + " ".join(map(str, literals)) + " 0")
    return ("\n".join(lines) + "\n").encode()


def write_exact(path: Path, payload: bytes, force: bool = False) -> None:
    if path.exists():
        actual = path.read_bytes()
        if actual == payload:
            return
        if not force:
            raise SATEncodingError(f"refusing to overwrite mismatching file {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.part")
    temporary.write_bytes(payload)
    temporary.replace(path)


def manifest_for(encoding: TensorRankCNF, cnf_path: Path) -> dict[str, Any]:
    return {
        "schema": ENCODING_SCHEMA,
        "shape": list(encoding.shape),
        "rank": encoding.rank,
        "branch": encoding.branch,
        "semantics": {
            "field": "F2",
            "nonzero_factors": True,
            "exact_coefficient_parity": True,
            "parity_encoding": "native-xor" if encoding.native_xor else "tseitin-cnf",
            "term_order_symmetry_breaking": encoding.fixed_u_masks is None,
            "fixed_u_profile": encoding.fixed_u_masks is not None,
            "fixed_w0_is_single_glc_orbit_subcase": (
                encoding.fixed_w0_mask is not None
            ),
            "w_top_glc_canonicalized": encoding.canonicalize_w_top_glc,
            "output_contraction_support_strengthening": (
                encoding.output_contraction_support
            ),
            "projected_slice_span_strengthening": encoding.projected_slice_span,
            "middle_projected_slice_span_strengthening": (
                encoding.middle_projected_slice_span
            ),
            "column_diagonal_vw_coordinate_support_strengthening": (
                encoding.column_diagonal_vw_coordinate_support
            ),
            "target_ones": sum(
                value
                for plane in target_tensor(encoding.shape)
                for row in plane
                for value in row
            ),
        },
        "fixed_u_masks": list(encoding.fixed_u_masks) if encoding.fixed_u_masks else None,
        "fixed_w0_mask": encoding.fixed_w0_mask,
        "canonicalize_w_top_glc": encoding.canonicalize_w_top_glc,
        "output_contraction_support": encoding.output_contraction_support,
        "output_contraction_support_clauses": encoding.output_contraction_clause_count,
        "projected_slice_span": encoding.projected_slice_span,
        "projected_slice_span_clauses": encoding.projected_slice_clause_count,
        "middle_projected_slice_span": encoding.middle_projected_slice_span,
        "middle_projected_slice_span_clauses": (
            encoding.middle_projected_slice_clause_count
        ),
        "column_diagonal_vw_coordinate_support": (
            encoding.column_diagonal_vw_coordinate_support
        ),
        "column_diagonal_vw_coordinate_support_clauses": (
            encoding.column_diagonal_vw_coordinate_clause_count
        ),
        "cnf": {
            "path": str(cnf_path),
            "sha256": sha256(cnf_path),
            "variables": encoding.builder.variable_count,
            "clauses": len(encoding.builder.clauses),
            "xor_constraints": len(encoding.xor_constraints),
        },
        "factor_variable_ranges": [
            {
                "term": index,
                "u": [variables[0], variables[-1]],
                "v": [encoding.factors[index][1][0], encoding.factors[index][1][-1]],
                "w": [encoding.factors[index][2][0], encoding.factors[index][2][-1]],
            }
            for index, variables in enumerate(factor[0] for factor in encoding.factors)
        ],
    }


def parse_model(path: Path, variable_count: int) -> dict[int, bool]:
    assignment: dict[int, bool] = {}
    saw_sat = False
    for line in path.read_text(errors="replace").splitlines():
        if line.startswith("s ") and "SATISFIABLE" in line and "UNSATISFIABLE" not in line:
            saw_sat = True
        if not line.startswith("v "):
            continue
        for token in line.split()[1:]:
            literal = int(token)
            if literal == 0:
                continue
            variable = abs(literal)
            value = literal > 0
            if variable in assignment and assignment[variable] != value:
                raise SATEncodingError(f"model assigns variable {variable} both ways")
            assignment[variable] = value
    if not saw_sat:
        raise SATEncodingError("model log does not report SATISFIABLE")
    missing = set(range(1, variable_count + 1)) - assignment.keys()
    if missing:
        raise SATEncodingError(f"model omits {len(missing)} variables")
    return assignment


def run_command(command: Sequence[str], timeout: int) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(
            list(command),
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as error:
        raise SATEncodingError(
            f"command timed out after {timeout}s: {' '.join(command)}"
        ) from error


def require_tool(name_or_path: str | Path) -> Path:
    path = Path(name_or_path)
    if path.is_absolute() or path.parent != Path("."):
        if not path.is_file():
            raise SATEncodingError(f"required tool missing: {path}")
        return path
    resolved = shutil.which(str(name_or_path))
    if not resolved:
        raise SATEncodingError(f"required tool missing: {name_or_path}")
    return Path(resolved)


def load_manifest_encoding(manifest_path: Path) -> tuple[dict[str, Any], TensorRankCNF, Path]:
    manifest = json.loads(manifest_path.read_text())
    if manifest.get("schema") != ENCODING_SCHEMA:
        raise SATEncodingError("unexpected manifest schema")
    native_xor = manifest.get("semantics", {}).get("parity_encoding") == "native-xor"
    encoding = build_encoding(
        manifest["shape"],
        manifest["rank"],
        manifest["branch"],
        native_xor,
        manifest.get("fixed_u_masks"),
        manifest.get("fixed_w0_mask"),
        bool(manifest.get("canonicalize_w_top_glc", False)),
        bool(manifest.get("output_contraction_support", False)),
        bool(manifest.get("projected_slice_span", False)),
        bool(manifest.get("middle_projected_slice_span", False)),
        bool(manifest.get("column_diagonal_vw_coordinate_support", False)),
    )
    cnf_path = Path(manifest["cnf"]["path"])
    if not cnf_path.is_absolute():
        cnf_path = ROOT / cnf_path
    expected_cnf = xor_dimacs_bytes(encoding) if native_xor else dimacs_bytes(encoding)
    if not cnf_path.is_file() or cnf_path.read_bytes() != expected_cnf:
        raise SATEncodingError("CNF does not byte-reproduce from the manifest")
    if sha256(cnf_path) != manifest["cnf"]["sha256"]:
        raise SATEncodingError("CNF hash mismatch")
    if manifest["cnf"]["variables"] != encoding.builder.variable_count:
        raise SATEncodingError("manifest variable count mismatch")
    if manifest["cnf"]["clauses"] != len(encoding.builder.clauses):
        raise SATEncodingError("manifest clause count mismatch")
    if manifest["cnf"].get("xor_constraints", 0) != len(encoding.xor_constraints):
        raise SATEncodingError("manifest XOR count mismatch")
    return manifest, encoding, cnf_path


def gaussian_matrix_limit(encoding: TensorRankCNF) -> int:
    """Return a safe matrix cap that includes every native-XOR component."""

    if not encoding.native_xor or not encoding.xor_constraints:
        raise SATEncodingError("Gaussian matrix limit requires native XOR constraints")
    return len(encoding.xor_constraints)


def target_artifact(
    encoding: TensorRankCNF, terms: Sequence[dict], cnf_sha256: str
) -> dict[str, Any]:
    if encoding.shape != TARGET_SHAPE:
        raise SATEncodingError("tracked decomposition artifacts are target-specific")
    return {
        "schema": DECOMPOSITION_SCHEMA,
        "field": "F2",
        "format": TARGET_FORMAT,
        "declared_rank": encoding.rank,
        "terms": list(terms),
        "sat_provenance": {
            "cnf_sha256": cnf_sha256,
            "branch": encoding.branch,
        },
    }


def solve_case(
    manifest_path: Path, output_prefix: Path, timeout: int, force: bool
) -> dict[str, Any]:
    manifest, encoding, cnf_path = load_manifest_encoding(manifest_path)
    solver_name = "cryptominisat5" if encoding.native_xor else "cadical"
    solver = require_tool(solver_name)
    log_path = output_prefix.with_suffix(
        ".cryptominisat.log" if encoding.native_xor else ".cadical.log"
    )
    drat_path = output_prefix.with_suffix(".drat")
    lrat_path = output_prefix.with_suffix(".lrat")
    artifact_path = output_prefix.with_suffix(".rank19.json")
    result_path = output_prefix.with_suffix(".result.json")
    for path in (log_path, drat_path, lrat_path, artifact_path, result_path):
        if path.exists() and not force:
            raise SATEncodingError(f"output {path} already exists (use --force)")
    output_prefix.parent.mkdir(parents=True, exist_ok=True)
    if encoding.native_xor:
        # The target's 576 coefficient equations decompose into 96 small
        # six-row XOR systems, while optional strengthenings add further XOR
        # components. Use the number of encoded XORs as a safe upper bound;
        # the former hard-coded cap of 96 silently discarded strengthening
        # matrices after projected-slice constraints were added.
        gaussian_matrices = gaussian_matrix_limit(encoding)
        command = [
            str(solver),
            "--maxtime",
            str(timeout),
            "--threads",
            "1",
            "--random",
            "0",
            "--maxnummatrices",
            str(gaussian_matrices),
            "--maxxormat",
            "10000",
            str(cnf_path),
        ]
    else:
        command = [
            str(solver),
            "--seed=0",
            "--unsat",
            "--no-binary",
            str(cnf_path),
            str(drat_path),
        ]
    try:
        completed = subprocess.run(
            command,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout + 30 if encoding.native_xor else timeout,
            check=False,
        )
        output = completed.stdout
        returncode: int | None = completed.returncode
    except subprocess.TimeoutExpired as error:
        partial = error.stdout or ""
        output = partial.decode(errors="replace") if isinstance(partial, bytes) else partial
        returncode = None
    write_exact(log_path, output.encode(), force)
    base_result: dict[str, Any] = {
        "schema": "f2-tensor-rank-sat-run-v1",
        "manifest": str(manifest_path),
        "cnf_sha256": manifest["cnf"]["sha256"],
        "shape": list(encoding.shape),
        "rank": encoding.rank,
        "branch": encoding.branch,
        "timeout_seconds": timeout,
        "solver": str(solver),
        "solver_command": command,
        "log": str(log_path),
    }
    if returncode is None:
        drat_path.unlink(missing_ok=True)
        result = {
            **base_result,
            "status": "UNKNOWN_TIMEOUT",
            "interpretation": "Bounded search only; no rank conclusion.",
        }
        write_exact(
            result_path, (json.dumps(result, indent=2, sort_keys=True) + "\n").encode(), force
        )
        return result
    if returncode == 10 and "SATISFIABLE" in output and "UNSATISFIABLE" not in output:
        drat_path.unlink(missing_ok=True)
        assignment = parse_model(log_path, encoding.builder.variable_count)
        clause = first_unsatisfied_clause(encoding.builder.clauses, assignment)
        if clause is not None:
            raise SATEncodingError(f"solver model violates CNF clause {clause}")
        xor = first_unsatisfied_xor(encoding.xor_constraints, assignment)
        if xor is not None:
            raise SATEncodingError(f"solver model violates XOR constraint {xor}")
        terms = decode_terms(encoding, assignment)
        artifact = target_artifact(encoding, terms, manifest["cnf"]["sha256"])
        write_exact(
            artifact_path,
            (json.dumps(artifact, indent=2, sort_keys=True) + "\n").encode(),
            force,
        )
        result = {
            **base_result,
            "status": "SAT_VERIFIED",
            "artifact": str(artifact_path),
            "artifact_sha256": sha256(artifact_path),
            "interpretation": f"Exact rank-{encoding.rank} decomposition found.",
        }
        write_exact(
            result_path, (json.dumps(result, indent=2, sort_keys=True) + "\n").encode(), force
        )
        return result
    if encoding.native_xor and returncode in (0, 15) and "INDETERMINATE" in output:
        result = {
            **base_result,
            "status": "UNKNOWN_TIMEOUT",
            "interpretation": "Bounded native-XOR search only; no rank conclusion.",
        }
        write_exact(
            result_path,
            (json.dumps(result, indent=2, sort_keys=True) + "\n").encode(),
            force,
        )
        return result
    if returncode == 20 and "UNSATISFIABLE" in output:
        if encoding.native_xor:
            result = {
                **base_result,
                "status": "UNSAT_UNCERTIFIED",
                "interpretation": (
                    "CryptoMiniSat returned UNSAT, but no independently checked "
                    "FRAT-XOR/XLRUP proof was produced; no rank conclusion."
                ),
            }
            write_exact(
                result_path,
                (json.dumps(result, indent=2, sort_keys=True) + "\n").encode(),
                force,
            )
            return result
        drat_trim = require_tool(PROOF_CHECKERS / "drat-trim")
        lrat_check = require_tool(PROOF_CHECKERS / "lrat-check")
        if not drat_path.is_file():
            raise SATEncodingError("CaDiCaL reported UNSAT without a proof file")
        checked = run_command(
            [str(drat_trim), str(cnf_path), str(drat_path), "-L", str(lrat_path)], timeout
        )
        if checked.returncode != 0 or "s VERIFIED" not in checked.stdout:
            raise SATEncodingError(f"DRAT replay failed:\n{checked.stdout[-2000:]}")
        lrat_result = run_command([str(lrat_check), str(cnf_path), str(lrat_path)], timeout)
        if lrat_result.returncode != 0 or "VERIFIED" not in lrat_result.stdout.upper():
            raise SATEncodingError(f"LRAT replay failed:\n{lrat_result.stdout[-2000:]}")
        result = {
            **base_result,
            "status": "UNSAT_CERTIFIED",
            "drat": {"path": str(drat_path), "sha256": sha256(drat_path)},
            "lrat": {"path": str(lrat_path), "sha256": sha256(lrat_path)},
            "interpretation": (
                f"This symmetry branch has no exact nonzero rank-{encoding.rank} decomposition."
            ),
        }
        write_exact(
            result_path, (json.dumps(result, indent=2, sort_keys=True) + "\n").encode(), force
        )
        return result
    raise SATEncodingError(
        f"unexpected CaDiCaL result code {returncode}:\n{output[-2000:]}"
    )


def verify_controls(timeout: int) -> dict[str, Any]:
    with tempfile.TemporaryDirectory() as directory_name:
        directory = Path(directory_name)
        positive = build_encoding((2, 2, 2), 7)
        positive_cnf = directory / "rank7.cnf"
        positive_cnf.write_bytes(dimacs_bytes(positive))
        kissat = require_tool("kissat")
        sat = run_command([str(kissat), "--seed=0", str(positive_cnf)], timeout)
        if sat.returncode != 10 or "SATISFIABLE" not in sat.stdout:
            raise SATEncodingError(f"rank-7 positive control failed:\n{sat.stdout[-2000:]}")
        sat_log = directory / "rank7.log"
        sat_log.write_text(sat.stdout)
        sat_assignment = parse_model(sat_log, positive.builder.variable_count)
        clause = first_unsatisfied_clause(positive.builder.clauses, sat_assignment)
        if clause is not None:
            raise SATEncodingError(f"rank-7 solver model violates clause {clause}")
        decoded = decode_terms(positive, sat_assignment)
        verify_rank_decomposition(decoded, (2, 2, 2), 7)

        # Independent known witness must also satisfy the encoding exactly.
        strassen_assignment = assignment_for_terms(positive, strassen_rank_7())
        clause = first_unsatisfied_clause(positive.builder.clauses, strassen_assignment)
        if clause is not None:
            raise SATEncodingError(f"Strassen assignment violates CNF clause {clause}")

        native = build_encoding((2, 2, 2), 7, native_xor=True)
        native_cnf = directory / "rank7-native-xor.cnf"
        native_cnf.write_bytes(xor_dimacs_bytes(native))
        cryptominisat = require_tool("cryptominisat5")
        native_sat = run_command(
            [
                str(cryptominisat),
                "--maxtime",
                str(timeout),
                "--threads",
                "1",
                "--random",
                "0",
                str(native_cnf),
            ],
            timeout + 10,
        )
        if native_sat.returncode != 10 or "SATISFIABLE" not in native_sat.stdout:
            raise SATEncodingError(
                f"rank-7 native-XOR control failed:\n{native_sat.stdout[-2000:]}"
            )
        native_log = directory / "rank7-native-xor.log"
        native_log.write_text(native_sat.stdout)
        native_assignment = parse_model(native_log, native.builder.variable_count)
        clause = first_unsatisfied_clause(native.builder.clauses, native_assignment)
        xor = first_unsatisfied_xor(native.xor_constraints, native_assignment)
        if clause is not None or xor is not None:
            raise SATEncodingError(
                f"native-XOR model failed exact formula check: clause={clause}, xor={xor}"
            )
        decode_terms(native, native_assignment)

        negative = build_encoding((2, 2, 2), 6)
        negative_cnf = directory / "rank6.cnf"
        negative_cnf.write_bytes(dimacs_bytes(negative))
        cadical = require_tool("cadical")
        drat_trim = require_tool(PROOF_CHECKERS / "drat-trim")
        lrat_check = require_tool(PROOF_CHECKERS / "lrat-check")
        drat = directory / "rank6.drat"
        unsat = run_command(
            [str(cadical), "--seed=0", "--unsat", "--no-binary", str(negative_cnf), str(drat)],
            timeout,
        )
        if unsat.returncode != 20 or "UNSATISFIABLE" not in unsat.stdout:
            raise SATEncodingError(f"rank-6 negative control failed:\n{unsat.stdout[-2000:]}")
        lrat = directory / "rank6.lrat"
        checked = run_command(
            [str(drat_trim), str(negative_cnf), str(drat), "-L", str(lrat)], timeout
        )
        if checked.returncode != 0 or "s VERIFIED" not in checked.stdout:
            raise SATEncodingError(f"DRAT control replay failed:\n{checked.stdout[-2000:]}")
        lrat_result = run_command([str(lrat_check), str(negative_cnf), str(lrat)], timeout)
        if lrat_result.returncode != 0 or "VERIFIED" not in lrat_result.stdout.upper():
            raise SATEncodingError(f"LRAT control replay failed:\n{lrat_result.stdout[-2000:]}")
        return {
            "verdict": "CONTROL_PASS",
            "positive_rank7": {
                "variables": positive.builder.variable_count,
                "clauses": len(positive.builder.clauses),
                "solver_model_exactly_verified": True,
                "strassen_assignment_satisfies_cnf": True,
                "native_xor_model_exactly_verified": True,
            },
            "negative_rank6": {
                "variables": negative.builder.variable_count,
                "clauses": len(negative.builder.clauses),
                "cadical_unsat": True,
                "drat_verified": True,
                "lrat_verified": True,
            },
        }


def parse_shape(value: str) -> tuple[int, int, int]:
    try:
        return _validate_shape(tuple(int(part) for part in value.split(",")))
    except ValueError as error:
        raise argparse.ArgumentTypeError("shape must be a,b,c") from error


def transpose_wang_3x2_mask(mask: int) -> int:
    """Map Wang's row-major 3x2 A factor to target row-major 2x3 U."""

    if mask < 1 or mask >= 1 << 6:
        raise SATEncodingError(f"Wang profile mask must be nonzero six-bit, got {mask}")
    result = 0
    for row in range(3):
        for column in range(2):
            if (mask >> (2 * row + column)) & 1:
                result |= 1 << (3 * column + row)
    return result


def load_wang_profile(path: Path, rank: int) -> tuple[int, ...]:
    artifact = json.loads(path.read_text())
    selected = artifact.get("selected_a_forms")
    if not isinstance(selected, list) or len(selected) != rank:
        raise SATEncodingError(f"Wang profile must contain exactly {rank} forms")
    transposed = tuple(sorted(transpose_wang_3x2_mask(mask) for mask in selected))
    if len(set(transposed)) != rank:
        raise SATEncodingError("Wang profile contains duplicate forms after transpose")
    return transposed


def parse_mask_list(value: str) -> tuple[int, ...]:
    try:
        masks = tuple(int(part, 0) for part in value.split(",") if part)
    except ValueError as error:
        raise argparse.ArgumentTypeError("masks must be comma-separated integers") from error
    if not masks:
        raise argparse.ArgumentTypeError("mask list must be nonempty")
    return masks


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    export_parser = subparsers.add_parser("export", help="write deterministic CNF and manifest")
    export_parser.add_argument("--shape", type=parse_shape, default=TARGET_SHAPE)
    export_parser.add_argument("--rank", type=int, required=True)
    export_parser.add_argument("--branch", choices=BRANCHES, default="none")
    export_parser.add_argument("--native-xor", action="store_true")
    export_parser.add_argument(
        "--wang-profile",
        type=Path,
        help="fix target U factors to a transposed Wang 3x2 profile artifact",
    )
    export_parser.add_argument(
        "--projected-slice-span",
        action="store_true",
        help=(
            "require the first-row projected columns u_s(x)w_s to span the "
            "full b*c slice space; redundant exact fixed-U strengthening"
        ),
    )
    export_parser.add_argument(
        "--middle-projected-slice-span",
        action="store_true",
        help=(
            "for every dual middle-index pairing, require the fixed-U/V "
            "projections to span the full a*c output slice; redundant exact "
            "fixed-U strengthening"
        ),
    )
    export_parser.add_argument(
        "--column-diagonal-vw-coordinate-support",
        action="store_true",
        help=(
            "for each shared product column and U-dual coordinate, require "
            "one simultaneous V/W product; redundant exact fixed-U "
            "strengthening"
        ),
    )
    export_parser.add_argument(
        "--output-contraction-support",
        action="store_true",
        help=(
            "add the exact necessary U-support condition for every nonzero W "
            "contraction; redundant strengthening for fixed-U searches"
        ),
    )
    export_parser.add_argument(
        "--canonicalize-w-top",
        action="store_true",
        help=(
            "for fixed U, canonically echelonize first-row W projections under "
            "right GL(c,2); exhaustive because the target W-support is full"
        ),
    )
    export_parser.add_argument(
        "--fixed-u-target-masks",
        type=parse_mask_list,
        help="fix target row-major U factors to comma-separated bitmasks",
    )
    export_parser.add_argument(
        "--fix-w0-mask",
        type=lambda value: int(value, 0),
        help=(
            "fix one distinguished W0 subcase; for target fixed-U searches, "
            "masks 1,16,17,33 together cover the four right-GL(4,2) orbits"
        ),
    )
    export_parser.add_argument("--cnf", type=Path, required=True)
    export_parser.add_argument("--manifest", type=Path, required=True)
    export_parser.add_argument("--force", action="store_true")
    decode_parser = subparsers.add_parser("decode-model", help="verify and decode a SAT model")
    decode_parser.add_argument("--manifest", type=Path, required=True)
    decode_parser.add_argument("--model", type=Path, required=True)
    decode_parser.add_argument("--artifact", type=Path, required=True)
    decode_parser.add_argument("--force", action="store_true")
    solve_parser = subparsers.add_parser(
        "solve", help="run one bounded CaDiCaL case with exact SAT/UNSAT checks"
    )
    solve_parser.add_argument("--manifest", type=Path, required=True)
    solve_parser.add_argument("--output-prefix", type=Path, required=True)
    solve_parser.add_argument("--timeout", type=int, default=300)
    solve_parser.add_argument("--force", action="store_true")
    controls_parser = subparsers.add_parser("verify-controls", help="run SAT and checked-UNSAT controls")
    controls_parser.add_argument("--timeout", type=int, default=300)
    args = parser.parse_args(argv)

    try:
        if args.command == "export":
            if args.wang_profile and args.fixed_u_target_masks:
                raise SATEncodingError(
                    "--wang-profile and --fixed-u-target-masks are mutually exclusive"
                )
            fixed_u = (
                load_wang_profile(args.wang_profile, args.rank)
                if args.wang_profile
                else args.fixed_u_target_masks
            )
            encoding = build_encoding(
                args.shape,
                args.rank,
                args.branch,
                args.native_xor,
                fixed_u,
                args.fix_w0_mask,
                args.canonicalize_w_top,
                args.output_contraction_support,
                args.projected_slice_span,
                args.middle_projected_slice_span,
                args.column_diagonal_vw_coordinate_support,
            )
            payload = xor_dimacs_bytes(encoding) if args.native_xor else dimacs_bytes(encoding)
            write_exact(args.cnf, payload, args.force)
            manifest = manifest_for(encoding, args.cnf)
            if args.wang_profile:
                manifest["fixed_u_source"] = {
                    "path": str(args.wang_profile),
                    "sha256": sha256(args.wang_profile),
                    "map": "row-major 3x2 transpose to row-major 2x3",
                }
            write_exact(
                args.manifest,
                (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode(),
                args.force,
            )
            print(
                f"PASS: wrote {args.cnf} with {encoding.builder.variable_count} variables, "
                f"{len(encoding.builder.clauses)} clauses, "
                f"{len(encoding.xor_constraints)} XORs, branch={args.branch}"
            )
            return 0
        if args.command == "decode-model":
            manifest, encoding, _ = load_manifest_encoding(args.manifest)
            assignment = parse_model(args.model, encoding.builder.variable_count)
            clause = first_unsatisfied_clause(encoding.builder.clauses, assignment)
            if clause is not None:
                raise SATEncodingError(f"model violates CNF clause {clause}")
            terms = decode_terms(encoding, assignment)
            artifact = target_artifact(encoding, terms, manifest["cnf"]["sha256"])
            write_exact(
                args.artifact,
                (json.dumps(artifact, indent=2, sort_keys=True) + "\n").encode(),
                args.force,
            )
            print(f"FOUND: exact rank-{encoding.rank} artifact at {args.artifact}")
            return 0
        if args.command == "solve":
            if args.timeout < 1:
                raise SATEncodingError("timeout must be positive")
            result = solve_case(
                args.manifest, args.output_prefix, args.timeout, args.force
            )
            print(json.dumps(result, indent=2, sort_keys=True))
            return 0
        if args.timeout < 1:
            raise SATEncodingError("timeout must be positive")
        print(json.dumps(verify_controls(args.timeout), indent=2, sort_keys=True))
        return 0
    except (
        OSError,
        ValueError,
        KeyError,
        json.JSONDecodeError,
        SATEncodingError,
        TensorRankEvaluationError,
    ) as error:
        print(f"BROKEN: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
