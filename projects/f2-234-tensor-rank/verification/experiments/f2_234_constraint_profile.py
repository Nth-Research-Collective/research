#!/usr/bin/env python3
r"""Exact obstruction test for Wang's current n324 orbit lower bounds.

For a hypothetical rank-19 decomposition, let x_f be the multiplicity of the
nonzero A-factor f in F_2^6.  For every constraint subspace S, substitution gives

    sum_{f in S \ {0}} x_f + LB(T restricted by S) <= 19.

This script expands the 31 orbit bounds in Wang's pinned n324 certificate to all
2,825 subspaces of F_2^6 under GL(3,2) x GL(2,2), then asks whether an integral
19-term A-profile obeys every inequality.  A SAT profile is an exact structural
obstruction: the current orbit-bound map cannot yield a rank-20 backtracking
certificate, regardless of step budget.  It is not a tensor decomposition.

The emitted JSON can be checked without a solver via the ``verify`` subcommand.
"""

from __future__ import annotations

import argparse
import ast
import json
import re
import sys
from collections import Counter
from collections.abc import Iterable, Sequence
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.bootstrap_f2_234_sources import (  # noqa: E402
    WANG_BTP_SHA256,
    WANG_CERT_NAME,
    WANG_CERT_SHA256,
    WANG_COMMIT,
    WANG_TREE,
    sha256,
)

SCHEMA = "f2-234-wang-constraint-profile-v1"
NA = 6
HYPOTHETICAL_RANK = 19
TARGET_LOWER_BOUND = 20
EXPECTED_ORBITS = 31
EXPECTED_SUBSPACES = 2825
CERT_PATH = WANG_TREE / "certs" / "matrix" / WANG_CERT_NAME
BTP_PATH = CERT_PATH.with_name("cert_matrix_q02_n324.btp")


class ProfileError(RuntimeError):
    """Pinned source, orbit expansion, solver, or artifact check failed."""


def rref(rows: Iterable[int], width: int = NA) -> tuple[int, ...]:
    """Wang's column-reversed F2 RREF, with zero rows omitted."""

    work = list(rows)
    if any(not isinstance(row, int) or isinstance(row, bool) for row in work):
        raise ValueError("RREF rows must be integers")
    if any(row < 0 or row >= 1 << width for row in work):
        raise ValueError(f"RREF rows must fit width {width}")
    current = len(work) - 1
    rank = 0
    for pivot in range(width - 1, -1, -1):
        pivot_row = next(
            (row for row in range(current, -1, -1) if (work[row] >> pivot) & 1),
            None,
        )
        if pivot_row is None:
            continue
        work[current], work[pivot_row] = work[pivot_row], work[current]
        for row in range(len(work)):
            if row != current and ((work[row] >> pivot) & 1):
                work[row] ^= work[current]
        rank += 1
        current -= 1
        if current < 0:
            break
    return tuple(work[len(work) - rank :])


def matrix_rank(rows: Sequence[int], width: int) -> int:
    return len(rref(rows, width))


def invertible_matrices(n: int) -> list[tuple[int, ...]]:
    """All row-packed matrices in GL(n,2), in integer order."""

    result: list[tuple[int, ...]] = []
    mask = (1 << n) - 1
    for data in range(1 << (n * n)):
        rows = tuple((data >> (n * row)) & mask for row in range(n))
        if matrix_rank(rows, n) == n:
            result.append(rows)
    return result


def matrix_multiply(
    left: Sequence[int], right: Sequence[int], inner: int
) -> tuple[int, ...]:
    """Multiply row-packed binary matrices; ``inner`` is the shared dimension."""

    product: list[int] = []
    for left_row in left:
        row = 0
        for index in range(inner):
            if (left_row >> index) & 1:
                row ^= right[index]
        product.append(row)
    return tuple(product)


def transform_form(
    form: int, left: Sequence[int], right: Sequence[int]
) -> int:
    """Direct Wang action X -> L X R on a row-major 3x2 binary form."""

    x_rows = tuple((form >> (2 * row)) & 0b11 for row in range(3))
    transformed = matrix_multiply(matrix_multiply(left, x_rows, 3), right, 2)
    return sum(row << (2 * index) for index, row in enumerate(transformed))


def transform_subspace(
    basis: Sequence[int], left: Sequence[int], right: Sequence[int]
) -> tuple[int, ...]:
    return rref((transform_form(form, left, right) for form in basis))


def _constrained_tensor_blocks(text: str) -> list[str]:
    blocks: list[str] = []
    current: list[str] | None = None
    depth = 0
    for line in text.splitlines():
        if current is None:
            if line.strip() != "constrained_tensors {":
                continue
            current = [line]
            depth = 1
            continue
        current.append(line)
        depth += line.count("{") - line.count("}")
        if depth == 0:
            blocks.append("\n".join(current))
            current = None
    if current is not None:
        raise ProfileError("unterminated constrained_tensors block")
    return blocks


def parse_orbit_bounds(path: Path = CERT_PATH) -> list[dict[str, Any]]:
    """Parse only the three top-level fields needed from Wang's text proto."""

    if not path.is_file() or sha256(path) != WANG_CERT_SHA256:
        raise ProfileError(f"pinned Wang certificate missing or mismatched: {path}")
    records: list[dict[str, Any]] = []
    for default_index, block in enumerate(_constrained_tensor_blocks(path.read_text())):
        index_match = re.search(r"^  index: (\d+)$", block, re.MULTILINE)
        index = int(index_match.group(1)) if index_match else 0
        constraints_match = re.search(
            r'^  constraints: ("(?:\\.|[^"\\])*")$', block, re.MULTILINE
        )
        if constraints_match:
            decoded = ast.literal_eval(constraints_match.group(1))
            basis = tuple(decoded.encode("latin1"))
        else:
            basis = ()
        bound_match = re.search(r"^  rank_lower_bound: (-?\d+)$", block, re.MULTILINE)
        if not bound_match:
            raise ProfileError(f"orbit {index} has no rank_lower_bound")
        canonical = rref(basis)
        if canonical != basis:
            raise ProfileError(
                f"orbit {index} constraints are not canonical: {basis} -> {canonical}"
            )
        records.append(
            {"index": index, "basis": basis, "rank_lower_bound": int(bound_match.group(1))}
        )
        if index != default_index:
            raise ProfileError(
                f"certificate orbit order mismatch: position {default_index}, index {index}"
            )
    if len(records) != EXPECTED_ORBITS:
        raise ProfileError(f"expected {EXPECTED_ORBITS} orbits, got {len(records)}")
    return records


def expand_orbit_bounds(
    records: Sequence[dict[str, Any]],
) -> tuple[dict[tuple[int, ...], int], dict[tuple[int, ...], int], dict[int, int]]:
    """Return subspace->LB, subspace->orbit-index, and orbit-size maps."""

    gl3 = invertible_matrices(3)
    gl2 = invertible_matrices(2)
    if (len(gl3), len(gl2)) != (168, 6):
        raise ProfileError(f"unexpected GL sizes {(len(gl3), len(gl2))}")
    bounds: dict[tuple[int, ...], int] = {}
    orbit_index: dict[tuple[int, ...], int] = {}
    orbit_sizes: dict[int, int] = {}
    for record in records:
        images = {
            transform_subspace(record["basis"], left, right)
            for left in gl3
            for right in gl2
        }
        orbit_sizes[record["index"]] = len(images)
        for image in images:
            previous = bounds.get(image)
            if previous is not None and (
                previous != record["rank_lower_bound"]
                or orbit_index[image] != record["index"]
            ):
                raise ProfileError(
                    f"conflicting orbit assignment for {image}: "
                    f"{orbit_index[image]}/{previous} and "
                    f"{record['index']}/{record['rank_lower_bound']}"
                )
            bounds[image] = record["rank_lower_bound"]
            orbit_index[image] = record["index"]
    if len(bounds) != EXPECTED_SUBSPACES:
        raise ProfileError(
            f"orbit expansion covers {len(bounds)} subspaces, expected {EXPECTED_SUBSPACES}"
        )
    if sum(orbit_sizes.values()) != EXPECTED_SUBSPACES:
        raise ProfileError("orbit sizes do not partition all subspaces")
    return bounds, orbit_index, orbit_sizes


def span_nonzero(basis: Sequence[int]) -> tuple[int, ...]:
    values = {0}
    for row in basis:
        values |= {value ^ row for value in tuple(values)}
    values.discard(0)
    return tuple(sorted(values))


def audit_profile(
    selected: Sequence[int],
    bounds: dict[tuple[int, ...], int],
    orbit_index: dict[tuple[int, ...], int],
) -> dict[str, Any]:
    if len(selected) != HYPOTHETICAL_RANK:
        raise ProfileError(
            f"profile must contain {HYPOTHETICAL_RANK} forms, got {len(selected)}"
        )
    if any(not isinstance(form, int) or isinstance(form, bool) for form in selected):
        raise ProfileError("profile forms must be integers")
    if any(form < 1 or form >= 1 << NA for form in selected):
        raise ProfileError("profile forms must be nonzero six-bit vectors")
    multiplicities = Counter(selected)
    max_score = -1
    binding: list[dict[str, Any]] = []
    by_dimension: dict[int, int] = Counter()
    for subspace, bound in bounds.items():
        count = sum(multiplicities[form] for form in span_nonzero(subspace))
        score = count + bound
        if score > HYPOTHETICAL_RANK:
            raise ProfileError(
                f"profile violates orbit {orbit_index[subspace]}: "
                f"count {count} + lower bound {bound} = {score}"
            )
        max_score = max(max_score, score)
        if score == HYPOTHETICAL_RANK:
            by_dimension[len(subspace)] += 1
            binding.append(
                {
                    "orbit_index": orbit_index[subspace],
                    "dimension": len(subspace),
                    "basis": list(subspace),
                    "profile_count": count,
                    "rank_lower_bound": bound,
                }
            )
    return {
        "max_substitution_score": max_score,
        "binding_subspaces": len(binding),
        "binding_by_dimension": {
            str(dimension): count for dimension, count in sorted(by_dimension.items())
        },
        "binding_examples": binding[:20],
    }


def solve_profile(
    bounds: dict[tuple[int, ...], int], timeout_seconds: int
) -> list[int] | None:
    try:
        from ortools.sat.python import cp_model
    except ImportError as error:  # pragma: no cover - environment dependency.
        raise ProfileError("OR-Tools is required for the solve subcommand") from error

    model = cp_model.CpModel()
    variables = {
        form: model.new_bool_var(f"x_{form:02x}") for form in range(1, 1 << NA)
    }
    model.add(sum(variables.values()) == HYPOTHETICAL_RANK)
    for subspace, bound in bounds.items():
        forms = span_nonzero(subspace)
        capacity = HYPOTHETICAL_RANK - bound
        if forms:
            model.add(sum(variables[form] for form in forms) <= capacity)
        elif capacity < 0:
            return None
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(timeout_seconds)
    solver.parameters.num_search_workers = 1
    result = solver.solve(model)
    if result == cp_model.UNKNOWN:
        raise ProfileError("solver returned unknown: timeout")
    if result == cp_model.INFEASIBLE:
        return None
    if result not in (cp_model.FEASIBLE, cp_model.OPTIMAL):
        raise ProfileError(f"unexpected solver status {solver.status_name(result)}")
    return [form for form, variable in variables.items() if solver.value(variable)]


def source_metadata() -> dict[str, Any]:
    if not BTP_PATH.is_file() or sha256(BTP_PATH) != WANG_BTP_SHA256:
        raise ProfileError(f"pinned Wang BTP archive missing or mismatched: {BTP_PATH}")
    return {
        "wang_commit": WANG_COMMIT,
        "certificate_sha256": WANG_CERT_SHA256,
        "btp_sha256": WANG_BTP_SHA256,
        "problem": "matrix_q02_n324",
        "equivalent_target": "F2 <2,3,4>",
    }


def build_artifact(
    selected: Sequence[int],
    bounds: dict[tuple[int, ...], int],
    orbit_index: dict[tuple[int, ...], int],
    orbit_sizes: dict[int, int],
) -> dict[str, Any]:
    audit = audit_profile(selected, bounds, orbit_index)
    return {
        "schema": SCHEMA,
        "source": source_metadata(),
        "hypothetical_rank": HYPOTHETICAL_RANK,
        "target_lower_bound": TARGET_LOWER_BOUND,
        "selected_a_forms": sorted(selected),
        "selected_a_forms_binary": [f"{form:06b}" for form in sorted(selected)],
        "orbit_count": EXPECTED_ORBITS,
        "subspace_count": EXPECTED_SUBSPACES,
        "orbit_sizes": {str(index): size for index, size in sorted(orbit_sizes.items())},
        **audit,
        "verdict": "current-orbit-map-obstruction",
        "interpretation": (
            "This exact 19-form A-profile satisfies every substitution inequality "
            "from the pinned orbit lower bounds. It proves that Wang backtracking "
            "cannot certify lower bound 20 without strengthening at least one "
            "constrained-orbit bound. It is not a rank-19 tensor decomposition."
        ),
    }


def verify_artifact(artifact: dict[str, Any]) -> dict[str, Any]:
    if artifact.get("schema") != SCHEMA:
        raise ProfileError(f"unexpected artifact schema {artifact.get('schema')!r}")
    if artifact.get("source") != source_metadata():
        raise ProfileError("artifact source metadata does not match pinned inputs")
    records = parse_orbit_bounds()
    bounds, orbit_index, orbit_sizes = expand_orbit_bounds(records)
    selected = artifact.get("selected_a_forms")
    if not isinstance(selected, list):
        raise ProfileError("selected_a_forms must be a list")
    audit = audit_profile(selected, bounds, orbit_index)
    expected = build_artifact(selected, bounds, orbit_index, orbit_sizes)
    if artifact != expected:
        raise ProfileError("artifact fields do not match exact reconstruction")
    return audit


def write_new_json(path: Path, artifact: dict[str, Any], force: bool) -> None:
    if path.exists() and not force:
        raise ProfileError(f"output {path} already exists (use --force to overwrite)")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    solve_parser = subparsers.add_parser("solve", help="find an exact obstruction profile")
    solve_parser.add_argument("--timeout-seconds", type=int, default=300)
    solve_parser.add_argument("--output", type=Path, required=True)
    solve_parser.add_argument("--force", action="store_true")
    verify_parser = subparsers.add_parser("verify", help="verify an emitted profile exactly")
    verify_parser.add_argument("artifact", type=Path)
    args = parser.parse_args(argv)

    try:
        if args.command == "solve":
            if args.timeout_seconds < 1:
                raise ProfileError("timeout-seconds must be positive")
            records = parse_orbit_bounds()
            bounds, orbit_index, orbit_sizes = expand_orbit_bounds(records)
            selected = solve_profile(bounds, args.timeout_seconds)
            if selected is None:
                print(
                    "UNSAT_UNCERTIFIED: no profile exists, but solver status is not "
                    "a portable lower-bound certificate"
                )
                return 2
            artifact = build_artifact(selected, bounds, orbit_index, orbit_sizes)
            write_new_json(args.output, artifact, args.force)
            print(
                "OBSTRUCTION_FOUND: exact 19-form profile evades every current "
                f"orbit-bound inequality; artifact={args.output}"
            )
            print(
                "NOTE: this blocks the current lower-bound map; it is not a "
                "rank-19 tensor decomposition"
            )
            return 0
        with args.artifact.open() as handle:
            artifact = json.load(handle)
        audit = verify_artifact(artifact)
        print(
            "PASS: exact obstruction profile satisfies all "
            f"{EXPECTED_SUBSPACES} substitution inequalities "
            f"(max score {audit['max_substitution_score']})"
        )
        return 0
    except (OSError, ValueError, ProfileError, json.JSONDecodeError) as error:
        print(f"BROKEN: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
