"""Exact binary evaluator for rank decompositions of the 2x3-by-3x4 matrix
multiplication tensor over F2.

The target is the matrix-multiplication tensor

    M_{2,3,4} = sum_{i,j,k} e_{ij} (x) e_{jk} (x) e_{ik}
              in U (x) V (x) W,

with canonical factor order

    U = F2^6,    a 2x3 left factor A,   row-major index 3*i + j,
    V = F2^12,   a 3x4 right factor B,  row-major index 4*j + k,
    W = F2^8,    a 2x4 output dual,     row-major index 4*i + k,

so the target has exactly one 1 at each coordinate
((i,j), (j,k), (i,k)) for i in [0,2), j in [0,3), k in [0,4): 24 ones
among 6*12*8 = 576 coefficients.

A candidate decomposition is a list of rank-one terms (u, v, w).  The
evaluator rejects malformed dimensions, non-binary entries, zero factor
vectors, and a wrong declared rank, then recomputes all
576 target coefficients by XOR over the terms.  It accepts only on exact
coefficient equality and, on failure, reports the first mismatching tensor
coordinate with expected and actual values.  No numerical tolerances are used.

The verification is generic over the shape (a, b, c) so the known rank-7
Strassen decomposition of <2,2,2> can be used as a positive control.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any

SCHEMA = "f2-234-tensor-rank-decomposition-v1"
SHAPE = (2, 3, 4)  # (a, b, c): A is a x b, B is b x c, output is a x c.
FACTOR_DIMS = (6, 12, 8)
COEFFICIENT_COUNT = 576
TARGET_ONES = 24
ROOT = Path(__file__).resolve().parent.parent
BASELINE_ARTIFACT_PATH = ROOT / "knowledge" / "data" / "f2_234_rank20_alphatensor.json"

Coordinate = tuple[int, int, int]


class TensorRankEvaluationError(RuntimeError):
    """A candidate decomposition failed exact validation."""


def _validate_shape(shape: Sequence[int]) -> tuple[int, int, int]:
    if not isinstance(shape, Sequence) or len(shape) != 3:
        raise TensorRankEvaluationError(f"shape must be three integers, got {shape!r}")
    if any(not isinstance(value, int) or isinstance(value, bool) for value in shape):
        raise TensorRankEvaluationError(f"shape must be three integers, got {shape!r}")
    dims = tuple(shape)
    if any(value < 1 for value in dims):
        raise TensorRankEvaluationError(f"shape entries must be positive, got {shape!r}")
    return dims  # type: ignore[return-value]


def target_tensor(shape: Sequence[int] = SHAPE) -> tuple[tuple[int, ...], ...]:
    """Return the matrix-multiplication tensor for shape as an a*b x b*c x a*c
    array of F2 coefficients, indexed (i,j),(j,k),(i,k) in row-major order."""

    a, b, c = _validate_shape(shape)
    tensor = [[[0] * (a * c) for _ in range(b * c)] for _ in range(a * b)]
    for i in range(a):
        for j in range(b):
            for k in range(c):
                tensor[i * b + j][j * c + k][i * c + k] = 1
    return tuple(tuple(tuple(row) for row in plane) for plane in tensor)


def _validate_factor(values: Any, length: int, name: str) -> tuple[int, ...]:
    if not isinstance(values, Sequence) or isinstance(values, (str, bytes)):
        raise TensorRankEvaluationError(f"{name} factor must be a sequence of {length} entries")
    if len(values) != length:
        raise TensorRankEvaluationError(
            f"{name} factor has length {len(values)}, expected {length}"
        )
    parsed: list[int] = []
    for value in values:
        if not isinstance(value, int) or value not in (0, 1):
            raise TensorRankEvaluationError(
                f"{name} factor entry {value!r} is not a binary value"
            )
        parsed.append(value)
    return tuple(parsed)


def _term_triple(term: Any, dims: tuple[int, int, int]) -> tuple[tuple[int, ...], ...]:
    if isinstance(term, Mapping):
        raw = (term.get("u"), term.get("v"), term.get("w"))
    elif isinstance(term, Sequence) and not isinstance(term, (str, bytes)):
        raw = tuple(term)
    else:
        raise TensorRankEvaluationError(f"term {term!r} is not a u/v/w triple")
    if len(raw) != 3:
        raise TensorRankEvaluationError(f"term {term!r} does not carry three factors")
    u, v, w = raw
    parsed = (
        _validate_factor(u, dims[0], "u"),
        _validate_factor(v, dims[1], "v"),
        _validate_factor(w, dims[2], "w"),
    )
    if not any(parsed[0]) or not any(parsed[1]) or not any(parsed[2]):
        raise TensorRankEvaluationError(f"term {term!r} contains a zero factor vector")
    return parsed


def first_mismatch(
    terms: Sequence[Any],
    shape: Sequence[int] = SHAPE,
) -> tuple[Coordinate, int, int] | None:
    """Return ((i, j, k), expected, actual) at the first target coordinate where
    the XOR reconstruction differs, or None when the decomposition is exact."""

    a, b, c = _validate_shape(shape)
    dims = (a * b, b * c, a * c)
    target = target_tensor(shape)
    reconstructed = [[[0] * (a * c) for _ in range(b * c)] for _ in range(a * b)]
    for term in terms:
        u, v, w = _term_triple(term, dims)
        for i in range(a * b):
            if not u[i]:
                continue
            for j in range(b * c):
                if not v[j]:
                    continue
                for k in range(a * c):
                    if w[k]:
                        reconstructed[i][j][k] ^= 1
    for i in range(a * b):
        for j in range(b * c):
            for k in range(a * c):
                expected = target[i][j][k]
                actual = reconstructed[i][j][k]
                if actual != expected:
                    return (i, j, k), expected, actual
    return None


def verify_rank_decomposition(
    terms: Sequence[Any],
    shape: Sequence[int] = SHAPE,
    declared_rank: int | None = None,
) -> dict:
    """Replay a rank decomposition against the exact target tensor.

    Raises TensorRankEvaluationError on malformed input, wrong declared rank,
    or any coefficient mismatch, carrying the first
    mismatching coordinate as the witness.  Returns a verdict dict on success.
    """

    a, b, c = _validate_shape(shape)
    factor_dims = (a * b, b * c, a * c)
    if not isinstance(terms, Sequence) or isinstance(terms, (str, bytes)):
        raise TensorRankEvaluationError("terms must be a sequence of rank-one terms")
    if declared_rank is not None:
        if not isinstance(declared_rank, int) or isinstance(declared_rank, bool):
            raise TensorRankEvaluationError("declared rank must be an integer")
        if declared_rank != len(terms):
            raise TensorRankEvaluationError(
                f"declared rank {declared_rank} does not match {len(terms)} terms"
            )
    triples: list[tuple[tuple[int, ...], ...]] = []
    for term in terms:
        triples.append(_term_triple(term, factor_dims))
    mismatch = first_mismatch(triples, shape)
    if mismatch is not None:
        (i, j, k), expected, actual = mismatch
        raise TensorRankEvaluationError(
            f"tensor mismatch at coordinate ({i}, {j}, {k}): "
            f"expected {expected}, got {actual}"
        )
    return {
        "verdict": "VERIFIED",
        "shape": [a, b, c],
        "rank": len(triples),
        "coefficients": a * b * b * c * a * c,
        "target_ones": a * b * c,
    }


def verify_artifact(artifact: Mapping) -> dict:
    """Replay a tracked JSON artifact against the canonical 2x3-by-3x4 target."""

    if not isinstance(artifact, Mapping):
        raise TensorRankEvaluationError("artifact must be a JSON object")
    if artifact.get("schema") != SCHEMA:
        raise TensorRankEvaluationError(
            f"unexpected schema {artifact.get('schema')!r}, expected {SCHEMA!r}"
        )
    if artifact.get("field") != "F2":
        raise TensorRankEvaluationError(
            f"unexpected field {artifact.get('field')!r}, expected 'F2'"
        )
    if artifact.get("format") != "2x3-by-3x4":
        raise TensorRankEvaluationError(
            f"unexpected format {artifact.get('format')!r}, expected '2x3-by-3x4'"
        )
    declared_rank = artifact.get("declared_rank")
    if not isinstance(declared_rank, int) or isinstance(declared_rank, bool) or declared_rank < 1:
        raise TensorRankEvaluationError(f"invalid declared rank {declared_rank!r}")
    terms = artifact.get("terms")
    if not isinstance(terms, list):
        raise TensorRankEvaluationError("artifact terms must be a list")
    result = verify_rank_decomposition(terms, shape=SHAPE, declared_rank=declared_rank)
    result.update(
        {
            "verdict": "VERIFIED_ARTIFACT",
            "schema": SCHEMA,
            "declared_rank": declared_rank,
        }
    )
    return result


def strassen_rank_7() -> list[dict]:
    """The classical Strassen rank-7 decomposition of <2,2,2> over F2.

    Terms are (u, v, w) in row-major 2x2 order with
    m1=(a11+a22)(b11+b22), m2=(a21+a22)b11, m3=a11(b12+b22),
    m4=a22(b11+b21), m5=(a11+a12)b22, m6=(a11+a21)(b11+b12),
    m7=(a12+a22)(b12+b21) and output masks
    c11=m1+m4+m5+m7, c12=m3+m5, c21=m2+m4, c22=m1+m2+m3+m6.
    """

    def term(u: Sequence[int], v: Sequence[int], w: Sequence[int]) -> dict:
        return {"u": list(u), "v": list(v), "w": list(w)}

    return [
        term((1, 0, 0, 1), (1, 0, 0, 1), (1, 0, 0, 1)),
        term((0, 0, 1, 1), (1, 0, 0, 0), (0, 0, 1, 1)),
        term((1, 0, 0, 0), (0, 1, 0, 1), (0, 1, 0, 1)),
        term((0, 0, 0, 1), (1, 0, 1, 0), (1, 0, 1, 0)),
        term((1, 1, 0, 0), (0, 0, 0, 1), (1, 1, 0, 0)),
        term((1, 0, 1, 0), (1, 1, 0, 0), (0, 0, 0, 1)),
        term((0, 1, 0, 1), (0, 0, 1, 1), (1, 0, 0, 0)),
    ]


def control_report() -> dict:
    """Run the smallest positive, negative, and corruption controls."""

    target = target_tensor(SHAPE)
    ones = sum(value for plane in target for row in plane for value in row)
    coefficients = len(target) * len(target[0]) * len(target[0][0])
    if ones != TARGET_ONES or coefficients != COEFFICIENT_COUNT:
        raise TensorRankEvaluationError(
            f"target control failed: ones={ones}, coefficients={coefficients}"
        )

    strassen = strassen_rank_7()
    verify_rank_decomposition(strassen, shape=(2, 2, 2), declared_rank=7)

    corrupted = [dict(term) for term in strassen]
    corrupted[3]["w"][0] ^= 1
    try:
        verify_rank_decomposition(corrupted, shape=(2, 2, 2), declared_rank=7)
    except TensorRankEvaluationError as error:
        witness = str(error)
    else:
        raise TensorRankEvaluationError("one-bit corruption was not rejected")
    if "coordinate" not in witness:
        raise TensorRankEvaluationError("corruption rejection lacks a coordinate witness")

    zero = [dict(term) for term in strassen]
    zero[5] = {"u": [0] * 4, "v": [0] * 4, "w": [0] * 4}
    try:
        verify_rank_decomposition(zero, shape=(2, 2, 2), declared_rank=7)
    except TensorRankEvaluationError as error:
        zero_witness = str(error)
    else:
        raise TensorRankEvaluationError("zero factor vector was not rejected")
    if "zero factor" not in zero_witness:
        raise TensorRankEvaluationError("zero-vector rejection lacks a clear message")

    try:
        verify_rank_decomposition(strassen, shape=(2, 2, 2), declared_rank=6)
    except TensorRankEvaluationError as error:
        rank_witness = str(error)
    else:
        raise TensorRankEvaluationError("declared-rank mismatch was not rejected")
    if "declared rank" not in rank_witness:
        raise TensorRankEvaluationError("rank-mismatch rejection lacks a clear message")

    try:
        with BASELINE_ARTIFACT_PATH.open() as handle:
            baseline = json.load(handle)
        baseline_result = verify_artifact(baseline)
    except (OSError, ValueError) as error:
        raise TensorRankEvaluationError(
            f"cannot load tracked rank-20 baseline: {error}"
        ) from error
    if baseline_result["rank"] != 20:
        raise TensorRankEvaluationError(
            f"tracked baseline has rank {baseline_result['rank']}, expected 20"
        )

    return {
        "verdict": "CONTROL_PASS",
        "target_ones": ones,
        "coefficients": coefficients,
        "strassen_rank_7_accepted": True,
        "one_bit_corruption_rejected": witness,
        "zero_factor_rejected": zero_witness,
        "declared_rank_mismatch_rejected": rank_witness,
        "alphatensor_rank_20_accepted": True,
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    verify_parser = subparsers.add_parser(
        "verify", help="verify a rank-decomposition JSON artifact"
    )
    verify_parser.add_argument("--artifact", type=Path, required=True)
    subparsers.add_parser("verify-controls", help="run exact evaluator controls")

    args = parser.parse_args(argv)
    if args.command == "verify":
        try:
            with args.artifact.open() as handle:
                artifact = json.load(handle)
            result = verify_artifact(artifact)
        except (OSError, ValueError, TensorRankEvaluationError) as error:
            print(f"BROKEN: {error}", file=sys.stderr)
            return 1
        print(
            f"PASS: {args.artifact} verified, "
            f"rank={result['declared_rank']}, "
            f"terms={result['term_count'] if 'term_count' in result else result['rank']}, "
            f"coefficients={result['coefficients']}, target_ones={result['target_ones']}"
        )
        return 0

    if args.command == "verify-controls":
        try:
            report = control_report()
        except (TensorRankEvaluationError, AssertionError) as error:
            print(f"BROKEN: {error}", file=sys.stderr)
            return 1
        print(json.dumps(report, indent=2, sort_keys=True))
        return 0
    raise AssertionError("unreachable command")


if __name__ == "__main__":
    raise SystemExit(main())
