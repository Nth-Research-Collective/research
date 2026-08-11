#!/usr/bin/env python3
r"""Exact test of the Δ-containment elimination for F₂ tensor rank.

With U and W factors fixed, the V factors occur linearly.  Regard the target as
a 48-by-12 matrix whose columns are its V-coordinate slices.  If K is the
48-by-r matrix with columns u_s (x) w_s, then compatible V factors exist exactly
when every target column lies in span(K).  This module checks that criterion,
recovers V by exact F₂ elimination, and replays the resulting decomposition.

The CLI runs known controls and a bounded deterministic W sample on the legal
19-form U profile from the frozen Wang-orbit obstruction.  A no-hit sample is
only a mechanism diagnostic, never a tensor-rank lower bound.
"""

from __future__ import annotations

import argparse
import json
import random
import sys
from collections import Counter
from collections.abc import Sequence
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from evaluators.f2_234_tensor_rank_eval import (  # noqa: E402
    SHAPE,
    strassen_rank_7,
    target_tensor,
    verify_rank_decomposition,
)
from evaluators.f2_tensor_rank_sat import (  # noqa: E402
    load_wang_profile,
    matrix_rank_2x3,
)

BASELINE = ROOT / "knowledge" / "data" / "f2_234_rank20_alphatensor.json"
PROFILE = ROOT / "output" / "f2-234-tensor-rank" / "current-orbit-map-obstruction.json"
SCHEMA = "f2-234-delta-containment-diagnostic-v1"


class DeltaContainmentError(RuntimeError):
    """An exact containment, recovery, or artifact check failed."""


def bits_to_mask(bits: Sequence[int]) -> int:
    return sum(int(bit) << index for index, bit in enumerate(bits))


def mask_to_bits(mask: int, width: int) -> list[int]:
    return [(mask >> index) & 1 for index in range(width)]


def outer_mask(left: int, right: int, right_width: int) -> int:
    result = 0
    for index in range(left.bit_length()):
        if (left >> index) & 1:
            result ^= right << (right_width * index)
    return result


def echelon_with_combinations(vectors: Sequence[int]) -> dict[int, tuple[int, int]]:
    """Highest-pivot F₂ basis; each row carries its input-combination mask."""

    basis: dict[int, tuple[int, int]] = {}
    for index, vector in enumerate(vectors):
        value = vector
        combination = 1 << index
        while value:
            pivot = value.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = (value, combination)
                break
            row, row_combination = basis[pivot]
            value ^= row
            combination ^= row_combination
    return basis


def solve_in_span(basis: dict[int, tuple[int, int]], target: int) -> int | None:
    value = target
    combination = 0
    while value:
        pivot = value.bit_length() - 1
        if pivot not in basis:
            return None
        row, row_combination = basis[pivot]
        value ^= row
        combination ^= row_combination
    return combination


def target_delta_columns(shape: Sequence[int]) -> list[int]:
    a, b, c = shape
    dims = (a * b, b * c, a * c)
    tensor = target_tensor(shape)
    columns: list[int] = []
    for v_index in range(dims[1]):
        column = 0
        for u_index in range(dims[0]):
            for w_index in range(dims[2]):
                if tensor[u_index][v_index][w_index]:
                    column |= 1 << (dims[2] * u_index + w_index)
        columns.append(column)
    return columns


def contain_and_recover(
    u_masks: Sequence[int], w_masks: Sequence[int], shape: Sequence[int]
) -> tuple[bool, list[int] | None, dict[str, int]]:
    if len(u_masks) != len(w_masks) or not u_masks:
        raise DeltaContainmentError("U/W profiles must have the same positive length")
    a, b, c = shape
    du, dv, dw = a * b, b * c, a * c
    if any(mask < 1 or mask >= 1 << du for mask in u_masks):
        raise DeltaContainmentError("U mask is zero or out of range")
    if any(mask < 1 or mask >= 1 << dw for mask in w_masks):
        raise DeltaContainmentError("W mask is zero or out of range")
    columns = [outer_mask(u, w, dw) for u, w in zip(u_masks, w_masks, strict=True)]
    basis = echelon_with_combinations(columns)
    delta = target_delta_columns(shape)
    solutions = [solve_in_span(basis, target) for target in delta]
    metadata = {
        "k_rank": len(basis),
        "delta_rank": len(echelon_with_combinations(delta)),
        "combined_rank": len(echelon_with_combinations([*columns, *delta])),
    }
    if any(solution is None for solution in solutions):
        return False, None, metadata
    v_masks = [0] * len(u_masks)
    for v_index, combination in enumerate(solutions):
        assert combination is not None
        for term in range(len(u_masks)):
            if (combination >> term) & 1:
                v_masks[term] |= 1 << v_index
    return True, v_masks, metadata


def terms_from_masks(
    u_masks: Sequence[int], v_masks: Sequence[int], w_masks: Sequence[int], shape: Sequence[int]
) -> list[dict[str, Any]]:
    a, b, c = shape
    dims = (a * b, b * c, a * c)
    return [
        {
            "u": mask_to_bits(u, dims[0]),
            "v": mask_to_bits(v, dims[1]),
            "w": mask_to_bits(w, dims[2]),
        }
        for u, v, w in zip(u_masks, v_masks, w_masks, strict=True)
    ]


def verify_recovery(terms: Sequence[dict[str, Any]], shape: Sequence[int]) -> dict[str, Any]:
    nonzero = [term for term in terms if any(term["u"]) and any(term["v"]) and any(term["w"])]
    result = verify_rank_decomposition(nonzero, shape, len(nonzero))
    return {"recovered_rank": len(nonzero), "exact_replay": result["verdict"]}


def masks_from_terms(terms: Sequence[dict[str, Any]]) -> tuple[list[int], list[int], list[int]]:
    return (
        [bits_to_mask(term["u"]) for term in terms],
        [bits_to_mask(term["v"]) for term in terms],
        [bits_to_mask(term["w"]) for term in terms],
    )


def dual_slack_report(u_masks: Sequence[int]) -> dict[str, Any]:
    rows: list[tuple[int, int, int, int]] = []
    for dual in range(1, 1 << 6):
        rank = matrix_rank_2x3(dual)
        count = sum((dual & u).bit_count() & 1 for u in u_masks)
        rows.append((dual, rank, count, count - 4 * rank))
    return {
        "slack_histogram": {
            str(slack): count for slack, count in sorted(Counter(row[3] for row in rows).items())
        },
        "rank_count_histogram": {
            f"rank{rank}_count{count}": multiplicity
            for (rank, count), multiplicity in sorted(
                Counter((row[1], row[2]) for row in rows).items()
            )
        },
        "tight_duals": [dual for dual, _, _, slack in rows if slack == 0],
        "violating_duals": [
            {"dual": dual, "rank": rank, "count": count, "slack": slack}
            for dual, rank, count, slack in rows
            if slack < 0
        ],
    }


def run_diagnostic(samples: int, seed: int) -> dict[str, Any]:
    strassen = strassen_rank_7()
    su, sv, sw = masks_from_terms(strassen)
    contained, recovered_v, metadata = contain_and_recover(su, sw, (2, 2, 2))
    if not contained or recovered_v is None:
        raise DeltaContainmentError("Strassen positive control failed containment")
    strassen_recovery = verify_recovery(
        terms_from_masks(su, recovered_v, sw, (2, 2, 2)), (2, 2, 2)
    )
    false_containment, _, false_metadata = contain_and_recover(
        su, [1] * len(su), (2, 2, 2)
    )
    if false_containment:
        raise DeltaContainmentError("deliberately collapsed-W control unexpectedly contained Δ")

    baseline = json.loads(BASELINE.read_text())
    au, av, aw = masks_from_terms(baseline["terms"])
    contained, recovered_v, alpha_metadata = contain_and_recover(au, aw, SHAPE)
    if not contained or recovered_v is None:
        raise DeltaContainmentError("AlphaTensor rank-20 control failed containment")
    alpha_recovery = verify_recovery(terms_from_masks(au, recovered_v, aw, SHAPE), SHAPE)

    profile_u = load_wang_profile(PROFILE, 19)
    rng = random.Random(seed)
    hits: list[dict[str, Any]] = []
    rank_histogram: Counter[int] = Counter()
    combined_rank_histogram: Counter[int] = Counter()
    for sample in range(samples):
        w_masks = [rng.randrange(1, 1 << 8) for _ in profile_u]
        contained, recovered_v, sample_metadata = contain_and_recover(profile_u, w_masks, SHAPE)
        rank_histogram[sample_metadata["k_rank"]] += 1
        combined_rank_histogram[sample_metadata["combined_rank"]] += 1
        if contained:
            assert recovered_v is not None
            terms = terms_from_masks(profile_u, recovered_v, w_masks, SHAPE)
            recovery = verify_recovery(terms, SHAPE)
            hits.append(
                {
                    "sample": sample,
                    "w_masks": w_masks,
                    "v_masks": recovered_v,
                    **sample_metadata,
                    **recovery,
                }
            )
    return {
        "schema": SCHEMA,
        "controls": {
            "strassen_rank7": {"contained": True, **metadata, **strassen_recovery},
            "collapsed_w_negative": {"contained": False, **false_metadata},
            "alphatensor_rank20": {
                "contained": True,
                **alpha_metadata,
                **alpha_recovery,
            },
        },
        "fixed_profile": {
            "source": str(PROFILE.relative_to(ROOT)),
            "u_masks_target_2x3": list(profile_u),
            "dual_slack": dual_slack_report(profile_u),
            "samples": samples,
            "seed": seed,
            "containment_hits": hits,
            "k_rank_histogram": {str(rank): count for rank, count in sorted(rank_histogram.items())},
            "combined_rank_histogram": {
                str(rank): count for rank, count in sorted(combined_rank_histogram.items())
            },
            "interpretation": (
                "A no-hit random sample is only a diagnostic of the proposed search "
                "representation and is not a tensor-rank lower bound."
            ),
        },
    }


def write_new(path: Path, report: dict[str, Any], force: bool) -> None:
    payload = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if path.exists() and not force:
        if path.read_text() == payload:
            return
        raise DeltaContainmentError(f"refusing to overwrite mismatching output {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(payload)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=200)
    parser.add_argument("--seed", type=lambda value: int(value, 0), default=0xD311A)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args(argv)
    try:
        if args.samples < 1:
            raise DeltaContainmentError("samples must be positive")
        report = run_diagnostic(args.samples, args.seed)
        write_new(args.output, report, args.force)
        print(
            "DELTA_DIAGNOSTIC_PASS: controls exact; "
            f"fixed-profile hits={len(report['fixed_profile']['containment_hits'])}/"
            f"{args.samples}; output={args.output}"
        )
        return 0
    except (OSError, ValueError, KeyError, DeltaContainmentError) as error:
        print(f"BROKEN: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
