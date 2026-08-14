"""Exact controls for the Dynamic MoE positive-body reduction.

This module checks the algebraic bridge from Dynamic MoE Serving to chasing
positive bodies.  It does not implement the positive-body chaser itself; that
competitive theorem is a pinned external input.  All arithmetic in the bridge
controls is rational.
"""

from __future__ import annotations

import argparse
import itertools
import json
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence


RATIO = Fraction(3, 2)
ENVELOPE_FACTOR = Fraction(3, 4)


def _fraction(value: int | Fraction) -> Fraction:
    return value if isinstance(value, Fraction) else Fraction(value)


def allocations(parts: int, total: int) -> tuple[tuple[int, ...], ...]:
    """Enumerate nonnegative integer vectors of fixed total."""

    if parts < 1 or total < 0:
        raise ValueError("parts must be positive and total nonnegative")
    if parts == 1:
        return ((total,),)
    return tuple(
        (first,) + rest
        for first in range(total + 1)
        for rest in allocations(parts - 1, total - first)
    )


def allocations_at_most(parts: int, total: int) -> tuple[tuple[int, ...], ...]:
    """Enumerate nonnegative integer vectors whose total is at most ``total``."""

    return tuple(
        vector
        for mass in range(total + 1)
        for vector in allocations(parts, mass)
    )


def latency(
    workload: Sequence[int | Fraction], allocation: Sequence[int | Fraction]
) -> Fraction:
    if len(workload) != len(allocation) or not workload:
        raise ValueError("workload and allocation must have the same positive length")
    if any(_fraction(value) < 0 for value in workload):
        raise ValueError("workloads must be nonnegative")
    if any(_fraction(value) < 0 for value in allocation):
        raise ValueError("allocations must be nonnegative")
    return max(
        _fraction(request) / (1 + _fraction(replicas))
        for request, replicas in zip(workload, allocation, strict=True)
    )


def l1(first: Sequence[int | Fraction], second: Sequence[int | Fraction]) -> Fraction:
    if len(first) != len(second):
        raise ValueError("vectors must have the same length")
    return sum(
        (abs(_fraction(left) - _fraction(right)) for left, right in zip(first, second, strict=True)),
        Fraction(0),
    )


def tangent_grid(k: int) -> tuple[Fraction, ...]:
    """Return the rational geometric tangent scales needed up to augmented mass ``2k``."""

    if not isinstance(k, int) or k < 0:
        raise ValueError("k must be a nonnegative integer")
    maximum_q = Fraction(1 + 2 * k)
    scales: list[Fraction] = []
    scale = Fraction(1)
    while scale <= maximum_q:
        scales.append(scale)
        scale *= RATIO
    return tuple(scales)


def reciprocal(request: int | Fraction, allocation: int | Fraction) -> Fraction:
    request_q = _fraction(request)
    allocation_q = _fraction(allocation)
    if request_q < 0 or allocation_q < 0:
        raise ValueError("request and allocation must be nonnegative")
    return request_q / (1 + allocation_q)


def tangent_value(
    request: int | Fraction,
    allocation: int | Fraction,
    scale: int | Fraction,
) -> Fraction:
    """Evaluate the tangent at ``a=scale-1`` to ``r/(1+u)``."""

    request_q = _fraction(request)
    allocation_q = _fraction(allocation)
    scale_q = _fraction(scale)
    if request_q < 0 or allocation_q < 0 or scale_q < 1:
        raise ValueError("request/allocation must be nonnegative and scale at least one")
    q = 1 + allocation_q
    return request_q * (2 * scale_q - q) / (scale_q * scale_q)


def tangent_envelope(
    request: int | Fraction, allocation: int | Fraction, k: int
) -> Fraction:
    return max(tangent_value(request, allocation, scale) for scale in tangent_grid(k))


def tangent_identity(
    request: int | Fraction,
    allocation: int | Fraction,
    scale: int | Fraction,
) -> dict[str, Fraction]:
    """Return both exact nonnegative gaps used by the tangent proof."""

    request_q = _fraction(request)
    allocation_q = _fraction(allocation)
    scale_q = _fraction(scale)
    q = 1 + allocation_q
    tangent_gap = reciprocal(request_q, allocation_q) - tangent_value(
        request_q, allocation_q, scale_q
    )
    expected_gap = request_q * (q - scale_q) ** 2 / (q * scale_q**2)
    return {
        "tangent_gap": tangent_gap,
        "expected_tangent_gap": expected_gap,
        "ratio": tangent_value(request_q, allocation_q, scale_q)
        / reciprocal(request_q, allocation_q)
        if request_q
        else Fraction(1),
    }


def select_covering_scale(allocation: int | Fraction, k: int) -> Fraction:
    """Choose the largest grid scale not exceeding ``q=1+allocation``."""

    allocation_q = _fraction(allocation)
    if allocation_q < 0 or allocation_q > 2 * k:
        raise ValueError("allocation must lie in the augmented interval [0,2k]")
    q = 1 + allocation_q
    return max(scale for scale in tangent_grid(k) if scale <= q)


def verify_tangent_envelope_at(
    request: int | Fraction, allocation: int | Fraction, k: int
) -> bool:
    """Check ``3/4 * reciprocal <= envelope <= reciprocal`` exactly."""

    allocation_q = _fraction(allocation)
    if allocation_q < 0 or allocation_q > 2 * k:
        raise ValueError("allocation must lie in the augmented interval [0,2k]")
    value = reciprocal(request, allocation_q)
    envelope = tangent_envelope(request, allocation_q, k)
    return ENVELOPE_FACTOR * value <= envelope <= value


def reservoir_map(
    augmented: Sequence[int | Fraction], k: int, reservoir: int = 0
) -> tuple[Fraction, ...]:
    """Map ``sum(u)<=2k`` to a nonnegative exact-budget allocation."""

    if not augmented or not 0 <= reservoir < len(augmented):
        raise ValueError("invalid augmented vector or reservoir index")
    vector = tuple(_fraction(value) for value in augmented)
    if any(value < 0 for value in vector) or sum(vector) > 2 * k:
        raise ValueError("augmented allocation must be nonnegative with mass at most 2k")
    result = [value / 2 for value in vector]
    result[reservoir] = Fraction(k) - sum(
        result[index] for index in range(len(result)) if index != reservoir
    )
    if result[reservoir] < 0 or sum(result) != k:
        raise AssertionError("internal reservoir mapping failure")
    return tuple(result)


def balanced_map(
    augmented: Sequence[int | Fraction], k: int
) -> tuple[Fraction, ...]:
    """Symmetrically map ``sum(u)<=2k`` to an exact-budget allocation."""

    if not augmented:
        raise ValueError("augmented vector must be nonempty")
    vector = tuple(_fraction(value) for value in augmented)
    if any(value < 0 for value in vector) or sum(vector) > 2 * k:
        raise ValueError("augmented allocation must be nonnegative with mass at most 2k")
    slack_per_coordinate = (Fraction(k) - sum(vector, Fraction(0)) / 2) / len(vector)
    result = tuple(value / 2 + slack_per_coordinate for value in vector)
    if any(value < 0 for value in result) or sum(result) != k:
        raise AssertionError("internal balanced mapping failure")
    return result


def reset_service_bound(
    epigraph_height: int | Fraction,
    previous_reset_height: int | Fraction,
    next_reset_height: int | Fraction,
) -> dict[str, Fraction | bool]:
    """Check the vertical-reset inequality used to charge service to movement."""

    height = _fraction(epigraph_height)
    previous = _fraction(previous_reset_height)
    following = _fraction(next_reset_height)
    if min(height, previous, following) < 0:
        raise ValueError("heights must be nonnegative")
    vertical = abs(height - previous) + abs(height - following)
    return {
        "vertical_movement": vertical,
        "twice_height": 2 * height,
        "reset_allowance": previous + following,
        "passes": 2 * height <= vertical + previous + following,
    }


def offline_optimum(
    workloads: Sequence[Sequence[int | Fraction]],
    initial: Sequence[int],
) -> tuple[Fraction, tuple[tuple[int, ...], ...]]:
    """Compute the exact integral offline optimum by finite-state DP."""

    if not initial or any(value < 0 for value in initial):
        raise ValueError("initial allocation must be a nonnegative integer vector")
    m = len(initial)
    k = sum(initial)
    states = allocations(m, k)
    costs: dict[tuple[int, ...], Fraction] = {tuple(initial): Fraction(0)}
    paths: dict[tuple[int, ...], tuple[tuple[int, ...], ...]] = {
        tuple(initial): ()
    }
    for workload in workloads:
        if len(workload) != m:
            raise ValueError("every workload must match the initial dimension")
        next_costs: dict[tuple[int, ...], Fraction] = {}
        next_paths: dict[tuple[int, ...], tuple[tuple[int, ...], ...]] = {}
        for state in states:
            best_cost, best_previous = min(
                (
                    previous_cost + l1(previous, state) + latency(workload, state),
                    previous,
                )
                for previous, previous_cost in costs.items()
            )
            next_costs[state] = best_cost
            next_paths[state] = paths[best_previous] + (state,)
        costs, paths = next_costs, next_paths
    final_state = min(costs, key=lambda state: (costs[state], state))
    return costs[final_state], paths[final_state]


def _fraction_text(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def _exhaustive_bridge_controls(m: int = 3, k: int = 3) -> dict[str, int | str]:
    vectors = allocations_at_most(m, 2 * k)
    movement_checks = 0
    service_checks = 0
    workloads = tuple(
        tuple(Fraction(value) for value in workload)
        for workload in itertools.product((0, 1, 3), repeat=m)
        if any(workload)
    )
    for first in vectors:
        mapped_first = balanced_map(first, k)
        for second in vectors:
            mapped_second = balanced_map(second, k)
            if l1(mapped_first, mapped_second) > l1(first, second):
                raise AssertionError("balanced map expanded movement")
            movement_checks += 1
        for workload in workloads:
            envelope_height = max(
                tangent_envelope(request, replicas, k)
                for request, replicas in zip(workload, first, strict=True)
            )
            if latency(workload, mapped_first) > Fraction(8, 3) * envelope_height:
                raise AssertionError("mapped service exceeded the 8/3 envelope bound")
            service_checks += 1
    return {
        "m": m,
        "k": k,
        "augmented_vectors": len(vectors),
        "movement_checks": movement_checks,
        "service_checks": service_checks,
        "verdict": "EXHAUSTIVE_BRIDGE_PASS",
    }


def control_report() -> dict[str, object]:
    k = 8
    rational_samples = tuple(Fraction(numerator, 8) for numerator in range(16 * k + 1))
    if not all(verify_tangent_envelope_at(7, allocation, k) for allocation in rational_samples):
        raise AssertionError("tangent envelope control failed")

    one_step_cost, one_step_path = offline_optimum(((0, 4),), (1, 0))
    if one_step_cost != 4:
        raise AssertionError("one-step offline control failed")

    full = l1((3, 0, 0), (0, 2, 1))
    one_sided = sum(
        max(right - left, 0)
        for left, right in zip((3, 0, 0), (0, 2, 1), strict=True)
    )
    if full != 2 * one_sided:
        raise AssertionError("movement-normalization negative control failed")

    reset = reset_service_bound(Fraction(11, 3), Fraction(1, 8), Fraction(1, 16))
    if not reset["passes"]:
        raise AssertionError("reset accounting control failed")

    return {
        "verdict": "DYNAMIC_MOE_POSITIVE_BODY_CONTROL_PASS",
        "tangent_grid": {
            "k": k,
            "ratio": _fraction_text(RATIO),
            "envelope_factor": _fraction_text(ENVELOPE_FACTOR),
            "scales": [_fraction_text(scale) for scale in tangent_grid(k)],
            "rational_samples": len(rational_samples),
        },
        "bridge": _exhaustive_bridge_controls(),
        "offline_dp": {
            "one_step_cost": _fraction_text(one_step_cost),
            "one_step_path": [list(state) for state in one_step_path],
            "m1_cost": _fraction_text(offline_optimum(((6,), (3,)), (0,))[0]),
        },
        "movement_negative_control": {
            "full_l1": _fraction_text(full),
            "one_sided": _fraction_text(one_sided),
            "factor": 2,
        },
        "reset": {
            key: _fraction_text(value) if isinstance(value, Fraction) else value
            for key, value in reset.items()
        },
        "analytic_constants": {
            "augmented_budget_factor": 2,
            "polyhedral_epigraph_loss": _fraction_text(1 / ENVELOPE_FACTOR),
            "balanced_map_service_loss": 2,
            "fractional_service_to_vertical_movement": _fraction_text(Fraction(4, 3)),
            "fractional_total_to_body_movement": _fraction_text(Fraction(7, 3)),
            "lazy_threshold_latency_loss": 3,
        },
    }


def write_report(path: Path | None = None) -> dict[str, object]:
    report = control_report()
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if path is None:
        print(rendered, end="")
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(rendered, encoding="utf-8")
        print(f"PASS: wrote {path}")
    return report


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    arguments = parser.parse_args(list(argv) if argv is not None else None)
    write_report(arguments.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
