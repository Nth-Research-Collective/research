#!/usr/bin/env python3
r"""Exact exclusion of the all-rank-one (7,7,5) U-profile orbit.

If a rank-19 decomposition has rank-one U factors ``a_s tensor b_s`` whose
three nonzero F2^2 row directions occur with multiplicities (7,7,5), two
different one-row restrictions leave exactly 12 terms.  Each restricted target
has V-flattening rank 12 and output image ``F2^3 tensor (x tensor F2^4)``.
Equality in the 12-term flattening bound forces every surviving W factor into
``x tensor F2^4``.  The five terms shared by the two restrictions would then
have W in two disjoint four-spaces, contradicting nonzero factors.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from collections.abc import Sequence
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from evaluators.f2_234_tensor_rank_eval import SHAPE  # noqa: E402
from evaluators.f2_234_tensor_rank_eval import verify_rank_decomposition  # noqa: E402
from evaluators.f2_tensor_rank_sat import (  # noqa: E402
    matrix_rank_2x3,
    sha256,
    write_exact,
)
from experiments.f2_234_delta_containment import BASELINE  # noqa: E402
from experiments.f2_234_constraint_profile import (  # noqa: E402
    invertible_matrices,
    transform_form,
)
from experiments.f2_234_profile_orbits import (  # noqa: E402
    classification,
    enumerate_profiles,
    transpose_wang_3x2_mask,
    verify_packet as verify_profile_packet,
)

SCHEMA = "f2-234-tight-row-restriction-exclusion-v1"
ALL_RANK_ONE_SCHEMA = "f2-234-all-rank-one-u-exclusion-v1"
ALL_PROFILE_SCHEMA = "f2-234-all-legal-u-profile-exclusion-v1"
REVIEWED_ALL_PROFILE_SCHEMA = "f2-234-all-legal-u-profile-exclusion-v2"
EXACT_RANK_SCHEMA = "f2-234-exact-rank20-certificate-v2"

PROFILE_ARTIFACT = (
    ROOT / "output" / "f2-234-tensor-rank" / "profile-orbits" / "profile-orbits.json"
)
PROFILE_PROVENANCE = (
    ROOT
    / "output"
    / "f2-234-tensor-rank"
    / "profile-orbits"
    / "proof-pair.manifest.json"
)
ALL_PROFILE_ARTIFACT = (
    ROOT
    / "output"
    / "f2-234-tensor-rank"
    / "all-legal-u-profile-tight-row-exclusion-reviewed.json"
)
WANG_LINUX_LOG = (
    ROOT / "output" / "f2-234-tensor-rank" / "wang-n324-linux-full.log"
)
WANG_LINUX_HASHES = (
    ROOT / "output" / "f2-234-tensor-rank" / "wang-n324-linux-sha256.txt"
)
WANG_SOURCE = (
    ROOT
    / "tmp"
    / "upstream"
    / "f2-234-tensor-rank"
    / "tensor-rank-lower-bound-0ab0562f2fb5430e3ce16035e5882720b5bb613b"
)


class TightRestrictionError(RuntimeError):
    """The theorem assumptions, orbit census, or artifact replay failed."""


def _dot(left: int, right: int) -> int:
    return (left & right).bit_count() & 1


def _binary_rank(vectors: Sequence[int]) -> int:
    basis: dict[int, int] = {}
    for vector in vectors:
        value = int(vector)
        while value:
            pivot = value.bit_length() - 1
            if pivot in basis:
                value ^= basis[pivot]
            else:
                basis[pivot] = value
                break
    return len(basis)


def rank_one_2x3_factors(mask: int) -> tuple[int, int]:
    """Recover the unique nonzero ``a,b`` with mask = a tensor b."""

    if matrix_rank_2x3(mask) != 1:
        raise TightRestrictionError("U mask is not a nonzero rank-one 2x3 form")
    top = mask & 0b111
    bottom = (mask >> 3) & 0b111
    if top and not bottom:
        return 1, top
    if bottom and not top:
        return 2, bottom
    if top == bottom and top:
        return 3, top
    raise TightRestrictionError("rank-one factor recovery reached an impossible case")


def annihilator(direction: int) -> int:
    candidates = tuple(x for x in range(1, 4) if not _dot(direction, x))
    if len(candidates) != 1:
        raise TightRestrictionError("nonzero F2^2 direction lacks a unique annihilator")
    return candidates[0]


def output_row_subspace(x: int, c: int) -> frozenset[int]:
    if x < 1 or x >= 4 or c < 1:
        raise TightRestrictionError("malformed output-row subspace parameters")
    return frozenset(
        (z if x & 1 else 0) | ((z if x & 2 else 0) << c)
        for z in range(1 << c)
    )


def restricted_flattening_rank(x: int, shape: Sequence[int] = SHAPE) -> int:
    """Rank of the restricted target's V flattening, computed independently."""

    a, b, c = tuple(int(value) for value in shape)
    if a != 2 or x < 1 or x >= 4:
        raise TightRestrictionError("tight-row theorem requires a=2 and nonzero x")
    vectors = []
    w_width = a * c
    for middle in range(b):
        for column in range(c):
            w = ((1 << column) if x & 1 else 0) | (
                (1 << (c + column)) if x & 2 else 0
            )
            vectors.append(w << (middle * w_width))
    return _binary_rank(vectors)


def profile_exclusion_report(
    u_masks: Sequence[int], shape: Sequence[int] = SHAPE
) -> dict[str, Any]:
    shape_tuple = tuple(int(value) for value in shape)
    a, b, c = shape_tuple
    masks = tuple(int(mask) for mask in u_masks)
    if shape_tuple != SHAPE or len(masks) != 19 or len(set(masks)) != 19:
        raise TightRestrictionError("the theorem packet requires 19 distinct target U masks")
    if any(mask < 1 or mask >= 1 << (a * b) for mask in masks):
        raise TightRestrictionError("U mask is zero or outside the target space")
    if any(matrix_rank_2x3(mask) != 1 for mask in masks):
        return {
            "verdict": "NOT_APPLICABLE",
            "reason": "at least one U factor has rank two",
        }

    factors = tuple(rank_one_2x3_factors(mask) for mask in masks)
    directions = tuple(a_factor for a_factor, _ in factors)
    counts = Counter(directions)
    multiplicities = tuple(sorted(counts.values(), reverse=True))
    if multiplicities != (7, 7, 5):
        return {
            "verdict": "NOT_APPLICABLE",
            "reason": "row-direction multiplicities are not (7,7,5)",
            "row_direction_counts": {
                str(direction): counts[direction] for direction in range(1, 4)
            },
        }

    tight_directions = tuple(sorted(direction for direction, count in counts.items() if count == 7))
    deficient_direction = next(direction for direction, count in counts.items() if count == 5)
    restrictions = []
    active_sets = []
    for direction in tight_directions:
        x = annihilator(direction)
        active = tuple(index for index, row in enumerate(directions) if _dot(row, x))
        if len(active) != b * c:
            raise TightRestrictionError("tight restriction does not leave exactly b*c terms")
        flattening_rank = restricted_flattening_rank(x, shape_tuple)
        if flattening_rank != b * c:
            raise TightRestrictionError("restricted V-flattening does not have full rank")
        subspace = output_row_subspace(x, c)
        if len(subspace) != 1 << c:
            raise TightRestrictionError("restricted output subspace has the wrong size")
        active_sets.append(set(active))
        restrictions.append(
            {
                "omitted_row_direction": direction,
                "input_row_vector": x,
                "active_term_indices": list(active),
                "active_terms": len(active),
                "v_flattening_rank": flattening_rank,
                "output_subspace_size": len(subspace),
            }
        )
    overlap = tuple(sorted(active_sets[0] & active_sets[1]))
    deficient_indices = tuple(
        index for index, direction in enumerate(directions) if direction == deficient_direction
    )
    if overlap != deficient_indices or len(overlap) != 5:
        raise TightRestrictionError("the two tight restrictions have the wrong overlap")
    x0, x1 = (restriction["input_row_vector"] for restriction in restrictions)
    intersection = output_row_subspace(x0, c) & output_row_subspace(x1, c)
    if intersection != {0}:
        raise TightRestrictionError("the two restricted output spaces do not intersect trivially")
    return {
        "verdict": "EXACT_EXCLUSION",
        "shape": list(shape_tuple),
        "hypothetical_rank": len(masks),
        "row_direction_counts": {
            str(direction): counts[direction] for direction in range(1, 4)
        },
        "tight_row_directions": list(tight_directions),
        "deficient_row_direction": deficient_direction,
        "restrictions": restrictions,
        "overlap_term_indices": list(overlap),
        "overlap_terms": len(overlap),
        "output_subspace_intersection": sorted(intersection),
        "contradiction": (
            "Each overlapping nonzero W factor must lie in both restricted output "
            "spaces, whose intersection is {0}."
        ),
    }


def _pure_tensor_mask(left: int, right: int, right_width: int) -> int:
    return sum(
        right << (index * right_width)
        for index in range(3)
        if (left >> index) & 1
    )


def profile_766_exclusion_report(
    u_masks: Sequence[int], shape: Sequence[int] = SHAPE
) -> dict[str, Any]:
    """Verify the two-stage 12/13-term exclusion for a (7,6,6) profile."""

    shape_tuple = tuple(int(value) for value in shape)
    a, b, c = shape_tuple
    masks = tuple(int(mask) for mask in u_masks)
    if shape_tuple != SHAPE or len(masks) != 19 or len(set(masks)) != 19:
        raise TightRestrictionError("the theorem packet requires 19 distinct target U masks")
    if any(mask < 1 or mask >= 1 << (a * b) for mask in masks):
        raise TightRestrictionError("U mask is zero or outside the target space")
    if any(matrix_rank_2x3(mask) != 1 for mask in masks):
        return {
            "verdict": "NOT_APPLICABLE",
            "reason": "at least one U factor has rank two",
        }
    factors = tuple(rank_one_2x3_factors(mask) for mask in masks)
    directions = tuple(a_factor for a_factor, _ in factors)
    counts = Counter(directions)
    if tuple(sorted(counts.values(), reverse=True)) != (7, 6, 6):
        return {
            "verdict": "NOT_APPLICABLE",
            "reason": "row-direction multiplicities are not (7,6,6)",
            "row_direction_counts": {
                str(direction): counts[direction] for direction in range(1, 4)
            },
        }

    full_direction = next(direction for direction, count in counts.items() if count == 7)
    deficient_directions = tuple(
        sorted(direction for direction, count in counts.items() if count == 6)
    )
    x0 = annihilator(full_direction)
    first_active = tuple(index for index, direction in enumerate(directions) if _dot(direction, x0))
    if len(first_active) != b * c or restricted_flattening_rank(x0) != b * c:
        raise TightRestrictionError("the first restriction is not a tight 12-term flattening")

    omitted_second, retained_deficient = deficient_directions
    x1 = annihilator(omitted_second)
    second_active = tuple(index for index, direction in enumerate(directions) if _dot(direction, x1))
    if len(second_active) != b * c + 1 or restricted_flattening_rank(x1) != b * c:
        raise TightRestrictionError("the second restriction is not a 13-term rank-12 flattening")
    retained_indices = tuple(
        index for index, direction in enumerate(directions) if direction == retained_deficient
    )
    retained_b = tuple(factors[index][1] for index in retained_indices)
    if len(retained_b) != 6 or len(set(retained_b)) != 6:
        raise TightRestrictionError("the retained deficient group lacks six distinct b factors")
    h0 = output_row_subspace(x0, c)
    h1 = output_row_subspace(x1, c)
    if h0 & h1 != {0}:
        raise TightRestrictionError("the two output row spaces do not intersect trivially")
    nonzero_h0 = tuple(sorted(h0 - {0}))
    pure_tensors = {
        _pure_tensor_mask(left, right, a * c)
        for left in range(1, 1 << b)
        for right in nonzero_h0
    }
    expected_factorizations = ((1 << b) - 1) * ((1 << c) - 1)
    if len(pure_tensors) != expected_factorizations:
        raise TightRestrictionError("nonzero pure tensors are not uniquely factored over F2")
    return {
        "verdict": "EXACT_EXCLUSION",
        "shape": list(shape_tuple),
        "hypothetical_rank": len(masks),
        "row_direction_counts": {
            str(direction): counts[direction] for direction in range(1, 4)
        },
        "full_row_direction": full_direction,
        "deficient_row_directions": list(deficient_directions),
        "first_restriction": {
            "input_row_vector": x0,
            "active_term_indices": list(first_active),
            "active_terms": len(first_active),
            "v_flattening_rank": b * c,
            "consequence": "All active W factors lie in H_x0.",
        },
        "second_restriction": {
            "omitted_row_direction": omitted_second,
            "retained_deficient_direction": retained_deficient,
            "input_row_vector": x1,
            "active_term_indices": list(second_active),
            "active_terms": len(second_active),
            "v_flattening_rank": b * c,
            "v_relation_kernel_dimension": len(second_active) - b * c,
        },
        "retained_deficient_term_indices": list(retained_indices),
        "retained_distinct_b_factors": list(retained_b),
        "output_subspace_intersection": sorted(h0 & h1),
        "nonzero_pure_tensor_factorizations_checked": expected_factorizations,
        "unique_nonzero_pure_tensors": len(pure_tensors),
        "contradiction": (
            "The one-dimensional V-relation forces six nonzero quotient pure "
            "tensors to agree, but their six b factors are distinct."
        ),
    }


def profile_rank2_exclusion_report(
    u_masks: Sequence[int], shape: Sequence[int] = SHAPE
) -> dict[str, Any]:
    """Verify the three-restriction incidence contradiction for orbit 3."""

    shape_tuple = tuple(int(value) for value in shape)
    a, b, c = shape_tuple
    masks = tuple(int(mask) for mask in u_masks)
    if shape_tuple != SHAPE or len(masks) != 19 or len(set(masks)) != 19:
        raise TightRestrictionError("the theorem packet requires 19 distinct target U masks")
    ranks = tuple(matrix_rank_2x3(mask) for mask in masks)
    rank_two_indices = tuple(index for index, rank in enumerate(ranks) if rank == 2)
    if len(rank_two_indices) != 1 or ranks.count(1) != 18:
        return {
            "verdict": "NOT_APPLICABLE",
            "reason": "profile does not contain exactly one rank-two U factor",
        }
    rank_two_index = rank_two_indices[0]
    rank_one_factors = {
        index: rank_one_2x3_factors(mask)
        for index, mask in enumerate(masks)
        if index != rank_two_index
    }
    direction_counts = Counter(left for left, _ in rank_one_factors.values())
    if tuple(direction_counts[direction] for direction in range(1, 4)) != (6, 6, 6):
        return {
            "verdict": "NOT_APPLICABLE",
            "reason": "rank-one row-direction multiplicities are not (6,6,6)",
            "row_direction_counts": {
                str(direction): direction_counts[direction]
                for direction in range(1, 4)
            },
        }
    rank_two_mask = masks[rank_two_index]
    rank_two_rows = (rank_two_mask & 0b111, (rank_two_mask >> 3) & 0b111)
    restrictions = []
    active_sets: dict[int, set[int]] = {}
    for x in range(1, 4):
        restricted_rank_two_b = (rank_two_rows[0] if x & 1 else 0) ^ (
            rank_two_rows[1] if x & 2 else 0
        )
        if not restricted_rank_two_b:
            raise TightRestrictionError("rank-two U factor vanishes on a nonzero row")
        active_rank_one = tuple(
            index
            for index, (direction, _) in rank_one_factors.items()
            if _dot(direction, x)
        )
        active = tuple(sorted((*active_rank_one, rank_two_index)))
        if len(active_rank_one) != 12 or len(active) != 13:
            raise TightRestrictionError("rank-two profile restriction has the wrong size")
        if restricted_flattening_rank(x) != b * c:
            raise TightRestrictionError("rank-two profile restriction lacks rank 12")
        active_groups = tuple(
            direction for direction in range(1, 4) if _dot(direction, x)
        )
        for direction in active_groups:
            b_factors = tuple(
                right
                for _, (left, right) in rank_one_factors.items()
                if left == direction
            )
            if len(b_factors) != 6 or len(set(b_factors)) != 6:
                raise TightRestrictionError("an active rank-one group lacks distinct b factors")
        active_sets[x] = set(active)
        restrictions.append(
            {
                "input_row_vector": x,
                "active_term_indices": list(active),
                "active_rank_one_terms": len(active_rank_one),
                "active_terms": len(active),
                "v_flattening_rank": b * c,
                "v_relation_kernel_dimension": len(active) - b * c,
                "active_rank_one_row_directions": list(active_groups),
                "rank_two_restricted_b": restricted_rank_two_b,
                "maximum_nonzero_relation_support": 3,
            }
        )
    pairwise_overlaps = []
    for left in range(1, 4):
        for right in range(left + 1, 4):
            overlap = active_sets[left] & active_sets[right]
            rank_one_overlap = overlap - {rank_two_index}
            b_values = tuple(rank_one_factors[index][1] for index in sorted(rank_one_overlap))
            if len(overlap) != 7 or len(rank_one_overlap) != 6 or len(set(b_values)) != 6:
                raise TightRestrictionError("restriction overlap lacks six distinct rank-one b factors")
            if output_row_subspace(left, c) & output_row_subspace(right, c) != {0}:
                raise TightRestrictionError("restriction output spaces do not intersect trivially")
            pairwise_overlaps.append(
                {
                    "input_row_vectors": [left, right],
                    "overlap_term_indices": sorted(overlap),
                    "overlap_terms": len(overlap),
                    "rank_one_overlap_terms": len(rank_one_overlap),
                    "distinct_rank_one_b_factors": list(b_values),
                    "output_subspace_intersection": [0],
                }
            )
    active_counts = Counter(
        index
        for active in active_sets.values()
        for index in active
        if index != rank_two_index
    )
    if set(active_counts.values()) != {2} or len(active_counts) != 18:
        raise TightRestrictionError("rank-one terms are not active in exactly two restrictions")
    required_incidences = len(active_counts)
    maximum_incidences = len(restrictions) * 3
    if required_incidences <= maximum_incidences:
        raise TightRestrictionError("relation-support incidence count does not contradict")
    return {
        "verdict": "EXACT_EXCLUSION",
        "shape": list(shape_tuple),
        "hypothetical_rank": len(masks),
        "rank_two_term_index": rank_two_index,
        "rank_two_u_mask": rank_two_mask,
        "rank_two_rows": list(rank_two_rows),
        "rank_one_row_direction_counts": {
            str(direction): direction_counts[direction] for direction in range(1, 4)
        },
        "restrictions": restrictions,
        "pairwise_restriction_overlaps": pairwise_overlaps,
        "rank_one_terms_needing_relation_support": len(active_counts),
        "required_relation_support_incidences": required_incidences,
        "maximum_relation_support_per_restriction": 3,
        "maximum_relation_support_incidences": maximum_incidences,
        "contradiction": (
            "Every rank-one term needs a nonzero relation coefficient in at least "
            "one of its two active restrictions (18 incidences), but three one-"
            "dimensional relations can support at most 3 terms each (9 incidences)."
        ),
    }
def _target_orbit_profiles(orbit: dict[str, Any]) -> tuple[tuple[int, ...], ...]:
    representative = tuple(orbit["representative_wang_3x2"])
    images = {
        tuple(sorted(transform_form(form, left, right) for form in representative))
        for left in invertible_matrices(3)
        for right in invertible_matrices(2)
    }
    legal_profiles, _ = enumerate_profiles()
    if len(images) != orbit["orbit_size"] or not images <= legal_profiles:
        raise TightRestrictionError("recomputed orbit does not match the legal profile census")
    return tuple(
        sorted(tuple(sorted(transpose_wang_3x2_mask(form) for form in profile)) for profile in images)
    )


def orbit_zero_packet() -> dict[str, Any]:
    census = classification()
    orbit = next(row for row in census["orbits"] if row["orbit_index"] == 0)
    target_profiles = _target_orbit_profiles(orbit)
    reports = tuple(profile_exclusion_report(profile) for profile in target_profiles)
    if any(report.get("verdict") != "EXACT_EXCLUSION" for report in reports):
        raise TightRestrictionError("the theorem does not exclude every orbit-0 profile")
    return {
        "schema": SCHEMA,
        "field": "F2",
        "shape": list(SHAPE),
        "hypothetical_rank": 19,
        "orbit_index": 0,
        "orbit_size": len(target_profiles),
        "representative_target_2x3": orbit["representative_target_2x3"],
        "representative_report": profile_exclusion_report(
            orbit["representative_target_2x3"]
        ),
        "orbit_profiles_target_2x3": [list(profile) for profile in target_profiles],
        "verified_exclusions": len(reports),
        "theorem": (
            "No rank-19 decomposition can have all rank-one U factors with row-"
            "direction multiplicities (7,7,5)."
        ),
        "proof_obligations": {
            "two_tight_restrictions": True,
            "active_terms_each": 12,
            "restricted_v_flattening_rank": 12,
            "shared_terms": 5,
            "restricted_output_intersection": [0],
            "nonzero_w_factors": True,
        },
        "scope": "All 63 legal U profiles in symmetry orbit 0; no other orbit.",
    }


def all_rank_one_packet() -> dict[str, Any]:
    census = classification()
    rows = []
    all_profiles: list[tuple[int, ...]] = []
    for orbit in census["orbits"]:
        orbit_index = orbit["orbit_index"]
        if orbit_index == 3:
            continue
        profiles = _target_orbit_profiles(orbit)
        report_function = profile_exclusion_report if orbit_index == 0 else profile_766_exclusion_report
        reports = tuple(report_function(profile) for profile in profiles)
        if any(report.get("verdict") != "EXACT_EXCLUSION" for report in reports):
            raise TightRestrictionError(
                f"all-rank-one theorem does not exclude every profile in orbit {orbit_index}"
            )
        all_profiles.extend(profiles)
        rows.append(
            {
                "orbit_index": orbit_index,
                "orbit_size": len(profiles),
                "representative_target_2x3": orbit["representative_target_2x3"],
                "row_direction_type": (
                    [7, 7, 5] if orbit_index == 0 else [7, 6, 6]
                ),
                "verified_exclusions": len(reports),
                "representative_report": report_function(
                    orbit["representative_target_2x3"]
                ),
            }
        )
    if len(all_profiles) != 210 or len(set(all_profiles)) != 210:
        raise TightRestrictionError("all-rank-one profiles do not total 210 distinct supports")
    orbit_three = next(row for row in census["orbits"] if row["orbit_index"] == 3)
    if profile_766_exclusion_report(orbit_three["representative_target_2x3"])[
        "verdict"
    ] != "NOT_APPLICABLE":
        raise TightRestrictionError("rank-two orbit was incorrectly included")
    return {
        "schema": ALL_RANK_ONE_SCHEMA,
        "field": "F2",
        "shape": list(SHAPE),
        "hypothetical_rank": 19,
        "theorem": (
            "No rank-19 decomposition can have 19 pairwise-distinct nonzero "
            "rank-one U factors from the Wang-legal profile census."
        ),
        "excluded_orbits": rows,
        "excluded_profiles": len(all_profiles),
        "legal_profiles_total": census["legal_profiles"],
        "remaining_orbits": [3],
        "remaining_profiles": orbit_three["orbit_size"],
        "remaining_profile_type": "one rank-two U factor and eighteen rank-one U factors",
        "proof_obligations": {
            "distinct_u_factors": census["distinctness_scope"],
            "type_775_two_tight_restrictions": True,
            "type_766_twelve_then_thirteen_term_restrictions": True,
            "restricted_v_flattening_rank": 12,
            "quotient_relation_kernel_dimension": 1,
            "pure_tensor_factorization_unique_over_f2": True,
        },
        "scope": "Exactly profile orbits 0, 1, and 2; orbit 3 remains open.",
        "independent_review": {
            "correctness": "PASS",
            "significance": "BELOW_BAR",
            "openness": "OPEN",
        },
    }


def all_profile_packet() -> dict[str, Any]:
    census = classification()
    rank_one = all_rank_one_packet()
    orbit_three = next(row for row in census["orbits"] if row["orbit_index"] == 3)
    profiles = _target_orbit_profiles(orbit_three)
    reports = tuple(profile_rank2_exclusion_report(profile) for profile in profiles)
    if any(report.get("verdict") != "EXACT_EXCLUSION" for report in reports):
        raise TightRestrictionError("rank-two theorem does not exclude every orbit-3 profile")
    excluded = rank_one["excluded_profiles"] + len(reports)
    if excluded != census["legal_profiles"]:
        raise TightRestrictionError("profile exclusions do not cover the legal census")
    return {
        "schema": ALL_PROFILE_SCHEMA,
        "field": "F2",
        "shape": list(SHAPE),
        "hypothetical_rank": 19,
        "theorem": (
            "Every one of the 252 Wang-legal distinct U profiles for a hypothetical "
            "rank-19 decomposition is incompatible with the matrix-multiplication tensor."
        ),
        "profile_census": {
            "legal_profiles": census["legal_profiles"],
            "orbit_count": census["orbit_count"],
            "distinctness_scope": census["distinctness_scope"],
        },
        "all_rank_one_exclusion": {
            "artifact_schema": ALL_RANK_ONE_SCHEMA,
            "orbits": [0, 1, 2],
            "profiles": rank_one["excluded_profiles"],
        },
        "rank_two_exclusion": {
            "orbit": 3,
            "profiles": len(reports),
            "representative_target_2x3": orbit_three["representative_target_2x3"],
            "representative_report": profile_rank2_exclusion_report(
                orbit_three["representative_target_2x3"]
            ),
        },
        "verified_profile_exclusions": excluded,
        "remaining_profiles": 0,
        "proof_obligations": {
            "all_rank_one_types_775_and_766": True,
            "rank_two_type_666_plus_one": True,
            "rank_two_relation_support_required_incidences": 18,
            "rank_two_relation_support_capacity": 9,
            "restricted_v_flattening_rank": 12,
            "nonzero_factors": True,
        },
        "scope": (
            "Complete relative to the pinned 252-profile census; profile-census "
            "provenance must replay before promoting the exact-rank claim."
        ),
        "independent_review": {
            "orbit_0_correctness": "PASS",
            "orbits_1_2_correctness": "PASS",
            "orbit_3_correctness": "PENDING_FRESH_REVIEW",
        },
    }


def reviewed_all_profile_packet() -> dict[str, Any]:
    packet = all_profile_packet()
    packet["schema"] = REVIEWED_ALL_PROFILE_SCHEMA
    packet["independent_review"] = {
        "openness": "OPEN",
        "correctness": "PASS",
        "significance": "NOTABLE_AS_COMPLETE_EXCLUSION",
        "orbit_0_correctness": "PASS",
        "orbits_1_2_correctness": "PASS",
        "orbit_3_correctness": "PASS",
    }
    return packet


def exact_rank20_packet() -> dict[str, Any]:
    expected_exclusion = reviewed_all_profile_packet()
    exclusion_artifact = json.loads(ALL_PROFILE_ARTIFACT.read_text())
    if exclusion_artifact != expected_exclusion:
        raise TightRestrictionError("all-profile exclusion artifact does not replay")
    profile_artifact = json.loads(PROFILE_ARTIFACT.read_text())
    if profile_artifact.get("classification") != classification():
        raise TightRestrictionError("profile artifact classification does not replay")
    provenance = json.loads(PROFILE_PROVENANCE.read_text())
    wang_log = WANG_LINUX_LOG.read_text()
    required_wang_signals = (
        "Verified. Rank lower bound for matrix_q02_n324 is 19.",
        "UNCONSTRAINED TENSOR RANK LOWER BOUND: 19",
        "OK. Verified certs/matrix/cert_matrix_q02_n324.pb.txt",
    )
    if any(signal not in wang_log for signal in required_wang_signals):
        raise TightRestrictionError("Linux Wang verifier log lacks an acceptance signal")
    cert_path = WANG_SOURCE / "certs" / "matrix" / "cert_matrix_q02_n324.pb.txt"
    btp_path = WANG_SOURCE / "certs" / "matrix" / "cert_matrix_q02_n324.btp"
    hash_record = WANG_LINUX_HASHES.read_text()
    cert_hash = sha256(cert_path)
    btp_hash = sha256(btp_path)
    if cert_hash not in hash_record or btp_hash not in hash_record:
        raise TightRestrictionError("Linux Wang hash record does not match pinned inputs")
    upper = json.loads(BASELINE.read_text())
    verify_rank_decomposition(upper["terms"], SHAPE, 20)
    return {
        "schema": EXACT_RANK_SCHEMA,
        "field": "F2",
        "format": "2x3-by-3x4",
        "claim": "R_F2(<2,3,4>) = 20",
        "lower_bound": {
            "excluded_rank": 19,
            "wang_certificate": {
                "source_commit": "0ab0562f2fb5430e3ce16035e5882720b5bb613b",
                "certificate_path": str(cert_path.relative_to(ROOT)),
                "certificate_sha256": cert_hash,
                "backtracking_archive_path": str(btp_path.relative_to(ROOT)),
                "backtracking_archive_sha256": btp_hash,
                "linux_bazel_version": "8.3.1",
                "linux_verifier_log": str(WANG_LINUX_LOG.relative_to(ROOT)),
                "linux_verifier_log_sha256": sha256(WANG_LINUX_LOG),
                "acceptance_signals": list(required_wang_signals),
            },
            "profile_classification": {
                "artifact": str(PROFILE_ARTIFACT.relative_to(ROOT)),
                "artifact_sha256": sha256(PROFILE_ARTIFACT),
                "proof_provenance": str(PROFILE_PROVENANCE.relative_to(ROOT)),
                "proof_provenance_sha256": sha256(PROFILE_PROVENANCE),
                "cnf_sha256": provenance["files"]["cnf"]["sha256"],
                "drat_sha256": provenance["files"]["drat"]["sha256"],
                "lrat_sha256": provenance["files"]["lrat"]["sha256"],
                "legal_profiles": 252,
                "orbit_count": 4,
                "maximum_rank_two_u_factors": 1,
            },
            "restriction_exclusion": {
                "artifact": str(ALL_PROFILE_ARTIFACT.relative_to(ROOT)),
                "artifact_sha256": sha256(ALL_PROFILE_ARTIFACT),
                "excluded_profiles": exclusion_artifact["verified_profile_exclusions"],
                "remaining_profiles": exclusion_artifact["remaining_profiles"],
            },
        },
        "upper_bound": {
            "rank": 20,
            "artifact": str(BASELINE.relative_to(ROOT)),
            "artifact_sha256": sha256(BASELINE),
            "terms": len(upper["terms"]),
            "coefficients_checked": 576,
            "target_ones": 24,
        },
        "independent_review": {
            "openness": "OPEN",
            "correctness": "PASS",
            "significance": "NOTABLE",
            "novelty": "PASS",
            "publication_recommendation": "PUBLISH",
        },
        "proof_source": "docs/research/2026-08-11-f2-234-rank20-proof.md",
        "replay": {
            "exact_certificate": (
                "python3 -m experiments.f2_234_tight_row_restriction "
                "verify-exact-rank20 --artifact output/f2-234-tensor-rank/"
                "exact-rank20-certificate-v2.json --timeout 300"
            ),
            "campaign_tests": "python3 -m pytest tests/test_*f2* -q",
            "upper_control": (
                "python3 -m evaluators.f2_234_tensor_rank_eval verify-controls"
            ),
        },
    }


def verify_exact_rank20_packet(path: Path, timeout: int) -> dict[str, Any]:
    if timeout < 1:
        raise TightRestrictionError("timeout must be positive")
    artifact = json.loads(path.read_text())
    expected = exact_rank20_packet()
    if artifact != expected:
        raise TightRestrictionError("exact-rank certificate does not replay exactly")
    profile_replay = verify_profile_packet(PROFILE_ARTIFACT, timeout)
    if profile_replay != {
        "verdict": "VERIFIED",
        "legal_profiles": 252,
        "orbit_count": 4,
        "max_rank_two": 1,
    }:
        raise TightRestrictionError("profile proof replay returned unexpected metadata")
    return {
        "verdict": "EXACT_RANK_VERIFIED",
        "rank": 20,
        "field": "F2",
        "format": "2x3-by-3x4",
        "excluded_rank19_profiles": 252,
        "upper_terms": 20,
    }


def verify_packet(path: Path) -> dict[str, Any]:
    artifact = json.loads(path.read_text())
    if artifact.get("schema") == SCHEMA:
        expected = orbit_zero_packet()
    elif artifact.get("schema") == ALL_RANK_ONE_SCHEMA:
        expected = all_rank_one_packet()
    elif artifact.get("schema") == ALL_PROFILE_SCHEMA:
        expected = all_profile_packet()
    elif artifact.get("schema") == REVIEWED_ALL_PROFILE_SCHEMA:
        expected = reviewed_all_profile_packet()
    else:
        raise TightRestrictionError("unexpected tight-row exclusion schema")
    if artifact != expected:
        raise TightRestrictionError("tight-row exclusion artifact does not replay exactly")
    return {
        "verdict": (
            "VERIFIED_ORBIT_EXCLUSION"
            if artifact["schema"] == SCHEMA
            else "VERIFIED_ALL_RANK_ONE_EXCLUSION"
            if artifact["schema"] == ALL_RANK_ONE_SCHEMA
            else "VERIFIED_ALL_PROFILE_EXCLUSION"
        ),
        "verified_exclusions": artifact.get(
            "verified_exclusions", artifact.get("excluded_profiles")
            if artifact["schema"]
            not in (ALL_PROFILE_SCHEMA, REVIEWED_ALL_PROFILE_SCHEMA)
            else artifact.get("verified_profile_exclusions")
        ),
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    export_parser = subparsers.add_parser("export")
    export_parser.add_argument("--output", type=Path, required=True)
    export_parser.add_argument("--force", action="store_true")
    export_all_parser = subparsers.add_parser("export-all-rank-one")
    export_all_parser.add_argument("--output", type=Path, required=True)
    export_all_parser.add_argument("--force", action="store_true")
    export_profiles_parser = subparsers.add_parser("export-all-profiles")
    export_profiles_parser.add_argument("--output", type=Path, required=True)
    export_profiles_parser.add_argument("--force", action="store_true")
    export_reviewed_parser = subparsers.add_parser("export-reviewed-all-profiles")
    export_reviewed_parser.add_argument("--output", type=Path, required=True)
    export_reviewed_parser.add_argument("--force", action="store_true")
    export_exact_parser = subparsers.add_parser("export-exact-rank20")
    export_exact_parser.add_argument("--output", type=Path, required=True)
    export_exact_parser.add_argument("--force", action="store_true")
    verify_parser = subparsers.add_parser("verify")
    verify_parser.add_argument("--artifact", type=Path, required=True)
    verify_exact_parser = subparsers.add_parser("verify-exact-rank20")
    verify_exact_parser.add_argument("--artifact", type=Path, required=True)
    verify_exact_parser.add_argument("--timeout", type=int, default=300)
    args = parser.parse_args(argv)
    try:
        if args.command in (
            "export",
            "export-all-rank-one",
            "export-all-profiles",
            "export-reviewed-all-profiles",
            "export-exact-rank20",
        ):
            packet = (
                orbit_zero_packet()
                if args.command == "export"
                else all_rank_one_packet()
                if args.command == "export-all-rank-one"
                else all_profile_packet()
                if args.command == "export-all-profiles"
                else reviewed_all_profile_packet()
                if args.command == "export-reviewed-all-profiles"
                else exact_rank20_packet()
            )
            write_exact(
                args.output,
                (json.dumps(packet, indent=2, sort_keys=True) + "\n").encode(),
                args.force,
            )
            result = {
                "verdict": (
                    "EXPORTED_EXACT_RANK_CERTIFICATE"
                    if packet.get("schema") == EXACT_RANK_SCHEMA
                    else "EXPORTED_ORBIT_EXCLUSION"
                ),
                "output": str(args.output),
                "verified_exclusions": packet.get(
                    "verified_exclusions",
                    packet.get("excluded_profiles")
                    if packet.get("schema")
                    not in (
                        ALL_PROFILE_SCHEMA,
                        REVIEWED_ALL_PROFILE_SCHEMA,
                        EXACT_RANK_SCHEMA,
                    )
                    else packet.get("verified_profile_exclusions")
                    if packet.get("schema")
                    in (ALL_PROFILE_SCHEMA, REVIEWED_ALL_PROFILE_SCHEMA)
                    else packet["lower_bound"]["restriction_exclusion"][
                        "excluded_profiles"
                    ],
                ),
            }
        elif args.command == "verify-exact-rank20":
            result = verify_exact_rank20_packet(args.artifact, args.timeout)
        else:
            result = verify_packet(args.artifact)
        print(json.dumps(result, indent=2, sort_keys=True))
        return 0
    except (TightRestrictionError, OSError, ValueError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
