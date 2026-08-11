#!/usr/bin/env python3
r"""Certify and enumerate legal Wang-profile supports for target rank 19.

The pinned n324 constrained-orbit lower bounds imply capacity inequalities on
the 19 distinct nonzero U factors of any rank-19 decomposition.  This script:

1. emits a deterministic CNF asserting a legal profile with at least two
   rank-two 3x2 factors and proves it UNSAT with checked DRAT/LRAT;
2. exhausts the remaining zero/one-rank-two profiles directly; and
3. quotients them under GL(3,2) x GL(2,2).

This classifies first-factor supports only. It does not prove that any support
extends to compatible V/W factors or determine the target tensor rank.
"""

from __future__ import annotations

import argparse
import itertools
import json
import sys
from collections import Counter
from collections.abc import Sequence
from fractions import Fraction
from pathlib import Path
from typing import Any

import pysat
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from evaluators.f2_tensor_rank_sat import (  # noqa: E402
    PROOF_CHECKERS,
    SATEncodingError,
    matrix_rank_2x3,
    load_manifest_encoding,
    require_tool,
    run_command,
    sha256,
    transpose_wang_3x2_mask,
    write_exact,
)
from experiments.f2_234_constraint_profile import (  # noqa: E402
    EXPECTED_SUBSPACES,
    WANG_BTP_SHA256,
    WANG_CERT_SHA256,
    WANG_COMMIT,
    expand_orbit_bounds,
    invertible_matrices,
    parse_orbit_bounds,
    span_nonzero,
    transform_form,
)

SCHEMA = "f2-234-legal-u-profile-orbits-v1"
PROVENANCE_SCHEMA = "f2-234-profile-proof-pair-provenance-v1"
HYPOTHETICAL_RANK = 19
EXPECTED_CANDIDATES = 56_070


class ProfileOrbitError(RuntimeError):
    """Profile CNF, proof replay, enumeration, or orbit quotient failed."""


def rank_classes() -> tuple[tuple[int, ...], tuple[int, ...]]:
    rank_one = tuple(
        form
        for form in range(1, 64)
        if matrix_rank_2x3(transpose_wang_3x2_mask(form)) == 1
    )
    rank_two = tuple(form for form in range(1, 64) if form not in rank_one)
    if (len(rank_one), len(rank_two)) != (21, 42):
        raise ProfileOrbitError(
            f"unexpected 3x2 rank classes {(len(rank_one), len(rank_two))}"
        )
    return rank_one, rank_two


def target_2x3_to_wang_3x2_mask(mask: int) -> int:
    """Invert ``transpose_wang_3x2_mask`` without reusing its source indexing."""

    if mask < 1 or mask >= 1 << 6:
        raise ProfileOrbitError(f"target profile mask must be nonzero six-bit, got {mask}")
    result = 0
    for target_row in range(2):
        for target_column in range(3):
            if (mask >> (3 * target_row + target_column)) & 1:
                result |= 1 << (2 * target_column + target_row)
    return result


def canonical_wang_profile_from_target(u_masks: Sequence[int]) -> tuple[int, ...]:
    """Return the canonical GL(3,2)xGL(2,2) representative of target U masks."""

    if len(u_masks) != HYPOTHETICAL_RANK or len(set(u_masks)) != HYPOTHETICAL_RANK:
        raise ProfileOrbitError("compatibility input must have 19 distinct U masks")
    wang_profile = tuple(sorted(target_2x3_to_wang_3x2_mask(mask) for mask in u_masks))
    return min(
        tuple(sorted(transform_form(form, left, right) for form in wang_profile))
        for left in invertible_matrices(3)
        for right in invertible_matrices(2)
    )


def one_dimensional_capacities() -> tuple[tuple[int, int], ...]:
    """Return and validate the cuts that force all 19 U factors to be distinct."""

    bounds, _, _ = expand_orbit_bounds(parse_orbit_bounds())
    cuts = tuple(
        sorted(
            (subspace[0], HYPOTHETICAL_RANK - lower_bound)
            for subspace, lower_bound in bounds.items()
            if len(subspace) == 1
        )
    )
    if len(cuts) != 63 or tuple(form for form, _ in cuts) != tuple(range(1, 64)):
        raise ProfileOrbitError("one-dimensional Wang cuts do not cover all 63 U forms")
    if any(capacity != 1 for _, capacity in cuts):
        raise ProfileOrbitError("one-dimensional Wang cuts do not force multiplicity one")
    return cuts


def active_capacities() -> list[tuple[int, int, int]]:
    """Return (63-bit subspace mask, capacity, dimension) nontrivial cuts."""

    one_dimensional_capacities()
    bounds, _, _ = expand_orbit_bounds(parse_orbit_bounds())
    active: list[tuple[int, int, int]] = []
    for subspace, lower_bound in bounds.items():
        forms = span_nonzero(subspace)
        capacity = HYPOTHETICAL_RANK - lower_bound
        # One-dimensional cap one is automatic for a set-valued profile.
        if len(forms) > 1 and capacity < len(forms):
            mask = sum(1 << (form - 1) for form in forms)
            active.append((mask, capacity, len(subspace)))
    active.sort()
    if len(active) != 1897:
        raise ProfileOrbitError(f"expected 1897 nontrivial capacities, got {len(active)}")
    return active


def fractional_rank_two_relaxation_report() -> dict[str, Any]:
    """Replay the exact fractional witness blocking a linear-dual proof."""

    rank_one, rank_two = rank_classes()
    rank_two_set = set(rank_two)
    value = Fraction(HYPOTHETICAL_RANK, len(rank_two))
    assignment = {
        form: value if form in rank_two_set else Fraction(0)
        for form in (*rank_one, *rank_two)
    }
    total = sum(assignment.values(), Fraction(0))
    rank_two_objective = sum(
        (assignment[form] for form in rank_two), Fraction(0)
    )
    slacks: list[Fraction] = []
    for subspace_mask, capacity, _ in active_capacities():
        lhs = sum(
            (
                assignment[form]
                for form in range(1, 64)
                if (subspace_mask >> (form - 1)) & 1
            ),
            Fraction(0),
        )
        slack = Fraction(capacity) - lhs
        if slack < 0:
            raise ProfileOrbitError("fractional rank-two witness violates a Wang capacity")
        slacks.append(slack)
    if total != HYPOTHETICAL_RANK or rank_two_objective != HYPOTHETICAL_RANK:
        raise ProfileOrbitError("fractional rank-two witness has the wrong objective")
    return {
        "verdict": "EXACT_FRACTIONAL_OBSTRUCTION",
        "rank_one_value": "0",
        "rank_two_value": f"{value.numerator}/{value.denominator}",
        "sum_x": str(total),
        "rank_two_objective": str(rank_two_objective),
        "checked_capacities": len(slacks),
        "minimum_slack": str(min(slacks)),
        "violated_capacities": 0,
        "interpretation": (
            "The LP relaxation permits rank-two objective 19, so a nonnegative "
            "linear combination of the recorded capacity inequalities cannot "
            "prove the integral at-most-one-rank-two claim."
        ),
    }


def profile_cnf() -> tuple[bytes, dict[str, int]]:
    """CNF for legal profile AND at least two rank-two forms."""

    one_dimensional_capacities()
    _, rank_two = rank_classes()
    bounds, _, _ = expand_orbit_bounds(parse_orbit_bounds())
    pool = IDPool(start_from=64)
    clauses: list[list[int]] = []
    clauses.extend(
        CardEnc.equals(
            list(range(1, 64)),
            bound=HYPOTHETICAL_RANK,
            vpool=pool,
            encoding=EncType.seqcounter,
        ).clauses
    )
    active = 0
    for subspace, lower_bound in sorted(bounds.items()):
        forms = list(span_nonzero(subspace))
        capacity = HYPOTHETICAL_RANK - lower_bound
        if len(forms) > 1 and capacity < len(forms):
            clauses.extend(
                CardEnc.atmost(
                    forms,
                    bound=capacity,
                    vpool=pool,
                    encoding=EncType.seqcounter,
                ).clauses
            )
            active += 1
    clauses.extend(
        CardEnc.atleast(
            list(rank_two), bound=2, vpool=pool, encoding=EncType.seqcounter
        ).clauses
    )
    lines = [f"p cnf {pool.top} {len(clauses)}"]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in clauses)
    return ("\n".join(lines) + "\n").encode(), {
        "variables": pool.top,
        "clauses": len(clauses),
        "active_capacities": active,
    }


def is_legal(profile: Sequence[int], capacities: Sequence[tuple[int, int, int]]) -> bool:
    mask = sum(1 << (form - 1) for form in profile)
    return all((mask & subspace).bit_count() <= capacity for subspace, capacity, _ in capacities)


def enumerate_profiles() -> tuple[set[tuple[int, ...]], int]:
    rank_one, rank_two = rank_classes()
    capacities = active_capacities()
    legal: set[tuple[int, ...]] = set()
    checked = 0
    for selected in itertools.combinations(rank_one, 19):
        checked += 1
        if is_legal(selected, capacities):
            legal.add(tuple(selected))
    for rank_two_form in rank_two:
        for selected_rank_one in itertools.combinations(rank_one, 18):
            checked += 1
            selected = tuple(sorted((*selected_rank_one, rank_two_form)))
            if is_legal(selected, capacities):
                legal.add(selected)
    if checked != EXPECTED_CANDIDATES:
        raise ProfileOrbitError(f"checked {checked} candidates, expected {EXPECTED_CANDIDATES}")
    return legal, checked


def quotient_profiles(
    profiles: set[tuple[int, ...]],
) -> list[dict[str, Any]]:
    rank_one, rank_two = rank_classes()
    rank_two_set = set(rank_two)
    group = [
        (left, right)
        for left in invertible_matrices(3)
        for right in invertible_matrices(2)
    ]
    if len(group) != 1008:
        raise ProfileOrbitError(f"unexpected group size {len(group)}")
    unseen = set(profiles)
    orbits: list[dict[str, Any]] = []
    while unseen:
        seed = min(unseen)
        images = {
            tuple(sorted(transform_form(form, left, right) for form in seed))
            for left, right in group
        }
        if not images <= profiles:
            raise ProfileOrbitError("legal profile set is not group-invariant")
        representative = min(images)
        unseen -= images
        target_u = sorted(transpose_wang_3x2_mask(form) for form in representative)
        orbits.append(
            {
                "representative_wang_3x2": list(representative),
                "representative_target_2x3": target_u,
                "orbit_size": len(images),
                "rank_two_forms_wang": [form for form in representative if form in rank_two_set],
                "omitted_rank_one_forms_wang": [
                    form for form in rank_one if form not in representative
                ],
            }
        )
    orbits.sort(key=lambda orbit: orbit["representative_wang_3x2"])
    for index, orbit in enumerate(orbits):
        orbit["orbit_index"] = index
    if sum(orbit["orbit_size"] for orbit in orbits) != len(profiles):
        raise ProfileOrbitError("orbit sizes do not partition legal profiles")
    return orbits


def classification() -> dict[str, Any]:
    profiles, checked = enumerate_profiles()
    _, rank_two = rank_classes()
    rank_two_set = set(rank_two)
    distribution = Counter(
        sum(form in rank_two_set for form in profile) for profile in profiles
    )
    orbits = quotient_profiles(profiles)
    if len(profiles) != 252 or distribution != Counter({0: 210, 1: 42}):
        raise ProfileOrbitError(
            f"unexpected legal profile census {len(profiles)}, {dict(distribution)}"
        )
    if len(orbits) != 4:
        raise ProfileOrbitError(f"expected four profile orbits, got {len(orbits)}")
    return {
        "distinctness_scope": {
            "one_dimensional_cuts": len(one_dimensional_capacities()),
            "capacity_per_nonzero_u_form": 1,
            "consequence": "every hypothetical rank-19 U factor is nonzero and appears at most once",
        },
        "checked_profiles_with_at_most_one_rank_two": checked,
        "legal_profiles": len(profiles),
        "legal_by_rank_two_count": {
            str(count): total for count, total in sorted(distribution.items())
        },
        "group": "GL(3,2) x GL(2,2)",
        "group_order": 1008,
        "orbit_count": len(orbits),
        "orbits": orbits,
    }


def tool_metadata(path: Path) -> dict[str, Any]:
    version = run_command([str(path), "--version"], 30)
    return {
        "path": str(path),
        "sha256": sha256(path),
        "version": version.stdout.splitlines()[0] if version.stdout else "unknown",
    }


def verify_proof_pair_provenance(manifest_path: Path) -> dict[str, Any]:
    """Check the recorded proof-pair bytes without claiming proof replay."""

    manifest = json.loads(manifest_path.read_text())
    if manifest.get("schema") != PROVENANCE_SCHEMA:
        raise ProfileOrbitError("unexpected proof-pair provenance schema")
    files = manifest.get("files")
    if not isinstance(files, dict):
        raise ProfileOrbitError("proof-pair provenance has no files map")
    expected_cnf, dimensions = profile_cnf()
    observed: dict[str, dict[str, Any]] = {}
    for key in ("cnf", "drat", "lrat"):
        entry = files.get(key)
        if not isinstance(entry, dict):
            raise ProfileOrbitError(f"proof-pair provenance has no {key} entry")
        path = Path(entry["path"])
        if not path.is_absolute():
            path = ROOT / path
        if not path.is_file():
            raise ProfileOrbitError(f"missing recorded {key} file: {path}")
        actual_bytes = path.stat().st_size
        actual_sha256 = sha256(path)
        if actual_bytes != entry.get("bytes"):
            raise ProfileOrbitError(
                f"{key} byte-count mismatch: {actual_bytes} != {entry.get('bytes')}"
            )
        if actual_sha256 != entry.get("sha256"):
            raise ProfileOrbitError(f"{key} SHA-256 mismatch")
        observed[key] = {
            "path": str(path),
            "bytes": actual_bytes,
            "sha256": actual_sha256,
        }
    cnf_path = Path(observed["cnf"]["path"])
    if cnf_path.read_bytes() != expected_cnf:
        raise ProfileOrbitError("recorded CNF does not reproduce byte-for-byte")
    return {
        "verdict": "PROVENANCE_VERIFIED_REPLAY_PENDING",
        "manifest": str(manifest_path),
        "cnf_dimensions": dimensions,
        "files": observed,
    }


def verify_compatibility_inputs(manifest_paths: Sequence[Path]) -> dict[str, Any]:
    """Check that four exact SAT inputs cover the four classified U orbits."""

    if len(manifest_paths) != 4:
        raise ProfileOrbitError("expected exactly four compatibility manifests")
    expected_orbits = {
        tuple(orbit["representative_wang_3x2"]): orbit["orbit_index"]
        for orbit in classification()["orbits"]
    }
    observed_orbits: set[tuple[int, ...]] = set()
    cases: list[dict[str, Any]] = []
    for manifest_path in manifest_paths:
        try:
            manifest, encoding, cnf_path = load_manifest_encoding(manifest_path)
        except SATEncodingError as error:
            raise ProfileOrbitError(
                f"compatibility manifest failed exact regeneration: {manifest_path}: {error}"
            ) from error
        if (
            encoding.shape != (2, 3, 4)
            or encoding.rank != HYPOTHETICAL_RANK
            or not encoding.native_xor
            or not encoding.canonicalize_w_top_glc
            or not encoding.projected_slice_span
            or encoding.fixed_u_masks is None
            or encoding.fixed_w0_mask is not None
        ):
            raise ProfileOrbitError(
                f"compatibility manifest lacks an exhaustive strengthened target case: {manifest_path}"
            )
        representative = canonical_wang_profile_from_target(encoding.fixed_u_masks)
        if representative not in expected_orbits:
            raise ProfileOrbitError(
                f"compatibility manifest is outside the classified U orbits: {manifest_path}"
            )
        if representative in observed_orbits:
            raise ProfileOrbitError(
                f"duplicate compatibility U orbit: {manifest_path}"
            )
        observed_orbits.add(representative)
        cases.append(
            {
                "manifest": str(manifest_path),
                "orbit_index": expected_orbits[representative],
                "representative_wang_3x2": list(representative),
                "cnf": {
                    "path": str(cnf_path),
                    "sha256": manifest["cnf"]["sha256"],
                    "variables": encoding.builder.variable_count,
                    "clauses": len(encoding.builder.clauses),
                    "xor_constraints": len(encoding.xor_constraints),
                    "byte_reproduces": True,
                },
            }
        )
    if observed_orbits != set(expected_orbits):
        raise ProfileOrbitError("compatibility manifests do not cover all four U orbits")
    cases.sort(key=lambda case: case["orbit_index"])
    return {
        "verdict": "FOUR_EXHAUSTIVE_INPUTS_VERIFIED",
        "case_count": len(cases),
        "cases": cases,
        "scope": (
            "Input coverage only. No SAT model or UNSAT proof has been produced for "
            "the four target cases."
        ),
    }


def build_packet(output_dir: Path, timeout: int, force: bool) -> Path:
    output_dir.mkdir(parents=True, exist_ok=True)
    cnf_path = output_dir / "at-least-two-rank2.cnf"
    drat_path = output_dir / "proof.drat"
    lrat_path = output_dir / "proof.lrat"
    artifact_path = output_dir / "profile-orbits.json"
    cnf, dimensions = profile_cnf()
    write_exact(cnf_path, cnf, force)
    cadical = require_tool("cadical")
    kissat = require_tool("kissat")
    drat_trim = require_tool(PROOF_CHECKERS / "drat-trim")
    lrat_check = require_tool(PROOF_CHECKERS / "lrat-check")
    proof_reused = drat_path.is_file() and lrat_path.is_file()
    if proof_reused:
        checked = run_command(
            [str(drat_trim), str(cnf_path), str(drat_path)], timeout
        )
        if checked.returncode != 0 or "s VERIFIED" not in checked.stdout:
            raise ProfileOrbitError(
                f"existing DRAT replay failed:\n{checked.stdout[-2000:]}"
            )
    else:
        if drat_path.exists() or lrat_path.exists():
            raise ProfileOrbitError("incomplete existing proof pair; refusing to overwrite")
        solved = run_command(
            [
                str(cadical),
                "--seed=0",
                "--unsat",
                "--no-binary",
                str(cnf_path),
                str(drat_path),
            ],
            timeout,
        )
        if solved.returncode != 20 or "UNSATISFIABLE" not in solved.stdout:
            raise ProfileOrbitError(
                f"CaDiCaL did not prove profile CNF UNSAT:\n{solved.stdout[-2000:]}"
            )
        checked = run_command(
            [str(drat_trim), str(cnf_path), str(drat_path), "-L", str(lrat_path)],
            timeout,
        )
        if checked.returncode != 0 or "s VERIFIED" not in checked.stdout:
            raise ProfileOrbitError(f"DRAT replay failed:\n{checked.stdout[-2000:]}")
    lrat_result = run_command([str(lrat_check), str(cnf_path), str(lrat_path)], timeout)
    if lrat_result.returncode != 0 or "VERIFIED" not in lrat_result.stdout.upper():
        raise ProfileOrbitError(f"LRAT replay failed:\n{lrat_result.stdout[-2000:]}")
    try:
        independent = run_command(
            [str(kissat), "--seed=0", "--unsat", str(cnf_path)],
            min(timeout, 60),
        )
        independent_status = (
            "UNSATISFIABLE"
            if independent.returncode == 20 and "UNSATISFIABLE" in independent.stdout
            else f"UNRESOLVED_RETURN_{independent.returncode}"
        )
    except SATEncodingError as error:
        independent_status = f"UNKNOWN_TIMEOUT: {error}"
    artifact = {
        "schema": SCHEMA,
        "source": {
            "wang_commit": WANG_COMMIT,
            "certificate_sha256": WANG_CERT_SHA256,
            "btp_sha256": WANG_BTP_SHA256,
            "subspaces": EXPECTED_SUBSPACES,
        },
        "claim": (
            "Every 19-form U support satisfying all pinned Wang n324 capacity "
            "inequalities contains at most one rank-two 3x2 form; the remaining "
            "supports comprise exactly 252 profiles in four symmetry orbits."
        ),
        "max_rank_two_proof": {
            "assertion": "legal profile with at least two rank-two forms is UNSAT",
            "cnf": {"path": str(cnf_path), "sha256": sha256(cnf_path), **dimensions},
            "drat": {"path": str(drat_path), "sha256": sha256(drat_path)},
            "lrat": {"path": str(lrat_path), "sha256": sha256(lrat_path)},
            "cadical_unsat": True,
            "drat_verified": True,
            "lrat_verified": True,
            "proof_reused_after_fresh_replay": proof_reused,
            "kissat_status": independent_status,
        },
        "classification": classification(),
        "tools": {
            "python_sat_version": pysat.__version__,
            "cadical": tool_metadata(cadical),
            "kissat": tool_metadata(kissat),
            "drat_trim": tool_metadata(drat_trim),
            "lrat_check": tool_metadata(lrat_check),
        },
        "interpretation": (
            "This is a complete first-factor support classification only. It does "
            "not establish compatible V/W factors or determine the tensor rank."
        ),
    }
    write_exact(
        artifact_path,
        (json.dumps(artifact, indent=2, sort_keys=True) + "\n").encode(),
        force,
    )
    return artifact_path


def verify_packet(artifact_path: Path, timeout: int) -> dict[str, Any]:
    artifact = json.loads(artifact_path.read_text())
    if artifact.get("schema") != SCHEMA:
        raise ProfileOrbitError("unexpected artifact schema")
    proof = artifact["max_rank_two_proof"]
    cnf_path = Path(proof["cnf"]["path"])
    drat_path = Path(proof["drat"]["path"])
    lrat_path = Path(proof["lrat"]["path"])
    expected_cnf, dimensions = profile_cnf()
    if cnf_path.read_bytes() != expected_cnf or sha256(cnf_path) != proof["cnf"]["sha256"]:
        raise ProfileOrbitError("profile CNF does not reproduce exactly")
    for key, expected in dimensions.items():
        if proof["cnf"].get(key) != expected:
            raise ProfileOrbitError(f"profile CNF dimension mismatch for {key}")
    if sha256(drat_path) != proof["drat"]["sha256"]:
        raise ProfileOrbitError("DRAT hash mismatch")
    if sha256(lrat_path) != proof["lrat"]["sha256"]:
        raise ProfileOrbitError("LRAT hash mismatch")
    drat_trim = require_tool(PROOF_CHECKERS / "drat-trim")
    lrat_check = require_tool(PROOF_CHECKERS / "lrat-check")
    checked = run_command([str(drat_trim), str(cnf_path), str(drat_path)], timeout)
    if checked.returncode != 0 or "s VERIFIED" not in checked.stdout:
        raise ProfileOrbitError("fresh DRAT replay failed")
    lrat_result = run_command([str(lrat_check), str(cnf_path), str(lrat_path)], timeout)
    if lrat_result.returncode != 0 or "VERIFIED" not in lrat_result.stdout.upper():
        raise ProfileOrbitError("fresh LRAT replay failed")
    exact_classification = classification()
    if artifact.get("classification") != exact_classification:
        raise ProfileOrbitError("profile classification does not reproduce")
    return {
        "verdict": "VERIFIED",
        "legal_profiles": exact_classification["legal_profiles"],
        "orbit_count": exact_classification["orbit_count"],
        "max_rank_two": 1,
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    build_parser = subparsers.add_parser("build", help="build the checked profile packet")
    build_parser.add_argument("--output-dir", type=Path, required=True)
    build_parser.add_argument("--timeout", type=int, default=300)
    build_parser.add_argument("--force", action="store_true")
    verify_parser = subparsers.add_parser("verify", help="freshly replay a profile packet")
    verify_parser.add_argument("--artifact", type=Path, required=True)
    verify_parser.add_argument("--timeout", type=int, default=300)
    provenance_parser = subparsers.add_parser(
        "verify-provenance",
        help="check recorded proof-pair hashes and deterministic CNF bytes",
    )
    provenance_parser.add_argument("--manifest", type=Path, required=True)
    inputs_parser = subparsers.add_parser(
        "verify-compatibility-inputs",
        help="regenerate four SAT inputs and match them to the four U orbits",
    )
    inputs_parser.add_argument("--manifests", type=Path, nargs="+", required=True)
    subparsers.add_parser(
        "check-linear-relaxation",
        help="verify the exact fractional witness blocking a linear-dual proof",
    )
    args = parser.parse_args(argv)
    try:
        if hasattr(args, "timeout") and args.timeout < 1:
            raise ProfileOrbitError("timeout must be positive")
        if args.command == "build":
            artifact = build_packet(args.output_dir, args.timeout, args.force)
            print(f"PROFILE_PACKET_PASS: artifact={artifact}")
            return 0
        if args.command == "verify-provenance":
            print(json.dumps(verify_proof_pair_provenance(args.manifest), indent=2, sort_keys=True))
            return 0
        if args.command == "verify-compatibility-inputs":
            print(json.dumps(verify_compatibility_inputs(args.manifests), indent=2, sort_keys=True))
            return 0
        if args.command == "check-linear-relaxation":
            print(json.dumps(fractional_rank_two_relaxation_report(), indent=2, sort_keys=True))
            return 0
        result = verify_packet(args.artifact, args.timeout)
        print(json.dumps(result, indent=2, sort_keys=True))
        return 0
    except (OSError, ValueError, KeyError, ProfileOrbitError) as error:
        print(f"BROKEN: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
