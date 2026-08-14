"""Emit the Lean dependency/axiom packet for the Dynamic MoE reduction."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

from formal.verify import LeanBackend


ROOT = Path(__file__).resolve().parent.parent
PROOF = ROOT / "formal/lean_project/LeanProject/DynamicMoePositiveBody.lean"
SEMANTICS_PROOF = ROOT / "formal/lean_project/LeanProject/DynamicMoeSemantics.lean"
LOWER_PROOF = ROOT / "formal/lean_project/LeanProject/DynamicMoeLowerBound.lean"
POSITIVE_REDUCTION_PROOF = (
    ROOT / "formal/lean_project/LeanProject/DynamicMoePositiveBodyReduction.lean"
)
ROUNDING_INTERFACE_PROOF = (
    ROOT / "formal/lean_project/LeanProject/DynamicMoeLazyThresholdInterface.lean"
)
MAIN_PROOF = ROOT / "formal/lean_project/LeanProject/DynamicMoeMain.lean"


def _portable_check(check: dict[str, object]) -> dict[str, object]:
    """Remove machine-local metadata without weakening the proof evidence."""

    portable = dict(check)
    proof_file = Path(str(portable["proof_file"])).resolve()
    try:
        portable["proof_file"] = proof_file.relative_to(ROOT).as_posix()
    except ValueError as exc:
        raise AssertionError(f"proof file escapes repository root: {proof_file}") from exc

    raw_version = str(portable["lean_version"])
    match = re.fullmatch(
        r"Lean \(version ([^,]+), .+?, commit ([0-9a-f]+), ([^)]+)\)",
        raw_version,
    )
    if match is None:
        raise AssertionError(f"unrecognized Lean version string: {raw_version}")
    version, commit, build = match.groups()
    portable["lean_version"] = (
        f"Lean (version {version}, commit {commit}, {build})"
    )
    return portable


def _check(statement: str, proof: Path) -> dict[str, object]:
    return _portable_check(LeanBackend().check(statement, str(proof)))

STATEMENTS = {
    "finite_tangent_grid": """theorem finite_grid_tangent_captures_three_quarters
    (r q k : ℝ) (hr : 0 ≤ r) (hq : 1 ≤ q) (hqk : q ≤ 1 + 2 * k) :
    ∃ n : ℕ,
      (3 / 2 : ℝ) ^ n ≤ 1 + 2 * k ∧
      (3 / 4 : ℝ) * (r / q) ≤
        r * (2 * (3 / 2 : ℝ) ^ n - q) / ((3 / 2 : ℝ) ^ n) ^ 2""",
    "integer_tangent_grid": """theorem integer_grid_tangent_captures_three_quarters
    (r q : ℝ) (k : ℕ) (hr : 0 ≤ r) (hq : 1 ≤ q)
    (hqk : q ≤ 1 + 2 * k) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 1 + 2 * k ∧
      (3 / 4 : ℝ) * (r / q) ≤
        r * (2 * (n : ℝ) - q) / (n : ℝ) ^ 2""",
    "shrinking_reset": """theorem shrinking_reset_charges_moe_service
    (s previous following δPrevious δFollowing : ℝ)
    (hprevious : previous ≤ 2 * δPrevious)
    (hfollowing : following ≤ 2 * δFollowing) :
    (8 / 3 : ℝ) * s ≤
      (4 / 3 : ℝ) * (|s - previous| + |s - following|) +
        (8 / 3 : ℝ) * (δPrevious + δFollowing)""",
    "competitive_assembly": """theorem integral_competitive_from_positive_body
    (C k opt M movement service integralCost : ℝ)
    (hbody : M ≤ C * (k + 2 * opt))
    (hmovement : movement ≤ M + 2 * k)
    (hservice : service ≤ (4 / 3 : ℝ) * M + 16 / 3)
    (hround : integralCost ≤ movement + 3 * service) :
    integralCost ≤ 10 * C * opt + (5 * C + 2) * k + 16""",
}

SEMANTIC_STATEMENT = """theorem uniform_constant_upper_of_interfaces
    (C : ℝ) (hC : 1 ≤ C)
    (hpositive : HasPositiveBodyFractionalReduction C)
    (hrounding : HasLazyThresholdRounding) :
    HasUniformConstantUpper"""

LOWER_STATEMENT = """theorem competitive_factor_lower_bound_at_least_one
    (k : ℕ) (Γ : ℝ) (hupper : HasCompetitiveUpperForK k Γ) : 1 ≤ Γ"""

POSITIVE_REDUCTION_STATEMENT = """theorem hasPositiveBodyFractionalReduction_of_twoSparseChaser {C : ℝ}
    (hchaser : HasTwoSparsePositiveBodyChaser.{0} C) :
    HasPositiveBodyFractionalReduction C"""

POSITIVE_SOURCE_COMPATIBILITY_STATEMENT = """theorem eventResetBodies_packing_positive_rightHandSide {m k : ℕ}
    (requests : List (Workload m)) :
    ∀ body ∈ eventResetBodies (m := m) (k := k) requests,
      body.PackingPositiveRightHandSide"""

ROUNDING_ADAPTER_STATEMENT = """theorem hasLazyThresholdRounding_of_primitive
    (hprimitive : HasLazyThresholdRoundingPrimitive) :
    HasLazyThresholdRounding"""

ROUNDING_SUMMATION_STATEMENT = """theorem expectedMovement_of_expectedStepMovement {m k : ℕ}
    {initial : IntegralAllocation m k}
    {fractional : FractionalOnlineAlgorithm m k}
    (witness : LazyThresholdRoundingWitness m k initial fractional)
    (requests : List (Workload m)) : by
    letI : MeasurableSpace witness.algorithm.Seed :=
      witness.algorithm.measurableSeed
    exact (∫ seed, realizedIntegralMovement witness.algorithm initial requests seed
      ∂witness.algorithm.seedMeasure) ≤ fractional.movementCost initial requests"""

MAIN_THETA_STATEMENT = """theorem dynamicMoe_randomized_theta_one_of_source_theorems
    (C : ℝ) (hC : 1 ≤ C)
    (hpositiveBody : HasTwoSparsePositiveBodyChaser.{0} C)
    (hlazyThreshold : HasLazyThresholdRoundingPrimitive) :
    HasTightConstantRandomizedCompetitiveRatio"""

MAIN_EXPLICIT_STATEMENT = """theorem dynamicMoe_explicit_constant_upper_of_source_theorems
    (C : ℝ) (hC : 1 ≤ C)
    (hpositiveBody : HasTwoSparsePositiveBodyChaser.{0} C)
    (hlazyThreshold : HasLazyThresholdRoundingPrimitive) :
    ∀ k : ℕ, 1 ≤ k → HasCompetitiveUpperForK k (10 * C)"""


def formal_report() -> dict[str, object]:
    algebra_checks = {
        name: _check(statement, PROOF)
        for name, statement in STATEMENTS.items()
    }
    proof_hashes = {check["proof_sha256"] for check in algebra_checks.values()}
    if len(proof_hashes) != 1:
        raise AssertionError("formal checks did not use one identical proof file")
    semantic_check = _check(SEMANTIC_STATEMENT, SEMANTICS_PROOF)
    lower_check = _check(LOWER_STATEMENT, LOWER_PROOF)
    positive_reduction_check = _check(
        POSITIVE_REDUCTION_STATEMENT, POSITIVE_REDUCTION_PROOF
    )
    positive_source_compatibility_check = _check(
        POSITIVE_SOURCE_COMPATIBILITY_STATEMENT, POSITIVE_REDUCTION_PROOF
    )
    rounding_adapter_check = _check(
        ROUNDING_ADAPTER_STATEMENT, ROUNDING_INTERFACE_PROOF
    )
    rounding_summation_check = _check(
        ROUNDING_SUMMATION_STATEMENT, ROUNDING_INTERFACE_PROOF
    )
    main_checks = {
        "randomized_theta_one": _check(
            MAIN_THETA_STATEMENT, MAIN_PROOF
        ),
        "explicit_constant_upper": _check(
            MAIN_EXPLICIT_STATEMENT, MAIN_PROOF
        ),
    }
    main_hashes = {check["proof_sha256"] for check in main_checks.values()}
    if len(main_hashes) != 1:
        raise AssertionError("main checks did not use one identical proof file")
    return {
        "verdict": "DYNAMIC_MOE_FORMAL_MAIN_PASS",
        "scope": (
            "Finite tangent-grid existence, shrinking-reset service charge, final cost "
            "assembly, causal fractional and randomized integral semantics, a concrete "
            "event/reset reduction from the primitive two-sparse positive-body chaser, "
            "a shared-seed path-level Lazy Threshold Rounding adapter, the explicit "
            "10*C upper bound, and the tight randomized Theta(1) theorem. The two "
            "primitive premises are exact formal boundaries for the cited source "
            "theorems; all Dynamic MoE bridges and the factor-one lower bound are proved."
        ),
        "algebra_proof_sha256": proof_hashes.pop(),
        "semantic_proof_sha256": semantic_check["proof_sha256"],
        "lower_proof_sha256": lower_check["proof_sha256"],
        "positive_reduction_proof_sha256": positive_reduction_check["proof_sha256"],
        "rounding_interface_proof_sha256": rounding_adapter_check["proof_sha256"],
        "main_proof_sha256": main_hashes.pop(),
        "algebra_checks": algebra_checks,
        "semantic_check": semantic_check,
        "lower_check": lower_check,
        "positive_reduction_check": positive_reduction_check,
        "positive_source_compatibility_check": positive_source_compatibility_check,
        "rounding_adapter_check": rounding_adapter_check,
        "rounding_summation_check": rounding_summation_check,
        "main_checks": main_checks,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    arguments = parser.parse_args()
    report = formal_report()
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if arguments.output is None:
        print(rendered, end="")
    else:
        arguments.output.parent.mkdir(parents=True, exist_ok=True)
        arguments.output.write_text(rendered, encoding="utf-8")
        print(f"PASS: wrote {arguments.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
