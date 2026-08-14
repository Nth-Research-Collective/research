import LeanProject.DynamicMoeLazyThresholdInterface
import LeanProject.DynamicMoeLowerBound
import LeanProject.DynamicMoePositiveBodyReduction

/-!
Main theorem packet for the original Dynamic MoE Serving primal problem.
The two premises are exact primitive formal boundaries for the cited positive-
body chaser and Lazy Threshold Rounding theorems. Every MoE-specific reduction,
cost bridge, quantifier, expectation, additive term, and lower bound is proved
inside the repository.
-/

namespace DynamicMoeMain

open DynamicMoeSemantics
open DynamicMoePositiveBodyInterface
open DynamicMoePositiveBodyReduction
open DynamicMoeLazyThresholdInterface

/-- A horizon-independent absolute randomized upper bound, together with the
unconditional factor-one lower bound for every replica budget. This is the
formal `Theta(1)` statement. -/
def HasTightConstantRandomizedCompetitiveRatio : Prop :=
  HasUniformConstantUpper ∧
    ∀ k : ℕ, ∀ Γ : ℝ, HasCompetitiveUpperForK k Γ → 1 ≤ Γ

theorem dynamicMoe_randomized_theta_one_of_source_theorems
    (C : ℝ) (hC : 1 ≤ C)
    (hpositiveBody : HasTwoSparsePositiveBodyChaser.{0} C)
    (hlazyThreshold : HasLazyThresholdRoundingPrimitive) :
    HasTightConstantRandomizedCompetitiveRatio := by
  refine ⟨?_, ?_⟩
  · exact uniform_constant_upper_of_interfaces C hC
      (hasPositiveBodyFractionalReduction_of_twoSparseChaser hpositiveBody)
      (hasLazyThresholdRounding_of_primitive hlazyThreshold)
  · intro k Γ hupper
    exact competitive_factor_lower_bound_at_least_one k Γ hupper

/-- The explicit upper constant and additive term proved by the construction. -/
theorem dynamicMoe_explicit_constant_upper_of_source_theorems
    (C : ℝ) (hC : 1 ≤ C)
    (hpositiveBody : HasTwoSparsePositiveBodyChaser.{0} C)
    (hlazyThreshold : HasLazyThresholdRoundingPrimitive) :
    ∀ k : ℕ, 1 ≤ k → HasCompetitiveUpperForK k (10 * C) := by
  let hpositive :=
    hasPositiveBodyFractionalReduction_of_twoSparseChaser hpositiveBody
  let hrounding := hasLazyThresholdRounding_of_primitive hlazyThreshold
  let hwitness := has_reduction_witness_of_interfaces C hpositive hrounding
  intro k hk m hm
  refine ⟨(5 * C + 2) * k + 16, ?_, ?_⟩
  · positivity
  · intro initial
    obtain ⟨witness⟩ := hwitness k hk m hm initial
    refine ⟨witness.algorithm, witness.integrableCost, ?_⟩
    intro requests
    have hfive :
        witness.algorithm.expectedCost initial requests ≤
          5 * witness.bodyMovement requests + 2 * k + 16 := by
      linarith [witness.movementBridge requests,
        witness.serviceBridge requests, witness.roundingBridge requests]
    have hbody :
        5 * witness.bodyMovement requests ≤
          5 * (C * ((k : ℝ) + 2 * offlineOpt initial requests)) := by
      linarith [witness.bodyBound requests]
    calc
      witness.algorithm.expectedCost initial requests
          ≤ 5 * witness.bodyMovement requests + 2 * k + 16 := hfive
      _ ≤ 5 * (C * ((k : ℝ) + 2 * offlineOpt initial requests)) +
          2 * k + 16 := by linarith
      _ = 10 * C * offlineOpt initial requests +
          ((5 * C + 2) * k + 16) := by ring

end DynamicMoeMain
