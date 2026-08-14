import unittest
from pathlib import Path

from formal.verify import LeanBackend


ROOT = Path(__file__).resolve().parent.parent
PROOF = ROOT / "formal/lean_project/LeanProject/DynamicMoeSemantics.lean"
STATEMENT = """theorem uniform_constant_upper_of_interfaces
    (C : ℝ) (hC : 1 ≤ C)
    (hpositive : HasPositiveBodyFractionalReduction C)
    (hrounding : HasLazyThresholdRounding) :
    HasUniformConstantUpper"""

BALANCED_MAP_STATEMENT = """theorem balanced_map_one_lipschitz {m k : ℕ}
    (first second : AugmentedAllocation m k) (hm : 0 < m) :
    fractionalMovement (first.toBalancedFractional hm)
        (second.toBalancedFractional hm) ≤
      ∑ i, |first.value i - second.value i|"""

BALANCED_SERVICE_STATEMENT = """theorem balanced_map_service_loss_eight_thirds {m k : ℕ}
    (request : Workload m) (allocation : AugmentedAllocation m k)
    (hm : 0 < m) (height : ℝ) (hheight : 0 ≤ height)
    (henvelope : ∀ i : Fin m,
      (3 / 4 : ℝ) *
          (request.value i / (1 + allocation.value i)) ≤ height) :
    fractionalLatency request (allocation.toBalancedFractional hm) ≤
      (8 / 3 : ℝ) * height"""


class TestDynamicMoeSemanticsFormal(unittest.TestCase):
    def test_balanced_exact_budget_map_is_one_lipschitz(self):
        evidence = LeanBackend().check(BALANCED_MAP_STATEMENT, str(PROOF))
        self.assertEqual(evidence["backend"], "lean")
        self.assertEqual(
            evidence["declaration"],
            "DynamicMoeSemantics.balanced_map_one_lipschitz",
        )
        self.assertEqual(
            set(evidence["axioms"]), {"propext", "Classical.choice", "Quot.sound"}
        )

    def test_balanced_exact_budget_map_preserves_service_with_constant_loss(self):
        evidence = LeanBackend().check(BALANCED_SERVICE_STATEMENT, str(PROOF))
        self.assertEqual(evidence["backend"], "lean")
        self.assertEqual(
            evidence["declaration"],
            "DynamicMoeSemantics.balanced_map_service_loss_eight_thirds",
        )
        self.assertEqual(
            set(evidence["axioms"]), {"propext", "Classical.choice", "Quot.sound"}
        )

    def test_all_parameter_semantic_reduction_passes_lean_backend(self):
        evidence = LeanBackend().check(STATEMENT, str(PROOF))
        self.assertEqual(evidence["backend"], "lean")
        self.assertEqual(
            evidence["declaration"],
            "DynamicMoeSemantics.uniform_constant_upper_of_interfaces",
        )
        self.assertEqual(
            set(evidence["axioms"]), {"propext", "Classical.choice", "Quot.sound"}
        )


if __name__ == "__main__":
    unittest.main()
