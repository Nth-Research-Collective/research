import unittest
from pathlib import Path

from formal.verify import LeanBackend


ROOT = Path(__file__).resolve().parent.parent
PROOF = ROOT / "formal/lean_project/LeanProject/DynamicMoePositiveBody.lean"
STATEMENT = """theorem integral_competitive_from_positive_body
    (C k opt M movement service integralCost : ℝ)
    (hbody : M ≤ C * (k + 2 * opt))
    (hmovement : movement ≤ M + 2 * k)
    (hservice : service ≤ (4 / 3 : ℝ) * M + 16 / 3)
    (hround : integralCost ≤ movement + 3 * service) :
    integralCost ≤ 10 * C * opt + (5 * C + 2) * k + 16"""

GRID_STATEMENT = """theorem finite_grid_tangent_captures_three_quarters
    (r q k : ℝ) (hr : 0 ≤ r) (hq : 1 ≤ q) (hqk : q ≤ 1 + 2 * k) :
    ∃ n : ℕ,
      (3 / 2 : ℝ) ^ n ≤ 1 + 2 * k ∧
      (3 / 4 : ℝ) * (r / q) ≤
        r * (2 * (3 / 2 : ℝ) ^ n - q) / ((3 / 2 : ℝ) ^ n) ^ 2"""

RESET_STATEMENT = """theorem shrinking_reset_charges_moe_service
    (s previous following δPrevious δFollowing : ℝ)
    (hprevious : previous ≤ 2 * δPrevious)
    (hfollowing : following ≤ 2 * δFollowing) :
    (8 / 3 : ℝ) * s ≤
      (4 / 3 : ℝ) * (|s - previous| + |s - following|) +
        (8 / 3 : ℝ) * (δPrevious + δFollowing)"""


class TestDynamicMoePositiveBodyFormal(unittest.TestCase):
    def test_reduction_assembly_passes_lean_backend(self):
        evidence = LeanBackend().check(STATEMENT, str(PROOF))
        self.assertEqual(evidence["backend"], "lean")
        self.assertIn("integral_competitive_from_positive_body", evidence["statement"])

    def test_finite_geometric_grid_passes_lean_backend(self):
        evidence = LeanBackend().check(GRID_STATEMENT, str(PROOF))
        self.assertEqual(evidence["backend"], "lean")
        self.assertIn("finite_grid_tangent_captures_three_quarters", evidence["statement"])

    def test_shrinking_reset_service_charge_passes_lean_backend(self):
        evidence = LeanBackend().check(RESET_STATEMENT, str(PROOF))
        self.assertEqual(evidence["backend"], "lean")
        self.assertIn("shrinking_reset_charges_moe_service", evidence["statement"])


if __name__ == "__main__":
    unittest.main()
