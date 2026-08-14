import unittest
from pathlib import Path

from formal.verify import LeanBackend


ROOT = Path(__file__).resolve().parent.parent
PROOF = ROOT / "formal/lean_project/LeanProject/DynamicMoeLowerBound.lean"
STATEMENT = """theorem competitive_factor_lower_bound_at_least_one
    (k : ℕ) (Γ : ℝ) (hupper : HasCompetitiveUpperForK k Γ) : 1 ≤ Γ"""


class TestDynamicMoeLowerBoundFormal(unittest.TestCase):
    def test_universal_constant_lower_bound_passes_lean_backend(self):
        evidence = LeanBackend().check(STATEMENT, str(PROOF))
        self.assertEqual(evidence["backend"], "lean")
        self.assertEqual(
            evidence["declaration"],
            "DynamicMoeSemantics.competitive_factor_lower_bound_at_least_one",
        )
        self.assertEqual(
            set(evidence["axioms"]), {"propext", "Classical.choice", "Quot.sound"}
        )


if __name__ == "__main__":
    unittest.main()
