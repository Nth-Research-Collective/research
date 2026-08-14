import unittest
from pathlib import Path

from evaluators.dynamic_moe_formal_eval import formal_report


class TestDynamicMoeFormalEval(unittest.TestCase):
    def test_formal_packet_has_one_clean_dependency_surface(self):
        report = formal_report()
        self.assertEqual(report["verdict"], "DYNAMIC_MOE_FORMAL_MAIN_PASS")
        self.assertEqual(len(report["algebra_proof_sha256"]), 64)
        self.assertEqual(len(report["semantic_proof_sha256"]), 64)
        self.assertEqual(len(report["lower_proof_sha256"]), 64)
        self.assertEqual(len(report["positive_reduction_proof_sha256"]), 64)
        self.assertEqual(len(report["rounding_interface_proof_sha256"]), 64)
        self.assertEqual(len(report["main_proof_sha256"]), 64)
        self.assertEqual(set(report["algebra_checks"]), {
            "finite_tangent_grid",
            "integer_tangent_grid",
            "shrinking_reset",
            "competitive_assembly",
        })
        for check in [
            *report["algebra_checks"].values(),
            report["semantic_check"],
            report["lower_check"],
            report["positive_reduction_check"],
            report["positive_source_compatibility_check"],
            report["rounding_adapter_check"],
            report["rounding_summation_check"],
            *report["main_checks"].values(),
        ]:
            self.assertEqual(check["backend"], "lean")
            self.assertFalse(Path(check["proof_file"]).is_absolute())
            self.assertNotIn("apple-darwin", check["lean_version"])
            self.assertRegex(
                check["lean_version"],
                r"^Lean \(version 4\.32\.2, commit [0-9a-f]+, Release\)$",
            )
            self.assertEqual(
                set(check["axioms"]), {"propext", "Classical.choice", "Quot.sound"}
            )
        self.assertEqual(
            report["semantic_check"]["declaration"],
            "DynamicMoeSemantics.uniform_constant_upper_of_interfaces",
        )
        self.assertEqual(
            report["lower_check"]["declaration"],
            "DynamicMoeSemantics.competitive_factor_lower_bound_at_least_one",
        )
        self.assertEqual(
            report["positive_reduction_check"]["declaration"],
            "DynamicMoePositiveBodyReduction."
            "hasPositiveBodyFractionalReduction_of_twoSparseChaser",
        )
        self.assertEqual(
            report["positive_source_compatibility_check"]["declaration"],
            "DynamicMoePositiveBodyReduction."
            "eventResetBodies_packing_positive_rightHandSide",
        )
        self.assertEqual(
            report["rounding_adapter_check"]["declaration"],
            "DynamicMoeLazyThresholdInterface.hasLazyThresholdRounding_of_primitive",
        )
        self.assertEqual(
            report["rounding_summation_check"]["declaration"],
            "DynamicMoeLazyThresholdInterface."
            "expectedMovement_of_expectedStepMovement",
        )
        self.assertEqual(set(report["main_checks"]), {
            "randomized_theta_one",
            "explicit_constant_upper",
        })
        self.assertEqual(
            report["main_checks"]["randomized_theta_one"]["declaration"],
            "DynamicMoeMain.dynamicMoe_randomized_theta_one_of_source_theorems",
        )
        self.assertEqual(
            report["main_checks"]["explicit_constant_upper"]["declaration"],
            "DynamicMoeMain.dynamicMoe_explicit_constant_upper_of_source_theorems",
        )


if __name__ == "__main__":
    unittest.main()
