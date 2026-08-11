import copy
import json
import unittest
from pathlib import Path

from evaluators.f2_234_tensor_rank_eval import (
    COEFFICIENT_COUNT,
    SCHEMA,
    SHAPE,
    TARGET_ONES,
    TensorRankEvaluationError,
    control_report,
    strassen_rank_7,
    target_tensor,
    verify_artifact,
    verify_rank_decomposition,
)

ARTIFACT_PATH = (
    Path(__file__).resolve().parent.parent
    / "knowledge"
    / "data"
    / "f2_234_rank20_alphatensor.json"
)


def load_tracked_artifact() -> dict:
    with ARTIFACT_PATH.open() as handle:
        return json.load(handle)


class TestF2TargetTensor(unittest.TestCase):
    def test_target_has_24_ones_among_576_coefficients(self):
        tensor = target_tensor(SHAPE)
        ones = sum(value for plane in tensor for row in plane for value in row)
        coefficients = len(tensor) * len(tensor[0]) * len(tensor[0][0])
        self.assertEqual(ones, TARGET_ONES)
        self.assertEqual(coefficients, COEFFICIENT_COUNT)

    def test_target_coordinates_are_the_matrix_multiplication_ones(self):
        tensor = target_tensor(SHAPE)
        expected = {(i * 3 + j, j * 4 + k, i * 4 + k) for i in range(2) for j in range(3) for k in range(4)}
        actual = {
            (i, j, k)
            for i in range(6)
            for j in range(12)
            for k in range(8)
            if tensor[i][j][k]
        }
        self.assertEqual(actual, expected)


class TestStrassenPositiveControl(unittest.TestCase):
    def test_strassen_rank_7_is_accepted_for_222(self):
        result = verify_rank_decomposition(strassen_rank_7(), shape=(2, 2, 2), declared_rank=7)
        self.assertEqual(result["verdict"], "VERIFIED")
        self.assertEqual(result["rank"], 7)
        self.assertEqual(result["coefficients"], 64)
        self.assertEqual(result["target_ones"], 8)

    def test_one_bit_corruption_is_rejected_with_coordinate_witness(self):
        corrupted = [copy.deepcopy(term) for term in strassen_rank_7()]
        corrupted[3]["w"][0] ^= 1
        with self.assertRaisesRegex(
            TensorRankEvaluationError, r"coordinate \(\d+, \d+, \d+\): expected \d, got \d"
        ):
            verify_rank_decomposition(corrupted, shape=(2, 2, 2), declared_rank=7)


class TestTrackedArtifact(unittest.TestCase):
    def test_tracked_alphatensor_rank_20_artifact_passes(self):
        artifact = load_tracked_artifact()
        self.assertEqual(artifact["schema"], SCHEMA)
        self.assertEqual(artifact["declared_rank"], 20)
        self.assertEqual(len(artifact["terms"]), 20)
        result = verify_artifact(artifact)
        self.assertEqual(result["verdict"], "VERIFIED_ARTIFACT")
        self.assertEqual(result["coefficients"], 576)
        self.assertEqual(result["target_ones"], 24)

    def test_artifact_has_pinned_upstream_identity(self):
        artifact = load_tracked_artifact()
        source = artifact["primary_source"]
        self.assertEqual(
            source["file_sha256"],
            "70f09f349d8d2874ef0e0e089459c7320f5aa3eef277df5ffa67f573709db2da",
        )
        self.assertEqual(source["blob_sha"], "74ca8d8d9db45e59d01a2db8cd974896b6497587")
        self.assertEqual(source["npz_key"], "2,3,4")
        self.assertEqual(source["factor_array_shapes"], [[6, 20], [12, 20], [8, 20]])
        self.assertIn("raw.githubusercontent.com", source["raw_url"])


class TestMalformedCandidates(unittest.TestCase):
    def setUp(self):
        self.terms = strassen_rank_7()

    def test_wrong_factor_length_is_rejected(self):
        malformed = copy.deepcopy(self.terms)
        malformed[1]["u"] = [1, 0, 0]
        with self.assertRaisesRegex(TensorRankEvaluationError, "length 3, expected 4"):
            verify_rank_decomposition(malformed, shape=(2, 2, 2), declared_rank=7)

    def test_non_binary_entry_is_rejected(self):
        malformed = copy.deepcopy(self.terms)
        malformed[0]["v"][2] = 2
        with self.assertRaisesRegex(TensorRankEvaluationError, "not a binary value"):
            verify_rank_decomposition(malformed, shape=(2, 2, 2), declared_rank=7)

    def test_non_integer_entry_is_rejected(self):
        malformed = copy.deepcopy(self.terms)
        malformed[2]["w"][1] = 0.5
        with self.assertRaisesRegex(TensorRankEvaluationError, "not a binary value"):
            verify_rank_decomposition(malformed, shape=(2, 2, 2), declared_rank=7)

    def test_zero_factor_vector_is_rejected(self):
        malformed = copy.deepcopy(self.terms)
        malformed[5]["u"] = [0, 0, 0, 0]
        with self.assertRaisesRegex(TensorRankEvaluationError, "zero factor vector"):
            verify_rank_decomposition(malformed, shape=(2, 2, 2), declared_rank=7)

    def test_wrong_declared_rank_is_rejected(self):
        with self.assertRaisesRegex(TensorRankEvaluationError, "declared rank"):
            verify_rank_decomposition(self.terms, shape=(2, 2, 2), declared_rank=6)

    def test_duplicate_pair_is_accepted_and_cancels_over_f2(self):
        duplicated = copy.deepcopy(self.terms)
        duplicated.extend((copy.deepcopy(self.terms[0]), copy.deepcopy(self.terms[0])))
        result = verify_rank_decomposition(duplicated, shape=(2, 2, 2), declared_rank=9)
        self.assertEqual(result["rank"], 9)

    def test_non_integer_shape_is_rejected_without_coercion(self):
        with self.assertRaisesRegex(TensorRankEvaluationError, "three integers"):
            verify_rank_decomposition(self.terms, shape=(2.5, 2, 2), declared_rank=7)

    def test_artifact_with_wrong_schema_is_rejected(self):
        artifact = load_tracked_artifact()
        artifact["schema"] = "other-schema-v1"
        with self.assertRaisesRegex(TensorRankEvaluationError, "unexpected schema"):
            verify_artifact(artifact)

    def test_artifact_with_corrupted_declared_rank_is_rejected(self):
        artifact = load_tracked_artifact()
        artifact["declared_rank"] = 19
        with self.assertRaisesRegex(TensorRankEvaluationError, "declared rank"):
            verify_artifact(artifact)

    def test_artifact_with_wrong_field_is_rejected(self):
        artifact = load_tracked_artifact()
        artifact["field"] = "F3"
        with self.assertRaisesRegex(TensorRankEvaluationError, "unexpected field"):
            verify_artifact(artifact)

    def test_artifact_with_wrong_format_is_rejected(self):
        artifact = load_tracked_artifact()
        artifact["format"] = "2x3-by-3x5"
        with self.assertRaisesRegex(TensorRankEvaluationError, "unexpected format"):
            verify_artifact(artifact)

    def test_artifact_with_corrupted_term_is_rejected_with_witness(self):
        artifact = load_tracked_artifact()
        artifact["terms"][7]["w"][3] ^= 1
        with self.assertRaisesRegex(
            TensorRankEvaluationError, r"coordinate \(\d+, \d+, \d+\): expected \d, got \d"
        ):
            verify_artifact(artifact)


class TestControls(unittest.TestCase):
    def test_control_report_passes(self):
        report = control_report()
        self.assertEqual(report["verdict"], "CONTROL_PASS")
        self.assertEqual(report["target_ones"], 24)
        self.assertEqual(report["coefficients"], 576)
        self.assertTrue(report["strassen_rank_7_accepted"])
        self.assertTrue(report["alphatensor_rank_20_accepted"])


if __name__ == "__main__":
    unittest.main()
