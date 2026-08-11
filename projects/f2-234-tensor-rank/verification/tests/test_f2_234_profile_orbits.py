import hashlib
import io
import json
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

from evaluators.f2_tensor_rank_sat import transpose_wang_3x2_mask
from experiments.f2_234_profile_orbits import (
    ProfileOrbitError,
    active_capacities,
    canonical_wang_profile_from_target,
    classification,
    fractional_rank_two_relaxation_report,
    main,
    one_dimensional_capacities,
    profile_cnf,
    quotient_profiles,
    rank_classes,
    target_2x3_to_wang_3x2_mask,
    verify_proof_pair_provenance,
)


class TestF2234ProfileOrbits(unittest.TestCase):
    def test_rank_classes_and_capacity_count(self):
        rank_one, rank_two = rank_classes()
        self.assertEqual((len(rank_one), len(rank_two)), (21, 42))
        self.assertEqual(len(active_capacities()), 1897)
        self.assertEqual(
            one_dimensional_capacities(), tuple((form, 1) for form in range(1, 64))
        )

    def test_wang_target_transpose_round_trip_and_orbit_canonicalization(self):
        for wang_mask in range(1, 64):
            target_mask = transpose_wang_3x2_mask(wang_mask)
            self.assertEqual(target_2x3_to_wang_3x2_mask(target_mask), wang_mask)
        orbit = classification()["orbits"][0]
        target_profile = tuple(
            transpose_wang_3x2_mask(mask)
            for mask in orbit["representative_wang_3x2"]
        )
        self.assertEqual(
            canonical_wang_profile_from_target(target_profile),
            tuple(orbit["representative_wang_3x2"]),
        )

    def test_profile_cnf_dimensions(self):
        payload, dimensions = profile_cnf()
        self.assertEqual(dimensions["variables"], 62267)
        self.assertEqual(dimensions["clauses"], 124027)
        self.assertTrue(payload.startswith(b"p cnf 62267 124027\n"))

    def test_exact_fractional_witness_blocks_linear_profile_bound(self):
        report = fractional_rank_two_relaxation_report()
        self.assertEqual(report["verdict"], "EXACT_FRACTIONAL_OBSTRUCTION")
        self.assertEqual(report["rank_two_value"], "19/42")
        self.assertEqual(report["sum_x"], "19")
        self.assertEqual(report["rank_two_objective"], "19")
        self.assertEqual(report["checked_capacities"], 1897)
        self.assertEqual(report["violated_capacities"], 0)

    def test_one_profile_has_a_nonempty_group_orbit(self):
        profile = tuple(range(1, 20))
        # This test exercises the exact group action, not legality.
        # A singleton arbitrary set is not group invariant and must fail loudly.
        with self.assertRaisesRegex(ProfileOrbitError, "not group-invariant"):
            quotient_profiles({profile})

    def test_proof_pair_provenance_checks_hashes_and_reproduces_cnf(self):
        payload, dimensions = profile_cnf()
        with tempfile.TemporaryDirectory() as temporary_directory:
            root = Path(temporary_directory)
            paths = {
                "cnf": root / "profile.cnf",
                "drat": root / "profile.drat",
                "lrat": root / "profile.lrat",
            }
            paths["cnf"].write_bytes(payload)
            paths["drat"].write_bytes(b"prepared-drat\n")
            paths["lrat"].write_bytes(b"prepared-lrat\n")
            manifest = {
                "schema": "f2-234-profile-proof-pair-provenance-v1",
                "files": {
                    key: {
                        "path": str(path),
                        "bytes": path.stat().st_size,
                        "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                    }
                    for key, path in paths.items()
                },
            }
            manifest_path = root / "manifest.json"
            manifest_path.write_text(json.dumps(manifest))
            result = verify_proof_pair_provenance(manifest_path)
            self.assertEqual(result["verdict"], "PROVENANCE_VERIFIED_REPLAY_PENDING")
            self.assertEqual(result["cnf_dimensions"], dimensions)
            with redirect_stdout(io.StringIO()) as stdout:
                self.assertEqual(
                    main(["verify-provenance", "--manifest", str(manifest_path)]),
                    0,
                )
            self.assertIn("PROVENANCE_VERIFIED_REPLAY_PENDING", stdout.getvalue())

            paths["drat"].write_bytes(b"changed\n")
            with self.assertRaisesRegex(ProfileOrbitError, "drat byte-count mismatch"):
                verify_proof_pair_provenance(manifest_path)


if __name__ == "__main__":
    unittest.main()
