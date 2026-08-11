import tempfile
import unittest
from pathlib import Path

from experiments.f2_234_profile_orbits import classification
from experiments.f2_234_tight_row_restriction import (
    all_rank_one_packet,
    all_profile_packet,
    exact_rank20_packet,
    orbit_zero_packet,
    output_row_subspace,
    profile_exclusion_report,
    profile_766_exclusion_report,
    profile_rank2_exclusion_report,
    rank_one_2x3_factors,
    restricted_flattening_rank,
    verify_packet,
)
from evaluators.f2_tensor_rank_sat import matrix_rank_2x3


class TestF2234TightRowRestriction(unittest.TestCase):
    def test_rank_one_factor_recovery(self):
        for mask in range(1, 64):
            if matrix_rank_2x3(mask) != 1:
                continue
            a, b = rank_one_2x3_factors(mask)
            reconstructed = (b if a & 1 else 0) | ((b if a & 2 else 0) << 3)
            self.assertEqual(reconstructed, mask)

    def test_restricted_flattenings_have_rank_twelve(self):
        self.assertEqual(
            [restricted_flattening_rank(x) for x in range(1, 4)],
            [12, 12, 12],
        )
        spaces = [output_row_subspace(x, 4) for x in range(1, 4)]
        for left in range(3):
            for right in range(left + 1, 3):
                self.assertEqual(spaces[left] & spaces[right], {0})

    def test_orbit_zero_representative_is_exactly_excluded(self):
        orbit = next(
            row for row in classification()["orbits"] if row["orbit_index"] == 0
        )
        report = profile_exclusion_report(orbit["representative_target_2x3"])
        self.assertEqual(report["verdict"], "EXACT_EXCLUSION")
        self.assertEqual(sorted(report["row_direction_counts"].values()), [5, 7, 7])
        self.assertEqual(report["overlap_terms"], 5)

    def test_other_orbits_are_not_laundered_into_the_theorem(self):
        for orbit in classification()["orbits"]:
            if orbit["orbit_index"] == 0:
                continue
            report = profile_exclusion_report(orbit["representative_target_2x3"])
            self.assertEqual(report["verdict"], "NOT_APPLICABLE")

    def test_766_theorem_excludes_exactly_orbits_one_and_two(self):
        for orbit in classification()["orbits"]:
            report = profile_766_exclusion_report(
                orbit["representative_target_2x3"]
            )
            expected = "EXACT_EXCLUSION" if orbit["orbit_index"] in (1, 2) else "NOT_APPLICABLE"
            self.assertEqual(report["verdict"], expected)
            if expected == "EXACT_EXCLUSION":
                self.assertEqual(
                    report["second_restriction"]["v_relation_kernel_dimension"],
                    1,
                )
                self.assertEqual(len(report["retained_distinct_b_factors"]), 6)

    def test_packet_covers_all_sixty_three_profiles_and_replays(self):
        packet = orbit_zero_packet()
        self.assertEqual(packet["orbit_size"], 63)
        self.assertEqual(packet["verified_exclusions"], 63)
        with tempfile.TemporaryDirectory() as directory_name:
            path = Path(directory_name) / "packet.json"
            import json

            path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n")
            replay = verify_packet(path)
            self.assertEqual(replay["verdict"], "VERIFIED_ORBIT_EXCLUSION")

    def test_all_rank_one_packet_excludes_two_hundred_ten_profiles(self):
        packet = all_rank_one_packet()
        self.assertEqual(packet["excluded_profiles"], 210)
        self.assertEqual(packet["remaining_orbits"], [3])
        self.assertEqual(packet["remaining_profiles"], 42)
        self.assertEqual(
            [row["orbit_index"] for row in packet["excluded_orbits"]],
            [0, 1, 2],
        )

    def test_rank_two_theorem_excludes_exactly_orbit_three(self):
        for orbit in classification()["orbits"]:
            report = profile_rank2_exclusion_report(
                orbit["representative_target_2x3"]
            )
            expected = "EXACT_EXCLUSION" if orbit["orbit_index"] == 3 else "NOT_APPLICABLE"
            self.assertEqual(report["verdict"], expected)
        orbit_three = classification()["orbits"][3]
        report = profile_rank2_exclusion_report(
            orbit_three["representative_target_2x3"]
        )
        self.assertEqual(report["required_relation_support_incidences"], 18)
        self.assertEqual(report["maximum_relation_support_incidences"], 9)

    def test_all_profile_packet_has_no_remaining_profiles(self):
        packet = all_profile_packet()
        self.assertEqual(packet["verified_profile_exclusions"], 252)
        self.assertEqual(packet["remaining_profiles"], 0)
        self.assertEqual(packet["rank_two_exclusion"]["profiles"], 42)

    def test_exact_rank_packet_closes_both_bounds(self):
        packet = exact_rank20_packet()
        self.assertEqual(packet["claim"], "R_F2(<2,3,4>) = 20")
        self.assertEqual(
            packet["lower_bound"]["restriction_exclusion"]["remaining_profiles"],
            0,
        )
        self.assertEqual(packet["upper_bound"]["rank"], 20)
        self.assertEqual(packet["independent_review"]["correctness"], "PASS")


if __name__ == "__main__":
    unittest.main()
