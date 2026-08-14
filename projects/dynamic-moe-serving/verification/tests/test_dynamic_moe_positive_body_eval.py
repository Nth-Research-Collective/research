"""Exact tests for the Dynamic MoE positive-body reduction."""

import unittest
from fractions import Fraction

from evaluators.dynamic_moe_positive_body_eval import (
    ENVELOPE_FACTOR,
    allocations,
    balanced_map,
    control_report,
    l1,
    latency,
    offline_optimum,
    reservoir_map,
    reset_service_bound,
    select_covering_scale,
    tangent_envelope,
    tangent_grid,
    tangent_identity,
    verify_tangent_envelope_at,
)


class TestTangentEnvelope(unittest.TestCase):
    def test_tangent_is_exact_underestimate(self):
        identity = tangent_identity(Fraction(7, 3), Fraction(5, 2), Fraction(9, 4))
        self.assertEqual(identity["tangent_gap"], identity["expected_tangent_gap"])
        self.assertGreaterEqual(identity["tangent_gap"], 0)

    def test_geometric_grid_gives_three_quarter_envelope(self):
        for k in range(1, 9):
            for numerator in range(16 * k + 1):
                allocation = Fraction(numerator, 8)
                self.assertTrue(verify_tangent_envelope_at(11, allocation, k))
                scale = select_covering_scale(allocation, k)
                q = 1 + allocation
                self.assertLessEqual(scale, q)
                self.assertLess(q, Fraction(3, 2) * scale)

    def test_grid_covers_augmented_range(self):
        for k in range(5):
            grid = tangent_grid(k)
            self.assertEqual(grid[0], 1)
            self.assertGreater(Fraction(3, 2) * grid[-1], 1 + 2 * k)

    def test_sparse_tangent_negative_control_fails(self):
        # The two scales corresponding to tangencies at a=0 and a=10 do not
        # give a constant envelope at u=1.  This preserves the referee's
        # smallest witness while showing why the geometric grid is needed.
        request = Fraction(1)
        allocation = Fraction(1)
        sparse = max(
            tangent_identity(request, allocation, scale)["ratio"]
            for scale in (Fraction(1), Fraction(11))
        )
        self.assertLess(sparse, ENVELOPE_FACTOR)
        self.assertGreaterEqual(
            tangent_envelope(request, allocation, 1),
            ENVELOPE_FACTOR * latency((request,), (allocation,)),
        )


class TestReservoirBridge(unittest.TestCase):
    def test_mapping_is_feasible_and_dominates_half_augmented_coordinates(self):
        augmented = (Fraction(3), Fraction(1), Fraction(2))
        mapped = reservoir_map(augmented, k=3, reservoir=0)
        self.assertEqual(sum(mapped), 3)
        self.assertTrue(all(value >= 0 for value in mapped))
        self.assertTrue(all(mapped[index] >= augmented[index] / 2 for index in range(3)))

    def test_mapping_is_one_lipschitz(self):
        vectors = tuple(
            vector
            for mass in range(5)
            for vector in allocations(3, mass)
        )
        for first in vectors:
            for second in vectors:
                self.assertLessEqual(
                    l1(reservoir_map(first, 2), reservoir_map(second, 2)),
                    l1(first, second),
                )

    def test_service_bridge(self):
        workload = (Fraction(7), Fraction(3), Fraction(5))
        augmented = (Fraction(1), Fraction(2), Fraction(3))
        height = max(
            tangent_envelope(request, replicas, 3)
            for request, replicas in zip(workload, augmented, strict=True)
        )
        self.assertLessEqual(
            latency(workload, reservoir_map(augmented, 3)),
            Fraction(8, 3) * height,
        )

    def test_symmetric_mapping_is_feasible_dominating_and_one_lipschitz(self):
        vectors = tuple(
            vector
            for mass in range(7)
            for vector in allocations(3, mass)
        )
        for first in vectors:
            mapped = balanced_map(first, 3)
            self.assertEqual(sum(mapped), 3)
            self.assertTrue(all(value >= 0 for value in mapped))
            self.assertTrue(all(mapped[i] >= Fraction(first[i], 2) for i in range(3)))
            for second in vectors:
                self.assertLessEqual(
                    l1(mapped, balanced_map(second, 3)),
                    l1(first, second),
                )

    def test_reset_charge(self):
        report = reset_service_bound(Fraction(9, 2), Fraction(1, 8), Fraction(1, 16))
        self.assertTrue(report["passes"])
        self.assertLessEqual(
            report["twice_height"],
            report["vertical_movement"] + report["reset_allowance"],
        )


class TestExactBaseline(unittest.TestCase):
    def test_m1_degeneration(self):
        cost, path = offline_optimum(((6,), (3,)), (0,))
        self.assertEqual(cost, 9)
        self.assertEqual(path, ((0,), (0,)))

    def test_one_step_integer_water_filling_control(self):
        cost, path = offline_optimum(((0, 4),), (1, 0))
        self.assertEqual(cost, 4)
        self.assertIn(path[0], ((0, 1), (1, 0)))

    def test_full_l1_is_twice_one_sided_on_fixed_budget(self):
        first = (3, 0, 0)
        second = (0, 2, 1)
        one_sided = sum(max(right - left, 0) for left, right in zip(first, second))
        self.assertEqual(l1(first, second), 2 * one_sided)

    def test_complete_control_report(self):
        report = control_report()
        self.assertEqual(report["verdict"], "DYNAMIC_MOE_POSITIVE_BODY_CONTROL_PASS")
        self.assertEqual(report["bridge"]["verdict"], "EXHAUSTIVE_BRIDGE_PASS")
        self.assertGreater(report["bridge"]["movement_checks"], 0)
        self.assertGreater(report["bridge"]["service_checks"], 0)


if __name__ == "__main__":
    unittest.main()
