"""Exact interval certificate for a quartic-BPR PoA interior maximum.

The network is a directed Wheatstone graph preceded by one common serial edge.
All coefficients, demand probes, interval boxes, and checks are rational.  The
certificate uses exact Krawczyk inclusions for the equilibrium and optimum KKT
systems, direct interval bounds for social costs, and exact boundary arguments
to keep all three Wardrop paths active from demand 17 through demand 24.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import json
from pathlib import Path
import random


Q = Fraction

# Edge 0 is common to every path.  Edges 1--5 form the Wheatstone base.
COEFFICIENTS = (
    (Q(12_800_000), Q(1855, 374)),
    (Q(17, 3), Q(13, 896)),
    (Q(236), Q(38, 5)),
    (Q(1280), Q(17, 80)),
    (Q(5504, 7), Q(188)),
    (Q(424, 7), Q(208, 3)),
)
PATHS = (
    (0, 1, 2),
    (0, 3, 4),
    (0, 1, 5, 4),
)
BASE = COEFFICIENTS[1:]
DISCOVERY_SEED = 20260879


def _q(value: str | int) -> Q:
    return Q(value)


def _scaled_wheatstone_coefficients(seed: int) -> tuple[tuple[Q, Q], ...]:
    """Reproduce the rational base generator that exposed the candidate."""
    rng = random.Random(seed)

    def draw() -> Q:
        exponent = rng.randint(-8, 8)
        power = Q(2**exponent) if exponent >= 0 else Q(1, 2**-exponent)
        return Q(rng.randint(1, 64), rng.randint(1, 16)) * power

    return tuple((draw(), draw()) for _ in range(5))


@dataclass(frozen=True)
class Interval:
    low: Q
    high: Q

    def __post_init__(self) -> None:
        if self.low > self.high:
            raise ValueError("reversed interval")

    @classmethod
    def point(cls, value: Q) -> "Interval":
        return cls(value, value)

    def __add__(self, other: "Interval") -> "Interval":
        return Interval(self.low + other.low, self.high + other.high)

    def __neg__(self) -> "Interval":
        return Interval(-self.high, -self.low)

    def __sub__(self, other: "Interval") -> "Interval":
        return self + (-other)

    def __mul__(self, other: "Interval") -> "Interval":
        products = (
            self.low * other.low,
            self.low * other.high,
            self.high * other.low,
            self.high * other.high,
        )
        return Interval(min(products), max(products))

    def scale(self, value: Q) -> "Interval":
        return self * Interval.point(value)

    def power(self, exponent: int) -> "Interval":
        if exponent < 0 or self.low < 0:
            raise ValueError("power certificate expects a nonnegative interval")
        return Interval(self.low**exponent, self.high**exponent)

    def midpoint(self) -> Q:
        return (self.low + self.high) / 2

    def radius(self) -> Q:
        return (self.high - self.low) / 2

    def render(self) -> list[str]:
        return [str(self.low), str(self.high)]


ROOT_BOXES = {
    (17, "equilibrium"): (
        Interval(_q("11.745703474"), _q("11.745703476")),
        Interval(_q("3.439049651"), _q("3.439049654")),
    ),
    (21, "equilibrium"): (
        Interval(_q("14.502098182"), _q("14.502098184")),
        Interval(_q("4.964355276"), _q("4.964355279")),
    ),
    (24, "equilibrium"): (
        Interval(_q("16.571658822"), _q("16.571658825")),
        Interval(_q("6.287152338"), _q("6.287152340")),
    ),
    (17, "optimum"): (
        Interval(_q("11.737926336"), _q("11.737926339")),
        Interval(_q("4.670152304"), _q("4.670152308")),
    ),
}

TWO_PATH_OPTIMUM_BOXES = {
    21: Interval(_q("14.499119464"), _q("14.499119467")),
    24: Interval(_q("16.569846371"), _q("16.569846374")),
}


def _cost(edge: int, load: Q, multiplier: int = 1) -> Q:
    a, b = BASE[edge]
    return a + multiplier * b * load**4


def _cost_interval(edge: int, load: Interval, multiplier: int = 1) -> Interval:
    a, b = BASE[edge]
    return Interval.point(a) + load.power(4).scale(multiplier * b)


def _derivative_interval(
    edge: int,
    load: Interval,
    multiplier: int,
) -> Interval:
    _, b = BASE[edge]
    return load.power(3).scale(4 * multiplier * b)


def _gradient(mu: Q, x: Q, y: Q, multiplier: int) -> tuple[Q, Q]:
    z = mu - x - y
    first = (
        _cost(1, x, multiplier)
        - _cost(4, z, multiplier)
        - _cost(3, mu - x, multiplier)
    )
    second = (
        _cost(2, y, multiplier)
        - _cost(0, mu - y, multiplier)
        - _cost(4, z, multiplier)
    )
    return first, second


def _jacobian_intervals(
    mu: Q,
    x: Interval,
    y: Interval,
    multiplier: int,
) -> tuple[tuple[Interval, Interval], tuple[Interval, Interval]]:
    z = Interval.point(mu) - x - y
    mu_minus_x = Interval.point(mu) - x
    mu_minus_y = Interval.point(mu) - y
    cross = _derivative_interval(4, z, multiplier)
    first = (
        _derivative_interval(1, x, multiplier)
        + cross
        + _derivative_interval(3, mu_minus_x, multiplier)
    )
    second = (
        _derivative_interval(2, y, multiplier)
        + _derivative_interval(0, mu_minus_y, multiplier)
        + cross
    )
    return ((first, cross), (cross, second))


def _inverse_2_by_2(matrix: tuple[tuple[Q, Q], tuple[Q, Q]]):
    (a, b), (c, d) = matrix
    determinant = a*d - b*c
    if determinant == 0:
        raise AssertionError("singular midpoint Jacobian")
    return ((d/determinant, -b/determinant),
            (-c/determinant, a/determinant))


def _krawczyk_check(
    demand: int,
    kind: str,
) -> dict:
    mu = Q(demand)
    multiplier = 1 if kind == "equilibrium" else 5
    box = ROOT_BOXES[(demand, kind)]
    center = tuple(interval.midpoint() for interval in box)
    radii = tuple(interval.radius() for interval in box)
    gradient = _gradient(mu, center[0], center[1], multiplier)
    jacobian = _jacobian_intervals(mu, box[0], box[1], multiplier)
    midpoint_jacobian = tuple(tuple(entry.midpoint() for entry in row)
                              for row in jacobian)
    inverse = _inverse_2_by_2(midpoint_jacobian)

    newton_center = tuple(
        center[row] - sum(inverse[row][column] * gradient[column]
                          for column in range(2))
        for row in range(2)
    )
    error_matrix: list[list[Interval]] = []
    for row in range(2):
        error_row = []
        for column in range(2):
            product = Interval.point(Q(0))
            for inner in range(2):
                product += jacobian[inner][column].scale(inverse[row][inner])
            error_row.append(Interval.point(Q(row == column)) - product)
        error_matrix.append(error_row)

    image = []
    for row in range(2):
        enclosure = Interval.point(newton_center[row])
        for column in range(2):
            radius = Interval(-radii[column], radii[column])
            enclosure += error_matrix[row][column] * radius
        if not (box[row].low < enclosure.low <= enclosure.high < box[row].high):
            raise AssertionError(
                f"Krawczyk image {enclosure.render()} escaped "
                f"{kind} box {box[row].render()} at demand {demand}"
            )
        image.append(enclosure)

    z = Interval.point(mu) - box[0] - box[1]
    if z.low <= 0:
        raise AssertionError("three-path root box is not interior")
    return {
        "demand": demand,
        "kind": kind,
        "multiplier": multiplier,
        "x_box": box[0].render(),
        "y_box": box[1].render(),
        "z_box": z.render(),
        "krawczyk_image": [entry.render() for entry in image],
    }


def _two_path_optimum_check(demand: int) -> dict:
    mu = Q(demand)
    u = TWO_PATH_OPTIMUM_BOXES[demand]

    def difference(flow: Q) -> Q:
        other = mu - flow
        return (
            _cost(0, flow, 5) + _cost(1, flow, 5)
            - _cost(2, other, 5) - _cost(3, other, 5)
        )

    low_sign = difference(u.low)
    high_sign = difference(u.high)
    if not low_sign < 0 < high_sign:
        raise AssertionError(f"two-path optimum bracket failed at {demand}")

    v = Interval.point(mu) - u
    used_zero = (
        _cost_interval(0, u, 5) + _cost_interval(1, u, 5)
    )
    unused = (
        _cost_interval(0, u, 5)
        + Interval.point(_cost(4, Q(0), 5))
        + _cost_interval(3, v, 5)
    )
    inactive_margin = Interval(
        unused.low - used_zero.high,
        unused.high - used_zero.low,
    )
    if inactive_margin.low <= 0:
        raise AssertionError(f"third path can enter optimum at {demand}")
    return {
        "demand": demand,
        "u_box": u.render(),
        "v_box": v.render(),
        "equal_cost_endpoint_signs": [str(low_sign), str(high_sign)],
        "inactive_marginal_margin": inactive_margin.render(),
    }


def _support_regime_check() -> dict:
    # At x=0, the all-path equality F=0 is impossible even at zero loads.
    x_zero_upper = BASE[1][0] - BASE[4][0] - BASE[3][0]
    if x_zero_upper >= 0:
        raise AssertionError("x=0 boundary exclusion failed")

    # At y=0, G=0 forces z<3.  Then F=0 forces x<8, hence mu<11.
    if _cost(4, Q(3)) + _cost(0, Q(0)) <= _cost(2, Q(0)):
        raise AssertionError("y=0 z bound failed")
    rhs_at_z_3 = (
        BASE[4][0] + BASE[3][0] - BASE[1][0]
        + (BASE[4][1] + BASE[3][1]) * Q(3)**4
    )
    if BASE[1][1] * Q(8)**4 <= rhs_at_z_3:
        raise AssertionError("y=0 x bound failed")
    if Q(8) + Q(3) >= Q(17):
        raise AssertionError("y=0 demand bound failed")

    # At z=0, all three path costs can agree only at these x^4,y^4.
    x_fourth = Q(3_831_364_840, 18_693)
    y_fourth = Q(1_083_769_565, 130_851)
    f_boundary = (
        BASE[1][0] + BASE[1][1]*x_fourth
        - BASE[4][0] - BASE[3][0] - BASE[3][1]*y_fourth
    )
    g_boundary = (
        BASE[2][0] + BASE[2][1]*y_fourth
        - BASE[0][0] - BASE[0][1]*x_fourth - BASE[4][0]
    )
    determinant = BASE[1][1]*BASE[2][1] - BASE[3][1]*BASE[0][1]
    if determinant == 0 or f_boundary != 0 or g_boundary != 0:
        raise AssertionError("z=0 boundary solution failed")
    if not x_fourth > Q(21)**4 or not y_fourth > Q(9)**4:
        raise AssertionError("z=0 demand lower bound failed")
    if Q(21) + Q(9) <= Q(24):
        raise AssertionError("z=0 boundary was not excluded above 24")

    # The exact Krawczyk root at demand 17 starts the all-positive branch.
    start = _krawczyk_check(17, "equilibrium")
    return {
        "interval": [17, 24],
        "start_root": start,
        "x_zero": f"F <= {x_zero_upper} < 0",
        "y_zero": "z<3 and x<8, hence demand<11",
        "z_zero": {
            "x_fourth": str(x_fourth),
            "y_fourth": str(y_fourth),
            "demand_bound": "x>21 and y>9, hence demand>30",
        },
        "conclusion": "all three Wardrop paths stay active on [17,24]",
    }


def _social_cost_interval(
    demand: int,
    path_box: tuple[Interval, Interval] | Interval,
) -> Interval:
    mu = Q(demand)
    if isinstance(path_box, Interval):
        x = path_box
        y = Interval.point(mu) - x
        z = Interval.point(Q(0))
    else:
        x, y = path_box
        z = Interval.point(mu) - x - y
    loads = (
        Interval.point(mu),
        x + z,
        x,
        y,
        y + z,
        z,
    )
    total = Interval.point(Q(0))
    for (a, b), load in zip(COEFFICIENTS, loads):
        total += load.scale(a) + load.power(5).scale(b)
    return total


def _poa_comparison_check() -> dict:
    equilibrium_boxes = {
        demand: ROOT_BOXES[(demand, "equilibrium")]
        for demand in (17, 21, 24)
    }
    optimum_boxes: dict[int, tuple[Interval, Interval] | Interval] = {
        17: ROOT_BOXES[(17, "optimum")],
        21: TWO_PATH_OPTIMUM_BOXES[21],
        24: TWO_PATH_OPTIMUM_BOXES[24],
    }
    equilibrium_costs = {
        demand: _social_cost_interval(demand, box)
        for demand, box in equilibrium_boxes.items()
    }
    optimum_costs = {
        demand: _social_cost_interval(demand, box)
        for demand, box in optimum_boxes.items()
    }

    comparisons = {}
    for endpoint in (17, 24):
        # lower(PoA(21)) > upper(PoA(endpoint))
        difference = (
            equilibrium_costs[21].low * optimum_costs[endpoint].low
            - equilibrium_costs[endpoint].high * optimum_costs[21].high
        )
        if difference <= 0:
            raise AssertionError(f"PoA comparison failed against {endpoint}")
        comparisons[f"PoA(21)>PoA({endpoint})"] = {
            "exact_cross_product_lower_difference": str(difference),
            "decimal_lower_difference": float(difference),
        }

    return {
        "equilibrium_cost_intervals": {
            str(demand): value.render()
            for demand, value in equilibrium_costs.items()
        },
        "optimum_cost_intervals": {
            str(demand): value.render()
            for demand, value in optimum_costs.items()
        },
        "comparisons": comparisons,
    }


def verify_counterexample() -> dict:
    if _scaled_wheatstone_coefficients(DISCOVERY_SEED) != BASE:
        raise AssertionError("discovery seed no longer reproduces the base")
    root_checks = [
        _krawczyk_check(demand, "equilibrium")
        for demand in (17, 21, 24)
    ]
    root_checks.append(_krawczyk_check(17, "optimum"))
    optimum_boundary_checks = [
        _two_path_optimum_check(demand) for demand in (21, 24)
    ]
    support = _support_regime_check()
    poa = _poa_comparison_check()
    return {
        "verdict": "EXACT_RATIONAL_INTERVAL_CERTIFICATE_PASS",
        "statement": (
            "PoA has an interior maximum in the constant all-path Wardrop "
            "support interval (17,24)"
        ),
        "logic": (
            "PoA is continuous; PoA(21) exceeds PoA(17) and PoA(24), so its "
            "maximum on [17,24] is attained in the interior"
        ),
        "topology": {
            "vertices": 5,
            "edges": 6,
            "simple_od_paths": 3,
            "paths": [list(path) for path in PATHS],
            "minimality_claim": "none",
        },
        "coefficients": [
            {"edge": edge, "a": str(a), "b": str(b)}
            for edge, (a, b) in enumerate(COEFFICIENTS)
        ],
        "root_checks": root_checks,
        "optimum_boundary_checks": optimum_boundary_checks,
        "wardrop_support": support,
        "poa_comparisons": poa,
        "proof_scope": (
            "exact rational arithmetic plus the standard Krawczyk inclusion "
            "theorem and continuity/strict-convexity KKT facts"
        ),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    report = verify_counterexample()
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
