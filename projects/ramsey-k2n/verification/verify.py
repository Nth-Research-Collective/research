"""Independently verify five exact complete-bipartite Ramsey numbers.

The diagonal certificate is Gritsenko's strongly regular graph with
parameters (65, 32, 15, 16).  The four off-diagonal certificates are the
symmetric Hadamard matrices reconstructed by :mod:`hadamard_ramsey`.
Together with the published upper-bound theorems, the finite checks certify
five exact values and close every case of
``R(K_{2,n-1}, K_{2,n})`` for ``3 <= n <= 58``.
"""
from __future__ import annotations

import argparse
from pathlib import Path

from hadamard_ramsey import verify_all as verify_hadamard_instances

HERE = Path(__file__).resolve().parent
DEFAULT_GRITSENKO = HERE / "gritsenko-srg65.rows"


def load_adjacency(path: Path = DEFAULT_GRITSENKO) -> list[list[int]]:
    rows = [line.strip() for line in path.read_text().splitlines() if line.strip()]
    if not rows or any(len(row) != len(rows) for row in rows):
        raise AssertionError("adjacency matrix is not square")
    if any(character not in "01" for row in rows for character in row):
        raise AssertionError("adjacency matrix is not binary")
    return [[int(character) for character in row] for row in rows]


def verify_gritsenko(path: Path = DEFAULT_GRITSENKO) -> dict[str, int | str]:
    """Verify the SRG(65,32,15,16) and both Ramsey color conditions."""
    adjacency = load_adjacency(path)
    vertices = len(adjacency)
    if vertices != 65:
        raise AssertionError(f"graph has {vertices} vertices, expected 65")
    if any(adjacency[i][i] for i in range(vertices)):
        raise AssertionError("graph has a loop")
    if any(adjacency[i][j] != adjacency[j][i]
           for i in range(vertices) for j in range(vertices)):
        raise AssertionError("adjacency matrix is not symmetric")

    degrees = [sum(row) for row in adjacency]
    if set(degrees) != {32}:
        raise AssertionError(f"degrees are not all 32: {sorted(set(degrees))}")

    red_codegrees: set[int] = set()
    blue_codegrees: set[int] = set()
    for i in range(vertices):
        for j in range(i + 1, vertices):
            common_red = sum(adjacency[i][k] and adjacency[j][k]
                             for k in range(vertices))
            common_blue = sum(
                k not in (i, j)
                and not adjacency[i][k]
                and not adjacency[j][k]
                for k in range(vertices)
            )
            expected_red = 15 if adjacency[i][j] else 16
            if common_red != expected_red:
                raise AssertionError(
                    f"pair {i},{j} has red codegree {common_red}, "
                    f"expected {expected_red}"
                )
            if common_blue > 16:
                raise AssertionError(
                    f"pair {i},{j} has blue codegree {common_blue}"
                )
            red_codegrees.add(common_red)
            blue_codegrees.add(common_blue)

    return {
        "n": 17,
        "vertices": vertices,
        "degree": 32,
        "red_codegrees": "/".join(map(str, sorted(red_codegrees))),
        "blue_codegrees": "/".join(map(str, sorted(blue_codegrees))),
        "ramsey_value": 66,
        "source": "Gritsenko, arXiv:2102.05432 (2021)",
    }


def verify_five(
    gritsenko_path: Path = DEFAULT_GRITSENKO,
) -> tuple[dict[str, int | str], list[dict]]:
    return verify_gritsenko(gritsenko_path), verify_hadamard_instances()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gritsenko", type=Path, default=DEFAULT_GRITSENKO)
    args = parser.parse_args(argv)
    diagonal, asymmetric = verify_five(args.gritsenko)
    print(
        "VERIFIED R(K_{2,17},K_{2,17})=66: "
        f"SRG({diagonal['vertices']},{diagonal['degree']},15,16), "
        f"red codegrees {diagonal['red_codegrees']}, "
        f"blue codegrees {diagonal['blue_codegrees']}"
    )
    for report in asymmetric:
        n = report["n"]
        print(
            f"VERIFIED R(K_{{2,{n - 1}}},K_{{2,{n}}})="
            f"{report['ramsey_value']}: Hadamard order "
            f"{report['hadamard_order']}, core {report['vertices']}, "
            f"max codegrees +/{report['max_common_plus']} "
            f"-/{report['max_common_minus']}"
        )
    print("COROLLARY R(K_{2,n-1},K_{2,n})=4n-4 for every 3<=n<=58")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
