"""Reconstruct and verify four exact complete-bipartite Ramsey witnesses.

Lortz--Mengersen prove

    R(K_{2,n-1}, K_{2,n}) <= 4n - 4,

with equality whenever a symmetric Hadamard matrix of order ``4n-4``
exists.  Later propus constructions supply the four orders that their 2002
paper left open below ``n=59``: 116, 156, 172, and 188.

This module reconstructs those matrices from the published difference
families, checks symmetry and orthogonality, and then independently checks
the common-neighbor inequalities in the resulting Ramsey coloring.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_DATA = HERE / "k2n-ramsey-hadamard.json"

Matrix = list[list[int]]


def circulant(order: int, negative_positions: list[int]) -> Matrix:
    """Return the +/-1 circulant whose first row is negative on the block."""
    first = [1] * order
    for position in negative_positions:
        first[position] = -1
    return [[first[(column - row) % order] for column in range(order)]
            for row in range(order)]


def transpose(matrix: Matrix) -> Matrix:
    return [list(column) for column in zip(*matrix)]


def right_reverse(matrix: Matrix) -> Matrix:
    """Multiply by the back-diagonal identity matrix on the right."""
    return [row[::-1] for row in matrix]


def negate(matrix: Matrix) -> Matrix:
    return [[-entry for entry in row] for row in matrix]


def block_matrix(rows: list[list[Matrix]]) -> Matrix:
    result: Matrix = []
    block_height = len(rows[0][0])
    for block_row in rows:
        for index in range(block_height):
            result.append(sum((block[index] for block in block_row), []))
    return result


def propus_hadamard(order: int, a: list[int], b: list[int], d: list[int]) -> Matrix:
    """Build the symmetric GP-array matrix from blocks A, B=C, D."""
    A, B, D = circulant(order, a), circulant(order, b), circulant(order, d)
    At, Bt, Dt = transpose(A), transpose(B), transpose(D)
    assert A == At, "published A block must be symmetric"
    return block_matrix([
        [A, right_reverse(B), right_reverse(B), right_reverse(D)],
        [right_reverse(B), right_reverse(Dt), negate(A), right_reverse(negate(Bt))],
        [right_reverse(B), negate(A), right_reverse(negate(Dt)), right_reverse(Bt)],
        [right_reverse(D), right_reverse(negate(Bt)), right_reverse(Bt), negate(A)],
    ])


def verify_hadamard(matrix: Matrix) -> None:
    order = len(matrix)
    if any(len(row) != order for row in matrix):
        raise AssertionError("matrix is not square")
    if any(entry not in (-1, 1) for row in matrix for entry in row):
        raise AssertionError("matrix has an entry outside +/-1")
    if matrix != transpose(matrix):
        raise AssertionError("matrix is not symmetric")
    for i in range(order):
        for j in range(i, order):
            dot = sum(matrix[i][k] * matrix[j][k] for k in range(order))
            expected = order if i == j else 0
            if dot != expected:
                raise AssertionError(f"rows {i},{j} have dot product {dot}, expected {expected}")


def normalized_core(matrix: Matrix) -> Matrix:
    """Normalize the first row/column to +1 and delete them."""
    if matrix[0][0] == -1:
        matrix = negate(matrix)
    signs = matrix[0]
    normalized = [
        [signs[i] * matrix[i][j] * signs[j] for j in range(len(matrix))]
        for i in range(len(matrix))
    ]
    if any(entry != 1 for entry in normalized[0]):
        raise AssertionError("Hadamard normalization failed")
    return [row[1:] for row in normalized[1:]]


def verify_ramsey_core(core: Matrix, n: int) -> dict[str, int]:
    """Check the K_{2,n-1}/K_{2,n} common-neighbor conditions exactly."""
    vertices = len(core)
    expected_vertices = 4 * n - 5
    if vertices != expected_vertices:
        raise AssertionError(f"core has {vertices} vertices, expected {expected_vertices}")
    maximum_plus = maximum_minus = 0
    for i in range(vertices):
        for j in range(i + 1, vertices):
            common_plus = sum(
                k not in (i, j) and core[i][k] == core[j][k] == 1
                for k in range(vertices)
            )
            common_minus = sum(
                k not in (i, j) and core[i][k] == core[j][k] == -1
                for k in range(vertices)
            )
            maximum_plus = max(maximum_plus, common_plus)
            maximum_minus = max(maximum_minus, common_minus)
    if maximum_plus >= n - 1:
        raise AssertionError(f"+ color contains K_{{2,{n - 1}}}")
    if maximum_minus >= n:
        raise AssertionError(f"- color contains K_{{2,{n}}}")
    return {
        "vertices": vertices,
        "max_common_plus": maximum_plus,
        "max_common_minus": maximum_minus,
    }


def verify_instance(instance: dict) -> dict:
    n, v = int(instance["n"]), int(instance["v"])
    matrix = propus_hadamard(v, instance["A"], instance["B"], instance["D"])
    verify_hadamard(matrix)
    result = verify_ramsey_core(normalized_core(matrix), n)
    result.update({
        "n": n,
        "hadamard_order": len(matrix),
        "ramsey_value": 4 * n - 4,
        "source": instance["source"],
    })
    return result


def verify_all(path: Path = DEFAULT_DATA) -> list[dict]:
    data = json.loads(path.read_text())
    return [verify_instance(instance) for instance in data["instances"]]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=DEFAULT_DATA)
    args = parser.parse_args(argv)
    reports = verify_all(args.data)
    for report in reports:
        n = report["n"]
        print(
            f"VERIFIED R(K_{{2,{n - 1}}},K_{{2,{n}}})={report['ramsey_value']}: "
            f"Hadamard order {report['hadamard_order']}, core {report['vertices']}, "
            f"max codegrees +/{report['max_common_plus']} "
            f"-/{report['max_common_minus']}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
