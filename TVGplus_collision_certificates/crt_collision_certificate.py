"""Exact finite collision certificates by a sorted CRT window and pair recursion."""

from bisect import bisect_left, bisect_right
from fractions import Fraction
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))  # repository copy: JA_pair_recursion.py next to this script (only change to the archived script)
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "mixed_prime_research"))
from JA_pair_recursion import pair_counter


def residues(prime, denominator, level):
    values = [0]
    modulus = 1
    for index in range(1, level + 1):
        prev = modulus
        modulus = prime ** (index * index)
        bound = (modulus - 1) // denominator
        values = [
            x + j * prev
            for x in values
            for j in range(-((bound + x) // prev), (bound - x) // prev + 1)
        ]
    return modulus, [x % modulus for x in values]


def candidates(denominator, height, binary_level, ternary_level):
    assert denominator % 2 == 0
    relaxed = denominator // 2
    binary, left = residues(2, relaxed, binary_level)
    ternary, right = residues(3, relaxed, ternary_level)
    inverse = pow(binary, -1, ternary)
    transformed = sorted((x * inverse) % ternary for x in right)
    extra = []
    for prime, index in [(2, binary_level + 1), (3, ternary_level + 1)]:
        while (modulus := prime ** (index * index)) <= relaxed * height:
            extra.append((modulus, (modulus - 1) // relaxed))
            index += 1
    extra.sort()
    for x in left:
        if x > height:
            continue
        offset = (x * inverse) % ternary
        last = offset + (height - x) // binary
        for cycle in range(last // ternary + 1):
            base = cycle * ternary
            start = bisect_left(transformed, offset - base)
            stop = bisect_right(transformed, last - base)
            for i in range(start, stop):
                h = x + binary * (transformed[i] + base - offset)
                if h and all(not bound < h % q < q - bound for q, bound in extra):
                    yield h


def run(denominator, height, binary_level, ternary_level):
    left = pair_counter(2, denominator, 0)(height)
    right = pair_counter(3, denominator, 0)(height)
    mass = left * right
    energy = mass
    tested = contributing = 0
    for h in candidates(denominator, height, binary_level, ternary_level):
        tested += 1
        left_count = pair_counter(2, denominator, h)(height)
        if left_count:
            right_count = pair_counter(3, denominator, h)(height)
            if right_count:
                contributing += 1
                energy += 2 * left_count * right_count
    lower = (mass * mass + energy - 1) // energy
    maxima = []
    for prime, count_at_height in ((2, left), (3, right)):
        count = pair_counter(prime, denominator, 0)
        lo, hi = 0, height
        while lo < hi:
            mid = (lo + hi) // 2
            if count(mid) == count_at_height:
                hi = mid
            else:
                lo = mid + 1
        assert count(lo) == count_at_height
        assert lo == 0 or count(lo - 1) == count_at_height - 1
        maxima.append(lo)
    return {
        "denominator": denominator, "height": height, "binary_count": left,
        "ternary_count": right, "energy": energy, "positive_candidates": tested,
        "positive_contributing": contributing,
        "normalized_energy": str(Fraction((2 * height + 1) * energy, mass * mass)),
        "normalized_approx": (2 * height + 1) * energy / (mass * mass),
        "target_range": 2 * lower - (2 * height + 1) - 1,
        "binary_max": maxima[0], "ternary_max": maxima[1],
        "hull_target_range": 2 * lower - sum(maxima) - 2,
    }


def block_range(denominator, height, energy, grid_size, block_size):
    """Lower-bound difference-block masses by whole pairs of integer bins."""
    width = (height + grid_size) // grid_size
    starts = list(range(0, height + 1, width))

    def bins(prime):
        count = pair_counter(prime, denominator, 0)
        cumulative = [count(min(height, x + width - 1)) for x in starts]
        return [y - x for x, y in zip([0] + cumulative, cumulative)]

    a, b = bins(3), bins(2)
    masses = {}
    for i, na in enumerate(a):
        if not na:
            continue
        for j, nb in enumerate(b):
            group, offset = divmod(i - j, block_size)
            if nb and offset:
                masses[group] = masses.get(group, 0) + na * nb
    doubled_square_sum = 2 * sum(m * m for m in masses.values())
    bound = (doubled_square_sum - 1) // energy - block_size * width
    return {"width": width, "block_size": block_size, "squared_mass_twice": doubled_square_sum,
            "target_range": bound}


if __name__ == "__main__":
    print(run(*map(int, sys.argv[1:])), flush=True)
