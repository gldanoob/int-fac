"""Exact suffix lists, absolute miss counts and worst subsets in a finite sampler."""

from fractions import Fraction
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path


spec = spec_from_file_location("advice", Path(__file__).with_name("cogentic-extractor-advice.py"))
advice = module_from_spec(spec)
spec.loader.exec_module(advice)


def main():
    width = 3
    space = 1 << width
    floor_cost = 1
    cap = 1 << width
    shifts = (0, 1, 2, 4)
    multipliers = (1, 3, 5, 15, 17, 51, 85, 255)
    values = [[advice.multiply(a, s) >> (8-width) for s in multipliers] for a in range(256)]
    worst_ratio = Fraction(0)
    restrictions = moment_tests = nonzero_misses = 0
    for target in range(1, 1 << space):
        good = {x for x in range(space) if (target >> x) & 1}
        amplified = {x for x in range(space) if any((x ^ s) in good for s in shifts)}
        assert 2*len(amplified) >= space
        costs = [cap]*len(values)
        tail = []
        for i in range(width):
            projected = {x >> i for x in amplified}
            assert 2*len(projected) >= (space >> i)
            missing = []
            for a, row in enumerate(values):
                outputs = {((x >> i) << i) + h for x in row for h in range(1 << i)}
                direct = not amplified.isdisjoint(outputs)
                prefix = any(x >> i in projected for x in row)
                assert direct == prefix
                if direct:
                    costs[a] = min(costs[a], 1 << i)
                else:
                    missing.append(a)
            tail.append(len(missing))
            nonzero_misses += bool(missing)
            worst_ratio = max(worst_ratio, Fraction(len(missing), space >> i))
            restrictions += 1
        for r in (1, 2, 3):
            largest = sorted((c**r for c in costs), reverse=True)
            for h in (1, 3, 11, 37, 90, 127, 256):
                # The h most costly masters dominate every arbitrary h-subset.
                tail_bound = h*floor_cost + sum(
                    ((2 << i)**r - (1 << i)**r)*min(h, count)
                    for i, count in enumerate(tail)
                )
                assert sum(largest[:h]) <= tail_bound
                moment_tests += 1
    assert worst_ratio <= 8
    print(f"{restrictions} target-stage projections; {nonzero_misses} nonempty miss sets; "
          f"maximal absolute miss ratio {worst_ratio}; {moment_tests} arbitrary-set moment bounds")


if __name__ == "__main__":
    main()
