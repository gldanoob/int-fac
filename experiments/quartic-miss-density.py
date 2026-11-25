"""Exact quadratic-character probabilities for the quartic coefficient box."""
from fractions import Fraction
from itertools import product
from math import isqrt, prod
from runpy import run_path
from pathlib import Path

helpers = run_path(str(Path(__file__).with_name("cubic-resolvent-profiles.py")))
eliminate, squareclass = helpers["eliminate"], helpers["squareclass"]


def torsion(coeffs):
    # Reduce X^65 by repeated multiplication by X in the quartic quotient.
    powers = [1, 0, 0, 0]
    for _ in range(65):
        lead = powers[-1]
        powers = [v - lead * c for v, c in zip([0, *powers[:3]], coeffs)]
    return powers[1:] == [0, 0, 0]


def constraints(height):
    events = set()
    for a, b, s in product(range(1, height + 1), range(-height, height + 1),
                            range(-isqrt(height), isqrt(height) + 1)):
        if not s or abs(s*a) > height:
            continue
        delta1 = a*a - 4*(b - 2*s)
        delta2 = (b + 2*s)**2 - 4*s*a*a
        if delta1 and delta2 and not torsion((s*s, s*a, b, a)):
            positive, negative1, negative2 = map(squareclass, (s, delta1, delta2))
            if not negative1 or not negative2 or positive in (negative1, negative2):
                continue
            events.add((positive, *sorted([negative1, negative2], key=lambda v: sorted(v))))
    return events


def miss_density(events, mod4):
    terms = []
    variables = set()
    for event in events:
        scope = tuple(sorted(set().union(*event) - {-1}))
        variables.update(scope)
        table = {}
        for bits in product((0, 1), repeat=len(scope)):
            assignment = dict(zip(scope, bits))
            assignment[-1] = int(mod4 == 3)
            signs = tuple(sum(assignment[v] for v in row) % 2 for row in event)
            table[bits] = int(signs != (0, 1, 1))
        terms.append((scope, table))
    factors, _ = eliminate(terms, variables, lambda _, rows: (sum(map(prod, rows)), None))
    return Fraction(prod(factors), 2**len(variables))


expected = ((27,64,3,4), (15,64,9,64), (45,1024,9,128),
            (19,1024,1,128), (351,32768,9,4096))
for height, (n1,d1,n3,d3) in enumerate(expected, start=1):
    events = constraints(height)
    one, three = (miss_density(events, mod4) for mod4 in (1, 3))
    both = (one + three) / 2
    assert (one, three) == (Fraction(n1,d1), Fraction(n3,d3))
    print(height, one, three, both)
