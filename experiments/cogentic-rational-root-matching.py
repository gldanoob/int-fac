"""Match certified modular roots through rational square classes and integer lifts."""

import argparse
import json
from fractions import Fraction
from math import gcd, isqrt, prod
from pathlib import Path
from runpy import run_path


SQUARES = run_path(str(Path(__file__).with_name("cogentic-quadratic-square-kernel.py")))
GRID = SQUARES["GRID"]


def matched_basis(n, witnesses):
    """Return (mask, normalized residue) for a basis of rationally square products."""
    if n <= 1 or n % 2 == 0:
        raise ValueError("expected an odd modulus greater than one")
    values, residues = [], []
    for value, root in witnesses:
        value = Fraction(value)
        if (gcd(value.numerator, n) != 1 or gcd(value.denominator, n) != 1
                or (root*root*value.denominator - value.numerator) % n):
            raise ValueError("each rational label needs a verified modular unit root")
        values.append(value)
        residues.append(root)
    size = len(values)
    basis = GRID["eliminate"](SQUARES["rational_words"](values), (1 << i for i in range(size)))
    matched = []
    for mask in basis:
        indices = list(GRID["support"](mask))
        value = prod(values[i] for i in indices)
        scale = SQUARES["rational_sqrt"](value)
        assert scale is not None and scale**2 == value
        numerator = prod(residues[i] % n for i in indices) * scale.denominator
        root = numerator * pow(scale.numerator, -1, n) % n
        assert root*root % n == 1
        matched.append((mask, root))
    return matched


def chart_matches(n, charts, *, primes=()):
    """Match explicit signed integer marks using the roots that can be reduced modulo N."""
    from sage.all import PolynomialRing, QQ

    if type(n) is not int or n <= 1 or n % 2 == 0:
        raise ValueError("expected an odd modulus greater than one")
    primes = tuple(primes)
    if primes:
        restrictions = run_path(str(Path(__file__).with_name("cogentic-local-square-restriction.py")))
    else:
        square_kernel = run_path(str(Path(__file__).with_name("cogentic-order-square-kernel.py")))["square_kernel"]
    ring = PolynomialRing(QQ, "x")
    x = ring.gen()
    generators, local, unavailable = [], [], []
    for index, chart in enumerate(charts):
        m, coefficients, points = (chart[key] for key in ("m", "field", "points"))
        if (type(m) is not int or len(coefficients) < 2 or coefficients[-1] != 1
                or any(type(c) is not int for c in coefficients)):
            raise ValueError("expected an integer base and a nonconstant monic integer polynomial")
        field = ring(coefficients)
        if field(m) % n or not field.is_irreducible():
            raise ValueError("expected an irreducible polynomial vanishing at its base modulo N")
        derivative = field.derivative()
        derivative_value = int(derivative(m))
        common = gcd(derivative_value, n)
        if 1 < common < n:
            return dict(status="derivative-gcd", chart=index, divisor=common, cofactor=n//common)
        marks, labels, slots = [], [], []
        points = tuple(points)
        for slot, (a, b) in enumerate(points):
            if type(a) is not int or type(b) is not int:
                raise ValueError("expected integer marked coefficients")
            value = a-b*m
            mark_gcd = gcd(value, n)
            if 1 < mark_gcd < n:
                return dict(status="mark-gcd", chart=index, point=(a, b), divisor=mark_gcd, cofactor=n//mark_gcd)
            if mark_gcd == 1:
                marks.append(a-b*x)
                labels.append(value)
                slots.append(slot)
        elements = [*marks, ring(-1)]
        if primes:
            masks, stats = restrictions["local_square_kernel"](field, elements, primes)
            complete, roots, residual_rank, tests, first = restrictions["SQUARES"]["complete_square_kernel"](
                field, elements, masks)
        else:
            complete, roots, residual_rank, tests, first = square_kernel(field, elements)
        assert complete and len(roots) + residual_rank == first
        local.append(dict(chart=index, first_dimension=first, square_dimension=len(roots),
                          residual_rank=residual_rank, tests=tests))
        if primes:
            local[-1]["restrictions"] = [(None if p is None else int(p), r, q) for p, r, q in stats]
        labels.append(-1)
        slots.append(len(points))
        unresolved = False
        for mask, root in roots:
            support = list(GRID["support"](mask))
            label = prod(labels[j] for j in support)
            denominator = int(root.denominator())
            denominator_gcd = gcd(denominator, n)
            if 1 < denominator_gcd < n:
                return dict(status="denominator-gcd", chart=index, divisor=denominator_gcd,
                            cofactor=n//denominator_gcd)
            if denominator_gcd == 1:
                numerator = denominator * root
            elif common == 1:
                # A square root of an integral product is integral in the field.
                numerator = (derivative * root) % field
                assert numerator.denominator() == 1
                denominator = derivative_value
            else:
                unresolved = True
                continue
            residue = int(numerator(m)) * pow(denominator, -1, n) % n
            assert residue*residue % n == label % n
            original_mask = sum(1 << slots[j] for j in support)
            generators.append(dict(chart=index, mask=original_mask, label=label, residue=residue,
                                   root=[str(c) for c in root.list()]))
        if unresolved:
            unavailable.append(index)

    basis = matched_basis(n, [(item["label"], item["residue"]) for item in generators])
    result = dict(generators=generators, basis=basis, local=local, unavailable=unavailable,
                  rational_rank=len(generators)-len(basis))
    for mask, residue in basis:
        divisor = gcd(residue-1, n)
        if 1 < divisor < n:
            return dict(result, status="square-split", match=mask, divisor=divisor, cofactor=n//divisor)
    return dict(result, status="incomplete" if unavailable else "complete-no-split")


def replay():
    n = 93
    fields = [(1, (72, 20, 1), (9, 2)), (2, (51, 19, 1), (30, 1))]
    witnesses = []
    for m, (constant, linear, leading), (a, b) in fields:
        assert leading == 1 and m*m + linear*m + constant == n
        disc = linear*linear - 4*constant
        assert disc > 0 and isqrt(disc)**2 != disc and gcd(2*m+linear, n) == 1
        assert (constant, linear) == (81-a, 18+b)  # (X+9)^2 - (a-bX)
        witness = (a-b*m, m+9)
        assert matched_basis(n, [witness]) == []
        witnesses.append(witness)
    assert witnesses == [(7, 10), (28, 11)]
    first, = matched_basis(n, witnesses)
    assert first == (3, 61) and gcd(first[1]-1, n) == 3
    ceil_sqrt = isqrt(n-1)+1
    lift = (ceil_sqrt**2 - n, ceil_sqrt)
    assert matched_basis(n, [witnesses[1], lift]) == [first]
    # Replacing 7 by 7/4 changes its root by the same rational factor.
    assert matched_basis(n, [(Fraction(7, 4), 5), witnesses[1]]) == [first]
    for nonunit in (Fraction(7, 3), Fraction(31, 4)):
        try:
            matched_basis(n, [(nonunit, 2)])
        except ValueError:
            pass
        else:
            raise AssertionError("a numerator or denominator shares a prime with the modulus")

    # A different representative of the same modular unit can introduce a match.
    assert matched_basis(65, [(56, 11), (79, 12)]) == []
    lifted, = matched_basis(65, [(56, 11), (79-65, 12)])
    assert lifted == (3, 14) and gcd(lifted[1]-1, 65) == 13

    # Compare the generated kernel and its sign map with every compatible subset.
    tested = 0
    for modulus in (15, 45, 65, 77, 93, 105, 221, 437):
        menu = [(r*r-k*modulus, r) for r, k in ((2, 0), (2, 1), (4, 1), (7, 1),
                                                 (8, 1), (11, 1), (13, 2), (16, 2))
                if gcd(r, modulus) == 1]
        menu += [(4*value, 2*root) for value, root in menu[1:3]]
        span = {0: 1}
        for mask, root in matched_basis(modulus, menu):
            span.update({v ^ mask: z*root % modulus for v, z in span.items()})
        for mask in range(1 << len(menu)):
            selected = [menu[i] for i in GRID["support"](mask)]
            value = prod(v for v, _ in selected)
            ok = value > 0 and isqrt(value)**2 == value
            assert (mask in span) == ok
            if ok:
                z = prod(r for _, r in selected) * pow(isqrt(value), -1, modulus) % modulus
                assert (z-span[mask]) % modulus == 0 or (z+span[mask]) % modulus == 0
            tested += 1
    bounded = run_path(str(Path(__file__).with_name("cogentic-quadratic-grid-norms.py")))["bounded_words"]
    large = [101*103, 107**2*109, (113*127)**2, -131*137]
    grid_values = [1, -1, 2*large[0], *large, -large[1], large[0]]
    # Squares, repeated and signed tails, partial gcds, and new public-only primes.
    for extras in ([], [103*107], [103*131, 101*137, 2*109, 139],
                   [-101*109, 107, 137*113, 139*149, 139, 149, 151**2]):
        raw = [*grid_values, *extras]
        encoded = bounded(grid_values, 13, extra_values=extras)
        exact = SQUARES["rational_words"](raw)
        masks = [1 << j for j in range(len(raw))]
        assert GRID["eliminate"](encoded, masks) == GRID["eliminate"](exact, masks)
    print(f"independent bases and a canonical lift split 93; {tested} subset matches checked; "
          "four auxiliary-label kernels agree with unrestricted gcd refinement")

    cubic = dict(m=1, field=[49, 33, 10, 1], points=[(16, 9)])
    quadratic = dict(m=2, field=[51, 19, 1], points=[(30, 1)])
    positive = chart_matches(93, [cubic, quadratic])
    assert positive["status"] == "square-split" and positive["divisor"] in (3, 31)
    assert [(g["chart"], g["label"]) for g in positive["generators"]] == [(0, 7), (1, 28)]
    same_sign = dict(m=3, field=[258, 35, 1], points=[(31, 1)])
    negative = chart_matches(93, [cubic, same_sign])
    assert negative["status"] == "complete-no-split" and negative["rational_rank"] == 1
    (mask, residue), = negative["basis"]
    assert mask == 3 and residue in (1, 92)
    repeated = dict(cubic, points=[(93, 0), (2, 0), (2, 0), (2, 0)])
    overlap = chart_matches(93, [repeated])
    assert overlap["status"] == "complete-no-split"
    assert [g["mask"] for g in overlap["generators"]] == [6, 10]
    assert overlap["rational_rank"] == 0 and len(overlap["basis"]) == 2
    singular = dict(m=0, field=[93**2, 0, 1], points=[])
    unresolved = chart_matches(93, [singular, cubic, same_sign])
    assert unresolved["status"] == "incomplete" and unresolved["unavailable"] == [0]
    assert chart_matches(93, [singular, cubic, quadratic])["status"] == "square-split"
    assert chart_matches(93, [dict(singular, field=[93, 93, 1])])["status"] == "complete-no-split"
    exposed = chart_matches(93, [dict(singular, field=[93, 3, 1])])
    assert exposed["status"] == "derivative-gcd" and exposed["divisor"] == 3
    exposed = chart_matches(93, [dict(cubic, points=[(3, 0)])])
    assert exposed["status"] == "mark-gcd" and exposed["divisor"] == 3
    exposed = chart_matches(895, [dict(m=29, field=[54, 0, -28, 1], points=[(18, 13), (0, 1)])])
    assert exposed["status"] == "denominator-gcd" and exposed["divisor"] == 5
    cleared = chart_matches(15, [dict(m=4, field=[54, 0, -28, 1], points=[(24, -10)])])
    root, = cleared["generators"]
    assert root["mask"] == 1 and root["label"] == 64
    assert Fraction(root["root"][-1]).denominator == 15
    assert root["residue"]**2 % 15 == 64 % 15
    restricted = chart_matches(93, [cubic, quadratic], primes=(2, 3))
    assert restricted["status"] == positive["status"] and restricted["basis"] == positive["basis"]
    assert [p for p, _, _ in restricted["local"][0]["restrictions"]] == [None, 2, 3]
    assert positive["local"][1]["residual_rank"] == 1 and restricted["local"][1]["residual_rank"] == 0
    print("Cubic different-base match and rank-one negative certificate verified")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--charts", type=Path, help="JSON object with n and explicit charts")
    args = parser.parse_args()
    if args.charts is None:
        replay()
    else:
        library = json.loads(args.charts.read_text())
        print(json.dumps(chart_matches(library["n"], library["charts"], primes=library.get("primes", ()))))
