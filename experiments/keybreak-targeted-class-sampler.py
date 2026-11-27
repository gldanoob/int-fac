#!/usr/bin/env python3
"""Draw targeted quadratic classes of discriminant -8N, or check small fixtures."""

from argparse import ArgumentParser
from collections import Counter, defaultdict
from math import gcd
from pathlib import Path
from random import Random, SystemRandom
from runpy import run_path

from sage.all import Integer


HERE = Path(__file__).parent
DIRECT = run_path(str(HERE / "keybreak-direct-class-sampler.py"))
FORMS = run_path(str(HERE / "keybreak-quadratic-class-roots.py"))
crt_root = DIRECT["crt_root"]
local_roots = DIRECT["local_roots"]
sample_reduced_class = DIRECT["sample_reduced_class"]
canonical_forms = FORMS["canonical_forms"]
prime_to_input = FORMS["prime_to_input"]
reduce_form = FORMS["reduce_form"]
oriented_square = FORMS["oriented_square"]


def unit_target(n, v):
    if n <= 1 or n % 2 == 0:
        raise ValueError("N must be odd and greater than one")
    if gcd(n, v) != 1:
        raise ValueError("v must be a unit modulo N")
    return v % n


def sample_orientation(n, v, rng):
    """Fix one verified oriented public ideal for all private draws."""
    v = unit_target(n, v)
    if v == 1:
        return 1, 0
    jacobi = int(Integer(v).jacobi(n))
    modulus = 8 * n
    split_classes = []
    for r in (1, 3, 5, 7):
        reciprocity = -1 if n % 4 == r % 4 == 3 else 1
        if int(Integer(-2).jacobi(r)) * reciprocity * jacobi == 1:
            split_classes.append(crt_root(((n, v), (8, r))))
    lower = n**3
    for _ in range(8):
        progressions = []
        for residue in split_classes:
            first = lower + (residue - lower) % modulus
            count = (2 * lower - 1 - first) // modulus + 1
            if count > 0:
                progressions.append((first, count))
        for _ in range(64 * n.bit_length()**2 if progressions else 0):
            first, count = rng.choice(progressions)
            candidate = first + modulus * rng.randrange(count)
            if Integer(candidate).is_prime(proof=True):
                _, roots = local_roots(-2 * n, candidate, 1)
                if candidate % n != v or len(roots) != 2:
                    raise ArithmeticError("public prime failed its target or splitting check")
                root = rng.choice(roots)
                if (root * root + 2 * n) % candidate:
                    raise ArithmeticError("incorrect public orientation root")
                return candidate, root
        lower *= 2
    raise RuntimeError("no split prime found within the bounded dyadic search")


def translate_square(n, v, seed, orientation):
    """Reduce I²P and retain its comparison root, before the global sign draw."""
    prime, public_root = orientation
    if prime == 1:
        return oriented_square(seed, n, radicand=2 * n)
    a, b, c = seed
    content = gcd(a, 2 * b)
    q = a // content
    if content not in (1, 2) or q % 2 == 0 or gcd(a, n * prime) != 1:
        raise ValueError("the seed norm must be coprime to N and the public prime")
    slope = 2 * b // content
    inverse = pow(slope, -1, q) if q > 1 else 0
    bezout = (1 - inverse * slope) // q
    square_middle = (bezout * q * b + inverse * ((b * b - 2 * n) // content)) % (q * q)
    leading = q * q * prime
    middle = crt_root(((q * q, square_middle), (prime, public_root)))
    trailing, remainder = divmod(middle * middle + 2 * n, leading)
    if remainder or a * c != b * b + 2 * n:
        raise ArithmeticError("incorrect ideal product")
    form, (x, y) = reduce_form(leading, middle, trailing)
    root = (leading * x + middle * y) * pow(q, -1, n) % n
    if root * root % n != v * form[0] % n:
        raise ArithmeticError("comparison root failed z² ≡ vA modulo N")
    return form, root


def draw(n, v, orientation, rng):
    """Draw from the coprime canonical seed law, adding an independent global sign."""
    seed, _ = sample_reduced_class(n, rng, radicand=2 * n)
    form, root = translate_square(n, v, seed, orientation)
    root = rng.choice((root, -root % n))
    if root * root % n != v * form[0] % n:
        raise ArithmeticError("comparison root failed z² ≡ vA modulo N")
    return form, root


def check_exact(n, v, forms, orientation):
    """Enumerate every seed class and every root of each unit target form."""
    relative = defaultdict(Counter)
    full = defaultdict(Counter)
    output_classes = Counter()
    for seed in forms:
        form, root = translate_square(n, v, prime_to_input(seed, n), orientation)
        output_classes[form] += 1
        if gcd(form[0], n) == 1:
            relative[form][min(root, -root % n)] += 1
            full[form].update((root, -root % n))

    roots_by_value = defaultdict(set)
    for z in range(n):
        roots_by_value[z * z % n].add(z)
    expected = {
        form: roots_by_value[v * form[0] % n]
        for form in forms
        if gcd(form[0], n) == 1 and roots_by_value[v * form[0] % n]
    }
    assert len(set(output_classes.values())) == 1
    assert set(full) == set(expected)
    for form, roots in expected.items():
        assert set(full[form]) == roots and len(set(full[form].values())) == 1
        relative_roots = {min(z, -z % n) for z in roots}
        assert set(relative[form]) == relative_roots and set(relative[form].values()) == {2}
    return expected


def check_fixtures(rng):
    checked, fibers, sampled = 0, 0, 0
    jacobi_signs = set()
    for n in (3, 9, 15, 45, 63, 105):
        forms = tuple(canonical_forms(2 * n))
        for v in range(1, n):
            if gcd(n, v) != 1:
                continue
            jacobi_signs.add(int(Integer(v).jacobi(n)))
            orientation = sample_orientation(n, v, rng)
            prime, public_root = orientation
            expected = check_exact(n, v, forms, orientation)
            if prime != 1:
                assert expected == check_exact(n, v, forms, (prime, -public_root % prime))
            checked += 1
            fibers += len(expected)
            for _ in range(3):
                form, root = draw(n, v, orientation, rng)
                if gcd(form[0], n) == 1:
                    assert root in expected[form]
                else:
                    assert 1 < gcd(form[0], n) < n
                sampled += 1
    assert jacobi_signs == {-1, 1}
    for n, v in ((1, 1), (4, 1), (9, 0), (9, 3), (15, -10)):
        try:
            unit_target(n, v)
        except ValueError:
            continue
        raise AssertionError("accepted an invalid modulus or target")
    assert unit_target(9, -1) == 8 and unit_target(9, 19) == 1
    print(f"Exhaustive uniform whole-class law: {checked} unit targets, {fibers} unit fibers")
    print(f"Sampled coprime canonical seed law: {sampled} checked draws")


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("N", nargs="?", type=int, help="odd modulus, paired with v")
    parser.add_argument("v", nargs="?", type=int, help="target unit modulo N")
    parser.add_argument("--draws", type=int, default=1, help="number of private draws")
    parser.add_argument("--seed", type=int, help="reproducible experiment seed")
    args = parser.parse_args()
    rng = SystemRandom() if args.seed is None else Random(args.seed)
    if args.N is None:
        check_fixtures(rng)
        return
    if args.v is None or args.draws < 1:
        parser.error("sampling requires N, v, and a positive draw count")
    try:
        v = unit_target(args.N, args.v)
        orientation = sample_orientation(args.N, v, rng)
    except (ValueError, RuntimeError) as error:
        parser.error(str(error))
    print(f"Coprime canonical seed law at N={args.N}, v={v}, public orientation={orientation}")
    for _ in range(args.draws):
        (a, b, c), root = draw(args.N, v, orientation, rng)
        factor = gcd(a, args.N)
        if factor != 1:
            print(f"A={a}, gcd(A, N)={factor}")
        else:
            print(f"[A, 2b, C]=[{a}, {2 * b}, {c}], z={root}")


if __name__ == "__main__":
    main()
