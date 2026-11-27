"""Sample unit reduced forms of discriminants -4N and -8N with factored leading coefficient."""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import gcd, isqrt, prod
from pathlib import Path
from random import Random
from runpy import run_path

from sage.all import GF, Integer


def factored_integer(limit, rng):
    """Kalai's uniform factored integer draw on [1, limit]."""
    if limit < 1:
        raise ValueError("the sampling interval must be nonempty")
    while True:
        factors = Counter()
        value = 1
        bound = limit
        while bound > 1:
            bound = rng.randrange(1, bound + 1)
            if Integer(bound).is_prime(proof=True):
                factors[bound] += 1
                value *= bound
            if value > limit:
                break
        else:
            if rng.randrange(limit) < value:
                return value, factors


def local_roots(value, prime, exponent):
    """Return the local roots for a unit or the ramified -8N dyadic branch."""
    if exponent < 1:
        raise ValueError("expected a positive prime-power exponent")
    if prime == 2 and value % 4 == 2:
        return 2**exponent, (0,) if exponent == 1 else ()
    if value % prime == 0:
        raise ValueError("expected a unit outside the ramified dyadic branch")
    if prime == 2:
        roots = [1]
        modulus = 2
        for _ in range(1, exponent):
            roots = [
                lift for root in roots for lift in (root, root + modulus)
                if (lift * lift - value) % (2 * modulus) == 0
            ]
            modulus *= 2
        return modulus, tuple(roots)

    if pow(value, (prime - 1) // 2, prime) != 1:
        return prime**exponent, ()
    root = int(GF(prime)(value).sqrt())
    root = min(root, prime - root)
    slope_inverse = pow(2 * root, -1, prime)
    modulus = prime
    for _ in range(1, exponent):
        root += modulus * (((value - root * root) // modulus) * slope_inverse % prime)
        modulus *= prime
    return modulus, (root, (-root) % modulus)


def crt_root(lifts):
    """Combine one chosen residue at each of the coprime local moduli."""
    value, modulus = 0, 1
    for prime_power, root in lifts:
        value += modulus * ((root - value) * pow(modulus, -1, prime_power) % prime_power)
        modulus *= prime_power
    return value


def center_root(root, leading):
    return root if 2 * root <= leading else root - leading


def canonical_from_root(radicand, leading, root):
    middle = center_root(root, leading)
    trailing, remainder = divmod(radicand + middle * middle, leading)
    if remainder or trailing < leading or (trailing == leading and middle < 0):
        return None
    if gcd(leading, gcd(2 * middle, trailing)) != 1:
        return None
    return leading, middle, trailing


def proposal_bounds(n, *, radicand=None):
    if n <= 1 or n % 2 == 0:
        raise ValueError("N must be odd and greater than one")
    radicand = n if radicand is None else radicand
    if radicand not in (n, 2 * n):
        raise ValueError("expected radicand N or 2N")
    upper = isqrt(4 * radicand // 3)
    last = (upper - 1).bit_length()
    return upper, 1 << last, last


def sample_reduced_class(n, rng, *, radicand=None):
    """Return ((A, b, C), factorization of A) for the form [A, 2b, C]."""
    radicand = n if radicand is None else radicand
    upper, power, last = proposal_bounds(n, radicand=radicand)
    while True:
        stage = rng.randrange(last + 1)
        start = 1 << stage
        d, factors_d = factored_integer(2 * start, rng)
        e, factors_e = factored_integer(power // start, rng)
        leading = d * e
        if not (start <= d < 2 * start and leading <= upper):
            continue
        if any(exponent != 1 for exponent in factors_d.values()) or gcd(leading, n) != 1:
            continue

        factors = factors_d + factors_e
        branches = [local_roots(-radicand, p, exponent) for p, exponent in factors.items()]
        root_count = prod(len(roots) for _, roots in branches)
        if rng.randrange(1 << (len(factors) + 1)) >= root_count:
            continue
        root = crt_root((modulus, rng.choice(roots)) for modulus, roots in branches)
        form = canonical_from_root(radicand, leading, root)
        if form is not None:
            return form, factors


def check_factored_weights(limit):
    # At bound p, repeated draws of p have geometric weights. A smaller
    # draw starts the same law as a fresh chain with bound p - 1.
    weights = [Fraction(value == 1) for value in range(limit + 1)]
    for bound in range(2, limit + 1):
        if not Integer(bound).is_prime(proof=True):
            continue
        previous = weights
        weights = [Fraction(0)]
        for value in range(1, limit + 1):
            weight = Fraction(bound - 1, bound) * previous[value]
            if value % bound == 0:
                weight += weights[value // bound] / bound
            weights.append(weight)
    accepted = {weights[value] * value / limit for value in range(1, limit + 1)}
    assert len(accepted) == 1 and next(iter(accepted)) > 0


def check_proposal_weights(n, canonical_forms, *, radicand=None):
    radicand = n if radicand is None else radicand
    upper, power, last = proposal_bounds(n, radicand=radicand)
    multiplicities = Counter()
    for stage in range(last + 1):
        start = 1 << stage
        for d in range(start, 2 * start):
            factors_d = Integer(d).factor()
            if any(exponent != 1 for _, exponent in factors_d):
                continue
            for e in range(1, power // start + 1):
                if d * e <= upper:
                    multiplicities[d * e] += 1

    weights = {}
    for leading in range(1, upper + 1):
        factors = [(int(p), int(k)) for p, k in Integer(leading).factor()]
        assert multiplicities[leading] == 1 << len(factors)
        if gcd(leading, n) != 1:
            continue
        branches = [local_roots(-radicand, p, exponent) for p, exponent in factors]
        lifts = [[(modulus, root) for root in roots] for modulus, roots in branches]
        roots = {crt_root(choice) for choice in product(*lifts)}
        assert roots == {root for root in range(leading) if (root * root + radicand) % leading == 0}
        if not roots:
            continue
        mass = (
            Fraction(multiplicities[leading], 2 * power * (last + 1))
            * Fraction(len(roots), 1 << (len(factors) + 1))
            / len(roots)
        )
        for root in roots:
            form = canonical_from_root(radicand, leading, root)
            if form is not None:
                assert form not in weights
                weights[form] = mass

    assert weights.keys() == {form for form in canonical_forms(radicand) if gcd(form[0], n) == 1}
    assert all(mass == Fraction(1, 4 * power * (last + 1)) for mass in weights.values())
    return weights


def parity_dependency(masks):
    """Return a dependency using only the public parity masks."""
    basis = {}
    for index, mask in enumerate(masks):
        selected = 1 << index
        while mask:
            pivot = mask.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = mask, selected
                break
            known_mask, known_selected = basis[pivot]
            mask ^= known_mask
            selected ^= known_selected
        else:
            return [i for i in range(index + 1) if (selected >> i) & 1]
    return None


def check_composed_split(n, oriented_square, seed, *, radicand=None):
    """Trial division stands in for analytic field descent in this finite check."""
    factor_base = (2, 3, 5, 7, 11, 13)
    rng, signs = Random(seed), Random(seed + 1)
    for _ in range(12):
        public_factors, public_masks, private_roots = [], [], []
        for _ in range(1000):
            form, _ = sample_reduced_class(n, rng, radicand=radicand)
            (leading, _, _), root = oriented_square(form, n, radicand=radicand)
            if gcd(leading, n) != 1:
                continue
            cofactor = leading
            exponents = [0] * len(factor_base)
            for index, prime in enumerate(factor_base):
                while cofactor % prime == 0:
                    exponents[index] += 1
                    cofactor //= prime
            mask = sum((exponent % 2) << i for i, exponent in enumerate(exponents))
            if cofactor != 1 or mask == 0 or mask in public_masks:
                continue
            public_factors.append(exponents)
            public_masks.append(mask)
            private_roots.append((-root if signs.randrange(2) else root) % n)
            selected = parity_dependency(public_masks)
            if selected is None:
                continue

            # Open the private root records only after the public solver chooses.
            assert len(selected) >= 3
            totals = [sum(public_factors[i][j] for i in selected) for j in range(len(factor_base))]
            assert all(exponent % 2 == 0 for exponent in totals)
            public_root = prod(prime**(exponent // 2) for prime, exponent in zip(factor_base, totals))
            private_root = prod(private_roots[i] for i in selected) % n
            assert (private_root**2 - public_root**2) % n == 0
            for candidate in (private_root - public_root, private_root + public_root):
                divisor = gcd(candidate, n)
                if 1 < divisor < n:
                    assert n % divisor == 0
                    return divisor, [public_masks[i] for i in selected]
            break
    raise AssertionError("the composed regression did not find a proper divisor")


if __name__ == "__main__":
    reference = run_path(str(Path(__file__).with_name("keybreak-quadratic-class-roots.py")))
    for limit in range(1, 51):
        check_factored_weights(limit)
    fixtures = (3, 15, 21, 45, 55, 63, 105, 175, 225, 315, 525)
    try:
        proposal_bounds(10)
    except ValueError:
        pass
    else:
        raise AssertionError("even N must be rejected")

    print("50 exact Kalai interval-weight checks")
    for multiplier, composed in ((1, (241 * 269, 43**2 * 47)), (2, (211 * 223, 43**2 * 47))):
        weights = {
            n: check_proposal_weights(n, reference["canonical_forms"], radicand=multiplier * n)
            for n in fixtures
        }
        assert any(form[0] % 2 == 0 for forms in weights.values() for form in forms)
        assert any(
            gcd(form[0], n) > 1 for n in fixtures for form in reference["canonical_forms"](multiplier * n)
        )
        if multiplier == 2:
            for n in fixtures:
                assert (2, 0, n) in weights[n]
                assert local_roots(-2 * n, 2, 1) == (2, (0,))
                assert local_roots(-2 * n, 2, 2) == (4, ())

        rng = Random(20261127)
        examples = []
        saw_even_seed = False
        for n in fixtures:
            for _ in range(8):
                form, factors = sample_reduced_class(n, rng, radicand=multiplier * n)
                assert form in weights[n]
                assert prod(p**exponent for p, exponent in factors.items()) == form[0]
                assert all(Integer(p).is_prime(proof=True) for p in factors)
                _, root = reference["oriented_square"](form, n, radicand=multiplier * n)
                assert 0 <= root < n
                saw_even_seed |= form[0] % 2 == 0
            examples.append((n, form, sorted(factors.items())))
        assert saw_even_seed
        print(f"-{4 * multiplier}N: {len(fixtures)} fixtures, {sum(map(len, weights.values()))} exact pointwise weights")
        print(f"{8 * len(fixtures)} seeded draws checked; last draw for each fixture:")
        for example in examples:
            print(example)
        for n in composed:
            divisor, masks = check_composed_split(
                n, reference["oriented_square"], seed=20261127, radicand=multiplier * n
            )
            print(f"composed split of {n}: divisor {divisor}, public dependency {masks}")
