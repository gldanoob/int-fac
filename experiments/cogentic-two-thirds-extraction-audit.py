"""Exact finite checks of the conservative schedule's extraction and saturation interfaces."""

from fractions import Fraction as Q
from itertools import chain, combinations
from math import ceil, floor, gcd, isqrt, lcm, prod


def evaluate(coefficients, argument):
    result = 0
    for coefficient in reversed(coefficients):
        result = result * argument + coefficient
    return result


def monic_with_roots(roots):
    coefficients = [1]
    for root in roots:
        coefficients = [a - root * b for a, b in zip([0] + coefficients, coefficients + [0])]
    return coefficients


def irreducible_binary(degree):
    for candidate in range(2**degree + 1, 2 ** (degree + 1), 2):
        for divisor in range(2, 2 ** (degree // 2 + 1)):
            remainder = candidate
            while remainder.bit_length() >= divisor.bit_length():
                remainder ^= divisor << (remainder.bit_length() - divisor.bit_length())
            if not remainder:
                break
        else:
            return candidate
    raise AssertionError("no irreducible polynomial")


def check_polynomials():
    degree, primorial, bound = 10, 210, 32
    bases = [17, 19, 23, 29, 31]
    mark_bound = 4 * degree * 2**15
    base_m = primorial * prod(bases) * 2**450
    modulus = base_m**degree - 1
    l0 = modulus.bit_length()
    width, precision, w = mark_bound**degree, 2**1600, Q(1, 4096)
    center0 = l0**2 * width * mark_bound
    leading = primorial // 2
    while leading * mark_bound**degree < 6 * precision * bound * primorial * base_m * center0:
        leading *= 3
    irreducible = irreducible_binary(degree)
    sign_pairs, grid_distances, polynomials = 0, 0, 0
    for prime in bases:
        assert gcd(modulus, primorial * prime * leading) == 1
        assert (base_m - 1)**degree < modulus < base_m**degree
        assert 4 * degree * mark_bound <= base_m and 4 * primorial * prime <= leading
        wanted = [r for r in range(prime) if r != base_m % prime][:degree]
        missing = next(s for s in range(prime)
                       if s not in {(pow(a, degree, prime) - a) % prime for a in range(prime)})
        local = [[leading * c for c in monic_with_roots(wanted)],
                 [-leading * missing, -leading] + [0] * (degree - 2) + [leading]]
        all_targets = [Q(i, 4 * degree) for i in range(1, 2 * degree + 1)]
        for field in range(2):
            centers = all_targets[field::2]
            target = [leading * c for c in monic_with_roots([mark_bound * r for r in centers])]
            step = primorial * prime
            start = []
            for j in range(degree):
                residue = next(r for r in range(step)
                               if r % 2 == (irreducible >> j) % 2
                               and r % (primorial // 2) == int(j == 0)
                               and r % prime == local[field][j] % prime)
                start.append(residue + step * floor((target[j] - residue) / step + Q(1, 2)))
            start.append(leading)
            correction = pow(step, -1, modulus) * evaluate(start, base_m) % modulus
            for j in range(degree):
                correction, digit = divmod(correction, base_m)
                start[j] -= step * digit
            assert not correction
            assert all(abs(x - t) < step * base_m for x, t in zip(start, target))
            cofactor, rem = divmod(evaluate(start, base_m), modulus)
            assert rem == 0 and 1 <= cofactor < 2 * leading and gcd(cofactor, step) == 1
            for u0, u1 in [(1, 1), (center0, l0**2 * width), (2 * center0, 2 * l0**2 * width)]:
                f = start[:]
                for j, change in enumerate([-base_m * u0, u0 - base_m * u1, u1]):
                    f[j] += step * change
                assert evaluate(f, base_m) == cofactor * modulus and gcd(*f) == 1
                assert max(map(abs, f)) <= 2**l0
                assert sum((a % 2) << j for j, a in enumerate(f)) == irreducible
                roots = [r for r in range(prime) if not evaluate(f, r) % prime]
                assert roots == (wanted if field == 0 else [])
                derivative = [j * f[j] for j in range(1, len(f))]
                assert all(evaluate(derivative, r) % prime for r in roots)
                delta = Q(1, 2**(19 * 1600 // 20))
                assert 8 * degree * delta < 1 and delta < w / 2
                for root in centers:
                    left = evaluate(f, mark_bound * (root - delta))
                    right = evaluate(f, mark_bound * (root + delta))
                    assert left * right < 0
                    sign_pairs += 1
                    for mark in [Q(3, 4)] + [t + w for t in all_targets]:
                        assert abs(mark - root) - delta >= w / 2 > Q(1, 2**l0)
                        grid_distances += 1
                polynomials += 1
    return polynomials, sign_pairs, grid_distances


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def order(a, modulus):
    x = a % modulus
    for k in range(1, modulus + 1):
        if x == 1:
            return k
        x = x * a % modulus
    raise AssertionError("nonunit")


def check_saturation():
    # Work with actual subgroup indices, including a repeated prime factor.
    # The uniform worst-case upper bound on those indices is tested separately.
    subsets, strict_indices, order_defects = 0, 0, 0
    for p, q in combinations([23, 29, 31, 37, 41, 43, 47], 2):
        for power in (1, 2):
            modulus = p**power * q
            for base_bound, generators in [(16, [11, 13]), (20, [11, 13, 17, 19])]:
                for selected in chain(combinations(generators, 1), combinations(generators, 2)):
                    star = lcm(2, *(lcm(order(a, p**power), order(a, q)) for a in selected))
                    assert all(pow(a, star, modulus) == 1 for a in selected)
                    indices = []
                    for r in (p, q):
                        size = lcm(*(order(a, r) for a in selected))
                        assert star % size == 0
                        assert len({a % r for a in selected}) == len(selected)
                        assert all(a < r and 2 * a > base_bound for a in selected)
                        indices.append((r - 1) // size)
                    cap = max(indices)
                    strict_indices += int(cap > 1)
                    order_defects += int(star % (p - 1) != 0 or star % (q - 1) != 0)
                    exponent = star * lcm(*range(1, cap + 1))
                    assert exponent % (p - 1) == exponent % (q - 1) == 0
                    subsets += 1
    return subsets, strict_indices, order_defects


def check_guards():
    # Upper rounding for Kidx and a fixed lower rounding for the count test.
    rounds = 0
    for bits in range(6, 600):
        log6bits = (6 * bits - 1).bit_length()
        for beta in range(3, 100):
            ceiling = (bits * log6bits + beta - 1) // beta
            assert beta * ceiling >= bits * log6bits
            assert 2**log6bits >= 6 * bits
            # 2/3 < ln(2) < 7/10, from the atanh(1/3) series.
            assert 3 * beta < 6 * beta * Q(2, 3)
            rounds += 1
    assert Q(1, 2) < Q(2, 3)
    for bits, beta in [(256, 48), (500, 70)]:
        exponent = beta + ceil(Q(bits * (6 * bits - 1).bit_length(), beta))
        assert exponent < bits // 2 - 1
    return rounds


if __name__ == "__main__":
    polynomials, brackets, distances = check_polynomials()
    subsets, strict_indices, defects = check_saturation()
    print(f"{polynomials} CRT field instances, {brackets} exact sign brackets, {distances} grid distances")
    print(f"{subsets} saturation instances, {strict_indices} proper subgroup indices, {defects} initially deficient exponents")
    print(f"{check_guards()} integer index/count guard checks")
