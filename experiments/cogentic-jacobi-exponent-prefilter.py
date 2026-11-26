"""Check the Jacobi prefilter against all units of small odd moduli."""

from math import gcd, lcm


def jacobi(a, n):
    a %= n
    sign = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                sign = -sign
        if a % 4 == n % 4 == 3:
            sign = -sign
        a, n = n % a, a
    return sign if n == 1 else 0


def v2(x):
    return (x & -x).bit_length() - 1


def test(n, factors):
    primes = list(factors)
    u = [v2(p - 1) for p in primes]
    s = min(u)
    odd_minimum = sum(factors[p] for p, height in zip(primes, u) if height == s) % 2
    assert (v2(n - 1) == s) == bool(odd_minimum)

    exponent = lcm(*(p ** (e - 1) * (p - 1) for p, e in factors.items()))
    units = [a for a in range(1, n) if gcd(a, n) == 1]
    failures = 0
    involutions = []
    odd = exponent >> v2(exponent)
    for a in units:
        x = pow(a, odd, n)
        gcds = []
        for _ in range(v2(exponent)):
            gcds.append(gcd(x - 1, n))
            x = x * x % n
        assert x == 1
        heights = {
            next(h for h in range(v2(exponent) + 1) if pow(a, odd << h, p) == 1)
            for p in primes
        }
        failed = all(d in (1, n) for d in gcds)
        assert failed == (len(heights) == 1)
        if jacobi(a, n) == -1 and failed:
            failures += 1
        if a * a % n == 1:
            involutions.append(a)

    index = 2 ** (len(primes) + sum(height - s for height in u))
    assert failures * index == odd_minimum * len(units)
    signatures = {}
    quotient_signatures = {}
    small_units = [a for a in units if a <= 3 * n.bit_length() ** 2]
    probes = [a for a in small_units if jacobi(a, n) == 1]
    negatives = [a for a in small_units if jacobi(a, n) == -1]
    if negatives:
        probes.extend(a * negatives[0] for a in negatives)
    inv_two = (n + 1) // 2
    for z in involutions:
        visible = tuple(z % p == 1 for p in primes if factors[p] % 2)
        signature = tuple(
            jacobi(((t + 1) + (t - 1) * z) * inv_two, n) for t in units
        )
        assert signatures.setdefault(signature, visible) == visible
        quotient_signature = tuple(
            jacobi(((t + 1) + (t - 1) * z) * inv_two, n) for t in probes
        )
        canonical = tuple(sign == visible[0] for sign in visible)
        assert quotient_signatures.setdefault(quotient_signature, canonical) == canonical
    assert len(signatures) == 2 ** sum(e % 2 for e in factors.values())
    assert len(quotient_signatures) == 2 ** max(sum(e % 2 for e in factors.values()) - 1, 0)
    return len(units), len(involutions), failures


if __name__ == "__main__":
    moduli = unit_count = involution_count = failed_negative = 0
    for n in range(3, 513, 2):
        remaining = n
        factors = {}
        for p in range(3, n + 1, 2):
            while remaining % p == 0:
                factors[p] = factors.get(p, 0) + 1
                remaining //= p
            if remaining == 1:
                break
        if len(factors) < 2:
            continue
        units, involutions, failures = test(n, factors)
        moduli += 1
        unit_count += units
        involution_count += involutions
        failed_negative += failures
    print(f"{moduli} moduli, {unit_count} units, {involution_count} affine signatures, "
          f"{failed_negative} failing negative-Jacobi chains")
