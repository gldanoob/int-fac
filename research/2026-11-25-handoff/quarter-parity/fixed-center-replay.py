from cmath import exp
from itertools import combinations
from math import gcd, log, pi, sin, sqrt, tau


def wave(x, modulus):
    distance = min(x % modulus, -x % modulus)
    return 1 if 4 * distance < modulus else -1


def quarter(modulus):
    return sum((x * x - 1) % modulus == 0 for x in range(1, modulus // 4 + 1))


def coefficient(values, frequency):
    return sum(value * exp(-1j * tau * frequency * i / len(values))
               for i, value in enumerate(values)) / len(values)


checks = 0
small_aux_checks = 0
for (p, d), (q, e) in combinations(((3, 3), (3, 9), (5, 5), (5, 25),
                                    (7, 7), (11, 11), (13, 13)), 2):
    if p == q:
        continue
    n = d * e
    r = next(x for x in range(2, n // 2 + 1) if (x * x - 1) % n == 0)
    signs = []
    modulated = []
    for a in range(n):
        sign = wave(a * (r - 1), n) * wave(a * (r + 1), n)
        sign *= gcd(a, n) == 1
        signs.append(sign)
        chi = 0 if a % p == 0 else 2 * (pow(a, (p - 1) // 2, p) == 1) - 1
        modulated.append(sign * chi)
    hidden = coefficient(signs, 2 * r)
    local_product = (coefficient([wave(x, d) * (x % p != 0) for x in range(d)], 1)
                     * coefficient([wave(x, e) * (x % q != 0) for x in range(e)], 1))
    assert abs(hidden - local_product) < 1e-11
    assert hidden.real >= (2 / pi - 1 / p) * (2 / pi - 1 / q) - 1e-11
    assert abs(coefficient(modulated, 2 * r)) <= (3 + 2 * log(p)) / sqrt(p)
    for ell in (3, 5, 7, 11, 13, 17, 19, 25, 27, 49, 81):
        if gcd(ell, n) != 1:
            continue
        a = pow(ell, -1, n)
        full_modulus = n * ell
        centered = quarter(full_modulus)
        literal = 0
        if full_modulus < 50_000:
            numerator = full_modulus
            denominator = full_modulus * full_modulus + 1
            middle = full_modulus
            radius = full_modulus // 4
            for t in range(middle - radius, middle + radius + 1):
                literal += numerator * t * t // denominator
            literal -= numerator * middle * middle // denominator
            assert (literal - centered) % 2 == 0
        assert sum(wave(1 + ell * (a * (x - 1) % n), full_modulus) == 1
                   for x in (1, -1, r, -r)) == centered
        corrected = (-1) ** ((centered - 1 - (wave(2 * a, n) == 1)) % 2)
        assert corrected == signs[a]
        checks += 1
        if ell == 3:
            small_aux_checks += 1

for d in range(3, 90, 2):
    measured = coefficient([wave(x, d) for x in range(d)], 1)
    assert abs(measured - 1 / (d * sin(pi / (2 * d)))) < 1e-13
# The one-block modulus n=5 attains the exceptional boundary crossing for ell=3.
assert wave(pow(3, -1, 5) * (4 - 1), 5) == 1
assert wave(4, 15) == -1
print(f"{checks} certified prime-power lifts, including {small_aux_checks} with ell=3")
print("Verified the n=5, ell=3 quarter-boundary crossing")
print("Literal floor parities, CRT Fourier coefficients and quadratic modulation passed")
