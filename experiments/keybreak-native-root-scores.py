"""Replay truncated primitive projective valuations for good and ramified forms."""

from fractions import Fraction
from itertools import product


def check_form(p, depth, coeff):
    degree = len(coeff) - 1
    modulus = p**depth

    def value(a, b):
        return sum(c * a**i * b**(degree-i) for i, c in enumerate(coeff))

    def truncated(a, b):
        n = value(a, b)
        for k in range(depth):
            if n % p:
                return k
            n //= p
        return depth

    vals = [truncated(a, 1) for a in range(modulus)]
    vals.extend(truncated(1, b) for b in range(0, modulus, p))
    avg = Fraction(sum(vals), len(vals))
    cap = Fraction(p, p*p-1)
    assert avg <= degree * cap * (1 - Fraction(1, p**depth))

    root_multiplicities = []
    for a, infinity in [(a, False) for a in range(p)] + [(0, True)]:
        terms = list(reversed(coeff)) if infinity else list(coeff)
        m = 0
        while len(terms) > 1:
            quotient = [0] * (len(terms)-1)
            carry = terms[-1]
            for i in reversed(range(len(quotient))):
                quotient[i] = carry
                carry = (a*carry + terms[i]) % p
            if carry:
                break
            m += 1
            terms = quotient
        if m:
            root_multiplicities.append(m)
    if all(m == 1 for m in root_multiplicities):
        assert avg == len(root_multiplicities) * cap * (1 - Fraction(1, p**depth))

    scale = 1 + Fraction(1, p + degree)
    assert scale**degree < p
    mgf = sum(scale**v for v in vals) / len(vals)
    bound = 1 + sum((scale**m - 1) / ((p+1)*(1-scale**m/p)) for m in root_multiplicities)
    assert mgf <= bound


if __name__ == "__main__":
    count = 0
    for p, degree, depth in ((2, 3, 5), (3, 3, 4), (5, 2, 3)):
        for coeff in product(range(p), repeat=degree+1):
            if any(coeff):
                check_form(p, depth, coeff)
                count += 1
    print(f"Verified projective valuation and exponential-moment bounds on {count} finite forms.")
