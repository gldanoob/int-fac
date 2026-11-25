"""Exact finite checks of marking a squarefree Euler product by its factor count."""

from fractions import Fraction as F
from itertools import combinations, product
from math import prod


def coefficients(weights):
    result = [F(1)]
    for weight in weights:
        result.append(F(0))
        for j in range(len(result)-1, 0, -1):
            result[j] += weight*result[j-1]
    return result


def main():
    primes = (11, 13, 17, 19, 23, 29, 31, 37)
    signed = radii = parseval = supported = positive = 0
    for signs in product((-1, 1), repeat=len(primes)):
        weights = [F(s, p) for s, p in zip(signs, primes)]
        coeffs = coefficients(weights)
        lists = range(len(primes))
        direct = [sum((prod(weights[i] for i in row) for row in combinations(lists, j)), F(0))
                  for j in range(len(primes)+1)]
        assert direct == coeffs
        signed += 1
        for radius in (F(2), F(5, 2), F(3)):
            max_ratio = radius*max(map(abs, weights))
            exponent = radius*abs(sum(weights)) + radius**2*sum(c*c for c in weights)/(2*(1-max_ratio))
            if exponent < 1:
                # exp(exponent) <= 1/(1-exponent) at these exact rational values.
                assert all(abs(c)*radius**j*(1-exponent) <= 1 for j, c in enumerate(coeffs))
                radii += 1
            # Exact cyclic average of P(r z)P(r/z) on every 16th root.
            marked = [c*radius**j for j, c in enumerate(coeffs)]
            average = sum(a*b for i, a in enumerate(marked) for j, b in enumerate(marked)
                          if (i-j) % 16 == 0)
            assert average == sum(a*a for a in marked)
            parseval += 1
    bound = max(primes)
    for j in range(len(primes)+1):
        for row in combinations(primes, j):
            n = prod(row)
            assert n <= bound**j
            for h in range(1, 4):
                if n > bound**h:
                    assert j > h
                    supported += 1
    for scale in range(2, 15):
        weights = [F(scale, p % 5 + 1) for p in primes]
        coeffs = coefficients(weights)
        mean = sum(w/(1+w) for w in weights)
        full = sum(coeffs)
        assert mean == sum(j*c for j, c in enumerate(coeffs))/full
        half_moment = prod((1+w/2)/(1+w) for w in weights)
        assert half_moment == sum(c/F(2)**j for j, c in enumerate(coeffs))/full
        for j in range(1, len(primes)+1):
            assert sum(coeffs[:j])/full <= 2**j*half_moment
            positive += 1
    print("marked coefficient arrays, rational Cauchy bounds, cyclic Parseval checks",
          signed, radii, parseval)
    print("degree support and positive lower-tail checks", supported, positive)


if __name__ == "__main__":
    main()
