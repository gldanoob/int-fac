"""Finite checks of squarefree Euler products, progression weights, and a curved Mellin contour."""

from cmath import exp
from math import ceil, exp as real_exp, gcd, log, pi, sqrt


def squarefree_products(primes):
    products = [1]
    for prime in primes:
        products.extend([prime * n for n in products])
    return products


def odd_prime_power_characters(q):
    units = {a for a in range(1, q) if gcd(a, q) == 1}
    for generator in sorted(units):
        powers = [pow(generator, k, q) for k in range(len(units))]
        if set(powers) == units:
            index = {a: k for k, a in enumerate(powers)}
            return [
                {a: exp(2j * pi * k * ell / len(units)) for a, ell in index.items()}
                for k in range(len(units))
            ]
    raise ValueError("The replay uses cyclic unit groups")


def log_gaussian(n, y, width_ratio):
    return width_ratio * real_exp(-0.5 * (width_ratio * log(n / y)) ** 2) / (sqrt(2 * pi) * n)


def check_orthogonality():
    fibers = products_checked = 0
    for q in (7, 9, 11, 13, 25, 27, 29):
        characters = odd_prime_power_characters(q)
        for primes in ([7, 11, 13, 17, 19, 23], [7, 13, 17, 19], [11, 17, 23, 29, 31]):
            products = squarefree_products(primes)
            s = 0.73 + 1.4j
            transforms = []
            for chi in characters:
                euler = 1
                for p in primes:
                    euler *= 1 + chi.get(p % q, 0) * p ** (-s)
                direct = sum(chi.get(n % q, 0) * n ** (-s) for n in products)
                assert abs(euler - direct) < 2e-12
                transforms.append(sum(chi.get(n % q, 0) * log_gaussian(n, 300, 2) for n in products))
                products_checked += 1
            for residue in characters[0]:
                direct = sum(log_gaussian(n, 300, 2) for n in products if n % q == residue)
                inverted = sum(chi[residue].conjugate() * z for chi, z in zip(characters, transforms)) / len(characters)
                assert abs(direct - inverted) < 1e-12
                fibers += 1
    return products_checked, fibers


def integrate_segment(f, lo, hi):
    if hi == lo:
        return 0
    pieces = 2 * ceil((hi - lo) / 0.002 / 2)
    step = (hi - lo) / pieces
    return step / 3 * (
        f(lo) + f(hi) + sum((4 if k % 2 else 2) * f(lo + k * step) for k in range(1, pieces))
    )


def check_contours():
    comparisons = 0
    for primes in ([7, 11, 13, 17, 19], [7, 11, 19, 23, 29]):
        b = max(primes)
        products = squarefree_products(primes)
        for y, width_ratio in ((100, 1.5), (250, 2.0), (900, 2.7)):
            alpha, sigma_min = 0.84, 0.55
            t_max = 14 * width_ratio
            corner = b ** (alpha - sigma_min)
            direct = sum(log_gaussian(n, y, width_ratio) for n in products)

            def integrand(t, sigma, sigma_prime):
                s = sigma + 1j * t
                kernel = y ** (s - 1) * exp((s - 1) ** 2 / (2 * width_ratio ** 2))
                for p in primes:
                    kernel *= 1 + p ** (-s)
                return (kernel * (1 - 1j * sigma_prime)).real / pi

            vertical = integrate_segment(lambda t: integrand(t, alpha, 0), 0, t_max)
            curved = integrate_segment(lambda t: integrand(t, alpha, 0), 0, 1)
            curved += integrate_segment(
                lambda t: integrand(t, alpha - log(t) / log(b), -1 / (t * log(b))), 1, corner
            )
            curved += integrate_segment(lambda t: integrand(t, sigma_min, 0), corner, t_max)
            assert abs(vertical - direct) < 2e-11
            assert abs(curved - direct) < 2e-11
            comparisons += 2
    return comparisons


if __name__ == "__main__":
    print("Euler products, progression masses, contour integrals:", *check_orthogonality(), check_contours())
