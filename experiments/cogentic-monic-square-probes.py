"""Remove impossible square dependencies with exact local Legendre rows."""

from math import gcd, prod
from pathlib import Path
from runpy import run_path
from subprocess import TimeoutExpired
from time import monotonic

HERE = Path(__file__).resolve().parent
GRID = run_path(str(HERE / "cogentic-monic-large-primes.py"))
PRIME_CUTOFF = 257


def parity_probe_cutoff(fields):
    """Uniform Dedekind-GRH cutoff for masks of even ideal parity."""
    size = 10
    for coefficients in fields:
        degree = len(coefficients) - 1
        height_bits = max(2, *(abs(c) for c in coefficients)).bit_length()
        size += (degree + (degree - 1) * (height_bits + (degree + 1).bit_length())
                 + degree * (height_bits + (degree**2).bit_length()))
    log_bits = (2 * size - 1).bit_length()
    return (10**6 * size * log_bits**2)**2


def growing_primes(limit):
    lower, upper = 1, min(32, limit)
    while lower < upper:
        yield from (prime for prime in GRID["primes_through"](upper) if prime > lower)
        lower, upper = upper, min(2 * upper, limit)


def leading_unit_row(degree, points, norms, prime, root, derivative, squares):
    row = (prime % 4 == 3) << len(points)
    inverse = pow(derivative, -1, prime)
    nonunit = False
    for index, ((a, b), norm) in enumerate(zip(points, norms, strict=True)):
        residue = (a - b * root) % prime
        if not residue:
            nonunit = True
            while a % prime == b % prime == 0:
                a //= prime
                b //= prime
            residue = (a - b * root) % prime
            if not residue:
                while norm % prime == 0:
                    norm //= prime
                residue = norm * pow(b, 1 - degree, prime) * inverse % prime
        if residue not in squares:
            row |= 1 << index
    return row, nonunit


def prefilter(fields, points, signed_parity_basis, discriminant=None, *,
              prime_cutoff=PRIME_CUTOFF, survivor_limit=0, deadline=None):
    """Return surviving support masks and counts of their exact probe constraints.

    The monic irreducible fields have degree at least two and use ascending
    coefficients. An optional nonzero discriminant multiple excludes its
    prime factors. The bit just above the last mark represents shared -1.
    """
    fields, points = tuple(fields), tuple(points)
    basis = list(signed_parity_basis)
    if discriminant == 0 or not fields or any(len(f) < 3 or f[-1] != 1 for f in fields):
        raise ValueError("need monic fields of degree at least two and a nonzero optional discriminant")
    if prime_cutoff < 0 or survivor_limit < 0:
        raise ValueError("prime cutoff and survivor limit must be nonnegative")
    if any(a == b == 0 for a, b in points):
        raise ValueError("marked elements must be nonzero")
    if any(word < 0 or word.bit_length() > len(points) + 1 for word in basis):
        raise ValueError("support masks may contain only the marks and shared sign bit")

    field_data = []
    for coefficients in fields:
        degree = len(coefficients) - 1
        derivative = tuple(j * value for j, value in enumerate(coefficients) if j)
        norms = [sum(c * a**j * b**(degree - j) for j, c in enumerate(coefficients))
                 for a, b in points]
        if not all(norms):
            raise ValueError("marked elements must have nonzero norm")
        field_data.append((coefficients, degree, derivative, norms))

    initial_dimension = len(basis)
    probes = rational_primes = nonunit_probes = 0
    last_prime = 0
    for prime in growing_primes(prime_cutoff):
        if len(basis) <= survivor_limit:
            break
        if deadline is not None and monotonic() >= deadline:
            raise TimeoutExpired("local square probes", 0)
        if prime == 2 or (discriminant is not None and discriminant % prime == 0):
            continue
        last_prime = prime
        before = probes
        squares = {r * r % prime for r in range(1, prime)}
        for coefficients, degree, derivative, norms in field_data:
            for root in range(prime):
                if GRID["polynomial"](coefficients, root, prime):
                    continue
                derivative_at_root = GRID["polynomial"](derivative, root, prime)
                if not derivative_at_root:
                    continue
                row, nonunit = leading_unit_row(
                    degree, points, norms, prime, root, derivative_at_root, squares)
                pivot = 0
                restricted = []
                for word in basis:
                    if (row & word).bit_count() % 2:
                        if not pivot:
                            pivot = word
                            continue
                        word ^= pivot
                    restricted.append(word)
                if pivot:
                    basis = restricted
                probes += 1
                nonunit_probes += nonunit
                if len(basis) <= survivor_limit:
                    break
            if len(basis) <= survivor_limit:
                break
        rational_primes += probes > before
    return basis, dict(probes=probes, rational_primes=rational_primes,
                       nonunit_probes=nonunit_probes, rank=initial_dimension - len(basis),
                       last_prime=last_prime,
                       stopped="survivor-limit" if len(basis) <= survivor_limit else "prime-cutoff")


def fixtures():
    points = [(3, 1), (3, -1), (7, 0), (10, 1), (1, 5)]
    row, nonunit = leading_unit_row(2, points, [7, 7, 49, 98, -49], 7, 3, 6, {1, 2, 4})
    assert nonunit and row == 0b111011
    # The two conjugate factors multiply to 7, so their product with 7 is square.
    assert (row & 0b0111).bit_count() % 2 == 0
    field = ((2, 2, 0, 1),)
    points = ((2, 0), (4, 0))
    # Modulo five this Eisenstein cubic has a repeated root at 1 and a simple root at 3.
    surviving, stats = prefilter(field, points, [1, 2],
                                 prime_cutoff=parity_probe_cutoff(field), survivor_limit=1)
    assert surviving == [2] and stats["last_prime"] == 5
    assert stats["probes"] == 1 and stats["stopped"] == "survivor-limit"
    assert prefilter(field, points, [1, 2], -140, prime_cutoff=5)[0] == [1, 2]

    driver = run_path(str(HERE / "cogentic-monic-kernel-driver.py"))
    repair = driver["REPAIR"]
    plant = run_path(str(HERE / "cogentic-planted-norm-two.py"))["monic_plants"]
    cutoff = max(GRID["BASE"], 2 * GRID["HEIGHT"]**2)
    primes = tuple(GRID["primes_through"](cutoff))
    for n, degree, planted in ((27, 2, False), (323, 3, False),
                              (247, 3, False), (85, 4, True)):
        if planted:
            m, _, left, right = plant(n, degree)
            fields = left, right
        else:
            m, left, right = GRID["CHECK_PAIR"](n, degree)
            _, fields = repair(n, m, left, right)
        coefficients = [list(f) for f in fields]
        discriminant = int(driver["gp_value"](
            f"poldisc(Polrev({coefficients[0]}))*poldisc(Polrev({coefficients[1]}))", 5))
        marks = GRID["relations"](n, m, fields, discriminant, primes, cutoff,
                                  complete_parity=True, include_ramified_two=True)
        points = [point for point, _, _, _ in marks]
        columns = GRID["parity_words"]([small + large for _, small, large, _ in marks])
        parity = GRID["eliminate"](columns, (1 << j for j in range(len(marks))))
        signed = [1 << len(marks), *parity]
        _, base_stats = prefilter(fields, points, signed, discriminant, prime_cutoff=GRID["BASE"])
        surviving, stats = prefilter(fields, points, signed, discriminant)
        if n in (323, 247):
            early, early_stats = prefilter(fields, points, signed, discriminant,
                                           survivor_limit=len(surviving))
            assert early == surviving and early_stats["stopped"] == "survivor-limit"
            stats["handoff_prime"] = early_stats["last_prime"]
        _, decode, query = driver["exact_oracle"](n, m, fields, marks)
        status, tested, _, square_basis = driver["adaptive"](surviving, query)
        assert all(GRID["combine"](word & ((1 << len(marks)) - 1), columns) == 0
                   for word, _ in square_basis)
        factors = set()
        for word, (left, right) in square_basis:
            sign, support = decode(word)
            target = sign * prod(a - b*m for a, b in support) % n
            assert gcd(target, n) == 1 and left**2 % n == right**2 % n == target
            divisor = gcd(left - right, n)
            if 1 < divisor < n:
                factors.add(divisor)
        if n == 247:
            assert status == "complete" and factors in ({13}, {19})
        if n == 85:
            assert len(signed) == 2 and not surviving and not tested
        print(dict(n=n, planted=planted, marks=len(marks), signed=len(signed),
                   surviving=len(surviving), status=status, tests=tested,
                   squares=len(square_basis), factors=sorted(factors), base_rank=base_stats["rank"],
                   **stats),
              flush=True)


if __name__ == "__main__":
    fixtures()
