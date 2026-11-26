"""Remove impossible square dependencies with exact local Legendre rows."""

from math import gcd, prod
from pathlib import Path
from runpy import run_path

HERE = Path(__file__).resolve().parent
GRID = run_path(str(HERE / "cogentic-monic-large-primes.py"))
PRIME_CUTOFF = 257


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


def prefilter(fields, points, signed_parity_basis, discriminant, *, prime_cutoff=PRIME_CUTOFF):
    """Return surviving support masks and counts of their exact probe constraints.

    The monic irreducible fields have degree at least two and use ascending
    coefficients. The nonzero discriminant is a multiple of every defining
    discriminant. The bit just above the last mark represents shared -1.
    """
    fields, points = tuple(fields), tuple(points)
    basis = list(signed_parity_basis)
    if not discriminant or any(len(f) < 3 or f[-1] != 1 for f in fields):
        raise ValueError("need monic fields of degree at least two and a nonzero discriminant product")
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

    columns = [0] * len(basis)
    probes = rational_primes = nonunit_probes = 0
    for prime in GRID["primes_through"](prime_cutoff):
        if prime == 2 or discriminant % prime == 0:
            continue
        before = probes
        squares = {r * r % prime for r in range(1, prime)}
        for coefficients, degree, derivative, norms in field_data:
            for root in range(prime):
                if GRID["polynomial"](coefficients, root, prime):
                    continue
                derivative_at_root = GRID["polynomial"](derivative, root, prime)
                row, nonunit = leading_unit_row(
                    degree, points, norms, prime, root, derivative_at_root, squares)
                bit = 1 << probes
                for index, word in enumerate(basis):
                    if (row & word).bit_count() % 2:
                        columns[index] |= bit
                probes += 1
                nonunit_probes += nonunit
        rational_primes += probes > before
    surviving = GRID["eliminate"](columns, basis)
    return surviving, dict(probes=probes, rational_primes=rational_primes,
                           nonunit_probes=nonunit_probes, rank=len(basis) - len(surviving))


def fixtures():
    points = [(3, 1), (3, -1), (7, 0), (10, 1), (1, 5)]
    row, nonunit = leading_unit_row(2, points, [7, 7, 49, 98, -49], 7, 3, 6, {1, 2, 4})
    assert nonunit and row == 0b111011
    # The two conjugate factors multiply to 7, so their product with 7 is square.
    assert (row & 0b0111).bit_count() % 2 == 0

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
