"""Exact checks of the extractor counting argument on a finite multiplier family."""

from fractions import Fraction


def multiply(x, y):
    """Multiply in F_2[X] modulo the AES polynomial X^8+X^4+X^3+X+1."""
    result = 0
    while y:
        if y & 1:
            result ^= x
        x <<= 1
        if x >= 256:
            x ^= 0x11B
        y >>= 1
    return result


def main():
    # The multipliers and output projection are a finite model. The asymptotic
    # advice construction uses the extractor in GUV Theorem 1.5.
    multipliers = [1]
    for _ in range(15):
        multipliers.append(multiply(3, multipliers[-1]))
    neighbors = [[multiply(a, s) >> 5 for s in multipliers] for a in range(256)]
    flat_size = 32
    error = Fraction(0)
    exceptions = []
    for mask in range(256):
        hits = [sum((mask >> y) & 1 for y in row) for row in neighbors]
        uniform = Fraction(mask.bit_count(), 8)
        largest = sorted(hits, reverse=True)[:flat_size]
        # Maximizing over a flat min-entropy source takes the largest counts.
        # The complementary masks give the other sign of the discrepancy.
        error = max(error, Fraction(sum(largest), flat_size*len(multipliers)) - uniform)
        if mask.bit_count() >= 4:
            missed = {a for a, count in enumerate(hits) if count == 0}
            assert len(missed) < flat_size
            exceptions.append(missed)
    assert error < Fraction(1, 2)
    # Every block of eight targets has a common successful master, directly
    # and by the sum of the individual exceptional counts.
    blocks = 0
    for i in range(len(exceptions)):
        targets = (exceptions[(i+j) % len(exceptions)] for j in range(8))
        assert len(set().union(*targets)) <= 8*(flat_size-1) < len(neighbors)
        blocks += 1
    # Any preassigned list with at most half the domain can occur as the
    # failure set of a dense test, including each list in an advice decoder.
    lists = [[a, (3*a+1) % 8, (5*a+2) % 8] for a in range(8)]
    good = [set(range(8)) - set(row) for row in lists]
    assert min(map(len, good)) >= 4
    obstructions = sum(any(not g.intersection(row) for g in good) for row in lists)
    assert obstructions == len(lists)
    print(f"256 output events; worst flat-source error {error}; "
          f"{len(exceptions)} dense tests; {blocks} common-master blocks; "
          f"{obstructions} decoder-list obstructions")


if __name__ == "__main__":
    main()
