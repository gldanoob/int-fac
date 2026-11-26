"""Check the disjoint rectangular partition of signed words of bounded support."""

from collections import Counter
from itertools import combinations, product
from math import comb


def signed_supports(dimension, size):
    for indices in combinations(range(dimension), size):
        for signs in product((-1, 1), repeat=size):
            yield tuple(zip(indices, signs, strict=True))


def route(dimension, size, left):
    """Group by the ancestors where the extremal index enters the required child."""
    leaf_start = 1 << (dimension - 1).bit_length()
    groups = [[] for _ in range(leaf_start)]
    for word in signed_supports(dimension, size):
        node = leaf_start + (word[-1][0] if left else word[0][0])
        while node > 1:
            if node % 2 == (0 if left else 1):
                groups[node // 2].append(word)
            node //= 2
    return groups


def rectangles(dimension, bound):
    if not 0 <= bound <= dimension:
        raise ValueError("require a support bound between zero and the dimension")
    yield [()], [()]
    if bound:
        yield list(signed_supports(dimension, 1)), [()]
    for size in range(2, bound + 1):
        before = size // 2
        prefixes = route(dimension, before, True)
        suffixes = route(dimension, size - before, False)
        for left, right in zip(prefixes, suffixes, strict=True):
            if left and right:
                yield left, right


def replay():
    cases = 0
    words = 0
    for dimension in range(9):
        for bound in range(dimension + 1):
            expected = {word for size in range(bound + 1)
                        for word in signed_supports(dimension, size)}
            actual = Counter()
            for left, right in rectangles(dimension, bound):
                actual.update(u + v for u in left for v in right)
            count = sum(2**s * comb(dimension, s) for s in range(bound + 1))
            assert len(actual) == count and actual.keys() == expected
            assert all(multiplicity == 1 for multiplicity in actual.values())
            cases += 1
            words += count
    print(f"Verified {words} exact signed-support words across {cases} tree partitions.")


if __name__ == "__main__":
    replay()
