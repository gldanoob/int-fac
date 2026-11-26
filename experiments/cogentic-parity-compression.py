#!/usr/bin/env python3
"""Exact finite replay for the parity-fiber arithmetic test obstruction."""

from itertools import product


def test(bits):
    # n = 1 + x1 + x2; accepted values are squarefree products from J={2}.
    n = 1 + sum(bits)
    return n in (1, 2)


words = list(product((0, 1), repeat=2))
even = [word for word in words if sum(word) % 2 == 0]
answers_by_parity = {}
for word in words:
    answers_by_parity.setdefault(sum(word) % 2, set()).add(test(word))

uniform_mean = sum(test(word) for word in words) / len(words)
even_mean = sum(test(word) for word in even) / len(even)

assert answers_by_parity[0] == {False, True}
assert uniform_mean == 3 / 4
assert even_mean == 1 / 2
assert abs(uniform_mean - even_mean) == 1 / 4

for word in words:
    print(f"{''.join(map(str, word))}: parity={'odd' if sum(word) % 2 else 'even'}, "
          f"n={1 + sum(word)}, accepted={test(word)}")
print(f"uniform mean={uniform_mean}; even-support mean={even_mean}; gap={abs(uniform_mean-even_mean)}")
