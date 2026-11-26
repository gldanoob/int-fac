#!/usr/bin/env python3
"""Exact finite replay for the parity-fiber arithmetic test obstruction."""

from itertools import product
from math import gcd


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


def parity_modulus_bias_numerator(k, q, r):
    """Return |P(X=r mod q | even)-P(X=r mod q)| as an exact Fraction pair."""
    # The conditional support has exactly 2**(k-1) members for k >= 1.
    even_count = sum(x % 2 == 0 for x in range(1 << k))
    assert even_count == 1 << (k - 1)
    accepted = sum(x.bit_count() % 2 == 0 and x % q == r % q
                   for x in range(1 << k))
    all_count = 1 << k
    unconditioned = sum(x % q == r % q for x in range(all_count))
    # Difference numerator over even_count*all_count.
    return abs(accepted * all_count - unconditioned * even_count), even_count * all_count


def verify_affine_reduction(k, predicates):
    """Check empty/single-progression reduction, including nonunits and offsets."""
    modulus = 1
    residue = 0
    for coeff, offset, target, q in predicates:
        g = gcd(coeff, q)
        if (target - offset) % g:
            return []
        reduced_q = q // g
        if reduced_q == 1:
            continue
        # Solve coeff/g * x = (target-offset)/g mod q/g by a finite exact scan.
        row_residue = next(x for x in range(reduced_q)
                           if (coeff * x + offset - target) % q == 0)
        new_modulus = modulus * reduced_q // gcd(modulus, reduced_q)
        compatible = [x for x in range(new_modulus)
                      if x % modulus == residue and x % reduced_q == row_residue]
        if not compatible:
            return []
        residue, modulus = compatible[0], new_modulus
    # Generate the single combined progression and compare it with direct evaluation.
    return list(range(residue, 1 << k, modulus))


for k in range(1, 11):
    for q in (1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 15):
        for r in range(q):
            numerator, denominator = parity_modulus_bias_numerator(k, q, r)
            # Compare numerator/denominator <= (4/(3 sqrt(3)))^floor(k/2)
            # after raising to an even power; all arithmetic is integral.
            m = k // 2
            assert (numerator * numerator * 27**m <=
                    denominator * denominator * 16**m)

# Affine systems include noninvertible coefficients, inconsistent rows, and offsets.
systems = [
    [(2, 3, 2, 8)],              # noninvertible coefficient: empty
    [(2, 3, 5, 8)],              # noninvertible coefficient, one class mod 4
    [(3, 7, 1, 10), (2, 5, 1, 6)],
    [(1, 0, 0, 4), (1, 1, 0, 4)],  # genuinely incompatible classes
]
for system in systems:
    direct = [x for x in range(1 << 8)
              if all((a * x + b - c) % q == 0 for a, b, c, q in system)]
    assert verify_affine_reduction(8, system) == direct

# A fixed coefficient-word offset enters c+d(b+x) as d*b, not b.
offset = 5
coeff = 3
constant = 7
target = 2
q = 11
assert [x for x in range(32) if (constant + coeff * (offset + x) - target) % q == 0] == [x for x in range(32) if (coeff * x - (target - constant - coeff * offset)) % q == 0]

# For k=3, residue 0 mod 3 has an endpoint discrepancy: the unconditioned
# probability is 3/8, not 1/3. Verify both exact probabilities directly.
k, q, r = 3, 3, 0
even_count = sum(x.bit_count() % 2 == 0 for x in range(1 << k))
even_residue_count = sum(x.bit_count() % 2 == 0 and x % q == r for x in range(1 << k))
all_residue_count = sum(x % q == r for x in range(1 << k))
assert (even_residue_count, even_count, all_residue_count) == (3, 4, 3)
assert (even_residue_count / even_count) != (all_residue_count / (1 << k))

print("exact conditional-vs-unconditioned bias inequalities passed for k=1..10 and 11 moduli")
print("affine reduction cases passed, including nonunits and offsets")
print("endpoint-discrepancy example passed: 3/4 conditioned versus 3/8 unconditioned")
