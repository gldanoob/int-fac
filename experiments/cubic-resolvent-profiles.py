"""Exact minima for the quadratic resolvents of monic cubics of height five."""

from itertools import product


def squareclass(n):
    primes = {-1} if n < 0 else set()
    n = abs(n)
    p = 2
    while p * p <= n:
        while n % p == 0:
            primes ^= {p}
            n //= p
        p += 1
    if n > 1:
        primes.add(n)
    return frozenset(primes)


def box_classes(height):
    classes = set()
    for a, b, c in product(range(-height, height + 1), repeat=3):
        if c == 0:
            continue
        roots = (j for j in range(-abs(c), abs(c) + 1) if j and c % j == 0)
        if any(((j + a) * j + b) * j + c == 0 for j in roots):
            continue
        discriminant = a*a*b*b - 4*b**3 - 4*a**3*c - 27*c*c + 18*a*b*c
        classes.add(squareclass(discriminant))
    classes.discard(frozenset())
    return sorted(classes, key=lambda s: tuple(sorted(s)))


def basis(rows):
    """Canonical reduced binary row basis."""
    pivots = {}
    for row in rows:
        for j in sorted(pivots, reverse=True):
            if row & (1 << j):
                row ^= pivots[j]
        if row:
            j = row.bit_length() - 1
            for i, old in pivots.items():
                if old & (1 << j):
                    pivots[i] = old ^ row
            pivots[j] = row
    return tuple(pivots[j] for j in sorted(pivots))


def bitmask(indices):
    return sum(1 << j for j in indices)


def eliminate(terms, variables, merge):
    """Eliminate signs in minimum-neighborhood order, keeping boundary tables."""
    terms, remaining = list(terms), set(variables)
    archive = []
    while remaining:
        def neighbors(v):
            return set().union(*(s for s, _ in terms if v in s)) - {v}

        v = min(remaining, key=lambda u: (len(neighbors(u)), -u))
        scope = tuple(sorted(neighbors(v)))
        bucket = [(s, t) for s, t in terms if v in s]
        table, choices = {}, {}
        for bits in product((0, 1), repeat=len(scope)):
            assignment = dict(zip(scope, bits))
            inputs = []
            for sign in (0, 1):
                assignment[v] = sign
                inputs.append([t[tuple(assignment[u] for u in s)] for s, t in bucket])
            table[bits], choices[bits] = merge(v, inputs)
        archive.append((v, scope, choices))
        terms = [(s, t) for s, t in terms if v not in s] + [(scope, table)]
        remaining.remove(v)
    assert all(not s for s, _ in terms)
    return [t[()] for _, t in terms], archive


def merge_counts(v, inputs):
    costs = list(map(sum, inputs))
    best = min(costs)
    return best, tuple(i for i, cost in enumerate(costs) if cost == best)


def optimal_profiles(archive, assignment):
    if not archive:
        yield assignment
        return
    v, scope, choices = archive[-1]
    for sign in choices[tuple(assignment[u] for u in scope)]:
        assignment[v] = sign
        yield from optimal_profiles(archive[:-1], assignment)


def keep_minimum(table, span, state):
    if span not in table or state < table[span]:
        table[span] = state


def merge_ranks(v, inputs):
    """A state stores the charged internal rank and an attaining sign mask."""
    output = {}
    for sign, bucket in enumerate(inputs):
        states = {(): (0, sign << v)}
        for table in bucket:
            combined = {}
            for left, (a, m) in states.items():
                for right, (b, n) in table.items():
                    keep_minimum(combined, basis(left + right), (a + b, m | n))
            states = combined
        for span, (cost, witness) in states.items():
            pivot = next((x for x in span if x & (1 << v)), 0)
            tail = (x ^ pivot if x & (1 << v) else x for x in span if x != pivot)
            keep_minimum(output, basis(tail), (cost + bool(pivot), witness))
    return output, None


def check(height):
    classes = box_classes(height)
    primes = sorted(set().union(*classes))
    full = {p: i for i, p in enumerate(primes)}
    quotient = {p: i for i, p in enumerate(p for p in primes if p != 3)}
    anchor = frozenset({-1, 3})
    assert anchor in classes

    def rows(branch):
        for s in classes:
            projected = s ^ anchor if 3 in s else s
            scope = tuple(sorted(quotient[p] for p in projected))
            yield bitmask(full[p] for p in s), scope, branch * int(3 in s)

    for branch in (1, 0):
        original = list(rows(branch))
        counts, ranks = [], []
        for _, scope, shift in original:
            row = (bitmask(scope),) if scope else ()
            count_table, rank_table = {}, {}
            for bits in product((0, 1), repeat=len(scope)):
                active = (sum(bits) + shift) % 2 == 0
                count_table[bits] = int(active)
                rank_table[bits] = {row if active else (): (0, 0)}
            counts.append((scope, count_table))
            ranks.append((scope, rank_table))

        def active_rows(mask):
            return tuple(row for row, scope, shift in original
                         if ((mask & bitmask(scope)).bit_count() + shift) % 2 == 0)

        costs, archive = eliminate(counts, quotient.values(), merge_counts)
        minimum = sum(costs)
        states, _ = eliminate(ranks, quotient.values(), merge_ranks)
        assert all(set(state) == {()} for state in states)
        rank, mask = 1 - branch, 0
        for state in states:
            cost, witness = state[()]
            rank += cost
            mask |= witness
        assert len(basis(active_rows(mask))) == rank
        print(f'H={height} p mod 3={1+branch} classes={len(classes)} '
              f'minimum split count={minimum}, minimum rank={rank}')

        if height == 2:
            all_active = [active_rows(mask) for mask in range(1 << len(quotient))]
            assert minimum == min(map(len, all_active))
            assert rank == min(len(basis(rows)) for rows in all_active)
        if height == 5:
            assert len(classes) == 196 and rank == (28 if branch else 13)
            if branch:
                profiles, distinct = 0, set()
                for signs in optimal_profiles(archive, {}):
                    active = active_rows(bitmask(j for j, sign in signs.items() if sign))
                    assert len(active) == len(basis(active)) == minimum
                    distinct.add(active)
                    profiles += 1
                assert (minimum, profiles, len(distinct)) == (31, 8192, 8192)
                print(f'{profiles} minimum-count profiles, all of rank {minimum}')


if __name__ == '__main__':
    check(2)
    check(5)
