"""Compute minimum cubic resolvent ranks, or verify the supplied sign profiles."""

import argparse
from functools import lru_cache, partial
from itertools import product
from pathlib import Path
from runpy import run_path

HERE = Path(__file__).resolve().parent
profiles = run_path(str(HERE / 'cubic-resolvent-profiles.py'))
basis = lru_cache(maxsize=16384)(profiles['basis'])
bitmask = profiles['bitmask']


def prune(states):
    if len(states) < 2:
        return states
    kept = {}
    for span, state in sorted(states.items(), key=lambda pair: (pair[1][0], len(pair[0]))):
        # rank(U+W)-rank(V+W) is at most rank(U+V)-rank(V), for any future W.
        if not any(cost + len(basis(other + span)) - len(span) <= state[0]
                   for other, (cost, _) in kept.items()):
            kept[span] = state
    return kept


def solve(height, residue, cut, supplied=None):
    classes = profiles['box_classes'](height)
    primes = sorted(set().union(*classes, {-1, 3}))
    positions = {p: i for i, p in enumerate(primes)}
    raw = tuple(bitmask(positions[p] for p in s) for s in classes)
    anchor = bitmask((positions[-1], positions[3]))
    branch = residue - 1

    def active_rank(signs):
        return len(basis(tuple(r for r in raw if (r & signs).bit_count() % 2 == 0)))

    if supplied is not None:
        rank, signs = supplied
    elif anchor not in raw:
        # At height one the anchor is absent and there are five sign coordinates.
        rank, signs = min((active_rank(m), m) for m in range(1 << len(primes))
                          if (m & anchor).bit_count() % 2 == branch)
    else:
        variables = [positions[p] for p in primes if p != 3]
        if not 0 <= cut <= len(variables):
            raise ValueError(f'cut must be between 0 and {len(variables)}')
        fixed, free = variables[:cut], variables[cut:]
        rows = []
        for r in raw:
            shifted = bool(r & (1 << positions[3]))
            projected = r ^ anchor if shifted else r
            if projected:
                scope = tuple(i for i in free if projected & (1 << i))
                rows.append((projected, scope, branch * shifted))
        best = (len(primes) + 1, 0)
        for values in product((0, 1), repeat=cut):
            known = bitmask(i for i, value in zip(fixed, values) if value)
            terms = []
            for row, scope, shift in rows:
                parity = (row & known).bit_count() + shift
                table = {bits: {(row,) if (sum(bits) + parity) % 2 == 0 else (): (0, 0)}
                         for bits in product((0, 1), repeat=len(scope))}
                terms.append((scope, table))
            end, _ = profiles['eliminate'](terms, free, partial(profiles['merge_ranks'], prune=prune))
            # Fixed signs still contribute row coordinates, so join all terminal spans.
            for span, (cost, witness) in profiles['join_ranks'](end, known, prune).items():
                if (witness & anchor).bit_count() % 2 != branch:
                    witness |= 1 << positions[3]
                best = min(best, (cost + len(span) + 1 - branch, witness))
        rank, signs = best

    assert 0 <= signs < (1 << len(primes)) and (signs & anchor).bit_count() % 2 == branch
    assert active_rank(signs) == rank
    return rank, signs


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('heights', type=int, nargs='+')
    parser.add_argument('--cut', type=int, default=0, help='number of sign coordinates to fix per subproblem')
    parser.add_argument('--verify-only', action='store_true', help='check attaining signs without minimizing')
    args = parser.parse_args()
    certificate = {}
    for line in (HERE / 'cubic-rank-frontier.txt').read_text().splitlines():
        h, residue, rank, mask = line.split()
        certificate[int(h), int(residue)] = int(rank), int(mask, 16)
    for height in args.heights:
        if height < 1:
            parser.error('box heights must be positive')
        for residue in (2, 1):
            expected = certificate.get((height, residue))
            if args.verify_only and expected is None:
                parser.error(f'no saved witness for height {height}')
            rank, signs = solve(height, residue, args.cut, expected if args.verify_only else None)
            if expected and rank != expected[0]:
                raise ValueError(f'rank mismatch at height {height}, residue {residue}')
            print(height, residue, rank, f'{signs:x}', flush=True)
