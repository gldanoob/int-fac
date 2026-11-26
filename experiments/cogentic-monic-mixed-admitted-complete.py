"""Complete or cap an unsigned mixed decision on already-admitted columns."""

import argparse
import json
from collections import Counter
from pathlib import Path
from runpy import run_path
from time import monotonic


HERE = Path(__file__).resolve().parent
MIXED = run_path(str(HERE / "cogentic-monic-mixed-grid.py"))
COMPLETE = MIXED["DRIVER"]["complete_basis"]
FIXTURE = 358395019
HEIGHT, PROBE_CAP, QUERY_CAP, TIME_CAP = 256, 257, 1024, 45


def decide(n, m, fields, derivatives, discriminants, collected, *, query_cap=None, time_cap=None):
    """Use the full unsigned kernel relative to supplied three-field mark rows."""
    if not len(fields) == len(derivatives) == len(discriminants) == len(collected) == 3:
        raise ValueError("expected three fields and their corresponding parity data")
    if query_cap is not None and query_cap < 0 or time_cap is not None and time_cap < 0:
        raise ValueError("the exact-test and time limits must be nonnegative")
    variables, ideal = MIXED["rank_core"](collected)
    blocks, field_masks, offset = [], [], 0
    for i in range(len(fields)):
        points = [point for index, point in variables if index == i]
        blocks.append((offset, points))
        field_masks.append(((1 << len(points))-1) << offset)
        offset += len(points)
    probed = MIXED["probe"](fields, discriminants, blocks, ideal, prime_cutoff=PROBE_CAP)
    pair_ideal = list(map(len, MIXED["pair_parts"](ideal, field_masks)))
    pair_probed = list(map(len, MIXED["pair_parts"](probed, field_masks)))
    before = len(probed)
    queries, certificate, rounds, last_bound = [], None, [], PROBE_CAP
    deadline = monotonic()+time_cap if time_cap is not None else None

    def restrict(basis, complete_cutoff):
        nonlocal last_bound
        bound = PROBE_CAP * complete_cutoff // 3
        if bound > last_bound:
            basis = MIXED["probe"](fields, discriminants, blocks, basis, prime_cutoff=bound,
                                    after=last_bound, deadline=deadline)
        last_bound = bound
        rounds.append(dict(bound=bound, dimension=len(basis)))
        return sorted(basis, key=int.bit_count), dict(last_prime=bound)

    def query(word):
        nonlocal certificate
        result = MIXED["roots"](n, m, fields, derivatives, blocks, word, deadline)
        if result is None:
            queries.append(None)
            return None
        summary, found = result
        queries.append(summary)
        if found:
            certificate = found
        return summary["ratio"], 1

    status, tests, basis, survivors, _ = COMPLETE(
        probed, restrict, query, query_cap, n, deadline)
    if status == "complete":
        assert len(basis) == len(survivors) and certificate is None
        status = "complete-no-split"
    histogram = Counter(str(result["ratio"]) if result else "nonsquare" for result in queries)
    return dict(n=n, m=m, status=status, columns=list(map(len, collected)),
                core=[len(points) for _, points in blocks], ideal=len(ideal), probed=before,
                pair_ideal=pair_ideal, pair_probed=pair_probed, rounds=rounds,
                tests=tests, exact_basis=len(basis), survivors=len(survivors),
                histogram=dict(histogram), prefix=queries[:4], certificate=certificate)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate-file", type=Path)
    args = parser.parse_args()
    start = monotonic()
    n = FIXTURE
    m, fields, derivatives, discriminants = MIXED["field_library"](n)
    columns = [MIXED["COLLECT"](n, m, (field,), disc, 2*HEIGHT**2, height=HEIGHT,
                                include_ramified_two=True, mark_local=True)
               for field, disc in zip(fields, discriminants, strict=True)]
    result = decide(n, m, fields, derivatives, discriminants, columns,
                    query_cap=QUERY_CAP, time_cap=TIME_CAP)
    certificate = result.pop("certificate")
    if certificate:
        certificate["height"] = HEIGHT
        result["divisor"] = certificate["divisor"]
    if args.certificate_file is not None:
        args.certificate_file.write_text(json.dumps([certificate] if certificate else [],
                                                   separators=(",", ":"))+"\n")
    result["seconds"] = round(monotonic()-start, 4)
    print(json.dumps(result))


if __name__ == "__main__":
    main()
