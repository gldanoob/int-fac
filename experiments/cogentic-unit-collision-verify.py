"""Verify the frozen collision diagnostic independently using CRT residue sets."""

import argparse
from collections import Counter, defaultdict
from hashlib import sha256
import json
from math import expm1, gcd, isfinite, log1p
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
PLAN = HERE / "cogentic-unit-collision-search.json"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def proven_next(start):
    command = [os.environ.get("GP", "gp"), "-fq"]
    code = f"p=nextprime({start+1}); while(!isprime(p),p=nextprime(p+1)); print(p);\n"
    result = subprocess.run(command, input=code, capture_output=True, text=True, check=True, timeout=8)
    require(not result.stderr, "PARI prime regeneration failed")
    return int(result.stdout)


def regenerate(plan):
    excluded = set(json.loads((HERE / "cogentic-sheared-scaling-inputs.json").read_text()))
    labels, used = {}, set()
    seed = plan["seed"].encode("ascii")
    for group in plan["groups"]:
        bits = group["bits"]
        quarter = 1 << (bits//2-2)
        group_labels, counter = [], 0
        while len(group_labels) < 3:
            digest = sha256(seed+bits.to_bytes(2, "big")+counter.to_bytes(8, "big")).digest()
            counter += 1
            p, q = (proven_next(3*quarter+int.from_bytes(digest[i:i+16], "big") % quarter)
                    for i in (0, 16))
            n = p*q
            if p == q or max(p, q) >= 4*quarter or p in used or q in used or n in excluded:
                continue
            require(n.bit_length() == bits, "generator produced incorrect bit length")
            labels[n] = p, q
            used.update((p, q))
            group_labels.append(n)
        require(group_labels == group["inputs"], "regenerated public list disagrees with frozen plan")
    return labels


def chart(n, t, length):
    a = t*(t-1)*pow(t+1, -1, n) % n
    b = (t-1)*pow(t*(t+1), -1, n) % n
    left = pow(2, -1, n)*(a+1) % n
    right = pow(2, -1, n)*(b-1) % n
    return ([left*pow(a, i, n) % n for i in range(length)],
            [right*pow(b, i, n) % n for i in range(length)])


def hashes(domain, n, t, side, length):
    prefix = domain.encode("ascii")+b"\0"+n.to_bytes(8, "big")+t.to_bytes(2, "big")+bytes([side])
    limit = (1 << 256) - (1 << 256) % n
    output, counter = [], 0
    while len(output) < length:
        value = int.from_bytes(sha256(prefix+counter.to_bytes(8, "big")).digest(), "big")
        counter += 1
        if value < limit and gcd(value, n) == 1:
            output.append(value % n)
    return output


def crt_matches(n, p, q, left, right):
    # Keep global residues inside each reduction bucket; exclude exact equality, not the entire bucket.
    mod_p, mod_q, square_groups = defaultdict(set), defaultdict(set), defaultdict(set)
    signed = {}
    for j, y in enumerate(right):
        square_groups[(y*y % p, y*y % q)].add(min(y, -y % n))
        for sign in (1, -1):
            residue = sign*y % n
            signed.setdefault(residue, (j, sign))
            mod_p[residue % p].add(residue)
            mod_q[residue % q].add(residue)
    alignment = productive = False
    first_local = exact = None
    for i, x in enumerate(left):
        if first_local is None and any(len(bucket) > (x in bucket)
                                       for bucket in (mod_p[x % p], mod_q[x % q])):
            first_local = i
        square_classes = square_groups[(x*x % p, x*x % q)]
        alignment |= bool(square_classes)
        productive |= len(square_classes) > (min(x, -x % n) in square_classes)
        if exact is None and x in signed:
            j, sign = signed[x]
            exact = dict(i=i, j=j, x=x, y=right[j], sign=sign)
    return first_local, alignment, productive, exact, signed


def verify_pair(n, left, right, witness, *, signed=False):
    require(isinstance(witness, dict), f"{n}: invalid pair witness")
    i, j = witness["i"], witness["j"]
    require(type(i) is int and type(j) is int and 0 <= i < len(left) and 0 <= j < len(right),
            f"{n}: witness indices outside the frozen grid")
    x, y = left[i], right[j]
    require(type(witness["x"]) is int and type(witness["y"]) is int and
            witness["x"] == x and witness["y"] == y, f"{n}: witness residues disagree")
    if signed:
        sign = witness["sign"]
        require(type(sign) is int and sign in (1, -1), f"{n}: invalid witness sign")
        return x, y, sign
    return x, y


def verify_completed(record, p, q, left, right):
    n = p*q
    first_local, alignment, productive, exact, signed = crt_matches(n, p, q, left, right)
    local = first_local is not None
    require((record["status"] == "local-split") == local, f"{n}: local presence disagrees")
    require((record["global_alignment"] is not None) == alignment, f"{n}: global alignment disagrees")
    require((record["global_split"] is not None) == productive, f"{n}: productive alignment disagrees")
    require(record["exact_alignment"] == exact, f"{n}: first exact signed alignment disagrees")
    if exact is not None:
        verify_pair(n, left, right, record["exact_alignment"], signed=True)
    if alignment:
        x, y = verify_pair(n, left, right, record["global_alignment"])
        require((x*x-y*y) % n == 0, f"{n}: invalid full-square witness")
    if productive:
        witness = record["global_split"]
        x, y, sign = verify_pair(n, left, right, witness, signed=True)
        factor = gcd(x-sign*y, n)
        require((x*x-y*y) % n == 0 and factor in (p, q) and witness["factor"] == factor,
                f"{n}: invalid productive global witness")
    if local:
        witness = record["witness"]
        x, y, sign = verify_pair(n, left, right, witness, signed=True)
        factor = gcd(x-sign*y, n)
        require(factor in (p, q) and record["factor"] == factor and record["cofactor"]*factor == n,
                f"{n}: invalid local factor")
        require(witness["globally_aligned"] is ((x*x-y*y) % n == 0) and witness["exact_root"] is (x in signed),
                f"{n}: incorrect local witness flags")
        bucket, first_right = 1, None
        for value, right_index in signed.items():
            if value == x:
                continue
            bucket = bucket*(x-value) % n
            if first_right is None and ((x-value) % p == 0 or (x-value) % q == 0):
                first_right = right_index
        require(witness["i"] == first_local and (witness["j"], sign) == first_right,
                f"{n}: local witness is out of order")
        require(witness["bucket_gcd"] == gcd(bucket, n), f"{n}: incorrect global-hit removal in bucket")
    else:
        require(not any(key in record for key in ("factor", "cofactor", "witness")),
                f"{n}: unexpected local witness")
    return local, alignment, productive, exact is not None


def control_expectation(p, q, right, length):
    n = p*q
    signed = set(right) | {-value % n for value in right}
    mod_p = Counter(value % p for value in signed)
    mod_q = Counter(value % q for value in signed)
    safe = (p-1-len(mod_p))*(q-1-len(mod_q))
    safe += sum(mod_p[value % p] == mod_q[value % q] == 1 for value in signed)
    phi = (p-1)*(q-1)

    def at_least_once(hits):
        return 1.0 if hits == phi else -expm1(length*log1p(-hits/phi))

    return at_least_once(phi-safe), at_least_once(len(signed))


def read_records(path):
    def unique_object(pairs):
        result = dict(pairs)
        require(len(result) == len(pairs), "duplicate JSON key")
        return result

    records = [json.loads(line, object_pairs_hook=unique_object) for line in path.read_text().splitlines()]
    require(all(isinstance(record, dict) for record in records), "expected JSON object records")
    return records


def verify(path):
    plan = json.loads(PLAN.read_text())
    expected = [(group["bits"], n, t, group["length"], arm)
                for group in plan["groups"] for n in group["inputs"] for t in plan["parameters"]
                for arm in ("chart", "control")]
    records = read_records(path)
    require(len(records) == len(expected) == 72, "expected 72 frozen arm records")
    labels = regenerate(plan)
    aggregates = defaultdict(Counter)
    cap = plan["seconds_per_arm"]
    for record, (bits, n, t, length, arm) in zip(records, expected, strict=True):
        context = f"{n}, t={t}, {arm}"
        require(all(record[key] == value for key, value in (
            ("bits", bits), ("n", n), ("t", t), ("left_length", length),
            ("right_length", length), ("arm", arm))), f"{context}: changed plan or record order")
        seconds, status = record["seconds"], record["status"]
        require(type(seconds) in (int, float) and isfinite(seconds) and seconds >= 0,
                f"{context}: malformed wall time")
        compute = record.get("compute_seconds")
        require(compute is None or (type(compute) in (int, float) and isfinite(compute)
                                     and 0 <= compute <= seconds+0.001),
                f"{context}: inconsistent compute time")
        p, q = labels[n]
        group = aggregates[bits, arm]
        group["arms"] += 1
        checks = [("t", t), ("t-1", t-1), ("t+1", t+1), ("t^2+1", t*t+1)]
        failed = [(name, gcd(value, n)) for name, value in checks if gcd(value, n) != 1]
        if arm == "chart" and failed:
            direct = next(((name, value) for name, value in failed if 1 < value < n), None)
            if direct:
                name, factor = direct
                require(status == "parameter-gcd" and record["parameter_check"] == name and
                        record["factor"] == factor and record["cofactor"]*factor == n,
                        f"{context}: invalid parameter gcd")
            else:
                require(status == "ineligible", f"{context}: expected ineligible parameter")
            group[status] += 1
            continue
        if arm == "chart":
            left, right = chart(n, t, length)
        else:
            left, right = (hashes(plan["control_domain"], n, t, side, length) for side in (0, 1))
            local_expectation, productive_expectation = control_expectation(p, q, right, length)
            group["expected_local"] += local_expectation
            group["expected_productive"] += productive_expectation
        require(all(gcd(x, n) == 1 for x in left) and all(gcd(y, n) == 1 for y in right),
                f"{context}: nonunit residue")
        if status in ("time-cap", "process-error"):
            if status == "time-cap":
                require(seconds >= cap-0.001, f"{context}: premature time cap")
            require(compute is None and not any(key in record for key in ("factor", "cofactor", "witness")),
                    f"{context}: failed arm reported a factor")
            first_local, alignment, productive, exact, _ = crt_matches(n, p, q, left, right)
            flags = first_local is not None, alignment, productive, exact is not None
            group[status] += 1
        else:
            require(status in ("box-exhausted", "local-split"), f"{context}: unrecognized status")
            require(seconds <= cap+0.001 and compute is not None and compute <= cap,
                    f"{context}: completed arm exceeded its cap")
            flags = verify_completed(record, p, q, left, right)
            group["completed"] += 1
        for name, present in zip(("local", "aligned", "productive", "exact"), flags, strict=True):
            group[name] += int(present)
    for (bits, arm), counts in aggregates.items():
        print(json.dumps(dict(bits=bits, arm=arm, **counts)))
    print("Independently verified all 72 frozen arm records.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("records", nargs="?", type=Path,
                        default=HERE / "cogentic-unit-collision-search-results.jsonl")
    args = parser.parse_args()
    try:
        verify(args.records)
    except (ValueError, KeyError, OSError) as error:
        parser.error(str(error))
