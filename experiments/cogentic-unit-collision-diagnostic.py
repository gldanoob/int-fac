"""Run the frozen unit-chart and public-unit control boxes in serial."""

import argparse
import json
import subprocess
import sys
from hashlib import sha256
from math import gcd
from pathlib import Path
from runpy import run_path
from time import monotonic


HERE = Path(__file__).resolve().parent
PLAN = json.loads((HERE / "cogentic-unit-collision-search.json").read_text())
ARMS = ("chart", "control")


def public_units(n, t, side, length):
    domain = PLAN["control_domain"].encode("ascii") + b"\0"
    prefix = domain + n.to_bytes(8, "big") + t.to_bytes(2, "big") + bytes((side,))
    limit = (1 << 256) - (1 << 256) % n
    values, counter = [], 0
    while len(values) < length:
        candidate = int.from_bytes(sha256(prefix + counter.to_bytes(8, "big")).digest(), "big")
        counter += 1
        if candidate < limit:
            residue = candidate % n
            if gcd(residue, n) == 1:
                values.append(residue)
    return values


def work(n, t, length, arm):
    search = run_path(str(HERE / "cogentic-unit-collision-search.py"))
    start = monotonic()
    if arm == "chart":
        result = search["search"](n, t, length, length)
    else:
        left, right = (public_units(n, t, side, length) for side in (0, 1))
        result = search["search_residues"](n, left, right)
    return dict(result, compute_seconds=round(monotonic()-start, 4))


def run():
    for group in PLAN["groups"]:
        bits, length = group["bits"], group["length"]
        for n in group["inputs"]:
            for t in PLAN["parameters"]:
                for arm in ARMS:
                    start = monotonic()
                    cmd = [sys.executable, __file__, "--worker", str(n), str(t), str(length), arm]
                    try:
                        child = subprocess.run(cmd, check=True, capture_output=True, text=True,
                                               timeout=PLAN["seconds_per_arm"])
                        result = json.loads(child.stdout)
                    except subprocess.TimeoutExpired:
                        result = dict(status="time-cap")
                    except subprocess.CalledProcessError as error:
                        result = dict(status="process-error", error=error.stderr.strip() or str(error.returncode))
                    except json.JSONDecodeError as error:
                        result = dict(status="process-error", error=str(error))
                    result.update(n=n, bits=bits, t=t, left_length=length, right_length=length,
                                  arm=arm, seconds=round(monotonic()-start, 4))
                    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worker", nargs=4, metavar=("N", "T", "LENGTH", "ARM"), help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.worker:
        n, t, length, arm = args.worker
        if arm not in ARMS:
            parser.error("worker requires chart or control")
        print(json.dumps(work(int(n), int(t), int(length), arm)), flush=True)
    else:
        run()
