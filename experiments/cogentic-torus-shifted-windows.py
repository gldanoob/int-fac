"""Search two public factor windows in the Gaussian norm-one group."""

import argparse
from math import gcd
from pathlib import Path
from runpy import run_path


HERE = Path(__file__).resolve().parent
TORUS = run_path(str(HERE / "cogentic-varying-norm-torus.py"))
multiply, power, trace, signed_multiple, height_split, FactorFound = (
    TORUS[name] for name in ("multiply", "power", "trace", "signed_multiple",
                            "height_split", "FactorFound")
)
local_collision = run_path(str(HERE / "cogentic-unit-collision-search.py"))["local_collision"]


def square_powers(value, first, last, k, modulus):
    point = power(value, first * first, k, modulus)
    step = power(value, 2 * first + 1, k, modulus)
    step_increment = multiply(value, value, k, modulus)
    for index in range(first, last + 1):
        yield index * index, point
        point = multiply(point, step, k, modulus)
        step = multiply(step, step_increment, k, modulus)


def shifted_factor_windows(modulus, k, base, stage_one, first_window, second_window):
    """Return a factor, a verified multiple for the powered base, or neither."""
    a, b = first_window
    c, d = second_window
    if min(a, c, stage_one) < 1 or a > b or c > d:
        raise ValueError("need positive ordered intervals and a positive stage-one exponent")
    left_start, left_stop = (a + c + 1) // 2, (b + d) // 2
    right_low, right_high = (c - b + 1) // 2, (d - a) // 2
    right_start = 0 if right_low <= 0 <= right_high else min(abs(right_low), abs(right_high))
    right_stop = max(abs(right_low), abs(right_high))
    if left_start > left_stop or right_low > right_high:
        return None, None
    if left_start <= right_stop:
        raise ValueError("need disjoint absolute index intervals")

    value = power(base, stage_one, k, modulus)
    right = {}
    left = []
    try:
        for exponent, point in square_powers(value, right_start, right_stop, k, modulus):
            key = trace(point, modulus)
            if key in right:
                old_exponent, old_point = right[key]
                return None, signed_multiple(point, old_point, exponent, old_exponent, modulus)
            right[key] = exponent, point

        for exponent, point in square_powers(value, left_start, left_stop, k, modulus):
            key = trace(point, modulus)
            if key in right:
                old_exponent, old_point = right[key]
                return None, signed_multiple(point, old_point, exponent, old_exponent, modulus)
            left.append(key)
    except FactorFound as found:
        return found.args[0], None

    hit = local_collision(modulus, left, list(right))
    return (None if hit is None else hit["factor"]), None


def gaussian_search(modulus, stage_one, first_window, second_window):
    if modulus < 3 or modulus % 2 == 0:
        raise ValueError("need an odd modulus >= 3")
    if gcd(5, modulus) > 1:
        return (5 if modulus > 5 else None), None
    # In the basis 1, omega=(1+i)/2 we have omega^2-omega+1/2=0.
    k = pow(2, -1, modulus)
    inv5 = pow(5, -1, modulus)
    base = -inv5 % modulus, 8 * inv5 % modulus
    factor, multiple = shifted_factor_windows(modulus, k, base, stage_one,
                                               first_window, second_window)
    if multiple is not None:
        full_exponent = stage_one * multiple
        assert power(base, full_exponent, k, modulus) == (1, 0)
        odd = full_exponent // (full_exponent & -full_exponent)
        factor = height_split(modulus, k, power(base, odd, k, modulus))
    assert factor is None or (1 < factor < modulus and modulus % factor == 0)
    return factor, multiple


def replay():
    p, q = 80138044891, 136234676587
    assert gaussian_search(p*q, 4, (100000, 100130), (200000, 200130)) == (p, None)
    p, q = 80070802051, 720637218467
    factor, multiple = gaussian_search(p*q, 36, (100000, 100010), (200166, 200180))
    assert factor == p and multiple == 100003*200171
    print("Shifted factor-window replay passed a proper local gcd and a global order certificate.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", type=int, nargs="?", help="omit to run both regression examples")
    parser.add_argument("--first", nargs=2, type=int, metavar=("LOW", "HIGH"))
    parser.add_argument("--second", nargs=2, type=int, metavar=("LOW", "HIGH"))
    parser.add_argument("--exponent", type=int, default=4)
    args = parser.parse_args()
    if args.N is None:
        replay()
    else:
        if args.first is None or args.second is None:
            parser.error("supply both factor windows")
        try:
            factor, multiple = gaussian_search(args.N, args.exponent, args.first, args.second)
        except ValueError as error:
            parser.error(str(error))
        if factor is None:
            if multiple:
                print(f"Verified global multiplier {args.exponent * multiple} for the Gaussian base.")
            else:
                print("No match in the supplied windows.")
            raise SystemExit(1)
        print(f"{args.N} = {factor} * {args.N // factor}")
