"""Replay the dense-prime and exponent-merging steps on finite unit groups."""

from math import gcd, isqrt, lcm


def primes_up_to(limit):
    flags = bytearray([1]) * (limit + 1)
    flags[:2] = bytes(2)
    for prime in range(2, isqrt(limit) + 1):
        if flags[prime]:
            flags[prime * prime :: prime] = bytes((limit - prime * prime) // prime + 1)
    return [n for n in range(2, limit + 1) if flags[n]]


def order(a, n, group_size, divisors):
    result = group_size
    for p in divisors:
        while result % p == 0 and pow(a, result // p, n) == 1:
            result //= p
    return result


def generated_subgroup(bases, n):
    subgroup = {1}
    for a in bases:
        if a % n in subgroup:
            continue
        power = a % n
        coset_reps = [1]
        while power not in subgroup:
            coset_reps.append(power)
            power = power * a % n
        subgroup = {z * h % n for z in coset_reps for h in subgroup}
    return subgroup


def small_unit_guard(n, candidate):
    return all(
        pow(a, candidate, n) == 1
        for a in range(2, min(n, 3 * n.bit_length() ** 2 + 1))
        if gcd(a, n) == 1
    )


def two_part(n):
    return n & -n


def split_chain(n, p, exponent):
    power = pow(p, exponent // two_part(exponent), n)
    while power != 1:
        divisor = gcd(power - 1, n)
        if 1 < divisor < n:
            return divisor
        power = power * power % n
    return 1


def merge(n, bases, orders, full_exponent, inflate):
    candidate = 2
    merges = 0
    for p in bases:
        if pow(p, candidate, n) == 1:
            continue
        verified = orders[p % n] * (2 * (p + 1) if inflate else 1)
        assert pow(p, verified, n) == 1
        enlarged = lcm(candidate, verified)
        assert gcd(enlarged, full_exponent) >= 2 * gcd(candidate, full_exponent)
        candidate = enlarged
        merges += 1
    assert merges <= n.bit_length()
    assert candidate % full_exponent == 0 and small_unit_guard(n, candidate)
    return merges


def main():
    primes = primes_up_to(4096)
    interval = [p for p in primes if p > 2048]
    masks = merges_checked = deficient_rejections = lifted = max_merges = 0
    split_inputs = split_chains = equal_valuations = 0
    for n in range(3, 385):
        units = {a for a in range(1, n) if gcd(a, n) == 1}
        divisors = [p for p in primes if len(units) % p == 0]
        orders = {a: order(a, n, len(units), divisors) for a in units}
        exponent = lcm(*orders.values())
        residue_exponent = lcm(*(p - 1 for p in primes if n % p == 0))
        lifted += exponent > residue_exponent
        for p in divisors:
            if exponent % p == 0:
                assert not small_unit_guard(n, exponent // p)
                deficient_rejections += 1
        half_exponent = exponent // 2
        hardest = sorted(interval, key=lambda p: pow(p, half_exponent, n) != 1)
        quarter = len(interval) // 4
        for selected in (interval, interval[quarter:], hardest[:-quarter]):
            assert generated_subgroup(selected, n) == units
            masks += 1
            for inflate in (False, True):
                max_merges = max(max_merges, merge(n, selected, orders, exponent, inflate))
                merges_checked += 1
        prime_divisors = [p for p in primes if n % p == 0]
        if n % 2 and len(prime_divisors) >= 2:
            p, q = sorted(prime_divisors, key=lambda p: two_part(p - 1), reverse=True)[:2]
            tied = two_part(p - 1) == two_part(q - 1)
            witnesses = 0
            for base in interval:
                p_negative = pow(base, (p - 1) // 2, p) == p - 1
                q_negative = pow(base, (q - 1) // 2, q) == q - 1
                if p_negative == (tied and q_negative):
                    continue
                witnesses += 1
                for multiple in (1, 2 * base * (base + 1)):
                    divisor = split_chain(n, base, multiple * orders[base % n])
                    assert 1 < divisor < n and n % divisor == 0
                    split_chains += 1
            assert witnesses
            split_inputs += 1
            equal_valuations += tied
    print(f"{len(interval)} dyadic primes, 382 moduli, {masks} generated groups")
    print(f"{merges_checked} exponent sweeps replayed, at most {max_merges} updates per replay")
    print(f"{deficient_rejections} deficient exponents rejected, {lifted} strict prime-power lifts")
    print(f"{split_chains} witness chains split {split_inputs} odd inputs, {equal_valuations} tied cases")


if __name__ == "__main__":
    main()
