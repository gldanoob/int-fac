"""Construct two monic Eisenstein polynomials with an exact shared value."""


def integer_root(n, degree):
    """Floor of the positive integer root, by binary search."""
    low, high = 0, 1 << ((n.bit_length()+degree-1)//degree)
    while high-low > 1:
        middle = (low+high)//2
        if middle**degree <= n:
            low = middle
        else:
            high = middle
    return low


def scheduled_degree(n):
    bits = n.bit_length()
    return max(2, integer_root(bits//bits.bit_length(), 3))


def monic_pair(n, degree):
    """Return the odd common argument and coefficients in ascending order."""
    if n < 9 or n % 2 == 0 or degree < 2:
        raise ValueError("need an odd input at least nine and degree at least two")
    m = integer_root(n, degree)
    if m % 2 == 0:
        m -= 1
    if m < 3:
        raise ValueError("need an odd base at least three")

    quotient, constant = divmod((n-m**degree)//2, m)
    if constant % 2 == 0:
        constant -= m
        quotient += 1
    digits = [constant]
    for _ in range(degree-2):
        quotient, digit = divmod(quotient, m)
        digits.append(digit)
    # The top coefficient holds the remaining quotient, even past one digit.
    f = tuple(2*digit for digit in (*digits, quotient)) + (1,)
    g = f[:-1] + (1-m, 1)
    return m, f, g


def check_pair(n, degree):
    m, f, g = monic_pair(n, degree)
    assert m >= 3 and m % 2 == 1 and m**degree <= n < (m+2)**degree
    assert len(f) == degree+1 and g == f[:-1]+(1-m, 1)
    assert abs(f[-2]//2)*m**(degree-1) <= (n-m**degree)//2+m
    for coefficients in (f, g):
        assert coefficients[-1] == 1 and coefficients[0] % 4 == 2
        assert all(c % 2 == 0 for c in coefficients[:-1])
        assert sum(c*m**i for i, c in enumerate(coefficients)) == n
    return m, f, g


def run():
    assert check_pair(9, 2) == (3, (-6, 2, 1), (-6, 2, -2, 1))
    assert check_pair(11, 2)[1] == (2, 0, 1)
    assert check_pair(17, 2)[0] == 3  # even floor root rounds down
    assert check_pair(123, 3)[1][-2] == 10  # top quotient exceeds the radix
    for n, degree in ((7, 2), (10, 2), (9, 1), (9, 3)):
        try:
            monic_pair(n, degree)
        except ValueError:
            pass
        else:
            raise AssertionError((n, degree))

    inputs = (9, 11, 17, 21, 23, 25, 125, (1 << 127)+1, (1 << 255)-19, (1 << 1023)+1)
    for n in inputs:
        degree = scheduled_degree(n)
        m, f, g = check_pair(n, degree)
        assert max(map(abs, f+g)) <= 2*m
        height = 11
        for coefficients in (f, g):
            e = len(coefficients)-1
            for a, b in ((-height, height), (2, -3), (1, 0)):
                norm = sum(c*a**i*b**(e-i) for i, c in enumerate(coefficients))
                assert abs(norm) <= 2*m*(e+1)*height**e
    print(f"Verified monic Eisenstein pairs on {len(inputs)} scheduled inputs, plus carry and boundary cases")


if __name__ == '__main__':
    run()
