"""Finite CRT and divisor identities for the smaller-space schedule."""
from fractions import Fraction
from itertools import combinations, product
from math import gcd, prod


def divisors_of_squarefree(primes):
    return [prod(s) for k in range(len(primes)+1) for s in combinations(primes,k)]


def local_classes():
    checks = 0
    for delta, prescribed, base in ((3*5*7,11,2),(3**2*5,7,2),(5*7**2,3,2),(3*11,5,7)):
        modulus = base*delta*prescribed
        allowed = [p for p in (2,3,5,7,11) if delta%p == 0 and gcd(p,prescribed*base)==1]
        support = prod(allowed)
        for u, slope in product(range(1,200), (-4,-1,0,2,5)):
            v = u + delta*slope
            forced = gcd(v, modulus)
            if gcd(v,base)>1 or any(forced % (p*p)==0 for p in (2,3,5,7,11)):
                continue
            assert prescribed*gcd(support,u) % forced == 0
            checks += 1
    return checks


def weighted_loss(primes):
    ds = divisors_of_squarefree(primes)
    total = prod(p+1 for p in primes)
    checks = 0
    for mask in ds:
        relevant = [p for p in primes if mask%p==0]
        # Count a CRT toy distribution with probability 1/(1+p) of each hit.
        masses = {n: Fraction(prod(p for p in primes if n%p),total) for n in ds}
        assert sum(masses.values()) == 1
        for restricted in (False,True):
            weighted = Fraction()
            upper = Fraction()
            for n,mass in masses.items():
                common = gcd(mask,n)
                if restricted and common==1:
                    continue
                weight = 2**sum(common%p==0 for p in relevant)
                weighted += mass*weight
                upper += mass*sum(2**sum(d%p==0 for p in relevant)
                                  for d in ds if common%d==0 and (d>1 or not restricted))
            euler = prod(1+Fraction(2,p+1) for p in relevant) - int(restricted)
            assert weighted<=upper==euler
            checks += 1
    return checks


def parameter_checks():
    count = 0
    for theta in map(Fraction, ('1/16','1/7','1/5','1/4','3/10','33/100')):
        for beta in map(Fraction, ('1/10','1','9/4','10')):
            kappa=1-2*theta
            for margin in map(Fraction, ('1/1000','1/10','1/2')):
                v = 4*kappa/beta + margin
                xmax = (beta*v/(2*kappa)-1)/v
                x = (1/v+xmax)/2
                c = (2*kappa*(v+1/x)/beta+v/x)/2
                assert v>1/x and v>x*c and c>2*kappa*(v+1/x)/beta
                count += 1
    return count


if __name__ == '__main__':
    print(local_classes(), 'admissible conditioned classes')
    print(weighted_loss([3,5,7,11,13]), 'exact weighted divisor sums')
    print(parameter_checks(), 'strict space/time schedules')
