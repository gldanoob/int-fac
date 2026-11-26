#!/usr/bin/env python3
"""Try stage-one factoring on twists of a fixed split genus-two quintic."""

import argparse
import ast
import os
from math import isqrt, prod
from pathlib import Path
import subprocess
import sys


HERE = Path(__file__).resolve().parent
ROOTS = (0, 1, 3, 7, 11)

PROGRAM = r'''
read("genus-two-cantor.gp");

odd_scalar(n, bound) = {
  my(exponent=1, limit=16*n^2);
  forprime(p=3,min(bound,limit), exponent*=p^logint(limit,p));
  exponent;
}

twist(e,u,v) = {
  my(shifts=vector(#e,i,v*e[i]), d=prod(i=1,#e,u-shifts[i]));
  [vector(#e,i,d*shifts[i]),d*u,d^3];
}

twist_class(e,u,v) = {
  my(data=twist(e,u,v), roots=data[1]);
  [prod(i=1,#roots,x-roots[i]), [x-data[2],data[3]]];
}

torsion_test(data,scalar,n) = {
  my(roots=data[1], one=Mod(1,n));
  my(f=prod(i=1,#roots,(x-roots[i])*one), point=[(x-data[2])*one,data[3]*one]);
  my(current=multiply_divisor(point,scalar,f,n), upper=logint(16*n^2,2)+1);
  for(k=1,upper,
    if(current[1]==1,break);
    my(doubled=cantor(current,current,f,n));
    if(doubled[1]==1,
      if(current[2]!=0,error("nonzero v on global two-torsion"));
      for(i=1,#roots,unit_or_factor(subst(current[1],x,roots[i]),n));
      break;
    );
    current=doubled;
  );
  0;
}

check_torsion(e,u,v,scalar,n) = {
  my(result=0);
  iferr(torsion_test(twist(e,u,v),scalar,n),err,
    if(errname(err)!="e_USER",error(err));
    my(payload=component(err,1));
    if(#payload!=2 || payload[1]!="factor ",error(err));
    result=payload[2];
  );
  result;
}

candidate(e,u,v,scalar,n) = {
  my(singular=0);
  for(i=0,#e,
    my(g=gcd(if(i==0,v,u-v*e[i]),n));
    if(g>1 && g<n,return(g));
    if(g==n,singular=1);
  );
  if(singular,return(0));
  check_torsion(e,u,v,scalar,n);
}

search_twists(n,e,bound,height,scalar) = {
  my(singular=0);
  for(i=1,#e, for(j=1,i-1,
    my(g=gcd(e[i]-e[j],n));
    if(g>1 && g<n,return([g,0,0]));
    if(g==n,singular=1);
  ));
  if(singular,return([0,0,0]));
  if(!scalar,scalar=odd_scalar(n,bound));
  for(h=1,height,
    for(u=-h,h,
      if(gcd(u,h)!=1,next);
      my(g=candidate(e,u,h,scalar,n));
      if(g,return([g,u,h]));
    );
    for(v=1,h-1,
      if(gcd(h,v)!=1,next);
      forstep(u=-h,h,2*h,
        my(g=candidate(e,u,v,scalar,n));
        if(g,return([g,u,v]));
      );
    );
  );
  [0,0,0];
}
'''


def run_gp(expression, extra=""):
    source = PROGRAM + extra + f'\niferr(print({expression}), err, print(err); quit(1))\nquit(0)\n'
    result = subprocess.run([os.environ.get("GP", "gp"), "-fq"], cwd=HERE, input=source,
                            text=True, capture_output=True)
    if result.returncode or result.stderr:
        raise RuntimeError((result.stderr or result.stdout).strip())
    return ast.literal_eval(result.stdout)


def find_split(modulus, bound, menu, roots=ROOTS, exponent=None):
    """Return a proper divisor and its chart, or None after the bounded search."""
    if type(modulus) is not int or modulus < 3 or modulus % 2 == 0:
        raise ValueError("need an odd modulus at least 3")
    if any(type(x) is not int or x < 1 for x in (bound, menu)):
        raise ValueError("smoothness and chart bounds must be positive integers")
    if len(roots) != 5 or any(type(x) is not int for x in roots) or len(set(roots)) != 5:
        raise ValueError("need five distinct integer roots")
    if exponent is not None and (type(exponent) is not int or exponent < 1 or exponent % 2 == 0):
        raise ValueError("the explicit multiplier must be a positive odd integer")
    square = isqrt(modulus)
    if square*square == modulus:
        return square, None
    divisor, u, v = run_gp(f"search_twists({modulus},{list(roots)},{bound},{menu},{exponent or 0})")
    if divisor == 0:
        return None
    assert 1 < divisor < modulus and modulus % divisor == 0
    return divisor, (u, v) if v else None


REPLAY = r'''
curve_order(e,u,v,p) = {
  my(chart=twist_class(e,u,v), one=Mod(1,p));
  my(f=chart[1]*one, point=chart[2]*one);
  my(weil=hyperellcharpoly(f), order=subst(weil,x,1), marked_order=order);
  if(multiply_divisor(point,order,f,p)[1]!=1,error("Jacobian order does not kill the mark"));
  my(primes=factor(order)[,1]);
  for(i=1,#primes,
    my(ell=primes[i]);
    while(marked_order%ell==0 && multiply_divisor(point,marked_order/ell,f,p)[1]==1,marked_order/=ell);
  );
  [order,marked_order,Vecrev(weil),polisirreducible(weil)];
}

normalization(e,u,v) = {
  my(rational=twist_class(e,u/v,1), integral=twist_class(e,u,v));
  integral[1]==v^30*subst(rational[1],x,x/v^6) &&
  integral[2][1]==v^6*subst(rational[2][1],x,x/v^6) && integral[2][2]==v^15*rational[2][2];
}

comparison_orders(p) = {
  my(a=ellcard(ellinit([0,-4,0,3,0],p)));
  [p-1,p+1,a,2*p+2-a];
}
'''


def check_cosets():
    expected = {(twist, mask) for twist in (0, 1) for mask in range(32) if mask.bit_count() % 2 == 0}
    for prime in (127, 331, 347, 439):
        covered = set()
        for mark in range(prime):
            shifts = tuple((mark - e) % prime for e in ROOTS)
            if 0 in shifts:
                continue
            power = (prime - 1)//2
            d = prod(shifts) % prime
            raw = sum((pow(s, power, prime) == prime - 1) << i for i, s in enumerate(shifts))
            twist = pow(d, power, prime) == prime - 1
            mask = sum((pow(d*s, power, prime) == prime - 1) << i for i, s in enumerate(shifts))
            assert twist == raw.bit_count() % 2 and mask == raw ^ (31*twist)
            covered.add((twist, mask))
        assert covered == expected


def replay():
    check_cosets()
    e = list(ROOTS)
    p, q = 439, 347
    modulus = p*q
    expression = (f"[normalization({e},-2,3),candidate({e},-4,1,3,{modulus}),"
                  f"curve_order({e},-4,1,{p}),curve_order({e},-4,1,{q}),"
                  f"comparison_orders({p}),comparison_orders({q})]")
    normalized, gcd, first, second, *orders = run_gp(expression, REPLAY)
    assert normalized == 1 and gcd == p
    assert first == [196608, 32, [192721, 3512, 366, 8, 1], 1]
    assert second[:2] == [121904, 15238]
    for order in (*orders[0], *orders[1]):
        while order % 2 == 0:
            order //= 2
        while order % 3 == 0:
            order //= 3
        assert order > 1
    assert find_split(modulus, 3, 1) == (q, (-1, 1))
    assert find_split(101, 3, 2) is None
    assert find_split(11**2, 3, 1) == (11, None)
    print("All 32 twist and Kummer coset combinations occur at each of four replay primes.")
    print(f"Public bound-3 search splits {modulus} = {p} * {q}. The marked orders at c=-4 are 32 and 15238.")


def main():
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", type=int, nargs="?", help="odd integer to split, or omit to run the replay")
    options = parser.add_mutually_exclusive_group()
    options.add_argument("--exponent", type=int, help="public odd scalar")
    options.add_argument("--bound", type=int, default=3, help="odd smoothness cutoff, defaults to 3")
    parser.add_argument("--menu", type=int, default=12, help="maximum numerator or denominator magnitude")
    parser.add_argument("--roots", type=int, nargs=5, default=ROOTS, help="five distinct integer roots")
    args = parser.parse_args()
    if args.N is None:
        replay()
        return
    try:
        result = find_split(args.N, args.bound, args.menu, args.roots, args.exponent)
    except ValueError as error:
        parser.error(str(error))
    if result is None:
        print("No split in the specified menu.")
        raise SystemExit(1)
    divisor, chart = result
    suffix = f" (chart {chart[0]}/{chart[1]})" if chart is not None else ""
    print(f"{args.N} = {divisor} * {args.N // divisor}{suffix}")


if __name__ == "__main__":
    main()
