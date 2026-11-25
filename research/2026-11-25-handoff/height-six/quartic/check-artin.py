"""Recompute the relative norms and cubic splitting types at certified quartic values."""

import ast
import json
import subprocess
from math import gcd, isqrt
from pathlib import Path

here = Path(__file__).resolve().parent
fixture = json.loads((here / "construction.json").read_text())
fields = [ast.literal_eval(line) for line in (here.parent / "fields6.txt").read_text().splitlines()]
s, ray = fixture["seed"], fixture["ray_conductor"]
a, b = fixture["alpha"], fixture["beta"]
assert gcd(s, ray * fixture["marker_modulus"]) == 1
for vector, first in [(a, 1), (b, 0)]:
    assert (vector[0] - first) % ray == 0 and all(v % ray == 0 for v in vector[1:])
    assert all(v % fixture["marker_modulus"] == 0 for v in vector[2:])
    u, v = fixture["u"], fixture["v"]
    assert (u*u-u+1) % s**3 == (v*v-v+5) % s**3 == 0
    assert sum(t*z for t,z in zip(vector, [1,u,v,u*v])) % s**3 == 0

locked = []
for disc, row in fields:
    for D in (-3, -19, 57):
        if disc % D == 0 and disc // D > 0:
            f = isqrt(disc // D)
            if disc == D * f*f:
                assert ray % f == 0
                locked.append(row)
assert len(locked) == 16
scripts = [
    f"s={s}; A={a}; B={b}; P=Polrev({fixture['coefficients']});",
    "v=A+x*B; z=v[1]+v[2]*y+v[3]*t+v[4]*y*t;",
    'if(polresultant(y^2-y+1,polresultant(t^2-t+5,z,t),y)!=s^3*P,error("quartic norm"));',
    f"fields={fields}; locked={locked};",
    f"markers={[[int(key), bit] for key,bit in fixture['profile'].items()]};",
    """check(j)={
        my(p=subst(P,x,j),inert=0,rest=0,forced=0);
        if(!isprime(p) || p==s || p%24!=1,error("prime value"));
        foreach(markers,c,if(kronecker(c[1],p)!=(-1)^c[2],error("profile")));
        foreach([7,9,13,19],m,if(!sum(a=1,m,(a^3-p)%m==0),error("cyclic conductor")));
        foreach(fields,g,
            my(d=g[1],r=g[2],f=x^3+Polrev(r),factors=factormod(f,p,1));
            if(vecmax(factors[,2])>1,error("unexpected ramification"));
            if(setsearch(Set(locked),r),
                if(matsize(factors)[1]!=3,error("locked cubic"));
                forced++);
            my(inactive=issquare(d) || kronecker(d,p)<0);
            if(inactive && factors[1,1]==3,error("fixed field bit"));
            if(!inactive && !setsearch(Set(locked),r),rest++;inert+=(factors[1,1]==3)));
        if(forced!=16 || rest!=54,error("partition"));
        print([j,logint(p,2)+1,forced,rest,inert]);
    };""",
    'iferr(foreach([532,683,1238],j,check(j)),E,print(E);quit(1));',
]
result = subprocess.run(["gp", "-s", "256M", "-fq"], input="\n".join(scripts)+"\n",
                        capture_output=True, text=True)
if result.returncode or result.stderr or len(result.stdout.splitlines()) != 3:
    raise RuntimeError(result.stderr or result.stdout)
print(result.stdout, end="")
