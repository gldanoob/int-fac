\\ Finite literal cyclic-order gcd refinements from one supplied value.
field_library(k, conductors) = {
  my(levels=List(conductors), fields=List());
  for(i=1,#conductors-1, for(j=i+1,#conductors,
    listput(levels,conductors[i]*conductors[j])
  ));
  foreach(Vec(levels), conductor,
    my(polynomials=polsubcyclo(conductor,k));
    if(type(polynomials)=="t_POL",polynomials=[polynomials]);
    foreach(polynomials, f,
      if(nfdisc(f)!=conductor^(k-1),next);
      listput(fields,[conductor,f])
    )
  );
  Vec(fields)
};

literal_scalar(f, a, exponent, t) = {
  my(roots=polrootsmod(f,t));
  if(#roots,
    my(values=apply(root->subst(a,x,root)^exponent,Vec(roots)));
    return(#Set(values)==1)
  );
  my(y=ffgen(Mod(1,t)*f,'y), z=(y^0*subst(a,x,y))^exponent);
  z^t==z
};

refine(parts,g) = {
  my(result=List());
  foreach(parts, a,
    my(b=gcd(a,g));
    if(1<b&&b<a,listput(result,b);listput(result,a/b),listput(result,a))
  );
  vecsort(Vec(result))
};

check_pair_library(fields, primes, k) = {
  my(table=matrix(#fields,#primes,i,j,#polrootsmod(fields[i][2],primes[j])));
  for(i=1,#fields, for(j=1,#primes,
    if(!(table[i,j]==0 || table[i,j]==k),error("noncyclic local pattern"));
    if(isprime(fields[i][1]) && table[i,j]!=0,error("fixture requires all singleton fields inert"))
  ));
  for(i=1,#primes-1, for(j=i+1,#primes,
    if(!sum(h=1,#fields,table[h,i]!=table[h,j]),
      error("pair not separated by a cyclic field", [k,primes[i],primes[j]]))
  ))
};

run_literal(label, original, test_primes, M, k, fields, radius) = {
  my(n=original, small=List(), history=List(), exponent=M>>valuation(M,2), attempts=0);
  forprime(t=2,5,while(n%t==0,listput(small,t);n/=t));
  if(n!=prod(i=1,#test_primes,test_primes[i]),error("clipped residual"));
  foreach(test_primes,t,
    if(exponent%((t^k-1)/(t-1))!=0,error("uncovered projective order", [k,t]))
  );
  my(parts=[n]);
  foreach(fields, field,
    my([conductor,f]=field);
    if(#parts==#test_primes,break);
    forvec(c=vector(k,i,[-radius,radius]),
      if(#parts==#test_primes,break);
      if(!vecmax(abs(c)),next);
      my(a=Polrev(c), value=liftall(Mod(Mod(1,n)*a,f)^exponent));
      attempts++;
      my(g=gcd(n,gcd(vector(k-1,i,polcoeff(value,i)))), candidate=refine(parts,g));
      if(#candidate==#parts,next);
      my(direct=prod(i=1,#test_primes,my(t=test_primes[i]); if(literal_scalar(f,a,exponent,t),t,1)));
      if(g!=direct,error("literal gcd disagrees with finite field checks", [k,conductor,c,g,direct]));
      if(isprime(conductor),error("expected scalar refinement only at 2-conductor fields"));
      if(prod(i=1,#candidate,candidate[i])!=n,error("refinement product"));
      listput(history,[conductor,c,g,#candidate]);
      parts=candidate
    )
  );
  if(parts!=test_primes,error("incomplete literal partition", [label,k,parts]));
  if(prod(i=1,#small,small[i])*prod(i=1,#parts,parts[i])!=original,
    error("original product not recovered"));
  print(label, " k=",k," N=",original," Mbits=",#binary(M)," tries=",attempts, " full factors=",concat(Vec(small),parts));
  print("  [conductor, coefficient vector, global gcd, part count] ",Vec(history))
};

fixture(k, j, conductors, primes) = {
  my(small=[[2,4],[3,2],[5,3]], factors=concat(small,apply(p->[p,1],primes)),
     original=prod(i=1,#factors,factors[i][1]^factors[i][2]),
     M=prod(i=1,#factors,my(p=factors[i][1], e=j*factors[i][2]); (p^(e+1)-1)/(p-1)),
     fields=field_library(k,conductors),
     inflated=M*2^137*(2^509+1)*(10^210+9));
  if(j%2 || (j+1)%k || factor(j+1)[1,1]!=k,error("bad power fixture"));
  check_pair_library(fields,primes,k);
  run_literal(Str("one sigma(N^",j,")"),original,primes,M,k,fields,1);
  run_literal("same value times arbitrary large multiplier",original,primes,inflated,k,fields,1)
};


saturate(n,g) = gcd(n,lift(Mod(g,n)^#binary(n)));

projective_order_at_inert(k,t) = (t^k-1)/(t-1);

check_single_coverage(n, M, primes, k, covered) = {
  my(orders=apply(t->projective_order_at_inert(k,t),primes));
  if(select(i->M%orders[i]==0,[1..#primes])!=[covered],
    error("fixture must have exactly one covered local order", [k,M,primes,covered]));
  if(n%prod(i=1,#primes,primes[i])!=0,error("fixture prime support"))
};

quad_library(ds) = {
  my(fields=List());
  foreach(ds,d,listput(fields,[d,x^2-d]));
  for(i=1,#ds-1,for(j=i+1,#ds,
    listput(fields,[ds[i]*ds[j],x^2-ds[i]*ds[j]])
  ));
  Vec(fields)
};

one_covered_literal(k,n,M,p,q,fields) = {
  my(first=[], oriented=[], odd=M>>valuation(M,2));
  foreach(fields, field,
    if(#first && #oriented, break);
    my([conductor,f]=field, orientation=(#polrootsmod(f,p)==0 && #polrootsmod(f,q)==k));
    forvec(c=vector(k,i,[-1,1]),
      if(#first && #oriented,break);
      if(!vecmax(abs(c)),next);
      my(a=Polrev(c), ex=odd, steps=if(k==2,valuation(M,2)+1,1));
      for(i=1,steps,
        my(v=liftall(Mod(Mod(1,n)*a,f)^ex),
           g=saturate(n,gcd(n,gcd(vector(k-1,j,polcoeff(v,j))))));
        if(1<g && g<n,
          if(!#first,first=[conductor,c,i-1,g]);
          if(!#oriented && orientation && !(g%p) && g%q,
            if(!literal_scalar(f,a,ex,p) || literal_scalar(f,a,ex,q),
              error("orientation disagrees with local test"));
            oriented=[conductor,c,i-1,g]
          );
        );
        ex*=2;
      )
    )
  );
  if(!#first || !#oriented,error("single-covered split failed", [k,n,p,q,first,oriented]));
  print("single covered k=",k," covered=",p," comparator=",q," Mbits=",#binary(M),
        " first=",first," inert/split certificate=",oriented)
};

single_fixture(k,conductors,primes) = {
  my(n=primes[1]^2*primes[2]*primes[3]^3,
     fields=if(k==2,quad_library(conductors),field_library(k,conductors)),
     inflation=2^137*(2^509+1)*(10^210+9));
  foreach([1,3], covered,
    my(other=4-covered,p=primes[covered],q=primes[other],M=projective_order_at_inert(k,p)*inflation);
    check_single_coverage(n,M,primes,k,covered);
    one_covered_literal(k,n,M,p,q,fields)
  )
};

reference_fixture() = {
  my(p=1019,q=1000037, r=1031, n=p^2*q^3*r,
     M=lcm(p+1,q-1)*2^137*(2^509+1)*(10^210+9), odd=M>>valuation(M,2),
     found=[], fields=quad_library([2,3,5,7,11]));
  check_single_coverage(n,M,[p,r,q],2,1);
  if(valuation(p+1,2)!=valuation(q-1,2) || M%(q-1)!=0,
    error("intended field thresholds do not tie"));
  if(!sum(i=1,#fields,kronecker(fields[i][1],p)==-1&&kronecker(fields[i][1],q)==1),
    error("missing inert/split field"));
  for(a=2,40,
    if(#found,break);
    if(gcd(a,n)!=1,next);
    for(i=0,valuation(M,2),
      my(g=saturate(n,gcd(n,lift(Mod(a,n)^(odd<<i))-1)));
      if(1<g&&g<n && ((g%p==0)!=(g%q==0)),found=[a,i,g];break)
    )
  );
  if(!#found,error("reference failed to split a tied inert/split pair"));
  print("single covered k=2 with tied inert/split thresholds, covered=",p,
        " comparator=",q," reference certificate=",found)
};

iferr({
  fixture(3,8,[7,13,19,31],[1153,1181,1277,1297,1307,1381]);
  fixture(5,24,[11,31,41,61],[1009,1019,1021,1061,1103,1129]);
  single_fixture(3,[7,13,19,31],[1153,1181,1000253]);
  single_fixture(5,[11,31,41,61],[1009,1019,1000037]);
  single_fixture(2,[2,3,5,7,11],[1019,1031,1000037]);
  reference_fixture();
},err,print(err);quit(1));
