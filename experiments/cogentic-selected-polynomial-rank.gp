\\ Exact finite scoring. Run after cogentic-quadratic-order.gp is loaded.

rank_field_marks(n, m, slope, constant, height, primeset) = {
  my(disc = slope^2-4*constant, marks = Map());
  my(excluded = prod(j=1,#primeset,if(disc % primeset[j]^2 == 0,primeset[j],1)));
  my(prime_product = prod(j=1,#primeset,primeset[j]));
  for(a=1,height, for(b=-height,height,
    if(b == 0 || gcd(a,b) != 1 || gcd(a-b*m,n) != 1, next);
    \\ Reject nonsmooth norms before computing all the separate valuations.
    my(rest = a^2+slope*a*b+constant*b^2, part);
    while(rest>1 && (part=gcd(rest,prime_product))>1, rest /= part);
    if(rest>1, next);
    my(entries = norm_entries(a,b,1,[slope],[constant],[excluded],primeset));
    if(type(entries) == "t_VEC", mapput(marks,a*(2*height+1)+b,entries));
  ));
  marks;
}

rank_pair_score(n, left, right, slope, constant, primeset) = {
  my(rows = Map(), columns = List(), rowcount = 0);
  for(i=1,matsize(left)[1],
    my(other);
    if(!mapisdefined(right,left[i,1],&other), next);
    my(col = concat(left[i,2],vector(#other,j,[[2,other[j][1][2],other[j][1][3]],other[j][2]])));
    for(j=1,#col,
      my(key = col[j][1]);
      if(!mapisdefined(rows,key), rowcount++; mapput(rows,key,rowcount));
    );
    listput(columns,col);
  );
  if(!rowcount, return([0,#columns,0,#columns]));
  my(M = matrix(rowcount,#columns));
  for(i=1,#columns, for(j=1,#columns[i],
    my(entry = columns[i][j]);
    M[mapget(rows,entry[1]),i] = entry[2];
  ));
  my(piv = matindexrank(M), rank = #piv[2]);
  my(basis = vecextract(M,[1..rowcount],piv[2]), inverse = vecextract(M,piv[1],piv[2])^-1);
  my(disc = slope^2-4*constant, targets = 0);
  for(i=1,#primeset,
    my(p = primeset[i], first, second);
    if(p<=2 || gcd(p,n*disc)!=1, next);
    my(roots = polrootsmod(x^2+slope*x+constant,p));
    if(#roots != 2 || !mapisdefined(rows,[1,p,lift(roots[1])],&first)
                   || !mapisdefined(rows,[1,p,lift(roots[2])],&second), next);
    my(rhs = vector(rowcount)~);
    rhs[first] = rhs[second] = 1;
    if(basis*(inverse*vecextract(rhs,piv[1])) == rhs, targets++);
  );
  [targets,#columns-rank,rank,#columns];
}

rank_box_scores(n, slopes, constants, points, height, bound) = {
  my(m = sqrtint(n), primeset = primes([2,bound]));
  my(slope = vector(2,i,vector(#points[i],j,slopes[i]+n*points[i][j][2])));
  my(constant = vector(2,i,vector(#points[i],j,constants[i]+n*points[i][j][1])));
  my(left = vector(#points[1],j,Mat(rank_field_marks(n,m,slope[1][j],constant[1][j],height,primeset))));
  my(right = vector(#points[2],j,rank_field_marks(n,m,slope[2][j],constant[2][j],height,primeset)));
  vector(#left,i,vector(#right,j,rank_pair_score(n,left[i],right[j],slope[1][i],constant[1][i],primeset)));
}

check_rank_score() = {
  my(right = Map(), first = [[1,5,2],1], second = [[1,5,3],1]);
  for(i=1,3,mapput(right,i,[]));
  my(spanning = [1,[first]; 2,[second]; 3,[first]]);
  my(unreachable = Mat([1,[first,[[1,5,3],2]]]));
  if(rank_pair_score(77,spanning,right,0,1,[5]) != [1,1,2,3]
     || rank_pair_score(77,unreachable,right,0,1,[5]) != [0,0,1,1], return(0));
  for(i=1,3,mapput(right,i,spanning[i,2]));
  rank_pair_score(77,spanning,right,0,1,[5]) == [0,1,2,3];
}
