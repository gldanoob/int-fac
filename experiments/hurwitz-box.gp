\\ From the repo root: read("experiments/hurwitz-box.gp"); checkHurwitzBox()
\\ For odd n >= 3, lo and hi are inclusive bounds on the first-coordinate offset.
hurwitzBoxBall(n, lo, hi, offset) = {
  my(A=n^2+1, H=A^2, L=n*A/2, radius2=A*H^2+L^2+offset, count=0);
  for(x=lo, hi,
    my(row=radius2-(n*H+x)^2);
    for(t=0, n,
      my(room=row-(L-t)^2);
      \\ Count all second coordinates in [H-n^2,H] below the spherical boundary.
      if(room >= 0, count += max(0, min(H,sqrtint(room))-(H-n^2)+1))
    )
  );
  count
};

hurwitzBoxShell(n, lo, hi) = {
  my(A=n^2+1);
  hurwitzBoxBall(n,lo,hi,2*A-1) - hurwitzBoxBall(n,lo,hi,A-1)
};

hurwitzBoxForms(n, lo, hi) = {
  my(D=-4*(n^2-1), count=0, b);
  \\ Fix leading coefficient n. Reduction gives c >= n; the slice is 2*lo <= b <= 2*hi < n.
  for(c=n, ((2*hi)^2-D)\(4*n),
    if(issquare(D+4*n*c,&b) && 2*lo <= b && b <= 2*hi && gcd(n,gcd(b,c)) == 1,
      count++)
  );
  count
};

hurwitzBoxSplit(n, slice) = {
  my(lo=2, hi=n\2);
  if(slice(n,lo,hi)%2 == 0, return(0));
  while(lo < hi,
    my(mid=(lo+hi)\2);
    if(slice(n,lo,mid)%2, hi=mid, lo=mid+1)
  );
  gcd(n,lo-1)
};

checkHurwitzBox() = {
  my(moduli=0, splits=0);
  \\ Literal counts on the 6*226*16 box at n=15, either side of a lattice point.
  if([hurwitzBoxBall(15,2,7,226),hurwitzBoxBall(15,2,7,227)] != [15203,15204],
    error("inclusive ball boundary at n=15"));
  forstep(n=3, 105, 2,
    my(expected=2^(omega(n)-1)-1, hi=n\2);
    foreach([hurwitzBoxShell,hurwitzBoxForms], slice,
      for(x=2, hi,
        if(slice(n,x,x) != (x^2%n == 1), error("singleton ",[n,x,slice]))
      );
      if(slice(n,2,hi) != expected, error("whole interval ",[n,slice]));
      my(d=hurwitzBoxSplit(n,slice));
      if(expected == 0,
        if(d != 0, error("unexpected split ",[n,d])),
        if(d <= 1 || d >= n || n%d, error("invalid split ",[n,d]))
      )
    );
    moduli++;
    if(expected, splits++)
  );
  [moduli,splits]
};
