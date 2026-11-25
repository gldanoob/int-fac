check()={
my(p=61755930038030462315039402752984735073672860971337787055355211571518104815605241892893104556569868428563998052259059242676947312075227109635399000901084963144580685910731568194230649741871903026924039328774417981912864458041,q=62226733512980887768369397248206084908954125958021064924681219744806942979973966516537282810283149788378181054241387941666106430227419989806927453153345105285127316093685227330794676770230032086699262306710196119183233935249,n=p*q,m=lcm(p^2+p+1,q^2+q+1),counts=matrix(2,4),properbyheight=vector(7),first=vector(7));
for(degree=2,3,
forvec(v=vector(degree,i,[-6,6]),
my(f=x^degree+Polrev(v),power=liftall(Mod(Mod(1,n)*x,f)^m),g=gcd(concat([n],vector(degree-1,i,polcoef(power,i)))),slot=if(g==1,1,if(g==p,2,if(g==q,3,4))));
counts[degree-1,slot]++;
my(proper=g>1&&g<n,expected=0);
if(degree==3&&(v[2]!=0||v[3]!=0),my(a=!#polrootsmod(f,p),b=!#polrootsmod(f,q));expected=a!=b;if(expected&&g!=if(a,p,q),error("orientation",v)));
if(proper!=expected,error("literal model mismatch",degree,v,g));
if(proper,my(h=vecmax(abs(v)));properbyheight[h+1]++;if(!first[h+1],first[h+1]=[g,v]));
));
print(["literal_gcd_counts_1_p_q_N",counts]);print(["proper_by_exact_height",properbyheight]);print(["first_proper_at_height",first]);
if(sum(i=1,2,sum(j=1,4,counts[i,j]))!=2366,error("count"));
};
iferr(check(),E,print(E);quit(1));
