# A smaller factor base for KeyBreak's GRH descent

Keep the field degree, outer private-prime band, and top endpoint from KeyBreak's Appendix G. The factor-base coefficient can decrease from $19/20$ to $3759/4000=0.93975$. This changes the descent cutoff recurrence and its global density bound. The bottom mean uses the rational smoothness loss in its own search region. All estimates refer to the November 26 preprint pinned in the [private-shape analysis](keybreak-private-shape-work.md). [KeyBreak, Appendices G–H](https://crypto.sjtu.edu.cn/factoring.pdf#page=104)

## Integer schedule

Use the paper's $d,t=d\,b(n),\Lambda_d=(\log 2)t$, $e_0$, and $M=\lfloor N^{1/d}\rfloor$. Set
\[
 \beta=\frac{1253}{1000},\quad h_*=\frac{929}{250},\quad
 e_B=\lceil\beta t\rceil,\quad T_H=\lfloor h_*dt\rfloor,
 \qquad a_{\rm den}=\left\lceil\frac{209}{100}t\right\rceil.
\]
Keep $a_A=\lceil36t/25\rceil$, the box exponents $\lceil\alpha e_i+\gamma e_B\rceil$ for $\alpha=51/100$, $\gamma=247/300$, and all Gaussian definitions. Replace the cutoff recurrence by
\[
 e_{i+1}=\max\left(e_B,
       \left\lceil\frac{\alpha e_i+\gamma e_B+T_H/d}{43/10}\right\rceil\right).
\]
The exact recurrence implies $(43/10)d e_{i+1}\ge T_H+\alpha d e_i+\gamma d e_B$, including at the clamp. Its affine slope is $51/430$, and the distance from its fixed point to $e_B$ has a positive leading coefficient because $(89/30)\beta-h_*=37/30000>0$. Thus the cutoffs strictly decrease until the clamp and $j=\log D/(3\log(430/51))+O(1)$ as before. The integer checks in Appendix H are still applied, with these explicit values.

## Geometry, endpoint and progression bounds

The leading ratios in (G.56) are unchanged. In particular $\log_2 M=(64/27+o(1))dt$ and $\log_2(\sigma M)=(1504/405+o(1))dt$, and $h_*>1504/405$. The finite reference-height bound (G.57) therefore holds, with its polynomial factors absorbed by the strict gap. The recurrence gives the same upper algebraic smoothness argument $43d/10$ in (G.26). All endpoint arguments after the root and parent divisions remain between positive constant multiples of $d$.

The internal box conditions in (H.2) follow from
\[
 \log_2(V_i/(2B))\ge e_B/3-1,\qquad
 \log_2(V_i^2/Y_i)\ge5e_B/3.
\]
For an unclamped child the lower leading margin for $\log_2(V_i/Y_{i+1})/t$ is $((22/5)\beta-h_*)/(43/10)>0$. At the clamp it is at least $\beta/3+o(1)$. The internal denominators and child primes thus retain their distinct roles. At the top the limits
\[
 \frac{\log V_0}{\log M}\to\frac{17}{60},\quad
 \frac{\log Y_0}{\log M}\to\frac59,\quad
 \frac{\log Y_1}{\log M}\to\frac{17}{258},\quad
 \frac{\log V_1}{\log M}\to\frac{289}{8600}
\]
are unchanged, since $e_B$ and $T_H/d$ are $O(t)=o(e_0)$. Keep the original lower endpoint $e_{\min}=\lceil127e_0/128\rceil$. This preserves the denominator and parent separation in (G.3), every top geometry check in (H.2), and the private bands in (H.18). It also preserves the Gaussian congruence margin $2(51/100)-3(51/430)>0$ for $Y_1^3/\sigma$ in (H.1). The remaining Gaussian size and startup inequalities hold with the unchanged leading ratios. The raw integer-value check (G.58) has smaller $T_H$ and $e_B$ and still bounds every algebraic value by $\sqrt N$; the rational bound $M V_0/8<N$ is unchanged.

The two $\log M$ coefficients for the smooth-numerator errors (G.12) and (G.17) are unchanged and below $-1/4$. For the internal root average (G.15), the uniform bound for $-\log\rho_i$ is
\[
 \left(\frac{64/27}{3\beta}+o(1)\right)\Lambda_d
       +\left(\frac{\alpha}{3\beta d}+o(1/d)\right)\log Y_i .
\]
Hence the first error decreases with $e_i$, as in (G.13), and the bottom margin $(5/3)\beta-(64/27)/(3\beta)>0$ suffices. The $Y_1/M$ term and the top rational errors (G.18), (G.53) retain their strict negative powers of $M$. Inverse rational densities contribute only $e^{O(\Lambda_d)}$.

The conservative $3.7dt$ lower endpoint and $2.4dt$ upper period estimates in the last part of (G.13) remain valid, using the unchanged limits from (G.56). The first term of (G.38) still has maximum at the bottom, where its leading base-two logarithm divided by $dt$ is
\[
  \frac{237}{320}-\frac{400}{640}\beta=-\frac{17}{400}<-\frac1{25}.
\]
The same check covers $m_r\vartheta$ in (G.9). The additional endpoint factor $4k$ and fixed-power padding still contribute only $O(e_i+e_B)$, below the retained margin. The remaining mesh, radius and proxy terms use the same bounds and $j=O(\log D)$.

## Density, local means and finite search

The success proof needs both a global lower bound on the point density and a separate absolute lower bound on the mean in every search box. The original algebraic density bound $-\log a_P\le(43/30+o(1))\Lambda_d$ remains valid by Lemma G.6 and the unchanged upper smoothness argument. The worst rational density exponent relative to $\Lambda_d$ is the source's internal first-box exponent, with its $\log B$ denominator multiplied by $\beta/(19/15)$. The top rational cofactor uses $M V_0/p$ and remains smaller. Combining both sides gives an exponent bounded strictly below $209/100$:
\[
  \frac{43}{30}+\frac{5926}{12255}\frac{4}{3}\frac{19/15}{\beta}
  <\frac{209}{100}.
\]
Thus $p_A$ and the revised $p_{\rm den}$ satisfy the pointwise and normalized-mean bounds in (G.6).

For an internal box the actual rational loss exponent, using its own upper endpoint $M V_i$, is at most
\[
 \frac{64/27+\alpha e_i/(dt)+\gamma\beta/d}{3\beta}+o(1)
\]
in units $\Lambda_d$. On a rational-good box use its whole-box lower count, the true pointwise algebraic lower bound, and the geometric factor $V_i^2/Y_i$. For a normalized complete semismooth band the same lower bound loses only a logarithmic factor, as in (G.13). The resulting lower exponent for the mean is increasing in $e_i/t$ since $2\alpha-1-\alpha/(3\beta d)>0$ eventually. Its bottom limit exceeds the threshold in Proposition G.10:
\[
 \frac53\beta-\frac{43}{30}-\frac{64/27}{3\beta}>\frac1{50}.
\]
The top mean bounds still have an additional positive leading margin at scale $\log M$. This keeps the concentration hypotheses and the weighted child recursion unchanged, including a clamped last level. The conditional distributions, child incidences and parent masks are the original ones. The revised estimates plug into the proof of Theorem G.1 via (G.6), G.10, G.11 and G.12, using the same field for the counts in every band.

In Appendix H use the revised $p_{\rm den}$ in (H.15) and recalculate all record, sampler and recognition caps from the new integer parameters. The finite sampler comparisons and the confidence calculation use those recalculated counts. The field and square-certificate requirements in H.6 use and bound the actual accepted group and field data. Their factorial scale $\log S^*/\Lambda\to1/2$ is unchanged with $d$ fixed. For the private-shape proof the upper and lower shape exponents are unchanged, and $B$-rough inputs still have $\omega(N)=O(\log N/\log B)=o(\log Y_{\min})$ as required for that lower bound. The stronger $\omega(N)=o(\Lambda)$ needed in the expected launch-count upper bound comes from the separate small-prime pass. No cap is removed to obtain that expected-time saving.

The column, retained-product and height scales in (H.30) now have coefficient $b_*=(3/4)\beta=3759/4000$. On the original private bands, use the [launch loss and fast extraction](keybreak-private-shape-work.md) to obtain the raw-search coefficient $b_*+(3/4)(209/100)=2.50725$ and algebraic-recognition coefficient $b_*+(3/4)(36/25)+\sqrt{76313/322500}<2.507$. Both initial and first-child smoothness-test coefficients per test are unchanged, since the leading logarithms of $Y_0$ and $Y_1$ are unchanged. These transfers concern the original public geometry and its explicit revised bounds. A different private-band algorithm must verify its own launch and recognition costs at this factor base.
