# Reusable smooth padding for the deterministic mean factorer

After removing small prime factors from the input, a single known smooth multiplier can send every remaining input of a bounded size to the fast path of the deterministic mean factorer. A polynomial-time randomized choice of the multiplier has exponentially small probability of failing on any input of that size. A nonuniform choice takes $O(V_b)$ bits of advice. The smoothness cutoffs below are sharp in the model that gives only a bound on the number of exceptional integers. [Deterministic mean factorer](cogentic-universal-score-sampler.md) · [Prime padding for raw inputs](cogentic-exceptional-multipliers.md)

## Removing small primes makes the multiplier unique

Write $H_b=b^{1/3}(\log(2b))^{2/3}$ and $V_b=b^{2/3}(\log(2b))^{1/3}$. All logarithms are natural except $\log_2$. Fix a complete factorer and a fast time threshold $\exp(AH_t)$ on $t$-bit inputs. Assume the inputs exceeding that threshold form a set $E_t$ of size at most $\exp(CV_t)$ for a fixed $C>0$. Enlarge the constants to cover bounded sizes if needed.

Fix an input size bound $b$ and a public smoothness cutoff $Y=b^{O(1)}$. Sieve the primes up to $Y$, remove their powers from $N<2^b$, and call the remaining cofactor $R$. The sieve and removal cost polynomial time in $b$. If $R=1$, the removed primes give the complete factorization. Otherwise choose a positive $Y$-smooth multiplier $q$ with a known factorization, and factor $M=qR$. From the complete factorization of $M$, discard its primes at most $Y$ and restore the small prime powers removed from $N$.

For every such $M$, the $Y$-smooth part
\[
 \prod_{p\le Y}p^{v_p(M)}
\]
is exactly $q$, independently of the bit length of $R$. Thus each exceptional $M$ rules out at most one label $q$ for simultaneous success on all $Y$-rough cofactors $1<R<2^b$. This holds even if the original $N$ has primes in common with $q$.

Suppose the padding adds at most $s_b=o(b)$ bits. The trial inputs have lengths $1\le t\le b+s_b+1$, including when the sieve leaves a much shorter cofactor. The bound on the number of bad labels is
\[
 \sum_{t\le b+s_b+1}|E_t|
 \le (b+s_b+1)\exp(CV_{b+s_b+1})
 =\exp((C+o(1))V_b).
\]
In particular, a uniform draw from an explicitly indexed label set of size at least $\exp((C+\delta)V_b)$ for a fixed $\delta>0$ gives a multiplier that works for every $N<2^b$ with probability $1-\exp(-(\delta-o(1))V_b)$. Factoring with that multiplier takes $\exp(O(H_b))$ bit operations per input, including the sieve and complete verification.

## Cutoff of order $V_b$ with sublinear padding

Take $Y=\gamma V_b$ for a fixed $\gamma>0$, and let $n=\pi(Y)$. Set $s_b=\lfloor b/\log(2b)\rfloor$ and use the labels
\[
 q=\prod_{p\le Y}p^{e_p},\qquad
 0\le e_p\le w=\left\lfloor\frac{s_b}{n\log_2 Y}\right\rfloor .
\]
Every label is at most $2^{s_b}$ and the exponent vectors are its exact factorizations. The prime number theorem gives $n\sim\gamma V_b/\log(\gamma V_b)$, and $\log(w+1)=(1/3+o(1))\log b$. Consequently the number of labels is
\[
 (w+1)^n=\exp((\gamma/2+o(1))V_b).
\]
For $\gamma>2C$ this produces the required universal multiplier. A uniformly random index in the exponent box costs $O(V_b)$ expected fair bits and polynomial bit operations. A good index can also be fixed as $O(V_b)$ bits of advice for the entire range $N<2^b$.

For the converse count, even allowing all $Y$-smooth labels up to $2^{Db}$ for any fixed $D>0$, there are only $\exp((\gamma/2+o(1))V_b)$ labels when $Y=\gamma V_b$. The exponent vectors for primes at most $Y/(\log b)^2$ contribute at most $O(Y/\log b)=o(V_b)$ to the log count: each exponent is at most $Db$, and there are at most $Y/(\log b)^2$ such primes. For the other primes, $\log p=(2/3+o(1))\log b$ uniformly, so their exponents sum to at most $L=O_D(b/\log b)$. There are at most $\binom{n+L}{n}$ choices after rounding $L$ to an integer, and
\[
 \log\binom{n+L}{n}\le n\log\bigl(e(1+L/n)\bigr)
       \le(\gamma/2+o(1))V_b .
\]
The exponent box gives the matching lower count and fits within $2^{Db}$ for every fixed $D>0$ for large $b$. In particular $Y=o(V_b)$ gives only $\exp(o(V_b))$ labels within any such padding bound.

## Cutoff with padding of $O(V_b)$ bits

Measure the short padding budget by $\log q\le D V_b$ with a fixed $D>0$, and take $Y=b^\alpha$. For a fixed $\alpha>2/3$, choose $k=\lfloor D V_b/\log Y\rfloor$ distinct primes in $(Y/2,Y]$ and take their product. The prime number theorem gives $n\sim Y/(2\log Y)$ choices of primes, and
\[
 \log\binom nk
 \ge k\log(n/k)
 =\left(D\left(1-\frac{2}{3\alpha}\right)+o(1)\right)V_b .
\]
Subsets can be sampled uniformly by choosing an index and recovering its ordered prime indices with binomial counts. This uses $O(V_b)$ expected fair bits and polynomial bit operations. Whenever $D(1-2/(3\alpha))>C$, the resulting padding works simultaneously for all inputs below $2^b$ with the same exponential success estimate.

Allowing prime powers cannot improve the leading log count for this budget. For any fixed $0<\lambda<1$,
\[
 \#\{q\le e^{D V_b}:q\text{ is }Y\text{-smooth}\}
 \le e^{\lambda D V_b}\prod_{p\le Y}(1-p^{-\lambda})^{-1}.
\]
The log of the product is $O_\lambda(Y^{1-\lambda})$, by comparison with the sum of $j^{-\lambda}$ over integers $2\le j\le Y$. For $\alpha>2/3$, take any fixed $\lambda>1-2/(3\alpha)$ and let it decrease to that threshold after taking the upper limit in $b$. The leading coefficient is at most $D(1-2/(3\alpha))$, matching the squarefree count. For $Y\le b^{2/3+o(1)}$ every fixed $\lambda>0$ makes the product contribution $o(V_b)$, so the count is only $\exp(o(V_b))$.

## Scope of the lower bounds

Whenever the set of admissible labels has log cardinality at most $(C-\delta)V_b$ for a fixed $\delta>0$, fix one $b$-bit $Y$-rough semiprime $R_b$ and declare all its padded values $qR_b$ exceptional. Such semiprimes exist for large $b$ by taking both primes in a fixed multiplicative interval around $2^{(b-1)/2}$ whose products lie in $[2^{b-1},2^b)$. Every padded value has at least $b$ bits, so each output length still satisfies the stipulated exception bound. This also works simultaneously for all sufficiently large $b$: at a given length $t$, there are at most $t$ contributing input lengths $b\le t$, and $t\exp((C-\delta)V_t)\le\exp(CV_t)$ eventually. The obstruction applies to any selection among the admissible labels, including a choice that depends on the input or on prior timeouts.

The lower bounds concern what follows from the cardinalities alone. With random padding, a timeout on an individual input can trigger a fresh independent draw, giving expected time $\exp(O(H_b))$ and an always verified result. A supplied good index gives a deterministic per-input bound. Uniform deterministic selection at that cost still requires a way to hit the fast inputs of the actual factorer.
