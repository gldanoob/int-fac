# A parity summary does not preserve arithmetic score tests

The arithmetic test class used by the coefficient-word construction cannot in general be evaluated from the parity of the input bits alone, even for one affine norm and one band prime. This rules out the specific compression that replaces a coefficient word by its total parity while claiming exact preservation of every score test. It does not rule out a pseudorandom generator or other restricted-class compression.

Take two bits $x_1,x_2$, the affine norm $n(x)=1+x_1+x_2$, and the allowed prime set $J=\{2\}$. The smoothness indicator accepts exactly the squarefree products of primes in $J$, namely $|n|\in\{1,2\}$. Its truth table is

| word | parity | norm | accepted |
|---|---:|---:|---:|
| 00 | even | 1 | yes |
| 01 | odd | 2 | yes |
| 10 | odd | 2 | yes |
| 11 | even | 3 | no |

The two words in the even parity fiber receive different answers. Therefore no function of total parity alone can agree pointwise with this permitted arithmetic test. Moreover, the uniform acceptance probability is $3/4$, while the uniform distribution on the even-parity support has acceptance probability $1/2$: this support restriction changes the test mean by $1/4$.

This is a finite obstruction to parity-only compression, not an asymptotic lower bound on seed length. It also does not establish that parity compression would fail after cancellation in the full signed score; the claim is only about preserving the individual nonnegative tests used in its expansion.

Run `python3 experiments/cogentic-parity-compression.py` to enumerate the four words and verify both statements.
