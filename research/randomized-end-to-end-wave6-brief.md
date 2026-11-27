# Randomized factoring end-to-end: wave 6

Base: `explore/randomized-one-third` at `2546614`. Read
`research/randomized-end-to-end-status.md`, the wave-3/4/5 briefs, and the files
named in each task.

Wave 6 decomposes the remaining paper leaves. Same constraints: new file only,
no shared edits, no commit, no `sorry`/`admit`/`axiom`/`native_decide`,
`flock /tmp/intfac-lean.lock`, `LEAN_NUM_THREADS=1`,
`PATH="$HOME/.elan/bin:$PATH"`. Each task must produce a compiling reduction to
explicit `Prop`s; do not fake a paper estimate or set a loss to zero.

## W35. L20.2 interior concentration

File `Cogentic/RandomizedL20_2.lean`. Decompose `ConcentrationLeaf` (KB Thm 3.1,
G.8, G.10, App. C, Lemma G.2) into explicit concentration/saddle-point/CRT/
smooth-character inputs and prove the `ConcentrationLeaf` reduction.

## W36. L20.4 conditioned two-point bound

File `Cogentic/RandomizedL20_4.lean`. Decompose the child-root-conditioned
two-point bound (KB G.12; balanced-strip-transfer (2), top-field-pool item 3)
into explicit inputs and prove the `SubexpLeaf` reduction.

## W37. L21.2 RH smooth numbers near centres

File `Cogentic/RandomizedL21_2.lean`. Decompose the RH smooth-numbers-near-
integer-centres estimate (twisted zeta prime sum, Perron at Re s = 2/3, Fourier
L² comparison, tent smoothing) into explicit analytic inputs and prove the
`RatedLeaf`/`ledger` reduction.

## W38. L27.1 Lenstra–Pomerance ECM

File `Cogentic/RandomizedL27_1.lean`. Decompose the ECM failure estimate
(LP Thm 7.1: curves over Z/nZ, gcd exits, Hasse, Deuring/Lenstra counts) into
explicit inputs and prove the `RatedLeaf`/`ledger` reduction.

## W39. L30 genus-two partial factorer

File `Cogentic/RandomizedL30.lean`. Decompose KB Prop. H.3 (genus-two Jacobians,
Cantor arithmetic, LPP order-fibre theorem, Younis short-interval smoothness)
into explicit inputs and prove the `SubexpLeaf` reduction.

## W40. L34 effective Chebotarev

File `Cogentic/RandomizedL34.lean`. Decompose the effective Chebotarev/Stark
input (Lagarias–Odlyzko Thm 1.3, Dedekind zeta zero-free region) into explicit
inputs and prove the `RatedLeaf`/`ledger` reduction.

## W41. L4/L25/L36 form composition

File `Cogentic/RandomizedL4.lean`. Decompose the non-maximal-order form
composition / ideal-squaring / principal-genus bridge into explicit algebraic
inputs and prove the `AlgebraicLeaf`/`PrivateSupplyInputs.realized` reduction.

## W42. P1 prepass

File `Cogentic/RandomizedP1.lean`. Decompose the `exp(o(H))` prepass below
`exp((log n)^{2/3})` into explicit success/cost inputs and prove the `P1Leaf`
reduction. The trial-division cost gap must remain explicit.
