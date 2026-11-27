import Cogentic.RandomizedL20_4

/-!
# L20.4 sub-lemmas: the elementary half of the child-root-conditioned top step

`Cogentic.RandomizedL20_4` packages the KeyBreak G.12 top step under the
incoming-child-root law into the structures `ChildRootPairInputs`,
`G12TopInputs`, `DyadExceptionInputs` and `L20_4Inputs`.  Those structures mix
two layers: genuinely paper-level conditioning/concentration estimates, and
elementary probabilistic/numerical arithmetic.  This file separates the layers.

The paper-level estimates are kept as explicit `Prop`s:

* `ConditionedTwoPoint` --- pool-note item 3 / KB (G.53)--(G.55): the second
  moment of the normalized top height in the law conditioned on
  `g ∧ R_{q,s}` is at most `D ^ c`.  This is the statement that the
  *unconditioned* two-point bound does not imply.
* `ConditionedMeanLower` --- pool-note item 1 / balanced-strip-transfer (2):
  after normalization the conditioned first moment is at least the fixed
  `a > 0`.  The manuscript obtains this by comparing with the tested strip's
  own mean; the polynomial factors are absorbed into `Z`.
* `InteriorConcentration` --- pool-note item 2 plus L21.2: the G.11 internal
  base mass `δ_L`, the elliptic deletion fraction `η`, the G.11 rational error
  `ε_rat` and the incoming exceptional mass `ε_in` are each `D^{-B}` for every
  `B`.  This is the genuinely paper-level interior concentration input.
* `TopG12Comparison` (from `RandomizedL20_4`) --- the KeyBreak G.12 top
  square-root comparison.  It is retained as the explicit `Prop` of the parent
  file and is used only in the square-root propagation step.

Everything else is proved here, without touching the paper-level analysis:

1. **Conditioned Paley--Zygmund hit probability.**  The conditioned first and
   second moment bounds give the conditional hit probability
   `Pr(Z ≥ a/2 | g,R) ≥ a²/(4M)`; with `M ≤ D^{c}` and `D^{-1} ≤ a²/4` this is
   `≥ D^{-(c+1)}` (`PairData.hitProb_ge_exp`).
2. **Pool union bound.**  `K` independent draws with hit probability `q` miss
   with probability `(1-q)^K ≤ exp(-qK)`; with `q ≥ D^{-(c+1)}` and
   `K ≥ D^{c+c_d+2}` the miss mass `|J|(1-q)^K` is `D^{-B}` for every `B`
   (`PairData.poolLoss_subexp`).  The dyad factor, `q` and `K` stay explicit.
3. **Dyad Markov fraction.**  The deterministic fraction of the dyad on which
   the per-prime bad mass exceeds `D^{-1}` is at most the dyad average divided
   by `D^{-1}`, hence `D^{-B}` whenever the average is
   (`DyadData.loss_subexp`).
4. **G.11/G.12 propagation.**  The G.11 linear recurrence gives
   `δ_0 ≤ C^L (δ_L + L(η+ε_rat))`; the subexponential base and errors give
   `δ_0 ≤ D^{-T}`; the G.12 square-root comparison then gives the top mass
   `D^{-B}` (`TopData.top_subexp`).  The `D^{O(1)}` depth and top constants
   remain explicit.
5. **The reduction.**  `L20_4SubInputs.loss` is the sum of the three elementary
   deficits, and `L20_4SubInputs.subexpLoss` derives `D^{-B}` for every `B`.
   `L20_4SubInputs.toPaper` shows the finer inputs realize the parent
   `L20_4Inputs`, so this is a genuine refinement rather than a parallel
   assumption set.

No `sorry`, `admit`, `axiom` or `native_decide`.  No loss is set to zero: the
pool size, dyad factor, elliptic fraction, rational errors and incoming
exception are all explicit nonnegative quantities.
-/

namespace Cogentic.RandomizedL20_4Sub

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedL20_4

/-! ## 0. The paper-level `Prop`s -/

/-- **Pool-note item 3 / KB (G.53)--(G.55), conditioned two-point bound.**
In the law conditioned on `E n` (the event `g ∧ R_{q,s}`), the second moment of
the normalized top height `Z` is at most `D^c` for every large scale.  This is
the conditioned statement; the unconditioned bound does not imply it. -/
def ConditionedTwoPoint {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (E : ℕ → Ω → Prop) (Z : ℕ → Ω → ℝ) (c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    condExpect (μ n) (E n) (fun ω => Z n ω ^ 2) ≤ Real.exp (c * scale n)

/-- **Pool-note item 1 / balanced-strip-transfer (2), conditioned mean lower
bound.**  After normalization by the deterministic strip mean, the conditioned
first moment of the top height on `g ∧ R_{q,s}` is at least the fixed `a > 0`. -/
def ConditionedMeanLower {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (E : ℕ → Ω → Prop) (Z : ℕ → Ω → ℝ) (a : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, a ≤ condExpect (μ n) (E n) (Z n)

/-- **Pool-note item 2 and L21.2, interior concentration.**  The G.11 internal
base mass `δ_L`, the elliptic deletion fraction `η`, the G.11 rational error
`ε_rat` and the incoming exceptional mass `ε_in` are each `D^{-B}` for every
`B > 0`. -/
def InteriorConcentration (interior : ℕ → ℕ → ℝ) (L : ℕ)
    (eta epsRat epsIn : ℕ → ℝ) : Prop :=
  SubexpLoss (fun n => interior n L) ∧ SubexpLoss eta ∧
    SubexpLoss epsRat ∧ SubexpLoss epsIn

/-! ## 1. Conditioned Paley--Zygmund and the per-draw hit probability -/

/-- The per-draw conditional hit probability of one pool draw:
`Pr(g ∧ R_{q,s} ∧ Z ≥ a/2) / Pr(g ∧ R_{q,s})`. -/
noncomputable def hitProb {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (E : ℕ → Ω → Prop) (Z : ℕ → Ω → ℝ) (a : ℝ) (n : ℕ) : ℝ :=
  pmfProb (μ n) (fun ω => E n ω ∧ a / 2 ≤ Z n ω) / pmfProb (μ n) (E n)

/-- The conditional hit probability never exceeds one. -/
theorem hitProb_le_one {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (E : ℕ → Ω → Prop) (Z : ℕ → Ω → ℝ) (a : ℝ) (n : ℕ)
    (hpos : 0 < pmfProb (μ n) (E n)) : hitProb μ E Z a n ≤ 1 := by
  unfold hitProb
  rw [div_le_one hpos]
  exact pmfProb_mono (μ n) (fun ω hω => hω.1)

/-- **Conditioned Paley--Zygmund, exponential form.**  If the conditioned mean
of `Z` is at least `a > 0` and the conditioned second moment is at most
`M ≤ D^c`, and `D^{-1} ≤ a²/4`, then the conditional hit probability is at
least `D^{-(c+1)}`.  This is exactly the step that converts the polynomial
constant of item 3 into a polynomial success probability. -/
theorem hitProb_ge_exp {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (E : ℕ → Ω → Prop) (Z : ℕ → Ω → ℝ) {a c : ℝ} (ha : 0 < a)
    (hpos : ∀ n, 0 < pmfProb (μ n) (E n))
    (hmean : ConditionedMeanLower μ E Z a)
    (hpair : ConditionedTwoPoint μ E Z c) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-(c + 1) * scale n) ≤ hitProb μ E Z a n := by
  filter_upwards [Eventually.of_forall hpos, hmean, hpair,
    scale_grows.eventually_ge_atTop (Real.log (4 / a ^ 2) + 1)] with n hhpos hmean' hpair' hbig
  have hlog : Real.log (4 / a ^ 2) ≤ scale n := by linarith
  have hfac : Real.exp (-scale n) ≤ a ^ 2 / 4 := by
    calc Real.exp (-scale n) ≤ Real.exp (-(Real.log (4 / a ^ 2))) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = a ^ 2 / 4 := by
          rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) (pow_pos ha 2))]
          field_simp
  have hMpos : (0 : ℝ) < Real.exp (c * scale n) := Real.exp_pos _
  have hpz := cond_paley_zygmund (μ n) (E n) (Z n) hhpos ha hMpos hmean' hpair'
  have hexp : a ^ 2 / (4 * Real.exp (c * scale n)) =
      a ^ 2 / 4 * Real.exp (-(c * scale n)) := by
    rw [Real.exp_neg]
    field_simp
  have hmul := mul_le_mul_of_nonneg_right hfac (Real.exp_pos (-(c * scale n))).le
  have hprod : Real.exp (-(c + 1) * scale n) =
      Real.exp (-scale n) * Real.exp (-(c * scale n)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc Real.exp (-(c + 1) * scale n)
      = Real.exp (-scale n) * Real.exp (-(c * scale n)) := hprod
    _ ≤ a ^ 2 / 4 * Real.exp (-(c * scale n)) := hmul
    _ = a ^ 2 / (4 * Real.exp (c * scale n)) := hexp.symm
    _ ≤ hitProb μ E Z a n := hpz

/-! ## 2. The pool union bound -/

/-- The pool miss mass: all `|J|` dyad primes miss `K` independent public draws,
`|J| · (1 - q)^K`. -/
noncomputable def poolLoss {Ω : Type*} [Fintype Ω] (dyadCard : ℕ → ℕ)
    (μ : ℕ → PMF Ω) (E : ℕ → Ω → Prop) (Z : ℕ → Ω → ℝ) (a : ℝ)
    (poolSize : ℕ → ℕ) (n : ℕ) : ℝ :=
  (dyadCard n : ℝ) * (1 - hitProb μ E Z a n) ^ poolSize n

/-- **The pool union bound is `D^{-B}` for every `B`.**  With per-draw hit
probability `q ≥ D^{-(c+1)}`, dyad cardinality `|J| ≤ D^{c_d}` and pool size
`K ≥ D^{c+c_d+2}`, the miss mass is at most
`D^{c_d} exp(-D)`, which is `≤ D^{-B}` once `(B+c_d) H ≤ exp H`.  The dyad
factor, `q` and `K` are all kept explicit. -/
theorem poolLoss_subexp {Ω : Type*} [Fintype Ω] (dyadCard : ℕ → ℕ)
    (μ : ℕ → PMF Ω) (E : ℕ → Ω → Prop) (Z : ℕ → Ω → ℝ) {a c cDyad : ℝ}
    (ha : 0 < a) (hpos : ∀ n, 0 < pmfProb (μ n) (E n))
    (hmean : ConditionedMeanLower μ E Z a)
    (hpair : ConditionedTwoPoint μ E Z c)
    (hcDyad : 0 ≤ cDyad)
    (hcard : ∀ᶠ n : ℕ in atTop,
      (dyadCard n : ℝ) ≤ Real.exp (cDyad * scale n))
    (poolSize : ℕ → ℕ)
    (hpool : ∀ᶠ n : ℕ in atTop,
      Real.exp ((c + cDyad + 2) * scale n) ≤ (poolSize n : ℝ)) :
    SubexpLoss (poolLoss dyadCard μ E Z a poolSize) := by
  intro B hB
  have hq := hitProb_ge_exp μ E Z ha hpos hmean hpair
  filter_upwards [hq, hcard, hpool, scale_grows.eventually_ge_atTop 0,
    scale_grows.eventually (eventually_mul_le_exp (B + cDyad))] with n hq' hcard' hK hH0 hdom
  have hH : 0 ≤ scale n := hH0
  have hq0 : 0 ≤ hitProb μ E Z a n := (Real.exp_pos _).le.trans hq'
  have hq1 : hitProb μ E Z a n ≤ 1 := hitProb_le_one μ E Z a n (hpos n)
  have hqK : Real.exp (scale n) ≤ hitProb μ E Z a n * (poolSize n : ℝ) := by
    have hmul := mul_le_mul hq' hK (Real.exp_pos _).le hq0
    have hprod : Real.exp (-(c + 1) * scale n) *
        Real.exp ((c + cDyad + 2) * scale n) =
        Real.exp ((cDyad + 1) * scale n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hle : Real.exp (scale n) ≤ Real.exp ((cDyad + 1) * scale n) :=
      Real.exp_le_exp.mpr (by nlinarith [hcDyad, hH])
    calc Real.exp (scale n) ≤ Real.exp ((cDyad + 1) * scale n) := hle
      _ = Real.exp (-(c + 1) * scale n) *
            Real.exp ((c + cDyad + 2) * scale n) := hprod.symm
      _ ≤ hitProb μ E Z a n * (poolSize n : ℝ) := hmul
  have hmiss : (1 - hitProb μ E Z a n) ^ poolSize n ≤
      Real.exp (-Real.exp (scale n)) := by
    have h1 := one_sub_pow_le_exp_neg_mul hq1 (poolSize n)
    exact h1.trans (Real.exp_le_exp.mpr (by linarith [hqK]))
  have hprod := mul_le_mul hcard' hmiss
    (pow_nonneg (sub_nonneg.mpr hq1) _) (Real.exp_pos _).le
  have hcombine : Real.exp (cDyad * scale n) * Real.exp (-Real.exp (scale n)) ≤
      Real.exp (-B * scale n) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : (B + cDyad) * scale n ≤ Real.exp (scale n) := hdom
    linarith
  exact hprod.trans hcombine

/-! ## 3. Deterministic dyad trimming (Markov across the dyad) -/

/-- The deterministic exceptional set of the dyad at scale `n`, with threshold
`D^{-1}` and no bad-child component (`err_bad = 0`). -/
noncomputable def badSet {P : Type*} [DecidableEq P] (dyad : ℕ → Finset P)
    (err : ℕ → P → ℝ) (n : ℕ) : Finset P :=
  badDyadPrimes (dyad n) (err n) (fun _ => 0) (Real.exp (-(1 : ℝ) * scale n)) 1

/-- The fraction of the dyad removed by the Markov trimming. -/
noncomputable def dyadLoss {P : Type*} [DecidableEq P] (dyad : ℕ → Finset P)
    (err : ℕ → P → ℝ) (n : ℕ) : ℝ :=
  ((badSet dyad err n).card : ℝ) / ((dyad n).card : ℝ)

theorem dyadLoss_nonneg {P : Type*} [DecidableEq P] (dyad : ℕ → Finset P)
    (err : ℕ → P → ℝ) (n : ℕ) : 0 ≤ dyadLoss dyad err n :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- **The dyad Markov fraction is `D^{-B}`.**  If the per-prime bad mass is
nonnegative and its dyad average is `D^{-B'}` for every `B'`, then the fraction
of the dyad on which it exceeds `D^{-1}` is at most the average divided by
`D^{-1}`, i.e. `D^{-B'}/D^{-1} = D^{-(B'-1)}`.  Taking `B' = B+1` gives
`D^{-B}`. -/
theorem dyadLoss_subexp {P : Type*} [DecidableEq P] (dyad : ℕ → Finset P)
    (err : ℕ → P → ℝ) (herr : ∀ n p, 0 ≤ err n p) (avg : ℕ → ℝ)
    (havg_def : ∀ n, avg n = (∑ p ∈ dyad n, err n p) / ((dyad n).card : ℝ))
    (havg : SubexpLoss avg) :
    SubexpLoss (dyadLoss dyad err) := by
  intro B hB
  filter_upwards [havg (B + 1) (by linarith)] with n havg'
  have hθ : 0 < Real.exp (-(1 : ℝ) * scale n) := Real.exp_pos _
  have hsum : ∑ p ∈ dyad n, err n p ≤ Real.exp (-(B + 1) * scale n) *
      ((dyad n).card : ℝ) := by
    have hdiv : (∑ p ∈ dyad n, err n p) / ((dyad n).card : ℝ) ≤
        Real.exp (-(B + 1) * scale n) := by
      rwa [havg_def n] at havg'
    exact sum_le_mul_card_of_div_le (dyad n) (err n) hdiv
  have hcard := badDyadPrimes_card_le (dyad n) (err n) (fun _ => 0)
    (δ_rat := Real.exp (-(B + 1) * scale n)) (δ_bad := 0)
    (θ_rat := Real.exp (-(1 : ℝ) * scale n)) (θ_bad := 1)
    hθ (by norm_num) (fun p _ => herr n p) (fun p _ => le_refl 0) hsum
    (by simp)
  have hratio : Real.exp (-(B + 1) * scale n) / Real.exp (-(1 : ℝ) * scale n) =
      Real.exp (-B * scale n) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hb : ((badSet dyad err n).card : ℝ) ≤
      Real.exp (-B * scale n) * ((dyad n).card : ℝ) := by
    calc ((badSet dyad err n).card : ℝ)
        ≤ (Real.exp (-(B + 1) * scale n) / Real.exp (-(1 : ℝ) * scale n) + 0 / 1) *
            ((dyad n).card : ℝ) := hcard
      _ = Real.exp (-B * scale n) * ((dyad n).card : ℝ) := by
          rw [hratio]
          norm_num
  unfold dyadLoss
  by_cases hz : (dyad n).card = 0
  · simp only [hz, Nat.cast_zero, div_zero]
    positivity
  · have hpos : (0 : ℝ) < ((dyad n).card : ℝ) :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz)
    rw [div_le_iff₀ hpos]
    linarith [hb]

/-! ## 4. G.11 propagation and the G.12 square-root step -/

/-- **G.11 propagation, subexponential form.**  A subexponential base mass
`δ_L ≤ exp (-A H)`, subexponential internal errors `η + ε_rat ≤ exp (-A H)`, a
depth factor `C^L ≤ exp (c_int H)` and `(L+1) ≤ exp H` give
`δ_0 ≤ exp (-T H)` as soon as `T + c_int + 1 ≤ A`.  This is
`interior_zero_le_exp` restated without any structure fields. -/
theorem interior_zero_subexp {L : ℕ} {δ : ℕ → ℝ} {Cstep eta eps T cInt A H : ℝ}
    (heta : 0 ≤ eta) (heps : 0 ≤ eps) (hC : 1 ≤ Cstep) (hH : 0 ≤ H)
    (hL : (L : ℝ) + 1 ≤ Real.exp H)
    (hrec : ∀ i < L, δ i ≤ Cstep * (δ (i + 1) + eta + eps))
    (hstep : Cstep ^ L ≤ Real.exp (cInt * H))
    (hbase : δ L ≤ Real.exp (-A * H))
    (halpha : eta + eps ≤ Real.exp (-A * H))
    (hA : T + cInt + 1 ≤ A) :
    δ 0 ≤ Real.exp (-T * H) :=
  interior_zero_le_exp heta heps hC hH hL hrec hstep hbase halpha hA

/-- **G.12 square-root step, subexponential form.**  A top comparison
`δ_top ≤ C (√δ_0 + √ε_in + η)` with `C ≤ exp (c_top H)`, interior and incoming
masses at most `exp (-2(B+c_top+1) H)` and elliptic fraction at most
`exp (-(B+c_top+1) H)` give `δ_top ≤ exp (-B H)`. -/
theorem top_le_exp_neg_subexp {δtop C intMass inMass eta B cTop H : ℝ}
    (hB : 0 < B) (hH : 0 ≤ H) (hH3 : Real.log 3 ≤ H)
    (hint_nn : 0 ≤ intMass) (hin_nn : 0 ≤ inMass) (heta_nn : 0 ≤ eta)
    (hC : C ≤ Real.exp (cTop * H))
    (hint : intMass ≤ Real.exp (-(2 * (B + cTop + 1)) * H))
    (hin : inMass ≤ Real.exp (-(2 * (B + cTop + 1)) * H))
    (hell : eta ≤ Real.exp (-(B + cTop + 1) * H))
    (htop : δtop ≤ C * (Real.sqrt intMass + Real.sqrt inMass + eta)) :
    δtop ≤ Real.exp (-B * H) :=
  top_le_exp_neg hB hH hH3 hint_nn hin_nn heta_nn hC hint hin hell htop

/-- **The G.12 top mass is a subexponential loss.**  Given the G.11 recurrence,
the depth/top `D^{O(1)}` bounds, the G.12 comparison and the interior
concentration `Prop`, the top bad-child mass is `D^{-B}` for every `B`.  This is
the paper's G.12 conclusion with the paper-level concentration input isolated. -/
theorem top_subexp_of_concentration {L : ℕ} (interior : ℕ → ℕ → ℝ)
    (step eta epsRat epsIn top Ctop : ℕ → ℝ) (cTop cInt : ℝ)
    (interior_nonneg : ∀ n i, 0 ≤ interior n i)
    (eta_nonneg : ∀ n, 0 ≤ eta n)
    (epsRat_nonneg : ∀ n, 0 ≤ epsRat n)
    (epsIn_nonneg : ∀ n, 0 ≤ epsIn n)
    (_top_nonneg : ∀ n, 0 ≤ top n)
    (_Ctop_nonneg : ∀ n, 0 ≤ Ctop n)
    (cTop_nonneg : 0 ≤ cTop)
    (recurrence : G11InteriorRecurrence interior L step eta epsRat)
    (step_ge_one : ∀ᶠ n : ℕ in atTop, 1 ≤ step n)
    (alpha_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ eta n + epsRat n)
    (depth_bound : ∀ᶠ n : ℕ in atTop,
      step n ^ L * ((L : ℝ) + 1) ≤ Real.exp (cInt * scale n))
    (comparison : TopG12Comparison top Ctop interior epsIn eta)
    (Ctop_le : ∀ᶠ n : ℕ in atTop, Ctop n ≤ Real.exp (cTop * scale n))
    (concentration : InteriorConcentration interior L eta epsRat epsIn) :
    SubexpLoss top := by
  obtain ⟨hbase_sub, heta_sub, hrat_sub, hin_sub⟩ := concentration
  intro B hB
  let T : ℝ := 2 * (B + cTop + 1)
  have hTpos : 0 < T := by dsimp [T]; nlinarith [hB, cTop_nonneg]
  let A : ℝ := max (T + cInt + 1) 1
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hAT : T + cInt + 1 ≤ A := le_max_left _ _
  have hcpos : 0 < B + cTop + 1 := by linarith [hB, cTop_nonneg]
  filter_upwards [step_ge_one, alpha_nonneg, recurrence, comparison,
    Ctop_le, depth_bound, hbase_sub A hApos,
    subexpLoss_add heta_sub hrat_sub A hApos,
    heta_sub (B + cTop + 1) hcpos, hin_sub T hTpos,
    scale_grows.eventually_ge_atTop 0,
    scale_grows.eventually_ge_atTop
      (max (Real.log 3) (Real.log ((L : ℝ) + 1) + 1))]
    with n hstep hα hrec hcmp hC hdepth hbase halpha heta hin hH0 hHbig
  have hH : 0 ≤ scale n := hH0
  have hH3 : Real.log 3 ≤ scale n := le_trans (le_max_left _ _) hHbig
  have hHL : (L : ℝ) + 1 ≤ Real.exp (scale n) := by
    have hlog : Real.log ((L : ℝ) + 1) ≤ scale n := by
      have hle : Real.log ((L : ℝ) + 1) + 1 ≤
          max (Real.log 3) (Real.log ((L : ℝ) + 1) + 1) := le_max_right _ _
      linarith
    calc (L : ℝ) + 1 = Real.exp (Real.log ((L : ℝ) + 1)) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (scale n) := Real.exp_le_exp.mpr hlog
  have hstepL : step n ^ L ≤ Real.exp (cInt * scale n) := by
    have hfac : step n ^ L ≤ step n ^ L * ((L : ℝ) + 1) := by
      have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
      have h1 : (1 : ℝ) ≤ (L : ℝ) + 1 := by linarith
      nlinarith [pow_nonneg (show 0 ≤ step n by linarith) L]
    exact hfac.trans hdepth
  have hint0 : interior n 0 ≤ Real.exp (-T * scale n) :=
    interior_zero_subexp (δ := interior n) (Cstep := step n) (eta := eta n)
      (eps := epsRat n) (T := T) (cInt := cInt) (A := A) (H := scale n)
      (eta_nonneg n) (epsRat_nonneg n) hstep hH hHL hrec hstepL hbase halpha hAT
  exact top_le_exp_neg_subexp (δtop := top n) (C := Ctop n) (intMass := interior n 0)
    (inMass := epsIn n) (eta := eta n) (B := B) (cTop := cTop) (H := scale n)
    hB hH hH3 (interior_nonneg n 0) (epsIn_nonneg n) (eta_nonneg n)
    hC (by simpa [T] using hint0) hin heta hcmp

/-! ## 5. The finer input structures -/

/-- The explicit child-root pair data, with only the two conditioned moment
statements kept as hypotheses `two_point` and `mean_lower`. -/
structure PairData (Ω : Type*) [Fintype Ω] where
  /-- The field/trial law. -/
  μ : ℕ → PMF Ω
  /-- Rational-good environments. -/
  good : ℕ → Ω → Prop
  /-- The prescribed child root event `R_{q,s}`. -/
  childRoot : ℕ → Ω → Prop
  /-- The normalized top height `H^det_{0,J}/B₁(q)`. -/
  Z : ℕ → Ω → ℝ
  /-- The fixed Paley--Zygmund mean constant. -/
  a : ℝ
  a_pos : 0 < a
  /-- Exponent of the conditioned two-point constant. -/
  cPair : ℝ
  cPair_nonneg : 0 ≤ cPair
  /-- Exponent of the dyad cardinality. -/
  cDyad : ℝ
  cDyad_nonneg : 0 ≤ cDyad
  dyadCard : ℕ → ℕ
  dyadCard_le : ∀ᶠ n : ℕ in atTop,
    (dyadCard n : ℝ) ≤ Real.exp (cDyad * scale n)
  poolSize : ℕ → ℕ
  poolSize_ge : ∀ᶠ n : ℕ in atTop,
    Real.exp ((cPair + cDyad + 2) * scale n) ≤ (poolSize n : ℝ)
  event_pos : ∀ n, 0 < pmfProb (μ n) (pairEvent good childRoot n)
  /-- The paper-level conditioned mean lower bound. -/
  mean_lower : ConditionedMeanLower μ (fun n => pairEvent good childRoot n) Z a
  /-- The paper-level conditioned two-point bound. -/
  two_point : ConditionedTwoPoint μ (fun n => pairEvent good childRoot n) Z cPair

namespace PairData

variable {Ω : Type*} [Fintype Ω]

/-- The conditional hit probability of one pool draw. -/
noncomputable def hit (S : PairData Ω) (n : ℕ) : ℝ :=
  hitProb S.μ (fun m => pairEvent S.good S.childRoot m) S.Z S.a n

/-- The pool miss mass of the dyad. -/
noncomputable def loss (S : PairData Ω) (n : ℕ) : ℝ :=
  poolLoss S.dyadCard S.μ (fun m => pairEvent S.good S.childRoot m) S.Z S.a S.poolSize n

theorem hit_le_one (S : PairData Ω) (n : ℕ) : S.hit n ≤ 1 :=
  hitProb_le_one S.μ _ S.Z S.a n (S.event_pos n)

theorem loss_nonneg (S : PairData Ω) (n : ℕ) : 0 ≤ S.loss n :=
  mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sub_nonneg.mpr (S.hit_le_one n)) _)

/-- The conditioned hit probability is `D^{-(c+1)}`. -/
theorem hit_ge_exp (S : PairData Ω) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-(S.cPair + 1) * scale n) ≤ S.hit n :=
  hitProb_ge_exp S.μ _ S.Z S.a_pos S.event_pos S.mean_lower S.two_point

/-- The pool union bound is a subexponential loss. -/
theorem loss_subexp (S : PairData Ω) : SubexpLoss S.loss :=
  poolLoss_subexp S.dyadCard S.μ _ S.Z S.a_pos S.event_pos S.mean_lower S.two_point
    S.cDyad_nonneg S.dyadCard_le S.poolSize S.poolSize_ge

/-- The finer pair data realize the parent `ChildRootPairInputs`. -/
noncomputable def toPaper (S : PairData Ω) : ChildRootPairInputs Ω where
  μ := S.μ
  good := S.good
  childRoot := S.childRoot
  Z := S.Z
  a := S.a
  a_pos := S.a_pos
  cPair := S.cPair
  cPair_nonneg := S.cPair_nonneg
  cDyad := S.cDyad
  cDyad_nonneg := S.cDyad_nonneg
  dyadCard := S.dyadCard
  dyadCard_le := S.dyadCard_le
  poolSize := S.poolSize
  poolSize_ge := S.poolSize_ge
  event_pos := S.event_pos
  mean_lower := by simpa [ConditionedMeanLower, IncomingGoodMeanLower] using S.mean_lower
  pair_bound := by
    simpa [ConditionedTwoPoint, ChildRootConditionedTwoPoint] using S.two_point

end PairData

/-- The explicit dyad data, with the average bound (pool-note item 1, last
sentence) kept as a `SubexpLoss` hypothesis. -/
structure DyadData (P : Type*) [DecidableEq P] where
  dyad : ℕ → Finset P
  err : ℕ → P → ℝ
  err_nonneg : ∀ n p, 0 ≤ err n p
  avg : ℕ → ℝ
  avg_def : ∀ n, avg n = (∑ p ∈ dyad n, err n p) / ((dyad n).card : ℝ)
  /-- Pool-note item 1: the dyad average is `D^{-B}` for every `B`. -/
  avg_subexp : SubexpLoss avg

namespace DyadData

variable {P : Type*} [DecidableEq P]

/-- The deterministic exceptional set with threshold `D^{-1}`. -/
noncomputable def bad (S : DyadData P) (n : ℕ) : Finset P :=
  badSet S.dyad S.err n

/-- The Markov-trimmed fraction of the dyad. -/
noncomputable def loss (S : DyadData P) (n : ℕ) : ℝ :=
  dyadLoss S.dyad S.err n

theorem loss_nonneg (S : DyadData P) (n : ℕ) : 0 ≤ S.loss n :=
  dyadLoss_nonneg S.dyad S.err n

/-- The dyad Markov fraction is a subexponential loss. -/
theorem loss_subexp (S : DyadData P) : SubexpLoss S.loss :=
  dyadLoss_subexp S.dyad S.err S.err_nonneg S.avg S.avg_def S.avg_subexp

/-- The finer dyad data realize the parent `DyadExceptionInputs`. -/
noncomputable def toPaper (S : DyadData P) : DyadExceptionInputs P where
  dyad := S.dyad
  err := S.err
  err_nonneg := S.err_nonneg
  avg := S.avg
  avg_def := S.avg_def
  avg_subexp := S.avg_subexp

end DyadData

/-- The explicit G.11/G.12 top data, with the interior concentration isolated in
a single `InteriorConcentration` hypothesis. -/
structure TopData where
  /-- Depth of the internal G.11 recurrence. -/
  L : ℕ
  interior : ℕ → ℕ → ℝ
  step : ℕ → ℝ
  eta : ℕ → ℝ
  epsRat : ℕ → ℝ
  epsIn : ℕ → ℝ
  top : ℕ → ℝ
  Ctop : ℕ → ℝ
  cTop : ℝ
  cInt : ℝ
  interior_nonneg : ∀ n i, 0 ≤ interior n i
  eta_nonneg : ∀ n, 0 ≤ eta n
  epsRat_nonneg : ∀ n, 0 ≤ epsRat n
  epsIn_nonneg : ∀ n, 0 ≤ epsIn n
  top_nonneg : ∀ n, 0 ≤ top n
  Ctop_nonneg : ∀ n, 0 ≤ Ctop n
  cTop_nonneg : 0 ≤ cTop
  recurrence : G11InteriorRecurrence interior L step eta epsRat
  step_ge_one : ∀ᶠ n : ℕ in atTop, 1 ≤ step n
  alpha_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ eta n + epsRat n
  depth_bound : ∀ᶠ n : ℕ in atTop,
    step n ^ L * ((L : ℝ) + 1) ≤ Real.exp (cInt * scale n)
  comparison : TopG12Comparison top Ctop interior epsIn eta
  Ctop_le : ∀ᶠ n : ℕ in atTop, Ctop n ≤ Real.exp (cTop * scale n)
  /-- The paper-level interior concentration input. -/
  concentration : InteriorConcentration interior L eta epsRat epsIn

namespace TopData

/-- The top bad-child mass is a subexponential loss. -/
theorem loss_subexp (S : TopData) : SubexpLoss S.top :=
  top_subexp_of_concentration S.interior S.step S.eta S.epsRat S.epsIn S.top S.Ctop
    S.cTop S.cInt S.interior_nonneg S.eta_nonneg S.epsRat_nonneg S.epsIn_nonneg
    S.top_nonneg S.Ctop_nonneg S.cTop_nonneg S.recurrence S.step_ge_one S.alpha_nonneg
    S.depth_bound S.comparison S.Ctop_le S.concentration

/-- The finer top data realize the parent `G12TopInputs`. -/
noncomputable def toPaper (S : TopData) : G12TopInputs where
  L := S.L
  interior := S.interior
  step := S.step
  eta := S.eta
  epsRat := S.epsRat
  epsIn := S.epsIn
  top := S.top
  Ctop := S.Ctop
  cTop := S.cTop
  cInt := S.cInt
  interior_nonneg := S.interior_nonneg
  eta_nonneg := S.eta_nonneg
  epsRat_nonneg := S.epsRat_nonneg
  epsIn_nonneg := S.epsIn_nonneg
  top_nonneg := S.top_nonneg
  Ctop_nonneg := S.Ctop_nonneg
  cTop_nonneg := S.cTop_nonneg
  recurrence := S.recurrence
  step_ge_one := S.step_ge_one
  alpha_nonneg := S.alpha_nonneg
  depth_bound := S.depth_bound
  comparison := S.comparison
  Ctop_le := S.Ctop_le
  base_subexp := S.concentration.1
  eta_subexp := S.concentration.2.1
  epsRat_subexp := S.concentration.2.2.1
  epsIn_subexp := S.concentration.2.2.2

end TopData

/-! ## 6. The L20.4 reduction -/

/-- **The L20.4 inputs, refined.**  The finer pair, top and dyad data. -/
structure L20_4SubInputs (Ω P : Type*) [Fintype Ω] [DecidableEq P] where
  pair : PairData Ω
  top : TopData
  dyad : DyadData P

namespace L20_4SubInputs

variable {Ω P : Type*} [Fintype Ω] [DecidableEq P]

/-- The L20.4 deficit: the pool miss mass, the dyad Markov fraction and the
G.12 top bad-child mass.  All three are genuine nonnegative deficits. -/
noncomputable def loss (S : L20_4SubInputs Ω P) (n : ℕ) : ℝ :=
  S.pair.loss n + S.dyad.loss n + S.top.top n

theorem loss_nonneg (S : L20_4SubInputs Ω P) (n : ℕ) : 0 ≤ S.loss n := by
  unfold loss
  exact add_nonneg (add_nonneg (S.pair.loss_nonneg n) (S.dyad.loss_nonneg n))
    (S.top.top_nonneg n)

/-- **The L20.4 reduction.**  The pool union bound, the dyad Markov trimming and
the G.12 top step are each `D^{-B}` for every `B`, hence their sum is. -/
theorem subexpLoss (S : L20_4SubInputs Ω P) : SubexpLoss S.loss := by
  have h1 : SubexpLoss fun n => S.pair.loss n + S.dyad.loss n :=
    subexpLoss_add S.pair.loss_subexp S.dyad.loss_subexp
  have h2 : SubexpLoss fun n => (S.pair.loss n + S.dyad.loss n) + S.top.top n :=
    subexpLoss_add h1 S.top.loss_subexp
  unfold loss
  exact h2

/-- The `SubexpLeaf` for L20.4 (KB G.12 in the child-root-conditioned law). -/
noncomputable def toSubexpLeaf (S : L20_4SubInputs Ω P) : SubexpLeaf where
  loss := S.loss
  loss_nonneg := S.loss_nonneg
  paper := S.subexpLoss

/-- The `B = 2` C5 ledger slot. -/
theorem slot_le (S : L20_4SubInputs Ω P) :
    ∀ᶠ n : ℕ in atTop, S.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  S.toSubexpLeaf.slot

/-- The finer inputs realize the parent `L20_4Inputs`. -/
noncomputable def toPaper (S : L20_4SubInputs Ω P) : L20_4Inputs Ω P where
  pair := S.pair.toPaper
  top := S.top.toPaper
  dyad := S.dyad.toPaper

/-- The parent realization carries exactly the same deficit. -/
theorem toPaper_loss_eq (S : L20_4SubInputs Ω P) (n : ℕ) :
    S.toPaper.loss n = S.loss n := rfl

/-- Consistency: the parent's own `subexpLoss` applied to the realization gives
the same conclusion. -/
theorem subexpLoss_via_paper (S : L20_4SubInputs Ω P) : SubexpLoss S.loss :=
  S.toPaper.subexpLoss

end L20_4SubInputs

/-! ## Axiom audit -/

#print axioms hitProb_ge_exp
#print axioms poolLoss_subexp
#print axioms dyadLoss_subexp
#print axioms interior_zero_subexp
#print axioms top_le_exp_neg_subexp
#print axioms top_subexp_of_concentration
#print axioms PairData.loss_subexp
#print axioms DyadData.loss_subexp
#print axioms TopData.loss_subexp
#print axioms L20_4SubInputs.subexpLoss
#print axioms L20_4SubInputs.slot_le

end Cogentic.RandomizedL20_4Sub
