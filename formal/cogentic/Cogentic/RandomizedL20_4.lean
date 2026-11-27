import Cogentic.RandomizedPaperLeafStatements
import Cogentic.RandomizedFieldPoolDescent
import Cogentic.RandomizedTopStripMoments
import Cogentic.RandomizedL19SecondMoment

/-!
# L20.4: the child-root-conditioned two-point bound and the top G.12 step

Blueprint §2 C5.a lists **L20.4** (`[GAP]`) as "top G.12 under the incoming-child-root
law, including the child-root-conditioned two-point bound `≤ D^{O(1)}` on
incoming-good parts".  The sources are

* KeyBreak Proposition G.12 and (G.53)–(G.55);
* `research/keybreak-balanced-strip-transfer.md` equation (2) and the paragraph
  "Apply the interior G.11 proof at fixed `k`";
* `research/keybreak-polynomial-top-field-pool.md` items 1–3, and its warning that
  *the unconditional top pair bound in item 1 does not imply the child-root-
  conditioned bound in item 3*, since conditioning on `R_{q,s}` can lose a factor
  of order `q`.

This file separates the paper's assumptions from the reduction that the C5 ledger
consumes.  Nothing here proves the analytic inequality; the file makes the
inequality an explicit `Prop` and proves that the paper's three quantitative
ingredients — the conditioned two-point bound (item 3), the conditioned mean
lower bound (item 1 / equation (2) after normalizing by the deterministic strip
mean), and the G.11/G.12 recurrence algebra (`RandomizedFieldPoolDescent`) —
imply the `SubexpLeaf` recorded for `C5Leaf.topChildLaw`.

## What is proved

1. **Conditioned law infrastructure** (`condWeight`, `condExpect`): the restriction
   of a finite `PMF` to the event `g ∧ R_{q,s}`.
2. **Conditioned Paley–Zygmund**: the conditioned second-moment bound
   `E[(H/B₁)² | g,R] ≤ M` together with the conditioned mean bound
   `E[H/B₁ | g,R] ≥ a` gives the per-draw hit probability
   `≥ a²/(4M)`.  This is exactly the step that turns the polynomial `D^{O(1)}`
   constant of item 3 into the polynomial success probability `D^{-O(1)}` of the
   pool note.
3. **Pool union bound**: `K` independent public draws with per-draw hit
   probability `q` miss with probability at most `(1-q)^K ≤ exp(-qK)`; with
   `q ≥ D^{-C}` and `K ≥ D^{C+1}` this is `exp(-D)` and hence at most `D^{-B}`
   for **every** fixed `B`.  The dyad factor `|J| ≤ D^{O(1)}` is kept explicit
   (it is absorbed by the extra pool exponent, not set to one).
4. **G.11 → G.12 recurrence algebra**: `internal_linear_recurrence_bound`
   propagates the base internal mass, `top_sqrt_of_internal_linear_bound` performs
   the KeyBreak G.12 square-root step, and the resulting top mass is `D^{-B}` for
   every `B` once the base mass, the incoming exceptional mass, and the elliptic
   deletion fraction are `D^{-B}` for every `B`.
5. **Dyad Markov trimming**: the deterministic fraction of a dyad on which the
   per-prime bad mass exceeds `D^{-1}` is at most the dyad average; this is
   `badDyadPrimes_card_le` applied with the explicit threshold `θ = D^{-1}`.
6. **The reduction**: the above three components sum to a `loss` function with
   `SubexpLoss loss`, producing `L20_4Inputs.toSubexpLeaf : SubexpLeaf` and the
   `B = 2` ledger slot.

## What is assumed (paper-level `Prop`s)

* `ChildRootConditionedTwoPoint`: item 3, `E[(H/B₁)² | g,R_{q,s}] ≤ D^{c}` on the
  incoming-good part (KB G.53–G.55, balanced-strip-transfer ¶2).
* `IncomingGoodMeanLower`: item 1, the conditioned normalized first moment is at
  least a fixed `a > 0` (this is equation (2) compared with the tested strip's own
  mean, whose polynomial factor is the already-proved L20.5 ratio
  `TopStripMoments.centeredBinProducts_dividedStrip_ratio_from_supply`).
* `G11InteriorRecurrence`, the subexponential base/exception/elliptic fields: the
  internal G.11 bad-child mass, the G.12 rational exceptions, and the elliptic
  deletion fraction (L21.2) are each `D^{-B}` for every `B` (pool-note item 2;
  KB G.11, G.14, G.51, G.55).
* `TopG12Comparison`: the KeyBreak G.12 top square-root comparison, with the
  `D^{O(1)}` top constant left explicit.

No `sorry`, `admit`, `axiom`, or `native_decide`.  No loss is set to zero: every
component of `L20_4Inputs.loss` is a genuine nonnegative deficit, and the pool
size, dyad factor, elliptic fraction, and rational exceptions are all explicit.
-/

namespace Cogentic.RandomizedL20_4

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedL19SecondMoment

/-! ## 1. The conditioned finite law -/

/-- The incoming event: a rational-good environment together with the prescribed
child root `R_{q,s}`.  This is the event the paper conditions on in G.12. -/
def pairEvent {Ω : Type*} (good childRoot : ℕ → Ω → Prop) (n : ℕ) (ω : Ω) : Prop :=
  good n ω ∧ childRoot n ω

/-- Mass of the event `E` concentrated at `ω`, i.e. the numerator weight of the
conditional law `μ(· | E)`. -/
noncomputable def condWeight {Ω : Type*} [Fintype Ω] (μ : PMF Ω) (E : Ω → Prop)
    (ω : Ω) : ℝ := by
  classical
  exact if E ω then pmfWeight μ ω else 0

/-- Conditional expectation `E[X | E]` under a finite law (zero when `Pr E = 0`). -/
noncomputable def condExpect {Ω : Type*} [Fintype Ω] (μ : PMF Ω) (E : Ω → Prop)
    (X : Ω → ℝ) : ℝ := by
  classical
  exact (∑ ω, condWeight μ E ω * X ω) / pmfProb μ E

theorem condWeight_nonneg {Ω : Type*} [Fintype Ω] (μ : PMF Ω) (E : Ω → Prop)
    (ω : Ω) : 0 ≤ condWeight μ E ω := by
  classical
  unfold condWeight
  split_ifs with h
  · exact pmfWeight_nonneg μ ω
  · exact le_refl 0

theorem condWeight_sum_eq {Ω : Type*} [Fintype Ω] (μ : PMF Ω) (E : Ω → Prop) :
    ∑ ω, condWeight μ E ω = pmfProb μ E := by
  classical
  rw [pmfProb_eq_sum_filter, Finset.sum_filter]
  simp [condWeight]

theorem condWeight_eq_zero_of_not {Ω : Type*} [Fintype Ω] (μ : PMF Ω) (E : Ω → Prop)
    {ω : Ω} (h : ¬ E ω) : condWeight μ E ω = 0 := by
  classical
  unfold condWeight
  simp [h]

theorem condWeight_eq_of_mem {Ω : Type*} [Fintype Ω] (μ : PMF Ω) (E : Ω → Prop)
    {ω : Ω} (h : E ω) : condWeight μ E ω = pmfWeight μ ω := by
  classical
  unfold condWeight
  simp [h]

/-! ## 2. Conditioned Paley–Zygmund and the per-draw hit probability -/

/-- **Weighted Paley–Zygmund with a sub-probability weight.**  For nonnegative
weights `w` of total mass `W`, a first moment at least `a W` and a second moment
at most `M W` force the event `{Z ≥ a/2}` to carry at least `(a²/(4M)) W` mass.
This is the homogeneous form of `pmf_paley_zygmund` that applies to the
conditioned sub-law `condWeight μ E`. -/
theorem paley_zygmund_weight {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (Z : Ω → ℝ) {a M W : ℝ} (ha : 0 < a) (hM : 0 < M)
    (hW : ∑ ω, w ω = W) (hmean : a * W ≤ ∑ ω, w ω * Z ω)
    (hsecond : ∑ ω, w ω * Z ω ^ 2 ≤ M * W) :
    a ^ 2 / (4 * M) * W ≤ ∑ ω ∈ Finset.univ.filter (fun ω => a / 2 ≤ Z ω), w ω := by
  classical
  have hW0 : 0 ≤ W := hW ▸ Finset.sum_nonneg fun ω _ => hw ω
  let large := Finset.univ.filter (fun ω => a / 2 ≤ Z ω)
  have hlargeMean : a * W / 2 ≤ ∑ ω ∈ large, w ω * Z ω := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun ω _ => show
        w ω * Z ω ≤ (if a / 2 ≤ Z ω then w ω * Z ω else 0) + (a / 2) * w ω by
      have hwω := hw ω
      split_ifs with hZ
      · linarith [mul_nonneg (show 0 ≤ a / 2 by positivity) hwω]
      · nlinarith [mul_le_mul_of_nonneg_left (le_of_not_ge hZ) hwω])
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.mul_sum, hW] at h
    linarith
  have hCS : (∑ ω ∈ large, w ω * Z ω) ^ 2 ≤
      (∑ ω ∈ large, w ω) * ∑ ω ∈ large, w ω * Z ω ^ 2 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul large
      (fun ω _ => hw ω)
      (fun ω _ => mul_nonneg (hw ω) (sq_nonneg _))
      (fun _ _ => by ring_nf; rfl)
  have hsub : ∑ ω ∈ large, w ω * Z ω ^ 2 ≤ M * W :=
    (Finset.sum_le_univ_sum_of_nonneg
      (fun ω => mul_nonneg (hw ω) (sq_nonneg _))).trans hsecond
  have hmul : (∑ ω ∈ large, w ω) * (∑ ω ∈ large, w ω * Z ω ^ 2) ≤
      (∑ ω ∈ large, w ω) * (M * W) :=
    mul_le_mul_of_nonneg_left hsub (Finset.sum_nonneg fun ω _ => hw ω)
  have hsq : (a * W / 2) ^ 2 ≤ (∑ ω ∈ large, w ω * Z ω) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlargeMean 2
  have hkey : (a * W / 2) ^ 2 ≤ (∑ ω ∈ large, w ω) * (M * W) :=
    hsq.trans (hCS.trans hmul)
  rcases eq_or_lt_of_le hW0 with hzero | hpos
  · rw [← hzero]
    simp only [mul_zero]
    exact Finset.sum_nonneg fun ω _ => hw ω
  · have hS : 0 ≤ ∑ ω ∈ large, w ω := Finset.sum_nonneg fun ω _ => hw ω
    have hdiv : a ^ 2 * W / 4 ≤ (∑ ω ∈ large, w ω) * M := by
      have hkey' : (a ^ 2 * W ^ 2 / 4) ≤ (∑ ω ∈ large, w ω) * (M * W) := by
        convert hkey using 1
        ring
      have hmul' : (a ^ 2 * W / 4) * W ≤ ((∑ ω ∈ large, w ω) * M) * W := by
        nlinarith [hkey']
      exact le_of_mul_le_mul_right hmul' hpos
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * M)]
    nlinarith [hdiv]

/-- **Conditioned Paley–Zygmund.**  If `Pr E > 0`, the conditional mean of `Z`
on `E` is at least `a > 0`, and the conditional second moment is at most `M`,
then the conditional probability of `{Z ≥ a/2}` is at least `a²/(4M)`. -/
theorem cond_paley_zygmund {Ω : Type*} [Fintype Ω] (μ : PMF Ω) (E : Ω → Prop)
    (Z : Ω → ℝ) {a M : ℝ} (hE : 0 < pmfProb μ E) (ha : 0 < a) (hM : 0 < M)
    (hmean : a ≤ condExpect μ E Z)
    (hsecond : condExpect μ E (fun ω => Z ω ^ 2) ≤ M) :
    a ^ 2 / (4 * M) ≤
      pmfProb μ (fun ω => E ω ∧ a / 2 ≤ Z ω) / pmfProb μ E := by
  classical
  have hmean' : a * pmfProb μ E ≤ ∑ ω, condWeight μ E ω * Z ω := by
    unfold condExpect at hmean
    rwa [le_div_iff₀ hE] at hmean
  have hsecond' : ∑ ω, condWeight μ E ω * Z ω ^ 2 ≤ M * pmfProb μ E := by
    unfold condExpect at hsecond
    rwa [div_le_iff₀ hE] at hsecond
  have hpz := paley_zygmund_weight (condWeight μ E) (condWeight_nonneg μ E) Z ha hM
    (condWeight_sum_eq μ E) hmean' hsecond'
  have hfilter : ∑ ω ∈ Finset.univ.filter (fun ω => a / 2 ≤ Z ω), condWeight μ E ω =
      pmfProb μ (fun ω => E ω ∧ a / 2 ≤ Z ω) := by
    rw [pmfProb_eq_sum_filter, Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h1 : E ω <;> by_cases h2 : a / 2 ≤ Z ω <;> simp [condWeight, h1, h2]
  rw [hfilter] at hpz
  exact (le_div_iff₀ hE).mpr hpz

/-! ## 3. The pool union bound -/

/-- A pool of `K` independent draws misses a fixed prime with probability at most
`exp (-q K)` when the per-draw hit probability is `q ∈ [0,1]`. -/
theorem pool_miss_le_exp {q : ℝ} (hq1 : q ≤ 1) (K : ℕ) :
    (1 - q) ^ K ≤ Real.exp (-q * (K : ℝ)) :=
  one_sub_pow_le_exp_neg_mul hq1 K

/-- `c H ≤ exp H` eventually.  This is the only growth comparison used to absorb
the polynomial dyad factor and the slack constants into `exp (-B H)`. -/
theorem eventually_mul_le_exp (c : ℝ) : ∀ᶠ H : ℝ in atTop, c * H ≤ Real.exp H := by
  filter_upwards [eventually_ge_atTop (max 0 (2 * c))] with H hH
  have hH0 : 0 ≤ H := (le_max_left _ _).trans hH
  have hc : c ≤ H / 2 := by
    have h2 : 2 * c ≤ H := (le_max_right _ _).trans hH
    linarith
  have hsq : H ^ 2 / 2 ≤ Real.exp H := by
    have h := Real.quadratic_le_exp_of_nonneg hH0
    nlinarith [hH0]
  have hm : c * H ≤ (H / 2) * H := mul_le_mul_of_nonneg_right hc hH0
  nlinarith

/-- `exp (-exp H) ≤ exp (-B H)` eventually, with no hypothesis on the sign of `B`
beyond `B > 0`. -/
theorem exp_neg_exp_le_exp_neg_mul {B : ℝ} (_hB : 0 < B) :
    ∀ᶠ H : ℝ in atTop, Real.exp (-Real.exp H) ≤ Real.exp (-B * H) := by
  filter_upwards [eventually_mul_le_exp B] with H hH
  exact Real.exp_le_exp.mpr (by linarith)

/-! ## 4. G.11 interior propagation and the G.12 square-root step -/

/-- The KeyBreak G.11 interior recurrence `δ_i ≤ C (δ_{i+1} + η + ε_rat)` at a
fixed multiplier, uniformly in `i < L`. -/
def G11InteriorRecurrence (δ : ℕ → ℕ → ℝ) (L : ℕ) (step eta eps : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ i < L, δ n i ≤ step n * (δ n (i + 1) + eta n + eps n)

/-- The KeyBreak G.12 top comparison
`δ_top ≤ C_top (√δ_1 + √ε_in + η)` under the incoming-child-root law. -/
def TopG12Comparison (top Ctop : ℕ → ℝ) (δ : ℕ → ℕ → ℝ) (epsIn eta : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    top n ≤ Ctop n * (Real.sqrt (δ n 0) + Real.sqrt (epsIn n) + eta n)

/-- **G.11 propagation to the top internal level.**  A subexponential base mass
`δ_L ≤ exp (-A H)` and subexponential internal errors `η + ε_rat ≤ exp (-A H)`
propagate through the linear recurrence at the cost of the `D^{O(1)}` depth
factor `C^L (L+1)`, giving `δ_0 ≤ exp (-T H)` as soon as
`T + c_int + 1 ≤ A`.  This is `internal_linear_recurrence_bound` followed by the
elementary `(L+1) ≤ exp H` bookkeeping; it is not a loss of the paper's estimate,
the base mass and the errors are genuinely `D^{-B}` inputs. -/
theorem interior_zero_le_exp {L : ℕ} {δ : ℕ → ℝ} {Cstep eta eps T cInt A H : ℝ}
    (heta : 0 ≤ eta) (heps : 0 ≤ eps) (hC : 1 ≤ Cstep) (hH : 0 ≤ H)
    (hL : (L : ℝ) + 1 ≤ Real.exp H)
    (hrec : ∀ i < L, δ i ≤ Cstep * (δ (i + 1) + eta + eps))
    (hstep : Cstep ^ L ≤ Real.exp (cInt * H))
    (hbase : δ L ≤ Real.exp (-A * H))
    (halpha : eta + eps ≤ Real.exp (-A * H))
    (hA : T + cInt + 1 ≤ A) :
    δ 0 ≤ Real.exp (-T * H) := by
  have hα : 0 ≤ eta + eps := add_nonneg heta heps
  have hint := internal_linear_recurrence_bound δ L hC hα hrec
  have hE : 0 ≤ Real.exp (-A * H) := (Real.exp_pos _).le
  have hinner : δ L + (L : ℝ) * (eta + eps) ≤ ((L : ℝ) + 1) * Real.exp (-A * H) := by
    have h1 : (L : ℝ) * (eta + eps) ≤ (L : ℝ) * Real.exp (-A * H) :=
      mul_le_mul_of_nonneg_left halpha (Nat.cast_nonneg L)
    have h2 : δ L + (L : ℝ) * (eta + eps) ≤
        Real.exp (-A * H) + (L : ℝ) * Real.exp (-A * H) := add_le_add hbase h1
    have h3 : Real.exp (-A * H) + (L : ℝ) * Real.exp (-A * H) =
        ((L : ℝ) + 1) * Real.exp (-A * H) := by ring
    linarith
  have hstepnn : 0 ≤ Cstep ^ L := pow_nonneg (by linarith) L
  have h4 : Cstep ^ L * (δ L + (L : ℝ) * (eta + eps)) ≤
      Cstep ^ L * (((L : ℝ) + 1) * Real.exp (-A * H)) :=
    mul_le_mul_of_nonneg_left hinner hstepnn
  have hLE : ((L : ℝ) + 1) * Real.exp (-A * H) ≤ Real.exp H * Real.exp (-A * H) :=
    mul_le_mul_of_nonneg_right hL hE
  have h5 : Cstep ^ L * (((L : ℝ) + 1) * Real.exp (-A * H)) ≤
      Real.exp (cInt * H) * (Real.exp H * Real.exp (-A * H)) :=
    mul_le_mul hstep hLE (by positivity) (Real.exp_pos _).le
  have h6 : Real.exp (cInt * H) * (Real.exp H * Real.exp (-A * H)) =
      Real.exp ((cInt + 1 - A) * H) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h7 : Real.exp ((cInt + 1 - A) * H) ≤ Real.exp (-T * H) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hA, hH]
  exact hint.trans (h4.trans (h5.trans (h6.trans_le h7)))

/-- **The G.12 top square-root step, converted to `D^{-B}`.**  Given the top
comparison at a polynomial top constant `C ≤ exp (c_top H)`, an interior mass
and an incoming exceptional mass each at most `exp (-2 (B + c_top + 1) H)`, and
an elliptic deletion fraction at most `exp (-(B + c_top + 1) H)`, the top mass is
at most `exp (-B H)`.  The three terms are bounded separately and the harmless
factor `3` is absorbed by `exp H ≥ 3`; no term is dropped. -/
theorem top_le_exp_neg {δtop C intMass inMass eta B cTop H : ℝ}
    (_hB : 0 < B) (_hH : 0 ≤ H) (hH3 : Real.log 3 ≤ H)
    (_hint_nn : 0 ≤ intMass) (_hin_nn : 0 ≤ inMass) (heta_nn : 0 ≤ eta)
    (hC : C ≤ Real.exp (cTop * H))
    (hint : intMass ≤ Real.exp (-(2 * (B + cTop + 1)) * H))
    (hin : inMass ≤ Real.exp (-(2 * (B + cTop + 1)) * H))
    (hell : eta ≤ Real.exp (-(B + cTop + 1) * H))
    (htop : δtop ≤ C * (Real.sqrt intMass + Real.sqrt inMass + eta)) :
    δtop ≤ Real.exp (-B * H) := by
  have hs_int : Real.sqrt intMass ≤ Real.exp (-(B + cTop + 1) * H) := by
    have hsq : intMass ≤ (Real.exp (-(B + cTop + 1) * H)) ^ 2 := by
      refine hint.trans (le_of_eq ?_)
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    calc Real.sqrt intMass ≤ Real.sqrt ((Real.exp (-(B + cTop + 1) * H)) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = Real.exp (-(B + cTop + 1) * H) := Real.sqrt_sq (Real.exp_pos _).le
  have hs_in : Real.sqrt inMass ≤ Real.exp (-(B + cTop + 1) * H) := by
    have hsq : inMass ≤ (Real.exp (-(B + cTop + 1) * H)) ^ 2 := by
      refine hin.trans (le_of_eq ?_)
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    calc Real.sqrt inMass ≤ Real.sqrt ((Real.exp (-(B + cTop + 1) * H)) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = Real.exp (-(B + cTop + 1) * H) := Real.sqrt_sq (Real.exp_pos _).le
  have hsum : Real.sqrt intMass + Real.sqrt inMass + eta ≤
      3 * Real.exp (-(B + cTop + 1) * H) := by
    linarith [hs_int, hs_in, hell]
  have hsum_nn : 0 ≤ Real.sqrt intMass + Real.sqrt inMass + eta :=
    add_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) heta_nn
  have hmul : C * (Real.sqrt intMass + Real.sqrt inMass + eta) ≤
      Real.exp (cTop * H) * (3 * Real.exp (-(B + cTop + 1) * H)) :=
    mul_le_mul hC hsum hsum_nn (Real.exp_pos _).le
  have hrhs : Real.exp (cTop * H) * (3 * Real.exp (-(B + cTop + 1) * H)) ≤
      Real.exp (-B * H) := by
    calc Real.exp (cTop * H) * (3 * Real.exp (-(B + cTop + 1) * H))
        = 3 * (Real.exp (cTop * H) * Real.exp (-(B + cTop + 1) * H)) := by ring
      _ = 3 * Real.exp (-(B + 1) * H) := by
          rw [← Real.exp_add]
          congr 2
          ring
      _ ≤ Real.exp H * Real.exp (-(B + 1) * H) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          rw [show (3 : ℝ) = Real.exp (Real.log 3) from (Real.exp_log (by norm_num)).symm]
          exact Real.exp_le_exp.mpr hH3
      _ = Real.exp (-B * H) := by
          rw [← Real.exp_add]
          congr 1
          ring
  exact htop.trans (hmul.trans hrhs)

/-- The explicit inputs of the KeyBreak G.12 top step in the law conditioned on
`g ∧ R_{q,s}`.  `interior n i` is the normalized internal bad-child mass `δ_i`,
`epsRat` the G.11 rational error, `eta` the elliptic deletion fraction, `epsIn`
the incoming exceptional mass, `top` the resulting top bad mass and `Ctop` the
`D^{O(1)}` G.12 comparison constant. -/
structure G12TopInputs where
  /-- Depth of the internal G.11 recurrence. -/
  L : ℕ
  /-- Internal normalized bad-child masses `δ_i`, `i = 0 … L`. -/
  interior : ℕ → ℕ → ℝ
  /-- G.11 step multiplier. -/
  step : ℕ → ℝ
  /-- Elliptic deletion fraction `η` (L21.2). -/
  eta : ℕ → ℝ
  /-- G.11 rational error `ε_rat`. -/
  epsRat : ℕ → ℝ
  /-- Incoming exceptional mass `ε̄^in_{0,J}` (G.12 rational exceptions). -/
  epsIn : ℕ → ℝ
  /-- Resulting top bad-child mass `δ_top`. -/
  top : ℕ → ℝ
  /-- The G.12 top constant. -/
  Ctop : ℕ → ℝ
  /-- Exponent of the top constant: `C_top ≤ D^{c_top}`. -/
  cTop : ℝ
  /-- Exponent of the depth factor: `step^L (L+1) ≤ D^{c_int}`. -/
  cInt : ℝ
  interior_nonneg : ∀ n i, 0 ≤ interior n i
  eta_nonneg : ∀ n, 0 ≤ eta n
  epsRat_nonneg : ∀ n, 0 ≤ epsRat n
  epsIn_nonneg : ∀ n, 0 ≤ epsIn n
  top_nonneg : ∀ n, 0 ≤ top n
  Ctop_nonneg : ∀ n, 0 ≤ Ctop n
  cTop_nonneg : 0 ≤ cTop
  /-- The G.11 recurrence holds at every internal level. -/
  recurrence : G11InteriorRecurrence interior L step eta epsRat
  /-- The step multiplier is at least one (G.11 uses `C_step ≥ 1`). -/
  step_ge_one : ∀ᶠ n : ℕ in atTop, 1 ≤ step n
  /-- The G.11 errors are nonnegative. -/
  alpha_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ eta n + epsRat n
  /-- The depth factor is `D^{O(1)}`. -/
  depth_bound : ∀ᶠ n : ℕ in atTop,
    step n ^ L * ((L : ℝ) + 1) ≤ Real.exp (cInt * scale n)
  /-- KeyBreak G.12 top square-root comparison. -/
  comparison : TopG12Comparison top Ctop interior epsIn eta
  /-- The top constant is `D^{O(1)}`. -/
  Ctop_le : ∀ᶠ n : ℕ in atTop, Ctop n ≤ Real.exp (cTop * scale n)
  /-- Pool-note item 2: the top internal bad mass is `D^{-B}` for every `B`. -/
  base_subexp : SubexpLoss fun n => interior n L
  /-- L21.2: the elliptic deletion fraction is `D^{-B}` for every `B`. -/
  eta_subexp : SubexpLoss eta
  /-- The G.11 rational error is `D^{-B}` for every `B`. -/
  epsRat_subexp : SubexpLoss epsRat
  /-- The incoming exceptional mass is `D^{-B}` for every `B`. -/
  epsIn_subexp : SubexpLoss epsIn

namespace G12TopInputs

/-- `internal_linear_recurrence_bound` applied at every scale. -/
theorem interior_zero_bound (S : G12TopInputs) :
    ∀ᶠ n : ℕ in atTop,
      S.interior n 0 ≤ S.step n ^ S.L *
        (S.interior n S.L + (S.L : ℝ) * (S.eta n + S.epsRat n)) := by
  filter_upwards [S.step_ge_one, S.alpha_nonneg, S.recurrence] with n hstep hα hrec
  exact internal_linear_recurrence_bound (S.interior n) S.L hstep hα hrec

/-- `top_sqrt_of_internal_linear_bound`: the G.12 top comparison composed with
the G.11 recurrence bound. -/
theorem top_bound (S : G12TopInputs) :
    ∀ᶠ n : ℕ in atTop,
      S.top n ≤ S.Ctop n *
        (Real.sqrt (S.step n ^ S.L *
            (S.interior n S.L + (S.L : ℝ) * (S.eta n + S.epsRat n))) +
          Real.sqrt (S.epsIn n) + S.eta n) := by
  filter_upwards [Eventually.of_forall S.Ctop_nonneg, S.step_ge_one, S.alpha_nonneg,
    S.recurrence, S.comparison] with n hCtop hstep hα hrec hcmp
  exact top_sqrt_of_internal_linear_bound (S.interior n) S.L hCtop hstep hα hrec hcmp

/-- **The top bad mass is a subexponential loss.**  The G.11 base mass, the
incoming exception and the elliptic fraction are `D^{-B}` for every `B`; the
depth and top constants are `D^{O(1)}`; hence the G.12 top mass is `D^{-B}` for
every `B`. -/
theorem top_subexp (S : G12TopInputs) : SubexpLoss S.top := by
  intro B hB
  let T : ℝ := 2 * (B + S.cTop + 1)
  have hTpos : 0 < T := by dsimp [T]; nlinarith [hB, S.cTop_nonneg]
  let A : ℝ := max (T + S.cInt + 1) 1
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hAT : T + S.cInt + 1 ≤ A := le_max_left _ _
  have hcpos : 0 < B + S.cTop + 1 := by linarith [hB, S.cTop_nonneg]
  filter_upwards [S.step_ge_one, S.alpha_nonneg, S.recurrence, S.comparison,
    S.Ctop_le, S.depth_bound, S.base_subexp A hApos,
    subexpLoss_add S.eta_subexp S.epsRat_subexp A hApos,
    S.eta_subexp (B + S.cTop + 1) hcpos, S.epsIn_subexp T hTpos,
    scale_grows.eventually_ge_atTop 0,
    scale_grows.eventually_ge_atTop
      (max (Real.log 3) (Real.log ((S.L : ℝ) + 1) + 1))]
    with n hstep hα hrec hcmp hC hdepth hbase halpha heta hin hH0 hHbig
  have hH : 0 ≤ scale n := hH0
  have hH3 : Real.log 3 ≤ scale n := le_trans (le_max_left _ _) hHbig
  have hHL : (S.L : ℝ) + 1 ≤ Real.exp (scale n) := by
    have hlog : Real.log ((S.L : ℝ) + 1) ≤ scale n := by
      have hle : Real.log ((S.L : ℝ) + 1) + 1 ≤
          max (Real.log 3) (Real.log ((S.L : ℝ) + 1) + 1) := le_max_right _ _
      linarith
    calc (S.L : ℝ) + 1 = Real.exp (Real.log ((S.L : ℝ) + 1)) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (scale n) := Real.exp_le_exp.mpr hlog
  have hstepL : S.step n ^ S.L ≤ Real.exp (S.cInt * scale n) := by
    have hfac : S.step n ^ S.L ≤ S.step n ^ S.L * ((S.L : ℝ) + 1) := by
      have hL0 : (0 : ℝ) ≤ (S.L : ℝ) := Nat.cast_nonneg S.L
      have h1 : (1 : ℝ) ≤ (S.L : ℝ) + 1 := by linarith
      nlinarith [pow_nonneg (show 0 ≤ S.step n by linarith) S.L]
    exact hfac.trans hdepth
  have hint0 : S.interior n 0 ≤ Real.exp (-T * scale n) :=
    interior_zero_le_exp (δ := S.interior n) (Cstep := S.step n) (eta := S.eta n)
      (eps := S.epsRat n) (T := T) (cInt := S.cInt) (A := A) (H := scale n)
      (S.eta_nonneg n) (S.epsRat_nonneg n) hstep hH hHL hrec hstepL hbase halpha hAT
  exact top_le_exp_neg (δtop := S.top n) (C := S.Ctop n) (intMass := S.interior n 0)
    (inMass := S.epsIn n) (eta := S.eta n) (B := B) (cTop := S.cTop) (H := scale n)
    hB hH hH3 (S.interior_nonneg n 0) (S.epsIn_nonneg n) (S.eta_nonneg n)
    hC (by simpa [T] using hint0) hin heta hcmp

end G12TopInputs

/-! ## 5. Deterministic dyad trimming (Markov across the dyad) -/

/-- A dyad average at most `δ` bounds the total error by `δ · |J|`. -/
theorem sum_le_mul_card_of_div_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) {δ : ℝ}
    (h : (∑ i ∈ s, f i) / (s.card : ℝ) ≤ δ) :
    ∑ i ∈ s, f i ≤ δ * (s.card : ℝ) := by
  rcases Nat.eq_zero_or_pos s.card with hz | hp
  · have hs : s = ∅ := Finset.card_eq_zero.mp hz
    rw [hs]
    simp
  · have hpos : (0 : ℝ) < (s.card : ℝ) := Nat.cast_pos.mpr hp
    rw [div_le_iff₀ hpos] at h
    linarith

/-- The deterministic Markov trimming of a top dyad: the paper removes the
primes on which the per-prime bad mass exceeds `D^{-1}`, and bounds the removed
fraction by the dyad average.  The canonical bad set is
`badDyadPrimes` from `RandomizedFieldPoolDescent`. -/
structure DyadExceptionInputs (P : Type*) [DecidableEq P] where
  /-- The top dyad at scale `n`. -/
  dyad : ℕ → Finset P
  /-- The per-prime normalized bad mass (rational exception or child-bad mass). -/
  err : ℕ → P → ℝ
  err_nonneg : ∀ n p, 0 ≤ err n p
  /-- The dyad average of the bad mass. -/
  avg : ℕ → ℝ
  avg_def : ∀ n, avg n = (∑ p ∈ dyad n, err n p) / ((dyad n).card : ℝ)
  /-- Pool-note item 1, last sentence: the dyad average is `D^{-B}` for every
  `B` (the imported exponents can be chosen large). -/
  avg_subexp : SubexpLoss avg

namespace DyadExceptionInputs

variable {P : Type*} [DecidableEq P]

/-- The deterministic exceptional set of the dyad at scale `n`, with threshold
`D^{-1}`. -/
noncomputable def badSet (S : DyadExceptionInputs P) (n : ℕ) : Finset P :=
  badDyadPrimes (S.dyad n) (S.err n) (fun _ => 0) (Real.exp (-(1 : ℝ) * scale n)) 1

/-- The fraction of the dyad removed by the Markov trimming. -/
noncomputable def loss (S : DyadExceptionInputs P) (n : ℕ) : ℝ :=
  ((S.badSet n).card : ℝ) / ((S.dyad n).card : ℝ)

theorem loss_nonneg (S : DyadExceptionInputs P) (n : ℕ) : 0 ≤ S.loss n :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- `badDyadPrimes_card_le` at the threshold `D^{-1}`: the exceptional fraction
is at most the dyad average divided by the threshold, hence `D^{-B}` for every
`B`. -/
theorem loss_subexp (S : DyadExceptionInputs P) : SubexpLoss S.loss := by
  intro B hB
  filter_upwards [S.avg_subexp (B + 1) (by linarith)] with n havg
  have hθ : 0 < Real.exp (-(1 : ℝ) * scale n) := Real.exp_pos _
  have hsum : ∑ p ∈ S.dyad n, S.err n p ≤ Real.exp (-(B + 1) * scale n) *
      ((S.dyad n).card : ℝ) := by
    have hdiv : (∑ p ∈ S.dyad n, S.err n p) / ((S.dyad n).card : ℝ) ≤
        Real.exp (-(B + 1) * scale n) := by
      rwa [S.avg_def n] at havg
    exact sum_le_mul_card_of_div_le (S.dyad n) (S.err n) hdiv
  have hcard := badDyadPrimes_card_le (S.dyad n) (S.err n) (fun _ => 0)
    (δ_rat := Real.exp (-(B + 1) * scale n)) (δ_bad := 0)
    (θ_rat := Real.exp (-(1 : ℝ) * scale n)) (θ_bad := 1)
    hθ (by norm_num) (fun p _ => S.err_nonneg n p) (fun p _ => le_refl 0) hsum
    (by simp)
  have hratio : Real.exp (-(B + 1) * scale n) / Real.exp (-(1 : ℝ) * scale n) =
      Real.exp (-B * scale n) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hb : ((S.badSet n).card : ℝ) ≤ Real.exp (-B * scale n) * ((S.dyad n).card : ℝ) := by
    calc ((S.badSet n).card : ℝ)
        ≤ (Real.exp (-(B + 1) * scale n) / Real.exp (-(1 : ℝ) * scale n) + 0 / 1) *
            ((S.dyad n).card : ℝ) := hcard
      _ = Real.exp (-B * scale n) * ((S.dyad n).card : ℝ) := by
          rw [hratio]
          norm_num
  unfold DyadExceptionInputs.loss
  by_cases hz : (S.dyad n).card = 0
  · simp only [hz, Nat.cast_zero, div_zero]
    positivity
  · have hpos : (0 : ℝ) < ((S.dyad n).card : ℝ) :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz)
    rw [div_le_iff₀ hpos]
    linarith [hb]

end DyadExceptionInputs

/-! ## 6. The paper-level inputs of L20.4 -/

/-- **Top-field-pool item 3 / KB (G.53)–(G.55).**  On the incoming-good part, in
the law of `(k, F)` conditioned on `g` and on the prescribed child root
`R_{q,s}`, the second moment of the normalized top height `H^det_{0,J}/B₁(q)` is
at most `D^c`.  This is a *conditioned* statement: the pool note stresses that
the ordinary unconditioned bound does not imply it, because conditioning can lose
a factor of order `q`. -/
def ChildRootConditionedTwoPoint {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (good childRoot : ℕ → Ω → Prop) (Z : ℕ → Ω → ℝ) (c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    condExpect (μ n) (pairEvent good childRoot n) (fun ω => Z n ω ^ 2) ≤
      Real.exp (c * scale n)

/-- **Pool-note item 1 / balanced-strip-transfer (2), normalized.**  After
dividing by the deterministic strip mean, the conditioned first moment of the
top height on the incoming-good part is at least a fixed `a > 0`.  In the
manuscript this is `E[H^det_{0,J} | g,R_{q,s}] ≪ D^{O(1)}/q · μ_q/μ · R_J/m_J`
compared with the tested strip's own mean; the polynomial factor `D^{O(1)}/q`
and the L20.5 ratio `μ_q/μ ≤ D^{O(1)}` are absorbed into the normalization. -/
def IncomingGoodMeanLower {Ω : Type*} [Fintype Ω] (μ : ℕ → PMF Ω)
    (good childRoot : ℕ → Ω → Prop) (Z : ℕ → Ω → ℝ) (a : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, a ≤ condExpect (μ n) (pairEvent good childRoot n) (Z n)

/-- The per-prime top law: the incoming event, the normalized top height, and
the conditioned moment inputs of items 1 and 3.  The pool size and the dyad
cardinality are explicit; the pool miss probability is compared with the dyad
union bound. -/
structure ChildRootPairInputs (Ω : Type*) [Fintype Ω] where
  /-- The field/trial law. -/
  μ : ℕ → PMF Ω
  /-- Rational-good environments. -/
  good : ℕ → Ω → Prop
  /-- The prescribed child root event `R_{q,s}`. -/
  childRoot : ℕ → Ω → Prop
  /-- The normalized top height `H^det_{0,J}/B₁(q)`. -/
  Z : ℕ → Ω → ℝ
  /-- The fixed Paley–Zygmund mean constant `a`. -/
  a : ℝ
  a_pos : 0 < a
  /-- Exponent of the conditioned two-point constant. -/
  cPair : ℝ
  cPair_nonneg : 0 ≤ cPair
  /-- Exponent of the dyad cardinality `|J|`. -/
  cDyad : ℝ
  cDyad_nonneg : 0 ≤ cDyad
  /-- Number of primes in the top dyad. -/
  dyadCard : ℕ → ℕ
  dyadCard_le : ∀ᶠ n : ℕ in atTop,
    (dyadCard n : ℝ) ≤ Real.exp (cDyad * scale n)
  /-- Number of independent public pool draws. -/
  poolSize : ℕ → ℕ
  /-- The pool exponent is large enough to beat every fixed power of `D`. -/
  poolSize_ge : ∀ᶠ n : ℕ in atTop,
    Real.exp ((cPair + cDyad + 2) * scale n) ≤ (poolSize n : ℝ)
  /-- The incoming event has positive conditional mass at every scale. -/
  event_pos : ∀ n, 0 < pmfProb (μ n) (pairEvent good childRoot n)
  /-- Pool-note item 1 / (2): the conditioned mean is at least `a`. -/
  mean_lower : IncomingGoodMeanLower μ good childRoot Z a
  /-- Pool-note item 3 / KB (G.53)–(G.55): the conditioned two-point bound. -/
  pair_bound : ChildRootConditionedTwoPoint μ good childRoot Z cPair

namespace ChildRootPairInputs

variable {Ω : Type*} [Fintype Ω]

/-- The conditional hit probability of one pool draw:
`Pr(g ∧ R_{q,s} ∧ Z ≥ a/2) / Pr(g ∧ R_{q,s})`. -/
noncomputable def hitProb (S : ChildRootPairInputs Ω) (n : ℕ) : ℝ :=
  pmfProb (S.μ n)
      (fun ω => pairEvent S.good S.childRoot n ω ∧ S.a / 2 ≤ S.Z n ω) /
    pmfProb (S.μ n) (pairEvent S.good S.childRoot n)

theorem hitProb_le_one (S : ChildRootPairInputs Ω) (n : ℕ) : S.hitProb n ≤ 1 := by
  unfold ChildRootPairInputs.hitProb
  rw [div_le_one (S.event_pos n)]
  exact pmfProb_mono (S.μ n) (fun ω hω => hω.1)

/-- **Conditioned Paley–Zygmund applied to item 3.**  The conditioned
two-point bound `E[Z² | g,R] ≤ D^{cPair}` and the conditioned mean bound `a`
give a per-draw hit probability at least `(a²/4) D^{-cPair}`, which is
`D^{-(cPair+1)}` once the constant `a²/4 ≥ D^{-1}`. -/
theorem hitProb_lower (S : ChildRootPairInputs Ω) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-(S.cPair + 1) * scale n) ≤ S.hitProb n := by
  filter_upwards [Eventually.of_forall S.event_pos, S.mean_lower, S.pair_bound,
    scale_grows.eventually_ge_atTop (Real.log (4 / S.a ^ 2) + 1)] with n hpos hmean hpair hbig
  have hlog : Real.log (4 / S.a ^ 2) ≤ scale n := by linarith
  have hfac : Real.exp (-scale n) ≤ S.a ^ 2 / 4 := by
    calc Real.exp (-scale n) ≤ Real.exp (-(Real.log (4 / S.a ^ 2))) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = S.a ^ 2 / 4 := by
          rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) (pow_pos S.a_pos 2))]
          field_simp
  have hMpos : (0 : ℝ) < Real.exp (S.cPair * scale n) := Real.exp_pos _
  have hpz := cond_paley_zygmund (S.μ n) (pairEvent S.good S.childRoot n) (S.Z n)
    hpos S.a_pos hMpos hmean hpair
  have hexp : S.a ^ 2 / (4 * Real.exp (S.cPair * scale n)) =
      S.a ^ 2 / 4 * Real.exp (-(S.cPair * scale n)) := by
    rw [Real.exp_neg]
    field_simp
  have hmul := mul_le_mul_of_nonneg_right hfac (Real.exp_pos (-(S.cPair * scale n))).le
  have hprod : Real.exp (-(S.cPair + 1) * scale n) =
      Real.exp (-scale n) * Real.exp (-(S.cPair * scale n)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc Real.exp (-(S.cPair + 1) * scale n)
      = Real.exp (-scale n) * Real.exp (-(S.cPair * scale n)) := hprod
    _ ≤ S.a ^ 2 / 4 * Real.exp (-(S.cPair * scale n)) := hmul
    _ = S.a ^ 2 / (4 * Real.exp (S.cPair * scale n)) := hexp.symm
    _ ≤ S.hitProb n := hpz

/-- The pool contribution to the top deficit: all `|J|` dyad primes miss the
pool, `|J| · (1 - q)^K`.  This is the quantity the pool note bounds by
`exp (-D^{c+o(1)})`. -/
noncomputable def poolLoss (S : ChildRootPairInputs Ω) (n : ℕ) : ℝ :=
  (S.dyadCard n : ℝ) * (1 - S.hitProb n) ^ S.poolSize n

theorem poolLoss_nonneg (S : ChildRootPairInputs Ω) (n : ℕ) : 0 ≤ S.poolLoss n :=
  mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sub_nonneg.mpr (S.hitProb_le_one n)) _)

/-- **The pool union bound is a subexponential loss.**  With `q ≥ D^{-(c+1)}`
and pool size at least `D^{c+c_dyad+2}`, the product `qK` is at least `D`, so the
miss probability is at most `exp (-D)`, and the polynomial dyad factor
`|J| ≤ D^{c_dyad}` is absorbed: the loss is `D^{-B}` for every `B`.  No factor is
set to one; `|J|`, `q` and `K` all remain explicit. -/
theorem poolLoss_subexp (S : ChildRootPairInputs Ω) : SubexpLoss S.poolLoss := by
  intro B hB
  filter_upwards [S.hitProb_lower, S.dyadCard_le, S.poolSize_ge,
    scale_grows.eventually_ge_atTop 0,
    scale_grows.eventually (eventually_mul_le_exp (B + S.cDyad))] with n hq hcard hK hH0 hdom
  have hH : 0 ≤ scale n := hH0
  have hq0 : 0 ≤ S.hitProb n := (Real.exp_pos _).le.trans hq
  have hq1 : S.hitProb n ≤ 1 := S.hitProb_le_one n
  have hqK : Real.exp (scale n) ≤ S.hitProb n * (S.poolSize n : ℝ) := by
    have hmul := mul_le_mul hq hK (Real.exp_pos _).le hq0
    have hprod : Real.exp (-(S.cPair + 1) * scale n) *
        Real.exp ((S.cPair + S.cDyad + 2) * scale n) =
        Real.exp ((S.cDyad + 1) * scale n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hle : Real.exp (scale n) ≤ Real.exp ((S.cDyad + 1) * scale n) :=
      Real.exp_le_exp.mpr (by nlinarith [S.cDyad_nonneg, hH])
    calc Real.exp (scale n) ≤ Real.exp ((S.cDyad + 1) * scale n) := hle
      _ = Real.exp (-(S.cPair + 1) * scale n) *
            Real.exp ((S.cPair + S.cDyad + 2) * scale n) := hprod.symm
      _ ≤ S.hitProb n * (S.poolSize n : ℝ) := hmul
  have hmiss : (1 - S.hitProb n) ^ S.poolSize n ≤ Real.exp (-Real.exp (scale n)) := by
    have h1 := one_sub_pow_le_exp_neg_mul hq1 (S.poolSize n)
    exact h1.trans (Real.exp_le_exp.mpr (by linarith [hqK]))
  have hprod := mul_le_mul hcard hmiss
    (pow_nonneg (sub_nonneg.mpr hq1) _) (Real.exp_pos _).le
  have hcombine : Real.exp (S.cDyad * scale n) * Real.exp (-Real.exp (scale n)) ≤
      Real.exp (-B * scale n) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : (B + S.cDyad) * scale n ≤ Real.exp (scale n) := hdom
    linarith
  exact hprod.trans hcombine

end ChildRootPairInputs

/-- **The L20.4 inputs.**  The child-root-conditioned top law of
`ChildRootPairInputs`, the G.11/G.12 top step of `G12TopInputs`, and the
deterministic dyad trimming of `DyadExceptionInputs`. -/
structure L20_4Inputs (Ω P : Type*) [Fintype Ω] [DecidableEq P] where
  pair : ChildRootPairInputs Ω
  top : G12TopInputs
  dyad : DyadExceptionInputs P

namespace L20_4Inputs

/-- The L20.4 deficit charged to the C5 `topChildLaw` slot: the pool miss mass of
the dyad, plus the deterministic Markov exceptional fraction of the dyad, plus
the G.12 top bad-child mass.  All three are genuine nonnegative deficits. -/
noncomputable def loss {Ω P : Type*} [Fintype Ω] [DecidableEq P]
    (S : L20_4Inputs Ω P) (n : ℕ) : ℝ :=
  S.pair.poolLoss n + S.dyad.loss n + S.top.top n

theorem loss_nonneg {Ω P : Type*} [Fintype Ω] [DecidableEq P]
    (S : L20_4Inputs Ω P) (n : ℕ) : 0 ≤ S.loss n := by
  unfold L20_4Inputs.loss
  exact add_nonneg (add_nonneg (S.pair.poolLoss_nonneg n) (S.dyad.loss_nonneg n))
    (S.top.top_nonneg n)

/-- **The L20.4 reduction.**  The pool union bound, the dyad Markov trimming and
the G.12 top step are each `D^{-B}` for every `B`, hence their sum is.  This is
the paper's conclusion: the top child law under the incoming-root conditioning
has deficit `D^{-B}` for every `B`. -/
theorem subexpLoss {Ω P : Type*} [Fintype Ω] [DecidableEq P]
    (S : L20_4Inputs Ω P) : SubexpLoss S.loss := by
  have h1 : SubexpLoss fun n => S.pair.poolLoss n + S.dyad.loss n :=
    subexpLoss_add S.pair.poolLoss_subexp S.dyad.loss_subexp
  have h2 : SubexpLoss fun n => (S.pair.poolLoss n + S.dyad.loss n) + S.top.top n :=
    subexpLoss_add h1 S.top.top_subexp
  unfold L20_4Inputs.loss
  exact h2

/-- The `SubexpLeaf` for L20.4 (KB G.12 in the child-root-conditioned law). -/
noncomputable def toSubexpLeaf {Ω P : Type*} [Fintype Ω] [DecidableEq P]
    (S : L20_4Inputs Ω P) : SubexpLeaf where
  loss := S.loss
  loss_nonneg := S.loss_nonneg
  paper := S.subexpLoss

/-- The `B = 2` C5 ledger slot for L20.4. -/
theorem slot_le {Ω P : Type*} [Fintype Ω] [DecidableEq P]
    (S : L20_4Inputs Ω P) :
    ∀ᶠ n : ℕ in atTop, S.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  S.toSubexpLeaf.slot

end L20_4Inputs

/-! ## Axiom audit -/

#print axioms cond_paley_zygmund
#print axioms interior_zero_le_exp
#print axioms top_le_exp_neg
#print axioms G12TopInputs.top_subexp
#print axioms DyadExceptionInputs.loss_subexp
#print axioms ChildRootPairInputs.hitProb_lower
#print axioms ChildRootPairInputs.poolLoss_subexp
#print axioms L20_4Inputs.subexpLoss
#print axioms L20_4Inputs.toSubexpLeaf
#print axioms L20_4Inputs.slot_le

end Cogentic.RandomizedL20_4
