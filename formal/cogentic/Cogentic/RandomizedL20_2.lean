import Cogentic.RandomizedPaperLeafStatements
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option linter.style.haveILetI false

/-!
# L20.2: interior concentration

The manuscript's L20.2 (blueprint §2 C5.a, `[INFRA]`) is the interior
concentration

  `ε_i ≤ D^{-2A}`,  `A = D^{1/48}`,

with moments of growing order.  The KeyBreak inputs are Theorem 3.1,
Proposition G.10 (the diagonal and off-diagonal concentration estimates),
equation (G.8) (the one-point density comparison), Appendix C (the
Hildebrand–Tenenbaum smooth-number saddle point), the truncated geometric CRT
laws, and Lemma G.2 p.106 (the GRH smooth-character sum).

This file decomposes L20.2 into named paper-level inputs and proves the
`ConcentrationLeaf` reduction.  The model is the G.10 proof itself:

* a finite cell with a probability weight `w` on an outcome space `Ω` and a
  finite set of interior points `P`;
* the actual score `f p ω ∈ [0,1]` and its computable proxy `proxy p ω ∈ [0,L]`;
* the ideal mean `μ = ∑ p ∑ ω w ω f p ω`;
* the one-point comparison `∑ p ∑ ω w ω proxy p ω ≤ 2 μ` (G.8);
* the off-diagonal two-point estimate bounded by the CRT plus
  smooth-character error budgets (G.10, Lemma G.2);
* the saddle-point lower bounds `Λ ≥ c D log D` and `μ ≥ exp (η Λ)`
  (Appendix C, Hildebrand–Tenenbaum).

The diagonal estimate of G.10 is *proved*, not assumed: the pointwise algebra
`(f - proxy)² ≤ f + L · proxy` and the one-point comparison give
`diag ≤ (1 + 2L) μ`.  Cauchy–Schwarz then turns the diagonal plus off-diagonal
second moment into the mean discrepancy, and the saddle-point lower bound makes
that discrepancy `D^{-2A}`.

Nothing is a `sorry`, an `admit`, an `axiom`, or `native_decide`; the loss is the
actual normalized mean discrepancy, never zero by fiat.
-/

namespace Cogentic.RandomizedL20_2

open Filter Real
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open scoped BigOperators
open Asymptotics

/-! ## 1. The paper's scales -/

/-- The manuscript's `D = exp (log D)`, with `log D = scale n`. -/
noncomputable def paperD (n : ℕ) : ℝ := exp (scale n)

/-- The manuscript's interior level `A = D^a`. -/
noncomputable def paperA (a : ℝ) (n : ℕ) : ℝ := exp (a * scale n)

theorem paperD_pos (n : ℕ) : 0 < paperD n := exp_pos _

theorem paperA_pos (a : ℝ) (n : ℕ) : 0 < paperA a n := exp_pos _

/-! ## 2. The finite interior cell

This is the object on which G.10's concentration is stated: a finite weighted
outcome space, a finite set of interior points, an actual score in `[0,1]`, and
a proxy score bounded by `L`. -/

/-- The finite data of one interior cell at ledger index `n`, with proxy bound
`L`.  The fields `f_nonneg`, `f_le_one`, `proxy_nonneg`, `proxy_le` are the
pointwise hypotheses of the G.10 diagonal estimate. -/
structure CellData (n : ℕ) (L : ℝ) where
  /-- The outcome space of the conditional law. -/
  Ω : Type
  /-- The outcome space is finite. -/
  [fintypeΩ : Fintype Ω]
  /-- The probability weights. -/
  w : Ω → ℝ
  /-- The weights are nonnegative. -/
  w_nonneg : ∀ ω, 0 ≤ w ω
  /-- The weights sum to one. -/
  w_sum : ∑ ω, w ω = 1
  /-- The finite set of interior points. -/
  P : Type
  /-- The point set is finite. -/
  [fintypeP : Fintype P]
  /-- The point set has decidable equality (for the diagonal/off-diagonal split). -/
  [decEqP : DecidableEq P]
  /-- The actual score. -/
  f : P → Ω → ℝ
  /-- The computable proxy score. -/
  proxy : P → Ω → ℝ
  /-- The actual score is nonnegative. -/
  f_nonneg : ∀ p ω, 0 ≤ f p ω
  /-- The actual score is at most one. -/
  f_le_one : ∀ p ω, f p ω ≤ 1
  /-- The proxy score is nonnegative. -/
  proxy_nonneg : ∀ p ω, 0 ≤ proxy p ω
  /-- The proxy score is at most `L`. -/
  proxy_le : ∀ p ω, proxy p ω ≤ L

namespace CellData

variable {n : ℕ} {L : ℝ} (C : CellData n L)

/-- The weighted mean of a point-indexed score. -/
noncomputable def mean (X : C.P → C.Ω → ℝ) : ℝ :=
  letI : Fintype C.P := C.fintypeP
  letI : Fintype C.Ω := C.fintypeΩ
  ∑ p, ∑ ω, C.w ω * X p ω

/-- The pointwise discrepancy at an outcome. -/
noncomputable def totalDiff (ω : C.Ω) : ℝ :=
  letI : Fintype C.P := C.fintypeP
  ∑ p, (C.f p ω - C.proxy p ω)

/-- The diagonal part of the second moment of the total discrepancy. -/
noncomputable def diag : ℝ :=
  letI : Fintype C.P := C.fintypeP
  letI : Fintype C.Ω := C.fintypeΩ
  ∑ p, ∑ ω, C.w ω * (C.f p ω - C.proxy p ω) ^ 2

/-- The off-diagonal part of the second moment of the total discrepancy. -/
noncomputable def cross : ℝ :=
  letI : Fintype C.P := C.fintypeP
  letI : Fintype C.Ω := C.fintypeΩ
  letI : DecidableEq C.P := C.decEqP
  ∑ p, ∑ q ∈ Finset.univ.erase p,
    ∑ ω, C.w ω * ((C.f p ω - C.proxy p ω) * (C.f q ω - C.proxy q ω))

/-- The full second moment of the total discrepancy. -/
noncomputable def second : ℝ :=
  letI : Fintype C.Ω := C.fintypeΩ
  ∑ ω, C.w ω * (C.totalDiff ω) ^ 2

/-- The mean of the actual score minus the mean of the proxy score is the mean
of the total discrepancy. -/
theorem mean_f_sub_mean_proxy :
    C.mean C.f - C.mean C.proxy =
      letI : Fintype C.Ω := C.fintypeΩ
      ∑ ω, C.w ω * C.totalDiff ω := by
  letI : Fintype C.P := C.fintypeP
  letI : Fintype C.Ω := C.fintypeΩ
  have hf : C.mean C.f = ∑ ω, ∑ p, C.w ω * C.f p ω := by
    unfold mean
    exact Finset.sum_comm
  have hp : C.mean C.proxy = ∑ ω, ∑ p, C.w ω * C.proxy p ω := by
    unfold mean
    exact Finset.sum_comm
  rw [hf, hp, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  rw [show C.w ω * C.totalDiff ω =
      ∑ p, (C.w ω * C.f p ω - C.w ω * C.proxy p ω) by
    unfold totalDiff
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring]
  rw [← Finset.sum_sub_distrib]

/-- Cauchy–Schwarz for a finite weighted mean: the squared mean is at most the
weighted second moment. -/
theorem mean_sq_le_second (X : C.Ω → ℝ) :
    (letI : Fintype C.Ω := C.fintypeΩ
      ∑ ω, C.w ω * X ω) ^ 2 ≤
      letI : Fintype C.Ω := C.fintypeΩ
      ∑ ω, C.w ω * X ω ^ 2 := by
  letI : Fintype C.Ω := C.fintypeΩ
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ)
    (fun ω => Real.sqrt (C.w ω)) (fun ω => Real.sqrt (C.w ω) * X ω)
  have hleft : ∀ ω, Real.sqrt (C.w ω) * (Real.sqrt (C.w ω) * X ω) =
      C.w ω * X ω := by
    intro ω
    calc
      Real.sqrt (C.w ω) * (Real.sqrt (C.w ω) * X ω) =
          (Real.sqrt (C.w ω) * Real.sqrt (C.w ω)) * X ω := by ring
      _ = C.w ω * X ω := by rw [Real.mul_self_sqrt (C.w_nonneg ω)]
  have hright1 : ∑ ω, (Real.sqrt (C.w ω)) ^ 2 = 1 := by
    simp_rw [Real.sq_sqrt (C.w_nonneg _)]
    exact C.w_sum
  have hright2 : ∑ ω, (Real.sqrt (C.w ω) * X ω) ^ 2 =
      ∑ ω, C.w ω * X ω ^ 2 := by
    apply Finset.sum_congr rfl
    intro ω _
    rw [mul_pow, Real.sq_sqrt (C.w_nonneg ω)]
  simp only [hleft, hright1, hright2, one_mul] at hcs
  exact hcs

/-- The second moment splits into the diagonal and off-diagonal sums. -/
theorem second_eq_diag_add_cross : C.second = C.diag + C.cross := by
  letI : Fintype C.P := C.fintypeP
  letI : Fintype C.Ω := C.fintypeΩ
  letI : DecidableEq C.P := C.decEqP
  have hsquare : ∀ ω : C.Ω,
      (∑ p, (C.f p ω - C.proxy p ω)) ^ 2 =
        ∑ p, ∑ q, (C.f p ω - C.proxy p ω) * (C.f q ω - C.proxy q ω) := by
    intro ω
    rw [pow_two, Finset.sum_mul_sum]
  simp only [second, diag, cross, totalDiff, hsquare, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hswap : ∀ p : C.P,
      (∑ ω, ∑ q, C.w ω * ((C.f p ω - C.proxy p ω) *
        (C.f q ω - C.proxy q ω))) =
      ∑ q, ∑ ω, C.w ω * ((C.f p ω - C.proxy p ω) *
        (C.f q ω - C.proxy q ω)) :=
    fun p => Finset.sum_comm
  simp_rw [hswap]
  have hsplit : ∀ p : C.P,
      (∑ q, ∑ ω, C.w ω * ((C.f p ω - C.proxy p ω) *
        (C.f q ω - C.proxy q ω))) =
      (∑ ω, C.w ω * ((C.f p ω - C.proxy p ω) * (C.f p ω - C.proxy p ω))) +
        ∑ q ∈ Finset.univ.erase p,
          ∑ ω, C.w ω * ((C.f p ω - C.proxy p ω) *
            (C.f q ω - C.proxy q ω)) := by
    intro p
    exact (Finset.add_sum_erase (Finset.univ)
      (fun q => ∑ ω, C.w ω * ((C.f p ω - C.proxy p ω) *
        (C.f q ω - C.proxy q ω))) (Finset.mem_univ p)).symm
  simp_rw [hsplit, Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro ω _
    ring

/-- The pointwise diagonal inequality of G.10:
`(f - proxy)² ≤ f + L · proxy` for `0 ≤ f ≤ 1` and `0 ≤ proxy ≤ L`. -/
theorem pointwise_sq_sub_le {f d L : ℝ} (hf0 : 0 ≤ f) (hf1 : f ≤ 1)
    (hd0 : 0 ≤ d) (hdL : d ≤ L) :
    (f - d) ^ 2 ≤ f + L * d := by
  have h1 : 0 ≤ f * (1 - f) := mul_nonneg hf0 (by linarith)
  have h2 : 0 ≤ d * (L - d) := mul_nonneg hd0 (by linarith)
  have h3 : 0 ≤ 2 * f * d := by positivity
  nlinarith only [h1, h2, h3]

/-- The diagonal estimate of G.10, proved from the pointwise inequality and the
one-point comparison `mean proxy ≤ 2 μ`: `diag ≤ (1 + 2L) μ`. -/
theorem diag_le (hL : 0 ≤ L) {μ : ℝ}
    (hproxy : C.mean C.proxy ≤ 2 * μ) (hμ : μ = C.mean C.f) :
    C.diag ≤ (1 + 2 * L) * μ := by
  letI : Fintype C.P := C.fintypeP
  letI : Fintype C.Ω := C.fintypeΩ
  have hpoint : ∀ p ω, C.w ω * (C.f p ω - C.proxy p ω) ^ 2 ≤
      C.w ω * (C.f p ω + L * C.proxy p ω) := by
    intro p ω
    exact mul_le_mul_of_nonneg_left
      (pointwise_sq_sub_le (C.f_nonneg p ω) (C.f_le_one p ω)
        (C.proxy_nonneg p ω) (C.proxy_le p ω)) (C.w_nonneg ω)
  have hdiag : C.diag ≤ C.mean C.f + L * C.mean C.proxy := by
    calc
      C.diag = ∑ p, ∑ ω, C.w ω * (C.f p ω - C.proxy p ω) ^ 2 := rfl
      _ ≤ ∑ p, ∑ ω, C.w ω * (C.f p ω + L * C.proxy p ω) :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun ω _ => hpoint p ω
      _ = C.mean C.f + L * C.mean C.proxy := by
        unfold mean
        simp_rw [mul_add, Finset.sum_add_distrib]
        congr 1
        conv_rhs => rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        conv_rhs => rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω _
        ring
  calc
    C.diag ≤ C.mean C.f + L * C.mean C.proxy := hdiag
    _ ≤ μ + L * (2 * μ) := by
      rw [← hμ]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hproxy hL)
    _ = (1 + 2 * L) * μ := by ring

/-- The mean discrepancy is controlled by the second moment. -/
theorem abs_mean_diff_sq_le_second :
    (C.mean C.f - C.mean C.proxy) ^ 2 ≤ C.second := by
  letI : Fintype C.Ω := C.fintypeΩ
  have hmean := C.mean_f_sub_mean_proxy
  rw [hmean]
  simpa only [second] using C.mean_sq_le_second C.totalDiff

end CellData

/-! ## 3. Paper-level sub-lemmas -/

/-- **Appendix C / Hildebrand–Tenenbaum saddle point, scale part.**  The
interior mean scale `Λ` dominates `c · D log D` with an explicit positive
constant `c`. -/
def SaddlePointScaleLower (Λ : ℕ → ℝ) (c : ℝ) : Prop :=
  0 < c ∧ ∀ n, c * paperD n * scale n ≤ Λ n

/-- **Appendix C / Hildebrand–Tenenbaum saddle point, mean part.**  The ideal
mean is at least `exp (η Λ)` for an explicit positive `η`; this is the
`μ ≥ exp (η Λ_d)` lower bound used in the G.10 diagonal estimate. -/
def SaddlePointMeanLower (μ Λ : ℕ → ℝ) (η : ℝ) : Prop :=
  0 < η ∧ ∀ n, exp (η * Λ n) ≤ μ n

/-- **Truncated geometric CRT law.**  The CRT refinement of the geometric
progression contributes a total-variation error `crtError` bounded by
`exp (-c · D log D)`.  This is the paper's truncated geometric CRT input; the
reduction consumes only its error budget, not the distributional identity. -/
def TruncatedGeometricCRTLaw (crtError : ℕ → ℝ) (c : ℝ) : Prop :=
  0 < c ∧ ∀ n, 0 ≤ crtError n ∧ crtError n ≤ exp (-c * paperD n * scale n)

/-- **Lemma G.2 p.106 / GRH smooth-character sums.**  The smooth-character sums
that control the off-diagonal two-point terms are bounded by
`exp (-c · D log D)`.  This is the sharp GRH input (Harper/Soundararajan type)
recorded at the manuscript's rate. -/
def SmoothCharacterSumBound (charError : ℕ → ℝ) (c : ℝ) : Prop :=
  0 < c ∧ ∀ n, 0 ≤ charError n ∧ charError n ≤ exp (-c * paperD n * scale n)

/-- **G.8 one-point density comparison.**  The proxy mean is at most twice the
actual interior mean.  This is the one-point comparison that makes the
diagonal estimate run. -/
def OnePointProxyComparison (proxyMean μ : ℕ → ℝ) : Prop :=
  ∀ n, proxyMean n ≤ 2 * μ n

/-- **G.10 off-diagonal two-point estimate.**  The off-diagonal part of the
second moment is at most the CRT plus smooth-character error budget times
`μ²`.  The reduction uses this estimate and proves the diagonal part itself. -/
def TwoPointOffDiagonalBound (cross μ crtError charError : ℕ → ℝ) : Prop :=
  ∀ n, cross n ≤ (crtError n + charError n) * μ n ^ 2

/-! ## 4. The decomposed L20.2 inputs -/

/-- The paper-level L20.2 inputs.  Every analytic field is a named manuscript
estimate: the saddle point (Appendix C), the truncated geometric CRT law, the
GRH smooth-character sum (Lemma G.2), the one-point comparison (G.8), and the
off-diagonal two-point estimate (G.10).  The finite cells are the conditional
laws on which G.10 operates. -/
structure L20_2Inputs where
  /-- The interior exponent `a` in `A = D^a`; the paper has `a = 1/48`. -/
  a : ℝ
  /-- The manuscript value `a = 1/48`. -/
  a_eq : a = 1 / 48
  /-- The saddle-point scale `Λ_d`. -/
  Λ : ℕ → ℝ
  /-- The ideal interior mean `μ`. -/
  μ : ℕ → ℝ
  /-- The proxy score bound `L`. -/
  L : ℕ → ℝ
  /-- The CRT error budget. -/
  crtError : ℕ → ℝ
  /-- The smooth-character error budget. -/
  charError : ℕ → ℝ
  /-- The constant in `Λ ≥ c D log D`. -/
  cLam : ℝ
  /-- The constant in `μ ≥ exp (η Λ)`. -/
  η : ℝ
  /-- The CRT decay constant. -/
  cCRT : ℝ
  /-- The smooth-character decay constant. -/
  cChar : ℝ
  /-- The polynomial exponent constant in `L ≤ exp (cL (log D)^5)`. -/
  cL : ℝ
  /-- Appendix C, scale part. -/
  saddle_scale : SaddlePointScaleLower Λ cLam
  /-- Appendix C, mean part. -/
  saddle_mean : SaddlePointMeanLower μ Λ η
  /-- `L` is nonnegative. -/
  L_nonneg : ∀ n, 0 ≤ L n
  /-- The polynomial exponent constant is nonnegative. -/
  cL_nonneg : 0 ≤ cL
  /-- The G.10 proxy bound is polynomial in `log D`: `L ≤ exp (cL (log D)^5)`.
  This is the paper's `L ≤ exp (O(A (log D)^2))` with `A = O((log D)^3)`. -/
  L_upper : ∀ n, L n ≤ exp (cL * (scale n) ^ 5)
  /-- The truncated geometric CRT law. -/
  crt_law : TruncatedGeometricCRTLaw crtError cCRT
  /-- The GRH smooth-character sum. -/
  char_sum : SmoothCharacterSumBound charError cChar
  /-- The finite interior cell at each ledger index. -/
  cell : ∀ n, CellData n (L n)
  /-- The ideal mean is the actual mean of the cell. -/
  μ_eq : ∀ n, μ n = (cell n).mean (cell n).f
  /-- G.8 one-point comparison. -/
  one_point : OnePointProxyComparison (fun n => (cell n).mean (cell n).proxy) μ
  /-- G.10 off-diagonal two-point estimate. -/
  two_point : TwoPointOffDiagonalBound
    (fun n => (cell n).cross) μ crtError charError

namespace L20_2Inputs

variable (I : L20_2Inputs)

/-- `a > 0`. -/
theorem a_pos : 0 < I.a := by
  rw [I.a_eq]
  norm_num

/-- `a < 1`. -/
theorem a_lt_one : I.a < 1 := by
  rw [I.a_eq]
  norm_num

/-- The interior level `A = D^a`. -/
noncomputable def A (n : ℕ) : ℝ := paperA I.a n

/-- The ideal mean is positive. -/
theorem μ_pos (n : ℕ) : 0 < I.μ n :=
  (exp_pos (I.η * I.Λ n)).trans_le (I.saddle_mean.2 n)

/-- The CRT plus smooth-character error budget `ρ`. -/
noncomputable def ρ (n : ℕ) : ℝ := I.crtError n + I.charError n

theorem ρ_nonneg (n : ℕ) : 0 ≤ I.ρ n :=
  add_nonneg (I.crt_law.2 n).1 (I.char_sum.2 n).1

/-- The L20.2 loss: the normalized discrepancy between the actual interior mean
and the proxy mean.  This is a genuine concentration error, not a placeholder. -/
noncomputable def loss (n : ℕ) : ℝ :=
  |(I.cell n).mean (I.cell n).f - (I.cell n).mean (I.cell n).proxy| / I.μ n

theorem loss_nonneg (n : ℕ) : 0 ≤ I.loss n :=
  div_nonneg (abs_nonneg _) (I.μ_pos n).le

/-! ### 5. Arithmetic: the saddle point beats the G.10 error budgets -/

/-- `(scale n)^k` is eventually at most any positive multiple of
`exp (c · scale n)`. -/
theorem eventually_pow_le_const_mul_exp {k : ℕ} {c ε : ℝ} (hc : 0 < c)
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (scale n) ^ k ≤ ε * exp (c * scale n) := by
  have h := (isLittleO_pow_exp_pos_mul_atTop k hc).def hε
  have h' := scale_grows.eventually h
  filter_upwards [h', scale_grows.eventually_ge_atTop 0] with n hn hs
  have hnk : 0 ≤ (scale n) ^ k := pow_nonneg hs k
  have hexp : 0 ≤ exp (c * scale n) := (exp_pos _).le
  rw [Real.norm_of_nonneg hnk, Real.norm_of_nonneg hexp] at hn
  exact hn

/-- A fixed constant is eventually at most any positive multiple of
`exp (scale n) · scale n`. -/
theorem eventually_const_le_exp_mul {c d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, c ≤ d * (paperD n * scale n) := by
  have h1 : ∀ᶠ n : ℕ in atTop, max c 0 / d ≤ scale n :=
    scale_grows.eventually_ge_atTop (max c 0 / d)
  filter_upwards [h1, scale_grows.eventually_ge_atTop 0] with n hn hs
  have hmax : max c 0 ≤ d * scale n := by
    calc
      max c 0 = d * (max c 0 / d) := by field_simp
      _ ≤ d * scale n := mul_le_mul_of_nonneg_left hn hd.le
  have hexp : 1 ≤ paperD n := by
    unfold paperD
    exact one_le_exp hs
  have hstep : d * scale n ≤ d * (paperD n * scale n) := by
    apply mul_le_mul_of_nonneg_left _ hd.le
    nlinarith only [hexp, hs]
  exact (le_max_left c 0).trans (hmax.trans hstep)

/-- `exp (a · scale n) · scale n` is eventually at most any positive multiple of
`exp (scale n) · scale n` when `a < 1`. -/
theorem eventually_exp_mul_le_exp_mul {a : ℝ} (ha : a < 1) {c : ℝ}
    (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      exp (a * scale n) * scale n ≤ c * (paperD n * scale n) := by
  have hd : 0 < 1 - a := sub_pos.mpr ha
  have hratio : Tendsto (fun n : ℕ => exp ((1 - a) * scale n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (scale_grows.const_mul_atTop hd)
  have hbig : ∀ᶠ n : ℕ in atTop,
      1 / c ≤ exp ((1 - a) * scale n) :=
    hratio.eventually_ge_atTop (1 / c)
  filter_upwards [hbig, scale_grows.eventually_ge_atTop 0] with n hn hs
  have h1 : 1 ≤ c * exp ((1 - a) * scale n) := by
    have := (div_le_iff₀ hc).mp hn
    simpa only [mul_comm] using this
  have hnonneg : 0 ≤ exp (a * scale n) * scale n :=
    mul_nonneg (exp_pos _).le hs
  have hexp_split : exp (scale n) =
      exp ((1 - a) * scale n) * exp (a * scale n) := by
    rw [← exp_add]
    congr 1
    ring
  calc
    exp (a * scale n) * scale n ≤
        (c * exp ((1 - a) * scale n)) * (exp (a * scale n) * scale n) :=
      le_mul_of_one_le_left hnonneg h1
    _ = c * (paperD n * scale n) := by
      unfold paperD
      rw [hexp_split]
      ring

/-- The exponent budget for the diagonal term: the polynomial proxy bound and
the interior level `A` are both absorbed by the saddle-point mean. -/
theorem eventually_diagonal_budget :
    ∀ᶠ n : ℕ in atTop,
      Real.log 3 + I.cL * (scale n) ^ 5 + Real.log 2 +
        4 * I.A n * scale n ≤
        I.η * I.cLam * (paperD n * scale n) := by
  have hK : 0 < I.η * I.cLam := mul_pos I.saddle_mean.1 I.saddle_scale.1
  have hK4 : 0 < I.η * I.cLam / 4 := by positivity
  -- constants
  have hconst : ∀ᶠ n : ℕ in atTop,
      Real.log 3 + Real.log 2 ≤
        (I.η * I.cLam / 4) * (paperD n * scale n) :=
    eventually_const_le_exp_mul (c := Real.log 3 + Real.log 2) hK4
  -- `cL * H^5`
  have hpow : ∀ᶠ n : ℕ in atTop,
      I.cL * (scale n) ^ 5 ≤
        (I.η * I.cLam / 4) * (paperD n * scale n) := by
    rcases eq_or_lt_of_le I.cL_nonneg with hcL | hcL
    · filter_upwards [scale_grows.eventually_ge_atTop 0] with n hs
      rw [← hcL, zero_mul]
      exact mul_nonneg (by positivity) (mul_nonneg (paperD_pos n).le hs)
    · have hε : 0 < (I.η * I.cLam) / (4 * I.cL) :=
        div_pos hK (by positivity)
      have hsmall := eventually_pow_le_const_mul_exp (k := 4) (c := 1)
        zero_lt_one hε
      filter_upwards [hsmall, scale_grows.eventually_ge_atTop 1] with n hn hs
      have hpow5 : (scale n) ^ 5 = (scale n) ^ 4 * scale n := by ring
      have hmul : (scale n) ^ 4 * scale n ≤
          ((I.η * I.cLam) / (4 * I.cL)) * exp (1 * scale n) * scale n :=
        mul_le_mul_of_nonneg_right (by simpa using hn) (by linarith only [hs])
      have hfac : I.cL * (((I.η * I.cLam) / (4 * I.cL)) *
          exp (1 * scale n) * scale n) =
          (I.η * I.cLam / 4) * (exp (1 * scale n) * scale n) := by
        field_simp [hcL.ne']
      have hrew : paperD n * scale n = exp (1 * scale n) * scale n := by
        unfold paperD
        ring_nf
      calc
        I.cL * (scale n) ^ 5 = I.cL * ((scale n) ^ 4 * scale n) := by rw [hpow5]
        _ ≤ I.cL * (((I.η * I.cLam) / (4 * I.cL)) *
              exp (1 * scale n) * scale n) :=
          mul_le_mul_of_nonneg_left hmul I.cL_nonneg
        _ = (I.η * I.cLam / 4) * (exp (1 * scale n) * scale n) := hfac
        _ = (I.η * I.cLam / 4) * (paperD n * scale n) := by rw [hrew]
  -- `4 A H`
  have hA : ∀ᶠ n : ℕ in atTop,
      4 * I.A n * scale n ≤
        (I.η * I.cLam / 4) * (paperD n * scale n) := by
    have hsmall := eventually_exp_mul_le_exp_mul (a := I.a) I.a_lt_one
      (c := (I.η * I.cLam) / 16) (by positivity)
    filter_upwards [hsmall] with n hn
    calc
      4 * I.A n * scale n = 4 * (exp (I.a * scale n) * scale n) := by
        unfold A paperA
        ring
      _ ≤ 4 * (((I.η * I.cLam) / 16) * (paperD n * scale n)) :=
        mul_le_mul_of_nonneg_left hn (by norm_num)
      _ = (I.η * I.cLam / 4) * (paperD n * scale n) := by ring
  filter_upwards [hconst, hpow, hA, scale_grows.eventually_ge_atTop 0] with n hc hp hA' hs
  have hsum : Real.log 3 + Real.log 2 + I.cL * (scale n) ^ 5 +
      4 * I.A n * scale n ≤
      3 * ((I.η * I.cLam / 4) * (paperD n * scale n)) := by
    linarith only [hc, hp, hA']
  have hnonneg : 0 ≤ (I.η * I.cLam / 4) * (paperD n * scale n) :=
    mul_nonneg (by positivity) (mul_nonneg (paperD_pos n).le hs)
  nlinarith only [hsum, hnonneg, hK]

/-- The exponent budget for the CRT plus smooth-character term. -/
theorem eventually_offdiagonal_budget :
    ∀ᶠ n : ℕ in atTop,
      2 * Real.log 2 + 4 * I.A n * scale n ≤
        min I.cCRT I.cChar * (paperD n * scale n) := by
  have hcpos : 0 < min I.cCRT I.cChar := lt_min I.crt_law.1 I.char_sum.1
  have hhalf : 0 < min I.cCRT I.cChar / 2 := by positivity
  have hconst : ∀ᶠ n : ℕ in atTop,
      2 * Real.log 2 ≤ (min I.cCRT I.cChar / 2) * (paperD n * scale n) :=
    eventually_const_le_exp_mul (c := 2 * Real.log 2) hhalf
  have hA : ∀ᶠ n : ℕ in atTop,
      4 * I.A n * scale n ≤
        (min I.cCRT I.cChar / 2) * (paperD n * scale n) := by
    have hsmall := eventually_exp_mul_le_exp_mul (a := I.a) I.a_lt_one
      (c := min I.cCRT I.cChar / 8) (by positivity)
    filter_upwards [hsmall] with n hn
    calc
      4 * I.A n * scale n = 4 * (exp (I.a * scale n) * scale n) := by
        unfold A paperA
        ring
      _ ≤ 4 * ((min I.cCRT I.cChar / 8) * (paperD n * scale n)) :=
        mul_le_mul_of_nonneg_left hn (by norm_num)
      _ = (min I.cCRT I.cChar / 2) * (paperD n * scale n) := by ring
  filter_upwards [hconst, hA] with n hc hA'
  linarith only [hc, hA']

/-! ### 6. From the finite cell to the concentration loss -/

/-- The squared mean discrepancy is bounded by the G.10 diagonal plus
off-diagonal second-moment budgets. -/
theorem mean_diff_sq_le (n : ℕ) :
    ((I.cell n).mean (I.cell n).f - (I.cell n).mean (I.cell n).proxy) ^ 2 ≤
      (1 + 2 * I.L n) * I.μ n + I.ρ n * I.μ n ^ 2 := by
  have hsecond := (I.cell n).abs_mean_diff_sq_le_second
  rw [(I.cell n).second_eq_diag_add_cross] at hsecond
  have hdiag := (I.cell n).diag_le (I.L_nonneg n) (I.one_point n) (I.μ_eq n)
  have hcross : (I.cell n).cross ≤ I.ρ n * I.μ n ^ 2 := by
    simpa only [ρ] using I.two_point n
  linarith only [hsecond, hdiag, hcross]

/-- The polynomial proxy factor `1 + 2L` is at most `exp (log 3 + cL H^5)`. -/
theorem eventually_one_add_two_L_le :
    ∀ᶠ n : ℕ in atTop,
      1 + 2 * I.L n ≤ exp (Real.log 3 + I.cL * (scale n) ^ 5) := by
  filter_upwards [scale_grows.eventually_ge_atTop 0] with n hs
  have hpow : 0 ≤ (scale n) ^ 5 := pow_nonneg hs 5
  have hexp1 : 1 ≤ exp (I.cL * (scale n) ^ 5) :=
    one_le_exp (mul_nonneg I.cL_nonneg hpow)
  have hL := I.L_upper n
  have h3 : 1 + 2 * I.L n ≤ 3 * exp (I.cL * (scale n) ^ 5) := by
    nlinarith only [hL, hexp1]
  have hlog3 : (3 : ℝ) = exp (Real.log 3) := (exp_log (by norm_num)).symm
  calc
    1 + 2 * I.L n ≤ 3 * exp (I.cL * (scale n) ^ 5) := h3
    _ = exp (Real.log 3) * exp (I.cL * (scale n) ^ 5) := by
      nth_rewrite 1 [hlog3]
      rfl
    _ = exp (Real.log 3 + I.cL * (scale n) ^ 5) := by rw [← exp_add]

/-- The diagonal term: the saddle-point mean dominates the polynomial proxy
factor. -/
theorem eventually_diagonal_term_le :
    ∀ᶠ n : ℕ in atTop,
      (1 + 2 * I.L n) / I.μ n ≤
        (1 / 2) * exp (-4 * I.A n * scale n) := by
  filter_upwards [I.eventually_diagonal_budget, I.eventually_one_add_two_L_le]
    with n hb hL
  set E : ℝ := Real.log 3 + I.cL * (scale n) ^ 5
  set F : ℝ := I.η * I.cLam * (paperD n * scale n)
  have hLam : I.cLam * (paperD n * scale n) ≤ I.Λ n := by
    simpa only [mul_assoc] using I.saddle_scale.2 n
  have hFmu : exp F ≤ I.μ n := by
    calc
      exp F = exp (I.η * (I.cLam * (paperD n * scale n))) := by
        congr 1
        dsimp only [F]
        ring
      _ ≤ exp (I.η * I.Λ n) := by
        apply exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hLam I.saddle_mean.1.le
      _ ≤ I.μ n := I.saddle_mean.2 n
  have hnum_nonneg : 0 ≤ 1 + 2 * I.L n := by nlinarith only [I.L_nonneg n]
  have hinv : (I.μ n)⁻¹ ≤ (exp F)⁻¹ := by
    exact inv_anti₀ (exp_pos F) hFmu
  have hquot : (1 + 2 * I.L n) / I.μ n ≤ exp E / exp F := by
    calc
      (1 + 2 * I.L n) / I.μ n = (1 + 2 * I.L n) * (I.μ n)⁻¹ := by
        rw [div_eq_mul_inv]
      _ ≤ exp E * (exp F)⁻¹ :=
        mul_le_mul hL hinv (inv_nonneg.mpr (I.μ_pos n).le) (exp_pos E).le
      _ = exp E / exp F := by rw [div_eq_mul_inv]
  have hbudget : E - F ≤ -Real.log 2 - 4 * I.A n * scale n := by
    dsimp only [E, F] at hb ⊢
    linarith only [hb]
  calc
    (1 + 2 * I.L n) / I.μ n ≤ exp E / exp F := hquot
    _ = exp (E - F) := (exp_sub E F).symm
    _ ≤ exp (-Real.log 2 - 4 * I.A n * scale n) := exp_le_exp.mpr hbudget
    _ = (1 / 2) * exp (-4 * I.A n * scale n) := by
      rw [show -Real.log 2 - 4 * I.A n * scale n =
        -Real.log 2 + (-4 * I.A n * scale n) by ring, exp_add]
      have hhalf : exp (-Real.log 2) = (1 / 2 : ℝ) := by
        rw [exp_neg, exp_log (by norm_num)]
        norm_num
      rw [hhalf]

/-- The CRT plus smooth-character term is at most half the target concentration
budget. -/
theorem eventually_rho_le :
    ∀ᶠ n : ℕ in atTop,
      I.ρ n ≤ (1 / 2) * exp (-4 * I.A n * scale n) := by
  filter_upwards [I.eventually_offdiagonal_budget, scale_grows.eventually_ge_atTop 0]
    with n hb hs
  have hX : 0 ≤ paperD n * scale n := mul_nonneg (paperD_pos n).le hs
  have hcrt : I.crtError n ≤
      exp (-(min I.cCRT I.cChar) * (paperD n * scale n)) := by
    refine (I.crt_law.2 n).2.trans ?_
    apply exp_le_exp.mpr
    have hle : min I.cCRT I.cChar ≤ I.cCRT := min_le_left _ _
    nlinarith only [mul_le_mul_of_nonneg_right hle hX]
  have hchar : I.charError n ≤
      exp (-(min I.cCRT I.cChar) * (paperD n * scale n)) := by
    refine (I.char_sum.2 n).2.trans ?_
    apply exp_le_exp.mpr
    have hle : min I.cCRT I.cChar ≤ I.cChar := min_le_right _ _
    nlinarith only [mul_le_mul_of_nonneg_right hle hX]
  have h2 : I.ρ n ≤ 2 * exp (-(min I.cCRT I.cChar) *
      (paperD n * scale n)) := by
    unfold ρ
    calc
      I.crtError n + I.charError n ≤
          exp (-(min I.cCRT I.cChar) * (paperD n * scale n)) +
            exp (-(min I.cCRT I.cChar) * (paperD n * scale n)) :=
        add_le_add hcrt hchar
      _ = 2 * exp (-(min I.cCRT I.cChar) * (paperD n * scale n)) := by ring
  have hlog2 : (2 : ℝ) = exp (Real.log 2) := (exp_log (by norm_num)).symm
  have hrho : I.ρ n ≤ exp (Real.log 2 -
      (min I.cCRT I.cChar) * (paperD n * scale n)) := by
    calc
      I.ρ n ≤ 2 * exp (-(min I.cCRT I.cChar) * (paperD n * scale n)) := h2
      _ = exp (Real.log 2) * exp (-(min I.cCRT I.cChar) *
            (paperD n * scale n)) := by
        nth_rewrite 1 [hlog2]
        rfl
      _ = exp (Real.log 2 - (min I.cCRT I.cChar) *
            (paperD n * scale n)) := by
        rw [← exp_add]
        ring_nf
  have hbudget : Real.log 2 - (min I.cCRT I.cChar) * (paperD n * scale n) ≤
      -Real.log 2 - 4 * I.A n * scale n := by
    nlinarith only [hb]
  calc
    I.ρ n ≤ exp (Real.log 2 -
        (min I.cCRT I.cChar) * (paperD n * scale n)) := hrho
    _ ≤ exp (-Real.log 2 - 4 * I.A n * scale n) := exp_le_exp.mpr hbudget
    _ = (1 / 2) * exp (-4 * I.A n * scale n) := by
      rw [show -Real.log 2 - 4 * I.A n * scale n =
        -Real.log 2 + (-4 * I.A n * scale n) by ring, exp_add]
      have hhalf : exp (-Real.log 2) = (1 / 2 : ℝ) := by
        rw [exp_neg, exp_log (by norm_num)]
        norm_num
      rw [hhalf]

/-- The normalized G.10 error is at most the `D^{-4A}` budget. -/
theorem eventually_normalized_error_le :
    ∀ᶠ n : ℕ in atTop,
      (1 + 2 * I.L n) / I.μ n + I.ρ n ≤
        exp (-4 * I.A n * scale n) := by
  filter_upwards [I.eventually_diagonal_term_le, I.eventually_rho_le] with n h1 h2
  calc
    (1 + 2 * I.L n) / I.μ n + I.ρ n ≤
        (1 / 2) * exp (-4 * I.A n * scale n) +
          (1 / 2) * exp (-4 * I.A n * scale n) := add_le_add h1 h2
    _ = exp (-4 * I.A n * scale n) := by ring

/-- Multiplying by `μ²` gives the unnormalized `D^{-4A}` second-moment budget. -/
theorem eventually_error_le :
    ∀ᶠ n : ℕ in atTop,
      (1 + 2 * I.L n) * I.μ n + I.ρ n * I.μ n ^ 2 ≤
        exp (-4 * I.A n * scale n) * I.μ n ^ 2 := by
  filter_upwards [I.eventually_normalized_error_le] with n hn
  have hmul := mul_le_mul_of_nonneg_right hn (sq_nonneg (I.μ n))
  have hμ : I.μ n ≠ 0 := (I.μ_pos n).ne'
  calc
    (1 + 2 * I.L n) * I.μ n + I.ρ n * I.μ n ^ 2 =
        ((1 + 2 * I.L n) / I.μ n + I.ρ n) * I.μ n ^ 2 := by
      field_simp [hμ]
    _ ≤ exp (-4 * I.A n * scale n) * I.μ n ^ 2 := hmul

/-- **L20.2 paper statement.**  The normalized discrepancy is at most
`D^{-2A}` with `A = D^a`. -/
theorem loss_le_paper :
    ∀ᶠ n : ℕ in atTop,
      I.loss n ≤ exp (-2 * I.A n * scale n) := by
  filter_upwards [I.eventually_error_le] with n hsmall
  have hsq := I.mean_diff_sq_le n
  have hsq' : ((I.cell n).mean (I.cell n).f -
      (I.cell n).mean (I.cell n).proxy) ^ 2 ≤
      exp (-4 * I.A n * scale n) * I.μ n ^ 2 := hsq.trans hsmall
  have hexp_sq : (exp (-2 * I.A n * scale n)) ^ 2 =
      exp (-4 * I.A n * scale n) := by
    rw [pow_two, ← exp_add]
    congr 1
    ring
  have hsquare : exp (-4 * I.A n * scale n) * I.μ n ^ 2 =
      (exp (-2 * I.A n * scale n) * I.μ n) ^ 2 := by
    rw [mul_pow, hexp_sq]
  have habs : |(I.cell n).mean (I.cell n).f -
      (I.cell n).mean (I.cell n).proxy| ≤
      exp (-2 * I.A n * scale n) * I.μ n := by
    apply abs_le_of_sq_le_sq
    · rw [← hsquare]
      exact hsq'
    · exact mul_nonneg (exp_pos _).le (I.μ_pos n).le
  unfold loss
  rw [div_le_iff₀ (I.μ_pos n)]
  exact habs

end L20_2Inputs

/-! ## 7. The `ConcentrationLeaf` reduction and the paper bundle -/

namespace L20_2Inputs

variable (I : L20_2Inputs)

/-- **The L20.2 `ConcentrationLeaf`.**  The loss is the actual normalized mean
discrepancy and `a = 1/48`. -/
noncomputable def toConcentrationLeaf : ConcentrationLeaf where
  loss := I.loss
  loss_nonneg := I.loss_nonneg
  a := I.a
  a_pos := I.a_pos
  paper := by
    filter_upwards [I.loss_le_paper] with n hn
    simpa only [A, paperA] using hn

/-- The `B = 2` instance is exactly the `C5Inputs.interiorConcentration` slot. -/
theorem slot_le :
    ∀ᶠ n : ℕ in atTop,
      I.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  I.toConcentrationLeaf.slot

/-- Replace the L20.2 field of a `PaperAnalyticAssumptions` bundle by the
decomposed implementation.  Every other leaf and the epoch family are untouched. -/
noncomputable def replacePaperLeaf
    {E : ∀ n, 3 ≤ n → Cogentic.RandomizedEpochAssembly.HardEpochData n} {C : ℝ}
    (P : PaperAnalyticAssumptions E C) (I : L20_2Inputs) :
    PaperAnalyticAssumptions E C :=
  { P with l20_2 := I.toConcentrationLeaf }

/-- The replaced bundle's interior-concentration slot is exactly the L20.2
`B = 2` loss bound. -/
theorem replacePaperLeaf_slot
    {E : ∀ n, 3 ≤ n → Cogentic.RandomizedEpochAssembly.HardEpochData n} {C : ℝ}
    (P : PaperAnalyticAssumptions E C) (I : L20_2Inputs) :
    ∀ᶠ n : ℕ in atTop,
      (replacePaperLeaf P I).slots .interiorConcentration n ≤
        exp (-(2 : ℝ) * scale n) :=
  PaperAnalyticAssumptions.slot_le (replacePaperLeaf P I) .interiorConcentration

end L20_2Inputs

/-! ## Axiom audit -/

#print axioms CellData.mean_f_sub_mean_proxy
#print axioms CellData.mean_sq_le_second
#print axioms CellData.second_eq_diag_add_cross
#print axioms CellData.pointwise_sq_sub_le
#print axioms CellData.diag_le
#print axioms CellData.abs_mean_diff_sq_le_second
#print axioms L20_2Inputs.eventually_pow_le_const_mul_exp
#print axioms L20_2Inputs.eventually_const_le_exp_mul
#print axioms L20_2Inputs.eventually_exp_mul_le_exp_mul
#print axioms L20_2Inputs.eventually_diagonal_budget
#print axioms L20_2Inputs.eventually_offdiagonal_budget
#print axioms L20_2Inputs.mean_diff_sq_le
#print axioms L20_2Inputs.eventually_one_add_two_L_le
#print axioms L20_2Inputs.eventually_diagonal_term_le
#print axioms L20_2Inputs.eventually_rho_le
#print axioms L20_2Inputs.eventually_normalized_error_le
#print axioms L20_2Inputs.eventually_error_le
#print axioms L20_2Inputs.loss_le_paper
#print axioms L20_2Inputs.toConcentrationLeaf
#print axioms L20_2Inputs.slot_le
#print axioms L20_2Inputs.replacePaperLeaf
#print axioms L20_2Inputs.replacePaperLeaf_slot

end Cogentic.RandomizedL20_2
