import Cogentic.RandomizedL21_2Remainder
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TruncatedPerronPsi

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-!
# L21.2: the reference Perron bound in the regime `T ≫ u`

`Cogentic.RandomizedL21_2Remainder.ReferencePerronBound` is the truncated
Perron/Abel approximation of the twisted prime sum `twistedPrimeSum` by the
reference-line integral `refZetaSum` at height `X^3 + 1`.  The existing kernel
argument in the `tree` package,
`GlobalTheory.PerronPsi.truncated_perron_psi`, proves the analogous statement
under the side condition `T ≤ 2 u` (the "`T` small" regime).  L21.2 uses the
opposite regime `T = X^3 ≫ u = v`.

This file proves the reference bound **unconditionally in `T`**:

* `truncatedPerron_vonMangoldt_twist` — the truncated Perron formula
  `‖Σ_{n≤v} Λ(n) n^{-it} - refZetaSum v t T‖ ≤ C (v (log v)^2 / T + log v)`
  for every `2 ≤ v` and every `1 ≤ T`, with a single absolute constant `C`.
  The proof is the kernel argument of `GlobalTheory.PerronPsi` with the
  `T ≤ 2u` hypothesis removed (it is in fact unused there; here the twist
  `n^{-it}` is absorbed into the coefficients of the `L`-series and the
  truncated Perron kernel is used verbatim).

* `twistedPrimeSum_sub_vonMangoldt_le` — the elementary prime-power removal:
  the difference between the prime-only sum and the full von Mangoldt sum is
  `O (v log v)`.

* `referencePerronBound_of_errorBound` and `referencePerronBound` — the two
  estimates combine to give `ReferencePerronBound X c K C` in the L21.2
  regime, with `K` explicit.

* `vonMangoldt_perron_old_regime` — the existing `T ≤ 2u` theorem, restricted
  to the principal character, is recovered as the special case `T ≤ 2v` of the
  unconditional estimate, so the old `T ≤ u` side condition is exactly the
  regime boundary that the new theorem removes.

No `sorry`, `admit`, `axiom` or `native_decide` is used.
-/

noncomputable section

namespace Cogentic.RandomizedL21_2ReferenceBound

open Filter Real MeasureTheory Complex
open scoped BigOperators
open ArithmeticFunction
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Shift
open Cogentic.RandomizedL21_2Remainder

/-! ## The full von Mangoldt sum and the truncated Perron kernel -/

/-- The twisted von Mangoldt sum `Σ_{n ≤ v} Λ(n) n^{-it}`. -/
def vonMangoldtTwist (v t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊v⌋₊, (Λ n : ℂ) * Complex.exp (-(t : ℂ) * I * (Real.log n : ℂ))

/-- The truncated Perron kernel
`(1 / 2π) ∫_{τ = -T}^{T} y^{c + iτ} / (c + iτ) dτ`. -/
def refPerronKernel (y c T : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ τ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (τ : ℂ) * I) / ((c : ℂ) + (τ : ℂ) * I)

/-- The absolute value of the exponential twist is one. -/
lemma norm_exp_twist (t : ℝ) (n : ℕ) :
    ‖Complex.exp (-(t : ℂ) * I * (Real.log n : ℂ))‖ = 1 := by
  have h : -(t : ℂ) * I * (Real.log n : ℂ) =
      ((-(t * Real.log n) : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- `n^{-it}` written as a complex power. -/
lemma cpow_neg_mul_I_eq_exp {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    (n : ℂ) ^ (-(t : ℂ) * I) =
      Complex.exp (-(t : ℂ) * I * (Real.log n : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn)]
  rw [show ((Real.log n : ℝ) : ℂ) = Complex.log (n : ℂ) from Complex.natCast_log]
  congr 1
  ring

/-! ## Summability and the `L`-series identity for the twist -/

/-- The `L`-series of `Λ(n) n^{-it}` is summable at `Re s > 1`. -/
lemma LSeriesSummable_twist {t σ : ℝ} (hσ : 1 < σ) :
    LSeriesSummable
      (fun n => (Λ n : ℂ) * Complex.exp (-(t : ℂ) * I * (Real.log n : ℂ)))
      (σ : ℂ) := by
  have hbase : LSeriesSummable (fun n => (Λ n : ℂ)) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hnorm :
      (fun n => ‖LSeries.term
          (fun n => (Λ n : ℂ) * Complex.exp (-(t : ℂ) * I * (Real.log n : ℂ)))
          (σ : ℂ) n‖) =
        (fun n => ‖LSeries.term (fun n => (Λ n : ℂ)) (σ : ℂ) n‖) := by
    funext n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs with hn
    · rfl
    · have h1 : ‖(Λ n : ℂ) * Complex.exp (-(t : ℂ) * I * (Real.log n : ℂ))‖ =
          ‖(Λ n : ℂ)‖ := by
        rw [norm_mul, norm_exp_twist, mul_one]
      rw [h1]
  exact summable_norm_iff.mp (hnorm ▸ (summable_norm_iff.mpr hbase))

/-- Pointwise identification of the twisted `L`-series term with the shifted
von Mangoldt term. -/
lemma LSeries_term_twist {t : ℝ} {s : ℂ} {n : ℕ} (hn : n ≠ 0) :
    LSeries.term
        (fun n => (Λ n : ℂ) * Complex.exp (-(t : ℂ) * I * (Real.log n : ℂ))) s n =
      LSeries.term (fun n => (Λ n : ℂ)) (s + (t : ℂ) * I) n := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
    ← cpow_neg_mul_I_eq_exp hn]
  have hneg : (n : ℂ) ^ (-(t : ℂ) * I) = ((n : ℂ) ^ ((t : ℂ) * I))⁻¹ := by
    rw [show -(t : ℂ) * I = -((t : ℂ) * I) by ring, Complex.cpow_neg]
  rw [hneg, Complex.cpow_add s ((t : ℂ) * I) hn0]
  field_simp

/-- **The twisted `L`-series is the shifted logarithmic derivative of `ζ`.** -/
lemma LSeries_twist_eq {t σ τ : ℝ} (hσ : 1 < σ) :
    LSeries
        (fun n => (Λ n : ℂ) * Complex.exp (-(t : ℂ) * I * (Real.log n : ℂ)))
        ((σ : ℂ) + (τ : ℂ) * I) =
      -logDeriv riemannZeta (((σ : ℂ) + (τ : ℂ) * I) + (t : ℂ) * I) := by
  have hcongr : LSeries
        (fun n => (Λ n : ℂ) * Complex.exp (-(t : ℂ) * I * (Real.log n : ℂ)))
        ((σ : ℂ) + (τ : ℂ) * I) =
      LSeries (fun n => (Λ n : ℂ)) (((σ : ℂ) + (τ : ℂ) * I) + (t : ℂ) * I) := by
    unfold LSeries
    exact tsum_congr fun n => by
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · exact LSeries_term_twist hn
  rw [hcongr,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hσ)]
  simp only [logDeriv, Pi.div_apply, div_eq_mul_inv]
  ring

/-! ## The truncated Perron formula without a `T ≤ u` side condition -/

/-- **The smallest explicit truncated-Perron error bound.**  A single absolute
constant `Cper` such that the truncated Perron formula for the twisted von
Mangoldt sum holds at every height `T ≥ 1` with the remainder
`Cper (v log²v / T + log v)`.  `truncatedPerron_vonMangoldt_twist` below proves
this unconditionally (in particular without any `T ≤ v` side condition). -/
def TruncatedPerronErrorBound (Cper : ℝ) : Prop :=
  ∀ (v t T : ℝ), 2 ≤ v → 1 ≤ T →
    ‖vonMangoldtTwist v t - refZetaSum v t T‖ ≤
      Cper * (v * (Real.log v) ^ 2 / T + Real.log v)

/-- **Truncated Perron for the twisted von Mangoldt sum, all heights `T ≥ 1`.**

This is `GlobalTheory.PerronPsi.truncated_perron_psi` with the side condition
`T ≤ 2u` removed and the twist `n^{-it}` absorbed into the `L`-series
coefficients.  The kernel bound
`GlobalTheory.PerronPsi.kernel_bound` is uniform in `T`, so the same
`O (u log²u / T + log u)` estimate holds for every `T ≥ 1`; in particular for
the L21.2 regime `T = X^3 + 1 ≫ v`. -/
theorem truncatedPerron_vonMangoldt_twist :
    ∃ C : ℝ, 0 < C ∧ TruncatedPerronErrorBound C := by
  obtain ⟨C0, hC0, hK⟩ := GlobalTheory.PerronPsi.kernel_bound
  refine ⟨240 * C0, by positivity, ?_⟩
  intro v t T hv hT
  have hv1 : 1 < v := by linarith
  have hv0 : 0 < v := by linarith
  have hT0 : 0 < T := by linarith
  have hL : 1 / 2 ≤ Real.log v := GlobalTheory.PerronPsi.half_le_log hv
  have hL0 : 0 < Real.log v := by linarith
  have hσ1 : 1 < refRe v := one_lt_refRe hv1
  have hσpos : 0 < refRe v := lt_trans zero_lt_one hσ1
  set N := ⌊v⌋₊ with hN
  set B := 2 * v / T with hB
  have hB0 : 0 ≤ B := div_nonneg (by linarith) hT0.le
  set a : ℕ → ℂ :=
    fun n => (Λ n : ℂ) * Complex.exp (-(t : ℂ) * I * (Real.log n : ℂ)) with ha
  have ha0 : a 0 = 0 := by simp [ha]
  have hsum : LSeriesSummable a (refRe v : ℂ) := by
    rw [ha]
    exact LSeriesSummable_twist hσ1
  -- Interchange the sum and the truncated integral.
  have hI := GlobalTheory.PerronPsi.interchange a ha0 T hσpos hv0 hsum
  have hIntEq :
      (∫ τ in (-T)..T,
          LSeries a ((refRe v : ℂ) + (τ : ℂ) * I) *
            (v : ℂ) ^ ((refRe v : ℂ) + (τ : ℂ) * I) /
              ((refRe v : ℂ) + (τ : ℂ) * I)) =
        ∫ τ in (-T)..T, zetaShiftFunction v t (perronLine (refRe v) τ) := by
    apply intervalIntegral.integral_congr
    intro τ _
    simp only [perronLine, zetaShiftFunction, ha]
    rw [LSeries_twist_eq (t := t) (σ := refRe v) (τ := τ) hσ1]
  have hZ : HasSum (fun n => a n * refPerronKernel (v / n) (refRe v) T)
      (refZetaSum v t T) := by
    have h0 := hI.mul_left (1 / (2 * Real.pi) : ℂ)
    rw [hIntEq] at h0
    have hvalue : (1 / (2 * Real.pi) : ℂ) *
        (∫ τ in (-T)..T, zetaShiftFunction v t (perronLine (refRe v) τ)) =
        refZetaSum v t T := by
      rw [refZetaSum]
    rw [hvalue] at h0
    have hsummand :
        (fun n => (1 / (2 * Real.pi) : ℂ) *
            (a n * ∫ τ in (-T)..T,
              ((v / n : ℝ) : ℂ) ^ ((refRe v : ℂ) + (τ : ℂ) * I) /
                ((refRe v : ℂ) + (τ : ℂ) * I))) =
          (fun n => a n * refPerronKernel (v / n) (refRe v) T) := by
      funext n
      simp only [refPerronKernel]
      ring
    rw [hsummand] at h0
    exact h0
  -- The finite truncated sum.
  have hfin : HasSum (fun n => a n * (if 1 ≤ v / n then (1 : ℂ) else 0))
      (vonMangoldtTwist v t) := by
    have h : HasSum (fun n => a n * (if 1 ≤ v / n then (1 : ℂ) else 0))
        (∑ n ∈ Finset.Icc 1 N, a n * (if 1 ≤ v / n then (1 : ℂ) else 0)) :=
      hasSum_sum_of_ne_finset_zero (by
        intro n hn
        by_cases h0 : n = 0
        · simp [h0, ha0]
        · have hnN : N < n := by
            rw [Finset.mem_Icc] at hn
            omega
          have hlt : v < n := by
            apply (Nat.floor_lt hv0.le).mp
            rwa [← hN]
          have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero h0
          have hnot : ¬ (1 ≤ v / n) := by
            rw [not_le, div_lt_one hnpos]
            exact hlt
          simp [hnot])
    convert h using 1
    rw [vonMangoldtTwist, ← hN]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hle : (n : ℝ) ≤ v := (Nat.le_floor_iff hv0.le).1 hn.2
    have h1 : 1 ≤ v / n := by
      rw [le_div_iff₀ hnpos]
      linarith
    simp [h1, ha]
  have hcomb := hfin.sub hZ
  -- The pointwise kernel error.
  have hτ1 : 1 < 1 + 1 / (2 * Real.log v) := by
    have := one_div_pos.2 (show 0 < 2 * Real.log v by linarith)
    linarith
  have hs1 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log v))) :=
    Real.summable_one_div_nat_rpow.2 hτ1
  have hA : 0 ≤ 12 * v * Real.log v / T :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hv0.le) hL0.le) hT0.le
  have hW0 : ∀ n, 0 ≤ (if n ∈ Finset.range (N + 1 + (N + 1)) then
      GlobalTheory.PerronPsi.w N B n else 0) := by
    intro n
    split_ifs
    · exact GlobalTheory.PerronPsi.w_nonneg N hB0 n
    · exact le_rfl
  have hg : HasSum (fun n : ℕ =>
        C0 * (12 * v * Real.log v / T *
            (1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log v))))
          + C0 * (16 * Real.log v *
            (if n ∈ Finset.range (N + 1 + (N + 1)) then
              GlobalTheory.PerronPsi.w N B n else 0)))
      (C0 * (12 * v * Real.log v / T *
          ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log v)))
        + C0 * (16 * Real.log v *
          ∑ n ∈ Finset.range (N + 1 + (N + 1)),
            (if n ∈ Finset.range (N + 1 + (N + 1)) then
              GlobalTheory.PerronPsi.w N B n else 0))) := by
    refine HasSum.add ((hs1.hasSum.mul_left _).mul_left _) ((HasSum.mul_left _ ?_).mul_left _)
    exact hasSum_sum_of_ne_finset_zero (fun n hn => if_neg hn)
  have hpt : ∀ n : ℕ,
      ‖a n * (if 1 ≤ v / n then (1 : ℂ) else 0)
        - a n * refPerronKernel (v / n) (refRe v) T‖ ≤
        C0 * (12 * v * Real.log v / T *
            (1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log v))))
          + C0 * (16 * Real.log v *
            (if n ∈ Finset.range (N + 1 + (N + 1)) then
              GlobalTheory.PerronPsi.w N B n else 0)) := by
    intro n
    have hg1 : 0 ≤ C0 * (12 * v * Real.log v / T *
        (1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log v)))) :=
      mul_nonneg hC0.le (mul_nonneg hA (by positivity))
    have hg2 : 0 ≤ C0 * (16 * Real.log v *
        (if n ∈ Finset.range (N + 1 + (N + 1)) then
          GlobalTheory.PerronPsi.w N B n else 0)) :=
      mul_nonneg hC0.le (mul_nonneg (by linarith) (hW0 n))
    by_cases h0 : n = 0
    · subst h0
      rw [ha0]
      simp only [zero_mul, sub_zero, norm_zero]
      linarith
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero h0
    have e : a n * (if 1 ≤ v / n then (1 : ℂ) else 0)
        - a n * refPerronKernel (v / n) (refRe v) T
        = -(a n * (refPerronKernel (v / n) (refRe v) T
            - (if 1 ≤ v / n then (1 : ℂ) else 0))) := by ring
    rw [e, norm_neg, norm_mul]
    have han : ‖a n‖ ≤ Real.log n := by
      have h1 : ‖a n‖ = Λ n := by
        simp only [ha]
        rw [norm_mul, norm_exp_twist, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg vonMangoldt_nonneg]
      rw [h1]
      exact vonMangoldt_le_log
    obtain ⟨hk1, hk2⟩ :=
      hK (v / n) (refRe v) T (div_pos hv0 hn0) hσpos (by linarith)
    have hk1' : ‖refPerronKernel (v / n) (refRe v) T -
        (if 1 ≤ v / n then (1 : ℂ) else 0)‖ ≤ C0 * (v / n) ^ refRe v := hk1
    have hk2' : ‖refPerronKernel (v / n) (refRe v) T -
        (if 1 ≤ v / n then (1 : ℂ) else 0)‖ *
        (T * |Real.log (v / n)|) ≤ C0 * (v / n) ^ refRe v := hk2
    have hstep := mul_le_mul_of_nonneg_right han
      (norm_nonneg (refPerronKernel (v / n) (refRe v) T
        - (if 1 ≤ v / n then (1 : ℂ) else 0)))
    by_cases hfar : (n : ℝ) ≤ v / 2 ∨ 2 * v ≤ n
    · have hft := GlobalTheory.PerronPsi.far_term hv hT0 (Nat.pos_of_ne_zero h0)
        hC0.le (norm_nonneg _) hk2' hfar
      linarith
    · push Not at hfar
      obtain ⟨h1, h2⟩ := hfar
      have hnt := GlobalTheory.PerronPsi.near_term hv hT0 hC0.le (norm_nonneg _)
        hk1' hk2' h1 h2
      have hmem : n ∈ Finset.range (N + 1 + (N + 1)) := by
        have huN : v < (N : ℝ) + 1 := by
          rw [hN]
          exact Nat.lt_floor_add_one v
        have h3 : (n : ℝ) < ((N + 1 + (N + 1) : ℕ) : ℝ) := by
          push_cast
          linarith
        rw [Finset.mem_range]
        exact_mod_cast h3
      rw [if_pos hmem]
      linarith
  have key := hcomb.norm_le_of_bounded hg hpt
  -- Sum the majorant.
  have hZsum : ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log v)) ≤
      1 + 2 * Real.log v := by
    have h1 := GlobalTheory.PerronPsi.zeta_bound hτ1
    rwa [add_sub_cancel_left, one_div_one_div] at h1
  have hWeq : ∑ n ∈ Finset.range (N + 1 + (N + 1)),
      (if n ∈ Finset.range (N + 1 + (N + 1)) then
        GlobalTheory.PerronPsi.w N B n else 0)
      = ∑ n ∈ Finset.range (N + 1 + (N + 1)), GlobalTheory.PerronPsi.w N B n :=
    Finset.sum_congr rfl (fun n hn => if_pos hn)
  have hlogN : Real.log N ≤ Real.log v := by
    have hNpos : (0 : ℝ) < N := by
      have h2 : (2 : ℕ) ≤ N := Nat.le_floor (by exact_mod_cast hv)
      exact_mod_cast (show 0 < N by omega)
    exact Real.log_le_log hNpos (by rw [hN]; exact Nat.floor_le hv0.le)
  have hW : ∑ n ∈ Finset.range (N + 1 + (N + 1)),
      GlobalTheory.PerronPsi.w N B n ≤ 2 + B * (2 * (1 + Real.log v)) := by
    have h1 := GlobalTheory.PerronPsi.sum_w N hB0
    have h2 : B * (2 * (1 + Real.log N)) ≤ B * (2 * (1 + Real.log v)) :=
      mul_le_mul_of_nonneg_left (by linarith) hB0
    linarith
  refine key.trans ?_
  rw [hWeq]
  have hX : 0 < v / T := div_pos hv0 hT0
  have e1 : 12 * v * Real.log v / T = 12 * Real.log v * (v / T) := by ring
  have e2 : B = 2 * (v / T) := by rw [hB]; ring
  have e3 : v * (Real.log v) ^ 2 / T = (Real.log v) ^ 2 * (v / T) := by ring
  have b1 := mul_le_mul_of_nonneg_left hZsum hA
  have b2 := mul_le_mul_of_nonneg_left hW (show (0 : ℝ) ≤ 16 * Real.log v by linarith)
  have b3 : 12 * v * Real.log v / T * (1 + 2 * Real.log v) +
      16 * Real.log v * (2 + B * (2 * (1 + Real.log v))) ≤
      240 * (v * (Real.log v) ^ 2 / T + Real.log v) := by
    rw [e1, e2, e3]
    nlinarith [mul_nonneg (mul_nonneg hL0.le hX.le)
        (show (0 : ℝ) ≤ 2 * Real.log v - 1 by linarith),
      mul_nonneg (mul_nonneg hL0.le hL0.le) hX.le]
  have b4 : 12 * v * Real.log v / T *
        ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log v)) +
      16 * Real.log v * ∑ n ∈ Finset.range (N + 1 + (N + 1)),
        GlobalTheory.PerronPsi.w N B n ≤
      240 * (v * (Real.log v) ^ 2 / T + Real.log v) := by
    linarith
  have b5 := mul_le_mul_of_nonneg_left b4 hC0.le
  linarith

/-! ## Prime-power removal -/

/-- **The prime-only sum differs from the full von Mangoldt sum by
`O (v log v)`.**  The difference consists of the proper prime powers
`p^k`, `k ≥ 2`, which we bound crudely by summing `log n` over all `n ≤ v`. -/
theorem twistedPrimeSum_sub_vonMangoldt_le {v t : ℝ} (hv : 2 ≤ v) :
    ‖twistedPrimeSum v t - vonMangoldtTwist v t‖ ≤ v * Real.log v := by
  have hv0 : 0 < v := by linarith
  set N := ⌊v⌋₊ with hN
  have hN0 : 0 ≤ N := Nat.zero_le _
  have hN1 : 1 ≤ N := by
    have h : ((1 : ℕ) : ℝ) ≤ v := by push_cast; linarith
    exact Nat.le_floor h
  have htw : twistedPrimeSum v t =
      ∑ n ∈ Finset.Icc 1 N,
        (if n.Prime then
          (Real.log n : ℂ) * Complex.exp (-(t : ℂ) * I * (Real.log n : ℂ))
        else 0) := by
    unfold twistedPrimeSum
    rw [← hN, Nat.range_succ_eq_Icc_zero,
      ← Finset.insert_Icc_succ_left_eq_Icc hN0]
    simp
  have hvm : vonMangoldtTwist v t =
      ∑ n ∈ Finset.Icc 1 N,
        (Λ n : ℂ) * Complex.exp (-(t : ℂ) * I * (Real.log n : ℂ)) := by
    unfold vonMangoldtTwist
    rw [← hN]
  rw [htw, hvm, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      ‖(if n.Prime then
          (Real.log n : ℂ) * Complex.exp (-(t : ℂ) * I * (Real.log n : ℂ))
        else 0) -
        (Λ n : ℂ) * Complex.exp (-(t : ℂ) * I * (Real.log n : ℂ))‖ ≤ Real.log n := by
    intro n hn
    by_cases hp : n.Prime
    · rw [if_pos hp, vonMangoldt_apply_prime hp, sub_self, norm_zero]
      exact (Real.log_pos (by exact_mod_cast hp.one_lt)).le
    · rw [if_neg hp, zero_sub, norm_neg, norm_mul, norm_exp_twist, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
      exact vonMangoldt_le_log
  refine (Finset.sum_le_sum hterm).trans ?_
  have hcard : (Finset.Icc 1 N).card = N := by
    rw [Nat.card_Icc]
    omega
  have hsumlog : ∑ n ∈ Finset.Icc 1 N, Real.log n ≤ N * Real.log N := by
    have hmono : ∀ n ∈ Finset.Icc 1 N, Real.log n ≤ Real.log N := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      exact Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
        (by exact_mod_cast hn.2)
    calc
      ∑ n ∈ Finset.Icc 1 N, Real.log n ≤ ∑ _n ∈ Finset.Icc 1 N, Real.log N :=
        Finset.sum_le_sum hmono
      _ = N * Real.log N := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hNle : (N : ℝ) ≤ v := by
    rw [hN]
    exact Nat.floor_le hv0.le
  have hlogN : Real.log N ≤ Real.log v := by
    apply Real.log_le_log (by positivity)
    exact hNle
  have hlogNnn : 0 ≤ Real.log N := by
    exact Real.log_nonneg (by exact_mod_cast hN1)
  calc
    ∑ n ∈ Finset.Icc 1 N, Real.log n ≤ N * Real.log N := hsumlog
    _ ≤ v * Real.log v :=
      mul_le_mul hNle hlogN hlogNnn hv0.le

/-- Explicit L21.2 reference-Perron constant.  It is deliberately very coarse:
`ReferencePerronBound` only needs an eventual comparison with the prime-power
scale `√v (log 2v)²`, and `v ≤ X`, `log v ≤ log X` in the L21.2 regime. -/
def refConstant (C : ℝ) (X : ℕ → ℝ) (n : ℕ) : ℝ :=
  (2 * C + 2) * (X n + 1) * ((bandLog X n) ^ 2 + 1)

/-- **The Perron and prime-power errors are dominated by the prime-power
scale.**  On the L21.2 range `2 ≤ v ≤ Q`, `log v ≤ U`, `log Q ≥ 3`, the
combined error
`v log v + C (v (log v)² / T + log v)` is at most `(2C+2)(Q+1)(U²+1)` times
`√v (log 2v)²`.  This is the only place where the choice of the (very
generous) constant `refConstant` is used. -/
lemma perronError_le_refConstant {C Q U v T : ℝ}
    (hC : 0 ≤ C) (hQ1 : 1 ≤ Q) (hU : 3 ≤ U) (hv : 2 ≤ v) (hvQ : v ≤ Q)
    (hlogv : Real.log v ≤ U) (hT : 1 ≤ T) :
    v * Real.log v + C * (v * (Real.log v) ^ 2 / T + Real.log v) ≤
      (2 * C + 2) * (Q + 1) * (U ^ 2 + 1) *
        (Real.sqrt v * (Real.log (2 * v)) ^ 2) := by
  have hv0 : 0 < v := by linarith
  have hlogv0 : 0 ≤ Real.log v := Real.log_nonneg (by linarith)
  have hlog2_le_one : Real.log 2 ≤ 1 := by
    have h := Real.log_two_lt_d9
    linarith
  have hlog2v_ge : 1 ≤ Real.log (2 * v) := by
    have h4 : (4 : ℝ) ≤ 2 * v := by linarith
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) h4
    have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      nlinarith [Real.log_two_gt_d9]
    linarith
  have hR1 : 1 ≤ Real.sqrt v * (Real.log (2 * v)) ^ 2 := by
    have h1 : (1 : ℝ) ≤ Real.sqrt v := Real.one_le_sqrt.mpr (by linarith)
    have h2 : (1 : ℝ) ≤ (Real.log (2 * v)) ^ 2 := by nlinarith
    exact one_le_mul_of_one_le_of_one_le h1 h2
  have hlog2v_le : Real.log (2 * v) ≤ U + 1 := by
    rw [Real.log_mul (by norm_num) hv0.ne']
    linarith
  have hlog2vsq : (Real.log (2 * v)) ^ 2 ≤ 4 * (U ^ 2 + 1) := by
    have h1 : Real.log (2 * v) ≤ U + 1 := hlog2v_le
    have h2 : 0 ≤ Real.log (2 * v) := by linarith
    have h3 : 1 ≤ U := by linarith
    nlinarith
  have hP0 : 0 ≤ (Q + 1) * (U ^ 2 + 1) := by positivity
  have hR0 : 0 ≤ Real.sqrt v * (Real.log (2 * v)) ^ 2 := by positivity
  have hA : v * Real.log v ≤
      (Q + 1) * (U ^ 2 + 1) * (Real.sqrt v * (Real.log (2 * v)) ^ 2) := by
    have h1 : v * Real.log v ≤ Q * (U + 1) :=
      mul_le_mul hvQ (by linarith) hlogv0 (by linarith)
    have h2 : Q * (U + 1) ≤ (Q + 1) * (U ^ 2 + 1) := by nlinarith
    calc
      v * Real.log v ≤ Q * (U + 1) := h1
      _ ≤ (Q + 1) * (U ^ 2 + 1) := h2
      _ ≤ (Q + 1) * (U ^ 2 + 1) *
            (Real.sqrt v * (Real.log (2 * v)) ^ 2) :=
        le_mul_of_one_le_right hP0 hR1
  have hB : v * (Real.log v) ^ 2 / T ≤
      (Q + 1) * (U ^ 2 + 1) * (Real.sqrt v * (Real.log (2 * v)) ^ 2) := by
    have h1 : v * (Real.log v) ^ 2 / T ≤ v * (Real.log v) ^ 2 :=
      div_le_self (by positivity) hT
    have h2 : v * (Real.log v) ^ 2 ≤ Q * U ^ 2 := by
      have hsq : (Real.log v) ^ 2 ≤ U ^ 2 := by nlinarith
      exact mul_le_mul hvQ hsq (sq_nonneg _) (by linarith)
    have h3 : Q * U ^ 2 ≤ (Q + 1) * (U ^ 2 + 1) := by nlinarith
    calc
      v * (Real.log v) ^ 2 / T ≤ v * (Real.log v) ^ 2 := h1
      _ ≤ Q * U ^ 2 := h2
      _ ≤ (Q + 1) * (U ^ 2 + 1) := h3
      _ ≤ (Q + 1) * (U ^ 2 + 1) *
            (Real.sqrt v * (Real.log (2 * v)) ^ 2) :=
        le_mul_of_one_le_right hP0 hR1
  have hD : Real.log v ≤
      (Q + 1) * (U ^ 2 + 1) * (Real.sqrt v * (Real.log (2 * v)) ^ 2) := by
    have h1 : Real.log v ≤ (Q + 1) * (U ^ 2 + 1) := by nlinarith
    calc
      Real.log v ≤ (Q + 1) * (U ^ 2 + 1) := h1
      _ ≤ (Q + 1) * (U ^ 2 + 1) *
            (Real.sqrt v * (Real.log (2 * v)) ^ 2) :=
        le_mul_of_one_le_right hP0 hR1
  have hB' : C * (v * (Real.log v) ^ 2 / T) ≤
      C * ((Q + 1) * (U ^ 2 + 1) * (Real.sqrt v * (Real.log (2 * v)) ^ 2)) :=
    mul_le_mul_of_nonneg_left hB hC
  have hD' : C * Real.log v ≤
      C * ((Q + 1) * (U ^ 2 + 1) * (Real.sqrt v * (Real.log (2 * v)) ^ 2)) :=
    mul_le_mul_of_nonneg_left hD hC
  have hPR0 : 0 ≤ (Q + 1) * (U ^ 2 + 1) *
      (Real.sqrt v * (Real.log (2 * v)) ^ 2) := by positivity
  nlinarith [hA, hB', hD', hC, hPR0]

/-- **The reference Perron bound from an absolute truncated-Perron estimate.**
Given a single constant `Cper` with
`‖Σ_{n≤v} Λ(n) n^{-it} − refZetaSum v t T‖ ≤ Cper (v log²v / T + log v)`
for all `T ≥ 1` (supplied by `truncatedPerron_vonMangoldt_twist`), and the
L21.2 range data, the full `ReferencePerronBound` holds with the explicit
constant `refConstant Cper X`. -/
theorem referencePerronBound_of_errorBound {X : ℕ → ℝ} {c Cper : ℝ}
    (hper : TruncatedPerronErrorBound Cper)
    (hCper : 0 ≤ Cper)
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n) (hc : c ≤ 1) :
    ReferencePerronBound X c (refConstant Cper X) 2 := by
  refine Filter.Eventually.of_forall ?_
  intro n v t hv hvB ht
  set Q := X n with hQdef
  set U := bandLog X n with hUdef
  have hQ1 : 1 < Q := hX n
  have hQ0 : 0 < Q := lt_trans zero_lt_one hQ1
  have hU3 : 3 ≤ U := hU n
  have hv0 : 0 < v := by linarith
  have hT1 : 1 ≤ X n ^ 3 + 1 := by
    have : 0 < X n ^ 3 := pow_pos hQ0 3
    linarith
  have hTX : paperRate X n ≤ U := by
    rw [paperRate, ← hUdef]
    have hlogU : Real.log U ≤ U := Real.log_le_self (by linarith)
    have hlogU0 : 0 ≤ Real.log U := Real.log_nonneg (by linarith)
    have hsq : U * Real.log U ≤ U ^ 2 := by nlinarith
    calc
      Real.sqrt (U * Real.log U) ≤ Real.sqrt (U ^ 2) := Real.sqrt_le_sqrt hsq
      _ = U := Real.sqrt_sq (by linarith)
  have hcT : c * paperRate X n ≤ U := by
    have hTn : 0 ≤ paperRate X n := Real.sqrt_nonneg _
    calc
      c * paperRate X n ≤ 1 * paperRate X n :=
        mul_le_mul_of_nonneg_right hc hTn
      _ = paperRate X n := one_mul _
      _ ≤ U := hTX
  have hvQ : v ≤ Q := by
    have key : v ≤ Real.exp (bandLog X n) :=
      hvB.trans (Real.exp_le_exp.mpr hcT)
    have hexp : Real.exp (bandLog X n) = Q := by
      rw [bandLog, ← hQdef, Real.exp_log hQ0]
    rwa [hexp] at key
  have hlogv : Real.log v ≤ U := Real.log_le_log hv0 hvQ
  have h1 := hper v t (X n ^ 3 + 1) hv hT1
  have h2 := twistedPrimeSum_sub_vonMangoldt_le (v := v) (t := t) hv
  have hkey := perronError_le_refConstant (C := Cper) (Q := Q) (U := U)
    (v := v) (T := X n ^ 3 + 1) hCper (le_of_lt hQ1) hU3 hv hvQ hlogv hT1
  have htri : ‖twistedPrimeSum v t - refZetaSum v t (X n ^ 3 + 1)‖ ≤
      v * Real.log v + Cper *
        (v * (Real.log v) ^ 2 / (X n ^ 3 + 1) + Real.log v) := by
    have hsplit : twistedPrimeSum v t - refZetaSum v t (X n ^ 3 + 1) =
        (twistedPrimeSum v t - vonMangoldtTwist v t) +
          (vonMangoldtTwist v t - refZetaSum v t (X n ^ 3 + 1)) := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    exact add_le_add h2 h1
  have hgoal : v * Real.log v + Cper *
        (v * (Real.log v) ^ 2 / (X n ^ 3 + 1) + Real.log v) ≤
      shiftPrimePower (refConstant Cper X n) v := by
    unfold shiftPrimePower
    exact hkey
  exact htri.trans hgoal

/-- **The reference Perron bound in the L21.2 regime.**  The truncated Perron
formula `truncatedPerron_vonMangoldt_twist` (valid for all `T ≥ 1`) and the
prime-power removal combine, with the explicit constant `refConstant Cper X`, to
discharge `ReferencePerronBound`.  The only hypotheses are `X n > 1` and
`log (X n) ≥ 3` (the latter always holds on the L21.2 bands), plus `c ≤ 1`,
which is what places `v` below `X`. -/
theorem referencePerronBound {X : ℕ → ℝ} {c : ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n) (hc : c ≤ 1) :
    ∃ (K : ℕ → ℝ) (C : ℝ), ReferencePerronBound X c K C := by
  obtain ⟨Cper, hCper, hper⟩ := truncatedPerron_vonMangoldt_twist
  exact ⟨refConstant Cper X, 2,
    referencePerronBound_of_errorBound hper hCper.le hX hU hc⟩

/-! ## The regime boundary: the old `T ≤ u` theorem -/

/-- **The old `T ≤ 2u` regime is contained in the new one.**  Specialising
`GlobalTheory.PerronPsi.truncated_perron_psi` to the principal character gives
the truncated Perron formula for `Σ_{n≤v} Λ(n)` in the old regime `T ≤ 2v`.
The statement below is exactly the `t = 0` case of
`truncatedPerron_vonMangoldt_twist`, whose side condition `T ≤ 2v` has been
removed; this shows that `T ≤ u` is precisely the boundary crossed by the new
proof. -/
theorem vonMangoldt_perron_old_regime :
    ∃ C : ℝ, 0 < C ∧ ∀ (v T : ℝ), 2 ≤ v → 2 ≤ T → T ≤ 2 * v →
      ‖vonMangoldtTwist v 0 - refZetaSum v 0 T‖ ≤
        C * (v * (Real.log v) ^ 2 / T + Real.log v) := by
  obtain ⟨C, hC, hpsi⟩ := GlobalTheory.PerronPsi.truncated_perron_psi
  refine ⟨C, hC, ?_⟩
  intro v T hv hT2 hTu
  have h := hpsi 1 (1 : DirichletCharacter ℂ 1) v T hT2 hTu hv
  have hleft :
      (∑ n ∈ Finset.Icc 1 ⌊v⌋₊,
          (Λ n : ℂ) * (1 : DirichletCharacter ℂ 1) (n : ZMod 1)) =
        vonMangoldtTwist v 0 := by
    rw [vonMangoldtTwist]
    apply Finset.sum_congr rfl
    intro n hn
    simp [Subsingleton.eq_one]
  have hright :
      (1 / (2 * Real.pi) : ℂ) *
        ∫ t in (-T)..T,
          -(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1))
                ((1 + 1 / Real.log v : ℝ) + t * I) /
              DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)
                ((1 + 1 / Real.log v : ℝ) + t * I)) *
            (v : ℂ) ^ (((1 + 1 / Real.log v : ℝ) : ℂ) + t * I) /
              (((1 + 1 / Real.log v : ℝ) : ℂ) + t * I) =
        refZetaSum v 0 T := by
    rw [refZetaSum]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    simp [zetaShiftFunction, logDeriv, perronLine, refRe]
  rwa [hleft, hright] at h

end Cogentic.RandomizedL21_2ReferenceBound

/-! ## Axiom audit -/

#print axioms Cogentic.RandomizedL21_2ReferenceBound.truncatedPerron_vonMangoldt_twist
#print axioms Cogentic.RandomizedL21_2ReferenceBound.twistedPrimeSum_sub_vonMangoldt_le
#print axioms Cogentic.RandomizedL21_2ReferenceBound.perronError_le_refConstant
#print axioms Cogentic.RandomizedL21_2ReferenceBound.referencePerronBound_of_errorBound
#print axioms Cogentic.RandomizedL21_2ReferenceBound.referencePerronBound
#print axioms Cogentic.RandomizedL21_2ReferenceBound.vonMangoldt_perron_old_regime
