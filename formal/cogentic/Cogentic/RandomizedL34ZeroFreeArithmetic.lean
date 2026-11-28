import Cogentic.RandomizedL34ClassicalRegion

/-!
# L34: the explicit exceptional-zero arithmetic `β₀ = 1 - 1/(4 F log |Δ|)`

`Cogentic.RandomizedL34ClassicalRegion` reduced the paper's zero-free input to
the classical de la Vallée Poussin region plus the height bridge, and
`Cogentic.RandomizedL34BelowOne` reduced the residual input to the strip
statement `β₀ < Re ρ → Re ρ < 1 → Re ρ ≤ 1 - cz / log |Δ_E|`.

This file closes the *arithmetic* interface around the paper's explicit choice

`β₀ n = 1 - 1 / (4 * F n * log |Δ_E| n)`,

which is the exact Stark line `1 - (4 F log |Δ_E|)⁻¹`.  No zero-free statement
is asserted: the analytic region is still a hypothesis, and the file only
proves the elementary facts that make the paper's constants meaningful.

## Contents

1. **The explicit `β₀`.**  `paperBeta0 F discLog` is the paper's choice.
   `paperBeta0_gap` records the identity `1 - β₀ n = 1/(4 F n log|Δ| n)`, and
   `paperBeta0_lt_one`, `paperBeta0_pos`, `paperBeta0_mem_Ioo` place it in
   `(0,1)`.  Positivity of `β₀` needs `4 F log|Δ| > 1`; `F > 0` and
   `log|Δ| > 0` alone only give `β₀ < 1`.  The corollary
   `paperBeta0_pos_of_one_le` covers the paper's factorial scale, where
   `F ≥ 1` and `log|Δ| ≥ 1`.

2. **Strip/classical inequalities.**  `paperBeta0` is exactly Stark's upper
   bound: `paperBeta0_starkBetaUpper` holds with equality, so every admissible
   `β` satisfies `β ≤ paperBeta0` (`starkBetaUpper_le_paperBeta0`).  The gap
   form `StarkGap` and the division-free product form `StarkBetaProduct` are
   proved as well.

3. **Consistency with the zero-free line.**  The exact arithmetic comparison
   `paperBeta0 ≤ 1 - c / log|Δ| ↔ c ≤ 1/(4 F)` is proved in
   `paperBeta0_le_zeroFreeLine_iff`.  Thus the Stark line and the zero-free
   line are always ordered, never mutually contradictory; both lie strictly
   below `1`.  The strip `(β₀, 1)` is nonempty
   (`paperBeta0_strip_nonempty`, `paperBeta0_region_consistent`).

4. **The strip region for the explicit `β₀`.**  The classical region plus the
   height bound give `DedekindZeroFreeAboveBetaBelowOne` for `paperBeta0`, and
   the half-plane bridge then gives the paper's `DedekindZeroFreeAboveBeta`
   and the smallest bundle `DedekindZeroFreeInput`.  The scalar Dedekind strip
   input is proved in sequence form for `paperBeta0`
   (`dedekindZetaStripInput_paperBeta0_of_classicalRegion`), with the
   sequence height bound `DedekindZetaStripHeightBound`.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no zero-free
region is claimed.
-/

namespace Cogentic.RandomizedL34ZeroFreeArithmetic

open Filter Real
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Sub
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedL34ZeroFree
open Cogentic.RandomizedL34HalfPlane
open Cogentic.RandomizedL34BelowOne
open Cogentic.RandomizedL34ClassicalRegion

noncomputable section

/-! ## 1. The paper's explicit exceptional zero -/

/-- **The paper's choice of exceptional zero**:
`β₀ n = 1 - 1 / (4 * F n * log |Δ_E| n)`.  This is the exact Stark line used
in `research/keybreak-cumulative-character-probes.md`. -/
def paperBeta0 (F discLog : ℕ → ℝ) : ℕ → ℝ :=
  fun n => 1 - 1 / (4 * F n * discLog n)

/-- The defining equation of `paperBeta0`. -/
theorem paperBeta0_def (F discLog : ℕ → ℝ) (n : ℕ) :
    paperBeta0 F discLog n = 1 - 1 / (4 * F n * discLog n) := rfl

/-- **The Stark gap of the explicit `β₀` is exactly `1/(4 F log|Δ|)`.** -/
theorem paperBeta0_gap (F discLog : ℕ → ℝ) (n : ℕ) :
    1 - paperBeta0 F discLog n = 1 / (4 * F n * discLog n) := by
  unfold paperBeta0
  ring

/-- **The explicit `β₀` lies strictly below `1`** as soon as the two constants
are positive. -/
theorem paperBeta0_lt_one {F discLog : ℕ → ℝ} {n : ℕ}
    (hF : 0 < F n) (hD : 0 < discLog n) :
    paperBeta0 F discLog n < 1 := by
  have hden : 0 < 4 * F n * discLog n :=
    mul_pos (mul_pos (by norm_num) hF) hD
  have hpos : 0 < 1 / (4 * F n * discLog n) := one_div_pos.mpr hden
  unfold paperBeta0
  linarith

/-- **The explicit `β₀` is positive** once `4 F log|Δ| > 1`.  This is the
additional arithmetic side condition needed for positivity: `F > 0` and
`log|Δ| > 0` alone give only `β₀ < 1`. -/
theorem paperBeta0_pos {F discLog : ℕ → ℝ} {n : ℕ}
    (h : 1 < 4 * F n * discLog n) :
    0 < paperBeta0 F discLog n := by
  have hden : 0 < 4 * F n * discLog n := lt_trans zero_lt_one h
  have hlt : 1 / (4 * F n * discLog n) < 1 := by
    rw [div_lt_iff₀ hden]
    linarith
  unfold paperBeta0
  linarith

/-- **Positivity at the paper's factorial scale.**  If `F n ≥ 1` and
`log |Δ_E| n ≥ 1`, then `4 F log|Δ| ≥ 4 > 1`, so `β₀` is positive. -/
theorem paperBeta0_pos_of_one_le {F discLog : ℕ → ℝ} {n : ℕ}
    (hF : 1 ≤ F n) (hD : 1 ≤ discLog n) :
    0 < paperBeta0 F discLog n := by
  apply paperBeta0_pos
  have hFpos : 0 < F n := lt_of_lt_of_le zero_lt_one hF
  have hmul : (1 : ℝ) ≤ F n * discLog n := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ F n * discLog n :=
        mul_le_mul hF hD (by norm_num) (le_of_lt hFpos)
  have h4 : (4 : ℝ) ≤ 4 * F n * discLog n := by nlinarith [hmul]
  linarith

/-- **The paper's `β₀` lies in `(0,1)`.** -/
theorem paperBeta0_mem_Ioo {F discLog : ℕ → ℝ} {n : ℕ}
    (hF : 0 < F n) (hD : 0 < discLog n)
    (hbig : 1 < 4 * F n * discLog n) :
    paperBeta0 F discLog n ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨paperBeta0_pos hbig, paperBeta0_lt_one hF hD⟩

/-- The `(0,1)` membership at the factorial scale `F ≥ 1`, `log|Δ| ≥ 1`. -/
theorem paperBeta0_mem_Ioo_of_one_le {F discLog : ℕ → ℝ} {n : ℕ}
    (hF : 1 ≤ F n) (hD : 1 ≤ discLog n) :
    paperBeta0 F discLog n ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨paperBeta0_pos_of_one_le hF hD,
    paperBeta0_lt_one (lt_of_lt_of_le zero_lt_one hF)
      (lt_of_lt_of_le zero_lt_one hD)⟩

/-- **The strip `(β₀, 1)` is nonempty.** -/
theorem paperBeta0_strip_nonempty {F discLog : ℕ → ℝ} {n : ℕ}
    (hF : 0 < F n) (hD : 0 < discLog n) :
    ∃ r : ℝ, paperBeta0 F discLog n < r ∧ r < 1 := by
  have hlt := paperBeta0_lt_one hF hD
  refine ⟨(paperBeta0 F discLog n + 1) / 2, ?_, ?_⟩
  · linarith
  · linarith

/-- **No contradictory bounds.**  The explicit `β₀` is in `(0,1)` and the open
strip `(β₀,1)` is nonempty, so the two strict strip conditions
`β₀ < Re ρ` and `Re ρ < 1` are simultaneously satisfiable. -/
theorem paperBeta0_region_consistent {F discLog : ℕ → ℝ} {n : ℕ}
    (hF : 0 < F n) (hD : 0 < discLog n)
    (hbig : 1 < 4 * F n * discLog n) :
    (0 < paperBeta0 F discLog n ∧ paperBeta0 F discLog n < 1) ∧
      ∃ r : ℝ, paperBeta0 F discLog n < r ∧ r < 1 :=
  ⟨⟨paperBeta0_pos hbig, paperBeta0_lt_one hF hD⟩,
    paperBeta0_strip_nonempty hF hD⟩

/-! ## 2. Stark's bound is an identity for the explicit `β₀` -/

/-- **The paper's `β₀` satisfies Stark's upper bound with equality.** -/
theorem paperBeta0_starkBetaUpper (F discLog : ℕ → ℝ) :
    StarkBetaUpper (paperBeta0 F discLog) F discLog := by
  intro n
  unfold paperBeta0
  exact le_rfl

/-- **Every admissible exceptional zero is at most the paper's `β₀`.**  The
explicit choice is the *largest* value allowed by Stark's bound. -/
theorem starkBetaUpper_le_paperBeta0 {beta0 F discLog : ℕ → ℝ}
    (h : StarkBetaUpper beta0 F discLog) (n : ℕ) :
    beta0 n ≤ paperBeta0 F discLog n := by
  simpa [paperBeta0] using h n

/-- **The explicit `β₀` satisfies Stark's gap form.** -/
theorem paperBeta0_starkGap (F discLog : ℕ → ℝ) :
    StarkGap (paperBeta0 F discLog) F discLog := by
  intro n
  rw [paperBeta0_gap]

/-- **The explicit `β₀` satisfies the division-free product form**
`4 F log|Δ| (1 - β₀) = 1`. -/
theorem paperBeta0_four_mul_gap {F discLog : ℕ → ℝ} {n : ℕ}
    (hF : 0 < F n) (hD : 0 < discLog n) :
    4 * F n * discLog n * (1 - paperBeta0 F discLog n) = 1 := by
  have hden : 4 * F n * discLog n ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos (by norm_num) hF) hD)
  rw [paperBeta0_gap, mul_one_div, div_self hden]

/-- **The explicit `β₀` satisfies `StarkBetaProduct`.** -/
theorem paperBeta0_starkProduct {F discLog : ℕ → ℝ}
    (hF : ∀ n, 0 < F n) (hD : ∀ n, 0 < discLog n) :
    StarkBetaProduct (paperBeta0 F discLog) F discLog := by
  intro n
  rw [paperBeta0_four_mul_gap (hF n) (hD n)]

/-! ## 3. Consistency with the classical zero-free line -/

/-- **Arithmetic comparison of the Stark line and the zero-free line.**  For
positive `F` and `log|Δ|`, the paper's `β₀` lies on or below
`1 - c / log|Δ|` exactly when `c ≤ 1/(4 F)`.  In particular the two lines are
always ordered: they cannot impose contradictory bounds. -/
theorem paperBeta0_le_zeroFreeLine_iff {F discLog : ℕ → ℝ} {n : ℕ} {c : ℝ}
    (hF : 0 < F n) (hD : 0 < discLog n) :
    paperBeta0 F discLog n ≤ 1 - c / discLog n ↔ c ≤ 1 / (4 * F n) := by
  have h4F : 4 * F n ≠ 0 := ne_of_gt (mul_pos (by norm_num) hF)
  have hden : 4 * F n * discLog n ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos (by norm_num) hF) hD)
  constructor
  · intro h
    have h1 : c / discLog n ≤ 1 / (4 * F n * discLog n) := by
      unfold paperBeta0 at h
      linarith
    have h2 : (c / discLog n) * discLog n ≤
        (1 / (4 * F n * discLog n)) * discLog n :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hD)
    have hc' : (c / discLog n) * discLog n = c := by
      field_simp [ne_of_gt hD]
    have hr' : (1 / (4 * F n * discLog n)) * discLog n = 1 / (4 * F n) := by
      field_simp [h4F, hden]
    linarith
  · intro hc
    have h1 : c / discLog n ≤ (1 / (4 * F n)) / discLog n :=
      div_le_div_of_nonneg_right hc (le_of_lt hD)
    have heq : (1 / (4 * F n)) / discLog n = 1 / (4 * F n * discLog n) := by
      rw [div_div]
    unfold paperBeta0
    linarith

/-- The `c ≤ 1/(4F)` direction of the line comparison. -/
theorem paperBeta0_le_zeroFreeLine {F discLog : ℕ → ℝ} {n : ℕ} {c : ℝ}
    (hF : 0 < F n) (hD : 0 < discLog n) (hc : c ≤ 1 / (4 * F n)) :
    paperBeta0 F discLog n ≤ 1 - c / discLog n :=
  (paperBeta0_le_zeroFreeLine_iff hF hD).mpr hc

/-- The complementary direction: if `1/(4F) ≤ c`, the zero-free line is on or
below the Stark line. -/
theorem zeroFreeLine_le_paperBeta0 {F discLog : ℕ → ℝ} {n : ℕ} {c : ℝ}
    (_hF : 0 < F n) (hD : 0 < discLog n) (hc : 1 / (4 * F n) ≤ c) :
    1 - c / discLog n ≤ paperBeta0 F discLog n := by
  have h1 : (1 / (4 * F n)) / discLog n ≤ c / discLog n :=
    div_le_div_of_nonneg_right hc (le_of_lt hD)
  have heq : (1 / (4 * F n)) / discLog n = 1 / (4 * F n * discLog n) := by
    rw [div_div]
  unfold paperBeta0
  linarith

/-- **The classical zero-free line lies strictly below `1`** for positive
constants.  Together with `paperBeta0_lt_one` this shows that both lines are
compatible with the strict upper strip bound `Re ρ < 1`. -/
theorem zeroFreeLine_lt_one {c D : ℝ} (hc : 0 < c) (hD : 0 < D) :
    1 - c / D < 1 := by
  have hpos : 0 < c / D := div_pos hc hD
  linarith

/-! ## 4. The residual strip statement for the explicit `β₀` -/

/-- **The classical region plus the height bound give the residual strip
statement for the paper's explicit `β₀`.**  This is
`DedekindZeroFreeAboveBetaBelowOne (paperBeta0 F discLog)`, the exact input
isolated in `Cogentic.RandomizedL34BelowOne`. -/
theorem dedekindZeroFreeAboveBetaBelowOne_paperBeta0_of_classicalRegion
    {f : ℂ → ℂ} {Z : ZetaZeroSequence f} {F discLog : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hreg : ClassicalZeroFreeRegion f c)
    (hheight : ZeroHeightBoundAt Z discLog) :
    DedekindZeroFreeAboveBetaBelowOne (paperBeta0 F discLog) Z.realPart c
      discLog :=
  ZeroSequenceUniformRegion.toBelowOne
    (classicalZeroFreeRegion_uniformSequence hc hreg Z hheight)

/-- **The explicit-`β₀` strip statement together with the `(0,1)` arithmetic.**
Every index has `β₀ ∈ (0,1)`, so the strip is genuine, and the residual
division-free strip statement holds. -/
theorem dedekindZeroFreeAboveBetaBelowOne_paperBeta0_of_classicalRegion_of_pos
    {f : ℂ → ℂ} {Z : ZetaZeroSequence f} {F discLog : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hreg : ClassicalZeroFreeRegion f c)
    (hheight : ZeroHeightBoundAt Z discLog)
    (hF : ∀ n, 0 < F n) (hD : ∀ n, 0 < discLog n)
    (hbig : ∀ n, 1 < 4 * F n * discLog n) :
    (∀ n, paperBeta0 F discLog n ∈ Set.Ioo (0 : ℝ) 1) ∧
      DedekindZeroFreeAboveBetaBelowOne (paperBeta0 F discLog) Z.realPart c
        discLog :=
  ⟨fun n => paperBeta0_mem_Ioo (hF n) (hD n) (hbig n),
    dedekindZeroFreeAboveBetaBelowOne_paperBeta0_of_classicalRegion hc hreg
      hheight⟩

/-- **The classical region alone gives the paper's "above `β₀`" region for the
explicit `β₀`.**  No half-plane hypothesis is needed: the uniform classical
region is already stronger. -/
theorem dedekindZeroFreeAboveBeta_paperBeta0_of_classicalRegion
    {f : ℂ → ℂ} {Z : ZetaZeroSequence f} {F discLog : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hreg : ClassicalZeroFreeRegion f c)
    (hheight : ZeroHeightBoundAt Z discLog) :
    DedekindZeroFreeAboveBeta (paperBeta0 F discLog) Z.realPart c discLog :=
  ZeroSequenceUniformRegion.toAboveBeta
    (classicalZeroFreeRegion_uniformSequence hc hreg Z hheight)

/-! ## 5. The half-plane bridge -/

/-- **A half-plane at `1` and the explicit-`β₀` strip statement give the
paper's zero-free region.**  This is the half-plane bridge specialized to
`paperBeta0`: the half-plane removes `Re ρ ≥ 1`, leaving exactly the strip
`β₀ < Re ρ < 1` where the classical region applies. -/
theorem dedekindZeroFreeAboveBeta_paperBeta0_of_strip_of_halfPlane
    {f : ℂ → ℂ} (Z : ZetaZeroSequence f) (hf : ZeroFreeHalfPlane f 1)
    {F discLog : ℕ → ℝ} {c : ℝ}
    (h : DedekindZeroFreeAboveBetaBelowOne (paperBeta0 F discLog) Z.realPart c
      discLog) :
    DedekindZeroFreeAboveBeta (paperBeta0 F discLog) Z.realPart c discLog :=
  dedekindZeroFreeAboveBeta_of_belowOne_of_halfPlane Z hf h

/-- **The half-plane bridge starting from the classical region and height
bound.**  The half-plane is supplied by the classical region itself
(`classicalZeroFreeRegion_halfPlane`), so the only analytic hypothesis is the
classical region. -/
theorem dedekindZeroFreeAboveBeta_paperBeta0_of_classicalRegion_halfPlane
    {f : ℂ → ℂ} {Z : ZetaZeroSequence f} {F discLog : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hreg : ClassicalZeroFreeRegion f c)
    (hheight : ZeroHeightBoundAt Z discLog) :
    DedekindZeroFreeAboveBeta (paperBeta0 F discLog) Z.realPart c discLog :=
  dedekindZeroFreeAboveBeta_paperBeta0_of_strip_of_halfPlane Z
    (classicalZeroFreeRegion_halfPlane hc hreg)
    (dedekindZeroFreeAboveBetaBelowOne_paperBeta0_of_classicalRegion hc hreg
      hheight)

/-- **The smallest zero-free bundle for the explicit `β₀`.** -/
theorem dedekindZeroFreeInput_paperBeta0_of_classicalRegion
    {f : ℂ → ℂ} {Z : ZetaZeroSequence f} {F discLog : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hreg : ClassicalZeroFreeRegion f c)
    (hheight : ZeroHeightBoundAt Z discLog) :
    DedekindZeroFreeInput (paperBeta0 F discLog) Z.realPart c discLog where
  cz_pos := hc
  above_beta :=
    dedekindZeroFreeAboveBeta_paperBeta0_of_classicalRegion_halfPlane hc hreg
      hheight

/-! ## 6. The Dedekind zeta function with the explicit `β₀` -/

/-- **Sequence-indexed strip height bound for `ζ_K`.**  Every strip zero has
`log(|Im z| + 2) ≤ discLog n`.  This is the sequence form needed because
`paperBeta0` varies with the index. -/
def DedekindZetaStripHeightBound (K : Type*) [Field K] [NumberField K]
    (beta0 : ℕ → ℝ) (discLog : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (z : ℂ), NumberField.dedekindZeta K z = 0 →
    beta0 n < z.re → z.re < 1 →
      Real.log (|z.im| + 2) ≤ discLog n

/-- **The classical Dedekind region plus the sequence height bound give the
exact strip input for the explicit `β₀`.**  This is the scalar
`DedekindZetaStripInput` with the paper's sequence `β₀ n`. -/
theorem dedekindZetaStripInput_paperBeta0_of_classicalRegion
    (K : Type*) [Field K] [NumberField K]
    {F discLog : ℕ → ℝ} {c : ℝ}
    (hreg : DedekindClassicalRegion K c)
    (hheight : DedekindZetaStripHeightBound K (paperBeta0 F discLog) discLog) :
    DedekindZetaStripInput K (paperBeta0 F discLog) c discLog := by
  intro n z hz hb hlt
  have hLpos : 0 < Real.log (|z.im| + 2) := by
    apply Real.log_pos
    have := abs_nonneg z.im
    linarith
  have hLle : Real.log (|z.im| + 2) ≤ discLog n := hheight n z hz hb hlt
  have hdisc : 0 < discLog n := lt_of_lt_of_le hLpos hLle
  have hre : z.re ≤ 1 - c / Real.log (|z.im| + 2) := by
    by_contra hnot
    exact hreg z (lt_of_not_ge hnot) hz
  have hc_le : c ≤ (1 - z.re) * Real.log (|z.im| + 2) := by
    have hquot : c / Real.log (|z.im| + 2) ≤ 1 - z.re := by linarith
    exact (div_le_iff₀ hLpos).mp hquot
  have hmul : (1 - z.re) * Real.log (|z.im| + 2) ≤
      (1 - z.re) * discLog n :=
    mul_le_mul_of_nonneg_left hLle (by linarith)
  have hdist : c ≤ (1 - z.re) * discLog n := le_trans hc_le hmul
  have hquot : c / discLog n ≤ 1 - z.re := (div_le_iff₀ hdisc).mpr hdist
  linarith

/-- **The residual strip statement for `ζ_K` and the explicit `β₀`.** -/
theorem dedekindZeta_zeroFreeAboveBetaBelowOne_paperBeta0
    (K : Type*) [Field K] [NumberField K]
    {F discLog : ℕ → ℝ} {c : ℝ}
    (hreg : DedekindClassicalRegion K c)
    (hheight : DedekindZetaStripHeightBound K (paperBeta0 F discLog) discLog)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K)) :
    DedekindZeroFreeAboveBetaBelowOne (paperBeta0 F discLog) Z.realPart c
      discLog :=
  dedekindZeroFreeAboveBetaBelowOne_of_zetaStripInput K
    (dedekindZetaStripInput_paperBeta0_of_classicalRegion K hreg hheight) Z

/-- **The paper's zero-free region for `ζ_K` and the explicit `β₀`.**  The
half-plane is supplied by the classical region; the strip input is supplied by
the classical region and the height bound. -/
theorem dedekindZeta_zeroFreeAboveBeta_paperBeta0
    (K : Type*) [Field K] [NumberField K]
    {F discLog : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hreg : DedekindClassicalRegion K c)
    (hheight : DedekindZetaStripHeightBound K (paperBeta0 F discLog) discLog)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K)) :
    DedekindZeroFreeAboveBeta (paperBeta0 F discLog) Z.realPart c discLog :=
  dedekindZeroFreeAboveBeta_of_zetaStripInput_of_halfPlane K
    (dedekindClassicalRegion_halfPlane K hc hreg)
    (dedekindZetaStripInput_paperBeta0_of_classicalRegion K hreg hheight) Z

/-- **The smallest Dedekind zero-free bundle for the explicit `β₀`.** -/
theorem dedekindZeta_zeroFreeInput_paperBeta0
    (K : Type*) [Field K] [NumberField K]
    {F discLog : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hreg : DedekindClassicalRegion K c)
    (hheight : DedekindZetaStripHeightBound K (paperBeta0 F discLog) discLog)
    (Z : ZetaZeroSequence (NumberField.dedekindZeta K)) :
    DedekindZeroFreeInput (paperBeta0 F discLog) Z.realPart c discLog where
  cz_pos := hc
  above_beta :=
    dedekindZeta_zeroFreeAboveBeta_paperBeta0 K hc hreg hheight Z

/-! ## Axiom audit -/

#print axioms paperBeta0_def
#print axioms paperBeta0_gap
#print axioms paperBeta0_lt_one
#print axioms paperBeta0_pos
#print axioms paperBeta0_pos_of_one_le
#print axioms paperBeta0_mem_Ioo
#print axioms paperBeta0_mem_Ioo_of_one_le
#print axioms paperBeta0_strip_nonempty
#print axioms paperBeta0_region_consistent
#print axioms paperBeta0_starkBetaUpper
#print axioms starkBetaUpper_le_paperBeta0
#print axioms paperBeta0_starkGap
#print axioms paperBeta0_four_mul_gap
#print axioms paperBeta0_starkProduct
#print axioms paperBeta0_le_zeroFreeLine_iff
#print axioms paperBeta0_le_zeroFreeLine
#print axioms zeroFreeLine_le_paperBeta0
#print axioms zeroFreeLine_lt_one
#print axioms dedekindZeroFreeAboveBetaBelowOne_paperBeta0_of_classicalRegion
#print axioms dedekindZeroFreeAboveBetaBelowOne_paperBeta0_of_classicalRegion_of_pos
#print axioms dedekindZeroFreeAboveBeta_paperBeta0_of_classicalRegion
#print axioms dedekindZeroFreeAboveBeta_paperBeta0_of_strip_of_halfPlane
#print axioms dedekindZeroFreeAboveBeta_paperBeta0_of_classicalRegion_halfPlane
#print axioms dedekindZeroFreeInput_paperBeta0_of_classicalRegion
#print axioms dedekindZetaStripInput_paperBeta0_of_classicalRegion
#print axioms dedekindZeta_zeroFreeAboveBetaBelowOne_paperBeta0
#print axioms dedekindZeta_zeroFreeAboveBeta_paperBeta0
#print axioms dedekindZeta_zeroFreeInput_paperBeta0

end

end Cogentic.RandomizedL34ZeroFreeArithmetic
