import Cogentic.RandomizedL20_2Decay
import Cogentic.RandomizedBalancedStrip

set_option linter.style.haveILetI false

/-!
# L20.2: the envelope width condition on the paper's prime bins

`RandomizedL20_2Decay` reduces the L20.2 smooth-character decay to the
per-bin real inequality

```
PrimeBinEnvelopeWidthCore K Ks c q A B n :
  ∀ i,
    exp ((c D log D) / #ι) * envelopeFactor K q (B i) * log (B i)
      + supplyError Ks (B i) ≤ B i - A i .
```

This file proves that inequality for the manuscript's own prime bins, or
rather reduces it to the single scalar width inequality that the paper's
choice of bin widths has to satisfy.

## The manuscript's bins

The paper splits a logarithmic band into the half-open intervals

```
I_j = [P exp (δ (j - a/k)),  P exp (δ (j + 1 - a/k))) ,
```

`RandomizedBalancedStrip.centeredBinEndpoint` and `centeredBinFloor` are the
real and integer endpoints.  We use exactly those bins:

```
paperBinLower P δ a k j = floor (centeredBinEndpoint P δ a k j)
paperBinUpper P δ a k j = floor (centeredBinEndpoint P δ a k (j+1)) .
```

`paperBinWidth` is the explicit width `δ * centeredBinEndpoint j - 1`; the
rounding loss is the `-1`, and `paperBinWidth_le_sub` proves

```
δ * centeredBinEndpoint j - 1 ≤ paperBinUpper j - paperBinLower j .
```

## The residual scalar inequality

To bound the exponential factor and the GRH supply error by this width it is
enough that the right endpoint is at most `y`, the left endpoint is at least
`L`, and the single scalar inequality `PaperBandScalarWidthBound` holds:

```
exp ((c D log D) / J) * (2 K) * (1 + log (3 q y))² * sqrt y * log y
  + Ks * (1 + log (3 y))² * sqrt y
  ≤ δ L - 1 .
```

All index dependence has disappeared: `y` is any common upper bound for the
bins, `L` any common lower bound for their left endpoints, and `J` is the
number of bins.  `paperBandGuard_of_scalarBound` checks the per-bin envelope
inequality from it, and `primeBinEnvelopeWidthCore_of_scalarBound` turns it
into `PrimeBinEnvelopeWidthCore` for the paper's bins.

`primeBinCharacterDecay_of_paperBandWidth` composes this with the existing
critical-line prime supply and the existing reduction of
`RandomizedL20_2Decay`, so the manuscript's smooth-character decay on the
paper's bins follows from `PaperBandScalarWidthBound` alone.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and the width is
never zero: it is `δ L - 1` with the rounding loss kept explicitly.
-/

namespace Cogentic.RandomizedL20_2Width

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedL20_2Decay
open Cogentic.RandomizedL20_2Char
open Cogentic.Randomized
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## 1. The manuscript's prime bins -/

/-- The lower integer endpoint of the manuscript's `j`-th prime bin. -/
noncomputable def paperBinLower (P δ : ℝ) (a k j : ℕ) : ℕ :=
  centeredBinFloor P δ a k j

/-- The upper integer endpoint of the manuscript's `j`-th prime bin. -/
noncomputable def paperBinUpper (P δ : ℝ) (a k j : ℕ) : ℕ :=
  centeredBinFloor P δ a k (j + 1)

/-- The explicit binomial width `δ * (lower real endpoint) - 1`.  The `-1`
is the exact integer-rounding loss of `centeredBinFloor`. -/
noncomputable def paperBinWidth (P δ : ℝ) (a k j : ℕ) : ℝ :=
  δ * centeredBinEndpoint P δ a k j - 1

/-- The real lower endpoint advances by the factor `exp δ` from one bin to
the next.  This is the paper's `I_j` relation. -/
theorem centeredBinEndpoint_succ' (P δ : ℝ) (a k j : ℕ) :
    centeredBinEndpoint P δ a k (j + 1) =
      centeredBinEndpoint P δ a k j * Real.exp δ := by
  unfold centeredBinEndpoint
  rw [Nat.cast_add, Nat.cast_one,
    show δ * ((j : ℝ) + 1 - (a : ℝ) / (k : ℝ)) =
      δ * ((j : ℝ) - (a : ℝ) / (k : ℝ)) + δ by ring,
    Real.exp_add, mul_assoc]

/-- **The paper's bin width.**  The integer bin is at least
`δ * (real lower endpoint) - 1` wide.  The `-1` is exactly the floor loss at
both endpoints. -/
theorem paperBinWidth_le_sub {P δ : ℝ} (hP : 0 ≤ P) (a k j : ℕ) :
    paperBinWidth P δ a k j ≤
      (paperBinUpper P δ a k j : ℝ) - (paperBinLower P δ a k j : ℝ) := by
  have hlo : 0 ≤ centeredBinEndpoint P δ a k j :=
    mul_nonneg hP (Real.exp_pos _).le
  have hgap := mul_le_mul_of_nonneg_left (Real.add_one_le_exp δ) hlo
  have hl := Nat.floor_le hlo
  have hu := Nat.lt_floor_add_one (centeredBinEndpoint P δ a k (j + 1))
  unfold paperBinWidth paperBinUpper paperBinLower centeredBinFloor
  nlinarith only [hgap, hl, hu, centeredBinEndpoint_succ' P δ a k j]

/-- The integer endpoints of consecutive bins are ordered. -/
theorem paperBinLower_le_upper {P δ : ℝ} (hP : 0 ≤ P) (hδ : 0 ≤ δ)
    (a k j : ℕ) :
    paperBinLower P δ a k j ≤ paperBinUpper P δ a k j := by
  unfold paperBinLower paperBinUpper
  apply Nat.floor_mono
  unfold centeredBinEndpoint
  apply mul_le_mul_of_nonneg_left _ hP
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left
    (sub_le_sub_right (by exact_mod_cast Nat.le_succ j) _) hδ

/-! ## 2. The per-bin guard on the paper's bins -/

/-- The exact per-bin width inequality on the manuscript's bins: the
stretched GRH envelope plus the prime-supply error fit into the explicit bin
width `paperBinWidth`. -/
def PrimeBinPaperBandGuard (K Ks c : ℝ) (q : ℕ) (n : ℕ)
    (P δ : ℝ) (a k J : ℕ) : Prop :=
  ∀ j < J,
    Real.exp (decayExponent c n / (J : ℝ)) *
        primeBinEnvelopeFactor K q (paperBinUpper P δ a k j) *
        Real.log (paperBinUpper P δ a k j) +
      primeBinSupplyError Ks (paperBinUpper P δ a k j) ≤
        paperBinWidth P δ a k j

/-- **The per-bin guard implies `PrimeBinEnvelopeWidthCore` for the paper's
bins.**  The only extra ingredient is the rounding inequality
`paperBinWidth_le_sub`. -/
theorem primeBinEnvelopeWidthCore_of_paperBandGuard
    {K Ks c : ℝ} {q n : ℕ} {P δ : ℝ} {a k J : ℕ}
    (hP : 0 ≤ P)
    (hguard : PrimeBinPaperBandGuard K Ks c q n P δ a k J) :
    PrimeBinEnvelopeWidthCore (ι := Fin J) K Ks c q
      (fun j => paperBinLower P δ a k j)
      (fun j => paperBinUpper P δ a k j) n := by
  intro j
  have hw := paperBinWidth_le_sub (P := P) (δ := δ) hP a k (j : ℕ)
  have hg := hguard (j : ℕ) j.isLt
  simp only [Fintype.card_fin] at hg ⊢
  exact hg.trans hw

/-! ## 3. The scalar width inequality -/

/-- **The smallest explicit width/interval inequality for the paper's
bands.**  All bin dependence is compressed into a common upper bound `y` for
the right endpoints and a common lower bound `L` for the left endpoints:

```
exp ((c D log D) / J) * 2K (1 + log (3qy))² sqrt y log y
  + Ks (1 + log (3y))² sqrt y
  ≤ δ L - 1 .
```
-/
def PaperBandScalarWidthBound (K Ks c : ℝ) (q : ℕ) (n J : ℕ)
    (δ y L : ℝ) : Prop :=
  Real.exp (decayExponent c n / (J : ℝ)) * (2 * K) *
      (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 * Real.sqrt y * Real.log y +
    Ks * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y ≤
      δ * L - 1

/-- The logarithm base of the envelope is monotone in the right endpoint. -/
private theorem log_three_mul_le {q : ℕ} (hq : 1 ≤ q) {B y : ℝ}
    (hB1 : 1 ≤ B) (hBy : B ≤ y) :
    Real.log (3 * (q : ℝ) * B) ≤ Real.log (3 * (q : ℝ) * y) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)
  have hypos : 0 < y := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hB1) hBy
  apply Real.log_le_log (by positivity)
  exact mul_le_mul_of_nonneg_left hBy (by positivity)

/-- The supply logarithm is monotone in the right endpoint. -/
private theorem log_three_le {B y : ℝ} (hB1 : 1 ≤ B) (hBy : B ≤ y) :
    Real.log (3 * B) ≤ Real.log (3 * y) := by
  have hypos : 0 < y := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hB1) hBy
  apply Real.log_le_log (by positivity)
  linarith

/-- **The scalar width inequality gives the per-bin guard.**  The paper's
relative-width bins have their right endpoint at most `y` and their left
endpoint at least `L`, so the scalar inequality dominates the stretched
envelope and the supply error bin by bin. -/
theorem paperBandGuard_of_scalarBound
    {K Ks c : ℝ} {q n : ℕ} {P δ y L : ℝ} {a k J : ℕ}
    (hK : 0 ≤ K) (hKs : 0 ≤ Ks) (hq : 1 ≤ q) (hδ : 0 ≤ δ)
    (hB1 : ∀ j < J, (1 : ℝ) ≤ (paperBinUpper P δ a k j : ℝ))
    (hBy : ∀ j < J, (paperBinUpper P δ a k j : ℝ) ≤ y)
    (hL : ∀ j < J, L ≤ centeredBinEndpoint P δ a k j)
    (hscalar : PaperBandScalarWidthBound K Ks c q n J δ y L) :
    PrimeBinPaperBandGuard K Ks c q n P δ a k J := by
  intro j hj
  have hB1j := hB1 j hj
  have hByj := hBy j hj
  have hLj := hL j hj
  have hBpos : 0 < (paperBinUpper P δ a k j : ℝ) :=
    lt_of_lt_of_le zero_lt_one hB1j
  have hlogB_nn : 0 ≤ Real.log (paperBinUpper P δ a k j : ℝ) :=
    Real.log_nonneg hB1j
  have hlogB : Real.log (paperBinUpper P δ a k j : ℝ) ≤ Real.log y :=
    Real.log_le_log hBpos hByj
  have hypos : 0 < y := lt_of_lt_of_le hBpos hByj
  have hqr : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlogbase :
      (1 + Real.log (3 * (q : ℝ) * (paperBinUpper P δ a k j : ℝ))) ^ 2 ≤
        (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 := by
    have hlog := log_three_mul_le hq hB1j hByj
    have hbase_nn : 0 ≤ 1 + Real.log (3 * (q : ℝ) * (paperBinUpper P δ a k j : ℝ)) := by
      have : 0 ≤ Real.log (3 * (q : ℝ) * (paperBinUpper P δ a k j : ℝ)) := by
        apply Real.log_nonneg
        have : (1 : ℝ) ≤ 3 * (q : ℝ) * (paperBinUpper P δ a k j : ℝ) := by
          nlinarith only [hqr, hB1j]
        exact this
      linarith
    exact pow_le_pow_left₀ hbase_nn (by linarith) 2
  have hlogbase_supply :
      (1 + Real.log (3 * (paperBinUpper P δ a k j : ℝ))) ^ 2 ≤
        (1 + Real.log (3 * y)) ^ 2 := by
    have hlog := log_three_le hB1j hByj
    have hbase_nn : 0 ≤ 1 + Real.log (3 * (paperBinUpper P δ a k j : ℝ)) := by
      have : 0 ≤ Real.log (3 * (paperBinUpper P δ a k j : ℝ)) := by
        apply Real.log_nonneg
        nlinarith only [hB1j]
      linarith
    exact pow_le_pow_left₀ hbase_nn (by linarith) 2
  have hsqrt_le : Real.sqrt (paperBinUpper P δ a k j : ℝ) ≤ Real.sqrt y :=
    Real.sqrt_le_sqrt hByj
  have henv_factor :
      2 * K * (1 + Real.log (3 * (q : ℝ) * (paperBinUpper P δ a k j : ℝ))) ^ 2 *
          Real.sqrt (paperBinUpper P δ a k j : ℝ) * Real.log (paperBinUpper P δ a k j : ℝ) ≤
        2 * K * (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 *
          Real.sqrt y * Real.log y := by
    have hfirst :
        2 * K * (1 + Real.log (3 * (q : ℝ) * (paperBinUpper P δ a k j : ℝ))) ^ 2 *
            Real.sqrt (paperBinUpper P δ a k j : ℝ) ≤
          2 * K * (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 * Real.sqrt y := by
      have hb_nonneg :
          (0 : ℝ) ≤ 2 * K * (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 := by
        have : 0 ≤ K := hK
        positivity
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hlogbase (by positivity))
        hsqrt_le (Real.sqrt_nonneg _) hb_nonneg
    exact mul_le_mul hfirst hlogB hlogB_nn
      (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (Real.sqrt_nonneg _))
  have henv :
      Real.exp (decayExponent c n / (J : ℝ)) *
          primeBinEnvelopeFactor K q (paperBinUpper P δ a k j) *
          Real.log (paperBinUpper P δ a k j) ≤
        Real.exp (decayExponent c n / (J : ℝ)) * (2 * K) *
          (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 *
          Real.sqrt y * Real.log y := by
    unfold primeBinEnvelopeFactor
    calc
      Real.exp (decayExponent c n / (J : ℝ)) *
          (2 * K * (1 + Real.log (3 * (q : ℝ) * (paperBinUpper P δ a k j : ℝ))) ^ 2 *
            Real.sqrt (paperBinUpper P δ a k j : ℝ)) *
          Real.log (paperBinUpper P δ a k j : ℝ)
          = Real.exp (decayExponent c n / (J : ℝ)) *
              ((2 * K * (1 + Real.log (3 * (q : ℝ) * (paperBinUpper P δ a k j : ℝ))) ^ 2 *
                Real.sqrt (paperBinUpper P δ a k j : ℝ)) *
                Real.log (paperBinUpper P δ a k j : ℝ)) := by ring
      _ ≤ Real.exp (decayExponent c n / (J : ℝ)) *
              ((2 * K * (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 *
                Real.sqrt y) * Real.log y) := by
        exact mul_le_mul_of_nonneg_left henv_factor (Real.exp_pos _).le
      _ = Real.exp (decayExponent c n / (J : ℝ)) * (2 * K) *
            (1 + Real.log (3 * (q : ℝ) * y)) ^ 2 *
            Real.sqrt y * Real.log y := by ring
  have hsupply :
      primeBinSupplyError Ks (paperBinUpper P δ a k j) ≤
        Ks * (1 + Real.log (3 * y)) ^ 2 * Real.sqrt y := by
    unfold primeBinSupplyError
    have hb_nonneg : (0 : ℝ) ≤ Ks * (1 + Real.log (3 * y)) ^ 2 := by
      positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left hlogbase_supply hKs)
      hsqrt_le (Real.sqrt_nonneg _) hb_nonneg
  have hwidth_le : δ * L - 1 ≤ paperBinWidth P δ a k j := by
    unfold paperBinWidth
    have := mul_le_mul_of_nonneg_left hLj hδ
    linarith
  exact (add_le_add henv hsupply).trans (hscalar.trans hwidth_le)

/-- **`PrimeBinEnvelopeWidthCore` for the paper's bins from the scalar
width inequality.** -/
theorem primeBinEnvelopeWidthCore_of_scalarBound
    {K Ks c : ℝ} {q n : ℕ} {P δ y L : ℝ} {a k J : ℕ}
    (hP : 0 ≤ P) (hK : 0 ≤ K) (hKs : 0 ≤ Ks) (hq : 1 ≤ q) (hδ : 0 ≤ δ)
    (hB1 : ∀ j < J, (1 : ℝ) ≤ (paperBinUpper P δ a k j : ℝ))
    (hBy : ∀ j < J, (paperBinUpper P δ a k j : ℝ) ≤ y)
    (hL : ∀ j < J, L ≤ centeredBinEndpoint P δ a k j)
    (hscalar : PaperBandScalarWidthBound K Ks c q n J δ y L) :
    PrimeBinEnvelopeWidthCore (ι := Fin J) K Ks c q
      (fun j => paperBinLower P δ a k j)
      (fun j => paperBinUpper P δ a k j) n :=
  primeBinEnvelopeWidthCore_of_paperBandGuard hP
    (paperBandGuard_of_scalarBound hK hKs hq hδ hB1 hBy hL hscalar)

/-! ## 4. Composing with the critical-line supply and the existing decay -/

/-- **`PrimeBinCharacterDecay` on the manuscript's bins from the scalar
width inequality and the critical-line GRH inputs.**  The constants `K` and
`Ks` are those of the existing prime-product bound and prime-supply estimate;
beyond them only `PaperBandScalarWidthBound` remains. -/
theorem primeBinCharacterDecay_of_paperBandWidth (line : DirichletLZerosOnLine) :
    ∃ K Ks : ℝ, 0 ≤ K ∧ 0 ≤ Ks ∧
      ∀ {c : ℝ} {q : ℕ} {n : ℕ} {P δ y L : ℝ} {a k J : ℕ},
        (hq : 1 ≤ q) →
        (hP : 0 ≤ P) → (hδ : 0 ≤ δ) →
        (hJ : 0 < J) →
        (hA2 : ∀ j < J, 2 ≤ paperBinLower P δ a k j) →
        (hB1 : ∀ j < J, (1 : ℝ) ≤ (paperBinUpper P δ a k j : ℝ)) →
        (hBy : ∀ j < J, (paperBinUpper P δ a k j : ℝ) ≤ y) →
        (hL : ∀ j < J, L ≤ centeredBinEndpoint P δ a k j) →
        PaperBandScalarWidthBound K Ks c q n J δ y L →
        PrimeBinCharacterDecay K c q
          (fun j : Fin J => paperBinLower P δ a k j)
          (fun j : Fin J => paperBinUpper P δ a k j) n := by
  obtain ⟨K, hK, _hb⟩ :=
    primeBinProducts_twist_le (primeBin_product_from_critical_line line)
  obtain ⟨Ks, hKs, hsupply⟩ := primeBin_supply_from_critical_line line
  have hsupply' : ∀ A B : ℕ, 2 ≤ A → A ≤ B →
      (B : ℝ) - (A : ℝ) - primeBinSupplyError Ks B ≤
        ((primeBin A B).card : ℝ) * Real.log B := by
    intro A B hA hAB
    simpa only [primeBinSupplyError] using hsupply A B hA hAB
  refine ⟨K, Ks, hK, hKs, ?_⟩
  intro c q n P δ y L a k J hq hP hδ hJ hA2 hB1 hBy hL hscalar
  have hdisj : Pairwise fun i j : Fin J =>
      Disjoint (primeBin (paperBinLower P δ a k i) (paperBinUpper P δ a k i))
        (primeBin (paperBinLower P δ a k j) (paperBinUpper P δ a k j)) := by
    intro i j hij
    exact centeredBin_disjoint hP hδ a k (Fin.val_injective.ne hij)
  have hA : ∀ i : Fin J, 2 ≤ paperBinLower P δ a k i :=
    fun i => hA2 (i : ℕ) i.isLt
  have hAB : ∀ i : Fin J, paperBinLower P δ a k i ≤ paperBinUpper P δ a k i :=
    fun i => paperBinLower_le_upper hP hδ a k (i : ℕ)
  have hcard : 0 < Fintype.card (Fin J) := by simpa using hJ
  exact primeBinCharacterDecay_of_width hK hsupply' hdisj hcard hA hAB
    (primeBinEnvelopeWidthCore_of_scalarBound hP hK hKs hq hδ hB1 hBy hL hscalar)

/-! ## Axiom audit -/

#print axioms centeredBinEndpoint_succ'
#print axioms paperBinWidth_le_sub
#print axioms paperBinLower_le_upper
#print axioms primeBinEnvelopeWidthCore_of_paperBandGuard
#print axioms paperBandGuard_of_scalarBound
#print axioms primeBinEnvelopeWidthCore_of_scalarBound
#print axioms primeBinCharacterDecay_of_paperBandWidth

end

end Cogentic.RandomizedL20_2Width
