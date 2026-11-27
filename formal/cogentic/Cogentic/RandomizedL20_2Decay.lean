import Cogentic.RandomizedL20_2Saddle
import Cogentic.RandomizedPrimeBinSupply
import Cogentic.RandomizedPrimeProductPlancherel

set_option linter.style.haveILetI false

/-!
# L20.2: reducing the prime-bin character decay

`Cogentic.RandomizedL20_2Char` and `Cogentic.RandomizedL20_2Saddle` reduce the
L20.2 smooth-character inputs to the GRH prime-bin product estimate
`Randomized.PrimeBinProductBound` plus the remaining explicit statement

```
PrimeBinCharacterDecay K c q A B n :
  primeBinRelativeEnvelope K q A B ≤
    exp (-(c D log D)) * (primeBinProducts A B).card .
```

This file isolates that statement and reduces it as far as the existing GRH
inputs allow.

## What is, and is not, analytic here

The GRH prime-bin estimates (`PrimeBinProductBound` /
`primeBin_product_from_critical_line`) bound *character sums*.  They have no
information about the cardinality of `primeBinProducts A B`, which is the
normalising factor on the right-hand side of `PrimeBinCharacterDecay`.  Indeed
the decay statement is false for a bin that contains no prime: with
`A = B = 2` the product set is empty, the envelope is positive, and the
right-hand side is zero.  `primeBinCharacterDecay_false_of_emptyBin` records
this, so the decay cannot be obtained from GRH alone.

The genuine remaining input is therefore a *counting* statement.  We give two
explicit forms, from finest to coarsest.

1. `PrimeBinEnvelopeDecayCore` is the per-bin cardinality inequality
   ```
   envelopeFactor K q (B i) ≤ exp (-(c D log D) / #ι) * #(primeBin (A i) (B i)) .
   ```
   `primeBinCharacterDecay_of_core` multiplies these over `i` and uses
   `primeBinProducts_card` to obtain `PrimeBinCharacterDecay`.  This is the
   statement that literally supplies the missing normalisation.

2. `PrimeBinEnvelopeWidthCore` replaces the prime-bin cardinality by the
   interval width via the existing GRH prime-supply estimate
   `Randomized.primeBin_supply_from_critical_line`:
   ```
   exp ((c D log D) / #ι) * envelopeFactor K q (B i) * log (B i)
     + Ks (1 + log (3 B i))^2 sqrt (B i) ≤ B i - A i .
   ```
   `primeBinEnvelopeDecayCore_of_width` proves that this pure real-arithmetic
   width condition implies the cardinality form, and
   `primeBinCharacterDecay_of_criticalLine` states the resulting reduction with
   the supply constant extracted from `DirichletLZerosOnLine`.

Thus the residual analytic `Prop` isolated here is exactly
`PrimeBinEnvelopeWidthCore K Ks c q A B n` (with `Ks` the supply constant);
everything else in the reduction is proved from the existing GRH inputs.

## Composition with GRH and the Plancherel residue energy

`primeBinTwist_le_of_criticalLine` combines `PrimeBinProductBound` with the
reduced decay and returns the actual nonprincipal twist bound at the manuscript
rate.  `smoothCharacterError_primeBin_le_of_widthCondition` converts it into a
bound on `smoothCharacterError`, and
`primeBinResidueEnergy_le_of_widthCondition` applies the Plancherel identity
`Randomized.classMass_centered_sq_le` to bound the squared residue discrepancy.
`primeBinMellinEnergy_zero_le_of_widthCondition` rewrites the `s = 0` Mellin
energy of `Randomized.primeBinMellinEnergy_le_of_fit` into the same residue
energy and transfers the bound.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.  No error, mass, or
cardinality is set to zero; the empty-bin counterexample shows exactly where the
counting input is indispensable.
-/

namespace Cogentic.RandomizedL20_2Decay

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedL20_2Sub
open Cogentic.RandomizedL20_2Char
open Cogentic.RandomizedL20_2Saddle
open Cogentic.Randomized
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.Window

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## 1. The decay exponent and the per-bin envelope -/

/-- The manuscript decay exponent `c D log D`, with `D = paperD n` and
`log D = scale n`. -/
def decayExponent (c : ℝ) (n : ℕ) : ℝ :=
  c * paperD n * scale n

/-- One factor of the GRH prime-bin envelope
`∏ i, 2 K (1 + log (3 q B i))^2 sqrt (B i)`. -/
def primeBinEnvelopeFactor (K : ℝ) (q B : ℕ) : ℝ :=
  2 * K * (1 + Real.log (3 * q * B)) ^ 2 * Real.sqrt B

/-- One factor of the GRH prime-supply error
`K (1 + log (3 B))^2 sqrt B`. -/
def primeBinSupplyError (Ks : ℝ) (B : ℕ) : ℝ :=
  Ks * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt B

/-- The GRH envelope is the product of its per-bin factors. -/
theorem primeBinRelativeEnvelope_eq_prod (K : ℝ) (q : ℕ) (A B : ι → ℕ) :
    primeBinRelativeEnvelope K q A B =
      ∏ i, primeBinEnvelopeFactor K q (B i) :=
  rfl

/-! ## 2. The exact per-bin cardinality input -/

/-- A concrete per-bin statement that supplies the normalisation in
`PrimeBinCharacterDecay`: each envelope factor is at most the manuscript decay
(divided evenly among the `#ι` bins) times the actual number of primes in that
bin. -/
def PrimeBinEnvelopeDecayCore (K c : ℝ) (q : ℕ) (A B : ι → ℕ) (n : ℕ) : Prop :=
  ∀ i, primeBinEnvelopeFactor K q (B i) ≤
    Real.exp (-(decayExponent c n / (Fintype.card ι))) *
      ((primeBin (A i) (B i)).card : ℝ)

/-- **The per-bin cardinality input implies the prime-bin character decay.**
The proof is the product of the per-bin inequalities; the exponential factors
multiply to `exp (-(c D log D))` because there are exactly `#ι` of them. -/
theorem primeBinCharacterDecay_of_core
    {K c : ℝ} {q : ℕ} {A B : ι → ℕ} {n : ℕ}
    (hK : 0 ≤ K)
    (hdisj : Pairwise fun i j => Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (hcard : 0 < Fintype.card ι)
    (hcore : PrimeBinEnvelopeDecayCore K c q A B n) :
    PrimeBinCharacterDecay K c q A B n := by
  unfold PrimeBinCharacterDecay
  rw [primeBinRelativeEnvelope_eq_prod, primeBinProducts_card A B hdisj, Nat.cast_prod]
  have hm : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hcard.ne'
  have hprod :
      (∏ i, primeBinEnvelopeFactor K q (B i)) ≤
        ∏ i, Real.exp (-(decayExponent c n / (Fintype.card ι))) *
          ((primeBin (A i) (B i)).card : ℝ) := by
    exact Finset.prod_le_prod
      (fun i _ => by
        unfold primeBinEnvelopeFactor
        positivity)
      (fun i _ => hcore i)
  calc
    (∏ i, primeBinEnvelopeFactor K q (B i))
        ≤ ∏ i, Real.exp (-(decayExponent c n / (Fintype.card ι))) *
            ((primeBin (A i) (B i)).card : ℝ) := hprod
    _ = (∏ i, Real.exp (-(decayExponent c n / (Fintype.card ι)))) *
          ∏ i, ((primeBin (A i) (B i)).card : ℝ) := by
      rw [Finset.prod_mul_distrib]
    _ = Real.exp (-(decayExponent c n / (Fintype.card ι))) ^ (Fintype.card ι) *
          ∏ i, ((primeBin (A i) (B i)).card : ℝ) := by
      rw [Finset.prod_const, Finset.card_univ]
    _ = Real.exp (-(decayExponent c n)) *
          ∏ i, ((primeBin (A i) (B i)).card : ℝ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    _ = Real.exp (-c * paperD n * scale n) *
          ∏ i, ((primeBin (A i) (B i)).card : ℝ) := by
      rw [decayExponent]
      congr 1
      ring_nf

/-! ## 3. Reducing the cardinality input to an interval-width condition -/

/-- The pure real-arithmetic width condition obtained from the GRH prime-supply
estimate.  It says that the width `B i - A i` covers both the stretched envelope
term and the GRH supply error. -/
def PrimeBinEnvelopeWidthCore (K Ks c : ℝ) (q : ℕ) (A B : ι → ℕ) (n : ℕ) : Prop :=
  ∀ i,
    Real.exp (decayExponent c n / (Fintype.card ι)) *
        primeBinEnvelopeFactor K q (B i) * Real.log (B i) +
      primeBinSupplyError Ks (B i) ≤ (B i : ℝ) - (A i : ℝ)

omit [DecidableEq ι] in
/-- **The width condition implies the per-bin cardinality input.**  This is the
only place where the GRH prime-supply count is used: it converts the lower bound
on the number of primes in a bin into the width condition. -/
theorem primeBinEnvelopeDecayCore_of_width
    {K Ks c : ℝ} {q : ℕ} {A B : ι → ℕ} {n : ℕ}
    (hsupply : ∀ A B : ℕ, 2 ≤ A → A ≤ B →
      (B : ℝ) - (A : ℝ) - primeBinSupplyError Ks B ≤
        ((primeBin A B).card : ℝ) * Real.log B)
    (hcard : 0 < Fintype.card ι)
    (hA : ∀ i, 2 ≤ A i) (hAB : ∀ i, A i ≤ B i)
    (hwidth : PrimeBinEnvelopeWidthCore K Ks c q A B n) :
    PrimeBinEnvelopeDecayCore K c q A B n := by
  intro i
  have hm : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hcard.ne'
  have hlog : 0 < Real.log (B i : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < B i by have := hA i; have := hAB i; omega)
  have hs := hsupply (A i) (B i) (hA i) (hAB i)
  have hw := hwidth i
  have hle :
      Real.exp (decayExponent c n / (Fintype.card ι)) *
          primeBinEnvelopeFactor K q (B i) * Real.log (B i) ≤
        ((primeBin (A i) (B i)).card : ℝ) * Real.log (B i) := by
    linarith only [hs, hw]
  have hdiv :
      Real.exp (decayExponent c n / (Fintype.card ι)) *
          primeBinEnvelopeFactor K q (B i) ≤
        ((primeBin (A i) (B i)).card : ℝ) := by
    have h' : Real.exp (decayExponent c n / (Fintype.card ι)) *
        primeBinEnvelopeFactor K q (B i) ≤
        (((primeBin (A i) (B i)).card : ℝ) * Real.log (B i)) / Real.log (B i) := by
      rw [le_div_iff₀ hlog]
      exact hle
    rwa [mul_div_cancel_right₀ _ hlog.ne'] at h'
  have hpos : 0 < Real.exp (-(decayExponent c n / (Fintype.card ι))) :=
    Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_left hdiv hpos.le
  have hsimp :
      Real.exp (-(decayExponent c n / (Fintype.card ι))) *
          (Real.exp (decayExponent c n / (Fintype.card ι)) *
            primeBinEnvelopeFactor K q (B i)) =
        primeBinEnvelopeFactor K q (B i) := by
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  rwa [hsimp] at hmul

/-- **Prime-bin character decay from the GRH supply count and the explicit width
condition.**  The supply constant `Ks` is an input here; the next theorem
extracts it from `DirichletLZerosOnLine`. -/
theorem primeBinCharacterDecay_of_width
    {K Ks c : ℝ} {q : ℕ} {A B : ι → ℕ} {n : ℕ}
    (hK : 0 ≤ K)
    (hsupply : ∀ A B : ℕ, 2 ≤ A → A ≤ B →
      (B : ℝ) - (A : ℝ) - primeBinSupplyError Ks B ≤
        ((primeBin A B).card : ℝ) * Real.log B)
    (hdisj : Pairwise fun i j => Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (hcard : 0 < Fintype.card ι)
    (hA : ∀ i, 2 ≤ A i) (hAB : ∀ i, A i ≤ B i)
    (hwidth : PrimeBinEnvelopeWidthCore K Ks c q A B n) :
    PrimeBinCharacterDecay K c q A B n :=
  primeBinCharacterDecay_of_core hK hdisj hcard
    (primeBinEnvelopeDecayCore_of_width hsupply hcard hA hAB hwidth)

/-! ## 4. The reduction from the critical line -/

/-- **`PrimeBinCharacterDecay` reduced to an explicit width condition and the
critical-line GRH input.**  `primeBin_supply_from_critical_line` supplies the
prime-count lower bound with a constant `Ks`; beyond it, only the real
inequality `PrimeBinEnvelopeWidthCore` remains. -/
theorem primeBinCharacterDecay_of_criticalLine (line : DirichletLZerosOnLine) :
    ∃ Ks : ℝ, 0 ≤ Ks ∧
      ∀ {K c : ℝ} {q : ℕ} {A B : ι → ℕ} {n : ℕ},
        (hK : 0 ≤ K) →
        (hdisj : Pairwise fun i j =>
          Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
        (hcard : 0 < Fintype.card ι) →
        (hA : ∀ i, 2 ≤ A i) → (hAB : ∀ i, A i ≤ B i) →
        PrimeBinEnvelopeWidthCore K Ks c q A B n →
        PrimeBinCharacterDecay K c q A B n := by
  obtain ⟨Ks, hKs, hsupply⟩ := primeBin_supply_from_critical_line line
  refine ⟨Ks, hKs, ?_⟩
  intro K c q A B n hK hdisj hcard hA hAB hwidth
  exact primeBinCharacterDecay_of_width hK
    (by simpa [primeBinSupplyError] using hsupply) hdisj hcard hA hAB hwidth

/-! ## 5. Composing with the GRH product bound -/

/-- **The actual nonprincipal twist bound at the manuscript rate.**  The GRH
product estimate `primeBin_product_from_critical_line` supplies the envelope
constant `K`; the reduced decay supplies the factor `exp (-(c D log D))` and the
normalisation by the product-set cardinality. -/
theorem primeBinTwist_le_of_criticalLine (line : DirichletLZerosOnLine) :
    ∃ K Ks : ℝ, 0 ≤ K ∧ 0 ≤ Ks ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ {c : ℝ} {A B : ι → ℕ} {n : ℕ},
        (hdisj : Pairwise fun i j =>
          Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
        (hcard : 0 < Fintype.card ι) →
        (hA : ∀ i, 2 ≤ A i) → (hAB : ∀ i, A i ≤ B i) →
        PrimeBinEnvelopeWidthCore K Ks c q A B n →
        ‖twist (primeBinProducts A B) (fun _ => 1) χ‖ ≤
          Real.exp (-(decayExponent c n)) *
            ((primeBinProducts A B).card : ℝ) := by
  obtain ⟨K, hK, hbound⟩ :=
    primeBinProducts_twist_le (primeBin_product_from_critical_line line)
  obtain ⟨Ks, hKs, hdecay⟩ := primeBinCharacterDecay_of_criticalLine
    (ι := ι) line
  refine ⟨K, Ks, hK, hKs, ?_⟩
  intro q _ χ hχ c A B n hdisj hcard hA hAB hwidth
  have hdec := hdecay hK hdisj hcard hA hAB hwidth
  unfold PrimeBinCharacterDecay at hdec
  simpa [decayExponent] using
    (hbound q χ hχ A B hA hAB hdisj).trans hdec

/-- **The reduced decay feeds the existing L20.2 smooth-character input.**
With `K` from `PrimeBinProductBound` and `Ks` from the critical-line supply
estimate, a width condition for every ledger index produces
`SmoothCharacterSumBound` for the concrete prime-bin smooth-character data. -/
theorem smoothCharacterSumBound_of_widthCondition
    (line : DirichletLZerosOnLine) :
    ∃ K Ks : ℝ, 0 ≤ K ∧ 0 ≤ Ks ∧
      ∀ (q : ℕ) [NeZero q] {c : ℝ} {A B : ι → ℕ}
        (hcard : 0 < (primeBinProducts A B).card),
        (hdisj : Pairwise fun i j =>
          Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
        (hbin : 0 < Fintype.card ι) →
        (hA : ∀ i, 2 ≤ A i) → (hAB : ∀ i, A i ≤ B i) →
        (hc : 0 < c) →
        (∀ n, PrimeBinEnvelopeWidthCore K Ks c q A B n) →
        SmoothCharacterSumBound
          (fun _ => smoothCharacterError (primeBinSmoothCharacterData q A B hcard)) c := by
  obtain ⟨K, hK, hbound⟩ :=
    primeBinProducts_twist_le (primeBin_product_from_critical_line line)
  obtain ⟨Ks, hKs, hdecay⟩ := primeBinCharacterDecay_of_criticalLine (ι := ι) line
  refine ⟨K, Ks, hK, hKs, ?_⟩
  intro q _ c A B hcard hdisj hbin hA hAB hc hwidth
  refine smoothCharacterSumBound_of_primeBinReduction hc A B hcard
    ⟨hK, (fun χ hχ => hbound q χ hχ A B hA hAB hdisj), (fun n => ?_)⟩
  exact hdecay hK hdisj hbin hA hAB (hwidth n)

/-! ## 6. The Plancherel/Mellin residue energy -/

/-- The Plancherel residue energy corresponding to the prime-bin product set. -/
def primeBinResidueEnergy (q : ℕ) [NeZero q] {ι : Type} [Fintype ι]
    [DecidableEq ι] (A B : ι → ℕ) : ℝ :=
  ∑ r : (ZMod q)ˣ,
    ‖classMass (primeBinProducts A B) (fun _ => 1) r -
      twist (primeBinProducts A B) (fun _ => 1)
        (1 : DirichletCharacter ℂ q) / q.totient‖ ^ 2

/-- The smooth-character error of the prime-bin product set is bounded by the
reduced decay, hence by the width condition. -/
theorem smoothCharacterError_primeBin_le_of_widthCondition
    (line : DirichletLZerosOnLine) :
    ∃ K Ks : ℝ, 0 ≤ K ∧ 0 ≤ Ks ∧
      ∀ (q : ℕ) [NeZero q] {c : ℝ} {A B : ι → ℕ} {n : ℕ}
        (hcard : 0 < (primeBinProducts A B).card),
        (hdisj : Pairwise fun i j =>
          Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
        (hbin : 0 < Fintype.card ι) →
        (hA : ∀ i, 2 ≤ A i) → (hAB : ∀ i, A i ≤ B i) →
        PrimeBinEnvelopeWidthCore K Ks c q A B n →
        smoothCharacterError (primeBinSmoothCharacterData q A B hcard) ≤
          Real.exp (-(decayExponent c n)) := by
  obtain ⟨K, Ks, hK, hKs, htwist⟩ := primeBinTwist_le_of_criticalLine (ι := ι) line
  refine ⟨K, Ks, hK, hKs, ?_⟩
  intro q _ c A B n hcard hdisj hbin hA hAB hwidth
  refine smoothCharacterError_le (primeBinSmoothCharacterData q A B hcard)
    (Real.exp_pos _).le ?_
  intro χ hχ
  simpa [primeBinSmoothCharacterData] using
    htwist q χ hχ hdisj hbin hA hAB hwidth

/-- **The Plancherel residue energy is bounded by the reduced decay.**  This is
`Randomized.classMass_centered_sq_le`, the Plancherel identity
`classMass_centered_plancherel`, applied to the prime-bin product set. -/
theorem primeBinResidueEnergy_le_of_widthCondition
    (line : DirichletLZerosOnLine) :
    ∃ K Ks : ℝ, 0 ≤ K ∧ 0 ≤ Ks ∧
      ∀ (q : ℕ) [NeZero q] {c : ℝ} {A B : ι → ℕ} {n : ℕ}
        (_hcard : 0 < (primeBinProducts A B).card),
        (hdisj : Pairwise fun i j =>
          Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
        (hbin : 0 < Fintype.card ι) →
        (hA : ∀ i, 2 ≤ A i) → (hAB : ∀ i, A i ≤ B i) →
        PrimeBinEnvelopeWidthCore K Ks c q A B n →
        primeBinResidueEnergy q A B ≤
          (Real.exp (-(decayExponent c n)) *
            ((primeBinProducts A B).card : ℝ)) ^ 2 := by
  obtain ⟨K, Ks, hK, hKs, hchar⟩ :=
    smoothCharacterError_primeBin_le_of_widthCondition (ι := ι) line
  refine ⟨K, Ks, hK, hKs, ?_⟩
  intro q _ c A B n _hcard hdisj hbin hA hAB hwidth
  letI : NeZero (primeBinSmoothCharacterData q A B _hcard).q := ‹NeZero q›
  exact centeredResidueEnergy_le_of_smoothCharacterError
    (primeBinSmoothCharacterData q A B _hcard)
    (hchar q _hcard hdisj hbin hA hAB hwidth)

/-- The `s = 0` Mellin residue energy is the Plancherel residue energy. -/
theorem primeBinMellinEnergy_zero_eq (q : ℕ) [NeZero q] {ι : Type} [Fintype ι]
    [DecidableEq ι] (A B : ι → ℕ) :
    primeBinMellinEnergy q A B 0 = primeBinResidueEnergy q A B := by
  unfold primeBinMellinEnergy primeBinResidueEnergy mellinClassError
  simp

/-- **The `s = 0` Mellin energy inherits the Plancherel bound.**  The Mellin
energy of `Randomized.primeBinMellinEnergy_le_of_fit` is the same residue energy
at height zero; the reduced character decay therefore bounds this energy too. -/
theorem primeBinMellinEnergy_zero_le_of_widthCondition
    (line : DirichletLZerosOnLine) :
    ∃ K Ks : ℝ, 0 ≤ K ∧ 0 ≤ Ks ∧
      ∀ (q : ℕ) [NeZero q] {c : ℝ} {A B : ι → ℕ} {n : ℕ}
        (_hcard : 0 < (primeBinProducts A B).card),
        (hdisj : Pairwise fun i j =>
          Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
        (hbin : 0 < Fintype.card ι) →
        (hA : ∀ i, 2 ≤ A i) → (hAB : ∀ i, A i ≤ B i) →
        PrimeBinEnvelopeWidthCore K Ks c q A B n →
        primeBinMellinEnergy q A B 0 ≤
          (Real.exp (-(decayExponent c n)) *
            ((primeBinProducts A B).card : ℝ)) ^ 2 := by
  obtain ⟨K, Ks, hK, hKs, henergy⟩ :=
    primeBinResidueEnergy_le_of_widthCondition (ι := ι) line
  refine ⟨K, Ks, hK, hKs, ?_⟩
  intro q _ c A B n _hcard hdisj hbin hA hAB hwidth
  rw [primeBinMellinEnergy_zero_eq]
  exact henergy q _hcard hdisj hbin hA hAB hwidth

/-! ## 7. The counting input is indispensable -/

/-- **The decay is not a consequence of GRH alone.**  For the single bin
`(2, 2]` there are no primes, so `primeBinProducts` is empty, the envelope is
positive, and the right-hand side of `PrimeBinCharacterDecay` is zero.  This is
the precise reason the per-bin cardinality/width input cannot be removed. -/
theorem primeBinCharacterDecay_false_of_emptyBin
    {K c : ℝ} (hK : 0 < K) (q n : ℕ) :
    ¬ PrimeBinCharacterDecay K c q (fun _ : Unit => 2) (fun _ : Unit => 2) n := by
  intro h
  unfold PrimeBinCharacterDecay at h
  have hlogpos : 0 < 1 + Real.log (3 * (q : ℝ) * 2) := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst q
      norm_num
    · have h6 : (1 : ℝ) < 3 * (q : ℝ) * 2 := by
        have h2 : (2 : ℕ) < 3 * q * 2 := by omega
        have h2R : (2 : ℝ) < 3 * (q : ℝ) * 2 := by exact_mod_cast h2
        linarith
      have := Real.log_pos h6
      linarith
  have henv : 0 < primeBinRelativeEnvelope K q
      (fun _ : Unit => 2) (fun _ : Unit => 2) := by
    simp only [primeBinRelativeEnvelope, Finset.prod_const, Finset.card_univ,
      Fintype.card_unit, pow_one]
    have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
    positivity
  have hcard :
      (primeBinProducts (fun _ : Unit => 2) (fun _ : Unit => 2)).card = 0 := by
    simp [primeBinProducts, primeBin]
  rw [hcard] at h
  norm_num at h
  linarith

/-! ## Axiom audit -/

#print axioms primeBinRelativeEnvelope_eq_prod
#print axioms primeBinCharacterDecay_of_core
#print axioms primeBinEnvelopeDecayCore_of_width
#print axioms primeBinCharacterDecay_of_width
#print axioms primeBinCharacterDecay_of_criticalLine
#print axioms primeBinTwist_le_of_criticalLine
#print axioms smoothCharacterSumBound_of_widthCondition
#print axioms smoothCharacterError_primeBin_le_of_widthCondition
#print axioms primeBinResidueEnergy_le_of_widthCondition
#print axioms primeBinMellinEnergy_zero_eq
#print axioms primeBinMellinEnergy_zero_le_of_widthCondition
#print axioms primeBinCharacterDecay_false_of_emptyBin

end

end Cogentic.RandomizedL20_2Decay
