import Cogentic.RandomizedL20_2DecayNonempty
import Cogentic.RandomizedL20_4RationalSource

set_option linter.style.haveILetI false

/-!
# L20.2: explicit CRT and smooth-character error budgets

`Cogentic.RandomizedL20_2Sub` proves the truncated geometric CRT tail

```
geometricCRTError n = exp (-1) ^ crtTruncation n / (1 - exp (-1))
```

and bounds it by `exp (-2 · paperD n · scale n)`.  The rational-source file
`Cogentic.RandomizedL20_4RationalSource` then combines that CRT budget with the
concrete smooth-character error into `paperEpsRat`, with the combined rate
`min 2 cChar`.

This file records those two budget facts in their sharp explicit forms.

## The CRT budget

* `geometricCRTError_pos`: the CRT defect is *strictly positive* at every
  ledger index, so the budget is a genuine nonzero error.
* `geometricCRTError_le_exp_paperScale`: for any `c ≤ 2` and `0 ≤ scale n`,
  `geometricCRTError n ≤ exp (-c · paperD n · scale n)`.  This is the exact
  exponential form used by the rational source, and the constant `2` is the
  truncated geometric constant.
* `geometricCRTError_le_exp_scale_eventually`: for every `c > 0` (indeed every
  real `c`), eventually `geometricCRTError n ≤ exp (-c · scale n)`.  This is
  the `SubexpLoss` form `D^{-B}` with `D = exp (scale n)`.
* `geometricCRTError_subexp`: the CRT defect is a `SubexpLoss`.

## The `paperEpsRat` budget

* `paperEpsRat_le_two_exp_of_budgets`: the abstract budget theorem.  A
  `TruncatedGeometricCRTLaw crtError cCRT` and a
  `SmoothCharacterSumBound charError cChar` give
  ```
  paperEpsRat crtError charError n ≤ 2 exp (-(min cCRT cChar) · paperD n · scale n)
  ```
  eventually.  The `min` is sharp for the literal sum of the two nonnegative
  errors; the factor `2` is not absorbed by setting a term to zero.
* `paperEpsRat_subInputs_le_two_exp` and
  `paperCharEpsRat_le_two_exp_of_char_sum` instantiate the abstract theorem
  with `cCRT = 2` and the concrete character data, recovering the `min 2 cChar`
  rate of the rational source.

## The GRH input

The concrete smooth-character budget for prime-bin product sets is the only
place where a Dirichlet input can enter.  The smallest explicit Proposition is
`SmoothCharacterGRHInput`, definitionally `PrimeBinProductBound`; it is *proved*
from `DirichletLZerosOnLine` by `primeBin_product_from_critical_line`
(`smoothCharacterGRHInput_of_criticalLine`).  Everything else in the reduction
is the arithmetic width/counting condition `PrimeBinEnvelopeWidthCore`, which
does not mention `L`-functions.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.  The errors are the
actual geometric tail and the actual normalized smooth-character error; no
error is set to zero.
-/

namespace Cogentic.RandomizedL20_2CRTBudget

open Filter Real
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedL20_2Sub
open Cogentic.RandomizedL20_2Char
open Cogentic.RandomizedL20_2Saddle
open Cogentic.RandomizedL20_4RationalSource
open Cogentic.RandomizedL20_4Interior
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedL20_2Decay
open Cogentic.RandomizedL20_2DecayNonempty
open Cogentic.Randomized
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.Window

noncomputable section

/-! ## 1. The explicit truncated-geometric CRT budget -/

/-- The truncated geometric CRT remainder is strictly positive at every ledger
index.  The numerator is a positive power and the denominator is positive
because `exp (-1) < 1`. -/
theorem geometricCRTError_pos (n : ℕ) : 0 < geometricCRTError n := by
  unfold geometricCRTError
  have hlt : exp (-1 : ℝ) < 1 := by
    rw [exp_neg]
    exact inv_lt_one_of_one_lt₀ (by linarith [Real.exp_one_gt_two])
  exact div_pos (pow_pos (exp_pos (-1 : ℝ)) _) (sub_pos.mpr hlt)

/-- **The CRT budget at the rational-source rate.**  For any constant `c ≤ 2`
and any ledger index with nonnegative scale, the truncated geometric tail is at
most `exp (-c · paperD n · scale n)`.  The constant `2` is the geometric
constant proved in `geometricCRTError_le`. -/
theorem geometricCRTError_le_exp_paperScale {c : ℝ} {n : ℕ}
    (hc : c ≤ 2) (hn : 0 ≤ scale n) :
    geometricCRTError n ≤ exp (-c * paperD n * scale n) := by
  refine (geometricCRTError_le n).trans (exp_le_exp.mpr ?_)
  have hX : 0 ≤ paperD n * scale n := mul_nonneg (paperD_pos n).le hn
  have hle : c * (paperD n * scale n) ≤ 2 * (paperD n * scale n) :=
    mul_le_mul_of_nonneg_right hc hX
  nlinarith only [hle]

/-- **The CRT budget on the bare ledger scale.**  For any `c ≤ 2` and
`0 ≤ scale n`, we have `geometricCRTError n ≤ exp (-c · scale n)`.  This is the
explicit `exp (-c · scale n)` tail bound; it is weaker than the paper rate but
records the exact constant `2` on the ledger scale. -/
theorem geometricCRTError_le_exp_scale_of_nonneg {c : ℝ} {n : ℕ}
    (hc : c ≤ 2) (hn : 0 ≤ scale n) :
    geometricCRTError n ≤ exp (-c * scale n) := by
  refine (geometricCRTError_le n).trans (exp_le_exp.mpr ?_)
  have hD : 1 ≤ paperD n := by
    unfold paperD
    calc
      (1 : ℝ) = exp 0 := by simp
      _ ≤ exp (scale n) := exp_le_exp.mpr hn
  have hcD : c ≤ 2 * paperD n := by
    have hpos := paperD_pos n
    nlinarith only [hc, hD, hpos]
  have hmul : c * scale n ≤ 2 * paperD n * scale n :=
    mul_le_mul_of_nonneg_right hcD hn
  nlinarith only [hmul]

/-- **The CRT tail on the ledger scale, eventually for every constant.**  Since
`paperD n = exp (scale n) → ∞`, the geometric tail beats `exp (-c · scale n)`
for every fixed real `c`. -/
theorem geometricCRTError_le_exp_scale_eventually (c : ℝ) :
    ∀ᶠ n : ℕ in atTop, geometricCRTError n ≤ exp (-c * scale n) := by
  have hexp : Tendsto (fun n : ℕ => paperD n) atTop atTop := by
    change Tendsto (fun n : ℕ => Real.exp (scale n)) atTop atTop
    exact Real.tendsto_exp_atTop.comp scale_grows
  filter_upwards [hexp.eventually_ge_atTop (max 0 (c / 2)),
    scale_grows.eventually_ge_atTop 0] with n hD hs
  refine (geometricCRTError_le n).trans (exp_le_exp.mpr ?_)
  have hDc : c / 2 ≤ paperD n := (le_max_right _ _).trans hD
  have hc : c ≤ 2 * paperD n := by linarith
  have hmul : c * scale n ≤ 2 * paperD n * scale n :=
    mul_le_mul_of_nonneg_right hc hs
  nlinarith only [hmul]

/-- **The truncated geometric CRT tail is a `SubexpLoss`.**  This is the
`D^{-B}` form of the CRT budget, derived directly from the geometric law rather
than from an abstract `L20_2Inputs` field. -/
theorem geometricCRTError_subexp : SubexpLoss geometricCRTError := by
  intro B _
  exact geometricCRTError_le_exp_scale_eventually B

/-! ## 2. The `paperEpsRat` CRT plus smooth-character budget -/

/-- **The abstract `min` budget for `paperEpsRat`.**  A truncated geometric CRT
law with rate `cCRT` and a smooth-character sum bound with rate `cChar` give,
eventually, the literal sum bound
`crtError n + charError n ≤ 2 exp (-(min cCRT cChar) · paperD n · scale n)`.

Both summands are retained: the factor `2` is the sum of two equal exponentials
and is not removed by setting either error to zero. -/
theorem paperEpsRat_le_two_exp_of_budgets
    {crtError charError : ℕ → ℝ} {cCRT cChar : ℝ}
    (hcrt : TruncatedGeometricCRTLaw crtError cCRT)
    (hchar : SmoothCharacterSumBound charError cChar) :
    ∀ᶠ n : ℕ in atTop,
      paperEpsRat crtError charError n ≤
        2 * exp (-(min cCRT cChar) * paperD n * scale n) := by
  filter_upwards [scale_grows.eventually_ge_atTop 0] with n hs
  have hX : 0 ≤ paperD n * scale n := mul_nonneg (paperD_pos n).le hs
  have hcrt' : crtError n ≤ exp (-(min cCRT cChar) * (paperD n * scale n)) := by
    refine (hcrt.2 n).2.trans (exp_le_exp.mpr ?_)
    have hle : min cCRT cChar ≤ cCRT := min_le_left _ _
    nlinarith only [hle, hX]
  have hchar' : charError n ≤ exp (-(min cCRT cChar) * (paperD n * scale n)) := by
    refine (hchar.2 n).2.trans (exp_le_exp.mpr ?_)
    have hle : min cCRT cChar ≤ cChar := min_le_right _ _
    nlinarith only [hle, hX]
  rw [paperEpsRat_apply]
  calc
    crtError n + charError n
        ≤ exp (-(min cCRT cChar) * (paperD n * scale n)) +
            exp (-(min cCRT cChar) * (paperD n * scale n)) :=
      add_le_add hcrt' hchar'
    _ = 2 * exp (-(min cCRT cChar) * paperD n * scale n) := by
      rw [show -(min cCRT cChar) * (paperD n * scale n) =
        -(min cCRT cChar) * paperD n * scale n by ring]
      ring

/-- **The `paperEpsRat` budget is subexponential.**  If both rates are positive,
the `min` rate is positive and the two-exponential bound is a `SubexpLoss`. -/
theorem paperEpsRat_subexp_of_budgets
    {crtError charError : ℕ → ℝ} {cCRT cChar : ℝ}
    (hcrt : TruncatedGeometricCRTLaw crtError cCRT)
    (hchar : SmoothCharacterSumBound charError cChar) :
    SubexpLoss (paperEpsRat crtError charError) := by
  have hmin : 0 < min cCRT cChar := lt_min hcrt.1 hchar.1
  refine subexpLoss_of_eventually_le
    (paperEpsRat_le_two_exp_of_budgets hcrt hchar) ?_
  exact subexpLoss_two_mul (subexpLoss_exp_neg_paperD hmin)

/-- **The concrete `L20_2SubInputs` budget.**  The CRT side is the *proved*
truncated geometric tail (constant `2`), and the character side is the bundle's
`charError`; the combined rational error is eventually at most
`2 exp (-(min 2 cChar) · paperD n · scale n)`. -/
theorem paperEpsRat_subInputs_le_two_exp (S : L20_2SubInputs) :
    ∀ᶠ n : ℕ in atTop,
      paperEpsRat geometricCRTError S.charError n ≤
        2 * exp (-(min 2 S.cChar) * paperD n * scale n) :=
  paperEpsRat_le_two_exp_of_budgets truncatedGeometricCRTLaw S.char_sum

/-- **The concrete `L20_2CharInputs` budget.**  The character side is the actual
normalized smooth-character error `smoothCharacterError (S.charData n)`, and the
bound is obtained from the concrete sums with the explicit mass normalisation.
The exponent is exactly `min 2 S.cChar`. -/
theorem paperCharEpsRat_le_two_exp_of_char_sum (S : L20_2CharInputs) :
    ∀ᶠ n : ℕ in atTop,
      paperCharEpsRat S n ≤
        2 * exp (-(min 2 S.cChar) * paperD n * scale n) := by
  refine paperEpsRat_le_two_exp_of_budgets truncatedGeometricCRTLaw ?_
  exact smoothCharacterSumBound_of_concrete S.charData S.cChar_pos S.char_concrete

/-- The concrete character bundle's rational error is a `SubexpLoss`, with the
positivity of `min 2 cChar` supplied by `cChar_pos`. -/
theorem paperCharEpsRat_subexp_via_budget (S : L20_2CharInputs) :
    SubexpLoss (paperCharEpsRat S) :=
  paperEpsRat_subexp_of_budgets truncatedGeometricCRTLaw
    (smoothCharacterSumBound_of_concrete S.charData S.cChar_pos S.char_concrete)

/-- **The rational error is strictly positive.**  The truncated geometric CRT
defect is strictly positive, so `paperEpsRat` with that CRT budget is nonzero at
every ledger index whenever the character error is nonnegative.  This records
that the budget is a genuine sum of two errors, not a zero placeholder. -/
theorem paperEpsRat_geometricCRTError_pos (charError : ℕ → ℝ) (n : ℕ)
    (hchar : 0 ≤ charError n) :
    0 < paperEpsRat geometricCRTError charError n := by
  rw [paperEpsRat_apply]
  exact add_pos_of_pos_of_nonneg (geometricCRTError_pos n) hchar

/-! ## 3. The isolated GRH input and its Dirichlet reduction -/

/-- **The smallest explicit GRH input for the smooth-character budget.**  It is
exactly the existing `PrimeBinProductBound`: a uniform envelope for nonprincipal
character twists of prime-bin product sets.  This is the only Prop in this file
that mentions `L`-functions, and it is proved from `DirichletLZerosOnLine` by
`smoothCharacterGRHInput_of_criticalLine`. -/
def SmoothCharacterGRHInput : Prop := PrimeBinProductBound

/-- **The Dirichlet reduction of the isolated GRH input.**  This is the proven
reduction `DirichletLZerosOnLine → SmoothCharacterGRHInput`, obtained from the
existing critical-line prime-bin estimate. -/
theorem smoothCharacterGRHInput_of_criticalLine (line : DirichletLZerosOnLine) :
    SmoothCharacterGRHInput :=
  primeBin_product_from_critical_line line

/-- The explicit envelope decay for *every* ledger index.  This is the
arithmetic width/counting input; it does not mention `L`-functions. -/
def PrimeBinCharacterDecayAll (K c : ℝ) (q : ℕ) {ι : Type} [Fintype ι]
    [DecidableEq ι] (A B : ι → ℕ) : Prop :=
  ∀ n, PrimeBinCharacterDecay K c q A B n

/-- **The smooth-character sum budget from the isolated GRH input and the
explicit decay.**  The GRH input supplies the envelope constant `K`, and the
decay supplies the normalising factor; the conclusion is the concrete
`SmoothCharacterSumBound` consumed by `paperEpsRat`. -/
theorem smoothCharacterSumBound_of_GRHInput_and_decay
    (hgrh : SmoothCharacterGRHInput) {c : ℝ} (hc : 0 < c)
    {q : ℕ} [NeZero q] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ι → ℕ) (hA : ∀ i, 2 ≤ A i) (hAB : ∀ i, A i ≤ B i)
    (hdisj : Pairwise fun i j =>
      Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (hcard : 0 < (primeBinProducts A B).card)
    (hdecay : PrimeBinCharacterDecayAll (primeBinGRHConstant hgrh) c q A B) :
    SmoothCharacterSumBound
      (fun _ => smoothCharacterError (primeBinSmoothCharacterData q A B hcard)) c :=
  smoothCharacterSumBound_of_primeBinProductBound hgrh hc A B hA hAB hdisj hcard
    (fun n => hdecay n)

/-- The same budget with the GRH input discharged from `DirichletLZerosOnLine`. -/
theorem smoothCharacterSumBound_of_criticalLine_and_decay
    (line : DirichletLZerosOnLine) {c : ℝ} (hc : 0 < c)
    {q : ℕ} [NeZero q] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ι → ℕ) (hA : ∀ i, 2 ≤ A i) (hAB : ∀ i, A i ≤ B i)
    (hdisj : Pairwise fun i j =>
      Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j)))
    (hcard : 0 < (primeBinProducts A B).card)
    (hdecay : PrimeBinCharacterDecayAll
      (primeBinGRHConstant (smoothCharacterGRHInput_of_criticalLine line)) c q A B) :
    SmoothCharacterSumBound
      (fun _ => smoothCharacterError (primeBinSmoothCharacterData q A B hcard)) c :=
  smoothCharacterSumBound_of_GRHInput_and_decay
    (smoothCharacterGRHInput_of_criticalLine line) hc A B hA hAB hdisj hcard hdecay

/-- **The concrete smooth-character budget from GRH and the width condition.**
The constants `K` (GRH envelope) and `Ks` (prime-supply error) are extracted from
`DirichletLZerosOnLine`.  Beyond them, the only hypothesis is the explicit
arithmetic width condition `PrimeBinEnvelopeWidthCore` together with nonempty
bins; no further `L`-function input enters. -/
theorem smoothCharacterSumBound_of_criticalLine_width_nonempty
    (line : DirichletLZerosOnLine) :
    ∃ K Ks : ℝ, 0 ≤ K ∧ 0 ≤ Ks ∧
      ∀ (q : ℕ) [NeZero q] {c : ℝ} {ι : Type} [Fintype ι] [DecidableEq ι]
        (A B : ι → ℕ) (hcard : 0 < (primeBinProducts A B).card),
        (hdisj : Pairwise fun i j =>
          Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
        (hbin : 0 < Fintype.card ι) →
        (hA : ∀ i, 2 ≤ A i) →
        (hne : ∀ i, (primeBin (A i) (B i)).Nonempty) →
        (hc : 0 < c) →
        (∀ n, PrimeBinEnvelopeWidthCore K Ks c q A B n) →
        SmoothCharacterSumBound
          (fun _ => smoothCharacterError
            (primeBinSmoothCharacterData q A B hcard)) c := by
  obtain ⟨K, hK, hbound⟩ :=
    primeBinProducts_twist_le (primeBin_product_from_critical_line line)
  obtain ⟨Ks, hKs, hsupply⟩ :=
    primeBin_supply_nonempty_from_critical_line line
  refine ⟨K, Ks, hK, hKs, ?_⟩
  intro q _ c ι _ _ A B hcard hdisj hbin hA hne hc hwidth
  have hAB : ∀ i, A i ≤ B i :=
    fun i => le_of_lt (lt_of_primeBin_nonempty (hne i))
  refine smoothCharacterSumBound_of_primeBinReduction hc A B hcard
    ⟨hK, (fun χ hχ => hbound q χ hχ A B hA hAB hdisj),
      (fun n => primeBinCharacterDecay_of_width_nonempty
        hK hsupply hdisj hbin hne (hwidth n))⟩

/-- **The end-to-end `paperEpsRat` budget with GRH isolated.**  The CRT side is
again the proved geometric tail, while the character side is the concrete
prime-bin smooth-character error.  The GRH input has been discharged from
`DirichletLZerosOnLine`; the remaining hypothesis is exactly the explicit
arithmetic width condition plus nonempty bins.  The rate is
`min 2 c`. -/
theorem paperEpsRat_le_two_exp_of_criticalLine_width_nonempty
    (line : DirichletLZerosOnLine) :
    ∃ K Ks : ℝ, 0 ≤ K ∧ 0 ≤ Ks ∧
      ∀ (q : ℕ) [NeZero q] {c : ℝ} {ι : Type} [Fintype ι] [DecidableEq ι]
        (A B : ι → ℕ) (hcard : 0 < (primeBinProducts A B).card),
        (hdisj : Pairwise fun i j =>
          Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
        (hbin : 0 < Fintype.card ι) →
        (hA : ∀ i, 2 ≤ A i) →
        (hne : ∀ i, (primeBin (A i) (B i)).Nonempty) →
        (hc : 0 < c) →
        (∀ n, PrimeBinEnvelopeWidthCore K Ks c q A B n) →
        ∀ᶠ n : ℕ in atTop,
          paperEpsRat geometricCRTError
            (fun _ => smoothCharacterError
              (primeBinSmoothCharacterData q A B hcard)) n ≤
            2 * exp (-(min 2 c) * paperD n * scale n) := by
  obtain ⟨K, Ks, hK, hKs, hsum⟩ :=
    smoothCharacterSumBound_of_criticalLine_width_nonempty line
  refine ⟨K, Ks, hK, hKs, ?_⟩
  intro q _ c ι _ _ A B hcard hdisj hbin hA hne hc hwidth
  exact paperEpsRat_le_two_exp_of_budgets truncatedGeometricCRTLaw
    (hsum (q := q) (c := c) (A := A) (B := B)
      hcard hdisj hbin hA hne hc hwidth)

/-! ## 4. Axiom audit -/

#print axioms geometricCRTError_pos
#print axioms geometricCRTError_le_exp_paperScale
#print axioms geometricCRTError_le_exp_scale_of_nonneg
#print axioms geometricCRTError_le_exp_scale_eventually
#print axioms geometricCRTError_subexp
#print axioms paperEpsRat_le_two_exp_of_budgets
#print axioms paperEpsRat_subexp_of_budgets
#print axioms paperEpsRat_subInputs_le_two_exp
#print axioms paperCharEpsRat_le_two_exp_of_char_sum
#print axioms paperCharEpsRat_subexp_via_budget
#print axioms paperEpsRat_geometricCRTError_pos
#print axioms SmoothCharacterGRHInput
#print axioms smoothCharacterGRHInput_of_criticalLine
#print axioms PrimeBinCharacterDecayAll
#print axioms smoothCharacterSumBound_of_GRHInput_and_decay
#print axioms smoothCharacterSumBound_of_criticalLine_and_decay
#print axioms smoothCharacterSumBound_of_criticalLine_width_nonempty
#print axioms paperEpsRat_le_two_exp_of_criticalLine_width_nonempty

end

end Cogentic.RandomizedL20_2CRTBudget
