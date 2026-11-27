import Cogentic.RandomizedL21_2Perron

set_option linter.style.haveILetI false

/-!
# L21.2: the discrete smooth-count density normalization

`Cogentic.RandomizedL21_2Perron.L21_2PerronInputs` keeps the paper's local
smooth-count statement as an abstract field

```
densityNormalization :
  ∀ᶠ n, √(X n) * exp (-(R n)) ≤ smoothCount n
```

where `smoothCount` is an unspecified real sequence and

```
R = representationLog (kOf X c) (spacingOf X c) (bOf X c).
```

The present file makes the counting object explicit.  For a centre `p` and a
smoothness cutoff `y`, the paper's set is

```
{m : ℕ | |m - p| < √p and P⁺(m) ≤ y},
```

and `smoothCountNear p c X n` is its cardinality with `y = smoothCutoff c X n`.
The only remaining input is the *local count* `LocalSmoothCountLower p c X`,
i.e. the displayed lower bound for this explicit finite set.  This is the
smallest concrete counting statement: it is exactly the paper's "central
density" count at a good centre, with no abstract `smoothCount` left.

We prove:

1. the finite-set membership characterization `mem_sqrtSmoothNeighbours`;
2. nonnegativity of the explicit count, and monotonicity in the smoothness
   cutoff;
3. the bridge `centeredBinProducts_subset_sqrtSmoothNeighbours`: every product
   from the existing prime-bin strip construction whose multiplicative strip
   lies inside the `√p` neighbourhood is one of the counted smooth integers;
4. the reduction to the full L21.2 bundle:
   `L21_2DensityInputs.toPerronInputs : L21_2DensityInputs → L21_2PerronInputs`,
   together with the downstream `toReducedInputs`, `toInputs`, `toRatedLeaf`,
   `toSubexpLeaf`, the ledger slot, and the paper-assumption reassembly.

The existing `centeredBinProducts_density_*` bounds count *all* products in a
multiplicative strip of width `exp (k δ)`.  For the `√p`-neighbourhood one needs
`k δ ≲ p^{-1/2}`, so those global strip counts do not supply the sharp local
density `exp (-(1/(2c)) T_X)`; the paper's central-density/tent argument is
what supplies it.  The bridge in item 3 is the exact implication that *is*
available from the strip construction, and item 4 keeps the sharp local count
as the single explicit input.

No `sorry`, `admit`, `axiom` or `native_decide`; the count is a genuine
cardinality, never set to zero.
-/

noncomputable section

namespace Cogentic.RandomizedL21_2Density

open Filter Real
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Sub
open Cogentic.RandomizedL21_2Perron
open Cogentic.Randomized
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedOneThirdAsymptotic

/-! ## The explicit smooth neighbourhood -/

/-- `m` is `y`-smooth: every prime divisor of `m` is at most `y`.  This is the
same predicate as in `Cogentic.Randomized.centeredBinProducts_smooth`. -/
def SmoothUpTo (y : ℝ) (m : ℕ) : Prop :=
  ∀ q ∈ m.primeFactors, (q : ℝ) ≤ y

/-- The integers in the open `√p`-neighbourhood of `p` that are `y`-smooth.

The ambient `Finset.range (⌊p + √p⌋₊ + 1)` is large enough: any `m` with
`|m - p| < √p` satisfies `m < p + √p`, so the filter below is exactly the
paper's set of integers in the neighbourhood.  (The ambient value `0` is
harmless: `|0 - p| < √p` fails whenever `p > 1`, the paper's range.) -/
noncomputable def sqrtSmoothNeighbours (p y : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊p + Real.sqrt p⌋₊ + 1)).filter
    fun m : ℕ => |(m : ℝ) - p| < Real.sqrt p ∧ SmoothUpTo y m

/-- The paper's discrete smooth count
`#{m : |m - p| < √p, P⁺(m) ≤ exp (c T_X)}` at the centre `p`. -/
noncomputable def smoothCountNear (p : ℕ → ℝ) (c : ℝ) (X : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((sqrtSmoothNeighbours (p n) (smoothCutoff c X n)).card : ℝ)

/-- Membership in the explicit neighbourhood. -/
theorem mem_sqrtSmoothNeighbours {p y : ℝ} {m : ℕ} :
    m ∈ sqrtSmoothNeighbours p y ↔
      |(m : ℝ) - p| < Real.sqrt p ∧ SmoothUpTo y m := by
  classical
  unfold sqrtSmoothNeighbours
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, hneigh, hsmooth⟩
    exact ⟨hneigh, hsmooth⟩
  · rintro ⟨hneigh, hsmooth⟩
    refine ⟨?_, hneigh, hsmooth⟩
    have hp_nonneg : 0 ≤ p := by
      by_contra hp
      push Not at hp
      have hsqrt : Real.sqrt p = 0 := Real.sqrt_eq_zero_of_nonpos hp.le
      rw [hsqrt] at hneigh
      exact (not_lt_of_ge (abs_nonneg ((m : ℝ) - p))) hneigh
    have hlt : (m : ℝ) < p + Real.sqrt p := by
      have := (abs_lt.mp hneigh).2
      linarith
    have hnonneg : 0 ≤ p + Real.sqrt p :=
      add_nonneg hp_nonneg (Real.sqrt_nonneg p)
    have hmfloor : m ≤ ⌊p + Real.sqrt p⌋₊ :=
      (Nat.le_floor_iff hnonneg).mpr hlt.le
    exact Nat.lt_succ_of_le hmfloor

/-- The explicit count is the cardinality of the paper's `√p`-neighbourhood;
`mem_sqrtSmoothNeighbours` records the set-builder description. -/
theorem smoothCountNear_eq_card (p : ℕ → ℝ) (c : ℝ) (X : ℕ → ℝ) (n : ℕ) :
    smoothCountNear p c X n =
      ((sqrtSmoothNeighbours (p n) (smoothCutoff c X n)).card : ℝ) :=
  rfl

/-- The explicit smooth count is nonnegative. -/
theorem smoothCountNear_nonneg (p : ℕ → ℝ) (c : ℝ) (X : ℕ → ℝ) (n : ℕ) :
    0 ≤ smoothCountNear p c X n := by
  unfold smoothCountNear
  exact Nat.cast_nonneg _

/-- Increasing the smoothness cutoff can only add integers to the
neighbourhood. -/
theorem sqrtSmoothNeighbours_mono_cutoff {p y y' : ℝ} (hy : y ≤ y') :
    sqrtSmoothNeighbours p y ⊆ sqrtSmoothNeighbours p y' := by
  intro m hm
  rw [mem_sqrtSmoothNeighbours] at hm ⊢
  exact ⟨hm.1, fun q hq => (hm.2 q hq).trans hy⟩

/-- **General lower-bound principle.**  Any explicit finite set of smooth
integers in the `√p`-neighbourhood bounds the count from below.  This is the
form in which concrete smooth-number constructions are consumed. -/
theorem card_le_smoothCountNear_of_subset
    {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ} {n : ℕ} {S : Finset ℕ}
    (hsub : S ⊆ sqrtSmoothNeighbours (p n) (smoothCutoff c X n)) :
    (S.card : ℝ) ≤ smoothCountNear p c X n := by
  have hcard : (S.card : ℝ) ≤
      ((sqrtSmoothNeighbours (p n) (smoothCutoff c X n)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  simpa [smoothCountNear] using hcard

/-! ## The smallest explicit counting input -/

/-- **The local smooth-count lower bound.**  At the centre sequence `p`, the
`√p`-neighbourhood contains at least `√X exp (-R)` distinct `e^B`-smooth
integers, with exactly the manuscript's logarithmic loss `R`.

This is the smallest explicit form of the L21.2 `densityNormalization` field:
the counted object is a concrete `Finset`, and no abstract `smoothCount`
remains. -/
def LocalSmoothCountLower (p : ℕ → ℝ) (c : ℝ) (X : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    Real.sqrt (X n) *
        Real.exp (-(representationLog (kOf X c) (spacingOf X c) (bOf X c) n)) ≤
      smoothCountNear p c X n

/-- The explicit count obeys the manuscript's lower bound once the local count
is supplied. -/
theorem densityNormalization_of_localCount {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ}
    (h : LocalSmoothCountLower p c X) :
    ∀ᶠ n : ℕ in atTop,
      Real.sqrt (X n) *
          Real.exp (-(representationLog (kOf X c) (spacingOf X c) (bOf X c) n)) ≤
        smoothCountNear p c X n :=
  h

/-- The local count is strictly positive eventually, not a zero count: the
right-hand side `√X exp (-R)` is positive whenever `X > 0`. -/
theorem smoothCountNear_pos_of_localCount {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ}
    (hX : ∀ᶠ n : ℕ in atTop, 0 < X n)
    (h : LocalSmoothCountLower p c X) :
    ∀ᶠ n : ℕ in atTop, 0 < smoothCountNear p c X n := by
  filter_upwards [hX, h] with n hXn hn
  have hpos : 0 < Real.sqrt (X n) *
      Real.exp (-(representationLog (kOf X c) (spacingOf X c) (bOf X c) n)) :=
    mul_pos (Real.sqrt_pos.mpr hXn) (Real.exp_pos _)
  exact lt_of_lt_of_le hpos hn

/-! ## Compatibility with the existing prime-bin construction -/

/-- **Every integer in the prime-bin strip is a counted smooth integer** when
the whole multiplicative strip lies inside the `√p`-neighbourhood.  This is the
bridge between the explicit count and
`Cogentic.Randomized.centeredBinProducts`; the smoothness half is exactly
`Cogentic.Randomized.centeredBinProducts_smooth`. -/
theorem centeredBinProducts_subset_sqrtSmoothNeighbours
    {P δ : ℝ} {J K a : ℕ} {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ} {n : ℕ}
    (hP : 0 ≤ P) (hK : 0 < K)
    (hlo : p n - Real.sqrt (p n) < P ^ K)
    (hhi : P ^ K * Real.exp ((K : ℝ) * δ) < p n + Real.sqrt (p n))
    (hfloor : ∀ j < J, (centeredBinFloor P δ a K (j + 1) : ℝ) ≤
      smoothCutoff c X n) :
    centeredBinProducts P δ J K a ⊆
      sqrtSmoothNeighbours (p n) (smoothCutoff c X n) := by
  intro m hm
  rw [mem_sqrtSmoothNeighbours]
  refine ⟨?_, centeredBinProducts_smooth hfloor hm⟩
  have hstrip := centeredBinProducts_mem_strip hP hK hm
  rw [abs_lt]
  constructor
  · linarith
  · linarith

/-- The prime-bin strip supplies a lower bound for the explicit smooth count
whenever the strip is contained in the `√p`-neighbourhood. -/
theorem card_centeredBinProducts_le_smoothCountNear
    {P δ : ℝ} {J K a : ℕ} {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ} {n : ℕ}
    (hP : 0 ≤ P) (hK : 0 < K)
    (hlo : p n - Real.sqrt (p n) < P ^ K)
    (hhi : P ^ K * Real.exp ((K : ℝ) * δ) < p n + Real.sqrt (p n))
    (hfloor : ∀ j < J, (centeredBinFloor P δ a K (j + 1) : ℝ) ≤
      smoothCutoff c X n) :
    ((centeredBinProducts P δ J K a).card : ℝ) ≤ smoothCountNear p c X n := by
  have hsub := centeredBinProducts_subset_sqrtSmoothNeighbours
    (p := p) (c := c) (X := X) (n := n) hP hK hlo hhi hfloor
  have hcard : ((centeredBinProducts P δ J K a).card : ℝ) ≤
      ((sqrtSmoothNeighbours (p n) (smoothCutoff c X n)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  simpa [smoothCountNear] using hcard

/-! ## The bundle with the explicit count -/

/-- `L21_2PerronInputs` with the abstract count and its lower bound replaced by
the explicit `√p`-neighbourhood cardinality and the local count.  Every other
field is unchanged. -/
structure L21_2DensityInputs where
  /-- The dyadic centre bound `X`. -/
  X : ℕ → ℝ
  /-- The stage-one constant `c`. -/
  c : ℝ
  /-- Perron constant in the vertical error `O (v^{2/3} U^C)`. -/
  Kper : ℕ → ℝ
  /-- The absolute exponent `C` of the Perron/twisted-sum errors. -/
  Cper : ℝ
  /-- Exponent in `ε = e^{-a/3} U^{Ceps}`. -/
  Ceps : ℝ
  /-- The Fourier gap `μ̂ (t) - ν̂ (t)`. -/
  fourierGap : ℕ → ℝ → ℂ
  badCount : ℕ → ℝ
  lowTerm : ℕ → ℝ
  middleTerm : ℕ → ℝ
  tailTerm : ℕ → ℝ
  /-- Exponent of the explicit polynomial factor `(1 + U)^{polyExp}`. -/
  polyExp : ℝ
  /-- The centre sequence `p` at which the local count is asserted. -/
  p : ℕ → ℝ
  X_gt_one : ∀ n, 1 < X n
  c_pos : 0 < c
  c_le_one : c ≤ 1
  /-- `log X ≥ 3` for every band. -/
  U_ge_three : ∀ n, 3 ≤ bandLog X n
  Kper_nonneg : ∀ n, 0 ≤ Kper n
  Cper_ge_two : 2 ≤ Cper
  Ceps_nonneg : 0 ≤ Ceps
  polyExp_ge_three : 3 ≤ polyExp
  badCount_nonneg : ∀ n, 0 ≤ badCount n
  lowTerm_nonneg : ∀ n, 0 ≤ lowTerm n
  middleTerm_nonneg : ∀ n, 0 ≤ middleTerm n
  tailTerm_nonneg : ∀ n, 0 ≤ tailTerm n
  perronShift : ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v →
    v ≤ smoothCutoff c X n → |t| ≤ X n ^ 3 →
      ‖twistedPrimeSum v t - twistedMain v t‖ ≤
        Kper n * (v ^ (2 / 3 : ℝ) * (bandLog X n) ^ Cper
          + v * (bandLog X n) ^ Cper / X n ^ 3
          + Real.sqrt v * (Real.log (2 * v)) ^ 2)
  fourierSupBound : ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, |t| ≤ X n ^ 3 →
    ‖fourierGap n t‖ ≤ supEps X (aOf X c) Ceps n
  b_le_B : ∀ᶠ n : ℕ in atTop, bOf X c n ≤ logCutoff c X n
  tentChebyshev : ∀ᶠ n : ℕ in atTop,
    badCount n / (X n + 1) ≤
      4 * (kOf X c n * spacingOf X c n) ^ 2 *
        (lowTerm n + middleTerm n + tailTerm n)
  /-- **The local smooth-count input** for the explicit `√p`-neighbourhood. -/
  localCount : LocalSmoothCountLower p c X
  fourierLow : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    lowTerm n ≤ Real.exp (-(((2 * c) / 3) - δ) * paperRate X n)
  fourierMiddle : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    middleTerm n ≤ Real.exp (-((1 / c) - δ) * paperRate X n)
  fourierTail : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    tailTerm n ≤ Real.exp (-δ * paperRate X n)
  U_dominates : ∀ m : ℝ, 0 < m →
    ∀ᶠ n : ℕ in atTop, m * scale n ^ 2 ≤ bandLog X n
  U_le_exp : ∀ᶠ n : ℕ in atTop, bandLog X n ≤ Real.exp (scale n)

namespace L21_2DensityInputs

variable (D : L21_2DensityInputs)

/-- The explicit smooth count attached to the bundle. -/
abbrev smoothCount (n : ℕ) : ℝ := smoothCountNear D.p D.c D.X n

/-- **The density-normalization field** for the explicit count. -/
theorem densityNormalization :
    ∀ᶠ n : ℕ in atTop,
      Real.sqrt (D.X n) *
          Real.exp (-(representationLog (kOf D.X D.c) (spacingOf D.X D.c)
            (bOf D.X D.c) n)) ≤
        D.smoothCount n :=
  D.localCount

/-- **The explicit-count bundle builds `L21_2PerronInputs`.**  The only change
is that `smoothCount` is instantiated with the paper's `√p`-neighbourhood
cardinality and `densityNormalization` is supplied by `localCount`. -/
def toPerronInputs : L21_2PerronInputs where
  X := D.X
  c := D.c
  Kper := D.Kper
  Cper := D.Cper
  Ceps := D.Ceps
  fourierGap := D.fourierGap
  smoothCount := D.smoothCount
  badCount := D.badCount
  lowTerm := D.lowTerm
  middleTerm := D.middleTerm
  tailTerm := D.tailTerm
  polyExp := D.polyExp
  X_gt_one := D.X_gt_one
  c_pos := D.c_pos
  c_le_one := D.c_le_one
  U_ge_three := D.U_ge_three
  Kper_nonneg := D.Kper_nonneg
  Cper_ge_two := D.Cper_ge_two
  Ceps_nonneg := D.Ceps_nonneg
  polyExp_ge_three := D.polyExp_ge_three
  smoothCount_nonneg := fun n => smoothCountNear_nonneg D.p D.c D.X n
  badCount_nonneg := D.badCount_nonneg
  lowTerm_nonneg := D.lowTerm_nonneg
  middleTerm_nonneg := D.middleTerm_nonneg
  tailTerm_nonneg := D.tailTerm_nonneg
  perronShift := D.perronShift
  fourierSupBound := D.fourierSupBound
  b_le_B := D.b_le_B
  tentChebyshev := D.tentChebyshev
  densityNormalization := D.densityNormalization
  fourierLow := D.fourierLow
  fourierMiddle := D.fourierMiddle
  fourierTail := D.fourierTail
  U_dominates := D.U_dominates
  U_le_exp := D.U_le_exp

/-- The reduced `L21_2Sub` bundle. -/
def toReducedInputs : L21_2ReducedInputs :=
  L21_2PerronInputs.toReducedInputs D.toPerronInputs

/-- The parent `L21_2Inputs`. -/
def toInputs : L21_2Inputs :=
  L21_2PerronInputs.toInputs D.toPerronInputs

/-- The L21.2 `RatedLeaf`. -/
def toRatedLeaf : RatedLeaf :=
  L21_2PerronInputs.toRatedLeaf D.toPerronInputs

/-- The `D^{-B}` form as a `SubexpLeaf`. -/
def toSubexpLeaf : SubexpLeaf :=
  L21_2PerronInputs.toSubexpLeaf D.toPerronInputs

theorem loss_nonneg (n : ℕ) : 0 ≤ D.toReducedInputs.loss n :=
  D.toReducedInputs.loss_nonneg n

theorem loss_le_paper :
    ∀ᶠ n : ℕ in atTop,
      D.toReducedInputs.loss n ≤ Real.exp (-(((D.c) / 64) * paperRate D.X n)) :=
  D.toReducedInputs.loss_le_paper

theorem loss_le_ledger :
    ∀ᶠ n : ℕ in atTop,
      D.toReducedInputs.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  D.toReducedInputs.loss_le_ledger

/-- The `C5Leaf.ellipticExceptional` slot, when identified with this loss, is
eventually at most `exp (-2 * scale n)`. -/
theorem slot_le {slots : C5LossSlots}
    (h : slots .ellipticExceptional = D.toReducedInputs.loss) :
    ∀ᶠ n : ℕ in atTop,
      slots .ellipticExceptional n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  L21_2ReducedInputs.slot_le D.toReducedInputs h

/-- The eleven remaining leaves plus the explicit L21.2 density inputs give the
full paper assumptions. -/
def paperAssumptions_of_density
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (A : PaperAnalyticAssumptionsWithoutL21_2 E C) :
    PaperAnalyticAssumptions E C :=
  L21_2PerronInputs.paperAssumptions_of_perron D.toPerronInputs A

end L21_2DensityInputs

/-! ## Axiom audit -/

#print axioms Cogentic.RandomizedL21_2Density.mem_sqrtSmoothNeighbours
#print axioms Cogentic.RandomizedL21_2Density.smoothCountNear_eq_card
#print axioms Cogentic.RandomizedL21_2Density.smoothCountNear_nonneg
#print axioms Cogentic.RandomizedL21_2Density.sqrtSmoothNeighbours_mono_cutoff
#print axioms Cogentic.RandomizedL21_2Density.card_le_smoothCountNear_of_subset
#print axioms Cogentic.RandomizedL21_2Density.densityNormalization_of_localCount
#print axioms Cogentic.RandomizedL21_2Density.smoothCountNear_pos_of_localCount
#print axioms Cogentic.RandomizedL21_2Density.centeredBinProducts_subset_sqrtSmoothNeighbours
#print axioms Cogentic.RandomizedL21_2Density.card_centeredBinProducts_le_smoothCountNear
#print axioms Cogentic.RandomizedL21_2Density.L21_2DensityInputs.densityNormalization
#print axioms Cogentic.RandomizedL21_2Density.L21_2DensityInputs.toPerronInputs
#print axioms Cogentic.RandomizedL21_2Density.L21_2DensityInputs.toReducedInputs
#print axioms Cogentic.RandomizedL21_2Density.L21_2DensityInputs.toInputs
#print axioms Cogentic.RandomizedL21_2Density.L21_2DensityInputs.toRatedLeaf
#print axioms Cogentic.RandomizedL21_2Density.L21_2DensityInputs.toSubexpLeaf
#print axioms Cogentic.RandomizedL21_2Density.L21_2DensityInputs.slot_le
#print axioms Cogentic.RandomizedL21_2Density.L21_2DensityInputs.paperAssumptions_of_density

end Cogentic.RandomizedL21_2Density
