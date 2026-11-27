import Cogentic.RandomizedL19EnergyMass

/-!
# L19.4: removing the finite initial-segment checks from the envelope growth

`Cogentic.RandomizedL19EnergyMass` reduces the two analytic inputs of the
marginal-energy certificate to raw parameter growth of the explicit envelopes
`mellinEnvelope` and `gridPrefixEnvelope`.  The resulting structures
`MellinEnvelopeGrowth` and `GridPrefixEnvelopeGrowth` still carry an unbounded
initial-segment field

`initial : ∀ n, scale n ≤ S → envelope n ≤ exp (c · scale n)`

for the finitely many indices below the threshold `S`, because `scale` grows.

This file removes those unbounded fields in two complementary ways.

## 1. Literal finite check

`initialFinset S N = {n < N | scale n ≤ S}` is the explicit finite set of
indices in the initial segment, and `CoversInitialSegment S N` says that the
sample bound `N` covers every such index.  `exists_initialBound` produces `N`
from `scale_grows`.

For an arbitrary envelope `env` and exponent `base`, the predicate
`InitialSegmentCheck env base S` is the old unbounded field and
`FiniteInitialSegmentCheck env base S N` is its bounded version.
`initialSegmentCheck_iff_finite` proves the two are equivalent once `N` covers
the segment, and `finiteInitialSegmentCheck_iff_finset` rewrites the bounded
version as a check over the literal `Finset` `initialFinset S N`.

The structures `MellinEnvelopeGrowthFinite` and
`GridPrefixEnvelopeGrowthFinite` are the original growth structures with
`initial` replaced by this finite check; `toGrowth` forgets the sample bound and
recovers the original structures, while `ofGrowth` chooses the bound from
`exists_initialBound` and turns any original certificate into the finite one.
Thus the finite structures are equivalent to the original ones and every
downstream certificate is unchanged.

## 2. The actual envelopes: a three-point check with an adjusted exponent

The finite check can be made much smaller for the actual envelopes.  On the
ledger scale

* `scale 0 = 0` and `scale 1 = 0`;
* `scale 2 < 0` (the real-power convention contributes `cos (2π/3) = -1/2`);
* `scale n > 0` for every `n ≥ 3`.

Hence for `n ≥ 3` increasing the polynomial exponent always helps, and the
finitely many indices `3 ≤ n < N` with `scale n ≤ S` can be absorbed into a
single adjusted exponent.  The value used here is

`adjustedExponent env base S N =
   max base (max_{3 ≤ n < N, scale n ≤ S} log (max (env n) 1) / scale n)`,

a finite supremum.  The `max (env n) 1` makes the logarithm nonnegative and
avoids any positivity side condition on the envelope.

Consequently only the three indices `n = 0, 1, 2` have to be checked
explicitly.  At `n = 0, 1` the right-hand side is `exp (c · 0) = 1` for every
exponent `c`, and at `n = 2` the right-hand side *decreases* as `c` increases
(`exp_mul_scale_two_anti`).  Thus no choice of the polynomial constant can
absorb these points, and the exact finite check is data-dependent rather than a
consequence of the growth estimates.  It is recorded as

`small : ∀ n ∈ Finset.range 3, envelope n ≤ exp (cM · scale n)`.

The structures `MellinEnvelopeGrowthSmallCheck` and
`GridPrefixEnvelopeGrowthSmallCheck` carry this three-point check and a constant
`cM` at least the adjusted exponent.  Their `envelope_poly` theorem proves the
pointwise bound for every `n`; the section-`3` absorption covers `n ≥ 3` and
`small` covers `n < 3`.

## 3. Consequences

`mellinEnergyScaleOfSmallCheck`, `gridPrefixEnergyScaleOfSmallCheck` and their
`...OfTotientCountSmallCheck` variants build the concrete `EnergyScaleInputs`
directly from the three-point structures, using the existing reduction
`mellinEnergyScale` / `gridPrefixEnergyScale`.  The `mellinEnergyScaleOfFinite`
and `gridPrefixEnergyScaleOfFinite` constructors do the same from the literal
finite-`Finset` structures through `toGrowth`.  No envelope, mass or error is set
to zero, and the finite checks
are genuine hypotheses because the envelope constants at the first three
indices are arbitrary.

Nothing here is a `sorry`, an `admit`, an `axiom`, or a `native_decide`.
-/

namespace Cogentic.RandomizedL19EnergyMassFinite

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Filter Real
open scoped BigOperators Classical
open Cogentic.Randomized
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedL19Energy
open Cogentic.RandomizedL19EnergyMass

/-! ## 1. The finite initial segment -/

/-- The finite initial segment `{n < N | scale n ≤ S}`. -/
noncomputable def initialFinset (S : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n => scale n ≤ S)

theorem mem_initialFinset {S : ℝ} {N n : ℕ} :
    n ∈ initialFinset S N ↔ n < N ∧ scale n ≤ S := by
  simp [initialFinset]

/-- An explicit covering of the initial segment: every `n` with
`scale n ≤ S` is strictly below `N`. -/
def CoversInitialSegment (S : ℝ) (N : ℕ) : Prop :=
  ∀ n : ℕ, scale n ≤ S → n < N

/-- The initial segment is finite because `scale` tends to infinity. -/
theorem exists_initialBound (S : ℝ) : ∃ N : ℕ, CoversInitialSegment S N := by
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp (scale_grows.eventually_gt_atTop S)
  refine ⟨N, fun n hn => ?_⟩
  by_contra h
  exact absurd hn (not_le.mpr (hN n (le_of_not_gt h)))

theorem zero_mem_initialFinset {S : ℝ} {N : ℕ} (hS : 0 ≤ S) (hN : 0 < N) :
    0 ∈ initialFinset S N := by
  rw [mem_initialFinset]
  exact ⟨hN, by simpa [scale] using hS⟩

theorem initialFinset_nonempty {S : ℝ} {N : ℕ} (hS : 0 ≤ S) (hN : 0 < N) :
    (initialFinset S N).Nonempty :=
  ⟨0, zero_mem_initialFinset hS hN⟩

/-- The old unbounded initial-segment check of an envelope with exponent
`base`. -/
def InitialSegmentCheck (env : ℕ → ℝ) (base S : ℝ) : Prop :=
  ∀ n : ℕ, scale n ≤ S → env n ≤ exp (base * scale n)

/-- The same check restricted to an explicit finite sample bound `N`. -/
def FiniteInitialSegmentCheck (env : ℕ → ℝ) (base S : ℝ) (N : ℕ) : Prop :=
  ∀ n : ℕ, n < N → scale n ≤ S → env n ≤ exp (base * scale n)

theorem initialSegmentCheck_iff_finite {env : ℕ → ℝ} {base S : ℝ} {N : ℕ}
    (hN : CoversInitialSegment S N) :
    InitialSegmentCheck env base S ↔ FiniteInitialSegmentCheck env base S N := by
  constructor
  · intro h n _ hnS
    exact h n hnS
  · intro h n hnS
    exact h n (hN n hnS) hnS

/-- The bounded check written on the literal finite set `initialFinset S N`. -/
theorem finiteInitialSegmentCheck_iff_finset {env : ℕ → ℝ} {base S : ℝ} {N : ℕ} :
    FiniteInitialSegmentCheck env base S N ↔
      ∀ n ∈ initialFinset S N, env n ≤ exp (base * scale n) := by
  constructor
  · intro h n hn
    obtain ⟨hnN, hnS⟩ := mem_initialFinset.mp hn
    exact h n hnN hnS
  · intro h n hnN hnS
    exact h n (mem_initialFinset.mpr ⟨hnN, hnS⟩)

/-! ## 2. The ledger scale at the small indices -/

/-- `scale n` is positive for `n ≥ 3`. -/
theorem scale_pos_of_three_le {n : ℕ} (hn : 3 ≤ n) : 0 < scale n := by
  have h3log : (1 : ℝ) < Real.log 3 := by
    have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    simpa using h
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog_gt_one : (1 : ℝ) < Real.log (n : ℝ) :=
    lt_of_lt_of_le h3log (Real.log_le_log (by norm_num) hnR)
  have hlog_pos : 0 < Real.log (n : ℝ) := lt_trans zero_lt_one hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (n : ℝ)) := Real.log_pos hlog_gt_one
  unfold scale
  exact mul_pos (Real.rpow_pos_of_pos hlog_pos _)
    (Real.rpow_pos_of_pos hloglog_pos _)

theorem scale_zero : scale 0 = 0 := by simp [scale]

theorem scale_one : scale 1 = 0 := by simp [scale]

/-- The real-power convention makes `scale 2` negative, since
`cos (2π/3) = -1/2`.  This is why increasing the polynomial exponent cannot
absorb the index `n = 2`. -/
theorem scale_two_neg : scale 2 < 0 := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt1 : Real.log 2 < 1 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)]
    simpa using Real.exp_one_gt_two
  have h1pos : 0 < (Real.log 2) ^ (1 / 3 : ℝ) :=
    Real.rpow_pos_of_pos hlog2pos _
  have hloglog_neg : Real.log (Real.log 2) < 0 :=
    Real.log_neg hlog2pos hlog2lt1
  have h2neg : (Real.log (Real.log 2)) ^ (2 / 3 : ℝ) < 0 := by
    rw [Real.rpow_def_of_neg hloglog_neg]
    have hcos : Real.cos ((2 / 3 : ℝ) * π) = -(1 / 2) := by
      have harg : (2 / 3 : ℝ) * π = π - π / 3 := by ring
      rw [harg, Real.cos_pi_sub, Real.cos_pi_div_three]
    rw [hcos]
    have hexp : 0 < Real.exp (Real.log (Real.log (Real.log 2)) * (2 / 3 : ℝ)) :=
      Real.exp_pos _
    nlinarith
  unfold scale
  exact mul_neg_of_pos_of_neg h1pos h2neg

/-- At `n = 2`, enlarging the polynomial exponent makes the right-hand side
smaller.  Hence the literal bound at `n = 2` cannot be obtained by adjusting
the constant. -/
theorem exp_mul_scale_two_anti {c c' : ℝ} (hcc' : c ≤ c') :
    exp (c' * scale 2) ≤ exp (c * scale 2) := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_right hcc' scale_two_neg.le

/-! ## 3. The finite-slope exponent -/

/-- The finite supremum used to absorb the initial segment.  The `max` with `1`
keeps the logarithm nonnegative. -/
noncomputable def adjustedExponent (env : ℕ → ℝ) (base S : ℝ) (N : ℕ) : ℝ :=
  max base ((Finset.range (N + 1)).sup' ⟨0, by simp⟩
    (fun n => if 3 ≤ n ∧ scale n ≤ S
      then Real.log (max (env n) 1) / scale n else 0))

theorem adjustedExponent_ge_base (env : ℕ → ℝ) (base S : ℝ) (N : ℕ) :
    base ≤ adjustedExponent env base S N := le_max_left _ _

theorem adjustedExponent_nonneg {env : ℕ → ℝ} {base S : ℝ} {N : ℕ}
    (hbase : 0 ≤ base) : 0 ≤ adjustedExponent env base S N :=
  hbase.trans (adjustedExponent_ge_base env base S N)

/-- **The initial segment above `3` is absorbed by the adjusted exponent.** -/
theorem le_exp_adjustedExponent_of_three_le {env : ℕ → ℝ} {base S : ℝ} {N : ℕ}
    (hcovers : CoversInitialSegment S N)
    (hgrowth : ∀ n, S ≤ scale n → env n ≤ exp (base * scale n))
    {n : ℕ} (hn3 : 3 ≤ n) :
    env n ≤ exp (adjustedExponent env base S N * scale n) := by
  have hs : 0 < scale n := scale_pos_of_three_le hn3
  by_cases hnS : scale n ≤ S
  · have hnN : n < N := hcovers n hnS
    have hmem : n ∈ Finset.range (N + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_lt hnN)
    have hsup : (if 3 ≤ n ∧ scale n ≤ S
        then Real.log (max (env n) 1) / scale n else 0) ≤
        adjustedExponent env base S N := by
      have := Finset.le_sup'
        (fun m => if 3 ≤ m ∧ scale m ≤ S
          then Real.log (max (env m) 1) / scale m else 0) hmem
      exact this.trans (le_max_right _ _)
    rw [if_pos ⟨hn3, hnS⟩] at hsup
    have hstep : max (env n) 1 =
        exp (Real.log (max (env n) 1) / scale n * scale n) := by
      rw [div_mul_cancel₀ _ hs.ne']
      exact (Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_right _ _))).symm
    calc
      env n ≤ max (env n) 1 := le_max_left _ _
      _ = exp (Real.log (max (env n) 1) / scale n * scale n) := hstep
      _ ≤ exp (adjustedExponent env base S N * scale n) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right hsup hs.le
  · have hsS : S ≤ scale n := le_of_lt (lt_of_not_ge hnS)
    calc
      env n ≤ exp (base * scale n) := hgrowth n hsS
      _ ≤ exp (adjustedExponent env base S N * scale n) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right
          (adjustedExponent_ge_base env base S N) hs.le

/-- The same absorption for any exponent at least the adjusted one. -/
theorem le_exp_of_le_adjustedExponent {env : ℕ → ℝ} {base S : ℝ} {N : ℕ}
    {cM : ℝ} (hcovers : CoversInitialSegment S N)
    (hgrowth : ∀ n, S ≤ scale n → env n ≤ exp (base * scale n))
    (hle : adjustedExponent env base S N ≤ cM)
    {n : ℕ} (hn3 : 3 ≤ n) :
    env n ≤ exp (cM * scale n) := by
  have hs : 0 < scale n := scale_pos_of_three_le hn3
  calc
    env n ≤ exp (adjustedExponent env base S N * scale n) :=
      le_exp_adjustedExponent_of_three_le hcovers hgrowth hn3
    _ ≤ exp (cM * scale n) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right hle hs.le

/-! ## 4. The Mellin envelope -/

theorem mellinEnvelopeExponent_nonneg {ι : Type} [Fintype ι]
    (line : DirichletLZerosOnLine) {cB cQ cT : ℝ}
    (hcB : 0 ≤ cB) (hcQ : 0 ≤ cQ) (_hcT : 0 ≤ cT) :
    0 ≤ mellinEnvelopeExponent (ι := ι) line cB cQ cT := by
  unfold mellinEnvelopeExponent
  have hcard : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hmax : 0 ≤ max cB cT := hcB.trans (le_max_left _ _)
  have hK : 0 ≤ mellinKExponent line := mellinKExponent_nonneg line
  have hterm : 0 ≤ mellinKExponent line + cB / 2 +
      3 * (cQ + max cB cT + 2) := by
    have h1 : 0 ≤ cB / 2 := by linarith
    have h2 : 0 ≤ 3 * (cQ + max cB cT + 2) := by nlinarith
    linarith
  exact mul_nonneg hcard hterm

/-- Raw Mellin growth data, with the finite initial segment recorded by an
explicit sample bound. -/
structure MellinEnvelopeGrowthData (line : DirichletLZerosOnLine) (q : ℕ → ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (B : ℕ → ι → ℕ) (t : ℕ → ℝ) where
  cB : ℝ
  cQ : ℝ
  cT : ℝ
  S : ℝ
  hcB : 0 ≤ cB
  hcQ : 0 ≤ cQ
  hcT : 0 ≤ cT
  hS : 2 ≤ S
  hq : ∀ n, q n ≠ 0
  hB : ∀ n i, 2 ≤ B n i
  hBle : ∀ n, S ≤ scale n → ∀ i, (B n i : ℝ) ≤ exp (cB * scale n)
  hQle : ∀ n, S ≤ scale n → (q n : ℝ) ≤ exp (cQ * scale n)
  hTle : ∀ n, S ≤ scale n → |t n| ≤ exp (cT * scale n)
  N : ℕ
  covers : CoversInitialSegment S N

namespace MellinEnvelopeGrowthData

variable {line : DirichletLZerosOnLine} {q : ℕ → ℕ}
  {ι : Type} [Fintype ι] [DecidableEq ι] {B : ℕ → ι → ℕ} {t : ℕ → ℝ}

noncomputable def env (_D : MellinEnvelopeGrowthData line q B t) (n : ℕ) : ℝ :=
  mellinEnvelope (q n) (mellinK line) (B n) (t n)

noncomputable def baseExponent (D : MellinEnvelopeGrowthData line q B t) : ℝ :=
  mellinEnvelopeExponent (ι := ι) line D.cB D.cQ D.cT

theorem baseExponent_nonneg (D : MellinEnvelopeGrowthData line q B t) :
    0 ≤ D.baseExponent :=
  mellinEnvelopeExponent_nonneg line D.hcB D.hcQ D.hcT

theorem growth (D : MellinEnvelopeGrowthData line q B t) (n : ℕ)
    (hn : D.S ≤ scale n) :
    D.env n ≤ exp (D.baseExponent * scale n) :=
  mellinEnvelope_le_exp_of_growth line q B t D.hcB D.hcQ D.hcT D.hS
    D.hq D.hB D.hBle D.hQle D.hTle hn

noncomputable def adjExponent (D : MellinEnvelopeGrowthData line q B t) : ℝ :=
  adjustedExponent D.env D.baseExponent D.S D.N

theorem baseExponent_le_adjExponent (D : MellinEnvelopeGrowthData line q B t) :
    D.baseExponent ≤ D.adjExponent :=
  adjustedExponent_ge_base D.env D.baseExponent D.S D.N

theorem adjExponent_nonneg (D : MellinEnvelopeGrowthData line q B t) :
    0 ≤ D.adjExponent :=
  D.baseExponent_nonneg.trans D.baseExponent_le_adjExponent

theorem env_le_adjExponent_of_three_le (D : MellinEnvelopeGrowthData line q B t)
    {n : ℕ} (hn3 : 3 ≤ n) :
    D.env n ≤ exp (D.adjExponent * scale n) :=
  le_exp_adjustedExponent_of_three_le D.covers D.growth hn3

theorem env_le_of_adjExponent_le (D : MellinEnvelopeGrowthData line q B t)
    {cM : ℝ} (hle : D.adjExponent ≤ cM) {n : ℕ} (hn3 : 3 ≤ n) :
    D.env n ≤ exp (cM * scale n) :=
  le_exp_of_le_adjustedExponent D.covers D.growth hle hn3

end MellinEnvelopeGrowthData

/-- Mellin growth data with the unbounded initial field replaced by a
three-point finite check and a possibly enlarged polynomial exponent. -/
structure MellinEnvelopeGrowthSmallCheck (line : DirichletLZerosOnLine) (q : ℕ → ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (B : ℕ → ι → ℕ) (t : ℕ → ℝ) where
  data : MellinEnvelopeGrowthData line q B t
  cM : ℝ
  hadjusted : data.adjExponent ≤ cM
  small : ∀ n ∈ Finset.range 3, data.env n ≤ exp (cM * scale n)

namespace MellinEnvelopeGrowthSmallCheck

variable {line : DirichletLZerosOnLine} {q : ℕ → ℕ}
  {ι : Type} [Fintype ι] [DecidableEq ι] {B : ℕ → ι → ℕ} {t : ℕ → ℝ}

theorem envelope_poly (F : MellinEnvelopeGrowthSmallCheck line q B t) (n : ℕ) :
    F.data.env n ≤ exp (F.cM * scale n) := by
  by_cases hn3 : 3 ≤ n
  · exact F.data.env_le_of_adjExponent_le F.hadjusted hn3
  · exact F.small n (Finset.mem_range.mpr (not_le.mp hn3))

theorem cM_nonneg (F : MellinEnvelopeGrowthSmallCheck line q B t) : 0 ≤ F.cM :=
  F.data.adjExponent_nonneg.trans F.hadjusted

end MellinEnvelopeGrowthSmallCheck

/-- The literal finite version of `MellinEnvelopeGrowth`: the same exponent and
data, but the unbounded `initial` field is replaced by a finite check on
`initialFinset S N`. -/
structure MellinEnvelopeGrowthFinite (line : DirichletLZerosOnLine) (q : ℕ → ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (B : ℕ → ι → ℕ) (t : ℕ → ℝ) where
  cB : ℝ
  cQ : ℝ
  cT : ℝ
  S : ℝ
  hcB : 0 ≤ cB
  hcQ : 0 ≤ cQ
  hcT : 0 ≤ cT
  hS : 2 ≤ S
  hq : ∀ n, q n ≠ 0
  hB : ∀ n i, 2 ≤ B n i
  hBle : ∀ n, S ≤ scale n → ∀ i, (B n i : ℝ) ≤ exp (cB * scale n)
  hQle : ∀ n, S ≤ scale n → (q n : ℝ) ≤ exp (cQ * scale n)
  hTle : ∀ n, S ≤ scale n → |t n| ≤ exp (cT * scale n)
  N : ℕ
  covers : CoversInitialSegment S N
  initial_finite : FiniteInitialSegmentCheck
    (fun n => mellinEnvelope (q n) (mellinK line) (B n) (t n))
    (mellinEnvelopeExponent (ι := ι) line cB cQ cT) S N

namespace MellinEnvelopeGrowthFinite

variable {line : DirichletLZerosOnLine} {q : ℕ → ℕ}
  {ι : Type} [Fintype ι] [DecidableEq ι] {B : ℕ → ι → ℕ} {t : ℕ → ℝ}

/-- Forget the finite sample bound, recovering the unbounded growth structure. -/
noncomputable def toGrowth (F : MellinEnvelopeGrowthFinite line q B t) :
    MellinEnvelopeGrowth line q B t where
  cB := F.cB
  cQ := F.cQ
  cT := F.cT
  S := F.S
  hcB := F.hcB
  hcQ := F.hcQ
  hcT := F.hcT
  hS := F.hS
  hq := F.hq
  hB := F.hB
  hBle := F.hBle
  hQle := F.hQle
  hTle := F.hTle
  initial := fun n hn =>
    (initialSegmentCheck_iff_finite F.covers).mpr F.initial_finite n hn

theorem envelope_poly (F : MellinEnvelopeGrowthFinite line q B t) (n : ℕ) :
    mellinEnvelope (q n) (mellinK line) (B n) (t n) ≤
      exp (mellinEnvelopeExponent (ι := ι) line F.cB F.cQ F.cT * scale n) :=
  F.toGrowth.envelope_poly n

/-- Every unbounded growth certificate yields its finite-check version, by
choosing the explicit sample bound from `exists_initialBound`. -/
noncomputable def ofGrowth (G : MellinEnvelopeGrowth line q B t) :
    MellinEnvelopeGrowthFinite line q B t :=
  let N := Classical.choose (exists_initialBound G.S)
  let hN : CoversInitialSegment G.S N :=
    Classical.choose_spec (exists_initialBound G.S)
  { cB := G.cB
    cQ := G.cQ
    cT := G.cT
    S := G.S
    hcB := G.hcB
    hcQ := G.hcQ
    hcT := G.hcT
    hS := G.hS
    hq := G.hq
    hB := G.hB
    hBle := G.hBle
    hQle := G.hQle
    hTle := G.hTle
    N := N
    covers := hN
    initial_finite := (initialSegmentCheck_iff_finite hN).mp G.initial }

end MellinEnvelopeGrowthFinite

/-! ## 5. The sharp-prefix envelope -/

theorem gridPrefixEnvelopeExponent_nonneg {ι : Type} [Fintype ι]
    {cC cU cMB cX cK cN : ℝ}
    (hcC : 0 ≤ cC) (hcU : 0 ≤ cU) (hcMB : 0 ≤ cMB) (_hcX : 0 ≤ cX)
    (hcK : 0 ≤ cK) (hcN : 0 ≤ cN) :
    0 ≤ gridPrefixEnvelopeExponent (ι := ι) cC cU cMB cX cK cN := by
  unfold gridPrefixEnvelopeExponent
  have hcard : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hmax : 0 ≤ max cU (3 * cX) := hcU.trans (le_max_left _ _)
  have hcoef : 0 ≤ gridCoefficientExponent := gridCoefficientExponent_nonneg
  have hfirst : 0 ≤ cMB / 2 + (Fintype.card ι : ℝ) *
      (cC + cU / 2 + 3 * (cMB + max cU (3 * cX) + 2)) + cX +
      gridCoefficientExponent := by
    have h1 : 0 ≤ cMB / 2 := by linarith
    have h2 : 0 ≤ cC + cU / 2 + 3 * (cMB + max cU (3 * cX) + 2) := by
      have h3 : 0 ≤ cU / 2 := by linarith
      have h4 : 0 ≤ 3 * (cMB + max cU (3 * cX) + 2) := by nlinarith
      linarith
    have h5 : 0 ≤ (Fintype.card ι : ℝ) *
        (cC + cU / 2 + 3 * (cMB + max cU (3 * cX) + 2)) :=
      mul_nonneg hcard h2
    linarith
  have hsecond : 0 ≤ cMB / 2 + cK + cN + 2 := by
    have h : 0 ≤ cMB / 2 := by linarith
    linarith
  have hmax0 : 0 ≤ max
      (cMB / 2 + (Fintype.card ι : ℝ) *
        (cC + cU / 2 + 3 * (cMB + max cU (3 * cX) + 2)) + cX +
        gridCoefficientExponent)
      (cMB / 2 + cK + cN + 2) := le_max_of_le_left hfirst
  linarith

/-- Raw sharp-prefix growth data, with the finite initial segment recorded by an
explicit sample bound. -/
structure GridPrefixEnvelopeGrowthData (line : DirichletLZerosOnLine)
    (m B : ℕ → ℕ) (X : ℕ → ℝ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ℕ → ι → ℕ) where
  cC : ℝ
  cU : ℝ
  cMB : ℝ
  cX : ℝ
  cK : ℝ
  cN : ℝ
  S : ℝ
  hcC : 0 ≤ cC
  hcU : 0 ≤ cU
  hcMB : 0 ≤ cMB
  hcX : 0 ≤ cX
  hcK : 0 ≤ cK
  hcN : 0 ≤ cN
  hS : 2 ≤ S
  hm : ∀ n, m n ≠ 0
  hB : ∀ n, B n ≠ 0
  hU : ∀ n i, 2 ≤ U n i
  hX : ∀ n, S ≤ scale n → 2 ≤ X n
  hCle : ∀ n, S ≤ scale n →
    prefixC (m n) (B n) (hm n) (hB n) line ≤ exp (cC * scale n)
  hKle : ∀ n, S ≤ scale n →
    prefixK (m n) (B n) (hm n) (hB n) line ≤ exp (cK * scale n)
  hMBle : ∀ n, S ≤ scale n →
    ((m n * B n : ℕ) : ℝ) ≤ exp (cMB * scale n)
  hUle : ∀ n, S ≤ scale n → ∀ i, (U n i : ℝ) ≤ exp (cU * scale n)
  hXle : ∀ n, S ≤ scale n → X n ≤ exp (cX * scale n)
  hNle : ∀ n, S ≤ scale n →
    ((primeBinProducts (A n) (U n)).card : ℝ) ≤ exp (cN * scale n)
  N : ℕ
  covers : CoversInitialSegment S N

namespace GridPrefixEnvelopeGrowthData

variable {line : DirichletLZerosOnLine} {m B : ℕ → ℕ} {X : ℕ → ℝ}
  {ι : Type} [Fintype ι] [DecidableEq ι] {A U : ℕ → ι → ℕ}

noncomputable def env (D : GridPrefixEnvelopeGrowthData line m B X A U) (n : ℕ) : ℝ :=
  gridPrefixEnvelope (m n) (B n)
    (prefixC (m n) (B n) (D.hm n) (D.hB n) line)
    (prefixK (m n) (B n) (D.hm n) (D.hB n) line) (X n) (A n) (U n)

noncomputable def baseExponent (D : GridPrefixEnvelopeGrowthData line m B X A U) : ℝ :=
  gridPrefixEnvelopeExponent (ι := ι) D.cC D.cU D.cMB D.cX D.cK D.cN

theorem baseExponent_nonneg (D : GridPrefixEnvelopeGrowthData line m B X A U) :
    0 ≤ D.baseExponent :=
  gridPrefixEnvelopeExponent_nonneg D.hcC D.hcU D.hcMB D.hcX D.hcK D.hcN

theorem growth (D : GridPrefixEnvelopeGrowthData line m B X A U) (n : ℕ)
    (hn : D.S ≤ scale n) :
    D.env n ≤ exp (D.baseExponent * scale n) :=
  gridPrefixEnvelope_le_exp_of_growth line m B D.hm D.hB X A U
    D.hcC D.hcU D.hcMB D.hcX D.hcK D.hcN D.hS D.hU D.hX D.hCle D.hKle
    D.hMBle D.hUle D.hXle D.hNle hn

noncomputable def adjExponent (D : GridPrefixEnvelopeGrowthData line m B X A U) : ℝ :=
  adjustedExponent D.env D.baseExponent D.S D.N

theorem baseExponent_le_adjExponent (D : GridPrefixEnvelopeGrowthData line m B X A U) :
    D.baseExponent ≤ D.adjExponent :=
  adjustedExponent_ge_base D.env D.baseExponent D.S D.N

theorem adjExponent_nonneg (D : GridPrefixEnvelopeGrowthData line m B X A U) :
    0 ≤ D.adjExponent :=
  D.baseExponent_nonneg.trans D.baseExponent_le_adjExponent

theorem env_le_adjExponent_of_three_le (D : GridPrefixEnvelopeGrowthData line m B X A U)
    {n : ℕ} (hn3 : 3 ≤ n) :
    D.env n ≤ exp (D.adjExponent * scale n) :=
  le_exp_adjustedExponent_of_three_le D.covers D.growth hn3

theorem env_le_of_adjExponent_le (D : GridPrefixEnvelopeGrowthData line m B X A U)
    {cM : ℝ} (hle : D.adjExponent ≤ cM) {n : ℕ} (hn3 : 3 ≤ n) :
    D.env n ≤ exp (cM * scale n) :=
  le_exp_of_le_adjustedExponent D.covers D.growth hle hn3

end GridPrefixEnvelopeGrowthData

/-- Sharp-prefix growth data with the unbounded initial field replaced by a
three-point finite check and a possibly enlarged polynomial exponent. -/
structure GridPrefixEnvelopeGrowthSmallCheck (line : DirichletLZerosOnLine)
    (m B : ℕ → ℕ) (X : ℕ → ℝ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ℕ → ι → ℕ) where
  data : GridPrefixEnvelopeGrowthData line m B X A U
  cM : ℝ
  hadjusted : data.adjExponent ≤ cM
  small : ∀ n ∈ Finset.range 3, data.env n ≤ exp (cM * scale n)

namespace GridPrefixEnvelopeGrowthSmallCheck

variable {line : DirichletLZerosOnLine} {m B : ℕ → ℕ} {X : ℕ → ℝ}
  {ι : Type} [Fintype ι] [DecidableEq ι] {A U : ℕ → ι → ℕ}

theorem envelope_poly (F : GridPrefixEnvelopeGrowthSmallCheck line m B X A U) (n : ℕ) :
    F.data.env n ≤ exp (F.cM * scale n) := by
  by_cases hn3 : 3 ≤ n
  · exact F.data.env_le_of_adjExponent_le F.hadjusted hn3
  · exact F.small n (Finset.mem_range.mpr (not_le.mp hn3))

theorem cM_nonneg (F : GridPrefixEnvelopeGrowthSmallCheck line m B X A U) : 0 ≤ F.cM :=
  F.data.adjExponent_nonneg.trans F.hadjusted

end GridPrefixEnvelopeGrowthSmallCheck

/-- The literal finite version of `GridPrefixEnvelopeGrowth`: the same exponent
and data, but the unbounded `initial` field is replaced by a finite check on
`initialFinset S N`. -/
structure GridPrefixEnvelopeGrowthFinite (line : DirichletLZerosOnLine)
    (m B : ℕ → ℕ) (X : ℕ → ℝ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ℕ → ι → ℕ) where
  cC : ℝ
  cU : ℝ
  cMB : ℝ
  cX : ℝ
  cK : ℝ
  cN : ℝ
  S : ℝ
  hcC : 0 ≤ cC
  hcU : 0 ≤ cU
  hcMB : 0 ≤ cMB
  hcX : 0 ≤ cX
  hcK : 0 ≤ cK
  hcN : 0 ≤ cN
  hS : 2 ≤ S
  hm : ∀ n, m n ≠ 0
  hB : ∀ n, B n ≠ 0
  hU : ∀ n i, 2 ≤ U n i
  hX : ∀ n, S ≤ scale n → 2 ≤ X n
  hCle : ∀ n, S ≤ scale n →
    prefixC (m n) (B n) (hm n) (hB n) line ≤ exp (cC * scale n)
  hKle : ∀ n, S ≤ scale n →
    prefixK (m n) (B n) (hm n) (hB n) line ≤ exp (cK * scale n)
  hMBle : ∀ n, S ≤ scale n →
    ((m n * B n : ℕ) : ℝ) ≤ exp (cMB * scale n)
  hUle : ∀ n, S ≤ scale n → ∀ i, (U n i : ℝ) ≤ exp (cU * scale n)
  hXle : ∀ n, S ≤ scale n → X n ≤ exp (cX * scale n)
  hNle : ∀ n, S ≤ scale n →
    ((primeBinProducts (A n) (U n)).card : ℝ) ≤ exp (cN * scale n)
  N : ℕ
  covers : CoversInitialSegment S N
  initial_finite : FiniteInitialSegmentCheck
    (fun n => gridPrefixEnvelope (m n) (B n)
      (prefixC (m n) (B n) (hm n) (hB n) line)
      (prefixK (m n) (B n) (hm n) (hB n) line) (X n) (A n) (U n))
    (gridPrefixEnvelopeExponent (ι := ι) cC cU cMB cX cK cN) S N

namespace GridPrefixEnvelopeGrowthFinite

variable {line : DirichletLZerosOnLine} {m B : ℕ → ℕ} {X : ℕ → ℝ}
  {ι : Type} [Fintype ι] [DecidableEq ι] {A U : ℕ → ι → ℕ}

/-- Forget the finite sample bound, recovering the unbounded growth structure. -/
noncomputable def toGrowth (F : GridPrefixEnvelopeGrowthFinite line m B X A U) :
    GridPrefixEnvelopeGrowth line m B X A U where
  cC := F.cC
  cU := F.cU
  cMB := F.cMB
  cX := F.cX
  cK := F.cK
  cN := F.cN
  S := F.S
  hcC := F.hcC
  hcU := F.hcU
  hcMB := F.hcMB
  hcX := F.hcX
  hcK := F.hcK
  hcN := F.hcN
  hS := F.hS
  hm := F.hm
  hB := F.hB
  hU := F.hU
  hX := F.hX
  hCle := F.hCle
  hKle := F.hKle
  hMBle := F.hMBle
  hUle := F.hUle
  hXle := F.hXle
  hNle := F.hNle
  initial := fun n hn =>
    (initialSegmentCheck_iff_finite F.covers).mpr F.initial_finite n hn

theorem envelope_poly (F : GridPrefixEnvelopeGrowthFinite line m B X A U)
    (n : ℕ) :
    gridPrefixEnvelope (m n) (B n)
      (prefixC (m n) (B n) (F.hm n) (F.hB n) line)
      (prefixK (m n) (B n) (F.hm n) (F.hB n) line) (X n) (A n) (U n) ≤
      exp (gridPrefixEnvelopeExponent (ι := ι) F.cC F.cU F.cMB F.cX F.cK F.cN *
        scale n) :=
  F.toGrowth.envelope_poly n

/-- Every unbounded growth certificate yields its finite-check version, by
choosing the explicit sample bound from `exists_initialBound`. -/
noncomputable def ofGrowth (G : GridPrefixEnvelopeGrowth line m B X A U) :
    GridPrefixEnvelopeGrowthFinite line m B X A U :=
  let N := Classical.choose (exists_initialBound G.S)
  let hN : CoversInitialSegment G.S N :=
    Classical.choose_spec (exists_initialBound G.S)
  { cC := G.cC
    cU := G.cU
    cMB := G.cMB
    cX := G.cX
    cK := G.cK
    cN := G.cN
    S := G.S
    hcC := G.hcC
    hcU := G.hcU
    hcMB := G.hcMB
    hcX := G.hcX
    hcK := G.hcK
    hcN := G.hcN
    hS := G.hS
    hm := G.hm
    hB := G.hB
    hU := G.hU
    hX := G.hX
    hCle := G.hCle
    hKle := G.hKle
    hMBle := G.hMBle
    hUle := G.hUle
    hXle := G.hXle
    hNle := G.hNle
    N := N
    covers := hN
    initial_finite := (initialSegmentCheck_iff_finite hN).mp G.initial }

end GridPrefixEnvelopeGrowthFinite

/-! ## 6. Constructing `EnergyScaleInputs` from the finite checks -/

/-- **Mellin certificate from the three-point finite check.** -/
noncomputable def mellinEnergyScaleOfSmallCheck
    (line : DirichletLZerosOnLine)
    {W : ℕ → ℝ} (hW0 : ∀ n, 0 ≤ W n) (hW : DominatesScale W)
    {η : ℝ} (hη : 0 < η)
    (q : ℕ → ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ℕ → ι → ℕ) (hAB : ∀ n i, A n i ≤ B n i)
    (hdisj : ∀ n, Pairwise fun i j =>
      Disjoint (primeBin (A n i) (B n i)) (primeBin (A n j) (B n j)))
    (σ t ν : ℕ → ℝ) (hσ : ∀ n, 0 ≤ σ n) (hν : ∀ n, 0 < ν n)
    (F : MellinEnvelopeGrowthSmallCheck line q B t)
    (M : MarginalMassCount ν W η) :
    EnergyScaleInputs W :=
  mellinEnergyScale line hW0 hW hη q F.data.hq A B F.data.hB hAB hdisj σ t ν
    hσ hν F.envelope_poly M

/-- **Mellin certificate from the three-point check, with the paper's totient
count.** -/
noncomputable def mellinEnergyScaleOfTotientCountSmallCheck
    (line : DirichletLZerosOnLine)
    {W : ℕ → ℝ} (hW0 : ∀ n, 0 ≤ W n) (hW : DominatesScale W)
    {η : ℝ} (hη : 0 < η)
    (q : ℕ → ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ℕ → ι → ℕ) (hAB : ∀ n i, A n i ≤ B n i)
    (hdisj : ∀ n, Pairwise fun i j =>
      Disjoint (primeBin (A n i) (B n i)) (primeBin (A n j) (B n j)))
    (σ t : ℕ → ℝ) (hσ : ∀ n, 0 ≤ σ n)
    (F : MellinEnvelopeGrowthSmallCheck line q B t)
    (htotient : ∀ n, exp (2 * η * W n) ≤ ((q n).totient : ℝ)) :
    EnergyScaleInputs W :=
  mellinEnergyScaleOfSmallCheck line hW0 hW hη q A B hAB hdisj σ t
    (fun n => Real.sqrt (((q n).totient : ℝ))) hσ
    (fun n => by
      have hqpos : 0 < q n := Nat.pos_of_ne_zero (F.data.hq n)
      have hφ : (0 : ℝ) < ((q n).totient : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hqpos
      exact Real.sqrt_pos.mpr hφ)
    F (mass_lower_sqrt_totient q W η F.data.hq htotient)

/-- **Grid-prefix certificate from the three-point finite check.** -/
noncomputable def gridPrefixEnergyScaleOfSmallCheck
    (line : DirichletLZerosOnLine)
    {W : ℕ → ℝ} (hW0 : ∀ n, 0 ≤ W n) (hW : DominatesScale W)
    {η : ℝ} (hη : 0 < η)
    (m Bm : ℕ → ℕ) (cop : ∀ n, (m n).Coprime (Bm n))
    (X : ℕ → ℝ) (cutoffs : ℕ → Finset ℕ) (hne : ∀ n, (cutoffs n).Nonempty)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ℕ → ι → ℕ)
    (hX : ∀ n, 2 ≤ X n) (heX : ∀ n, Real.exp 1 ≤ X n)
    (hcut : ∀ n j, j ∈ cutoffs n → X n ≤ (j : ℝ) + 1 / 2 ∧
      (j : ℝ) + 1 / 2 ≤ 2 * X n)
    (hP : ∀ n y, y ∈ primeBinProducts (A n) (U n) → X n ≤ (y : ℝ) ∧
      (y : ℝ) ≤ 2 * X n)
    (hAU : ∀ n i, A n i ≤ U n i)
    (hdisj : ∀ n, Pairwise fun i j =>
      Disjoint (primeBin (A n i) (U n i)) (primeBin (A n j) (U n j)))
    (ν : ℕ → ℝ) (hν : ∀ n, 0 < ν n)
    (F : GridPrefixEnvelopeGrowthSmallCheck line m Bm X A U)
    (M : MarginalMassCount
      (fun n => Real.sqrt (((m n).totient : ℝ)) * ν n) W η) :
    EnergyScaleInputs W :=
  gridPrefixEnergyScale line hW0 hW hη m Bm F.data.hm F.data.hB cop X cutoffs hne
    A U hX heX hcut hP F.data.hU hAU hdisj ν hν F.envelope_poly M

/-- **Grid-prefix certificate from the three-point check, with the paper's
totient count.** -/
noncomputable def gridPrefixEnergyScaleOfTotientCountSmallCheck
    (line : DirichletLZerosOnLine)
    {W : ℕ → ℝ} (hW0 : ∀ n, 0 ≤ W n) (hW : DominatesScale W)
    {η : ℝ} (hη : 0 < η)
    (m Bm : ℕ → ℕ) (massCount : ℕ → ℕ)
    (cop : ∀ n, (m n).Coprime (Bm n))
    (X : ℕ → ℝ) (cutoffs : ℕ → Finset ℕ) (hne : ∀ n, (cutoffs n).Nonempty)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ℕ → ι → ℕ)
    (hX : ∀ n, 2 ≤ X n) (heX : ∀ n, Real.exp 1 ≤ X n)
    (hcut : ∀ n j, j ∈ cutoffs n → X n ≤ (j : ℝ) + 1 / 2 ∧
      (j : ℝ) + 1 / 2 ≤ 2 * X n)
    (hP : ∀ n y, y ∈ primeBinProducts (A n) (U n) → X n ≤ (y : ℝ) ∧
      (y : ℝ) ≤ 2 * X n)
    (hAU : ∀ n i, A n i ≤ U n i)
    (hdisj : ∀ n, Pairwise fun i j =>
      Disjoint (primeBin (A n i) (U n i)) (primeBin (A n j) (U n j)))
    (F : GridPrefixEnvelopeGrowthSmallCheck line m Bm X A U)
    (hcount : ∀ n, 0 < massCount n)
    (htotient : ∀ n, exp (2 * η * W n) ≤ ((m n).totient : ℝ)) :
    EnergyScaleInputs W :=
  gridPrefixEnergyScaleOfSmallCheck line hW0 hW hη m Bm cop X cutoffs hne A U
    hX heX hcut hP hAU hdisj (fun n => (massCount n : ℝ))
    (fun n => by exact_mod_cast hcount n) F
    (mass_lower_of_totient_count m massCount W η F.data.hm hcount htotient)

/-- **Mellin certificate from the literal finite-`Finset` check.** -/
noncomputable def mellinEnergyScaleOfFinite
    (line : DirichletLZerosOnLine)
    {W : ℕ → ℝ} (hW0 : ∀ n, 0 ≤ W n) (hW : DominatesScale W)
    {η : ℝ} (hη : 0 < η)
    (q : ℕ → ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ℕ → ι → ℕ) (hAB : ∀ n i, A n i ≤ B n i)
    (hdisj : ∀ n, Pairwise fun i j =>
      Disjoint (primeBin (A n i) (B n i)) (primeBin (A n j) (B n j)))
    (σ t ν : ℕ → ℝ) (hσ : ∀ n, 0 ≤ σ n) (hν : ∀ n, 0 < ν n)
    (F : MellinEnvelopeGrowthFinite line q B t)
    (M : MarginalMassCount ν W η) :
    EnergyScaleInputs W :=
  mellinEnergyScaleOfGrowth line hW0 hW hη q A B hAB hdisj σ t ν hσ hν
    F.toGrowth M

/-- **Grid-prefix certificate from the literal finite-`Finset` check.** -/
noncomputable def gridPrefixEnergyScaleOfFinite
    (line : DirichletLZerosOnLine)
    {W : ℕ → ℝ} (hW0 : ∀ n, 0 ≤ W n) (hW : DominatesScale W)
    {η : ℝ} (hη : 0 < η)
    (m Bm : ℕ → ℕ) (cop : ∀ n, (m n).Coprime (Bm n))
    (X : ℕ → ℝ) (cutoffs : ℕ → Finset ℕ) (hne : ∀ n, (cutoffs n).Nonempty)
    {ι : Type} [Fintype ι] [DecidableEq ι] (A U : ℕ → ι → ℕ)
    (hX : ∀ n, 2 ≤ X n) (heX : ∀ n, Real.exp 1 ≤ X n)
    (hcut : ∀ n j, j ∈ cutoffs n → X n ≤ (j : ℝ) + 1 / 2 ∧
      (j : ℝ) + 1 / 2 ≤ 2 * X n)
    (hP : ∀ n y, y ∈ primeBinProducts (A n) (U n) → X n ≤ (y : ℝ) ∧
      (y : ℝ) ≤ 2 * X n)
    (hAU : ∀ n i, A n i ≤ U n i)
    (hdisj : ∀ n, Pairwise fun i j =>
      Disjoint (primeBin (A n i) (U n i)) (primeBin (A n j) (U n j)))
    (ν : ℕ → ℝ) (hν : ∀ n, 0 < ν n)
    (F : GridPrefixEnvelopeGrowthFinite line m Bm X A U)
    (M : MarginalMassCount
      (fun n => Real.sqrt (((m n).totient : ℝ)) * ν n) W η) :
    EnergyScaleInputs W :=
  gridPrefixEnergyScaleOfGrowth line hW0 hW hη m Bm cop X cutoffs hne A U
    hX heX hcut hP hAU hdisj ν hν F.toGrowth M

/-! ## 7. Axiom audit -/

#print axioms mem_initialFinset
#print axioms exists_initialBound
#print axioms initialSegmentCheck_iff_finite
#print axioms finiteInitialSegmentCheck_iff_finset
#print axioms scale_pos_of_three_le
#print axioms scale_zero
#print axioms scale_one
#print axioms scale_two_neg
#print axioms exp_mul_scale_two_anti
#print axioms mellinEnvelopeExponent_nonneg
#print axioms gridPrefixEnvelopeExponent_nonneg
#print axioms adjustedExponent_ge_base
#print axioms adjustedExponent_nonneg
#print axioms le_exp_adjustedExponent_of_three_le
#print axioms le_exp_of_le_adjustedExponent
#print axioms MellinEnvelopeGrowthData.baseExponent_nonneg
#print axioms MellinEnvelopeGrowthData.growth
#print axioms MellinEnvelopeGrowthData.env_le_adjExponent_of_three_le
#print axioms MellinEnvelopeGrowthData.env_le_of_adjExponent_le
#print axioms MellinEnvelopeGrowthSmallCheck.envelope_poly
#print axioms MellinEnvelopeGrowthFinite.toGrowth
#print axioms MellinEnvelopeGrowthFinite.ofGrowth
#print axioms MellinEnvelopeGrowthFinite.envelope_poly
#print axioms GridPrefixEnvelopeGrowthData.baseExponent_nonneg
#print axioms GridPrefixEnvelopeGrowthData.growth
#print axioms GridPrefixEnvelopeGrowthData.env_le_adjExponent_of_three_le
#print axioms GridPrefixEnvelopeGrowthData.env_le_of_adjExponent_le
#print axioms GridPrefixEnvelopeGrowthSmallCheck.envelope_poly
#print axioms GridPrefixEnvelopeGrowthFinite.toGrowth
#print axioms GridPrefixEnvelopeGrowthFinite.ofGrowth
#print axioms GridPrefixEnvelopeGrowthFinite.envelope_poly
#print axioms mellinEnergyScaleOfSmallCheck
#print axioms mellinEnergyScaleOfTotientCountSmallCheck
#print axioms gridPrefixEnergyScaleOfSmallCheck
#print axioms gridPrefixEnergyScaleOfTotientCountSmallCheck
#print axioms mellinEnergyScaleOfFinite
#print axioms gridPrefixEnergyScaleOfFinite

end Cogentic.RandomizedL19EnergyMassFinite
