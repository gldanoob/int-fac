import Cogentic.RandomizedEpochAssembly
import Cogentic.RandomizedBalancedScalarMargins
import Cogentic.RandomizedEpochEventCost
import Cogentic.RandomizedPreprocessingCost

/-!
# Public-work bounds for staged hard-input epochs

This file isolates the public-work conjunct of
`Cogentic.RandomizedEpochAssembly.HardEpochAsymptoticBound` and proves it from a
finite stage decomposition of `HardEpochData.pubWork`.

The blueprint (C4, `S0`–`S9`) describes `pubWork` as a sum of named stage costs.
The results here turn per-stage eventual exponential bounds on the *expected*
stage costs into the single bound

`mean E.actual (fun x => E.pubWork x) ≤ ENNReal.ofReal (exp ((C + δ/2) * scale n))`.

Main contents:

1. `StageDecomposition`: a finite type of stages with per-stage `ℕ`-valued cost
   functions and a pointwise identity `pubWork x = ∑ j, cost j x`.
2. `eventually_mean_pubWork_le_exp`: the summation engine.  It lifts the stage
   decomposition to the all-`n` epoch space, applies the existing
   `eventually_mean_finset_sum_le_exp` / `eventually_finset_sum_le_exp` combiner,
   and transfers the result back to every `hN : 3 ≤ n`.
3. `mean_pubWork_le_exp_of_stagewise`: the same result in the exact shape used by
   `HardEpochAsymptoticBound`.
4. `HardEpochNonWorkBound` and `hardEpochAsymptoticBound_of_stagewise`: the
   plug-in theorem that discharges `HardEpochAsymptoticBound E C` once the
   non-work conjuncts (congruence, hidden uniformity, hit probability) are known.
5. `BlueprintStage` (the ten blueprint stages `S0`–`S9`) and the instantiation
   `eventually_mean_pubWork_le_exp_of_blueprintStages`.
6. `eventually_mean_pubWork_le_exp_of_balancedSchedule` and
   `hardEpochAsymptoticBound_of_balancedSchedule`: the per-stage exponents are
   the balanced-schedule knot costs `s.perturbation.h * s.knot (i + 1)`, and the
   strict inequalities needed by the summation engine are discharged from
   `BalancedRationalSchedule.Valid`.
7. `eventually_mean_pubWork_le_exp_of_screeningStage`: composition with the
   existing private-screening summation engine
   `balancedSchedule_multistage_screening_cost_le_exp`.  The aggregate screening
   stage uses `W j₀ n = rows n * ∑ i, arrivalProb i n * stageWork i n` and
   exponent `D`; its weight bound is supplied directly by that lemma.
8. `serialized_assembled_epoch_stagewise_from_critical_line`: the end-to-end
   serialized factoring theorem with the epoch work hypothesis replaced by a
   stage decomposition and per-stage bounds.

The only modelling input not provided by the current concrete definitions is the
identity between the PMF mean of a stage cost and its work weight `W j n`; it is
an explicit hypothesis (`hmean`) throughout.  In particular the concrete `S0`–`S9`
cost functions of the blueprint are not yet defined in Lean, so the blueprint
instantiation is stated for an arbitrary supplied stage list.
-/

namespace Cogentic.RandomizedEpochWork

open Cogentic.Randomized
open Cogentic.RandomizedCappedEpoch
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedFactorSerialization
open Cogentic.RandomizedFiniteSupportTV
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedInputDriver
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Filter Real
open scoped BigOperators ENNReal

/-! ## Stage decompositions -/

/-- A finite stage decomposition of the public work of a family of hard-input
epochs.  The stage costs are `ℕ`-valued, hence nonnegative by construction. -/
structure StageDecomposition (E : ∀ n, 3 ≤ n → HardEpochData n) (ι : Type*)
    [Fintype ι] where
  /-- Cost charged by stage `j` on epoch `n` and sample `x`. -/
  cost : ι → (n : ℕ) → (hN : 3 ≤ n) → (E n hN).Sample → ℕ
  /-- Pointwise decomposition of the public work into the named stages. -/
  pubWork_eq : ∀ (n : ℕ) (hN : 3 ≤ n) (x : (E n hN).Sample),
    (E n hN).pubWork x = ∑ j : ι, cost j n hN x

namespace StageDecomposition

/-- Stage cost lifted to the all-`n` epoch space, vanishing off the epoch
branch.  This is the observable to which the finite-sum expectation combiner is
applied. -/
def costOn {E : ∀ n, 3 ≤ n → HardEpochData n} {ι : Type*} [Fintype ι]
    (S : StageDecomposition E ι) (j : ι) (n : ℕ) : epochSpace E n → ℕ
  | none => 0
  | some ⟨h, x⟩ => S.cost j n h.down x

/-- Pointwise summation identity on the lifted epoch space. -/
theorem sum_costOn {E : ∀ n, 3 ≤ n → HardEpochData n} {ι : Type*} [Fintype ι]
    (S : StageDecomposition E ι) (n : ℕ) (a : epochSpace E n) :
    (∑ j : ι, S.costOn j n a) = match a with
      | none => 0
      | some ⟨h, x⟩ => (E n h.down).pubWork x := by
  cases a with
  | none => simp [costOn]
  | some p =>
    obtain ⟨h, x⟩ := p
    simpa only [costOn] using (S.pubWork_eq n h.down x).symm

end StageDecomposition

/-! ## The summation engine -/

/-- **Public-work summation engine.**  If the public work of every epoch splits
pointwise into finitely many stage costs, each stage has expected cost eventually
at most `W j n`, and `W j n ≤ exp (c j * scale n)` with `c j < D`, then the mean
public work is eventually at most `exp (D * scale n)` for every `hN`.

The proof reuses `eventually_mean_finset_sum_le_exp` (which itself is built on
`eventually_finset_sum_le_exp`) after lifting the stage costs to `epochSpace`. -/
theorem eventually_mean_pubWork_le_exp
    {ι : Type*} [Fintype ι]
    (E : ∀ n, 3 ≤ n → HardEpochData n) (S : StageDecomposition E ι)
    (W : ι → ℕ → ℝ) (c : ι → ℝ) {D : ℝ}
    (hc : ∀ j, c j < D)
    (hmean : ∀ j, ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
      mean (E n hN).actual
        (fun x => (S.cost j n hN x : ℝ≥0∞)) ≤ ENNReal.ofReal (W j n))
    (hW : ∀ j, ∀ᶠ n : ℕ in atTop, W j n ≤ exp (c j * scale n)) :
    ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
      ∃ W_pub : ℝ,
        mean (E n hN).actual (fun x => ((E n hN).pubWork x : ℝ≥0∞)) ≤
          ENNReal.ofReal W_pub ∧
        W_pub ≤ exp (D * scale n) := by
  classical
  let p : ∀ n, PMF (epochSpace E n) := epochLaw E
  let work : ι → ∀ n, epochSpace E n → ℕ := fun j n => S.costOn j n
  have hmean' : ∀ j, ∀ᶠ n : ℕ in atTop,
      mean (p n) (fun a => (work j n a : ℝ≥0∞)) ≤ ENNReal.ofReal (W j n) := by
    intro j
    filter_upwards [hmean j, eventually_ge_atTop (3 : ℕ)] with n hn h3
    rw [show p n = (E n h3).actual.map (epochEmbed E h3) from epochLaw_of_le E h3,
      mean_map]
    simpa only [work, StageDecomposition.costOn, epochEmbed] using hn h3
  have hsum := eventually_mean_finset_sum_le_exp (Finset.univ : Finset ι) p work W c
    (fun j _ => hc j) (fun j _ => hmean' j) (fun j _ => hW j)
  filter_upwards [hsum, eventually_ge_atTop (3 : ℕ)] with n hn h3
  intro hN
  obtain ⟨W_tot, hbound, hWle⟩ := hn
  refine ⟨W_tot, ?_, hWle⟩
  simp only [p] at hbound
  rw [show epochLaw E n = (E n hN).actual.map (epochEmbed E hN) from epochLaw_of_le E hN,
    mean_map] at hbound
  have hfun :
      (fun x : (E n hN).Sample =>
          ((∑ j : ι, work j n (epochEmbed E hN x) : ℕ) : ℝ≥0∞)) =
        fun x => ((E n hN).pubWork x : ℝ≥0∞) := by
    funext x
    rw [S.pubWork_eq n hN x]
    simp only [Nat.cast_sum, work, StageDecomposition.costOn, epochEmbed]
  rw [hfun] at hbound
  exact hbound

/-- The exact bound consumed by `HardEpochAsymptoticBound`: the mean public work
is eventually at most `exp (D * scale n)` in the `ℝ≥0∞`-valued form. -/
theorem mean_pubWork_le_exp_of_stagewise
    {ι : Type*} [Fintype ι]
    (E : ∀ n, 3 ≤ n → HardEpochData n) (S : StageDecomposition E ι)
    (W : ι → ℕ → ℝ) (c : ι → ℝ) {D : ℝ}
    (hc : ∀ j, c j < D)
    (hmean : ∀ j, ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
      mean (E n hN).actual
        (fun x => (S.cost j n hN x : ℝ≥0∞)) ≤ ENNReal.ofReal (W j n))
    (hW : ∀ j, ∀ᶠ n : ℕ in atTop, W j n ≤ exp (c j * scale n)) :
    ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
      mean (E n hN).actual (fun x => ((E n hN).pubWork x : ℝ≥0∞)) ≤
        ENNReal.ofReal (exp (D * scale n)) := by
  filter_upwards [eventually_mean_pubWork_le_exp E S W c hc hmean hW] with n hn
  intro hN
  obtain ⟨W_pub, h1, h2⟩ := hn hN
  exact h1.trans (ENNReal.ofReal_le_ofReal h2)

/-! ## Plugging the work bound into `HardEpochAsymptoticBound` -/

/-- The non-work conjuncts of `HardEpochAsymptoticBound`, split out so that the
public-work bound can be supplied independently by the stagewise engine. -/
def HardEpochNonWorkBound (E : ∀ n, 3 ≤ n → HardEpochData n) : Prop :=
  ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
    Odd n → ¬n.Prime → ¬IsPrimePow n →
      (E n hN).CongruenceCheck ∧
      (E n hN).HiddenUniform ∧
      ∃ γ ε : ℝ,
        0 ≤ γ ∧
        γ ≤ ((E n hN).ideal.toOuterMeasure
          {x | observe (E n hN).trace x ∈ (E n hN).good}).toReal ∧
        pmfTotalVariation (E n hN).ideal (E n hN).actual ≤ ε ∧
        exp (-(δ / 4) * scale n) ≤ γ / 2 - ε

/-- **Stagewise `HardEpochAsymptoticBound`.**  If every stage exponent is
strictly below `C` and the non-work conjuncts hold, then the full asymptotic
epoch bound at ceiling `C` holds.  This is the promised plug-in point: the
conclusion is exactly `HardEpochAsymptoticBound E C`, so it can be passed
directly to `serialized_assembled_epoch_from_critical_line` or to
`serialized_assembled_balancedEnvelopeInfimum_from_critical_line`. -/
theorem hardEpochAsymptoticBound_of_stagewise
    {ι : Type*} [Fintype ι]
    (E : ∀ n, 3 ≤ n → HardEpochData n) (S : StageDecomposition E ι)
    (W : ι → ℕ → ℝ) (c : ι → ℝ) {C : ℝ}
    (hc : ∀ j, c j < C)
    (hmean : ∀ j, ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
      mean (E n hN).actual
        (fun x => (S.cost j n hN x : ℝ≥0∞)) ≤ ENNReal.ofReal (W j n))
    (hW : ∀ j, ∀ᶠ n : ℕ in atTop, W j n ≤ exp (c j * scale n))
    (hrest : HardEpochNonWorkBound E) :
    HardEpochAsymptoticBound E C := by
  intro δ hδ
  have hδ2 : 0 < δ / 2 := by positivity
  filter_upwards [eventually_mean_pubWork_le_exp E S W c
      (fun j => (hc j).trans (by linarith only [hδ2] : C < C + δ / 2))
      hmean hW,
    hrest δ hδ, eventually_ge_atTop (3 : ℕ)] with n hwork hrestn h3
  intro hN ho hp hpow
  obtain ⟨W_pub, hmeanpub, hWpub⟩ := hwork hN
  obtain ⟨hcong, hunif, γ, ε, hγ0, hγ, hTV, hhit⟩ := hrestn hN ho hp hpow
  exact ⟨hcong, hunif, W_pub, γ, ε, hγ0, hmeanpub, hWpub, hγ, hTV, hhit⟩

/-! ## Instantiation on the blueprint stage list `S0`–`S9` -/

/-- The ten stages `S0`–`S9` of the randomized factoring blueprint, indexed by
`Fin 10`. -/
abbrev BlueprintStage : Type := Fin 10

namespace BlueprintStage

/-- Integer parameters / deterministic setup. -/
def S0 : BlueprintStage := ⟨0, by decide⟩

/-- Public coins: field pool and multiplier data. -/
def S1 : BlueprintStage := ⟨1, by decide⟩

/-- Character probes per field. -/
def S2 : BlueprintStage := ⟨2, by decide⟩

/-- Private reduced-class sampler. -/
def S3 : BlueprintStage := ⟨3, by decide⟩

/-- Staged private screening (ECM). -/
def S4 : BlueprintStage := ⟨4, by decide⟩

/-- Public descent. -/
def S5 : BlueprintStage := ⟨5, by decide⟩

/-- Row records. -/
def S6 : BlueprintStage := ⟨6, by decide⟩

/-- Sparse `F₂` dependency. -/
def S7 : BlueprintStage := ⟨7, by decide⟩

/-- Square root and product check. -/
def S8 : BlueprintStage := ⟨8, by decide⟩

/-- Private final gcd. -/
def S9 : BlueprintStage := ⟨9, by decide⟩

end BlueprintStage

/-- Blueprint instantiation of the summation engine: a concrete epoch whose
public work is the sum of ten named stage costs `S0`–`S9` satisfies the mean
public-work bound as soon as each named stage has the required eventual
exponential bound. -/
theorem eventually_mean_pubWork_le_exp_of_blueprintStages
    (E : ∀ n, 3 ≤ n → HardEpochData n)
    (cost : BlueprintStage → (n : ℕ) → (hN : 3 ≤ n) → (E n hN).Sample → ℕ)
    (hpub : ∀ (n : ℕ) (hN : 3 ≤ n) (x : (E n hN).Sample),
      (E n hN).pubWork x = ∑ j : BlueprintStage, cost j n hN x)
    (W : BlueprintStage → ℕ → ℝ) (c : BlueprintStage → ℝ) {D : ℝ}
    (hc : ∀ j, c j < D)
    (hmean : ∀ j, ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
      mean (E n hN).actual
        (fun x => (cost j n hN x : ℝ≥0∞)) ≤ ENNReal.ofReal (W j n))
    (hW : ∀ j, ∀ᶠ n : ℕ in atTop, W j n ≤ exp (c j * scale n)) :
    ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
      mean (E n hN).actual (fun x => ((E n hN).pubWork x : ℝ≥0∞)) ≤
        ENNReal.ofReal (exp (D * scale n)) :=
  mean_pubWork_le_exp_of_stagewise E ⟨cost, hpub⟩ W c hc hmean hW

/-- `HardEpochAsymptoticBound` from a named `S0`–`S9` decomposition. -/
theorem hardEpochAsymptoticBound_of_blueprintStages
    (E : ∀ n, 3 ≤ n → HardEpochData n)
    (cost : BlueprintStage → (n : ℕ) → (hN : 3 ≤ n) → (E n hN).Sample → ℕ)
    (hpub : ∀ (n : ℕ) (hN : 3 ≤ n) (x : (E n hN).Sample),
      (E n hN).pubWork x = ∑ j : BlueprintStage, cost j n hN x)
    (W : BlueprintStage → ℕ → ℝ) (c : BlueprintStage → ℝ) {C : ℝ}
    (hc : ∀ j, c j < C)
    (hmean : ∀ j, ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
      mean (E n hN).actual
        (fun x => (cost j n hN x : ℝ≥0∞)) ≤ ENNReal.ofReal (W j n))
    (hW : ∀ j, ∀ᶠ n : ℕ in atTop, W j n ≤ exp (c j * scale n))
    (hrest : HardEpochNonWorkBound E) :
    HardEpochAsymptoticBound E C :=
  hardEpochAsymptoticBound_of_stagewise E ⟨cost, hpub⟩ W c hc hmean hW hrest

/-! ## Schedule-derived stage exponents -/

/-- Given a valid `BalancedRationalSchedule`, every exponent of the form
`s.perturbation.h * s.knot (e j + 1)` is strictly below the schedule target
`D` (and hence below any larger ceiling). -/
theorem balancedSchedule_knotExponent_lt {ι : Type*} [Fintype ι]
    (s : BalancedRationalSchedule) {D : ℝ} (hvalid : s.Valid D)
    (e : ι → ℕ) (he : ∀ j, e j < s.k + 1) (j : ι) :
    s.perturbation.h * s.knot (e j + 1) < D := by
  have hbpos : 0 < s.perturbation.b := by
    have := hvalid.2.2.1
    linarith
  have hqpos : 0 < s.perturbation.q := hvalid.2.2.2.2.2.2.1
  have hwpos : ∀ i < s.k + 1, 0 < s.weight i :=
    hvalid.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hgate :=
    hvalid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (e j) (he j)
  have htail : 0 ≤ ∑ i ∈ Finset.Ico (e j) (s.k + 1), s.weight i :=
    Finset.sum_nonneg fun i hi => (hwpos i (Finset.mem_Ico.mp hi).2).le
  linarith only [hgate, hbpos, hqpos, htail]

/-- **Schedule-weighted work bound.**  If the stage exponents are the balanced
schedule knot costs `s.perturbation.h * s.knot (e j + 1)` and the schedule is
valid at target `D`, then the mean public work is eventually at most
`exp ((D + δ) * scale n)` for every `δ > 0`.  Strictness of the exponent
inequalities required by the summation engine is discharged from `s.Valid D`. -/
theorem eventually_mean_pubWork_le_exp_of_balancedSchedule
    {ι : Type*} [Fintype ι]
    (E : ∀ n, 3 ≤ n → HardEpochData n) (S : StageDecomposition E ι)
    (s : BalancedRationalSchedule) {D δ : ℝ}
    (hvalid : s.Valid D) (hδ : 0 < δ)
    (e : ι → ℕ) (he : ∀ j, e j < s.k + 1)
    (W : ι → ℕ → ℝ)
    (hmean : ∀ j, ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
      mean (E n hN).actual
        (fun x => (S.cost j n hN x : ℝ≥0∞)) ≤ ENNReal.ofReal (W j n))
    (hW : ∀ j, ∀ᶠ n : ℕ in atTop,
      W j n ≤ exp ((s.perturbation.h * s.knot (e j + 1)) * scale n)) :
    ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
      mean (E n hN).actual (fun x => ((E n hN).pubWork x : ℝ≥0∞)) ≤
        ENNReal.ofReal (exp ((D + δ) * scale n)) := by
  refine mean_pubWork_le_exp_of_stagewise E S W
    (fun j => s.perturbation.h * s.knot (e j + 1)) ?_ hmean hW
  intro j
  have hlt := balancedSchedule_knotExponent_lt s hvalid e he j
  linarith only [hlt, hδ]

/-- `HardEpochAsymptoticBound` at the schedule ceiling `D`, with stage exponents
given by the balanced schedule knots. -/
theorem hardEpochAsymptoticBound_of_balancedSchedule
    {ι : Type*} [Fintype ι]
    (E : ∀ n, 3 ≤ n → HardEpochData n) (S : StageDecomposition E ι)
    (s : BalancedRationalSchedule) {D : ℝ} (hvalid : s.Valid D)
    (e : ι → ℕ) (he : ∀ j, e j < s.k + 1)
    (W : ι → ℕ → ℝ)
    (hmean : ∀ j, ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
      mean (E n hN).actual
        (fun x => (S.cost j n hN x : ℝ≥0∞)) ≤ ENNReal.ofReal (W j n))
    (hW : ∀ j, ∀ᶠ n : ℕ in atTop,
      W j n ≤ exp ((s.perturbation.h * s.knot (e j + 1)) * scale n))
    (hrest : HardEpochNonWorkBound E) :
    HardEpochAsymptoticBound E D := by
  refine hardEpochAsymptoticBound_of_stagewise E S W
    (fun j => s.perturbation.h * s.knot (e j + 1)) ?_ hmean hW hrest
  intro j
  exact balancedSchedule_knotExponent_lt s hvalid e he j

/-! ## Composing the screening summation engine with the work engine -/

/-- **Screening-stage composition.**  This is the interface that consumes
`balancedSchedule_multistage_screening_cost_le_exp` directly.  One distinguished
stage `j₀` of the decomposition is the aggregate private-screening stage: its
work weight is the schedule product
`rows n * ∑ i, arrivalProb i n * stageWork i n` and its exponent is the schedule
ceiling `D`.  All other stages carry their own exponents `c j < D + δ`.  The
conclusion is the same public-work bound at ceiling `D + δ`.

The only modelling input not provided by the current definitions is `hmean`,
the identity between the PMF mean of each stage cost and its work weight. -/
theorem eventually_mean_pubWork_le_exp_of_screeningStage
    {ι : Type*} [Fintype ι]
    (E : ∀ n, 3 ≤ n → HardEpochData n) (S : StageDecomposition E ι) (j₀ : ι)
    (s : BalancedRationalSchedule) {D η δ : ℝ}
    (hvalid : s.Valid D) (hδ : 0 < δ)
    (rows : ℕ → ℝ) (arrivalProb stageWork : ℕ → ℕ → ℝ)
    (W : ι → ℕ → ℝ) (c : ι → ℝ)
    (hWj₀ : ∀ n : ℕ,
      W j₀ n = rows n * (∑ i ∈ Finset.range (s.k + 1),
        arrivalProb i n * stageWork i n))
    (hmean : ∀ j, ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
      mean (E n hN).actual
        (fun x => (S.cost j n hN x : ℝ≥0∞)) ≤ ENNReal.ofReal (W j n))
    (hcj₀ : c j₀ = D)
    (hc : ∀ j, j ≠ j₀ → c j < D + δ)
    (hW : ∀ j, j ≠ j₀ → ∀ᶠ n : ℕ in atTop, W j n ≤ exp (c j * scale n))
    (hrows_nn : ∀ᶠ n : ℕ in atTop, 0 ≤ rows n)
    (hprob_nn : ∀ i ≤ s.k, ∀ᶠ n : ℕ in atTop, 0 ≤ arrivalProb i n)
    (hwork_nn : ∀ i ≤ s.k, ∀ᶠ n : ℕ in atTop, 0 ≤ stageWork i n)
    (hrows : ∀ᶠ n : ℕ in atTop,
      rows n ≤ exp ((s.perturbation.b +
        (∑ j ∈ Finset.range (s.k + 1), s.weight j) + η) * scale n))
    (hprob : ∀ i ≤ s.k, ∀ᶠ n : ℕ in atTop,
      arrivalProb i n ≤ exp (-(∑ j ∈ Finset.range i, s.weight j) * scale n))
    (hstage : ∀ i ≤ s.k, ∀ᶠ n : ℕ in atTop,
      stageWork i n ≤ exp ((s.perturbation.h * s.knot (i + 1)) * scale n))
    (hη : η ≤ s.perturbation.q) :
    ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
      ∃ W_pub : ℝ,
        mean (E n hN).actual (fun x => ((E n hN).pubWork x : ℝ≥0∞)) ≤
          ENNReal.ofReal W_pub ∧
        W_pub ≤ exp ((D + δ) * scale n) := by
  have hc' : ∀ j, c j < D + δ := by
    intro j
    by_cases hj : j = j₀
    · rw [hj, hcj₀]
      linarith only [hδ]
    · exact hc j hj
  have screen := balancedSchedule_multistage_screening_cost_le_exp s hvalid hη
    rows arrivalProb stageWork hrows_nn hprob_nn hwork_nn hrows hprob hstage
  have hW' : ∀ j, ∀ᶠ n : ℕ in atTop, W j n ≤ exp (c j * scale n) := by
    intro j
    by_cases hj : j = j₀
    · subst j
      filter_upwards [screen] with n hn
      rw [hWj₀ n, hcj₀]
      exact hn
    · exact hW j hj
  exact eventually_mean_pubWork_le_exp E S W c hc' hmean hW'

/-! ## End-to-end plug-in -/

/-- End-to-end serialized factoring theorem in which the `HardEpochAsymptoticBound`
work hypothesis has been replaced by an explicit finite stage decomposition and
per-stage expected-cost bounds.  This is obtained purely by composing
`hardEpochAsymptoticBound_of_stagewise` with
`serialized_assembled_epoch_from_critical_line`; no scalar schedule proof is
duplicated. -/
theorem serialized_assembled_epoch_stagewise_from_critical_line
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (ι : Type) [Fintype ι]
      (E : ∀ n, 3 ≤ n → HardEpochData n) (S : StageDecomposition E ι)
      (W : ι → ℕ → ℝ) (c : ι → ℝ) {C : ℝ}, 0 ≤ C →
      (∀ j, c j < C) →
      (∀ j, ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
        mean (E n hN).actual
          (fun x => (S.cost j n hN x : ℝ≥0∞)) ≤ ENNReal.ofReal (W j n)) →
      (∀ j, ∀ᶠ n : ℕ in atTop, W j n ≤ exp (c j * scale n)) →
      HardEpochNonWorkBound E →
      (∀ n (hn : 2 ≤ n) bits,
        bits ∈ (outputBits k sound (epochHard (epochLaw E) (epochAttempt E)) n hn).support →
        ∃ xs, decodeFactors bits = some xs ∧ xs.Perm n.primeFactorsList) ∧
      ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
        mean (serializedFactor k sound (epochHard (epochLaw E) (epochAttempt E)) n hn)
          (fun out => (out.2 : ℝ≥0∞)) ≤ ENNReal.ofReal (exp ((C + ε) * scale n)) := by
  obtain ⟨k, sound, hmain⟩ := serialized_assembled_epoch_from_critical_line line
  refine ⟨k, sound, ?_⟩
  intro ι _ E S W c C hC hc hmean hW hrest
  exact hmain E hC (hardEpochAsymptoticBound_of_stagewise E S W c hc hmean hW hrest)

/-! ## Sanity check on a constant-work stage list -/

/-- For a family of epochs with a constant public work `K n` and a single stage
whose cost is that constant, the engine reproduces the expected
`exp (D * scale n)` bound as soon as `K n ≤ exp (c * scale n)` with `c < D`.
This checks that the interface is not vacuous in the work component. -/
theorem eventually_mean_pubWork_le_exp_of_constWork
    (E : ∀ n, 3 ≤ n → HardEpochData n) (K : ℕ → ℕ) (c D : ℝ)
    (hpub : ∀ (n : ℕ) (hN : 3 ≤ n) (x : (E n hN).Sample), (E n hN).pubWork x = K n)
    (hc : c < D) (hK : ∀ᶠ n : ℕ in atTop, (K n : ℝ) ≤ exp (c * scale n)) :
    ∀ᶠ n : ℕ in atTop, ∀ hN : 3 ≤ n,
      mean (E n hN).actual (fun x => ((E n hN).pubWork x : ℝ≥0∞)) ≤
        ENNReal.ofReal (exp (D * scale n)) := by
  classical
  let S : StageDecomposition E Unit :=
    { cost := fun _ n _ _ => K n
      pubWork_eq := by
        intro n hN x
        simpa using hpub n hN x }
  refine mean_pubWork_le_exp_of_stagewise E S (fun _ n => (K n : ℝ))
    (fun _ => c) (fun _ => hc) ?_ ?_
  · intro j
    filter_upwards with n hN
    change mean (E n hN).actual (fun _ => ((K n : ℕ) : ℝ≥0∞)) ≤
      ENNReal.ofReal ((K n : ℝ))
    rw [mean_const, ENNReal.ofReal_natCast]
  · intro j
    simpa using hK

/-! ## Axiom audit -/

#print axioms eventually_mean_pubWork_le_exp
#print axioms mean_pubWork_le_exp_of_stagewise
#print axioms hardEpochAsymptoticBound_of_stagewise
#print axioms eventually_mean_pubWork_le_exp_of_blueprintStages
#print axioms hardEpochAsymptoticBound_of_blueprintStages
#print axioms balancedSchedule_knotExponent_lt
#print axioms eventually_mean_pubWork_le_exp_of_balancedSchedule
#print axioms hardEpochAsymptoticBound_of_balancedSchedule
#print axioms eventually_mean_pubWork_le_exp_of_screeningStage
#print axioms serialized_assembled_epoch_stagewise_from_critical_line
#print axioms eventually_mean_pubWork_le_exp_of_constWork

end Cogentic.RandomizedEpochWork
