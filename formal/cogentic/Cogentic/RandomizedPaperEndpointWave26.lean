import Cogentic.RandomizedPaperEndpointWave25
import Cogentic.RandomizedL30NoBinomial

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# Wave 26: removing both L30 analytic density fields at once

Wave 25 removed the analytic sharp global upper density
`global_upper : GlobalOddUpperDensitySharp C p ε` from the L30 counts by
deriving it from the unconditional constant-`1` theorem
`paperScaleSmoothUpperSharp_one_unconditional` (through
`globalOddUpperDensitySharp_of_one_le`) using only `PaperDensityGrowth p`,
`0 < ε` and `1 ≤ C`.

`Cogentic.RandomizedL30NoBinomial` removed the analytic global binomial lower
bound `global_binomial : GlobalOddBinomialCount B p (paperT p) err` from the
L30 counts, replacing it by the pointwise global lower bound
`global_lower : YounisOddGlobalLower B p (paperT p) err`; that lower bound is
itself a theorem of GRH plus `PaperDensityGrowth p` via
`eventually_younisOddGlobalLower_paper_of_le` and the eventual-to-pointwise
shift adapter.

This file performs both reductions simultaneously.

* `Wave26L30Counts` has **no** `global_upper`, **no** `global_binomial` and,
  since the GRH lower bound is available through the line hypothesis, **no**
  `global_lower` field either.  Its fields are the prime/error/scale data, the
  four arithmetic constants with their side conditions, the sharp central
  interval count `short_interval`, and the (purely arithmetic/elementary)
  assumptions `growth`, `ε_pos`, `l30C_ge_one` and `l30B_le_eighth`.
* `sharpUpper` derives `GlobalOddUpperDensitySharp C p ε` unconditionally in the
  line hypothesis, and `globalLower line` derives the eventual global lower
  bound `EventuallyYounisOddGlobalLower B p (paperT p) err` from
  `eventually_younisOddGlobalLower_paper_of_le`.
* `toWave14L30CountsNoBinomial line` is the shift adapter that turns the
  eventual lower density into the pointwise `Wave14L30CountsNoBinomial` record,
  filling `global_upper` with the derived `sharpUpper` and `global_lower` with
  the shifted GRH bound.
* `Wave26L30Inputs` carries the Cantor/H.5 and H.3 failure data unchanged, so
  the ledger loss is still the actual failure probability
  (`toSubexpLeaf`, `loss_eq`).
* `PaperResidualFor26` is the Wave-25 E-generic record with
  `l30 : Wave26L30Inputs`; `toFullyDischargedInputs` is unconditional (the
  ledger only reads the L30 failure leaf), and
  `serialized_assembled_balancedEnvelopeInfimum_from_wave26Inputs` is the
  E-generic endpoint, with `E` quantified inside the conclusion.

Because the Wave-14 `Wave14L30Counts`/`Wave25L30Counts` records still store the
*explicit* binomial count (which is strictly stronger than the global lower
bound and is not available from GRH in this development), the arrows to those
two records are provided conditionally on an explicit `GlobalOddBinomialCount`;
the unconditional arrows go to the binomial-free records.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no count, loss,
probability or error is set to zero.
-/

namespace Cogentic.RandomizedPaperEndpointWave26

open Filter Real
open scoped BigOperators ENNReal Classical
open Cogentic.Randomized
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedC5Full
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedFactorSerialization
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedInputDriver
open Cogentic.RandomizedL18_4
open Cogentic.RandomizedL19Full
open Cogentic.RandomizedL20_2ConcentrationLeaf
open Cogentic.RandomizedL20_4LeafAssembly
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2ConcreteLeaf
open Cogentic.RandomizedL21_2LeafAssembly
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27StageOneFinish
open Cogentic.RandomizedL27Waterhouse
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30GlobalLower
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30LPP
open Cogentic.RandomizedL30LeafFromGRH
open Cogentic.RandomizedL30NoBinomial
open Cogentic.RandomizedL30PrimeReciprocal
open Cogentic.RandomizedL30Raw
open Cogentic.RandomizedL30Sharp
open Cogentic.RandomizedL30ShortInterval
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL34ChebotarevSides
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedP1Prepass
open Cogentic.RandomizedPaperEndpoint
open Cogentic.RandomizedPaperEndpointDischarged
open Cogentic.RandomizedPaperEndpointFullyDischarged
open Cogentic.RandomizedPaperEndpointWave13
open Cogentic.RandomizedPaperEndpointWave14
open Cogentic.RandomizedPaperEndpointWave15
open Cogentic.RandomizedPaperEndpointWave16
open Cogentic.RandomizedPaperEndpointWave17
open Cogentic.RandomizedPaperEndpointWave24
open Cogentic.RandomizedPaperEndpointWave25
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedPreprocessing
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedWave17Audit

universe u

/-! ## The Wave-26 L30 counts -/

/-- **The Wave-26 L30 counts: both analytic density fields are gone.**

Compared with `Wave14L30Counts`:

* the sharp global upper density `global_upper` is replaced by the arithmetic
  data `growth`, `ε_pos` and `l30C_ge_one`;
* the explicit global binomial lower bound `global_binomial` is replaced by the
  arithmetic/data-free field `l30B_le_eighth` (needed only to invoke the GRH
  lower bound at the paper constant `1/8`), and no pointwise `global_lower`
  field is kept because `globalLower` derives it from the line hypothesis.

The only analytic counting field is the sharp central paper interval count
`short_interval`.  The prime/error/scale data and the four constants `A`, `B`,
`c`, `C` with their arithmetic side conditions are unchanged.  The LPP data is
inserted unconditionally by the adapters, so it is not a field. -/
structure Wave26L30Counts where
  /-- The prime whose genus-two order is counted. -/
  p : ℕ → ℝ
  /-- The explicit `1 + o(1)` relative error. -/
  err : ℕ → ℝ
  /-- The constant paper error underlying the sharp density statements. -/
  ε : ℝ
  /-- The relative error is the constant paper error. -/
  err_eq : err = paperError ε
  /-- The relative short-interval density constant. -/
  A : ℝ
  /-- The global smooth lower-bound constant. -/
  B : ℝ
  /-- The paper short-count constant. -/
  c : ℝ
  /-- The global odd upper-density constant. -/
  C : ℝ
  /-- `A > 0`. -/
  A_pos : 0 < A
  /-- `B > 0`. -/
  B_pos : 0 < B
  /-- The arithmetic relation `A B ≥ 4`. -/
  AB_ge_four : 4 ≤ A * B
  /-- The paper count dominates the relative density constant. -/
  AC_le : A * C ≤ c
  /-- **Younis's sharp paper interval count** at `t = t_p`, with the true
  exponent `u log u`.  This is the only remaining L30 analytic field. -/
  short_interval : YounisOddPaperSharpIntervalCount c p ε
  /-- Paper density growth of `p`; an elementary growth hypothesis, used by the
  unconditional sharp upper-density theorem and by the GRH lower bound. -/
  growth : PaperDensityGrowth p
  /-- `ε > 0`. -/
  ε_pos : 0 < ε
  /-- **The arithmetic constant bound replacing the analytic upper density.** -/
  l30C_ge_one : 1 ≤ C
  /-- **The arithmetic constant bound needed by the GRH global lower bound.**
  The unconditional paper-scale global lower bound is proved at `1/8`; any
  `B ≤ 1/8` inherits it. -/
  l30B_le_eighth : B ≤ 1 / 8

namespace Wave26L30Counts

variable (S : Wave26L30Counts)

/-- **The derived sharp global odd upper density.**

This is not a field: it follows from
`paperScaleSmoothUpperSharp_one_unconditional` at `S.growth`, `S.ε_pos` and
from `S.l30C_ge_one`, together with monotonicity in the constant. -/
theorem sharpUpper :
    GlobalOddUpperDensitySharp S.C S.p S.ε :=
  globalOddUpperDensitySharp_of_one_le S.growth S.ε_pos S.l30C_ge_one

/-- **The derived global odd lower bound**, eventual at the paper scale.

This is the GRH statement `eventually_younisOddGlobalLower_paper_of_le` at the
constant `S.B ≤ 1/8`, rewritten along `S.err_eq`.  It is the only place where
the line hypothesis enters the L30 record. -/
theorem globalLower (line : DirichletLZerosOnLine) :
    EventuallyYounisOddGlobalLower S.B S.p (paperT S.p) S.err := by
  have h := eventually_younisOddGlobalLower_paper_of_le line S.p S.growth
    S.ε_pos S.l30B_le_eighth
  simpa only [S.err_eq] using h

/-- The relative error is at least `-1`, derived from `ε > 0` and `err = ε`. -/
theorem err_ge_neg_one (n : ℕ) : -1 ≤ S.err n := by
  rw [S.err_eq]
  dsimp [paperError]
  linarith [S.ε_pos]

/-- The prime is eventually at least two, derived from the density growth. -/
theorem eventually_p_ge_two : ∀ᶠ n in atTop, 2 ≤ S.p n :=
  S.growth.eventually_sixteen.mono fun _ hn => by linarith

/-- The remaining sharp central interval-count field. -/
theorem l30SharpCentral :
    YounisOddPaperSharpIntervalCount S.c S.p S.ε :=
  S.short_interval

/-- **The pointwise binomial-free wave-14 counts.**

The eventual sharp upper density and the eventual GRH global lower bound are
made pointwise by shifting `p` by a common tail threshold; the LPP superset is
the canonical multiples family.  This is exactly the construction of
`EventuallyL30Counts.toWave14L30CountsNoBinomial`, with the upper density
supplied by `S.sharpUpper` instead of a field. -/
noncomputable def toWave14L30CountsNoBinomial (line : DirichletLZerosOnLine) :
    Wave14L30CountsNoBinomial := by
  classical
  have hglobE : EventuallyYounisOddGlobalLower S.B S.p (paperT S.p)
      (paperError S.ε) := by
    simpa only [S.err_eq] using S.globalLower line
  have hp2 : ∀ᶠ n in atTop, 2 ≤ S.p n :=
    S.growth.eventually_sixteen.mono fun _ hn => by linarith
  let h := hp2.and (S.short_interval.and (S.sharpUpper.and hglobE))
  let N := eventuallyShift h
  let P : ℕ → ℝ := fun n => S.p (n + N)
  let E : ℕ → ℝ := paperError S.ε
  have hspec : ∀ n,
      (2 ≤ S.p (n + N)) ∧ (-1 ≤ S.ε) ∧
        (S.c * ((centralOrderInterval S.p (n + N)).card : ℝ) *
            Real.exp (-(paperDensityU S.p S.ε (n + N) *
              Real.log (paperDensityU S.p S.ε (n + N)))) ≤
          centralOddSmoothCount S.p (paperT S.p) (paperError S.ε) (n + N)) ∧
        (globalOddSmoothCount S.p (paperT S.p) (paperError S.ε) (n + N) /
            S.p (n + N) ^ 2 ≤
          S.C * Real.exp (-(paperDensityU S.p S.ε (n + N) *
            Real.log (paperDensityU S.p S.ε (n + N))))) ∧
        (S.B * S.p (n + N) ^ 2 *
            Real.exp (-(1 + S.ε) * paperT S.p (n + N)) ≤
          globalOddSmoothCount S.p (paperT S.p) (paperError S.ε) (n + N)) := by
    intro n
    have h' := eventuallyShift_spec h n
    exact ⟨h'.1, by linarith [S.ε_pos], h'.2.1, h'.2.2.1, h'.2.2.2⟩
  refine
    { p := P
      err := E
      ε := S.ε
      err_eq := rfl
      p_ge_two := fun n => (hspec n).1
      err_ge_neg_one := fun n => (hspec n).2.1
      fibreModels := fun n m => lppModelMultiples P n m
      A := S.A
      B := S.B
      c := S.c
      C := S.C
      A_pos := S.A_pos
      B_pos := S.B_pos
      AB_ge_four := S.AB_ge_four
      AC_le := S.AC_le
      short_interval := Filter.Eventually.of_forall fun n => (hspec n).2.2.1
      global_upper := Filter.Eventually.of_forall fun n => (hspec n).2.2.2.1
      global_lower := fun n => (hspec n).2.2.2.2
      lpp_superset := fun n m _ => subset_rfl }

/-- **The transported counts carry the derived sharp upper density.**  This is
a theorem about the transported record, not an assumed field. -/
theorem toWave14L30CountsNoBinomial_global_upper
    (line : DirichletLZerosOnLine) :
    GlobalOddUpperDensitySharp (S.toWave14L30CountsNoBinomial line).C
      (S.toWave14L30CountsNoBinomial line).p
      (S.toWave14L30CountsNoBinomial line).ε :=
  (S.toWave14L30CountsNoBinomial line).global_upper

/-- The transported counts keep the upper-density constant and the paper
error.  (The prime sequence is shifted by the eventual-to-pointwise adapter.) -/
theorem toWave14L30CountsNoBinomial_params (line : DirichletLZerosOnLine) :
    (S.toWave14L30CountsNoBinomial line).C = S.C ∧
      (S.toWave14L30CountsNoBinomial line).ε = S.ε :=
  ⟨rfl, rfl⟩

/-- The transport leaves the upper-density constant unchanged. -/
theorem toWave14L30CountsNoBinomial_C (line : DirichletLZerosOnLine) :
    (S.toWave14L30CountsNoBinomial line).C = S.C := rfl

/-- The transport leaves the paper error unchanged. -/
theorem toWave14L30CountsNoBinomial_ε (line : DirichletLZerosOnLine) :
    (S.toWave14L30CountsNoBinomial line).ε = S.ε := rfl

/-- **The conditional wave-25 counts**, given an explicit binomial count on the
original sequence.  The binomial count is not derivable from the global lower
bound, so this direction genuinely needs it; it is provided to show that the
Wave-26 record sits below the Wave-25 record in the hypothesis order. -/
noncomputable def toWave25L30Counts (line : DirichletLZerosOnLine)
    (hbin : GlobalOddBinomialCount S.B S.p (paperT S.p) S.err) :
    Wave25L30Counts := by
  classical
  have hglobE : EventuallyYounisOddGlobalLower S.B S.p (paperT S.p)
      (paperError S.ε) := by
    simpa only [S.err_eq] using S.globalLower line
  have hp2 : ∀ᶠ n in atTop, 2 ≤ S.p n :=
    S.growth.eventually_sixteen.mono fun _ hn => by linarith
  let h := hp2.and (S.short_interval.and (S.sharpUpper.and hglobE))
  let N := eventuallyShift h
  let P : ℕ → ℝ := fun n => S.p (n + N)
  let E : ℕ → ℝ := paperError S.ε
  have hspec : ∀ n,
      (2 ≤ S.p (n + N)) ∧ (-1 ≤ S.ε) ∧
        (S.c * ((centralOrderInterval S.p (n + N)).card : ℝ) *
            Real.exp (-(paperDensityU S.p S.ε (n + N) *
              Real.log (paperDensityU S.p S.ε (n + N)))) ≤
          centralOddSmoothCount S.p (paperT S.p) (paperError S.ε) (n + N)) ∧
        (globalOddSmoothCount S.p (paperT S.p) (paperError S.ε) (n + N) /
            S.p (n + N) ^ 2 ≤
          S.C * Real.exp (-(paperDensityU S.p S.ε (n + N) *
            Real.log (paperDensityU S.p S.ε (n + N))))) ∧
        (S.B * S.p (n + N) ^ 2 *
            Real.exp (-(1 + S.ε) * paperT S.p (n + N)) ≤
          globalOddSmoothCount S.p (paperT S.p) (paperError S.ε) (n + N)) := by
    intro n
    have h' := eventuallyShift_spec h n
    exact ⟨h'.1, by linarith [S.ε_pos], h'.2.1, h'.2.2.1, h'.2.2.2⟩
  have hbinE : GlobalOddBinomialCount S.B S.p (paperT S.p)
      (paperError S.ε) := by
    simpa only [S.err_eq] using hbin
  have hPT : paperT P = fun m => paperT S.p (m + N) := by
    funext m
    simp only [P, paperT]
  have hbinP : GlobalOddBinomialCount S.B P (paperT P) E := by
    intro n
    rw [hPT]
    exact hbinE (n + N)
  have h16P : ∀ᶠ n in atTop, 16 ≤ P n := by
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 S.growth.eventually_sixteen
    exact Filter.eventually_atTop.2
      ⟨M, fun n hn => hM (n + N) (le_trans hn (Nat.le_add_right n N))⟩
  have hgrowthP : PaperDensityGrowth P :=
    ⟨h16P, by
      simpa only [P, Function.comp_def] using
        S.growth.tendsto_log.comp (tendsto_add_atTop_nat N)⟩
  exact
    { p := P
      err := E
      ε := S.ε
      err_eq := rfl
      p_ge_two := fun n => (hspec n).1
      err_ge_neg_one := fun n => (hspec n).2.1
      fibreModels := fun n m => lppModelMultiples P n m
      A := S.A
      B := S.B
      c := S.c
      C := S.C
      A_pos := S.A_pos
      B_pos := S.B_pos
      AB_ge_four := S.AB_ge_four
      AC_le := S.AC_le
      short_interval := Filter.Eventually.of_forall fun n => (hspec n).2.2.1
      global_binomial := hbinP
      lpp_superset := fun n m _ => subset_rfl
      growth := hgrowthP
      ε_pos := S.ε_pos
      l30C_ge_one := S.l30C_ge_one }

end Wave26L30Counts

/-! ## The Wave-26 L30 inputs -/

/-- **The Wave-26 L30 replacement.**  The counts are `Wave26L30Counts`; the
Cantor/H.5 cost data and the H.3 failure data are unchanged. -/
structure Wave26L30Inputs where
  /-- The sharp central count with both density fields derived. -/
  counts : Wave26L30Counts
  /-- The Cantor/H.5 cost and correctness data. -/
  cantor : CantorCostInputs
  /-- The H.3 failure data, including the useful-prime split bound. -/
  failure : FailureData

namespace Wave26L30Inputs

variable (I : Wave26L30Inputs)

/-- **The binomial-free wave-14 L30 inputs from the wave-26 inputs.**  The
sharp upper density and the GRH global lower bound are derived; the Cantor and
failure data are unchanged. -/
noncomputable def toWave14L30InputsNoBinomial (line : DirichletLZerosOnLine) :
    Wave14L30InputsNoBinomial where
  counts := I.counts.toWave14L30CountsNoBinomial line
  cantor := I.cantor
  failure := I.failure

/-- The wave-13 L30 bundle, obtained by composing with the binomial-free
wave-14 reduction. -/
noncomputable def toWave13L30Inputs (line : DirichletLZerosOnLine) :
    Wave13L30Inputs :=
  (I.toWave14L30InputsNoBinomial line).toWave13L30Inputs

/-- **The conditional wave-25 L30 inputs**, given an explicit binomial
count.  The Wave-25 record still stores the binomial count; the Wave-26 record
does not, so this direction requires it as an extra hypothesis. -/
noncomputable def toWave25L30Inputs (line : DirichletLZerosOnLine)
    (hbin : GlobalOddBinomialCount I.counts.B I.counts.p
      (paperT I.counts.p) I.counts.err) :
    Wave25L30Inputs where
  counts := I.counts.toWave25L30Counts line hbin
  cantor := I.cantor
  failure := I.failure

/-- The L30 ledger leaf: the actual H.3 failure probability. -/
noncomputable def toSubexpLeaf : SubexpLeaf :=
  I.failure.toSubexpLeaf

/-- **The L30 loss is the actual H.3 failure probability.** -/
theorem loss_eq (n : ℕ) : I.toSubexpLeaf.loss n = I.failure.failure n := rfl

/-- The transport leaves the loss unchanged. -/
theorem toWave14L30InputsNoBinomial_loss_eq (line : DirichletLZerosOnLine)
    (n : ℕ) :
    (I.toWave14L30InputsNoBinomial line).toSubexpLeaf.loss n =
      I.failure.failure n := rfl

/-- The conditional wave-25 transport leaves the loss unchanged as well. -/
theorem toWave25L30Inputs_loss_eq (line : DirichletLZerosOnLine)
    (hbin : GlobalOddBinomialCount I.counts.B I.counts.p
      (paperT I.counts.p) I.counts.err) (n : ℕ) :
    (I.toWave25L30Inputs line hbin).toWave14L30Inputs.toSubexpLeaf.loss n =
      I.failure.failure n := rfl

/-- The derived sharp upper density carried by the wave-26 inputs. -/
theorem sharpUpper :
    GlobalOddUpperDensitySharp I.counts.C I.counts.p I.counts.ε :=
  I.counts.sharpUpper

/-- The derived eventual global lower bound carried by the wave-26 inputs. -/
theorem globalLower (line : DirichletLZerosOnLine) :
    EventuallyYounisOddGlobalLower I.counts.B I.counts.p
      (paperT I.counts.p) I.counts.err :=
  I.counts.globalLower line

end Wave26L30Inputs

/-! ## The Wave-26 ledger -/

/-- **The wave-26 ledger.**  The L30 slot is the actual H.3 failure leaf of the
wave-26 inputs (the ledger never reads the counting fields); every other leaf is
the same as in the wave-24/25 ledger. -/
noncomputable def wave26Slots
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : ConcreteLeafResidual) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave26L30Inputs) (l34 : L34ChebotarevSidesInputs)
    (p1 : SubexpPrepassInput) : C5LossSlots :=
  fullyDischargedSlots l18_4 l19.toL19FullCertificate
    (wave14L20_2Leaf l20_2) l20_4.toSubexpLeaf
    (wave14L21_2Leaf (wave17InputsOfResidual l21).toL21_2LeafData)
    (wave15L27Leaf l27_data l27_finish) l30.toSubexpLeaf
    (wave15L34Leaf l34) (wave15L4Leaf 9 3 wave24_l4N_odd wave24_l4Bits_budget)
    (wave14P1Leaf p1)

/-- **The wave-26 ledger is the wave-25 ledger at the conditional transport.**
Both reduce to the same fully discharged ledger at the same failure leaf. -/
theorem wave25Slots_eq_wave26Slots
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21 : ConcreteLeafResidual) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave26L30Inputs) (l34 : L34ChebotarevSidesInputs)
    (p1 : SubexpPrepassInput) (line : DirichletLZerosOnLine)
    (hbin : GlobalOddBinomialCount l30.counts.B l30.counts.p
      (paperT l30.counts.p) l30.counts.err) :
    wave25Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
        (l30.toWave25L30Inputs line hbin) l34 p1 =
      wave26Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish l30 l34 p1 := by
  simp only [wave25Slots, wave26Slots, wave24Slots, wave17Slots, wave15Slots,
    Wave26L30Inputs.toWave25L30Inputs, Wave25L30Inputs.toWave14L30Inputs,
    Wave25L30Counts.toWave14L30Counts, Wave14L30Inputs.toSubexpLeaf,
    Wave26L30Inputs.toSubexpLeaf]

/-! ## The E-generic residual record -/

/-- **The Wave-26 E-generic residual record.**

This is exactly `PaperResidualFor25` with

```
l30 : Wave25L30Inputs
```

replaced by

```
l30 : Wave26L30Inputs,
```

so the L30 leaf carries neither `global_upper` nor `global_binomial` (nor a
`global_lower` field).  All E-specific fields, the concrete C5 data and the
ledger domination are unchanged; the ledger is `wave26Slots`. -/
structure PaperResidualFor26
    (E : ∀ n, 3 ≤ n → HardEpochData n) (D : ℝ) where
  /-- The full L18.4 certificate. -/
  l18_4 : L18_4Certificate
  /-- The full L19 certificate, with the L19.6 thin slot built from lattice
  data. -/
  l19 : Wave15L19Inputs
  /-- L20.2: interior concentration from the paper-mass saddle source. -/
  l20_2 : SaddleConcentrationSource
  /-- L20.4: the sourced child-root-conditioned two-point data. -/
  l20_4 : Wave14L20_4Source
  /-- **The whole L21.2 analytic input**: the zeta side and the literal central
  short-interval smooth count. -/
  l21 : ConcreteLeafResidual
  /-- The parent L27.1 ECM data. -/
  l27_data : L27_1Inputs
  /-- The L27.1 stage-one finish data. -/
  l27_finish : L27StageOneFinishInputs l27_data
  /-- **L30 with both density fields derived**, leaving only the sharp central
  count, the GRH lower bound, the density growth and the H.3 failure data. -/
  l30 : Wave26L30Inputs
  /-- L34: the explicit Chebotarev-side counting inputs. -/
  l34 : L34ChebotarevSidesInputs
  /-- P1: the explicit `exp (o(H))`-cost prepass. -/
  p1 : SubexpPrepassInput
  /-- C1: the public congruence check (L1). -/
  c1 : C1Inputs E
  /-- C2: conditional hidden-sign uniformity (L2–L5, including L4). -/
  c2 : C2Inputs E
  /-- C3: the ideal/actual total-variation budget (L6–L10). -/
  c3 : C3Inputs E
  /-- C4: the expected public-work budget (L11–L16). -/
  c4 : C4Inputs E D
  /-- The concrete epoch family underlying the C5 certificate. -/
  concrete : ∀ n, 3 ≤ n → ConcreteEpochData n
  /-- Adapter: the ambient epoch is the concrete family's `toHardEpochData`. -/
  concrete_eq : ∀ n (hN : 3 ≤ n), E n hN = (concrete n hN).toHardEpochData
  /-- **The C5 data assembled by `c5FullOfCount`.** -/
  c5Data : Wave15C5Data concrete
  /-- Adapter: the concrete C5 loss is dominated by the wave-26 ledger. -/
  loss_le : ∀ n (hN : 3 ≤ n),
    c5TotalLoss hN (concrete n hN) (c5Data.toC5 n hN) ≤
      (wave26Slots l18_4 l19 l20_2 l20_4 l21 l27_data l27_finish
        l30 l34 p1).total n

namespace PaperResidualFor26

variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **The fully discharged inputs directly from the Wave-26 record.**

No binomial count and no sharp-upper field is needed: the fully discharged
ledger only reads the L30 failure leaf, so the counting transport is bypassed.
This is the unconditional route used by the endpoint. -/
noncomputable def toFullyDischargedInputs (I : PaperResidualFor26 E D) :
    FullyDischargedInputs E D where
  l18_4 := I.l18_4
  l19 := I.l19.toL19FullCertificate
  l20_2 := wave14L20_2Leaf I.l20_2
  l20_4 := I.l20_4.toSubexpLeaf
  l21_2 := wave14L21_2Leaf (wave17InputsOfResidual I.l21).toL21_2LeafData
  l27_1 := wave15L27Leaf I.l27_data I.l27_finish
  l30 := I.l30.toSubexpLeaf
  l34 := wave15L34Leaf I.l34
  l4_l25_l36 := wave15L4Leaf 9 3 wave24_l4N_odd wave24_l4Bits_budget
  p1 := wave14P1Leaf I.p1
  c1 := I.c1
  c2 := I.c2
  c3 := I.c3
  c4 := I.c4
  concrete := I.concrete
  concrete_eq := I.concrete_eq
  c5 := I.c5Data.toC5
  loss_le := by
    intro n hN
    simpa only [wave26Slots] using I.loss_le n hN

/-- **`PaperResidualFor26 E D → PaperResidualFor25 E D`, conditionally on an
explicit binomial count for the L30 sequence.**  The Wave-25 record stores the
binomial count; the Wave-26 record does not, and the binomial count is not
derivable from the global lower bound, so the additional hypothesis is
necessary.  The loss is unchanged because `wave25Slots` and `wave26Slots`
differ only in the counting fields of the L30 leaf. -/
noncomputable def toPaperResidualFor25 (I : PaperResidualFor26 E D)
    (line : DirichletLZerosOnLine)
    (hbin : GlobalOddBinomialCount I.l30.counts.B I.l30.counts.p
      (paperT I.l30.counts.p) I.l30.counts.err) :
    PaperResidualFor25 E D where
  l18_4 := I.l18_4
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21 := I.l21
  l27_data := I.l27_data
  l27_finish := I.l27_finish
  l30 := I.l30.toWave25L30Inputs line hbin
  l34 := I.l34
  p1 := I.p1
  c1 := I.c1
  c2 := I.c2
  c3 := I.c3
  c4 := I.c4
  concrete := I.concrete
  concrete_eq := I.concrete_eq
  c5Data := I.c5Data
  loss_le := by
    intro n hN
    rw [wave25Slots_eq_wave26Slots I.l18_4 I.l19 I.l20_2 I.l20_4 I.l21
      I.l27_data I.l27_finish I.l30 I.l34 I.p1 line hbin]
    exact I.loss_le n hN

/-- The reduction keeps the L30 block. -/
theorem toPaperResidualFor25_l30 (I : PaperResidualFor26 E D)
    (line : DirichletLZerosOnLine)
    (hbin : GlobalOddBinomialCount I.l30.counts.B I.l30.counts.p
      (paperT I.l30.counts.p) I.l30.counts.err) :
    (I.toPaperResidualFor25 line hbin).l30 =
      I.l30.toWave25L30Inputs line hbin := rfl

/-- **The transported Wave-25 counts carry the derived sharp upper density.**
The upper density is a theorem for the Wave-26 record, not an assumed field. -/
theorem toPaperResidualFor25_l30_global_upper (I : PaperResidualFor26 E D)
    (line : DirichletLZerosOnLine)
    (hbin : GlobalOddBinomialCount I.l30.counts.B I.l30.counts.p
      (paperT I.l30.counts.p) I.l30.counts.err) :
    GlobalOddUpperDensitySharp
      (I.toPaperResidualFor25 line hbin).l30.toWave14L30Inputs.counts.C
      (I.toPaperResidualFor25 line hbin).l30.toWave14L30Inputs.counts.p
      (I.toPaperResidualFor25 line hbin).l30.toWave14L30Inputs.counts.ε :=
  (I.toPaperResidualFor25 line hbin).l30.toWave14L30Inputs.counts.global_upper

/-- The conditional transport keeps the L30 upper-density constant and paper
error.  (The prime sequence is shifted by the adapter.) -/
theorem toPaperResidualFor25_l30_params (I : PaperResidualFor26 E D)
    (line : DirichletLZerosOnLine)
    (hbin : GlobalOddBinomialCount I.l30.counts.B I.l30.counts.p
      (paperT I.l30.counts.p) I.l30.counts.err) :
    (I.toPaperResidualFor25 line hbin).l30.toWave14L30Inputs.counts.C =
        I.l30.counts.C ∧
      (I.toPaperResidualFor25 line hbin).l30.toWave14L30Inputs.counts.ε =
        I.l30.counts.ε :=
  ⟨rfl, rfl⟩

/-- The reduction is the identity on the L30 failure data (hence on the loss). -/
theorem toPaperResidualFor25_loss_eq (I : PaperResidualFor26 E D)
    (line : DirichletLZerosOnLine)
    (hbin : GlobalOddBinomialCount I.l30.counts.B I.l30.counts.p
      (paperT I.l30.counts.p) I.l30.counts.err) (n : ℕ) :
    (I.toPaperResidualFor25 line hbin).l30.toWave14L30Inputs.toSubexpLeaf.loss n =
      I.l30.failure.failure n := rfl

/-- The record is nonempty as a `FullyDischargedInputs`. -/
theorem nonempty_fullyDischargedInputs (I : PaperResidualFor26 E D) :
    Nonempty (FullyDischargedInputs E D) :=
  ⟨I.toFullyDischargedInputs⟩

/-- The reduction is the identity on every c1–c4 field. -/
theorem toPaperResidualFor25_c (I : PaperResidualFor26 E D)
    (line : DirichletLZerosOnLine)
    (hbin : GlobalOddBinomialCount I.l30.counts.B I.l30.counts.p
      (paperT I.l30.counts.p) I.l30.counts.err) :
    (I.toPaperResidualFor25 line hbin).c1 = I.c1 ∧
      (I.toPaperResidualFor25 line hbin).c2 = I.c2 ∧
      (I.toPaperResidualFor25 line hbin).c3 = I.c3 ∧
      (I.toPaperResidualFor25 line hbin).c4 = I.c4 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The reduction is the identity on the concrete family, its adapter and the
C5 data. -/
theorem toPaperResidualFor25_c5 (I : PaperResidualFor26 E D)
    (line : DirichletLZerosOnLine)
    (hbin : GlobalOddBinomialCount I.l30.counts.B I.l30.counts.p
      (paperT I.l30.counts.p) I.l30.counts.err) :
    (I.toPaperResidualFor25 line hbin).concrete = I.concrete ∧
      (I.toPaperResidualFor25 line hbin).concrete_eq = I.concrete_eq ∧
      (I.toPaperResidualFor25 line hbin).c5Data = I.c5Data :=
  ⟨rfl, rfl, rfl⟩

end PaperResidualFor26

/-- **The schedule-indexed form of the Wave-26 record**, at the exact
quantification of the endpoint. -/
abbrev PaperResidualFor26Schedule
    (E : ∀ _s n, 3 ≤ n → HardEpochData n) (D : ℝ)
    (s : BalancedRationalSchedule) :=
  PaperResidualFor26 (E s) D

/-! ## The E-generic endpoint -/

/-- **Wave-26 paper endpoint.**

Under the critical-line hypothesis for Dirichlet `L`-functions, there is one
universal serialized factoring algorithm such that, for **every** balanced-
schedule epoch family `E` which, at every valid ceiling, carries a
`PaperResidualFor26 (E s) D` record, the kernel-checked driver outputs a
permutation of `n.primeFactorsList` and has expected serialized bit cost
eventually at most `exp ((balancedEnvelopeInfimum + ε) * scale n)`, with
`balancedEnvelopeInfimum ∈ (1.9839824118071388228, 1.9839824118071388230)`.

The L30 leaf of the record has no `global_upper`, no `global_binomial` and no
`global_lower` field: the first two are derived, and the third is the GRH
density theorem.  The epoch family `E` is quantified inside the conclusion.
The proof transports each record by
`PaperResidualFor26.toFullyDischargedInputs` and applies
`serialized_assembled_balancedEnvelopeInfimum_from_fullyDischargedInputs`. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave26Inputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        PaperResidualFor26 (E s) D) →
      1.9839824118071388228 < balancedEnvelopeInfimum ∧
      balancedEnvelopeInfimum < 1.9839824118071388230 ∧
      (∀ n (hn : 2 ≤ n) bits,
        bits ∈ (outputBits k sound
          (balancedUniversalHard (fun s => epochLaw (E s)) (fun s => epochAttempt (E s)))
          n hn).support →
        ∃ xs, decodeFactors bits = some xs ∧ xs.Perm n.primeFactorsList) ∧
      ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
        mean (serializedFactor k sound
          (balancedUniversalHard (fun s => epochLaw (E s)) (fun s => epochAttempt (E s)))
          n hn) (fun out => (out.2 : ℝ≥0∞)) ≤
          ENNReal.ofReal (exp ((balancedEnvelopeInfimum + ε) * scale n)) := by
  obtain ⟨k, sound, hmain⟩ :=
    serialized_assembled_balancedEnvelopeInfimum_from_fullyDischargedInputs line
  exact ⟨k, sound, fun E hI => hmain E fun s D hvalid =>
    (hI s D hvalid).toFullyDischargedInputs⟩

/-! ## The GRH constructor -/

/-- **The Wave-26 counts from the GRH line and the arithmetic data.**  The only
analytic premise is the sharp central interval count `hshort`; the sharp upper
density is derived from `PaperDensityGrowth` and `1 ≤ C`, and the global lower
bound is the GRH theorem (used later, in `globalLower`). -/
noncomputable def ofPaperGRHWithB
    (p : ℕ → ℝ) (h : PaperDensityGrowth p)
    {ε B : ℝ} (hε : 0 < ε) (hB : 0 < B) (hBle : B ≤ 1 / 8)
    (A : ℝ) (hA : 0 < A) (hAB : 4 ≤ A * B)
    (c C : ℝ) (hAC : A * C ≤ c) (hC : 1 ≤ C)
    (hshort : YounisOddPaperSharpIntervalCount c p ε) :
    Wave26L30Counts where
  p := p
  err := paperError ε
  ε := ε
  err_eq := rfl
  A := A
  B := B
  c := c
  C := C
  A_pos := hA
  B_pos := hB
  AB_ge_four := hAB
  AC_le := hAC
  short_interval := hshort
  growth := h
  ε_pos := hε
  l30C_ge_one := hC
  l30B_le_eighth := hBle

/-- **The Wave-26 inputs from the GRH line and the arithmetic data.** -/
noncomputable def Wave26L30Inputs.ofPaperGRHWithB
    (p : ℕ → ℝ) (h : PaperDensityGrowth p)
    {ε B : ℝ} (hε : 0 < ε) (hB : 0 < B) (hBle : B ≤ 1 / 8)
    (A : ℝ) (hA : 0 < A) (hAB : 4 ≤ A * B)
    (c C : ℝ) (hAC : A * C ≤ c) (hC : 1 ≤ C)
    (hshort : YounisOddPaperSharpIntervalCount c p ε)
    (cantor : CantorCostInputs) (failure : FailureData) :
    Wave26L30Inputs where
  counts := Cogentic.RandomizedPaperEndpointWave26.ofPaperGRHWithB
    p h hε hB hBle A hA hAB c C hAC hC hshort
  cantor := cantor
  failure := failure

/-! ## Residual accounting -/

/-- The field names of the Wave-26 L30 counts.  None of `global_upper`,
`global_binomial` or `global_lower` is present. -/
def wave26L30CountsFieldNames : List String :=
  ["p", "err", "ε", "err_eq", "A", "B", "c", "C", "A_pos", "B_pos",
   "AB_ge_four", "AC_le", "short_interval", "growth", "ε_pos",
   "l30C_ge_one", "l30B_le_eighth"]

theorem wave26L30CountsFieldNames_length :
    wave26L30CountsFieldNames.length = 17 := rfl

/-- **There is no analytic `global_upper` field in the Wave-26 counts.** -/
theorem wave26L30_no_globalUpper_field :
    wave26L30CountsFieldNames.all (fun s => decide (s ≠ "global_upper")) = true := by
  decide

/-- **There is no `global_binomial` field in the Wave-26 counts.** -/
theorem wave26L30_no_globalBinomial_field :
    wave26L30CountsFieldNames.all (fun s => decide (s ≠ "global_binomial")) = true := by
  decide

/-- **There is no `global_lower` field in the Wave-26 counts** either: it is the
GRH density theorem. -/
theorem wave26L30_no_globalLower_field :
    wave26L30CountsFieldNames.all (fun s => decide (s ≠ "global_lower")) = true := by
  decide

/-- **The residual L30 analytic list is exactly the sharp central count.** -/
def wave26RemainingL30FieldNames : List String :=
  ["short_interval"]

theorem wave26RemainingL30FieldNames_length :
    wave26RemainingL30FieldNames.length = 1 := rfl

/-- **The complete remaining L30 analytic input of the Wave-26 record.** -/
theorem wave26_l30_remaining (S : Wave26L30Counts) :
    YounisOddPaperSharpIntervalCount S.c S.p S.ε :=
  S.short_interval

/-- **The sharp upper density is not a residual field**: it is a theorem for
every record, with no line hypothesis. -/
theorem wave26_sharpUpper_derived (S : Wave26L30Counts) :
    GlobalOddUpperDensitySharp S.C S.p S.ε :=
  S.sharpUpper

/-- **The global lower bound is the GRH density theorem**, not a field. -/
theorem wave26_globalLower_derived (S : Wave26L30Counts)
    (line : DirichletLZerosOnLine) :
    EventuallyYounisOddGlobalLower S.B S.p (paperT S.p) S.err :=
  S.globalLower line

/-- **The residual L30 list of the E-generic record**, at the same
quantification as `wave24RemainingFieldNames`: the analytic L30 content is only
`short_interval`; `growth` is the density hypothesis, and the constants carry
the already-present arithmetic side conditions. -/
theorem wave26_l30_analytic_residual (S : Wave26L30Counts) :
    YounisOddPaperSharpIntervalCount S.c S.p S.ε ∧
      PaperDensityGrowth S.p ∧ 0 < S.ε ∧ 1 ≤ S.C ∧ S.B ≤ 1 / 8 :=
  ⟨S.short_interval, S.growth, S.ε_pos, S.l30C_ge_one, S.l30B_le_eighth⟩

/-! ## Axiom audit -/

#print axioms Wave26L30Counts.sharpUpper
#print axioms Wave26L30Counts.globalLower
#print axioms Wave26L30Counts.err_ge_neg_one
#print axioms Wave26L30Counts.eventually_p_ge_two
#print axioms Wave26L30Counts.l30SharpCentral
#print axioms Wave26L30Counts.toWave14L30CountsNoBinomial
#print axioms Wave26L30Counts.toWave14L30CountsNoBinomial_global_upper
#print axioms Wave26L30Counts.toWave14L30CountsNoBinomial_params
#print axioms Wave26L30Counts.toWave14L30CountsNoBinomial_C
#print axioms Wave26L30Counts.toWave14L30CountsNoBinomial_ε
#print axioms Wave26L30Counts.toWave25L30Counts
#print axioms Wave26L30Inputs.toWave14L30InputsNoBinomial
#print axioms Wave26L30Inputs.toWave13L30Inputs
#print axioms Wave26L30Inputs.toWave25L30Inputs
#print axioms Wave26L30Inputs.toSubexpLeaf
#print axioms Wave26L30Inputs.loss_eq
#print axioms Wave26L30Inputs.toWave14L30InputsNoBinomial_loss_eq
#print axioms Wave26L30Inputs.toWave25L30Inputs_loss_eq
#print axioms Wave26L30Inputs.sharpUpper
#print axioms Wave26L30Inputs.globalLower
#print axioms wave26Slots
#print axioms wave25Slots_eq_wave26Slots
#print axioms PaperResidualFor26.toFullyDischargedInputs
#print axioms PaperResidualFor26.toPaperResidualFor25
#print axioms PaperResidualFor26.toPaperResidualFor25_l30
#print axioms PaperResidualFor26.toPaperResidualFor25_l30_global_upper
#print axioms PaperResidualFor26.toPaperResidualFor25_l30_params
#print axioms PaperResidualFor26.toPaperResidualFor25_loss_eq
#print axioms PaperResidualFor26.nonempty_fullyDischargedInputs
#print axioms PaperResidualFor26.toPaperResidualFor25_c
#print axioms PaperResidualFor26.toPaperResidualFor25_c5
#print axioms PaperResidualFor26Schedule
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave26Inputs
#print axioms ofPaperGRHWithB
#print axioms Wave26L30Inputs.ofPaperGRHWithB
#print axioms wave26L30CountsFieldNames_length
#print axioms wave26L30_no_globalUpper_field
#print axioms wave26L30_no_globalBinomial_field
#print axioms wave26L30_no_globalLower_field
#print axioms wave26RemainingL30FieldNames_length
#print axioms wave26_l30_remaining
#print axioms wave26_sharpUpper_derived
#print axioms wave26_globalLower_derived
#print axioms wave26_l30_analytic_residual

end Cogentic.RandomizedPaperEndpointWave26
