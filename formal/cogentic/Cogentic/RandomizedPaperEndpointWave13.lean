import Cogentic.RandomizedPaperEndpointFullyDischarged
import Cogentic.RandomizedL4Bands
import Cogentic.RandomizedL27Waterhouse
import Cogentic.RandomizedL30Interval
import Cogentic.RandomizedL30Sharp
import Cogentic.RandomizedL30Sub
import Cogentic.RandomizedL34BelowOne
import Cogentic.RandomizedL34ClassicalStark
import Cogentic.RandomizedL34Sides

/-!
# Wave 13: the paper endpoint with the L4/L25/L36, L27.1, L30 and L34 leaves
reduced

`Cogentic.RandomizedPaperEndpointFullyDischarged.FullyDischargedInputs` still
takes four opaque analytic leaves besides L20.2, L20.4, L21.2 and P1:

* `l27_1 : RatedLeaf` (the Lenstra–Pomerance ECM leaf);
* `l30 : SubexpLeaf` (the genus-two partial factorer);
* `l34 : RatedLeaf` (effective Chebotarev character separation);
* `l4_l25_l36 : AlgebraicLeaf` (the quadratic class-group supply).

Waves 10–12 have since reduced each of those leaves to explicit records that
are already proved to imply the corresponding leaf:

* **L4/L25/L36** — `RandomizedL4Bands.realized_fullSplitBand` proves the
  maximal one-band split-prime realization unconditionally for odd `N`, using
  the Cox composition law and the ideal-squaring selection law.  We derive the
  algebraic defect from the empty unrealized-tuple set, so the zero loss is
  computed rather than assumed.
* **L27.1** — `RandomizedL27Waterhouse.L27WaterhouseInputs` contains the
  classical weighted Deuring/Waterhouse trace formula, the Siegel lower bound
  for Hurwitz class numbers, the model-domination hypothesis, the `j`-line
  stratification and the small-prime prepass.  Together with the parent
  `L27_1Inputs` (which supplies the Hasse bound, gcd-exit decomposition,
  stage-one success, curve budget and recursive-splitting multiplier) it proves
  `L27TraceClassInputs.toRatedLeaf`.
* **L30** — `RandomizedL30Sharp` and `RandomizedL30Interval` reduce the
  Younis/LPP count inputs to the sharp central interval count
  `YounisOddPaperSharpIntervalCount` and the sharp global odd upper density
  `GlobalOddUpperDensitySharp`, both at the true exponent `u log u`; the
  relative density is derived by `paperRelative_of_sharpUpper`.
  `RandomizedL30Younis` then supplies the LPP raw count and normalization.
  `FailureData` supplies the H.3 failure data, and
  `FailureData.toSubexpLeaf` is the ledger leaf.
* **L34** — `RandomizedL34BelowOne` gives the Dedekind strip/zero-free input,
  `RandomizedL34ClassicalStark` gives the classical Stark exceptional-zero
  lemma, and `RandomizedL34Dedekind`/`RandomizedL34Sides` give the Chebotarev
  range and one-sided error-slack inputs.  We assemble `L34SidesCore`, whose
  `ratedLeaf` is the L34 leaf.

The new record `Wave13Inputs` therefore replaces those four fields by

* `l4N`/`l4N_odd` and the proved `realized_fullSplitBand` data;
* `l27_data`/`l27_waterhouse`;
* `l30` (short-interval counts, LPP data and H.3 failure data);
* `l34` (Dedekind strip, classical Stark and Chebotarev data),

while keeping the two certificates, L20.2, L20.4, L21.2, P1, C1–C4, the W45
C5 certificate and the three concrete adapters.  The file proves

* `Wave13Inputs.toFullyDischargedInputs` : the fully discharged inputs;
* `Wave13Inputs.toFullyDischargedInputs_slots` : the ledger identity;
* `Wave13Inputs.toPaperEndpointInputs` : the paper endpoint inputs;
* `serialized_assembled_balancedEnvelopeInfimum_from_wave13Inputs` : the
  endpoint, obtained by composing with
  `RandomizedPaperEndpointFullyDischarged
  .serialized_assembled_balancedEnvelopeInfimum_from_fullyDischargedInputs`.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no loss, count,
mass or error is set to zero.
-/

namespace Cogentic.RandomizedPaperEndpointWave13

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
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27Analytic
open Cogentic.RandomizedL27Hurwitz
open Cogentic.RandomizedL27Waterhouse
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30Analytic
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30Sharp
open Cogentic.RandomizedL30SmoothDensity
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34BelowOne
open Cogentic.RandomizedL34ClassicalStark
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedL34HalfPlane
open Cogentic.RandomizedL34Sides
open Cogentic.RandomizedL34Stark
open Cogentic.RandomizedL4
open Cogentic.RandomizedL4Bands
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperEndpoint
open Cogentic.RandomizedPaperEndpointDischarged
open Cogentic.RandomizedPaperEndpointFullyDischarged
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Cogentic.RandomizedFormGroup
open Cogentic.RandomizedReducedFormSupply
open Filter Real
open scoped BigOperators ENNReal

set_option warn.classDefReducibility false

/-! ## L4/L25/L36: the proved split-band realization -/

/-- **The realized-tuple set of the maximal split band is empty.**  This is the
direct `realized_fullSplitBand` form: every principal-genus injective tuple of
split primes up to `√(2N)` is the leading coefficient of a reduced primitive
form of discriminant `-8N`. -/
theorem wave13L4_unrealized_empty (N : ℕ) (hN : Odd N) :
    unrealizedTuples (N := N) (fullSplitBand N) = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro t ht
  simp only [unrealizedTuples, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  obtain ⟨hgenus, hinj, hnot⟩ := ht
  exact hnot (realized_fullSplitBand N hN t hgenus hinj)

/-- The L4 realization theorem, re-exported for the wave record. -/
theorem wave13L4_realized (N : ℕ) (hN : Odd N) :
    ∀ (t : ∀ _i : Fin 1, {p : ℕ // p ∈ fullSplitBand N _i}),
      (∏ i, genusMap N (t i).1) = 1 →
      Function.Injective (fun i => (t i).1) →
        ∃ f : ℕ × ℤ × ℕ, f ∈ ReducedForms N ∧ f.1 = ∏ i, (t i).1 :=
  realized_fullSplitBand N hN

/-- The genuine algebraic defect of the maximal one-band family: the number of
realized principal-genus tuples that fail to lift to a reduced form.  It is
zero because `realized_fullSplitBand` proves the set empty. -/
noncomputable def wave13L4Loss (N : ℕ) : ℕ → ℝ :=
  fun _ => ((unrealizedTuples (N := N) (fullSplitBand N)).card : ℝ)

/-- The L4 defect is identically zero, derived from the split-band theorem. -/
theorem wave13L4Loss_zero (N : ℕ) (hN : Odd N) (n : ℕ) :
    wave13L4Loss N n = 0 := by
  unfold wave13L4Loss
  rw [wave13L4_unrealized_empty N hN]
  simp

/-- **The L4/L25/L36 leaf from the proved Cox+squaring+split-band data.**  The
zero deficit is the exactness of the supply bridge, not a discarded estimate. -/
noncomputable def wave13L4Leaf (N : ℕ) (hN : Odd N) : AlgebraicLeaf where
  loss := wave13L4Loss N
  loss_nonneg := fun n => (wave13L4Loss_zero N hN n).ge
  loss_zero := wave13L4Loss_zero N hN

/-! ## L27.1: the Waterhouse/Siegel inputs -/

/-- **The L27.1 leaf from the Waterhouse/Siegel inputs.**  The parent
`L27_1Inputs` supplies the Hasse bound, the three gcd-exit components, the
stage-one success bound, the curve budget and the recursive-splitting
multiplier; `L27WaterhouseInputs` supplies the weighted Deuring/Waterhouse
formula and the Siegel lower bound. -/
noncomputable def wave13L27Leaf (I : L27_1Inputs)
    (W : L27WaterhouseInputs I) : RatedLeaf :=
  W.toTraceClassInputs.toRatedLeaf I.hasse
    (gcdExitNonneg_of_bound I.gcd_exit)
    (gcdExitLeInv_of_bound I.gcd_exit)
    (gcdExitLeFailure_of_bound I.gcd_exit)
    I.stage_one I.curve_budget I.logFactor_subexp

/-- The Waterhouse field of the wave record. -/
theorem wave13L27_waterhouse (I : L27_1Inputs) (W : L27WaterhouseInputs I)
    (n : ℕ) :
    WaterhouseWeighted (I.p n) (W.p_prime n) W.hurwitz :=
  W.waterhouse n

/-- The Siegel field of the wave record. -/
theorem wave13L27_siegel (I : L27_1Inputs) (W : L27WaterhouseInputs I) :
    HurwitzSiegelLowerTrace I.p W.hurwitz W.c :=
  W.siegel_lower

/-! ## L30: the short-interval counts and the H.3 failure data -/

/-- The Younis/LPP count data at the paper scale.  The two Younis fields are
the sharp central interval count `YounisOddPaperSharpIntervalCount` and the
sharp global odd upper density `GlobalOddUpperDensitySharp`, both carrying the
true Dickman factor `exp (-(u log u))`; `paperRelative_of_sharpUpper` turns
them into the relative short-interval density consumed by
`YounisLPPInputs`.  The LPP raw count and normalization are kept explicit. -/
structure Wave13L30Counts where
  /-- The prime whose genus-two order is counted. -/
  p : ℕ → ℝ
  /-- The explicit `1 + o(1)` relative error. -/
  err : ℕ → ℝ
  /-- The constant paper error underlying the sharp density statements. -/
  ε : ℝ
  /-- The relative error is the constant paper error. -/
  err_eq : err = paperError ε
  /-- The prime is at least two. -/
  p_ge_two : ∀ n, 2 ≤ p n
  /-- The finite set of quintic models attached to each order. -/
  fibreModels : ℕ → ℕ → Finset ℕ
  /-- The polylogarithmic loss in the raw LPP count. -/
  Q : ℕ → ℝ
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
  exponent `u log u`. -/
  short_interval : YounisOddPaperSharpIntervalCount c p ε
  /-- **The sharp global odd smooth upper density** at `u log u`. -/
  global_upper : GlobalOddUpperDensitySharp C p ε
  /-- The global odd smooth lower bound. -/
  global_lower : YounisOddGlobalLower B p (paperT p) err
  /-- The LPP normalization. -/
  lpp_normalization : LPPNormalization p (paperT p) err Q
  /-- The raw LPP per-order model count. -/
  lpp_raw : LPPRawModelCount p (paperT p) err fibreModels Q

namespace Wave13L30Counts

/-- **The reduced Younis/LPP inputs.**  The relative short-interval density is
derived from the sharp interval count and the sharp global upper density by
`paperRelative_of_sharpUpper`; the sharp fields are eventual, so they are made
pointwise by shifting `p`, `fibreModels` and `Q` by a common tail threshold.
The paper error is the constant `paperError ε`. -/
noncomputable def toYounisLPPInputs (S : Wave13L30Counts) : YounisLPPInputs := by
  classical
  have hrel : EventuallyYounisOddSharpRelativeShortInterval S.A S.p S.ε :=
    paperRelative_of_sharpUpper S.A_pos.le S.AC_le S.short_interval S.global_upper
  let hAll : ∀ᶠ n in atTop,
      (S.c * ((centralOrderInterval S.p n).card : ℝ) *
          Real.exp (-(paperDensityU S.p S.ε n *
            Real.log (paperDensityU S.p S.ε n))) ≤
        centralOddSmoothCount S.p (paperT S.p) (paperError S.ε) n) ∧
      ((globalOddSmoothCount S.p (paperT S.p) (paperError S.ε) n / S.p n ^ 2 ≤
          S.C * Real.exp (-(paperDensityU S.p S.ε n *
            Real.log (paperDensityU S.p S.ε n)))) ∧
        (S.A * ((centralOrderInterval S.p n).card : ℝ) *
            (globalOddSmoothCount S.p (paperT S.p) (paperError S.ε) n /
              S.p n ^ 2) ≤
          centralOddSmoothCount S.p (paperT S.p) (paperError S.ε) n)) :=
    S.short_interval.and (S.global_upper.and hrel)
  let N := Classical.choose (Filter.eventually_atTop.1 hAll)
  have hspec : ∀ n,
      (S.c * ((centralOrderInterval S.p (n + N)).card : ℝ) *
          Real.exp (-(paperDensityU S.p S.ε (n + N) *
            Real.log (paperDensityU S.p S.ε (n + N)))) ≤
        centralOddSmoothCount S.p (paperT S.p) (paperError S.ε) (n + N)) ∧
      ((globalOddSmoothCount S.p (paperT S.p) (paperError S.ε) (n + N) /
          S.p (n + N) ^ 2 ≤
          S.C * Real.exp (-(paperDensityU S.p S.ε (n + N) *
            Real.log (paperDensityU S.p S.ε (n + N))))) ∧
        (S.A * ((centralOrderInterval S.p (n + N)).card : ℝ) *
            (globalOddSmoothCount S.p (paperT S.p) (paperError S.ε) (n + N) /
              S.p (n + N) ^ 2) ≤
          centralOddSmoothCount S.p (paperT S.p) (paperError S.ε) (n + N))) := by
    intro n
    have h := Classical.choose_spec (Filter.eventually_atTop.1 hAll) (n + N)
      (Nat.le_add_left N n)
    simpa only [hAll] using h
  let P : ℕ → ℝ := fun n => S.p (n + N)
  let T : ℕ → ℝ := fun n => paperT S.p (n + N)
  let E : ℕ → ℝ := paperError S.ε
  let F : ℕ → ℕ → Finset ℕ := fun n m => S.fibreModels (n + N) m
  let Q : ℕ → ℝ := fun n => S.Q (n + N)
  have hglob : YounisOddGlobalLower S.B P T E := by
    intro n
    have h := S.global_lower (n + N)
    rw [S.err_eq] at h
    exact h
  have hQ : LPPNormalization P T E Q := by
    intro n
    have h := S.lpp_normalization (n + N)
    rw [S.err_eq] at h
    simpa only [LPPNormalization, P, T, E, Q, paperError] using h
  have hraw : LPPRawModelCount P T E F Q := by
    intro n m hm
    have hm' : m ∈ centralSmoothOrders S.p (paperT S.p) S.err (n + N) := by
      simpa only [centralSmoothOrders, centralOrderInterval, smoothCutoff,
        P, T, E, paperError, paperT, S.err_eq] using hm
    have h := S.lpp_raw (n + N) m hm'
    simpa only [LPPRawModelCount, P, T, E, F, Q] using h
  refine
    { p := P
      t := T
      err := E
      p_ge_two := fun n => S.p_ge_two (n + N)
      fibreModels := F
      Q := Q
      A := S.A
      B := S.B
      A_pos := S.A_pos
      B_pos := S.B_pos
      AB_ge_four := S.AB_ge_four
      younis_relative := ?_
      younis_global := hglob
      lpp_normalization := hQ
      lpp_raw := hraw }
  · intro n
    exact (hspec n).2.2

/-- The Younis short-interval count derived from the sharp counts (at the
common shifted index). -/
theorem younisShortIntervalCount (S : Wave13L30Counts) :
    YounisShortIntervalCount S.toYounisLPPInputs.p S.toYounisLPPInputs.t
      S.toYounisLPPInputs.err :=
  S.toYounisLPPInputs.younisShortIntervalCount

/-- The LPP per-order fibre count derived from the raw count and normalization
(at the common shifted index). -/
theorem lppOrderFibreCount (S : Wave13L30Counts) :
    LPPOrderFibreCount S.toYounisLPPInputs.p S.toYounisLPPInputs.t
      S.toYounisLPPInputs.err S.toYounisLPPInputs.fibreModels :=
  S.toYounisLPPInputs.lppOrderFibreCount

end Wave13L30Counts

/-- **The L30 replacement.**  The short-interval/LPP counts, the Cantor/H.5 cost
data, and the H.3 failure data.  The ledger leaf is `failure.toSubexpLeaf`; no
count, cost or failure probability is set to zero. -/
structure Wave13L30Inputs where
  /-- The Younis/LPP short-interval counts. -/
  counts : Wave13L30Counts
  /-- The Cantor/H.5 cost and correctness data. -/
  cantor : CantorCostInputs
  /-- The H.3 failure data, including the useful-prime split bound. -/
  failure : FailureData

namespace Wave13L30Inputs

/-- The reduced `AnalyticInputs`, with both counting fields discharged. -/
noncomputable def toAnalyticInputs (I : Wave13L30Inputs) : AnalyticInputs :=
  I.counts.toYounisLPPInputs.toAnalyticInputs I.cantor

/-- The reduced `L30Sub.PaperInputs`. -/
noncomputable def toPaperInputs (I : Wave13L30Inputs) : PaperInputs :=
  I.toAnalyticInputs.toPaperInputs

/-- The L30 ledger leaf. -/
noncomputable def toSubexpLeaf (I : Wave13L30Inputs) : SubexpLeaf :=
  I.failure.toSubexpLeaf

/-- The Younis short-interval count carried by the record (at the common
shifted index). -/
theorem younisShortIntervalCount (I : Wave13L30Inputs) :
    YounisShortIntervalCount I.counts.toYounisLPPInputs.p
      I.counts.toYounisLPPInputs.t I.counts.toYounisLPPInputs.err :=
  I.counts.younisShortIntervalCount

/-- The LPP per-order fibre count carried by the record (at the common shifted
index). -/
theorem lppOrderFibreCount (I : Wave13L30Inputs) :
    LPPOrderFibreCount I.counts.toYounisLPPInputs.p
      I.counts.toYounisLPPInputs.t I.counts.toYounisLPPInputs.err
      I.counts.toYounisLPPInputs.fibreModels :=
  I.counts.lppOrderFibreCount

end Wave13L30Inputs

/-- The L30 leaf used by the wave ledger. -/
noncomputable def wave13L30Leaf (I : Wave13L30Inputs) : SubexpLeaf :=
  I.toSubexpLeaf

/-! ## L34: the Dedekind strip, classical Stark and Chebotarev inputs -/

/-- **The L34 replacement.**  This is `L34SidesCore` with the bundled
`DedekindSidesInputs` replaced by its four explicit pieces:

* the Dedekind strip/zero-free input `DedekindZeroFreeInput`;
* the classical Stark exceptional-zero lemma
  `StarkClassicalExceptionalZero ... (1/4)`;
* the Lagarias–Odlyzko range `ChebotarevRangeInput`;
* the one-sided Chebotarev error slack `ChebotarevErrorSlack`.

All remaining fields (probe budget, mask compression, bracket, tree/inert
bookkeeping, etc.) are copied from `L34SidesCore`. -/
structure Wave13L34Inputs where
  /-- The Chebotarev cutoff `x`. -/
  x : ℕ → ℝ
  /-- The absolute degree of `E = K(√γ)`. -/
  degree : ℕ → ℝ
  /-- `log |Δ_E|`. -/
  discLog : ℕ → ℝ
  /-- The factorial factor. -/
  F : ℕ → ℝ
  /-- The polynomial input parameter `T`. -/
  T : ℕ → ℝ
  /-- The class-group logarithm `h*`. -/
  hstar : ℕ → ℝ
  /-- The compressed bit length `m = h* + 7`. -/
  m : ℕ → ℝ
  /-- The number of probes `R`. -/
  R : ℕ → ℕ
  /-- The number of nonrational classes. -/
  classCount : ℕ → ℝ
  /-- The per-trial detection probability. -/
  pTrial : ℕ → ℝ
  /-- The possible exceptional real zero `β₀`. -/
  beta0 : ℕ → ℝ
  /-- The real part of a generic zero of `ζ_E`. -/
  zeroRealPart : ℕ → ℝ
  /-- A cumulative Chebotarev count. -/
  count : ℕ → ℝ
  /-- The cumulative inert count. -/
  inertCount : ℕ → ℝ
  /-- The degree-one inert count. -/
  degreeOneInert : ℕ → ℝ
  /-- `Li x`. -/
  liX : ℕ → ℝ
  /-- `Li x^{β₀}`. -/
  liBeta0 : ℕ → ℝ
  /-- The range constant. -/
  K : ℝ
  /-- The constant `C` in the effective error. -/
  C : ℝ
  /-- The constant `c` in the effective error. -/
  cZ : ℝ
  /-- The zero-free-region constant `c_z`. -/
  cz : ℝ
  /-- The bracket constant. -/
  cbr : ℝ
  /-- The per-ideal selection constant. -/
  csel : ℝ
  /-- The polynomial constant in `h* ≤ Ch T³`. -/
  Ch : ℝ
  /-- The cutoff is positive. -/
  x_pos : ∀ n, 0 < x n
  /-- The extension degree is positive. -/
  degree_pos : ∀ n, 0 < degree n
  /-- The discriminant logarithm is positive. -/
  discLog_pos : ∀ n, 0 < discLog n
  /-- The factorial factor is positive. -/
  F_pos : ∀ n, 0 < F n
  /-- The polynomial parameter is positive. -/
  T_pos : ∀ n, 0 < T n
  /-- The polynomial parameter is at least one. -/
  T_ge_one : ∀ n, 1 ≤ T n
  /-- There is at least one nonrational class. -/
  classCount_pos : ∀ n, 0 < classCount n
  /-- The per-trial probability is nonnegative. -/
  pTrial_nonneg : ∀ n, 0 ≤ pTrial n
  /-- The per-trial probability is at most one. -/
  pTrial_le_one : ∀ n, pTrial n ≤ 1
  /-- The actual failure probability of the probe stage. -/
  actualMiss : ℕ → ℝ
  /-- The actual failure probability is nonnegative. -/
  actualMiss_nonneg : ∀ n, 0 ≤ actualMiss n
  /-- The probe union bound. -/
  union_bound : ProbeMissUnionBound actualMiss pTrial classCount R
  /-- The degree is bounded by the polynomial parameter. -/
  degree_le_T : ∀ n, degree n ≤ T n
  /-- **The Dedekind strip/zero-free input.** -/
  zeroFree : DedekindZeroFreeInput beta0 zeroRealPart cz discLog
  /-- **The classical Stark exceptional-zero lemma.** -/
  starkClassical : StarkClassicalExceptionalZero beta0 F discLog (1 / 4)
  /-- **The Lagarias–Odlyzko range condition.** -/
  range : ChebotarevRangeInput K x degree discLog
  /-- **The one-sided Chebotarev error slack.** -/
  cheb : ChebotarevErrorSlack C cZ x degree count (mainOf liX liBeta0)
  /-- The inert count contains the counted nonidentity class. -/
  inert_ge_count : ∀ n, count n ≤ inertCount n
  /-- Stark's bound converted to the dyadic bracket. -/
  bracket : LogIntegralBracket cbr x F T liX liBeta0
  /-- The Chebotarev error is negligible against the bracket. -/
  error_negligible : ChebotarevErrorNegligible cbr x F T
    (lagariasOdlyzkoError C cZ x degree)
  /-- Discarding small / higher-degree ideals is negligible. -/
  degree_one_loss : DegreeOneLossNegligible cbr x degree F T
  /-- The degree-one reduction. -/
  degree_one_reduction : DegreeOneInertReduction inertCount degreeOneInert degree x
  /-- Probe selection at `1/(d x)` per eligible ideal. -/
  selection : ProbeSelectionLowerBound csel x degree degreeOneInert pTrial
  /-- The paper's budget `R = F T¹⁰`. -/
  budget : ProbeBudget R F T
  /-- Lemma E.2: at most `2^{h*}` nonrational classes. -/
  class_le : ClassCountBound classCount hstar
  /-- The polynomial bound `h* = O(T³)`. -/
  hstar_poly : ClassCountPolynomial Ch hstar T
  /-- The mask-compression bit budget. -/
  mask_bits : MaskCompressionBits hstar m
  /-- The probe constant beats the class-count entropy constant. -/
  constant_margin : Ch * Real.log 2 < csel * cbr / 4
  /-- The probe exponent `T³` eventually dominates the ledger scale. -/
  scale_cubic : ∀ᶠ n : ℕ in atTop,
    2 * scale n ≤ (csel * cbr / 4 - Ch * Real.log 2) * T n ^ 3

namespace Wave13L34Inputs

/-- Reassemble `L34SidesCore` by deriving the bundled
`DedekindSidesInputs` from the four explicit analytic pieces. -/
noncomputable def toL34SidesCore (S : Wave13L34Inputs) : L34SidesCore where
  x := S.x
  degree := S.degree
  discLog := S.discLog
  F := S.F
  T := S.T
  hstar := S.hstar
  m := S.m
  R := S.R
  classCount := S.classCount
  pTrial := S.pTrial
  beta0 := S.beta0
  zeroRealPart := S.zeroRealPart
  count := S.count
  inertCount := S.inertCount
  degreeOneInert := S.degreeOneInert
  liX := S.liX
  liBeta0 := S.liBeta0
  K := S.K
  C := S.C
  cZ := S.cZ
  cz := S.cz
  cbr := S.cbr
  csel := S.csel
  Ch := S.Ch
  x_pos := S.x_pos
  degree_pos := S.degree_pos
  discLog_pos := S.discLog_pos
  F_pos := S.F_pos
  T_pos := S.T_pos
  T_ge_one := S.T_ge_one
  classCount_pos := S.classCount_pos
  pTrial_nonneg := S.pTrial_nonneg
  pTrial_le_one := S.pTrial_le_one
  actualMiss := S.actualMiss
  actualMiss_nonneg := S.actualMiss_nonneg
  union_bound := S.union_bound
  degree_le_T := S.degree_le_T
  sides :=
    DedekindSidesInputs.ofSlack S.zeroFree
      S.starkClassical.toStarkClassicalInput.toStarkInput S.range S.cheb
  inert_ge_count := S.inert_ge_count
  bracket := S.bracket
  error_negligible := S.error_negligible
  degree_one_loss := S.degree_one_loss
  degree_one_reduction := S.degree_one_reduction
  selection := S.selection
  budget := S.budget
  class_le := S.class_le
  hstar_poly := S.hstar_poly
  mask_bits := S.mask_bits
  constant_margin := S.constant_margin
  scale_cubic := S.scale_cubic

/-- The L34 ledger leaf from the explicit Dedekind/Stark/Chebotarev inputs. -/
noncomputable def toRatedLeaf (S : Wave13L34Inputs) : RatedLeaf :=
  S.toL34SidesCore.ratedLeaf

/-- The Dedekind strip consequence of the zero-free input. -/
theorem strip (S : Wave13L34Inputs) :
    DedekindZeroFreeAboveBetaBelowOne S.beta0 S.zeroRealPart S.cz S.discLog :=
  dedekindZeroFreeAboveBetaBelowOne_of_aboveBeta S.zeroFree.above_beta

/-- The classical Stark gap carried by the record. -/
theorem stark (S : Wave13L34Inputs) :
    StarkGap S.beta0 S.F S.discLog :=
  S.starkClassical.toStarkClassicalInput.toStarkInput.gap

/-- The one-sided Chebotarev lower bound carried by the record. -/
theorem chebotarev (S : Wave13L34Inputs) :
    ChebotarevLowerBound S.count (mainOf S.liX S.liBeta0)
      (lagariasOdlyzkoError S.C S.cZ S.x S.degree) :=
  S.cheb.lower

end Wave13L34Inputs

/-- The L34 leaf used by the wave ledger. -/
noncomputable def wave13L34Leaf (S : Wave13L34Inputs) : RatedLeaf :=
  S.toRatedLeaf

/-! ## The wave-13 ledger -/

/-- The C5 ledger of the wave-13 inputs: the two certificates, the four
remaining opaque leaves, and the four leaves produced from the wave records. -/
noncomputable def wave13Slots
    (l18_4 : L18_4Certificate) (l19 : L19FullCertificate)
    (l20_2 : ConcentrationLeaf) (l20_4 : SubexpLeaf)
    (l21_2 : RatedLeaf) (l27_data : L27_1Inputs)
    (l27_waterhouse : L27WaterhouseInputs l27_data)
    (l30 : Wave13L30Inputs) (l34 : Wave13L34Inputs)
    (l4N : ℕ) (l4N_odd : Odd l4N) (p1 : P1Leaf) : C5LossSlots :=
  fullyDischargedSlots l18_4 l19 l20_2 l20_4 l21_2
    (wave13L27Leaf l27_data l27_waterhouse) (wave13L30Leaf l30)
    (wave13L34Leaf l34) (wave13L4Leaf l4N l4N_odd) p1

/-- **The wave-13 ledger, term by term.**  The total is the sum of the two
certificate losses, the four remaining paper losses, and the four produced
leaves.  In particular no slot is dropped or set to zero. -/
theorem wave13Slots_total_eq
    (l18_4 : L18_4Certificate) (l19 : L19FullCertificate)
    (l20_2 : ConcentrationLeaf) (l20_4 : SubexpLeaf)
    (l21_2 : RatedLeaf) (l27_data : L27_1Inputs)
    (l27_waterhouse : L27WaterhouseInputs l27_data)
    (l30 : Wave13L30Inputs) (l34 : Wave13L34Inputs)
    (l4N : ℕ) (l4N_odd : Odd l4N) (p1 : P1Leaf) (n : ℕ) :
    (wave13Slots l18_4 l19 l20_2 l20_4 l21_2 l27_data l27_waterhouse
        l30 l34 l4N l4N_odd p1).total n =
      l18_4.toInputs.loss n + l19.toL19Inputs.poisson.loss n +
        l19.toL19Inputs.zeroMode.loss n + l19.toL19Inputs.thin.loss n +
        l20_2.loss n + l20_4.loss n + l21_2.loss n +
        (wave13L27Leaf l27_data l27_waterhouse).loss n +
        (wave13L30Leaf l30).loss n + (wave13L34Leaf l34).loss n +
        (wave13L4Leaf l4N l4N_odd).loss n + p1.loss n := by
  simpa only [wave13Slots] using
    fullyDischargedSlots_total_eq l18_4 l19 l20_2 l20_4 l21_2
      (wave13L27Leaf l27_data l27_waterhouse) (wave13L30Leaf l30)
      (wave13L34Leaf l34) (wave13L4Leaf l4N l4N_odd) p1 n

/-- **The wave-13 inputs.**  The four replaced leaves are explicit records; the
other fields are exactly those of `FullyDischargedInputs`. -/
structure Wave13Inputs
    (E : ∀ n, 3 ≤ n → HardEpochData n) (D : ℝ) where
  /-- The full L18.4 certificate. -/
  l18_4 : L18_4Certificate
  /-- The full L19 certificate. -/
  l19 : L19FullCertificate
  /-- L20.2: interior concentration. -/
  l20_2 : ConcentrationLeaf
  /-- L20.4: child-root-conditioned two-point bound. -/
  l20_4 : SubexpLeaf
  /-- L21.2: RH smooth numbers near integer centres. -/
  l21_2 : RatedLeaf
  /-- The odd modulus of the L4 split-band realization. -/
  l4N : ℕ
  /-- The L4 modulus is odd. -/
  l4N_odd : Odd l4N
  /-- The parent L27.1 ECM data. -/
  l27_data : L27_1Inputs
  /-- The Waterhouse/Siegel data proving the L27.1 Deuring input. -/
  l27_waterhouse : L27WaterhouseInputs l27_data
  /-- L30: the short-interval counts, LPP data and H.3 failure data. -/
  l30 : Wave13L30Inputs
  /-- L34: the Dedekind strip, classical Stark and Chebotarev data. -/
  l34 : Wave13L34Inputs
  /-- P1: the `exp (o(H))`-cost prepass. -/
  p1 : P1Leaf
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
  concrete_eq : ∀ n hN, E n hN = (concrete n hN).toHardEpochData
  /-- The W45 C5 certificate. -/
  c5 : ∀ n hN, @C5FullInputs n (concrete n hN) (sampleFintype hN (concrete n hN))
  /-- Adapter: the concrete C5 loss is dominated by the wave-13 ledger. -/
  loss_le : ∀ n hN,
    c5TotalLoss hN (concrete n hN) (c5 n hN) ≤
      (wave13Slots l18_4 l19 l20_2 l20_4 l21_2 l27_data l27_waterhouse
        l30 l34 l4N l4N_odd p1).total n

namespace Wave13Inputs

variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **The fully discharged inputs made from the wave records.**  The four
replaced leaves are the proved wave reductions; every other field is passed
through unchanged. -/
noncomputable def toFullyDischargedInputs (I : Wave13Inputs E D) :
    FullyDischargedInputs E D where
  l18_4 := I.l18_4
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21_2 := I.l21_2
  l27_1 := wave13L27Leaf I.l27_data I.l27_waterhouse
  l30 := wave13L30Leaf I.l30
  l34 := wave13L34Leaf I.l34
  l4_l25_l36 := wave13L4Leaf I.l4N I.l4N_odd
  p1 := I.p1
  c1 := I.c1
  c2 := I.c2
  c3 := I.c3
  c4 := I.c4
  concrete := I.concrete
  concrete_eq := I.concrete_eq
  c5 := I.c5
  loss_le := by
    intro n hN
    simpa only [wave13Slots] using I.loss_le n hN

/-- **The wave-13 ledger is the fully discharged ledger.** -/
theorem toFullyDischargedInputs_slots (I : Wave13Inputs E D) :
    I.toFullyDischargedInputs.toPaperAnalyticAssumptions.slots =
      wave13Slots I.l18_4 I.l19 I.l20_2 I.l20_4 I.l21_2 I.l27_data
        I.l27_waterhouse I.l30 I.l34 I.l4N I.l4N_odd I.p1 := by
  rw [FullyDischargedInputs.toPaperAnalyticAssumptions_slots]
  rfl

/-- **The paper endpoint inputs from the wave-13 inputs.** -/
noncomputable def toPaperEndpointInputs (I : Wave13Inputs E D) :
    PaperEndpointInputs E D :=
  I.toFullyDischargedInputs.toPaperEndpointInputs

/-- The paper record produced by the wave-13 inputs has the wave-13 ledger. -/
theorem toPaperEndpointInputs_paper_slots (I : Wave13Inputs E D) :
    I.toPaperEndpointInputs.paper.slots =
      wave13Slots I.l18_4 I.l19 I.l20_2 I.l20_4 I.l21_2 I.l27_data
        I.l27_waterhouse I.l30 I.l34 I.l4N I.l4N_odd I.p1 :=
  I.toFullyDischargedInputs_slots

end Wave13Inputs

/-! ## The endpoint -/

/-- **Wave-13 paper endpoint.**  Under the critical-line hypothesis for
Dirichlet L-functions, there is one universal serialized factoring algorithm
such that, for every balanced-schedule epoch family which, at every valid
ceiling, carries

* the full L18.4 certificate,
* the full L19 certificate,
* L20.2, L20.4, L21.2 and P1,
* the proved L4 split-band realization (Cox composition + ideal squaring),
* the L27 Waterhouse/Siegel data,
* the L30 short-interval counts and H.3 failure data,
* the L34 Dedekind strip, classical Stark and Chebotarev data,
* C1–C4, and
* the W45 C5 certificate,

the kernel-checked driver always outputs a permutation of `n.primeFactorsList`
and has expected serialized bit cost eventually at most
`exp ((balancedEnvelopeInfimum + ε) * scale n)`, where
`balancedEnvelopeInfimum ∈ (1.9839824118071388228, 1.9839824118071388230)`.

The proof is
`RandomizedPaperEndpointFullyDischarged
.serialized_assembled_balancedEnvelopeInfimum_from_fullyDischargedInputs`
applied to `Wave13Inputs.toFullyDischargedInputs`. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave13Inputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        Wave13Inputs (E s) D) →
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

/-! ## Axiom audit -/

#print axioms wave13L4_unrealized_empty
#print axioms wave13L4_realized
#print axioms wave13L4Loss
#print axioms wave13L4Loss_zero
#print axioms wave13L4Leaf
#print axioms wave13L27Leaf
#print axioms wave13L27_waterhouse
#print axioms wave13L27_siegel
#print axioms Wave13L30Counts.toYounisLPPInputs
#print axioms Wave13L30Counts.younisShortIntervalCount
#print axioms Wave13L30Counts.lppOrderFibreCount
#print axioms Wave13L30Inputs.toAnalyticInputs
#print axioms Wave13L30Inputs.toPaperInputs
#print axioms Wave13L30Inputs.toSubexpLeaf
#print axioms Wave13L30Inputs.younisShortIntervalCount
#print axioms Wave13L30Inputs.lppOrderFibreCount
#print axioms wave13L30Leaf
#print axioms Wave13L34Inputs.toL34SidesCore
#print axioms Wave13L34Inputs.toRatedLeaf
#print axioms Wave13L34Inputs.strip
#print axioms Wave13L34Inputs.stark
#print axioms Wave13L34Inputs.chebotarev
#print axioms wave13L34Leaf
#print axioms wave13Slots
#print axioms wave13Slots_total_eq
#print axioms Wave13Inputs.toFullyDischargedInputs
#print axioms Wave13Inputs.toFullyDischargedInputs_slots
#print axioms Wave13Inputs.toPaperEndpointInputs
#print axioms Wave13Inputs.toPaperEndpointInputs_paper_slots
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave13Inputs

end Cogentic.RandomizedPaperEndpointWave13
