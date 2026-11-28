import Cogentic.RandomizedPaperEndpointWave16
import Cogentic.RandomizedL21_2LeafAssembly
import Cogentic.RandomizedL21_2ReferenceBound
import Cogentic.RandomizedL21_2StripBound

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-!
# Wave 17: an absolute L21.2 reference constant and a non-vacuous line constant

`Cogentic.RandomizedPaperEndpointWave16.Wave16L21_2Inputs` carries the
reference constant

```
wave16Kref X n = refConstant wave16Cper X n
               = (2 Cper + 2) (X n + 1) ((log X n)^2 + 1),
```

which grows like `X n (log X n)^2`.  Its `Ksum_le` field then asks a *single
real* `Kline` to dominate this growing quantity against
`(Kline / π) (1 + log (X n^3 / (2/3)))`, which grows only like
`Kline log X n`.  Hence the wave-16 L21.2 record is vacuously strong: for
unbounded `X` no finite `Kline` can satisfy it.

The present file repairs this.  The key point is that
`ReferencePerronBound X c K C` only asks for the error bound

```
‖twistedPrimeSum v t - refZetaSum v t (X n^3 + 1)‖
  ≤ K * (sqrt v * (log (2 v))^2),
```

and the unconditional truncated-Perron estimate, together with the improved
prime-power removal `‖twistedPrimeSum - vonMangoldtTwist‖ ≤ 2 sqrt v log v`,
gives this with a single absolute constant

```
wave17KrefConst = 2 * wave17Cper + 2.
```

The ingredients are proved here explicitly:

* `twistedPrimeSum_sub_vonMangoldt_le_sqrt` — the prime-power removal is only
  `2 sqrt v log v` (the non-prime terms form `ψ - θ`), not `v log v`;
* `referencePerronBound_absolute` — the absolute reference-Perron bound,
  using `v ≤ X n` on the L21.2 range and `v / (X^3 + 1) ≤ 1`.

The repaired record `Wave17L21_2Inputs` has

* `Kref := wave17KrefConst` (absolute);
* `Kcont := wave17KcontConst = (3 e / π) stripK` (the explicit off-pole strip
  constant of `RandomizedL21_2StripBound`);
* `Ktail : ℝ` (the given tail constant);
* `KlineRaw` (the genuine line-bound constant), and the *derived*
  `Kline = max KlineRaw (π (Kref + Kcont + Ktail))`.

Then `Ksum_le` is a theorem, and the line bound at the enlarged constant follows
from monotonicity of `VerticalLineBound`.  The reduction
`Wave17L21_2Inputs.toL21_2LeafData` builds the assembled record, so
`Kline` is now a genuine absolute number.

The file also constructs an inhabitant of the repaired record from the genuine
line bound, tail bound, local count and Fourier data
(`Wave17L21_2Inputs.ofRaw`), and proves that the reduction keeps the loss
definition unchanged (same `profile`, `c`, `p`; only the Perron constants are
replaced by the absolute ones).

`Wave17Inputs` is `Wave16Inputs` with the L21.2 field replaced by
`Wave17L21_2Inputs`; the file proves the endpoint

* `serialized_assembled_balancedEnvelopeInfimum_from_wave17Inputs`.

No `sorry`, `admit`, `axiom` or `native_decide` is used, and no loss, count,
mass or error is set to zero.
-/

namespace Cogentic.RandomizedPaperEndpointWave17

open Cogentic.Randomized
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedC5Algebra
open Cogentic.RandomizedC5Coupling
open Cogentic.RandomizedC5Full
open Cogentic.RandomizedC5GoodIff
open Cogentic.RandomizedC5HitMassFinish
open Cogentic.RandomizedConcreteHitMass
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedFactorSerialization
open Cogentic.RandomizedFieldPoolDescent
open Cogentic.RandomizedHiddenOutputLaw
open Cogentic.RandomizedInputDriver
open Cogentic.RandomizedL18_4
open Cogentic.RandomizedL18_4ThinFinish
open Cogentic.RandomizedL19Energy
open Cogentic.RandomizedL19Full
open Cogentic.RandomizedL19Poisson
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedL19Thin
open Cogentic.RandomizedL19ZeroMode
open Cogentic.RandomizedL20_2ConcentrationLeaf
open Cogentic.RandomizedL20_4LeafAssembly
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Abel
open Cogentic.RandomizedL21_2Density
open Cogentic.RandomizedL21_2Fourier
open Cogentic.RandomizedL21_2LeafAssembly
open Cogentic.RandomizedL21_2LineBound
open Cogentic.RandomizedL21_2PaperLocal
open Cogentic.RandomizedL21_2Perron
open Cogentic.RandomizedL21_2ReferenceBound
open Cogentic.RandomizedL21_2Remainder
open Cogentic.RandomizedL21_2Shift
open Cogentic.RandomizedL21_2StripBound
open Cogentic.RandomizedL21_2Sub
open Cogentic.RandomizedL21_2Tent
open Cogentic.RandomizedL21_2Vertical
open Cogentic.RandomizedL27_1
open Cogentic.RandomizedL27StageOneFinish
open Cogentic.RandomizedL30
open Cogentic.RandomizedL30GlobalLower
open Cogentic.RandomizedL30Interval
open Cogentic.RandomizedL30Raw
open Cogentic.RandomizedL30ShortInterval
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30Younis
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34ChebotarevSides
open Cogentic.RandomizedL34Sides
open Cogentic.RandomizedL4
open Cogentic.RandomizedL4BitBudget
open Cogentic.RandomizedL4Bands
open Cogentic.RandomizedL4Sub
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedP1Prepass
open Cogentic.RandomizedPaperEndpoint
open Cogentic.RandomizedPaperEndpointDischarged
open Cogentic.RandomizedPaperEndpointFullyDischarged
open Cogentic.RandomizedPaperEndpointWave13
open Cogentic.RandomizedPaperEndpointWave14
open Cogentic.RandomizedPaperEndpointWave15
open Cogentic.RandomizedPaperEndpointWave16
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedSerializedDriver
open Cogentic.RandomizedUniversalSchedule
open Filter Real Complex
open scoped BigOperators ENNReal
open ArithmeticFunction

set_option warn.classDefReducibility false

universe u

/-! ## The absolute reference constant -/

/-- The absolute truncated-Perron constant extracted from
`truncatedPerron_vonMangoldt_twist`. -/
noncomputable def wave17Cper : ℝ :=
  Classical.choose truncatedPerron_vonMangoldt_twist

theorem wave17Cper_pos : 0 < wave17Cper :=
  (Classical.choose_spec truncatedPerron_vonMangoldt_twist).1

/-- **The unconditional truncated-Perron estimate** at the extracted constant. -/
theorem wave17TruncatedPerronBound : TruncatedPerronErrorBound wave17Cper :=
  (Classical.choose_spec truncatedPerron_vonMangoldt_twist).2

/-- The absolute reference-Perron constant `2 Cper + 2`. -/
noncomputable def wave17KrefConst : ℝ := 2 * wave17Cper + 2

theorem wave17KrefConst_nonneg : 0 ≤ wave17KrefConst := by
  unfold wave17KrefConst
  have h := wave17Cper_pos
  linarith

/-- The explicit off-pole strip constant, i.e. the horizontal contour constant
`(3 e / π) stripK`. -/
noncomputable def wave17KcontConst : ℝ := (3 * Real.exp 1 / Real.pi) * stripK

theorem wave17KcontConst_nonneg : 0 ≤ wave17KcontConst := by
  unfold wave17KcontConst
  exact mul_nonneg (by positivity) stripK_nonneg

/-- **Improved prime-power removal.**  The prime-only twisted sum differs from
the full von Mangoldt twisted sum by at most `2 sqrt v log v`.  The non-prime
terms are exactly `ψ - θ`, bounded by `2 sqrt v log v`; the old crude bound
`v log v` is not needed for an absolute Perron constant. -/
theorem twistedPrimeSum_sub_vonMangoldt_le_sqrt {v t : ℝ} (hv : 2 ≤ v) :
    ‖twistedPrimeSum v t - vonMangoldtTwist v t‖ ≤
      2 * Real.sqrt v * Real.log v := by
  have hv0 : 0 < v := by linarith
  set N := ⌊v⌋₊ with hN
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
      ← Finset.insert_Icc_succ_left_eq_Icc (Nat.zero_le _)]
    simp
  have hvm : vonMangoldtTwist v t =
      ∑ n ∈ Finset.Icc 1 N,
        (Λ n : ℂ) * Complex.exp (-(t : ℂ) * I * (Real.log n : ℂ)) := by
    unfold vonMangoldtTwist
    rw [← hN]
  rw [htw, hvm, ← Finset.sum_sub_distrib]
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      ‖(if n.Prime then
          (Real.log n : ℂ) * Complex.exp (-(t : ℂ) * I * (Real.log n : ℂ))
        else 0) -
        (Λ n : ℂ) * Complex.exp (-(t : ℂ) * I * (Real.log n : ℂ))‖ ≤
        (if n.Prime then (0 : ℝ) else Λ n) := by
    intro n hn
    by_cases hp : n.Prime
    · rw [if_pos hp, if_pos hp, vonMangoldt_apply_prime hp, sub_self, norm_zero]
    · rw [if_neg hp, if_neg hp, zero_sub, norm_neg, norm_mul,
        norm_exp_twist, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg vonMangoldt_nonneg]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum hterm).trans ?_
  have hsum_eq : ∑ n ∈ Finset.Icc 1 N, (if n.Prime then (0 : ℝ) else Λ n) =
      ∑ n ∈ Finset.Icc 1 N with ¬ n.Prime, Λ n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime <;> simp [hp]
  rw [hsum_eq]
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext n
    simp [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hpsi : ∑ n ∈ Finset.Icc 1 N with ¬ n.Prime, Λ n =
      Chebyshev.psi v - Chebyshev.theta v := by
    rw [hIcc, hN, ← Chebyshev.psi_sub_theta_eq_sum_not_prime v]
  rw [hpsi]
  exact Chebyshev.psi_sub_theta_le (by linarith)

/-- **The absolute reference-Perron bound from `TruncatedPerronErrorBound C`.**
The error `C (v log²v / T + log v)` is at most `2 C sqrt v (log (2v))²`, and the
improved prime-power removal contributes another `2 sqrt v (log (2v))²`, so
`2 C + 2` is an absolute constant.  On the L21.2 range
`v ≤ smoothCutoff c X n ≤ X n = exp U`, the Perron term
`v (log v)^2 / (X^3 + 1)` is at most `(log v)^2`. -/
theorem referencePerronBound_of_errorBound_absolute {X : ℕ → ℝ} {c C Cper : ℝ}
    (hper : TruncatedPerronErrorBound C) (hC : 0 ≤ C)
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n) (hc : c ≤ 1) :
    ReferencePerronBound X c (fun _ => 2 * C + 2) Cper := by
  refine Eventually.of_forall ?_
  intro n v t hv hvB ht
  set U := bandLog X n with hUdef
  have hU3 : 3 ≤ U := hU n
  have hU0 : 0 < U := by linarith
  have hXpos : 0 < X n := lt_trans zero_lt_one (hX n)
  have hX1 : 1 ≤ X n := le_of_lt (hX n)
  have hlogU_le : Real.log U ≤ U := Real.log_le_self hU0.le
  have hlogU_nonneg : 0 ≤ Real.log U := Real.log_nonneg (by linarith)
  have hsq : U * Real.log U ≤ U ^ 2 := by nlinarith
  have hTle : paperRate X n ≤ U := by
    unfold paperRate
    calc
      Real.sqrt (U * Real.log U) ≤ Real.sqrt (U ^ 2) := Real.sqrt_le_sqrt hsq
      _ = U := Real.sqrt_sq hU0.le
  have hcRate : c * paperRate X n ≤ U := by
    have hc' : c * paperRate X n ≤ 1 * paperRate X n :=
      mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)
    calc
      c * paperRate X n ≤ paperRate X n := by simpa using hc'
      _ ≤ U := hTle
  have hvX : v ≤ X n := by
    have h := hvB
    unfold smoothCutoff at h
    have hexp : Real.exp (logCutoff c X n) ≤ Real.exp U :=
      Real.exp_le_exp.mpr (by simpa [logCutoff, hUdef] using hcRate)
    have hXeq : Real.exp U = X n := by
      rw [hUdef, bandLog]
      exact Real.exp_log hXpos
    calc
      v ≤ Real.exp (logCutoff c X n) := h
      _ ≤ Real.exp U := hexp
      _ = X n := hXeq
  have hvT : v ≤ X n ^ 3 + 1 := by
    have hX2 : 1 ≤ X n ^ 2 := by nlinarith [hX1, sq_nonneg (X n)]
    have hX3 : X n ≤ X n ^ 3 := by
      calc
        X n = X n * 1 := (mul_one _).symm
        _ ≤ X n * X n ^ 2 := mul_le_mul_of_nonneg_left hX2 hXpos.le
        _ = X n ^ 3 := by ring
    linarith
  have hT1 : 1 ≤ X n ^ 3 + 1 := by
    have h3 : 0 ≤ X n ^ 3 := pow_nonneg hXpos.le 3
    linarith
  have hper_v := hper v t (X n ^ 3 + 1) hv hT1
  have hpp := twistedPrimeSum_sub_vonMangoldt_le_sqrt (v := v) (t := t) hv
  have hcos : 0 ≤ C := hC
  have htri :
      ‖twistedPrimeSum v t - refZetaSum v t (X n ^ 3 + 1)‖ ≤
        C * (v * (Real.log v) ^ 2 / (X n ^ 3 + 1) + Real.log v) +
          2 * Real.sqrt v * Real.log v := by
    have hsplit :
        twistedPrimeSum v t - refZetaSum v t (X n ^ 3 + 1) =
          (twistedPrimeSum v t - vonMangoldtTwist v t) +
            (vonMangoldtTwist v t - refZetaSum v t (X n ^ 3 + 1)) := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have h := add_le_add hpp hper_v
    linarith
  have hv0 : 0 < v := by linarith
  have hlogv0 : 0 ≤ Real.log v := Real.log_nonneg (by linarith)
  have hlog2v_ge1 : 1 ≤ Real.log (2 * v) := by
    have h4 : (4 : ℝ) ≤ 2 * v := by linarith
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) h4
    have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
      nlinarith [Real.log_two_gt_d9]
    linarith
  have hlog2v_nonneg : 0 ≤ Real.log (2 * v) := by linarith
  have hlogv_le : Real.log v ≤ Real.log (2 * v) :=
    Real.log_le_log hv0 (by linarith)
  have hsq_le : (Real.log v) ^ 2 ≤ (Real.log (2 * v)) ^ 2 := by
    nlinarith
  have hlog_le_sq : Real.log v ≤ (Real.log (2 * v)) ^ 2 := by nlinarith
  have hsqrt1 : 1 ≤ Real.sqrt v := Real.one_le_sqrt.mpr (by linarith)
  have hR : (Real.log (2 * v)) ^ 2 ≤
      Real.sqrt v * (Real.log (2 * v)) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hsqrt1 (sq_nonneg (Real.log (2 * v)))
    simpa using h
  have hdiv : v * (Real.log v) ^ 2 / (X n ^ 3 + 1) ≤ (Real.log v) ^ 2 := by
    have hTpos : 0 < X n ^ 3 + 1 := by linarith
    rw [div_le_iff₀ hTpos]
    nlinarith [mul_le_mul_of_nonneg_right hvT (sq_nonneg (Real.log v))]
  have hkey :
      v * (Real.log v) ^ 2 / (X n ^ 3 + 1) + Real.log v ≤
        2 * (Real.sqrt v * (Real.log (2 * v)) ^ 2) := by
    have h1 : v * (Real.log v) ^ 2 / (X n ^ 3 + 1) + Real.log v ≤
        (Real.log v) ^ 2 + Real.log v := by linarith
    have h2 : (Real.log v) ^ 2 + Real.log v ≤
        2 * (Real.log (2 * v)) ^ 2 := by nlinarith
    have h3 : 2 * (Real.log (2 * v)) ^ 2 ≤
        2 * (Real.sqrt v * (Real.log (2 * v)) ^ 2) := by nlinarith
    linarith
  have hfinal1 := mul_le_mul_of_nonneg_left hkey hcos
  have hpp2 : 2 * Real.sqrt v * Real.log v ≤
      2 * (Real.sqrt v * (Real.log (2 * v)) ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hlog_le_sq
      (show 0 ≤ 2 * Real.sqrt v by positivity)
    nlinarith
  refine htri.trans ?_
  have hsum : C * (v * (Real.log v) ^ 2 / (X n ^ 3 + 1) + Real.log v) +
        2 * Real.sqrt v * Real.log v ≤
      (2 * C + 2) * (Real.sqrt v * (Real.log (2 * v)) ^ 2) := by
    nlinarith [hfinal1, hpp2]
  exact hsum

/-- **The absolute reference-Perron bound** at the extracted constant
`wave17KrefConst = 2 * wave17Cper + 2`. -/
theorem referencePerronBound_absolute {X : ℕ → ℝ} {c : ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n) (hc : c ≤ 1) :
    ReferencePerronBound X c (fun _ => wave17KrefConst) 2 := by
  have h := referencePerronBound_of_errorBound_absolute (Cper := 2)
    wave17TruncatedPerronBound wave17Cper_pos.le hX hU hc
  simpa [wave17KrefConst] using h

/-- The absolute reference-Perron bound at an arbitrary exponent `Cper` (the
exponent is ignored by `ReferencePerronBound`). -/
theorem referencePerronBound_absolute_exponent {X : ℕ → ℝ} {c Cper : ℝ}
    (hX : ∀ n, 1 < X n) (hU : ∀ n, 3 ≤ bandLog X n) (hc : c ≤ 1) :
    ReferencePerronBound X c (fun _ => wave17KrefConst) Cper :=
  referencePerronBound_absolute hX hU hc

/-- Monotonicity of the uniform line bound in its constant. -/
theorem verticalLineBound_mono {X : ℕ → ℝ} {K K' : ℕ → ℝ} {C : ℝ}
    (hX : ∀ n, 1 < X n) (h : VerticalLineBound X K C)
    (hle : ∀ᶠ n : ℕ in atTop, K n ≤ K' n) :
    VerticalLineBound X K' C := by
  filter_upwards [h, hle] with n hn hk
  intro u hu
  have hU0 : 0 ≤ bandLog X n := (Real.log_pos (hX n)).le
  exact (hn u hu).trans
    (mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hU0 C))

/-! ## The repaired L21.2 record -/

/-- **The wave-17 L21.2 data.**  Unlike `Wave16L21_2Inputs`, the reference
constant is the *absolute* `wave17KrefConst`, the horizontal constant is the
explicit off-pole strip constant `wave17KcontConst`, and the tail constant
`Ktail` is a single real.  The line constant is `KlineRaw`; the record derives

```
Kline = max KlineRaw (π (wave17KrefConst + wave17KcontConst + Ktail))
```

so that `Ksum_le` is a theorem rather than an unbounded adapter. -/
structure Wave17L21_2Inputs where
  /-- The finite Fourier/tent discrepancy profile. -/
  profile : TentProfile
  /-- The stage-one constant `c`. -/
  c : ℝ
  /-- The final Perron exponent. -/
  Cper : ℝ
  /-- The raw vertical-line constant. -/
  KlineRaw : ℝ
  /-- The given vertical-tail constant. -/
  Ktail : ℝ
  /-- The centre sequence of the short-interval count. -/
  p : ℕ → ℝ
  X_gt_one : ∀ n, 1 < profile.X n
  c_pos : 0 < c
  c_le_one : c ≤ 1
  /-- `log X ≥ 3`. -/
  U_ge_three : ∀ n, 3 ≤ bandLog profile.X n
  /-- `Cper ≥ 3`. -/
  Cper_ge_three : 3 ≤ Cper
  Kline_raw_nonneg : 0 ≤ KlineRaw
  Ktail_nonneg : 0 ≤ Ktail
  /-- The Riemann hypothesis for `ζ`, used by the off-pole strip route. -/
  hRH : RiemannZetaZerosOnLine
  /-- The genuine `ζ'/ζ` line bound at the raw constant. -/
  lineBound : VerticalLineBound profile.X (fun _ => KlineRaw) (Cper - 1)
  /-- The genuine vertical-tail estimate at the given tail constant. -/
  verticalTail : VerticalTailBound profile.X (fun _ => Ktail) (Cper - 1)
  /-- The centre is eventually larger than one. -/
  p_gt_one : ∀ᶠ n : ℕ in atTop, 1 < p n
  /-- The literal short-interval smooth count. -/
  localCount : ShortIntervalSmoothCountLower p c profile.X
  /-- `b ≤ B`. -/
  b_le_B : ∀ᶠ n : ℕ in atTop, bOf profile.X c n ≤ logCutoff c profile.X n
  /-- `e^a ≥ 2`. -/
  a_ge_log_two : ∀ᶠ n : ℕ in atTop, Real.log 2 ≤ aOf profile.X c n
  /-- Low-frequency energy bound. -/
  fourierLow : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.lowEnergy n ≤ Real.exp (-(((2 * c) / 3) - δ) * paperRate profile.X n)
  /-- Middle-frequency energy bound. -/
  fourierMiddle : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.middleEnergy n ≤ Real.exp (-((1 / c) - δ) * paperRate profile.X n)
  /-- High-frequency energy bound. -/
  fourierTail : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    profile.tailEnergy n ≤ Real.exp (-δ * paperRate profile.X n)
  /-- Two-scale separation. -/
  U_dominates : ∀ m : ℝ, 0 < m →
    ∀ᶠ n : ℕ in atTop, m * scale n ^ 2 ≤ bandLog profile.X n
  /-- `log X ≤ exp (scale n)`. -/
  U_le_exp : ∀ᶠ n : ℕ in atTop, bandLog profile.X n ≤ Real.exp (scale n)

namespace Wave17L21_2Inputs

variable (D : Wave17L21_2Inputs)

/-- The derived absolute line constant. -/
noncomputable def Kline : ℝ :=
  max D.KlineRaw (Real.pi * (wave17KrefConst + wave17KcontConst + D.Ktail))

theorem Kline_nonneg : 0 ≤ D.Kline := by
  unfold Kline
  refine le_max_of_le_right ?_
  exact mul_nonneg Real.pi_pos.le
    (add_nonneg (add_nonneg wave17KrefConst_nonneg wave17KcontConst_nonneg)
      D.Ktail_nonneg)

/-- **`Ksum_le` is a theorem** at the derived line constant. -/
theorem Ksum_le : ∀ᶠ n : ℕ in atTop,
    (fun _ => wave17KrefConst) n + (fun _ => wave17KcontConst) n +
        (fun _ => D.Ktail) n ≤
      (D.Kline / Real.pi) *
        (1 + Real.log (D.profile.X n ^ 3 / perronRe)) := by
  refine Eventually.of_forall ?_
  intro n
  set S : ℝ := wave17KrefConst + wave17KcontConst + D.Ktail with hS
  have hS0 : 0 ≤ S := by
    rw [hS]
    exact add_nonneg (add_nonneg wave17KrefConst_nonneg wave17KcontConst_nonneg)
      D.Ktail_nonneg
  have hpi : 0 < Real.pi := Real.pi_pos
  have hmax : Real.pi * S ≤ D.Kline := by
    rw [hS]
    unfold Kline
    exact le_max_right _ _
  have hle : S ≤ D.Kline / Real.pi := by
    rw [le_div_iff₀ hpi]
    linarith
  have hXpos : 0 < D.profile.X n := lt_trans zero_lt_one (D.X_gt_one n)
  have hX3 : 1 < D.profile.X n ^ 3 :=
    one_lt_pow₀ (D.X_gt_one n) (by norm_num)
  have hpr : 0 < perronRe := by norm_num [perronRe]
  have hratio : 1 < D.profile.X n ^ 3 / perronRe := by
    rw [one_lt_div hpr]
    norm_num [perronRe]
    linarith
  have hlogpos : 0 ≤ Real.log (D.profile.X n ^ 3 / perronRe) :=
    (Real.log_pos hratio).le
  have hcoef : 0 ≤ D.Kline / Real.pi := div_nonneg D.Kline_nonneg hpi.le
  have hone : (1 : ℝ) ≤ 1 + Real.log (D.profile.X n ^ 3 / perronRe) := by linarith
  calc
    (fun _ => wave17KrefConst) n + (fun _ => wave17KcontConst) n +
        (fun _ => D.Ktail) n = S := by rw [hS]
    _ ≤ D.Kline / Real.pi := hle
    _ = (D.Kline / Real.pi) * 1 := (mul_one _).symm
    _ ≤ (D.Kline / Real.pi) *
        (1 + Real.log (D.profile.X n ^ 3 / perronRe)) :=
      mul_le_mul_of_nonneg_left hone hcoef

/-- The line bound at the derived constant, by monotonicity. -/
theorem lineBound_derived :
    VerticalLineBound D.profile.X (fun _ => D.Kline) (D.Cper - 1) :=
  verticalLineBound_mono D.X_gt_one D.lineBound
    (Eventually.of_forall fun _ => le_max_left _ _)

/-- **The assembled L21.2 record.**  The reference and horizontal constants are
the absolute ones, `Kline` is the derived maximum, and every other field is
passed through unchanged. -/
noncomputable def toL21_2LeafData : L21_2LeafData where
  profile := D.profile
  c := D.c
  Cper := D.Cper
  Kline := D.Kline
  Kref := fun _ => wave17KrefConst
  Kcont := fun _ => wave17KcontConst
  Ktail := fun _ => D.Ktail
  p := D.p
  X_gt_one := D.X_gt_one
  c_pos := D.c_pos
  c_le_one := D.c_le_one
  U_ge_three := D.U_ge_three
  Cper_ge_three := D.Cper_ge_three
  Kline_nonneg := D.Kline_nonneg
  Kref_nonneg := Eventually.of_forall fun _ => wave17KrefConst_nonneg
  Kcont_nonneg := Eventually.of_forall fun _ => wave17KcontConst_nonneg
  Ktail_nonneg := Eventually.of_forall fun _ => D.Ktail_nonneg
  Ksum_le := D.Ksum_le
  hRH := D.hRH
  lineBound := D.lineBound_derived
  referencePerron :=
    referencePerronBound_absolute D.X_gt_one D.U_ge_three D.c_le_one
  horizontalRemainder :=
    horizontalRemainderBound_of_contourRemainder D.X_gt_one D.hRH
      (contourRemainderBound_of_stripOffPole D.hRH
        (stripZetaBoundOffPole_of_RH_exponent D.X_gt_one D.U_ge_three D.hRH
          (by linarith [D.Cper_ge_three]))
        D.X_gt_one (fun _ => stripK_nonneg)
        (Eventually.of_forall fun _ => le_rfl))
  verticalTail := D.verticalTail
  p_gt_one := D.p_gt_one
  localCount := D.localCount
  b_le_B := D.b_le_B
  a_ge_log_two := D.a_ge_log_two
  fourierLow := D.fourierLow
  fourierMiddle := D.fourierMiddle
  fourierTail := D.fourierTail
  U_dominates := D.U_dominates
  U_le_exp := D.U_le_exp

theorem toL21_2LeafData_Kline :
    D.toL21_2LeafData.Kline = D.Kline := rfl

/-- The derived constant is exactly the advertised maximum. -/
theorem Kline_eq : D.Kline =
    max D.KlineRaw (Real.pi * (wave17KrefConst + wave17KcontConst + D.Ktail)) :=
  rfl

/-- The reference-Perron field of the assembled record is the absolute bound. -/
theorem toL21_2LeafData_referencePerron :
    ReferencePerronBound D.profile.X D.c (fun _ => wave17KrefConst) (D.Cper - 1) :=
  D.toL21_2LeafData.referencePerron

/-- The horizontal field of the assembled record is the off-pole strip bound. -/
theorem toL21_2LeafData_horizontalRemainder :
    HorizontalRemainderBound D.profile.X D.c (fun _ => wave17KcontConst)
      (D.Cper - 1) :=
  D.toL21_2LeafData.horizontalRemainder

theorem toL21_2LeafData_Kref :
    D.toL21_2LeafData.Kref = fun _ => wave17KrefConst := rfl

theorem toL21_2LeafData_Kcont :
    D.toL21_2LeafData.Kcont = fun _ => wave17KcontConst := rfl

theorem toL21_2LeafData_Ktail :
    D.toL21_2LeafData.Ktail = fun _ => D.Ktail := rfl

/-- The reduction does not alter the loss data: the profile, `c` and the centre
sequence are exactly those of the repaired record. -/
theorem toL21_2LeafData_loss_data :
    D.toL21_2LeafData.profile = D.profile ∧
      D.toL21_2LeafData.c = D.c ∧ D.toL21_2LeafData.p = D.p :=
  ⟨rfl, rfl, rfl⟩

/-- The loss is still the genuine normalized bad-centre count. -/
theorem toL21_2LeafData_loss_eq_card_fraction (n : ℕ) :
    D.toL21_2LeafData.ratedLeaf.loss n =
      ((D.toL21_2LeafData.toAbelInputs.toFourierInputs.badSet n).card : ℝ) /
        (D.profile.N n : ℝ) :=
  D.toL21_2LeafData.ratedLeaf_loss_eq_card_fraction n

/-! ### Non-vacuity: an inhabitant from the genuine data -/

/-- **The repaired record is inhabited** from the genuine line bound, tail
bound, local count and Fourier data.  The line bound is supplied at the raw
constant `KlineRaw`; the record itself derives the enlarged constant
`max KlineRaw (π (Kref + Kcont + Ktail))`, and all the derived fields
(`Kline_nonneg`, `Ksum_le`, `lineBound_derived`, the absolute reference-Perron
field and the off-pole horizontal field) are theorems.  The loss data
(`profile`, `c`, `p`) are unchanged. -/
noncomputable def ofRaw
    (profile : TentProfile) (c Cper KlineRaw Ktail : ℝ) (p : ℕ → ℝ)
    (X_gt_one : ∀ n, 1 < profile.X n) (c_pos : 0 < c) (c_le_one : c ≤ 1)
    (U_ge_three : ∀ n, 3 ≤ bandLog profile.X n) (Cper_ge_three : 3 ≤ Cper)
    (Kline_raw_nonneg : 0 ≤ KlineRaw) (Ktail_nonneg : 0 ≤ Ktail)
    (hRH : RiemannZetaZerosOnLine)
    (lineBound : VerticalLineBound profile.X (fun _ => KlineRaw) (Cper - 1))
    (verticalTail : VerticalTailBound profile.X (fun _ => Ktail) (Cper - 1))
    (p_gt_one : ∀ᶠ n : ℕ in atTop, 1 < p n)
    (localCount : ShortIntervalSmoothCountLower p c profile.X)
    (b_le_B : ∀ᶠ n : ℕ in atTop, bOf profile.X c n ≤ logCutoff c profile.X n)
    (a_ge_log_two : ∀ᶠ n : ℕ in atTop, Real.log 2 ≤ aOf profile.X c n)
    (fourierLow : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      profile.lowEnergy n ≤ Real.exp (-(((2 * c) / 3) - δ) * paperRate profile.X n))
    (fourierMiddle : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      profile.middleEnergy n ≤ Real.exp (-((1 / c) - δ) * paperRate profile.X n))
    (fourierTail : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      profile.tailEnergy n ≤ Real.exp (-δ * paperRate profile.X n))
    (U_dominates : ∀ m : ℝ, 0 < m →
      ∀ᶠ n : ℕ in atTop, m * scale n ^ 2 ≤ bandLog profile.X n)
    (U_le_exp : ∀ᶠ n : ℕ in atTop, bandLog profile.X n ≤ Real.exp (scale n)) :
    Wave17L21_2Inputs where
  profile := profile
  c := c
  Cper := Cper
  KlineRaw := KlineRaw
  Ktail := Ktail
  p := p
  X_gt_one := X_gt_one
  c_pos := c_pos
  c_le_one := c_le_one
  U_ge_three := U_ge_three
  Cper_ge_three := Cper_ge_three
  Kline_raw_nonneg := Kline_raw_nonneg
  Ktail_nonneg := Ktail_nonneg
  hRH := hRH
  lineBound := lineBound
  verticalTail := verticalTail
  p_gt_one := p_gt_one
  localCount := localCount
  b_le_B := b_le_B
  a_ge_log_two := a_ge_log_two
  fourierLow := fourierLow
  fourierMiddle := fourierMiddle
  fourierTail := fourierTail
  U_dominates := U_dominates
  U_le_exp := U_le_exp

theorem ofRaw_Kline
    (profile : TentProfile) (c Cper KlineRaw Ktail : ℝ) (p : ℕ → ℝ)
    (X_gt_one : ∀ n, 1 < profile.X n) (c_pos : 0 < c) (c_le_one : c ≤ 1)
    (U_ge_three : ∀ n, 3 ≤ bandLog profile.X n) (Cper_ge_three : 3 ≤ Cper)
    (Kline_raw_nonneg : 0 ≤ KlineRaw) (Ktail_nonneg : 0 ≤ Ktail)
    (hRH : RiemannZetaZerosOnLine)
    (lineBound : VerticalLineBound profile.X (fun _ => KlineRaw) (Cper - 1))
    (verticalTail : VerticalTailBound profile.X (fun _ => Ktail) (Cper - 1))
    (p_gt_one : ∀ᶠ n : ℕ in atTop, 1 < p n)
    (localCount : ShortIntervalSmoothCountLower p c profile.X)
    (b_le_B : ∀ᶠ n : ℕ in atTop, bOf profile.X c n ≤ logCutoff c profile.X n)
    (a_ge_log_two : ∀ᶠ n : ℕ in atTop, Real.log 2 ≤ aOf profile.X c n)
    (fourierLow : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      profile.lowEnergy n ≤ Real.exp (-(((2 * c) / 3) - δ) * paperRate profile.X n))
    (fourierMiddle : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      profile.middleEnergy n ≤ Real.exp (-((1 / c) - δ) * paperRate profile.X n))
    (fourierTail : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      profile.tailEnergy n ≤ Real.exp (-δ * paperRate profile.X n))
    (U_dominates : ∀ m : ℝ, 0 < m →
      ∀ᶠ n : ℕ in atTop, m * scale n ^ 2 ≤ bandLog profile.X n)
    (U_le_exp : ∀ᶠ n : ℕ in atTop, bandLog profile.X n ≤ Real.exp (scale n)) :
    (ofRaw profile c Cper KlineRaw Ktail p X_gt_one c_pos c_le_one U_ge_three
      Cper_ge_three Kline_raw_nonneg Ktail_nonneg hRH lineBound verticalTail
      p_gt_one localCount b_le_B a_ge_log_two fourierLow fourierMiddle
      fourierTail U_dominates U_le_exp).Kline =
      max KlineRaw (Real.pi * (wave17KrefConst + wave17KcontConst + Ktail)) :=
  rfl

end Wave17L21_2Inputs

/-! ## The wave-17 inputs -/

/-- The C5 ledger of the wave-17 inputs. -/
noncomputable def wave17Slots
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21_2 : Wave17L21_2Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave14L30Inputs) (l34 : L34ChebotarevSidesInputs)
    (l4N l4Bits : ℕ) (l4N_odd : Odd l4N) (l4Bits_budget : 2 ^ l4Bits ≤ l4N)
    (p1 : SubexpPrepassInput) : C5LossSlots :=
  wave15Slots l18_4 l19 l20_2 l20_4 l21_2.toL21_2LeafData l27_data l27_finish
    l30 l34 l4N l4Bits l4N_odd l4Bits_budget p1

/-- **The wave-17 ledger is the wave-15 ledger at the assembled L21.2 record.** -/
theorem wave17Slots_eq
    (l18_4 : L18_4Certificate) (l19 : Wave15L19Inputs)
    (l20_2 : SaddleConcentrationSource) (l20_4 : Wave14L20_4Source)
    (l21_2 : Wave17L21_2Inputs) (l27_data : L27_1Inputs)
    (l27_finish : L27StageOneFinishInputs l27_data)
    (l30 : Wave14L30Inputs) (l34 : L34ChebotarevSidesInputs)
    (l4N l4Bits : ℕ) (l4N_odd : Odd l4N) (l4Bits_budget : 2 ^ l4Bits ≤ l4N)
    (p1 : SubexpPrepassInput) :
    wave17Slots l18_4 l19 l20_2 l20_4 l21_2 l27_data l27_finish l30 l34
        l4N l4Bits l4N_odd l4Bits_budget p1 =
      wave15Slots l18_4 l19 l20_2 l20_4 l21_2.toL21_2LeafData l27_data
        l27_finish l30 l34 l4N l4Bits l4N_odd l4Bits_budget p1 :=
  rfl

/-- **The wave-17 inputs.**  They are the wave-16 inputs with the L21.2 record
replaced by the repaired `Wave17L21_2Inputs`, whose line constant is absolute
and whose `Ksum_le` is a theorem.  Every other field is passed through
unchanged. -/
structure Wave17Inputs
    (E : ∀ n, 3 ≤ n → HardEpochData n) (D : ℝ) where
  /-- The full L18.4 certificate. -/
  l18_4 : L18_4Certificate
  /-- The full L19 certificate, with the L19.6 thin slot built from
  `ThinLatticeData`. -/
  l19 : Wave15L19Inputs
  /-- L20.2: interior concentration from the paper-mass saddle source. -/
  l20_2 : SaddleConcentrationSource
  /-- L20.4: the sourced child-root-conditioned two-point data. -/
  l20_4 : Wave14L20_4Source
  /-- L21.2: RH smooth numbers near integer centres, with the absolute
  reference constant and the derived line constant. -/
  l21_2 : Wave17L21_2Inputs
  /-- The odd modulus of the L4 split-band realization. -/
  l4N : ℕ
  /-- The explicit bit budget of the L4 band. -/
  l4Bits : ℕ
  /-- The L4 modulus is odd. -/
  l4N_odd : Odd l4N
  /-- **The L4 bit budget**: the budgeted band is inside the modulus. -/
  l4Bits_budget : 2 ^ l4Bits ≤ l4N
  /-- The parent L27.1 ECM data. -/
  l27_data : L27_1Inputs
  /-- The L27.1 stage-one finish data. -/
  l27_finish : L27StageOneFinishInputs l27_data
  /-- L30: the sourced counts and the H.3 failure data. -/
  l30 : Wave14L30Inputs
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
  /-- Adapter: the concrete C5 loss is dominated by the wave-17 ledger. -/
  loss_le : ∀ n (hN : 3 ≤ n),
    c5TotalLoss hN (concrete n hN) (c5Data.toC5 n hN) ≤
      (wave17Slots l18_4 l19 l20_2 l20_4 l21_2 l27_data l27_finish
        l30 l34 l4N l4Bits l4N_odd l4Bits_budget p1).total n

namespace Wave17Inputs

variable {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}

/-- **The wave-15 inputs from the wave-17 inputs.**  Only the L21.2 record
changes: it is assembled by `Wave17L21_2Inputs.toL21_2LeafData`. -/
noncomputable def toWave15Inputs (I : Wave17Inputs E D) : Wave15Inputs E D where
  l18_4 := I.l18_4
  l19 := I.l19
  l20_2 := I.l20_2
  l20_4 := I.l20_4
  l21_2 := I.l21_2.toL21_2LeafData
  l4N := I.l4N
  l4Bits := I.l4Bits
  l4N_odd := I.l4N_odd
  l4Bits_budget := I.l4Bits_budget
  l27_data := I.l27_data
  l27_finish := I.l27_finish
  l30 := I.l30
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
    simpa only [wave17Slots] using I.loss_le n hN

/-- **The wave-17 ledger is the wave-15 ledger of the reduction.** -/
theorem toWave15Inputs_slots (I : Wave17Inputs E D) :
    I.toWave15Inputs.toFullyDischargedInputs.toPaperAnalyticAssumptions.slots =
      wave17Slots I.l18_4 I.l19 I.l20_2 I.l20_4 I.l21_2 I.l27_data
        I.l27_finish I.l30 I.l34 I.l4N I.l4Bits I.l4N_odd I.l4Bits_budget I.p1 := by
  rw [Wave15Inputs.toFullyDischargedInputs_slots]
  rfl

/-- **The fully discharged inputs from the wave-17 inputs.** -/
noncomputable def toFullyDischargedInputs (I : Wave17Inputs E D) :
    FullyDischargedInputs E D :=
  I.toWave15Inputs.toFullyDischargedInputs

/-- **The paper endpoint inputs from the wave-17 inputs.** -/
noncomputable def toPaperEndpointInputs (I : Wave17Inputs E D) :
    PaperEndpointInputs E D :=
  I.toFullyDischargedInputs.toPaperEndpointInputs

/-- The paper record produced by the wave-17 inputs has the wave-17 ledger. -/
theorem toPaperEndpointInputs_paper_slots (I : Wave17Inputs E D) :
    I.toPaperEndpointInputs.paper.slots =
      wave17Slots I.l18_4 I.l19 I.l20_2 I.l20_4 I.l21_2 I.l27_data
        I.l27_finish I.l30 I.l34 I.l4N I.l4Bits I.l4N_odd I.l4Bits_budget I.p1 :=
  I.toWave15Inputs_slots

end Wave17Inputs

/-! ## The endpoint -/

/-- **Wave-17 paper endpoint.**  Under the critical-line hypothesis for
Dirichlet L-functions, there is one universal serialized factoring algorithm
such that, for every balanced-schedule epoch family which, at every valid
ceiling, carries

* the full L18.4 certificate,
* the L19 certificate with its thin slot built from `ThinLatticeData`,
* the L20.2 paper-mass concentration source,
* the sourced L20.4 disjunction-event data,
* the repaired L21.2 data, with an **absolute** reference-Perron constant, the
  explicit off-pole horizontal constant, a given tail constant, and the derived
  line constant `max KlineRaw (π (Kref + Kcont + Ktail))`,
* the proved L4 bit-budget split-band realization (`Odd N`, `2 ^ bits ≤ N`),
* the L27.1 stage-one finish data,
* the explicit L30 short-interval count, global binomial lower bound and H.3
  failure data,
* the L34 explicit Chebotarev-side counting inputs,
* P1 with an explicit `exp (o(H))` cost rate,
* C1–C4, and
* the C5 certificate assembled by `c5FullOfCount`,

the kernel-checked driver always outputs a permutation of `n.primeFactorsList`
and has expected serialized bit cost eventually at most
`exp ((balancedEnvelopeInfimum + ε) * scale n)`, where
`balancedEnvelopeInfimum ∈ (1.9839824118071388228, 1.9839824118071388230)`.

The proof composes `Wave17Inputs.toWave15Inputs` with the wave-15 endpoint,
which is the same fully discharged endpoint used by the wave-16 theorem. -/
theorem serialized_assembled_balancedEnvelopeInfimum_from_wave17Inputs
    (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (E : ∀ (_s : BalancedRationalSchedule) (n : ℕ), 3 ≤ n → HardEpochData n),
      (∀ (s : BalancedRationalSchedule) (D : ℝ), s.Valid D →
        Wave17Inputs (E s) D) →
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

#print axioms wave17Cper
#print axioms wave17Cper_pos
#print axioms wave17TruncatedPerronBound
#print axioms wave17KrefConst
#print axioms wave17KrefConst_nonneg
#print axioms wave17KcontConst
#print axioms wave17KcontConst_nonneg
#print axioms twistedPrimeSum_sub_vonMangoldt_le_sqrt
#print axioms referencePerronBound_of_errorBound_absolute
#print axioms referencePerronBound_absolute
#print axioms referencePerronBound_absolute_exponent
#print axioms verticalLineBound_mono
#print axioms Wave17L21_2Inputs.Kline
#print axioms Wave17L21_2Inputs.Kline_nonneg
#print axioms Wave17L21_2Inputs.Ksum_le
#print axioms Wave17L21_2Inputs.lineBound_derived
#print axioms Wave17L21_2Inputs.toL21_2LeafData
#print axioms Wave17L21_2Inputs.Kline_eq
#print axioms Wave17L21_2Inputs.toL21_2LeafData_Kline
#print axioms Wave17L21_2Inputs.toL21_2LeafData_referencePerron
#print axioms Wave17L21_2Inputs.toL21_2LeafData_horizontalRemainder
#print axioms Wave17L21_2Inputs.toL21_2LeafData_loss_data
#print axioms Wave17L21_2Inputs.toL21_2LeafData_loss_eq_card_fraction
#print axioms Wave17L21_2Inputs.ofRaw
#print axioms Wave17L21_2Inputs.ofRaw_Kline
#print axioms wave17Slots
#print axioms wave17Slots_eq
#print axioms Wave17Inputs.toWave15Inputs
#print axioms Wave17Inputs.toWave15Inputs_slots
#print axioms Wave17Inputs.toFullyDischargedInputs
#print axioms Wave17Inputs.toPaperEndpointInputs
#print axioms Wave17Inputs.toPaperEndpointInputs_paper_slots
#print axioms serialized_assembled_balancedEnvelopeInfimum_from_wave17Inputs

end Cogentic.RandomizedPaperEndpointWave17
