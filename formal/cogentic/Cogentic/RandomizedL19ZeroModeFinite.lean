import Cogentic.RandomizedL19ZeroMode

/-!
# L19.5: replacing `rho_initial` by a finite check

`Cogentic.RandomizedL19ZeroMode.ZeroModeResidualCertificate` contains the field
`rho_initial`, asserting the residual bound on the initial segment
`scale n ≤ S`.  Since `scale` tends to infinity, that segment is finite, but the
certificate records it by an unbounded `∀ n` with a side condition.

This file replaces that field by an explicit finite check on a `Finset`.

* `initialFinset S N` is `{n < N | scale n ≤ S}`.
* `CoversInitialSegment S N` says every `n` with `scale n ≤ S` satisfies
  `n < N`; `exists_initialBound` produces such an `N` from `scale_grows`.
* `RhoInitial` is the old initial-segment predicate and `FiniteInitialCheck`
  is its finite version.
* `rhoInitial_iff_finiteCheck` shows they are equivalent once `N` covers the
  initial segment.
* `finiteMaxRatio` is the exact finite maximum
  `max_{n < N, scale n ≤ S} ρ n / (exp (2 c₀ scale n) exp (-η W n))`, and
  `finiteCheck_iff_finiteMaxRatio_le_one` proves that the finite check is
  *equivalent* to that finite maximum being at most `1`.

Because `ρ` is an arbitrary field of the certificate, no theorem can prove the
finite check for it: the finite maximum is a genuine hypothesis.  What is
proved is that this single finite maximum condition is exactly the initial
segment input, and that it suffices for the whole reduction.

For the "absorb by constants" direction, `exists_adjust_c0_of_nonneg_scale`
shows that when `scale` is nonnegative on the initial segment, a finite uniform
bound on `ρ` is always absorbed by increasing `c₀`; only the indices with
`scale n = 0` need a separate explicit check.  No such absorption is asserted
for negative `scale`, where increasing `c₀` would move the bound in the wrong
direction.

Nothing here is a `sorry`, an `admit`, an `axiom`, or `native_decide`.  No
mass, count, maximum or error is set to zero.
-/

namespace Cogentic.RandomizedL19ZeroModeFinite

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL19ZeroMode
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperLeafStatements

/-! ## 1. The finite initial segment -/

/-- The finite initial segment `{n < N | scale n ≤ S}`. -/
noncomputable def initialFinset (S : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n => scale n ≤ S)

/-- An explicit covering of the initial segment: every `n` with
`scale n ≤ S` is strictly below `N`. -/
def CoversInitialSegment (S : ℝ) (N : ℕ) : Prop :=
  ∀ n : ℕ, scale n ≤ S → n < N

theorem mem_initialFinset {S : ℝ} {N n : ℕ} :
    n ∈ initialFinset S N ↔ n < N ∧ scale n ≤ S := by
  simp [initialFinset]

theorem zero_mem_initialFinset {S : ℝ} {N : ℕ} (hS : 0 ≤ S) (hN : 0 < N) :
    0 ∈ initialFinset S N := by
  simp [initialFinset, scale, hN, hS]

theorem initialFinset_nonempty {S : ℝ} {N : ℕ} (hS : 0 ≤ S) (hN : 0 < N) :
    (initialFinset S N).Nonempty :=
  ⟨0, zero_mem_initialFinset hS hN⟩

/-- The initial segment is finite because `scale` tends to infinity. -/
theorem exists_initialBound (S : ℝ) : ∃ N : ℕ, CoversInitialSegment S N := by
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp (scale_grows.eventually_gt_atTop S)
  refine ⟨N, fun n hn => ?_⟩
  by_contra h
  exact absurd hn (not_le.mpr (hN n (le_of_not_gt h)))

/-! ## 2. The old predicate, the finite predicate, and the exact finite maximum -/

/-- The old `rho_initial` statement, written as a predicate. -/
def RhoInitial (W rho : ℕ → ℝ) (c0 eta S : ℝ) : Prop :=
  ∀ n : ℕ, scale n ≤ S →
    rho n ≤ exp (2 * c0 * scale n) * exp (-eta * W n)

/-- The finite version of `RhoInitial`: only the finitely many indices below
the explicit sample bound `N` are checked. -/
def FiniteInitialCheck (W rho : ℕ → ℝ) (c0 eta S : ℝ) (N : ℕ) : Prop :=
  ∀ n : ℕ, n < N → scale n ≤ S →
    rho n ≤ exp (2 * c0 * scale n) * exp (-eta * W n)

theorem rhoInitial_iff_finiteCheck {W rho : ℕ → ℝ} {c0 eta S : ℝ} {N : ℕ}
    (hN : CoversInitialSegment S N) :
    RhoInitial W rho c0 eta S ↔
      FiniteInitialCheck W rho c0 eta S N := by
  constructor
  · intro h n _ hnS
    exact h n hnS
  · intro h n hnS
    exact h n (hN n hnS) hnS

/-- The literal `Finset` form of the finite initial check: the bound is
required only at members of `initialFinset S N`. -/
def FinsetInitialCheck (W rho : ℕ → ℝ) (c0 eta S : ℝ) (N : ℕ) : Prop :=
  ∀ n ∈ initialFinset S N,
    rho n ≤ exp (2 * c0 * scale n) * exp (-eta * W n)

theorem finsetInitialCheck_iff_finiteInitialCheck
    {W rho : ℕ → ℝ} {c0 eta S : ℝ} {N : ℕ} :
    FinsetInitialCheck W rho c0 eta S N ↔
      FiniteInitialCheck W rho c0 eta S N := by
  constructor
  · intro h n hn hnS
    exact h n (mem_initialFinset.mpr ⟨hn, hnS⟩)
  · intro h n hn
    obtain ⟨hnN, hnS⟩ := mem_initialFinset.mp hn
    exact h n hnN hnS

/-- The normalised residual ratio whose finite maximum is the exact initial
segment condition. -/
noncomputable def rhoRatio (W rho : ℕ → ℝ) (c0 eta : ℝ) (n : ℕ) : ℝ :=
  rho n / (exp (2 * c0 * scale n) * exp (-eta * W n))

theorem rhoRatio_denom_pos (W _rho : ℕ → ℝ) (c0 eta : ℝ) (n : ℕ) :
    0 < exp (2 * c0 * scale n) * exp (-eta * W n) := by
  positivity

/-- **The exact finite-max condition.**  The maximum of the normalised
residual over the finite initial segment, with indices outside the segment
contributing `0` (which is harmless because the target bound is `1`). -/
noncomputable def finiteMaxRatio (W rho : ℕ → ℝ) (c0 eta S : ℝ) (N : ℕ) : ℝ :=
  (Finset.range (N + 1)).sup' ⟨0, by simp⟩
    (fun n => if scale n ≤ S then rhoRatio W rho c0 eta n else 0)

/-- The finite maximum is `≤ 1` exactly when the finite initial check holds. -/
theorem finiteCheck_iff_finiteMaxRatio_le_one
    {W rho : ℕ → ℝ} {c0 eta S : ℝ} {N : ℕ}
    (hN : CoversInitialSegment S N) :
    FiniteInitialCheck W rho c0 eta S N ↔
      finiteMaxRatio W rho c0 eta S N ≤ 1 := by
  constructor
  · intro h
    refine Finset.sup'_le _ _ ?_
    intro n hn
    by_cases hnS : scale n ≤ S
    · rw [if_pos hnS]
      rw [rhoRatio, div_le_one (rhoRatio_denom_pos W rho c0 eta n)]
      have hnlt : n < N := by
        have hlt := Finset.mem_range.mp hn
        by_contra h
        have hcontra := hN n hnS
        omega
      exact h n hnlt hnS
    · rw [if_neg hnS]
      norm_num
  · intro h n hn hnS
    have hmem : n ∈ Finset.range (N + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_lt hn)
    have hle :
        (if scale n ≤ S then rhoRatio W rho c0 eta n else 0) ≤ 1 :=
      (Finset.le_sup' _ hmem).trans h
    rw [if_pos hnS] at hle
    rwa [rhoRatio, div_le_one (rhoRatio_denom_pos W rho c0 eta n)] at hle

/-- The finite check with the maximum written on the literal finite set
`initialFinset S N` rather than on `range (N + 1)`. -/
noncomputable def finiteMaxRatioOn (W rho : ℕ → ℝ) (c0 eta S : ℝ) (N : ℕ)
    (hne : (initialFinset S N).Nonempty) : ℝ :=
  (initialFinset S N).sup' hne (fun n => rhoRatio W rho c0 eta n)

theorem finiteCheck_iff_finiteMaxRatioOn_le_one
    {W rho : ℕ → ℝ} {c0 eta S : ℝ} {N : ℕ}
    (hne : (initialFinset S N).Nonempty) :
    FiniteInitialCheck W rho c0 eta S N ↔
      finiteMaxRatioOn W rho c0 eta S N hne ≤ 1 := by
  constructor
  · intro h
    refine Finset.sup'_le _ _ ?_
    intro n hn
    obtain ⟨hnN, hnS⟩ := mem_initialFinset.mp hn
    rw [rhoRatio, div_le_one (rhoRatio_denom_pos W rho c0 eta n)]
    exact h n hnN hnS
  · intro h n hn hnS
    have hmem : n ∈ initialFinset S N := mem_initialFinset.mpr ⟨hn, hnS⟩
    have hle : rhoRatio W rho c0 eta n ≤ 1 :=
      (Finset.le_sup' _ hmem).trans h
    rwa [rhoRatio, div_le_one (rhoRatio_denom_pos W rho c0 eta n)] at hle

/-! ## 3. The residual certificate with a finite initial check -/

/-- The residual certificate with `rho_initial` replaced by a finite check on
`initialFinset S N`. -/
structure FiniteZeroModeResidualCertificate (W : ℕ → ℝ) where
  /-- `W = log V` is nonnegative. -/
  W_nonneg : ∀ n, 0 ≤ W n
  /-- The discarded inner ellipse. -/
  ellipse : EllipseDiscardData W
  /-- The period-prime deletion. -/
  period : PeriodPrimeResidual W
  /-- The residual `ρ`. -/
  rho : ℕ → ℝ
  /-- `ρ` is nonnegative. -/
  rho_nonneg : ∀ n, 0 ≤ rho n
  /-- Internal exponent of the combined residual. -/
  c0 : ℝ
  /-- The internal exponent is positive. -/
  c0_pos : 0 < c0
  /-- Combined decay exponent. -/
  eta : ℝ
  /-- The combined decay is genuine. -/
  eta_pos : 0 < eta
  /-- The combined decay is no larger than the ellipse decay. -/
  eta_le_ellipse : eta ≤ 2 * ellipse.a
  /-- The combined decay is no larger than the period-prime decay. -/
  eta_le_period : eta ≤ period.cP
  /-- The period-prime exponent fits under `c0`. -/
  period_exp_le : period.cN / Real.log 2 ≤ c0
  /-- **Residual decomposition**: `ρ` is the sum of the ellipse and period
  residuals. -/
  rho_eq : ∀ n, rho n = ellipse.discardedMass n + period.residual n
  /-- The threshold where the asymptotic constant is absorbed. -/
  S : ℝ
  /-- The threshold is nonnegative. -/
  S_nonneg : 0 ≤ S
  /-- The threshold dominates `log (16π) / c0`. -/
  S_ge_const : Real.log (16 * π) / c0 ≤ S
  /-- Explicit sample bound for the finite initial segment. -/
  N : ℕ
  /-- The sample bound covers every index with `scale n ≤ S`. -/
  covers : CoversInitialSegment S N
  /-- **Finite initial check**: the bound on the explicit finite segment. -/
  rho_finite : FiniteInitialCheck W rho c0 eta S N

namespace FiniteZeroModeResidualCertificate

variable {W : ℕ → ℝ} (R : FiniteZeroModeResidualCertificate W)

/-- Forget the finite sample bound, recovering the original certificate. -/
noncomputable def toZeroModeResidualCertificate :
    ZeroModeResidualCertificate W where
  W_nonneg := R.W_nonneg
  ellipse := R.ellipse
  period := R.period
  rho := R.rho
  rho_nonneg := R.rho_nonneg
  c0 := R.c0
  c0_pos := R.c0_pos
  eta := R.eta
  eta_pos := R.eta_pos
  eta_le_ellipse := R.eta_le_ellipse
  eta_le_period := R.eta_le_period
  period_exp_le := R.period_exp_le
  rho_eq := R.rho_eq
  S := R.S
  S_nonneg := R.S_nonneg
  S_ge_const := R.S_ge_const
  rho_initial := fun n hn => R.rho_finite n (R.covers n hn) hn

/-- **The residual bound from the finite check.** -/
theorem rho_bound (n : ℕ) :
    R.rho n ≤ exp ((2 * R.c0) * scale n) * exp (-R.eta * W n) :=
  R.toZeroModeResidualCertificate.rho_bound n

/-- The certificate's initial check in literal `Finset` form. -/
theorem rho_finite_finset :
    FinsetInitialCheck W R.rho R.c0 R.eta R.S R.N :=
  finsetInitialCheck_iff_finiteInitialCheck.mpr R.rho_finite

/-- The finite check is equivalent to the finite maximum condition. -/
theorem rho_finite_iff_max :
    FiniteInitialCheck W R.rho R.c0 R.eta R.S R.N ↔
      finiteMaxRatio W R.rho R.c0 R.eta R.S R.N ≤ 1 :=
  finiteCheck_iff_finiteMaxRatio_le_one R.covers

end FiniteZeroModeResidualCertificate

/-! ## 4. The full certificate with a finite initial check -/

/-- The L19.5 certificate with the residual initial segment recorded by a
finite check. -/
structure FiniteZeroModeCertificate (W : ℕ → ℝ) where
  /-- `W = log V` is nonnegative. -/
  W_nonneg : ∀ n, 0 ≤ W n
  /-- `log V = D^{O(1)}` dominates every fixed multiple of `scale`. -/
  W_dominates : DominatesScale W
  /-- The ordinary reference density `μ`. -/
  mu : ℕ → ℝ
  /-- `μ` is positive. -/
  mu_pos : ∀ n, 0 < mu n
  /-- The covering data for the retained zero mode. -/
  covering : ZeroModeCoveringData W
  /-- Exponent of the divided-strip comparison. -/
  cq : ℝ
  /-- **Divided-strip ratio** `μ_q ≤ D^{cq} μ`. -/
  muq_le : ∀ n, covering.muq n ≤ exp (cq * scale n) * mu n
  /-- The retained part of the zero mode. -/
  retained : ℕ → ℝ
  /-- The retained part is nonnegative. -/
  retained_nonneg : ∀ n, 0 ≤ retained n
  /-- The retained part is the covering data's retained part. -/
  retained_eq : ∀ n, retained n = covering.retained n
  /-- The discarded part of the zero mode. -/
  discarded : ℕ → ℝ
  /-- The discarded part is nonnegative. -/
  discarded_nonneg : ∀ n, 0 ≤ discarded n
  /-- The ideal zero mode. -/
  zeroMode : ℕ → ℝ
  /-- The zero mode is nonnegative. -/
  zeroMode_nonneg : ∀ n, 0 ≤ zeroMode n
  /-- The zero mode is the sum of the retained and discarded parts. -/
  zeroMode_eq : ∀ n, zeroMode n = retained n + discarded n
  /-- The residual certificate with a finite initial check. -/
  residual : FiniteZeroModeResidualCertificate W
  /-- **Discarded zero-mode bound**: `discarded ≤ ρ μ²`. -/
  discarded_le : ∀ n, discarded n ≤ residual.rho n * mu n ^ 2

namespace FiniteZeroModeCertificate

variable {W : ℕ → ℝ} (C : FiniteZeroModeCertificate W)

/-- Forget the finite initial check. -/
noncomputable def toZeroModeCertificate : ZeroModeCertificate W where
  W_nonneg := C.W_nonneg
  W_dominates := C.W_dominates
  mu := C.mu
  mu_pos := C.mu_pos
  covering := C.covering
  cq := C.cq
  muq_le := C.muq_le
  retained := C.retained
  retained_nonneg := C.retained_nonneg
  retained_eq := C.retained_eq
  discarded := C.discarded
  discarded_nonneg := C.discarded_nonneg
  zeroMode := C.zeroMode
  zeroMode_nonneg := C.zeroMode_nonneg
  zeroMode_eq := C.zeroMode_eq
  residual := C.residual.toZeroModeResidualCertificate
  discarded_le := C.discarded_le

/-- The ideal zero-mode bound survives the finite replacement. -/
theorem zero_mode_bound (n : ℕ) :
    C.zeroMode n ≤
      exp ((2 * C.covering.cb + C.covering.cc) * scale n) *
          C.covering.muq n ^ 2 +
        C.residual.rho n * C.mu n ^ 2 :=
  C.toZeroModeCertificate.zero_mode_bound n

/-- The residual bound survives the finite replacement. -/
theorem rho_bound (n : ℕ) :
    C.residual.rho n ≤
      exp ((2 * C.residual.c0) * scale n) * exp (-C.residual.eta * W n) :=
  C.toZeroModeCertificate.rho_bound n

/-- The L19.5 inputs with the finite initial check. -/
noncomputable def toIdealZeroModeInputs : IdealZeroModeInputs :=
  C.toZeroModeCertificate.toIdealZeroModeInputs

/-- The `SubexpLoss` statement survives the finite replacement. -/
theorem subexpLoss : SubexpLoss C.toIdealZeroModeInputs.loss :=
  ZeroModeCertificate.subexpLoss C.toZeroModeCertificate

/-- The C5 `B = 2` slot survives the finite replacement. -/
theorem slot_le : ∀ᶠ n : ℕ in atTop,
    C.toIdealZeroModeInputs.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  ZeroModeCertificate.slot_le C.toZeroModeCertificate

end FiniteZeroModeCertificate

/-! ## 5. Absorbing a finite bound by adjusting `c₀` -/

/-- All residual data except the initial-segment inequality.  This is the input
on which the finite-maximum replacement is built. -/
structure ZeroModeResidualData (W : ℕ → ℝ) where
  /-- `W = log V` is nonnegative. -/
  W_nonneg : ∀ n, 0 ≤ W n
  /-- The discarded inner ellipse. -/
  ellipse : EllipseDiscardData W
  /-- The period-prime deletion. -/
  period : PeriodPrimeResidual W
  /-- The residual `ρ`. -/
  rho : ℕ → ℝ
  /-- `ρ` is nonnegative. -/
  rho_nonneg : ∀ n, 0 ≤ rho n
  /-- Internal exponent of the combined residual. -/
  c0 : ℝ
  /-- The internal exponent is positive. -/
  c0_pos : 0 < c0
  /-- Combined decay exponent. -/
  eta : ℝ
  /-- The combined decay is genuine. -/
  eta_pos : 0 < eta
  /-- The combined decay is no larger than the ellipse decay. -/
  eta_le_ellipse : eta ≤ 2 * ellipse.a
  /-- The combined decay is no larger than the period-prime decay. -/
  eta_le_period : eta ≤ period.cP
  /-- The period-prime exponent fits under `c0`. -/
  period_exp_le : period.cN / Real.log 2 ≤ c0
  /-- **Residual decomposition**. -/
  rho_eq : ∀ n, rho n = ellipse.discardedMass n + period.residual n
  /-- The threshold where the asymptotic constant is absorbed. -/
  S : ℝ
  /-- The threshold is nonnegative. -/
  S_nonneg : 0 ≤ S
  /-- The threshold dominates `log (16π) / c0`. -/
  S_ge_const : Real.log (16 * π) / c0 ≤ S
  /-- Explicit sample bound for the finite initial segment. -/
  N : ℕ
  /-- The sample bound covers every index with `scale n ≤ S`. -/
  covers : CoversInitialSegment S N

namespace ZeroModeResidualData

variable {W : ℕ → ℝ} (D : ZeroModeResidualData W)

theorem N_pos : 0 < D.N := by
  have h := D.covers 0 (by simpa [scale] using D.S_nonneg)
  exact h

/-- The finite maximum of `ρ` on the initial segment. -/
noncomputable def finiteMaxRho : ℝ :=
  (initialFinset D.S D.N).sup' (initialFinset_nonempty D.S_nonneg D.N_pos) D.rho

theorem finiteMaxRho_nonneg : 0 ≤ D.finiteMaxRho := by
  unfold finiteMaxRho
  exact (D.rho_nonneg 0).trans
    (Finset.le_sup' D.rho (zero_mem_initialFinset D.S_nonneg D.N_pos))

theorem rho_le_finiteMaxRho {n : ℕ} (hn : n < D.N) (hnS : scale n ≤ D.S) :
    D.rho n ≤ D.finiteMaxRho := by
  unfold finiteMaxRho
  exact Finset.le_sup' D.rho (mem_initialFinset.mpr ⟨hn, hnS⟩)

/-- Build the finite certificate at a chosen exponent `c0'`, once the
finite check at `c0'` is known. -/
noncomputable def toFinite (c0' : ℝ) (_hc0_le : D.c0 ≤ c0') (hc0_pos : 0 < c0')
    (hper : D.period.cN / Real.log 2 ≤ c0')
    (hS : Real.log (16 * π) / c0' ≤ D.S)
    (hfin : FiniteInitialCheck W D.rho c0' D.eta D.S D.N) :
    FiniteZeroModeResidualCertificate W where
  W_nonneg := D.W_nonneg
  ellipse := D.ellipse
  period := D.period
  rho := D.rho
  rho_nonneg := D.rho_nonneg
  c0 := c0'
  c0_pos := hc0_pos
  eta := D.eta
  eta_pos := D.eta_pos
  eta_le_ellipse := D.eta_le_ellipse
  eta_le_period := D.eta_le_period
  period_exp_le := hper
  rho_eq := D.rho_eq
  S := D.S
  S_nonneg := D.S_nonneg
  S_ge_const := hS
  N := D.N
  covers := D.covers
  rho_finite := hfin

/-- **The exact finite maximum suffices directly** for the residual bound,
without mentioning the bounded-quantifier form of the check. -/
theorem rho_bound_of_finiteMaxRatio
    (hmax : finiteMaxRatio W D.rho D.c0 D.eta D.S D.N ≤ 1) (n : ℕ) :
    D.rho n ≤ exp ((2 * D.c0) * scale n) * exp (-D.eta * W n) := by
  have hfin : FiniteInitialCheck W D.rho D.c0 D.eta D.S D.N :=
    (finiteCheck_iff_finiteMaxRatio_le_one D.covers).mpr hmax
  exact (D.toFinite D.c0 le_rfl D.c0_pos D.period_exp_le D.S_ge_const hfin).rho_bound n

/-- **Constant adjustment on a nonnegative initial segment.**  If `scale` is
nonnegative on the finite segment, then the finite check is automatic once the
zero-scale indices are checked explicitly: choose `c0'` at least the finite
maximum of the required exponents.  This is the precise sense in which the
finite check can be discharged by adjusting the constants.

The hypothesis `0 ≤ scale n` is not redundant: `scale` (as defined by the
ledger) is negative at `n = 2`, and increasing `c0` would move the exponential
bound there in the wrong direction.  Hence the exact finite check, rather than
an unconditional absorption claim, is the honest replacement for
`rho_initial`. -/
theorem exists_adjust_c0_of_nonneg_scale
    (hscale : ∀ n, n < D.N → 0 ≤ scale n)
    (hzero : ∀ n, n < D.N → scale n ≤ D.S → scale n = 0 →
      D.rho n ≤ exp (-D.eta * W n)) :
    ∃ c0' : ℝ, D.c0 ≤ c0' ∧ 0 < c0' ∧
      D.period.cN / Real.log 2 ≤ c0' ∧
      Real.log (16 * π) / c0' ≤ D.S ∧
      FiniteInitialCheck W D.rho c0' D.eta D.S D.N := by
  let B : ℝ := D.finiteMaxRho
  have hB0 : 0 ≤ B := D.finiteMaxRho_nonneg
  have hlog16 : 0 ≤ Real.log (16 * π) := by
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]
  by_cases hB : B = 0
  · -- All residual mass on the initial segment is zero; any admissible
    -- exponent works.
    let c0' : ℝ := max D.c0 1
    have hc0_le : D.c0 ≤ c0' := le_max_left _ _
    have hc0_pos : 0 < c0' := lt_of_lt_of_le D.c0_pos hc0_le
    have hper : D.period.cN / Real.log 2 ≤ c0' := D.period_exp_le.trans hc0_le
    have hS : Real.log (16 * π) / c0' ≤ D.S :=
      (div_le_div_of_nonneg_left hlog16 D.c0_pos hc0_le).trans D.S_ge_const
    refine ⟨c0', hc0_le, hc0_pos, hper, hS, ?_⟩
    intro n hn hnS
    have hrho : D.rho n ≤ 0 := by
      have hle := D.rho_le_finiteMaxRho hn hnS
      simpa [B, hB] using hle
    exact hrho.trans (le_of_lt (rhoRatio_denom_pos W D.rho c0' D.eta n))
  · -- `B > 0`: absorb the finite maximum into the exponent.
    have hBpos : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hB)
    let req : ℝ :=
      (Finset.range (D.N + 1)).sup' ⟨0, by simp⟩
        (fun n => if 0 < scale n then
          (Real.log B + D.eta * W n) / (2 * scale n) else 0)
    let c0' : ℝ := max (max D.c0 1) req
    have hc0_le : D.c0 ≤ c0' :=
      (le_max_left D.c0 1).trans (le_max_left _ _)
    have hc0_pos : 0 < c0' :=
      lt_of_lt_of_le (lt_of_lt_of_le D.c0_pos (le_max_left D.c0 1))
        (le_max_left _ _)
    have hper : D.period.cN / Real.log 2 ≤ c0' := D.period_exp_le.trans hc0_le
    have hS : Real.log (16 * π) / c0' ≤ D.S :=
      (div_le_div_of_nonneg_left hlog16 D.c0_pos hc0_le).trans D.S_ge_const
    refine ⟨c0', hc0_le, hc0_pos, hper, hS, ?_⟩
    intro n hn hnS
    by_cases hscale0 : scale n = 0
    · have hfac : exp (2 * c0' * scale n) = 1 := by
        rw [hscale0]
        ring_nf
        exact Real.exp_zero
      rw [hfac, one_mul]
      exact hzero n hn hnS hscale0
    · have hscale_pos : 0 < scale n :=
        lt_of_le_of_ne (hscale n hn) (Ne.symm hscale0)
      have hmem : n ∈ Finset.range (D.N + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_lt hn)
      have hle_req :
          (if 0 < scale n then
            (Real.log B + D.eta * W n) / (2 * scale n) else 0) ≤ req := by
        dsimp only [req]
        exact Finset.le_sup'
          (fun m => if 0 < scale m then
            (Real.log B + D.eta * W m) / (2 * scale m) else 0) hmem
      rw [if_pos hscale_pos] at hle_req
      have hreq_le : (Real.log B + D.eta * W n) / (2 * scale n) ≤ c0' :=
        hle_req.trans (le_max_right _ _)
      have hden : 0 < 2 * scale n := by positivity
      have hkey : Real.log B + D.eta * W n ≤ c0' * (2 * scale n) :=
        (div_le_iff₀ hden).mp hreq_le
      have hlogB : Real.log B ≤ 2 * c0' * scale n - D.eta * W n := by
        nlinarith
      have hexp : B ≤ exp (2 * c0' * scale n - D.eta * W n) :=
        (Real.log_le_iff_le_exp hBpos).mp hlogB
      calc
        D.rho n ≤ B := D.rho_le_finiteMaxRho hn hnS
        _ ≤ exp (2 * c0' * scale n - D.eta * W n) := hexp
        _ = exp (2 * c0' * scale n) * exp (-D.eta * W n) := by
          rw [show 2 * c0' * scale n - D.eta * W n =
            2 * c0' * scale n + (-D.eta * W n) by ring, Real.exp_add]

/-- The same adjustment, packaged as an actual finite residual certificate. -/
theorem exists_finite_certificate_of_nonneg_scale
    (hscale : ∀ n, n < D.N → 0 ≤ scale n)
    (hzero : ∀ n, n < D.N → scale n ≤ D.S → scale n = 0 →
      D.rho n ≤ exp (-D.eta * W n)) :
    ∃ F : FiniteZeroModeResidualCertificate W,
      F.rho = D.rho ∧ D.c0 ≤ F.c0 := by
  obtain ⟨c0', hc0_le, hc0_pos, hper, hS, hfin⟩ :=
    D.exists_adjust_c0_of_nonneg_scale hscale hzero
  exact ⟨D.toFinite c0' hc0_le hc0_pos hper hS hfin, rfl, hc0_le⟩

end ZeroModeResidualData

/-! ## Axiom audit -/

#print axioms mem_initialFinset
#print axioms exists_initialBound
#print axioms rhoInitial_iff_finiteCheck
#print axioms FinsetInitialCheck
#print axioms finsetInitialCheck_iff_finiteInitialCheck
#print axioms finiteCheck_iff_finiteMaxRatio_le_one
#print axioms finiteCheck_iff_finiteMaxRatioOn_le_one
#print axioms FiniteZeroModeResidualCertificate.toZeroModeResidualCertificate
#print axioms FiniteZeroModeResidualCertificate.rho_bound
#print axioms FiniteZeroModeResidualCertificate.rho_finite_finset
#print axioms FiniteZeroModeResidualCertificate.rho_finite_iff_max
#print axioms FiniteZeroModeCertificate.toZeroModeCertificate
#print axioms FiniteZeroModeCertificate.toIdealZeroModeInputs
#print axioms FiniteZeroModeCertificate.subexpLoss
#print axioms FiniteZeroModeCertificate.slot_le
#print axioms ZeroModeResidualData.finiteMaxRho
#print axioms ZeroModeResidualData.rho_bound_of_finiteMaxRatio
#print axioms ZeroModeResidualData.exists_adjust_c0_of_nonneg_scale
#print axioms ZeroModeResidualData.exists_finite_certificate_of_nonneg_scale

end Cogentic.RandomizedL19ZeroModeFinite
