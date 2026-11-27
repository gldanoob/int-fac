import Cogentic.RandomizedL19SecondMoment
import Cogentic.RandomizedEllipticAndGaussian

/-!
# L19.5: the ideal zero mode and its residual

`Cogentic.RandomizedL19SecondMoment.IdealZeroModeInputs` assumes two analytic
fields of the narrow-width top second moment:

* `zero_mode_bound`, the ideal zero-mode estimate
  `zeroMode ≤ D ^ cz · μ_q ^ 2 + ρ · μ ^ 2`, whose polynomial part comes from the
  ellipse covering and whose residual is the discarded part of the Gaussian; and
* `rho_bound`, the period-prime removal
  `ρ ≤ D ^ cr · V ^ (-η)` of
  `research/keybreak-balanced-ideal-pair-audit.md` §"Prime factors of the period".

This file reduces both fields to smaller explicit objects.

## Layer cake and covering

`ZeroModeCoveringData` records a finite covering of the retained zero mode by
layer boxes: the `i`-th box carries mass `boxMass n i`, the retained zero mode is
the sum of the squared box masses, each box mass is at most
`exp (cb · scale n) · μ_q`, and the covering has at most `exp (cc · scale n)`
boxes.  The elementary layer-cake estimate

`∑ᵢ mᵢ² ≤ (#boxes) · (maxᵢ mᵢ)²`

then proves

`retained ≤ exp ((2 cb + cc) · scale n) · μ_q²`.

This is the finite form of "cover the ellipse by squares of side `≍ R / ϑ`; the
covering has `O(R² / ϑ)` boxes and the count of grid points in the whole covering
is at most a constant times the ellipse count" of the audit.

## Period primes

`PeriodPrimeResidual` records the paper's period-prime deletion.  The period is a
number `period n = V^{O(1)}`; the only exceptional primes are its prime factors,
whose number is at most `period n`.log2 by
`primeFactors_card_le_log2`; each contributes a mass at most `V ^ (-cP)`.
The arithmetic bound `log2 N ≤ log N / log 2` turns this into
`D ^{O(1)} · V ^ (-cP)`.

## Ellipse discard

`EllipseDiscardData` is exactly the hypothesis list of
`mahalanobis_2d_discarded_radius_rpow_le`: a translated Mahalanobis lattice with
mesh at most `V ^ (-a)`.  The theorem bounds the discarded inner-ellipse mass by
`8π V ^ (-2a)`, which is the `O(V ^ (-2a))` residual of the audit.

Nothing here is a `sorry`, an `admit`, an `axiom`, or `native_decide`.  No mass,
count, or error is set to zero; the only finite initial-segment input is the
explicit field `rho_initial`, which is the target inequality on the (finite)
region `scale ≤ S` where the asymptotic constants have not yet been absorbed.
-/

namespace Cogentic.RandomizedL19ZeroMode

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEllipticAndGaussian

/-! ## 1. Finite layer-cake and covering estimates -/

/-- **Layer cake with a uniform box bound.**  For nonnegative masses `m` on a
finite set, each at most `B`, the sum of squares is at most the number of boxes
times `B²`. -/
theorem sum_sq_le_card_mul_sq {ι : Type*} (s : Finset ι) (m : ι → ℝ) {B : ℝ}
    (_hB : 0 ≤ B) (hm : ∀ i ∈ s, 0 ≤ m i) (hle : ∀ i ∈ s, m i ≤ B) :
    ∑ i ∈ s, m i ^ 2 ≤ (s.card : ℝ) * B ^ 2 := by
  have hterm : ∀ i ∈ s, m i ^ 2 ≤ B ^ 2 := fun i hi =>
    pow_le_pow_left₀ (hm i hi) (hle i hi) 2
  calc
    ∑ i ∈ s, m i ^ 2 ≤ ∑ _i ∈ s, B ^ 2 := Finset.sum_le_sum hterm
    _ = (s.card : ℝ) * B ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- **Layer-cake Cauchy–Schwarz form.**  If the total mass is at most `M` and
each layer mass is at most `B`, then the second moment is at most `B · M`. -/
theorem sum_sq_le_bound_mul_sum {ι : Type*} (s : Finset ι) (m : ι → ℝ) {B M : ℝ}
    (hB : 0 ≤ B) (hm : ∀ i ∈ s, 0 ≤ m i) (hle : ∀ i ∈ s, m i ≤ B)
    (hM : ∑ i ∈ s, m i ≤ M) :
    ∑ i ∈ s, m i ^ 2 ≤ B * M := by
  calc
    ∑ i ∈ s, m i ^ 2 ≤ ∑ i ∈ s, m i * B := by
      refine Finset.sum_le_sum fun i hi => ?_
      have h0 := hm i hi
      have h1 := hle i hi
      nlinarith
    _ = (∑ i ∈ s, m i) * B := by rw [Finset.sum_mul]
    _ = B * (∑ i ∈ s, m i) := by ring
    _ ≤ B * M := mul_le_mul_of_nonneg_left hM hB

/-- **Covering count form.**  A covering with `N` boxes of uniform mass at most
`B` has second moment at most `N · B²`. -/
theorem covering_sum_sq_le {ι : Type*} (s : Finset ι) (m : ι → ℝ) {B N : ℝ}
    (hB : 0 ≤ B) (hN : (s.card : ℝ) ≤ N) (hm : ∀ i ∈ s, 0 ≤ m i)
    (hle : ∀ i ∈ s, m i ≤ B) :
    ∑ i ∈ s, m i ^ 2 ≤ N * B ^ 2 :=
  (sum_sq_le_card_mul_sq s m hB hm hle).trans
    (mul_le_mul_of_nonneg_right hN (sq_nonneg B))

/-- The exponent identity behind the covering bound:
`exp (cc s) · (exp (cb s) · μ)² = exp ((2 cb + cc) s) · μ²`. -/
theorem exp_mul_sq_exp {cb cc μ s : ℝ} :
    exp (cc * s) * (exp (cb * s) * μ) ^ 2 =
      exp ((2 * cb + cc) * s) * μ ^ 2 := by
  rw [mul_pow]
  have hsq : exp (cb * s) ^ 2 = exp ((2 * cb) * s) := by
    rw [pow_two, ← exp_add]
    congr 1
    ring_nf
  rw [hsq, ← mul_assoc, ← exp_add]
  congr 1
  ring_nf

/-- **The zero-mode covering data.**  A finite family of layer boxes with
nonnegative masses, a uniform box bound, and a covering-count bound. -/
structure ZeroModeCoveringData (W : ℕ → ℝ) where
  /-- The index type of the covering boxes. -/
  ι : Type*
  /-- The boxes are finite. -/
  fintype : Fintype ι
  /-- The boxes have decidable membership. -/
  decidableEq : DecidableEq ι
  /-- The retained covering boxes. -/
  boxes : Finset ι
  /-- The mass of the `i`-th box at ledger index `n`. -/
  boxMass : ℕ → ι → ℝ
  /-- Box masses are nonnegative. -/
  boxMass_nonneg : ∀ n i, i ∈ boxes → 0 ≤ boxMass n i
  /-- The retained zero-mode part. -/
  retained : ℕ → ℝ
  /-- The retained part is nonnegative. -/
  retained_nonneg : ∀ n, 0 ≤ retained n
  /-- The retained part is the layer-cake second moment of the box masses. -/
  retained_eq : ∀ n, retained n = ∑ i ∈ boxes, boxMass n i ^ 2
  /-- Exponent of the uniform box bound. -/
  cb : ℝ
  /-- Exponent of the covering count. -/
  cc : ℝ
  /-- The divided reference density `μ_q`. -/
  muq : ℕ → ℝ
  /-- `μ_q` is nonnegative. -/
  muq_nonneg : ∀ n, 0 ≤ muq n
  /-- `μ_q` is positive. -/
  muq_pos : ∀ n, 0 < muq n
  /-- **Box mass bound**: each box mass is at most
  `exp (cb · scale n) · μ_q`. -/
  boxMass_le : ∀ n i, i ∈ boxes → boxMass n i ≤ exp (cb * scale n) * muq n
  /-- The covering count. -/
  coverCount : ℕ → ℝ
  /-- The covering count is nonnegative. -/
  coverCount_nonneg : ∀ n, 0 ≤ coverCount n
  /-- The covering has at least as many boxes as the finite family. -/
  coverCount_ge : ∀ n, (boxes.card : ℝ) ≤ coverCount n
  /-- **Covering count bound**: `O(R² / ϑ) = D^{O(1)}` boxes. -/
  coverCount_le : ∀ n, coverCount n ≤ exp (cc * scale n)

namespace ZeroModeCoveringData

variable {W : ℕ → ℝ} (C : ZeroModeCoveringData W)

/-- **The retained zero-mode bound.**  The layer-cake estimate and the covering
count give `retained ≤ exp ((2 cb + cc) · scale n) · μ_q²`. -/
theorem retained_le (n : ℕ) :
    C.retained n ≤ exp ((2 * C.cb + C.cc) * scale n) * C.muq n ^ 2 := by
  have hB : 0 ≤ exp (C.cb * scale n) * C.muq n :=
    mul_nonneg (exp_pos _).le (C.muq_nonneg n)
  have hsum := covering_sum_sq_le C.boxes (fun i => C.boxMass n i) hB
    (C.coverCount_ge n) (C.boxMass_nonneg n) (C.boxMass_le n)
  have hcount : C.coverCount n ≤ exp (C.cc * scale n) := C.coverCount_le n
  have hbounded : C.coverCount n * (exp (C.cb * scale n) * C.muq n) ^ 2 ≤
      exp (C.cc * scale n) * (exp (C.cb * scale n) * C.muq n) ^ 2 :=
    mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
  calc
    C.retained n = ∑ i ∈ C.boxes, C.boxMass n i ^ 2 := C.retained_eq n
    _ ≤ C.coverCount n * (exp (C.cb * scale n) * C.muq n) ^ 2 := hsum
    _ ≤ exp (C.cc * scale n) * (exp (C.cb * scale n) * C.muq n) ^ 2 := hbounded
    _ = exp ((2 * C.cb + C.cc) * scale n) * C.muq n ^ 2 :=
      exp_mul_sq_exp

end ZeroModeCoveringData

/-! ## 2. Period-prime arithmetic -/

/-- **`log₂` versus the natural logarithm.**  For `N ≠ 0`,
`N.log2 ≤ log N / log 2`.  This is the arithmetic behind counting the prime
factors of the period: `N.primeFactors.card ≤ N.log2`. -/
theorem log2_le_log_div_log_two {N : ℕ} (hN : N ≠ 0) :
    (N.log2 : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (2 : ℕ) ^ N.log2 ≤ N := Nat.log2_self_le hN
  have hlog : Real.log (((2 : ℕ) ^ N.log2 : ℝ)) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hpow)
  have hcast : (((2 : ℕ) ^ N.log2 : ℝ)) = (2 : ℝ) ^ N.log2 := by norm_num
  rw [hcast, Real.log_pow] at hlog
  rw [le_div_iff₀ h2]
  exact hlog

/-- **The period-prime residual bound.**  If the period `N` is at most
`exp (cN · s)`, its number of prime factors is at most `log₂ N`, and each
exceptional prime contributes at most `ε ≤ exp (-cP · W)`, then the total
period-prime residual is at most
`exp ((cN / log 2) · s) · exp (-cP · W)`. -/
theorem period_prime_residual_le {N : ℕ} {cN cP W s ε : ℝ}
    (hN : N ≠ 0) (_hcN : 0 ≤ cN)
    (hNle : (N : ℝ) ≤ exp (cN * s))
    (hε0 : 0 ≤ ε) (hε : ε ≤ exp (-cP * W)) :
    ((N.primeFactors.card : ℝ)) * ε ≤
      exp ((cN / Real.log 2) * s) * exp (-cP * W) := by
  have hlog2 := log2_le_log_div_log_two hN
  have hlogN : Real.log (N : ℝ) ≤ cN * s :=
    (Real.log_le_iff_le_exp (by positivity)).mpr hNle
  have hcard : ((N.primeFactors.card : ℝ)) ≤ (N.log2 : ℝ) := by
    exact_mod_cast primeFactors_card_le_log2 N
  have hmain : ((N.primeFactors.card : ℝ)) ≤ (cN / Real.log 2) * s := by
    calc
      ((N.primeFactors.card : ℝ)) ≤ (N.log2 : ℝ) := hcard
      _ ≤ Real.log (N : ℝ) / Real.log 2 := hlog2
      _ ≤ (cN * s) / Real.log 2 :=
        div_le_div_of_nonneg_right hlogN (Real.log_pos (by norm_num)).le
      _ = (cN / Real.log 2) * s := by ring
  have hmain_nonneg : 0 ≤ (cN / Real.log 2) * s :=
    (Nat.cast_nonneg _).trans hmain
  calc
    ((N.primeFactors.card : ℝ)) * ε ≤ ((cN / Real.log 2) * s) * ε :=
      mul_le_mul_of_nonneg_right hmain hε0
    _ ≤ ((cN / Real.log 2) * s) * exp (-cP * W) :=
      mul_le_mul_of_nonneg_left hε hmain_nonneg
    _ ≤ exp ((cN / Real.log 2) * s) * exp (-cP * W) :=
      mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp ((cN / Real.log 2) * s)]) (by positivity)

/-- **The period-prime certificate.**  It records the period, its `D^{O(1)}`
size, the exceptional primes (its prime factors), and the `V^{-cP}` mass of
each exceptional prime. -/
structure PeriodPrimeResidual (W : ℕ → ℝ) where
  /-- The period `N`, of size `V^{O(1)}`. -/
  period : ℕ → ℕ
  /-- The period is nonzero, so its prime factors are defined. -/
  period_ne_zero : ∀ n, period n ≠ 0
  /-- Exponent of the period in `D = exp (scale)`. -/
  cN : ℝ
  /-- The period exponent is nonnegative. -/
  cN_nonneg : 0 ≤ cN
  /-- **Period size**: `period ≤ exp (cN · scale)`. -/
  period_poly : ∀ n, (period n : ℝ) ≤ exp (cN * scale n)
  /-- The period-prime mass exponent, `cP > 0`. -/
  cP : ℝ
  /-- The period-prime decay is genuine. -/
  cP_pos : 0 < cP
  /-- The mass contributed by one exceptional prime. -/
  exceptionMass : ℕ → ℝ
  /-- The exceptional-prime mass is nonnegative. -/
  exceptionMass_nonneg : ∀ n, 0 ≤ exceptionMass n
  /-- **One-prime mass**: each exceptional prime contributes at most
  `V^{-cP} = exp (-cP · W)`. -/
  exceptionMass_le : ∀ n, exceptionMass n ≤ exp (-cP * W n)
  /-- The residual mass contributed by the period primes. -/
  residual : ℕ → ℝ
  /-- The period-prime residual is nonnegative. -/
  residual_nonneg : ∀ n, 0 ≤ residual n
  /-- **Period-prime residual**: at most one mass per prime factor of the
  period. -/
  residual_le : ∀ n, residual n ≤ (period n).primeFactors.card * exceptionMass n

namespace PeriodPrimeResidual

variable {W : ℕ → ℝ} (P : PeriodPrimeResidual W)

/-- **The period-prime `rho` bound.** -/
theorem residual_bound (n : ℕ) :
    P.residual n ≤ exp ((P.cN / Real.log 2) * scale n) * exp (-P.cP * W n) := by
  refine (P.residual_le n).trans ?_
  exact period_prime_residual_le (P.period_ne_zero n) P.cN_nonneg
    (P.period_poly n) (P.exceptionMass_nonneg n) (P.exceptionMass_le n)

end PeriodPrimeResidual

/-! ## 3. The discarded inner ellipse -/

/-- The discarded-inner-ellipse mass ratio of the Mahalanobis lattice: the
Gaussian mass on lattice points of Mahalanobis radius `< V ^ (-a)`, divided by
the full lattice mass. -/
noncomputable def ellipseDiscardRatio
    (T₁ T₂ c₁ c₂ ρ h₁ h₂ V a : ℝ) (x₀ : ℝ × ℝ) : ℝ :=
  let lat : ℤ × ℤ → ℝ × ℝ :=
    fun k => (x₀.1 + (k.1 : ℝ) * h₁, x₀.2 + (k.2 : ℝ) * h₂)
  let rad : ℤ × ℤ → ℝ := fun k =>
    euclidNorm2 (mahalanobisCoord T₁ T₂ c₁ c₂ ρ (lat k))
  let g : ℤ × ℤ → ℝ := fun k => gaussian2D T₁ T₂ c₁ c₂ ρ (lat k)
  (∑' k : ℤ × ℤ, if rad k < V ^ (-a) then g k else 0) /
    (∑' k : ℤ × ℤ, g k)

/-- **The ellipse discard data.**  These are exactly the hypotheses of
`mahalanobis_2d_discarded_radius_rpow_le`, with `V = exp (W n)`. -/
structure EllipseDiscardData (W : ℕ → ℝ) where
  /-- First marginal scale. -/
  T₁ : ℕ → ℝ
  /-- Second marginal scale. -/
  T₂ : ℕ → ℝ
  /-- First Gaussian center. -/
  c₁ : ℕ → ℝ
  /-- Second Gaussian center. -/
  c₂ : ℕ → ℝ
  /-- Correlation. -/
  ρ : ℕ → ℝ
  /-- First lattice mesh. -/
  h₁ : ℕ → ℝ
  /-- Second lattice mesh. -/
  h₂ : ℕ → ℝ
  /-- Lattice origin. -/
  x₀ : ℕ → ℝ × ℝ
  /-- Discard exponent `a > 0`. -/
  a : ℝ
  /-- The discard exponent is positive. -/
  a_pos : 0 < a
  /-- Positivity of the first marginal scale. -/
  hT₁ : ∀ n, 0 < T₁ n
  /-- Positivity of the second marginal scale. -/
  hT₂ : ∀ n, 0 < T₂ n
  /-- The correlation is nondegenerate. -/
  hρ : ∀ n, |ρ n| < 1
  /-- Positivity of the first mesh. -/
  hh₁ : ∀ n, 0 < h₁ n
  /-- Positivity of the second mesh. -/
  hh₂ : ∀ n, 0 < h₂ n
  /-- The Mahalanobis mesh is small. -/
  hδ10 : ∀ n, mahalanobisMesh (T₁ n) (T₂ n) (ρ n) (h₁ n) (h₂ n) ≤ 1 / 10
  /-- The mesh is below the discarded radius `V ^ (-a)`. -/
  hδr : ∀ n, mahalanobisMesh (T₁ n) (T₂ n) (ρ n) (h₁ n) (h₂ n) ≤
    (exp (W n)) ^ (-a)
  /-- The discarded mass. -/
  discardedMass : ℕ → ℝ
  /-- The discarded mass is the actual lattice ratio. -/
  discardedMass_eq : ∀ n, discardedMass n =
    ellipseDiscardRatio (T₁ n) (T₂ n) (c₁ n) (c₂ n) (ρ n) (h₁ n) (h₂ n)
      (exp (W n)) a (x₀ n)

namespace EllipseDiscardData

variable {W : ℕ → ℝ} (E : EllipseDiscardData W)

/-- **The `O(V^{-2a})` discarded-ellipse bound.**  This is
`mahalanobis_2d_discarded_radius_rpow_le` at `V = exp (W n)`, with the
rpow exponent rewritten as `exp (-2 a W n)`. -/
theorem discardedMass_le (n : ℕ) :
    E.discardedMass n ≤ 8 * π * exp (-2 * E.a * W n) := by
  have hV : 0 < exp (W n) := exp_pos _
  have h := mahalanobis_2d_discarded_radius_rpow_le
    (E.T₁ n) (E.T₂ n) (E.c₁ n) (E.c₂ n) (E.ρ n) (E.h₁ n) (E.h₂ n)
    (exp (W n)) E.a (E.x₀ n) (E.hT₁ n) (E.hT₂ n) (E.hρ n) (E.hh₁ n)
    (E.hh₂ n) hV (E.hδ10 n) (E.hδr n)
  rw [E.discardedMass_eq n]
  dsimp only [ellipseDiscardRatio]
  refine h.trans_eq ?_
  have hrpow : (exp (W n)) ^ (-2 * E.a) = exp (-2 * E.a * W n) := by
    rw [Real.rpow_def_of_pos hV, Real.log_exp]
    congr 1
    ring
  rw [hrpow]

end EllipseDiscardData

/-! ## 4. The residual `ρ` from ellipse discard and period primes -/

/-- **The residual certificate.**  The residual `ρ` is the sum of the discarded
inner-ellipse mass and the period-prime mass.  The fields `c0`, `eta` and `S`
carry the exponent bookkeeping; `rho_initial` is the target inequality on the
finite region `scale ≤ S`, where the asymptotic constant `16π` need not yet have
been absorbed. -/
structure ZeroModeResidualCertificate (W : ℕ → ℝ) where
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
  /-- **Initial-segment check**: on `scale ≤ S` the residual already satisfies
  the final bound.  This is a finite, explicit condition; no loss is set to
  zero. -/
  rho_initial : ∀ n, scale n ≤ S →
    rho n ≤ exp ((2 * c0) * scale n) * exp (-eta * W n)

namespace ZeroModeResidualCertificate

variable {W : ℕ → ℝ} (R : ZeroModeResidualCertificate W)

/-- **The `rho_bound` field.**  The ellipse discard contributes `8π V^{-2a}`,
the period primes contribute `D^{O(1)} V^{-cP}`; the `16π` constant is absorbed
by `exp (c0 · scale)` on the large region, and `rho_initial` covers the finite
initial region. -/
theorem rho_bound (n : ℕ) :
    R.rho n ≤ exp ((2 * R.c0) * scale n) * exp (-R.eta * W n) := by
  by_cases hsmall : scale n ≤ R.S
  · exact R.rho_initial n hsmall
  · have hS : R.S < scale n := lt_of_not_ge hsmall
    have hs_nonneg : 0 ≤ scale n := le_of_lt (lt_of_le_of_lt R.S_nonneg hS)
    have hconst : 16 * π ≤ exp (R.c0 * scale n) := by
      have hlog_le : Real.log (16 * π) ≤ R.c0 * scale n := by
        have hS_ge := R.S_ge_const
        rw [div_le_iff₀ R.c0_pos] at hS_ge
        have hmul : Real.log (16 * π) ≤ R.c0 * R.S := by
          calc
            Real.log (16 * π) ≤ R.S * R.c0 := hS_ge
            _ = R.c0 * R.S := by ring
        exact hmul.trans (mul_lt_mul_of_pos_left hS R.c0_pos).le
      exact (Real.log_le_iff_le_exp (by positivity)).mp hlog_le
    have hdecay_ellipse : exp (-2 * R.ellipse.a * W n) ≤ exp (-R.eta * W n) := by
      apply exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_right R.eta_le_ellipse (R.W_nonneg n)
      nlinarith
    have hdecay_period : exp (-R.period.cP * W n) ≤ exp (-R.eta * W n) := by
      apply exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_right R.eta_le_period (R.W_nonneg n)
      nlinarith
    have hellipse : R.ellipse.discardedMass n ≤
        8 * π * exp (R.c0 * scale n) * exp (-R.eta * W n) := by
      calc
        R.ellipse.discardedMass n ≤ 8 * π * exp (-2 * R.ellipse.a * W n) :=
          R.ellipse.discardedMass_le n
        _ ≤ 8 * π * exp (-R.eta * W n) := by
          have h8 : 0 ≤ (8 : ℝ) * π := by positivity
          exact mul_le_mul_of_nonneg_left hdecay_ellipse h8
        _ ≤ 8 * π * exp (R.c0 * scale n) * exp (-R.eta * W n) := by
          have hexp1 : 1 ≤ exp (R.c0 * scale n) := by
            rw [← Real.exp_zero]
            exact exp_le_exp.mpr (mul_nonneg R.c0_pos.le hs_nonneg)
          have h8 : 0 ≤ (8 : ℝ) * π := by positivity
          have hbase : 0 ≤ exp (-R.eta * W n) := (exp_pos _).le
          have hstep : exp (-R.eta * W n) ≤
              exp (R.c0 * scale n) * exp (-R.eta * W n) := by
            calc
              exp (-R.eta * W n) = 1 * exp (-R.eta * W n) := by ring
              _ ≤ exp (R.c0 * scale n) * exp (-R.eta * W n) :=
                mul_le_mul_of_nonneg_right hexp1 hbase
          calc
            8 * π * exp (-R.eta * W n) =
                (8 * π) * exp (-R.eta * W n) := by ring
            _ ≤ (8 * π) *
                (exp (R.c0 * scale n) * exp (-R.eta * W n)) :=
              mul_le_mul_of_nonneg_left hstep h8
            _ = 8 * π * exp (R.c0 * scale n) * exp (-R.eta * W n) := by ring
    have hperiod : R.period.residual n ≤
        exp (R.c0 * scale n) * exp (-R.eta * W n) := by
      refine (R.period.residual_bound n).trans ?_
      have hexp_le : exp ((R.period.cN / Real.log 2) * scale n) ≤
          exp (R.c0 * scale n) := by
        apply exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right R.period_exp_le hs_nonneg
      exact mul_le_mul hexp_le hdecay_period (exp_pos _).le (exp_pos _).le
    calc
      R.rho n = R.ellipse.discardedMass n + R.period.residual n := R.rho_eq n
      _ ≤ 8 * π * exp (R.c0 * scale n) * exp (-R.eta * W n) +
            exp (R.c0 * scale n) * exp (-R.eta * W n) :=
        add_le_add hellipse hperiod
      _ = (8 * π + 1) * (exp (R.c0 * scale n) * exp (-R.eta * W n)) := by ring
      _ ≤ 16 * π * (exp (R.c0 * scale n) * exp (-R.eta * W n)) := by
        have hA : 0 ≤ exp (R.c0 * scale n) * exp (-R.eta * W n) := by positivity
        have hcoef : 8 * π + 1 ≤ 16 * π := by
          have hpi : 3 ≤ π := Real.pi_gt_three.le
          nlinarith
        exact mul_le_mul_of_nonneg_right hcoef hA
      _ ≤ exp (R.c0 * scale n) * (exp (R.c0 * scale n) * exp (-R.eta * W n)) := by
        have hA : 0 ≤ exp (R.c0 * scale n) * exp (-R.eta * W n) := by positivity
        exact mul_le_mul_of_nonneg_right hconst hA
      _ = exp ((2 * R.c0) * scale n) * exp (-R.eta * W n) := by
        rw [← mul_assoc, ← exp_add]
        congr 1
        ring_nf

end ZeroModeResidualCertificate

/-! ## 5. The full zero-mode certificate -/

/-- **The L19.5 certificate.**  It splits the ideal zero mode into a retained
part (bounded by the layer-cake covering data) and a discarded part (bounded by
`ρ μ²`), and supplies `ρ` from the ellipse and period-prime certificates. -/
structure ZeroModeCertificate (W : ℕ → ℝ) where
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
  /-- **Divided-strip ratio** `μ_q ≤ D^{cq} μ`, supplied by
  `RandomizedL19Muq.DividedStripRatioInputs.muq_le`. -/
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
  /-- The residual certificate for `ρ`. -/
  residual : ZeroModeResidualCertificate W
  /-- **Discarded zero-mode bound**: `discarded ≤ ρ μ²`. -/
  discarded_le : ∀ n, discarded n ≤ residual.rho n * mu n ^ 2

namespace ZeroModeCertificate

variable {W : ℕ → ℝ} (C : ZeroModeCertificate W)

/-- **`IdealZeroModeInputs.zero_mode_bound`.**  The retained part is bounded by
the layer-cake covering estimate with exponent `cz = 2 cb + cc`; the discarded
part is the `ρ μ²` term. -/
theorem zero_mode_bound (n : ℕ) :
    C.zeroMode n ≤
      exp ((2 * C.covering.cb + C.covering.cc) * scale n) * C.covering.muq n ^ 2 +
        C.residual.rho n * C.mu n ^ 2 := by
  rw [C.zeroMode_eq n]
  exact add_le_add (C.retained_eq n ▸ C.covering.retained_le n) (C.discarded_le n)

/-- **`IdealZeroModeInputs.rho_bound`**, with the exponent `2 c0` of the
combined residual certificate. -/
theorem rho_bound (n : ℕ) :
    C.residual.rho n ≤ exp ((2 * C.residual.c0) * scale n) *
      exp (-C.residual.eta * W n) :=
  C.residual.rho_bound n

/-- **The L19.5 inputs from the certificate.**  Both analytic fields
`zero_mode_bound` and `rho_bound` are now derived from the layer-cake covering
data, the ellipse discard, and the period-prime residual. -/
noncomputable def toIdealZeroModeInputs : IdealZeroModeInputs where
  W := W
  W_nonneg := C.W_nonneg
  W_dominates := C.W_dominates
  mu := C.mu
  mu_pos := C.mu_pos
  muq := C.covering.muq
  muq_pos := C.covering.muq_pos
  cq := C.cq
  muq_le := C.muq_le
  cz := 2 * C.covering.cb + C.covering.cc
  zeroMode := C.zeroMode
  zeroMode_nonneg := C.zeroMode_nonneg
  rho := C.residual.rho
  rho_nonneg := C.residual.rho_nonneg
  cr := 2 * C.residual.c0
  eta := C.residual.eta
  eta_pos := C.residual.eta_pos
  rho_bound := C.rho_bound
  zero_mode_bound := C.zero_mode_bound

/-- The `SubexpLoss` statement of L19.5 survives the replacement. -/
theorem subexpLoss : SubexpLoss C.toIdealZeroModeInputs.loss :=
  C.toIdealZeroModeInputs.subexpLoss

/-- The C5 `B = 2` slot survives the replacement. -/
theorem slot_le : ∀ᶠ n : ℕ in atTop,
    C.toIdealZeroModeInputs.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  C.toIdealZeroModeInputs.slot_le

end ZeroModeCertificate

/-! ## Axiom audit -/

#print axioms sum_sq_le_card_mul_sq
#print axioms sum_sq_le_bound_mul_sum
#print axioms covering_sum_sq_le
#print axioms exp_mul_sq_exp
#print axioms ZeroModeCoveringData.retained_le
#print axioms log2_le_log_div_log_two
#print axioms period_prime_residual_le
#print axioms PeriodPrimeResidual.residual_bound
#print axioms EllipseDiscardData.discardedMass_le
#print axioms ZeroModeResidualCertificate.rho_bound
#print axioms ZeroModeCertificate.zero_mode_bound
#print axioms ZeroModeCertificate.rho_bound
#print axioms ZeroModeCertificate.toIdealZeroModeInputs
#print axioms ZeroModeCertificate.subexpLoss
#print axioms ZeroModeCertificate.slot_le

end Cogentic.RandomizedL19ZeroMode
