import Cogentic.RandomizedL21_2Sub
import Cogentic.RandomizedProductPerron
import Cogentic.RandomizedSmoothDensity

set_option linter.style.haveILetI false

/-!
# L21.2: the Perron / Fourier / tent-smoothing reduction

`Cogentic.RandomizedL21_2Sub` isolates the five paper-level analytic statements
of the smooth-numbers-near-centres estimate:

* `perronShift` (Perron at `Re s = 2/3` for the twisted prime sum),
* `fourierSupBound` (the partial-summation Fourier-gap bound),
* `plancherelSplit` (the three-range Plancherel split),
* `tentSmoothing` (the Chebyshev/tent comparison),
* `densityNormalization` (the smooth-count density normalization).

This file reduces them where the reduction is structural or elementary, and
keeps only the genuinely analytic zeta/Fourier/smooth-count statements as
explicit sub-`Prop`s.

## What is reduced

1. **Plancherel split** (`plancherelSplit`).  The squared `L²` term is
   *defined* as the sum of the three frequency contributions.  The range split
   is then the definitional inequality `l2Term ≤ low + middle + tail`; all
   analytic content is in `fourierLow`, `fourierMiddle`, `fourierTail`.  This
   matches the paper's Plancherel computation, where the split is the
   additivity of the frequency integral over `|t| ≤ 1`,
   `1 < |t| ≤ X³` and `|t| > X³`.
2. **Tent smoothing** (`tentSmoothing`).  The Chebyshev step is isolated as
   `tentChebyshev`:
   `badCount/(X+1) ≤ 4 (kΔ)² · l2Term`.
   The polynomial factor `(1+U)^{polyExp}` absorbs `4 (kΔ)²` for
   `polyExp ≥ 3`.  The absorption is *proved* here from the elementary bounds
   `kΔ = (U + (log 2)/2)/log k` and `1 ≤ log k` (which follows from
   `k ≥ e`), together with `U ≥ 3`.
3. **Density normalization** (`densityNormalization`) and the two zeta/Fourier
   inputs `perronShift`, `fourierSupBound` stay as explicit sub-`Prop`s.  The
   repository has character-side estimates
   (`RandomizedPrimeBinLogTwist.primeBin_mellin_from_critical_line`,
   `RandomizedProductPerron.*`, `RandomizedSmoothDensity.*`) but no
   principal-character/Riemann-zeta Perron shift, no partial-summation link
   from `twistedPrimeSum` to `fourierGap`, and no neighbourhood smooth-count
   theorem; those three are therefore the smallest explicit analytic inputs
   that remain.

The assembled reduction is

`L21_2PerronInputs.toReducedInputs : L21_2PerronInputs → L21_2ReducedInputs`.

It feeds `L21_2ReducedInputs.toRatedLeaf`, `toSubexpLeaf`, the `B = 2` ledger
slot, and the paper-assumption reassembly.  No `sorry`, `admit`, `axiom` or
`native_decide`; the loss is still `badCount/(X+1)`, never set to zero.
-/

noncomputable section

namespace Cogentic.RandomizedL21_2Perron

open Filter Real
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Sub
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedOneThirdAsymptotic

/-! ## The reduced bundle

Compared with `L21_2ReducedInputs`:

* `l2Term` is not a field; it is `lowTerm + middleTerm + tailTerm`;
* `tentSmoothing` is replaced by `tentChebyshev`, before the polynomial
  normalization;
* `polyExp ≥ 3` is recorded so the polynomial factor provably absorbs the
  `4 (kΔ)²` Chebyshev constant;
* `perronShift`, `fourierSupBound` and `densityNormalization` stay explicit. -/

structure L21_2PerronInputs where
  /-- The dyadic centre bound `X`. -/
  X : ℕ → ℝ
  /-- The stage-one constant `c` (the paper takes `c = 1/√2`). -/
  c : ℝ
  /-- Perron constant in the vertical error `O (v^{2/3} U^C)`. -/
  Kper : ℕ → ℝ
  /-- The absolute exponent `C` of the Perron/twisted-sum errors. -/
  Cper : ℝ
  /-- Exponent in `ε = e^{-a/3} U^{Ceps}`. -/
  Ceps : ℝ
  /-- The Fourier gap `μ̂ (t) - ν̂ (t)`. -/
  fourierGap : ℕ → ℝ → ℂ
  smoothCount : ℕ → ℝ
  badCount : ℕ → ℝ
  lowTerm : ℕ → ℝ
  middleTerm : ℕ → ℝ
  tailTerm : ℕ → ℝ
  /-- Exponent of the explicit polynomial factor `(1 + U)^{polyExp}`. -/
  polyExp : ℝ
  X_gt_one : ∀ n, 1 < X n
  c_pos : 0 < c
  c_le_one : c ≤ 1
  /-- `log X ≥ 3` for every band. -/
  U_ge_three : ∀ n, 3 ≤ bandLog X n
  Kper_nonneg : ∀ n, 0 ≤ Kper n
  Cper_ge_two : 2 ≤ Cper
  Ceps_nonneg : 0 ≤ Ceps
  /-- The polynomial factor `(1+U)^{polyExp}` dominates the Chebyshev
  normalization `4 (k Δ)²`.  The paper's factor has a positive power of
  `1 + U`; three is enough. -/
  polyExp_ge_three : 3 ≤ polyExp
  smoothCount_nonneg : ∀ n, 0 ≤ smoothCount n
  badCount_nonneg : ∀ n, 0 ≤ badCount n
  lowTerm_nonneg : ∀ n, 0 ≤ lowTerm n
  middleTerm_nonneg : ∀ n, 0 ≤ middleTerm n
  tailTerm_nonneg : ∀ n, 0 ≤ tailTerm n
  /-- **Perron at `Re s = 2/3`** (paper §1, "Twisted prime sum").  This is the
  smallest zeta-side analytic input: the repository has character-side
  estimates but no principal-character/Riemann-zeta Perron shift. -/
  perronShift : ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v →
    v ≤ smoothCutoff c X n → |t| ≤ X n ^ 3 →
      ‖twistedPrimeSum v t - twistedMain v t‖ ≤
        Kper n * (v ^ (2 / 3 : ℝ) * (bandLog X n) ^ Cper
          + v * (bandLog X n) ^ Cper / X n ^ 3
          + Real.sqrt v * (Real.log (2 * v)) ^ 2)
  /-- **Twisted prime sum by partial summation** (paper §1).  This is the
  smallest Fourier-side analytic input: the repository does not formalise the
  Abel step from `twistedPrimeSum` to `fourierGap`. -/
  fourierSupBound : ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, |t| ≤ X n ^ 3 →
    ‖fourierGap n t‖ ≤ supEps X (aOf X c) Ceps n
  /-- `b ≤ B` eventually, the paper's prime-product cutoff below `B = c T_X`. -/
  b_le_B : ∀ᶠ n : ℕ in atTop, bOf X c n ≤ logCutoff c X n
  /-- **Chebyshev/tent smoothing before polynomial normalization.**  This is
  the tent comparison with the exact Chebyshev constant `4 (k Δ)²`; the
  polynomial factor is removed and proved below to dominate this constant. -/
  tentChebyshev : ∀ᶠ n : ℕ in atTop,
    badCount n / (X n + 1) ≤
      4 * (kOf X c n * spacingOf X c n) ^ 2 *
        (lowTerm n + middleTerm n + tailTerm n)
  /-- **The density-normalization count** (paper §1, last paragraph).  The
  neighbourhood of a good centre contains at least
  `√X exp (-R)` distinct smooth integers.  Kept as the smallest explicit
  smooth-count input: the existing `RandomizedSmoothDensity` strip lower bounds
  are for a wider prime-bin strip, not for the `√p` neighbourhood. -/
  densityNormalization : ∀ᶠ n : ℕ in atTop,
    Real.sqrt (X n) *
        Real.exp (-(representationLog (kOf X c) (spacingOf X c) (bOf X c) n)) ≤
      smoothCount n
  /-- **Low frequency** (`|t| ≤ 1`). -/
  fourierLow : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    lowTerm n ≤ Real.exp (-(((2 * c) / 3) - δ) * paperRate X n)
  /-- **Middle frequency** (`1 < |t| ≤ X³`). -/
  fourierMiddle : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    middleTerm n ≤ Real.exp (-((1 / c) - δ) * paperRate X n)
  /-- **High frequency** (`|t| > X³`). -/
  fourierTail : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    tailTerm n ≤ Real.exp (-δ * paperRate X n)
  /-- **Two-scale separation**. -/
  U_dominates : ∀ m : ℝ, 0 < m →
    ∀ᶠ n : ℕ in atTop, m * scale n ^ 2 ≤ bandLog X n
  /-- `log X ≤ exp (scale n)`. -/
  U_le_exp : ∀ᶠ n : ℕ in atTop, bandLog X n ≤ Real.exp (scale n)

namespace L21_2PerronInputs

variable (P : L21_2PerronInputs)

/-! ### Elementary parameter bounds

These are the only arithmetic facts needed to absorb the Chebyshev constant.
They are proved from `U ≥ 3`, `0 < c ≤ 1` and the explicit definitions, with no
asymptotic input. -/

/-- `U = log X`. -/
abbrev U (n : ℕ) : ℝ := UOf P.X n

/-- `T = sqrt (U log U)`. -/
abbrev T (n : ℕ) : ℝ := TOf P.X n

/-- `B = c T`. -/
abbrev B (n : ℕ) : ℝ := BOf P.c P.X n

/-- `r = (U + 1)/B`. -/
abbrev r (n : ℕ) : ℝ := rOf P.X P.c n

/-- `k = r (1 + 2/log r)`. -/
abbrev k (n : ℕ) : ℝ := kOf P.X P.c n

/-- `m = (U + (log 2)/2)/k`. -/
abbrev m (n : ℕ) : ℝ := mOf P.X P.c n

/-- `Δ = m/log k`. -/
abbrev spacing (n : ℕ) : ℝ := spacingOf P.X P.c n

/-- The Plancherel sum `low + middle + tail`. -/
abbrev l2 (n : ℕ) : ℝ := P.lowTerm n + P.middleTerm n + P.tailTerm n

theorem U_pos (n : ℕ) : 0 < P.U n := lt_of_lt_of_le (by norm_num) (P.U_ge_three n)

theorem U_gt_one (n : ℕ) : 1 < P.U n := lt_of_lt_of_le (by norm_num) (P.U_ge_three n)

theorem logU_pos (n : ℕ) : 0 < Real.log (P.U n) := Real.log_pos (P.U_gt_one n)

theorem T_pos (n : ℕ) : 0 < P.T n := by
  unfold T TOf paperRate
  exact Real.sqrt_pos.mpr (mul_pos (P.U_pos n) (P.logU_pos n))

theorem T_nonneg (n : ℕ) : 0 ≤ P.T n := (P.T_pos n).le

theorem T_sq (n : ℕ) : P.T n ^ 2 = P.U n * Real.log (P.U n) := by
  have h : 0 ≤ bandLog P.X n * Real.log (bandLog P.X n) :=
    mul_nonneg (P.U_pos n).le (P.logU_pos n).le
  show Real.sqrt (bandLog P.X n * Real.log (bandLog P.X n)) ^ 2 =
    bandLog P.X n * Real.log (bandLog P.X n)
  rw [Real.sq_sqrt h]

/-- `T = sqrt (U log U) ≤ U` for `U ≥ 1`. -/
theorem T_le_U (n : ℕ) : P.T n ≤ P.U n := by
  have hU : 0 ≤ P.U n := (P.U_pos n).le
  have hlog : Real.log (P.U n) ≤ P.U n := Real.log_le_self hU
  have hsq : P.U n * Real.log (P.U n) ≤ (P.U n) ^ 2 := by
    simpa [pow_two] using mul_le_mul_of_nonneg_left hlog hU
  calc
    P.T n = Real.sqrt (P.T n ^ 2) := (Real.sqrt_sq (P.T_nonneg n)).symm
    _ = Real.sqrt (P.U n * Real.log (P.U n)) := by rw [P.T_sq n]
    _ ≤ Real.sqrt ((P.U n) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = P.U n := Real.sqrt_sq hU

theorem B_pos (n : ℕ) : 0 < P.B n := by
  unfold B BOf logCutoff
  exact mul_pos P.c_pos (P.T_pos n)

theorem B_le_T (n : ℕ) : P.B n ≤ P.T n := by
  unfold B BOf logCutoff
  exact mul_le_of_le_one_left (P.T_nonneg n) P.c_le_one

/-- `r = (U+1)/B > 1`, since `B = c T ≤ T ≤ U < U + 1`. -/
theorem one_lt_r (n : ℕ) : 1 < P.r n := by
  have hB := P.B_pos n
  have hBT : P.B n ≤ P.T n := P.B_le_T n
  have hTU : P.T n ≤ P.U n := P.T_le_U n
  have hlt : P.B n < P.U n + 1 := by linarith [P.U_pos n]
  unfold r rOf
  rw [one_lt_div hB]
  exact hlt

theorem r_pos (n : ℕ) : 0 < P.r n := lt_trans zero_lt_one (P.one_lt_r n)

theorem logr_pos (n : ℕ) : 0 < Real.log (P.r n) := Real.log_pos (P.one_lt_r n)

/-- `k = r (1 + 2/log r) ≥ e` for all bands.  This is the only quantitative
input needed to make `log k ≥ 1`. -/
theorem exp_one_le_k (n : ℕ) : Real.exp 1 ≤ P.k n := by
  unfold k kOf
  have hr : 1 < P.r n := P.one_lt_r n
  have hr1 : 1 ≤ P.r n := le_of_lt hr
  have hlr : 0 < Real.log (P.r n) := P.logr_pos n
  by_cases h : Real.log (P.r n) ≤ 1
  · have hfac : 3 ≤ 1 + 2 / Real.log (P.r n) := by
      have h2 : 2 ≤ 2 / Real.log (P.r n) := by
        rw [le_div_iff₀ hlr]
        nlinarith
      linarith
    have hk3 : (3 : ℝ) ≤ P.r n * (1 + 2 / Real.log (P.r n)) := by
      calc
        (3 : ℝ) = 1 * 3 := by ring
        _ ≤ P.r n * (1 + 2 / Real.log (P.r n)) :=
          mul_le_mul hr1 hfac (by norm_num) (by positivity)
    exact le_trans Real.exp_one_lt_three.le hk3
  · have h1 : 1 ≤ Real.log (P.r n) := le_of_lt (lt_of_not_ge h)
    have hfac : 1 ≤ 1 + 2 / Real.log (P.r n) := by
      have h2 : 0 ≤ 2 / Real.log (P.r n) := div_nonneg (by norm_num) hlr.le
      linarith
    have hr_exp : Real.exp 1 ≤ P.r n := by
      calc
        Real.exp 1 ≤ Real.exp (Real.log (P.r n)) := Real.exp_le_exp.mpr h1
        _ = P.r n := Real.exp_log (P.r_pos n)
    calc
      Real.exp 1 = Real.exp 1 * 1 := by ring
      _ ≤ P.r n * (1 + 2 / Real.log (P.r n)) :=
        mul_le_mul hr_exp hfac (by norm_num) (P.r_pos n).le

theorem k_pos (n : ℕ) : 0 < P.k n := lt_of_lt_of_le (Real.exp_pos 1) (P.exp_one_le_k n)

/-- `1 ≤ log k`. -/
theorem logk_ge_one (n : ℕ) : 1 ≤ Real.log (P.k n) := by
  calc
    (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (P.k n) := Real.log_le_log (Real.exp_pos 1) (P.exp_one_le_k n)

theorem logk_pos (n : ℕ) : 0 < Real.log (P.k n) :=
  lt_of_lt_of_le zero_lt_one (P.logk_ge_one n)

/-- `k Δ = (U + (log 2)/2) / log k`, the explicit density-normalization
identity used in the polynomial absorption. -/
theorem k_mul_spacing (n : ℕ) :
    P.k n * P.spacing n = (P.U n + Real.log 2 / 2) / Real.log (P.k n) := by
  unfold spacing spacingOf mOf
  have hk : P.k n ≠ 0 := (P.k_pos n).ne'
  have hl : Real.log (P.k n) ≠ 0 := (P.logk_pos n).ne'
  field_simp [hk, hl]

/-- **Polynomial absorption of the Chebyshev constant.**  `4 (k Δ)² ≤ (1+U)³`
for every band.  Since `kΔ = (U + (log 2)/2)/log k`, `log k ≥ 1` and
`U ≥ 3`, this is the elementary estimate
`4 (U + (log 2)/2)² ≤ (U+1)³`. -/
theorem four_k_spacing_sq_le_cube (n : ℕ) :
    4 * (P.k n * P.spacing n) ^ 2 ≤ (1 + P.U n) ^ 3 := by
  have hk := P.k_mul_spacing n
  have hl : 1 ≤ Real.log (P.k n) := P.logk_ge_one n
  have hlpos : 0 < Real.log (P.k n) := P.logk_pos n
  have hl2 : 1 ≤ (Real.log (P.k n)) ^ 2 := by nlinarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2 : Real.log 2 / 2 < 1 := by
    have h := Real.log_two_lt_d9
    linarith
  have hnum_pos : 0 < P.U n + Real.log 2 / 2 := by linarith [P.U_pos n]
  have hnum_le : P.U n + Real.log 2 / 2 ≤ 1 + P.U n := by linarith
  have hsq : (P.k n * P.spacing n) ^ 2 ≤ (1 + P.U n) ^ 2 := by
    rw [hk, div_pow, div_le_iff₀ (pow_pos hlpos 2)]
    have h1 : (P.U n + Real.log 2 / 2) ^ 2 ≤ (1 + P.U n) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hnum_pos) hnum_le 2
    have h2 : (1 + P.U n) ^ 2 ≤ (1 + P.U n) ^ 2 * (Real.log (P.k n)) ^ 2 := by
      calc
        (1 + P.U n) ^ 2 = (1 + P.U n) ^ 2 * 1 := by ring
        _ ≤ (1 + P.U n) ^ 2 * (Real.log (P.k n)) ^ 2 :=
          mul_le_mul_of_nonneg_left hl2 (sq_nonneg _)
    exact h1.trans h2
  have h4 : 4 * (1 + P.U n) ^ 2 ≤ (1 + P.U n) ^ 3 := by
    have h3 : 3 ≤ P.U n := P.U_ge_three n
    have hU1 : 0 ≤ 1 + P.U n := by linarith
    nlinarith [sq_nonneg (1 + P.U n), mul_nonneg hU1 (sub_nonneg.mpr h3)]
  calc
    4 * (P.k n * P.spacing n) ^ 2 ≤ 4 * (1 + P.U n) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ ≤ (1 + P.U n) ^ 3 := h4

/-- `(1+U)³ ≤ (1+U)^{polyExp}` for `polyExp ≥ 3`. -/
theorem cube_le_polyFactor (n : ℕ) :
    (1 + P.U n) ^ 3 ≤ polyFactorOf P.polyExp P.X n := by
  have hbase : 1 ≤ 1 + P.U n := by linarith [P.U_pos n]
  have hbasepos : 0 < 1 + P.U n := by linarith [P.U_pos n]
  have hexp : (3 : ℝ) ≤ P.polyExp := by exact_mod_cast P.polyExp_ge_three
  have hpow : (1 + P.U n) ^ (3 : ℝ) ≤ (1 + P.U n) ^ P.polyExp :=
    Real.rpow_le_rpow_of_exponent_le hbase hexp
  calc
    (1 + P.U n) ^ 3 = (1 + P.U n) ^ (3 : ℝ) :=
      (Real.rpow_natCast (1 + P.U n) 3).symm
    _ ≤ (1 + P.U n) ^ P.polyExp := hpow
    _ = polyFactorOf P.polyExp P.X n := by
      unfold polyFactorOf
      rw [Real.rpow_def_of_pos hbasepos]
      ring_nf

/-- The polynomial factor dominates the Chebyshev constant `4 (k Δ)²`. -/
theorem eventually_four_k_spacing_sq_le_polyFactor :
    ∀ᶠ n : ℕ in atTop,
      4 * (P.k n * P.spacing n) ^ 2 ≤ polyFactorOf P.polyExp P.X n :=
  Eventually.of_forall fun n =>
    (P.four_k_spacing_sq_le_cube n).trans (P.cube_le_polyFactor n)

theorem l2_nonneg (n : ℕ) : 0 ≤ P.l2 n :=
  add_nonneg (add_nonneg (P.lowTerm_nonneg n) (P.middleTerm_nonneg n))
    (P.tailTerm_nonneg n)

/-! ### The reduction to `L21_2ReducedInputs` -/

/-- **The reduced bundle builds `L21_2ReducedInputs`.**  `l2Term` is the
Plancherel sum `low + middle + tail`, so `plancherelSplit` is definitional;
`tentSmoothing` follows from `tentChebyshev` and the proved polynomial
absorption.  The zeta, Fourier-gap and smooth-count inputs pass through. -/
def toReducedInputs : L21_2ReducedInputs where
  X := P.X
  c := P.c
  Kper := P.Kper
  Cper := P.Cper
  Ceps := P.Ceps
  fourierGap := P.fourierGap
  smoothCount := P.smoothCount
  badCount := P.badCount
  l2Term := P.l2
  lowTerm := P.lowTerm
  middleTerm := P.middleTerm
  tailTerm := P.tailTerm
  polyExp := P.polyExp
  X_gt_one := P.X_gt_one
  c_pos := P.c_pos
  c_le_one := P.c_le_one
  U_ge_three := P.U_ge_three
  Kper_nonneg := P.Kper_nonneg
  Cper_ge_two := P.Cper_ge_two
  Ceps_nonneg := P.Ceps_nonneg
  polyExp_nonneg := le_trans (by norm_num) P.polyExp_ge_three
  smoothCount_nonneg := P.smoothCount_nonneg
  badCount_nonneg := P.badCount_nonneg
  l2Term_nonneg := P.l2_nonneg
  perronShift := P.perronShift
  fourierSupBound := P.fourierSupBound
  b_le_B := P.b_le_B
  tentSmoothing := by
    filter_upwards [P.tentChebyshev, P.eventually_four_k_spacing_sq_le_polyFactor]
      with n hcheb hpoly
    exact hcheb.trans (mul_le_mul_of_nonneg_right hpoly (P.l2_nonneg n))
  densityNormalization := P.densityNormalization
  plancherelSplit := Eventually.of_forall fun _ => le_rfl
  fourierLow := P.fourierLow
  fourierMiddle := P.fourierMiddle
  fourierTail := P.fourierTail
  U_dominates := P.U_dominates
  U_le_exp := P.U_le_exp

/-- The parent `L21_2Inputs` assembled from the reduced inputs. -/
def toInputs : L21_2Inputs := L21_2ReducedInputs.toInputs P.toReducedInputs

/-- The L21.2 `RatedLeaf` produced by the reduced bundle. -/
def toRatedLeaf : RatedLeaf := L21_2ReducedInputs.toRatedLeaf P.toReducedInputs

/-- The `D^{-B}` form packaged as a `SubexpLeaf`. -/
def toSubexpLeaf : SubexpLeaf := L21_2ReducedInputs.toSubexpLeaf P.toReducedInputs

theorem loss_nonneg (n : ℕ) : 0 ≤ P.toReducedInputs.loss n :=
  P.toReducedInputs.loss_nonneg n

theorem loss_le_paper :
    ∀ᶠ n : ℕ in atTop,
      P.toReducedInputs.loss n ≤ Real.exp (-((P.c / 64) * paperRate P.X n)) :=
  P.toReducedInputs.loss_le_paper

theorem loss_le_ledger :
    ∀ᶠ n : ℕ in atTop,
      P.toReducedInputs.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  P.toReducedInputs.loss_le_ledger

/-- The `C5Leaf.ellipticExceptional` slot, when identified with this loss, is
eventually at most `exp (-2 * scale n)`. -/
theorem slot_le {slots : C5LossSlots}
    (h : slots .ellipticExceptional = P.toReducedInputs.loss) :
    ∀ᶠ n : ℕ in atTop,
      slots .ellipticExceptional n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  L21_2ReducedInputs.slot_le P.toReducedInputs h

/-- The eleven remaining leaves plus the reduced L21.2 inputs give the full
paper assumptions. -/
def paperAssumptions_of_perron
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (A : PaperAnalyticAssumptionsWithoutL21_2 E C) :
    PaperAnalyticAssumptions E C :=
  L21_2ReducedInputs.paperAssumptions_of_reduced P.toReducedInputs A

end L21_2PerronInputs

/-! ## Axiom audit -/

#print axioms Cogentic.RandomizedL21_2Perron.L21_2PerronInputs.T_le_U
#print axioms Cogentic.RandomizedL21_2Perron.L21_2PerronInputs.exp_one_le_k
#print axioms Cogentic.RandomizedL21_2Perron.L21_2PerronInputs.logk_ge_one
#print axioms Cogentic.RandomizedL21_2Perron.L21_2PerronInputs.k_mul_spacing
#print axioms Cogentic.RandomizedL21_2Perron.L21_2PerronInputs.four_k_spacing_sq_le_cube
#print axioms Cogentic.RandomizedL21_2Perron.L21_2PerronInputs.cube_le_polyFactor
#print axioms Cogentic.RandomizedL21_2Perron.L21_2PerronInputs.eventually_four_k_spacing_sq_le_polyFactor
#print axioms Cogentic.RandomizedL21_2Perron.L21_2PerronInputs.toReducedInputs
#print axioms Cogentic.RandomizedL21_2Perron.L21_2PerronInputs.toInputs
#print axioms Cogentic.RandomizedL21_2Perron.L21_2PerronInputs.toRatedLeaf
#print axioms Cogentic.RandomizedL21_2Perron.L21_2PerronInputs.toSubexpLeaf
#print axioms Cogentic.RandomizedL21_2Perron.L21_2PerronInputs.slot_le
#print axioms Cogentic.RandomizedL21_2Perron.L21_2PerronInputs.paperAssumptions_of_perron

end Cogentic.RandomizedL21_2Perron
