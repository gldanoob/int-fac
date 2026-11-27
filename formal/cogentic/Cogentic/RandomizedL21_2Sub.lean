import Cogentic.RandomizedL21_2
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option linter.style.haveILetI false

/-!
# L21.2 sub-lemmas: elementary parameters and count arithmetic

`Cogentic.RandomizedL21_2` decomposes the smooth-numbers-near-centres estimate
into a structure `L21_2Inputs` of paper-level fields.  This file replaces the
*elementary* part of that structure by explicit definitions and proofs, and
keeps the genuinely analytic Perron/Fourier/tent-smoothing statements as named
`Prop`-valued fields.

The parameters are the manuscript's explicit choices:

* `U = log X`, `T = sqrt (U log U)`, `B = c T`;
* `r = (U + 1)/B` and `k = r (1 + 2/log r)`;
* `m = (U + (log 2)/2)/k`, `Δ = m/log k`, `a = m - Δ`, `b = m + Δ`.

The ceiling in the paper's `k = ⌈r (1 + 2/log r)⌉` only changes `k` by an
absolute constant; all three parameter identities `k log k = (1/(2c)+o(1)) T`,
`k log (b/(2Δ)) = o(T)` and `log (kΔ) = o(T)` are insensitive to it, so we use
the real-valued expression directly.  Every identity below is *proved*:

* `kLogK`, `kLogB`, `kDeltaLog` from the limits of `log`, `sqrt` and `log log`;
* the density-normalization arithmetic `R ≤ ((1/(2c)) + δ) T` from those three;
* the polynomial absorption `polyFactor ≤ exp (δ T)` for the explicit
  `polyFactor = exp (polyExp · log (1 + U))`.

The Perron shift, the twisted-prime-sum partial summation, the Plancherel
range split and the tent/density-normalization *counting* input remain explicit
paper-level fields.

The assembled reduction is `L21_2ReducedInputs.toInputs :
L21_2ReducedInputs → L21_2Inputs`, i.e. every field of the original L21.2
decomposition whose content is elementary is now discharged.  From it we
obtain

* `toRatedLeaf : L21_2ReducedInputs → RatedLeaf`,
* `toSubexpLeaf : L21_2ReducedInputs → SubexpLeaf` (the proved `D^{-B}` form),
* `slot_le`, the `C5Leaf.ellipticExceptional` ledger slot at `B = 2`,
* `paperAssumptions_of_reduced`, reassembling the full paper assumptions.

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

noncomputable section

namespace Cogentic.RandomizedL21_2Sub

open Filter Real
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedOneThirdAsymptotic

/-! ## Abstract asymptotic scale lemmas

Throughout this section `u → ∞` and `t = sqrt (u log u)`.  These are the only
analytic facts needed for the parameter arithmetic. -/

namespace Scale

variable {u : ℕ → ℝ}

/-- The paper's `T_X = sqrt (U log U)` as a function of the abstract scale. -/
def t (u : ℕ → ℝ) (n : ℕ) : ℝ := Real.sqrt (u n * Real.log (u n))

lemma eventually_pos (hu : Tendsto u atTop atTop) :
    ∀ᶠ n : ℕ in atTop, 0 < u n :=
  hu.eventually_gt_atTop 0

lemma eventually_gt_one (hu : Tendsto u atTop atTop) :
    ∀ᶠ n : ℕ in atTop, 1 < u n :=
  hu.eventually_gt_atTop 1

lemma eventually_ge_two (hu : Tendsto u atTop atTop) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ u n :=
  hu.eventually_ge_atTop 2

lemma tendsto_log (hu : Tendsto u atTop atTop) :
    Tendsto (fun n => Real.log (u n)) atTop atTop :=
  Real.tendsto_log_atTop.comp hu

/-- `T = sqrt (u log u)` tends to infinity. -/
lemma tendsto_t (hu : Tendsto u atTop atTop) : Tendsto (t u) atTop atTop := by
  unfold t
  exact Real.tendsto_sqrt_atTop.comp (hu.atTop_mul_atTop₀ (tendsto_log hu))

/-- `log u / sqrt (u log u) → 0`. -/
lemma tendsto_log_div_t (hu : Tendsto u atTop atTop) :
    Tendsto (fun n => Real.log (u n) / t u n) atTop (nhds 0) := by
  have hsq : Tendsto (fun n => Real.log (u n) / u n) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hu
  have hsqrt : Tendsto (fun n => Real.sqrt (Real.log (u n) / u n)) atTop (nhds 0) := by
    have hcont : Tendsto Real.sqrt (nhds (0 : ℝ)) (nhds (Real.sqrt 0)) :=
      Real.continuous_sqrt.tendsto 0
    simpa [Function.comp_def, Real.sqrt_zero] using hcont.comp hsq
  refine hsqrt.congr' ?_
  filter_upwards [eventually_gt_one hu] with n hn
  have hu0 : 0 < u n := lt_trans zero_lt_one hn
  have hl0 : 0 < Real.log (u n) := Real.log_pos hn
  have ht0 : 0 < t u n := by
    unfold t
    exact Real.sqrt_pos.mpr (mul_pos hu0 hl0)
  have hsqeq : (Real.log (u n) / t u n) ^ 2 = Real.log (u n) / u n := by
    unfold t
    rw [div_pow, Real.sq_sqrt (le_of_lt (mul_pos hu0 hl0))]
    field_simp [hu0.ne', hl0.ne']
  have hnn : 0 ≤ Real.log (u n) / t u n := div_nonneg hl0.le ht0.le
  exact (Real.sqrt_eq_iff_eq_sq (div_nonneg hl0.le hu0.le) hnn).mpr hsqeq.symm

/-- `log log u / log u → 0`. -/
lemma tendsto_loglog_div_log (hu : Tendsto u atTop atTop) :
    Tendsto (fun n => Real.log (Real.log (u n)) / Real.log (u n)) atTop (nhds 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (tendsto_log hu)

/-- `log T / log u → 1/2`. -/
lemma tendsto_log_t_div_log_u (hu : Tendsto u atTop atTop) :
    Tendsto (fun n => Real.log (t u n) / Real.log (u n)) atTop (nhds (1 / 2)) := by
  have hlog : Tendsto (fun n => Real.log (Real.log (u n)) / Real.log (u n))
      atTop (nhds 0) := tendsto_loglog_div_log hu
  have hlim : Tendsto
      (fun n => (1 / 2 : ℝ) * (1 + Real.log (Real.log (u n)) / Real.log (u n)))
      atTop (nhds (1 / 2)) := by
    simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).add hlog)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_one hu] with n hn
  have hu0 : 0 < u n := lt_trans zero_lt_one hn
  have hl0 : 0 < Real.log (u n) := Real.log_pos hn
  have hmul : 0 < u n * Real.log (u n) := mul_pos hu0 hl0
  have htpos : 0 < t u n := by
    unfold t
    exact Real.sqrt_pos.mpr hmul
  have hlogt : Real.log (t u n) =
      (1 / 2) * (Real.log (u n) + Real.log (Real.log (u n))) := by
    unfold t
    rw [Real.log_sqrt (le_of_lt hmul), Real.log_mul hu0.ne' hl0.ne']
    ring
  rw [hlogt]
  field_simp [hl0.ne']

/-- `log (1 + 1/u) / log u → 0`. -/
lemma tendsto_log_one_add_inv_div_log (hu : Tendsto u atTop atTop) :
    Tendsto (fun n => Real.log (1 + 1 / u n) / Real.log (u n)) atTop (nhds 0) := by
  have hinv : Tendsto (fun n => 1 / u n) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hu
  have harg : Tendsto (fun n => 1 + 1 / u n) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hinv
  have hnum : Tendsto (fun n => Real.log (1 + 1 / u n)) atTop (nhds 0) := by
    have h := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp harg
    simpa [Function.comp_def] using h
  exact hnum.div_atTop (tendsto_log hu)

/-- `log (u + 1) / log u → 1`. -/
lemma tendsto_log_add_one_div_log (hu : Tendsto u atTop atTop) :
    Tendsto (fun n => Real.log (u n + 1) / Real.log (u n)) atTop (nhds 1) := by
  have hsplit : (fun n : ℕ => Real.log (u n + 1) / Real.log (u n)) =ᶠ[atTop]
      (fun n => 1 + Real.log (1 + 1 / u n) / Real.log (u n)) := by
    filter_upwards [eventually_gt_one hu] with n hn
    have hu0 : 0 < u n := lt_trans zero_lt_one hn
    have hl0 : 0 < Real.log (u n) := Real.log_pos hn
    have hargpos : 0 < 1 + 1 / u n := by positivity
    have h : u n + 1 = u n * (1 + 1 / u n) := by field_simp
    rw [h, Real.log_mul hu0.ne' hargpos.ne', add_div, div_self hl0.ne']
  have hg : Tendsto (fun n => 1 + Real.log (1 + 1 / u n) / Real.log (u n))
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_log_one_add_inv_div_log hu)
  exact Tendsto.congr' hsplit.symm hg

lemma tendsto_t_div_u (hu : Tendsto u atTop atTop) :
    Tendsto (fun n => t u n / u n) atTop (nhds 0) := by
  have hsq : Tendsto (fun n => Real.log (u n) / u n) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hu
  have hsqrt : Tendsto (fun n => Real.sqrt (Real.log (u n) / u n)) atTop (nhds 0) := by
    have hcont : Tendsto Real.sqrt (nhds (0 : ℝ)) (nhds (Real.sqrt 0)) :=
      Real.continuous_sqrt.tendsto 0
    simpa [Function.comp_def, Real.sqrt_zero] using hcont.comp hsq
  refine hsqrt.congr' ?_
  filter_upwards [eventually_gt_one hu] with n hn
  have hu0 : 0 < u n := lt_trans zero_lt_one hn
  have hl0 : 0 < Real.log (u n) := Real.log_pos hn
  have ht0 : 0 < t u n := by
    unfold t
    exact Real.sqrt_pos.mpr (mul_pos hu0 hl0)
  have hsqeq : (t u n / u n) ^ 2 = Real.log (u n) / u n := by
    unfold t
    rw [div_pow, Real.sq_sqrt (le_of_lt (mul_pos hu0 hl0))]
    field_simp [hu0.ne'] 
  have hnn : 0 ≤ t u n / u n := div_nonneg ht0.le hu0.le
  exact (Real.sqrt_eq_iff_eq_sq (div_nonneg hl0.le hu0.le) hnn).mpr hsqeq.symm

end Scale

/-! ## The manuscript's explicit parameter functions -/

/-- `U = log X`. -/
def UOf (X : ℕ → ℝ) (n : ℕ) : ℝ := bandLog X n

/-- `T = sqrt (U log U)`. -/
def TOf (X : ℕ → ℝ) (n : ℕ) : ℝ := paperRate X n

/-- `B = c T`. -/
def BOf (c : ℝ) (X : ℕ → ℝ) (n : ℕ) : ℝ := logCutoff c X n

/-- `r = (U + 1)/B`. -/
def rOf (X : ℕ → ℝ) (c : ℝ) (n : ℕ) : ℝ := (UOf X n + 1) / BOf c X n

/-- `k = r (1 + 2/log r)`: the paper's `k = ⌈r (1 + 2/log r)⌉` without the
harmless ceiling. -/
def kOf (X : ℕ → ℝ) (c : ℝ) (n : ℕ) : ℝ :=
  rOf X c n * (1 + 2 / Real.log (rOf X c n))

/-- `m = (U + (log 2)/2)/k`. -/
def mOf (X : ℕ → ℝ) (c : ℝ) (n : ℕ) : ℝ :=
  (UOf X n + Real.log 2 / 2) / kOf X c n

/-- `Δ = m/log k`. -/
def spacingOf (X : ℕ → ℝ) (c : ℝ) (n : ℕ) : ℝ :=
  mOf X c n / Real.log (kOf X c n)

/-- `a = m - Δ`. -/
def aOf (X : ℕ → ℝ) (c : ℝ) (n : ℕ) : ℝ :=
  mOf X c n - spacingOf X c n

/-- `b = m + Δ`. -/
def bOf (X : ℕ → ℝ) (c : ℝ) (n : ℕ) : ℝ :=
  mOf X c n + spacingOf X c n

/-- The explicit polynomial density-normalization factor `(1 + U)^{polyExp}`. -/
def polyFactorOf (polyExp : ℝ) (X : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp (polyExp * Real.log (1 + UOf X n))

/-! ## The reduced L21.2 inputs

Only the manuscript's genuinely paper-level estimates remain as fields.  The
parameters are no longer fields: they are the explicit functions above, and the
three identities `kLogK`, `kLogB`, `kDeltaLog` plus the polynomial absorption are
proved below. -/

structure L21_2ReducedInputs where
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
  l2Term : ℕ → ℝ
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
  polyExp_nonneg : 0 ≤ polyExp
  smoothCount_nonneg : ∀ n, 0 ≤ smoothCount n
  badCount_nonneg : ∀ n, 0 ≤ badCount n
  l2Term_nonneg : ∀ n, 0 ≤ l2Term n
  /-- **Perron at `Re s = 2/3`** (paper §1, "Twisted prime sum"). -/
  perronShift : ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v →
    v ≤ smoothCutoff c X n → |t| ≤ X n ^ 3 →
      ‖twistedPrimeSum v t - twistedMain v t‖ ≤
        Kper n * (v ^ (2 / 3 : ℝ) * (bandLog X n) ^ Cper
          + v * (bandLog X n) ^ Cper / X n ^ 3
          + Real.sqrt v * (Real.log (2 * v)) ^ 2)
  /-- **Twisted prime sum by partial summation** (paper §1). -/
  fourierSupBound : ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, |t| ≤ X n ^ 3 →
    ‖fourierGap n t‖ ≤ supEps X (aOf X c) Ceps n
  /-- `b ≤ B` eventually, the paper's prime-product cutoff below `B = c T_X`. -/
  b_le_B : ∀ᶠ n : ℕ in atTop, bOf X c n ≤ logCutoff c X n
  /-- **Tent smoothing and density normalization** (paper §1). -/
  tentSmoothing : ∀ᶠ n : ℕ in atTop,
    badCount n / (X n + 1) ≤ polyFactorOf polyExp X n * l2Term n
  /-- **The density-normalization count** (paper §1, last paragraph). -/
  densityNormalization : ∀ᶠ n : ℕ in atTop,
    Real.sqrt (X n) *
        Real.exp (-(representationLog (kOf X c) (spacingOf X c) (bOf X c) n)) ≤
      smoothCount n
  /-- **Plancherel range split**. -/
  plancherelSplit : ∀ᶠ n : ℕ in atTop,
    l2Term n ≤ lowTerm n + middleTerm n + tailTerm n
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

namespace L21_2ReducedInputs

variable (I : L21_2ReducedInputs)

/-- `U = log X`. -/
abbrev U (n : ℕ) : ℝ := UOf I.X n

/-- `T = sqrt (U log U)`. -/
abbrev T (n : ℕ) : ℝ := TOf I.X n

/-- `B = c T`. -/
abbrev B (n : ℕ) : ℝ := BOf I.c I.X n

/-- `r = (U + 1)/B`. -/
abbrev r (n : ℕ) : ℝ := rOf I.X I.c n

/-- `k = r (1 + 2/log r)`. -/
abbrev k (n : ℕ) : ℝ := kOf I.X I.c n

/-- `m = (U + (log 2)/2)/k`. -/
abbrev m (n : ℕ) : ℝ := mOf I.X I.c n

/-- `Δ = m/log k`. -/
abbrev spacing (n : ℕ) : ℝ := spacingOf I.X I.c n

/-- `a = m - Δ`. -/
abbrev a (n : ℕ) : ℝ := aOf I.X I.c n

/-- `b = m + Δ`. -/
abbrev b (n : ℕ) : ℝ := bOf I.X I.c n

/-- The explicit polynomial factor `(1 + U)^{polyExp}`. -/
abbrev polyFactor (n : ℕ) : ℝ := polyFactorOf I.polyExp I.X n

/-- The Fourier gap bound `ε = e^{-a/3} U^{Ceps}`. -/
abbrev eps (n : ℕ) : ℝ := supEps I.X I.a I.Ceps n

/-- The exceptional fraction of the dyadic band. -/
abbrev badFraction (n : ℕ) : ℝ := I.badCount n / (I.X n + 1)

/-- The L21.2 loss: the elliptic-exceptional deletion fraction. -/
abbrev loss (n : ℕ) : ℝ := I.badFraction n

/-! ### Elementary positivity -/

theorem U_ge_three' (n : ℕ) : 3 ≤ I.U n := I.U_ge_three n

theorem U_pos (n : ℕ) : 0 < I.U n := lt_of_lt_of_le (by norm_num) (I.U_ge_three' n)

theorem U_gt_one (n : ℕ) : 1 < I.U n := lt_of_lt_of_le (by norm_num) (I.U_ge_three' n)

theorem logU_pos (n : ℕ) : 0 < Real.log (I.U n) := Real.log_pos (I.U_gt_one n)

theorem T_pos (n : ℕ) : 0 < I.T n := by
  unfold T TOf paperRate
  exact Real.sqrt_pos.mpr (mul_pos (I.U_pos n) (I.logU_pos n))

theorem T_nonneg (n : ℕ) : 0 ≤ I.T n := (I.T_pos n).le

theorem B_pos (n : ℕ) : 0 < I.B n := by
  unfold B BOf logCutoff
  exact mul_pos I.c_pos (I.T_pos n)

theorem r_pos (n : ℕ) : 0 < I.r n := by
  unfold r rOf
  exact div_pos (by linarith [I.U_pos n]) (I.B_pos n)

theorem T_lt_U_add_one (n : ℕ) : I.T n < I.U n + 1 := by
  have hU0 : 0 < I.U n := I.U_pos n
  have hlog0 : 0 < Real.log (I.U n) := I.logU_pos n
  have hlogle : Real.log (I.U n) ≤ I.U n := Real.log_le_self hU0.le
  have hsq : I.T n ^ 2 = I.U n * Real.log (I.U n) := by
    unfold T TOf paperRate
    change Real.sqrt (I.U n * Real.log (I.U n)) ^ 2 =
      I.U n * Real.log (I.U n)
    rw [Real.sq_sqrt (mul_nonneg hU0.le hlog0.le)]
  have hlt : I.U n * Real.log (I.U n) < (I.U n + 1) ^ 2 := by
    nlinarith only [hlogle, hU0]
  have hTnn : 0 ≤ I.T n := I.T_nonneg n
  calc
    I.T n = Real.sqrt (I.T n ^ 2) := (Real.sqrt_sq hTnn).symm
    _ < Real.sqrt ((I.U n + 1) ^ 2) := Real.sqrt_lt_sqrt (sq_nonneg _) (by rw [hsq]; exact hlt)
    _ = I.U n + 1 := Real.sqrt_sq (by linarith)

theorem one_lt_r (n : ℕ) : 1 < I.r n := by
  have hB_eq : I.B n = I.c * I.T n := rfl
  have hcT : I.c * I.T n ≤ I.T n := by
    nlinarith only [I.c_le_one, I.T_pos n]
  unfold r rOf
  rw [one_lt_div (I.B_pos n), hB_eq]
  linarith [I.T_lt_U_add_one n]

theorem logr_pos (n : ℕ) : 0 < Real.log (I.r n) := Real.log_pos (I.one_lt_r n)

theorem one_lt_k (n : ℕ) : 1 < I.k n := by
  unfold k kOf
  have hr : 1 < I.r n := I.one_lt_r n
  have hl : 0 < Real.log (I.r n) := I.logr_pos n
  have hfac : 1 < 1 + 2 / Real.log (I.r n) := by
    have : 0 < 2 / Real.log (I.r n) := div_pos (by norm_num) hl
    linarith
  calc
    (1 : ℝ) = 1 * 1 := by ring
    _ < I.r n * 1 := by gcongr
    _ < I.r n * (1 + 2 / Real.log (I.r n)) := by gcongr

theorem k_pos (n : ℕ) : 0 < I.k n := lt_trans zero_lt_one (I.one_lt_k n)

theorem logk_pos (n : ℕ) : 0 < Real.log (I.k n) := Real.log_pos (I.one_lt_k n)

theorem m_pos (n : ℕ) : 0 < I.m n := by
  unfold m mOf
  apply div_pos
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith [I.U_pos n]
  · exact I.k_pos n

theorem spacing_pos (n : ℕ) : 0 < I.spacing n := by
  unfold spacing spacingOf
  exact div_pos (I.m_pos n) (I.logk_pos n)

theorem b_pos (n : ℕ) : 0 < I.b n := by
  unfold b bOf
  have hm := I.m_pos n
  have hsp := I.spacing_pos n
  linarith

/-! ### Growth of the scales -/

theorem T_sq (n : ℕ) : I.T n ^ 2 = I.U n * Real.log (I.U n) := by
  unfold T TOf paperRate
  change Real.sqrt (I.U n * Real.log (I.U n)) ^ 2 =
    I.U n * Real.log (I.U n)
  rw [Real.sq_sqrt (mul_nonneg (I.U_pos n).le (I.logU_pos n).le)]

theorem Scale_t_eq_T : Scale.t I.U = I.T := by
  funext n
  unfold Scale.t T TOf paperRate U UOf
  rfl

theorem U_grows : Tendsto I.U atTop atTop := by
  refine tendsto_atTop_mono' atTop (I.U_dominates 1 zero_lt_one) ?_
  simpa [pow_two, U] using scale_grows.atTop_mul_atTop₀ scale_grows

theorem T_grows : Tendsto I.T atTop atTop := by
  unfold T TOf paperRate
  show Tendsto (fun n => Real.sqrt (I.U n * Real.log (I.U n))) atTop atTop
  simpa [Function.comp_def] using
    Real.tendsto_sqrt_atTop.comp (I.U_grows.atTop_mul_atTop₀ (Scale.tendsto_log I.U_grows))

theorem tendsto_U_add_one_div_U :
    Tendsto (fun n => (I.U n + 1) / I.U n) atTop (nhds 1) := by
  have hinv : Tendsto (fun n => (I.U n)⁻¹) atTop (nhds 0) :=
    I.U_grows.inv_tendsto_atTop
  have h : Tendsto (fun n => 1 + (I.U n)⁻¹) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hinv
  refine h.congr' ?_
  filter_upwards [Eventually.of_forall I.U_pos] with n hU
  field_simp [hU.ne']

theorem tendsto_log_r_div_log_U :
    Tendsto (fun n => Real.log (I.r n) / Real.log (I.U n)) atTop (nhds (1 / 2)) := by
  have hu : Tendsto I.U atTop atTop := I.U_grows
  have hlogU : Tendsto (fun n => Real.log (I.U n)) atTop atTop := Scale.tendsto_log hu
  have hlogT : Tendsto (fun n => Real.log (I.T n) / Real.log (I.U n))
      atTop (nhds (1 / 2)) := by
    simpa [Scale.t, T, TOf, paperRate, U, UOf] using Scale.tendsto_log_t_div_log_u hu
  have hlogU1 : Tendsto (fun n => Real.log (I.U n + 1) / Real.log (I.U n))
      atTop (nhds 1) := Scale.tendsto_log_add_one_div_log hu
  have hconst : Tendsto (fun n => Real.log I.c / Real.log (I.U n)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hlogU
  have hlim : Tendsto
      (fun n => Real.log (I.U n + 1) / Real.log (I.U n)
        - Real.log I.c / Real.log (I.U n)
        - Real.log (I.T n) / Real.log (I.U n)) atTop (nhds (1 / 2)) := by
    have h := (hlogU1.sub hconst).sub hlogT
    convert h using 1
    ring_nf
  refine hlim.congr' ?_
  filter_upwards with n
  have hU1 : (0 : ℝ) < I.U n + 1 := by linarith [I.U_pos n]
  have hc : (0 : ℝ) < I.c := I.c_pos
  have hT : (0 : ℝ) < I.T n := I.T_pos n
  have hBdef : I.B n = I.c * I.T n := rfl
  show Real.log (I.U n + 1) / Real.log (I.U n)
      - Real.log I.c / Real.log (I.U n)
      - Real.log (I.T n) / Real.log (I.U n) = Real.log (I.r n) / Real.log (I.U n)
  rw [show I.r n = (I.U n + 1) / I.B n from rfl, hBdef,
    Real.log_div hU1.ne' (mul_pos hc hT).ne', Real.log_mul hc.ne' hT.ne']
  ring

theorem tendsto_log_r_atTop : Tendsto (fun n => Real.log (I.r n)) atTop atTop := by
  have hratio := I.tendsto_log_r_div_log_U
  have hquarter : ∀ᶠ n : ℕ in atTop,
      (1 / 4 : ℝ) < Real.log (I.r n) / Real.log (I.U n) :=
    (tendsto_order.mp hratio).1 (1 / 4) (by norm_num)
  have hlower : Tendsto (fun n => (1 / 4 : ℝ) * Real.log (I.U n)) atTop atTop :=
    (Scale.tendsto_log I.U_grows).const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ hlower
  filter_upwards [hquarter, Eventually.of_forall I.logU_pos] with n hq hl
  have hmul := mul_lt_mul_of_pos_right hq hl
  rw [div_mul_cancel₀ _ hl.ne'] at hmul
  exact hmul.le

theorem tendsto_k_div_r : Tendsto (fun n => I.k n / I.r n) atTop (nhds 1) := by
  have hinv : Tendsto (fun n => (Real.log (I.r n))⁻¹) atTop (nhds 0) :=
    I.tendsto_log_r_atTop.inv_tendsto_atTop
  have hfac : Tendsto (fun n => 1 + 2 * (Real.log (I.r n))⁻¹) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := (2 : ℝ))).mul hinv)
  refine hfac.congr' ?_
  filter_upwards [Eventually.of_forall I.r_pos] with n hr
  unfold k kOf
  field_simp [hr.ne']

theorem tendsto_log_k_div_log_r :
    Tendsto (fun n => Real.log (I.k n) / Real.log (I.r n)) atTop (nhds 1) := by
  have hinv : Tendsto (fun n => (Real.log (I.r n))⁻¹) atTop (nhds 0) :=
    I.tendsto_log_r_atTop.inv_tendsto_atTop
  have hfac : Tendsto (fun n => 1 + 2 * (Real.log (I.r n))⁻¹) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := (2 : ℝ))).mul hinv)
  have hlogfac : Tendsto (fun n => Real.log (1 + 2 * (Real.log (I.r n))⁻¹))
      atTop (nhds 0) := by
    have h := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hfac
    simpa [Function.comp_def] using h
  have hzero : Tendsto
      (fun n => Real.log (1 + 2 * (Real.log (I.r n))⁻¹) / Real.log (I.r n))
      atTop (nhds 0) :=
    hlogfac.div_atTop I.tendsto_log_r_atTop
  have hone : Tendsto
      (fun n => 1 + Real.log (1 + 2 * (Real.log (I.r n))⁻¹) / Real.log (I.r n))
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hzero
  refine hone.congr' ?_
  filter_upwards [Eventually.of_forall I.logr_pos] with n hl
  unfold k kOf
  have hr0 : I.r n ≠ 0 := (I.r_pos n).ne'
  have hfacpos : 0 < 1 + 2 / Real.log (I.r n) := by positivity
  rw [Real.log_mul hr0 hfacpos.ne']
  field_simp [hl.ne']

theorem tendsto_log_k_atTop : Tendsto (fun n => Real.log (I.k n)) atTop atTop := by
  have hratio := I.tendsto_log_k_div_log_r
  have hquarter : ∀ᶠ n : ℕ in atTop,
      (1 / 4 : ℝ) < Real.log (I.k n) / Real.log (I.r n) :=
    (tendsto_order.mp hratio).1 (1 / 4) (by norm_num)
  have hlower : Tendsto (fun n => (1 / 4 : ℝ) * Real.log (I.r n)) atTop atTop :=
    I.tendsto_log_r_atTop.const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ hlower
  filter_upwards [hquarter, Eventually.of_forall I.logr_pos] with n hq hl
  have hmul := mul_lt_mul_of_pos_right hq hl
  rw [div_mul_cancel₀ _ hl.ne'] at hmul
  exact hmul.le

theorem tendsto_log_k_div_log_U :
    Tendsto (fun n => Real.log (I.k n) / Real.log (I.U n)) atTop (nhds (1 / 2)) := by
  have h := I.tendsto_log_k_div_log_r.mul I.tendsto_log_r_div_log_U
  have hlim : Tendsto
      (fun n => (Real.log (I.k n) / Real.log (I.r n)) *
        (Real.log (I.r n) / Real.log (I.U n))) atTop (nhds (1 / 2)) := by
    convert h using 1
    ring_nf
  refine hlim.congr' ?_
  filter_upwards [Eventually.of_forall I.logr_pos] with n hl
  field_simp [hl.ne']

theorem tendsto_loglogk_div_log_U :
    Tendsto (fun n => Real.log (Real.log (I.k n)) / Real.log (I.U n))
      atTop (nhds 0) := by
  have h1 : Tendsto (fun n => Real.log (Real.log (I.k n)) / Real.log (I.k n))
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp I.tendsto_log_k_atTop
  have h := h1.mul I.tendsto_log_k_div_log_U
  have hlim : Tendsto
      (fun n => (Real.log (Real.log (I.k n)) / Real.log (I.k n)) *
        (Real.log (I.k n) / Real.log (I.U n))) atTop (nhds 0) := by
    simpa using h
  refine hlim.congr' ?_
  filter_upwards [Eventually.of_forall I.logk_pos] with n hl
  field_simp [hl.ne']

theorem tendsto_r_div_T : Tendsto (fun n => I.r n / I.T n) atTop (nhds 0) := by
  have hinvlog : Tendsto (fun n => (Real.log (I.U n))⁻¹) atTop (nhds 0) :=
    (Scale.tendsto_log I.U_grows).inv_tendsto_atTop
  have hprod : Tendsto
      (fun n => (1 / I.c) * ((I.U n + 1) / I.U n) * (Real.log (I.U n))⁻¹)
      atTop (nhds 0) := by
    have h := ((tendsto_const_nhds (x := 1 / I.c)).mul I.tendsto_U_add_one_div_U).mul
      hinvlog
    simpa using h
  refine hprod.congr' ?_
  filter_upwards [Eventually.of_forall I.U_pos, Eventually.of_forall I.logU_pos] with n hU hl
  have hT2 := I.T_sq n
  have hc : (0 : ℝ) < I.c := I.c_pos
  have hT : (0 : ℝ) < I.T n := I.T_pos n
  have hrw : I.r n = (I.U n + 1) / (I.c * I.T n) := rfl
  rw [hrw]
  calc
    (1 / I.c) * ((I.U n + 1) / I.U n) * (Real.log (I.U n))⁻¹
        = (I.U n + 1) / (I.c * (I.U n * Real.log (I.U n))) := by
          field_simp [hc.ne', hU.ne', hl.ne']
    _ = (I.U n + 1) / (I.c * I.T n ^ 2) := by rw [hT2]
    _ = ((I.U n + 1) / (I.c * I.T n)) / I.T n := by
          field_simp [hc.ne', hT.ne']

theorem tendsto_r_div_T_mul_logU :
    Tendsto (fun n => I.r n / I.T n * Real.log (I.U n)) atTop (nhds (1 / I.c)) := by
  have h : Tendsto (fun n => (1 / I.c) * ((I.U n + 1) / I.U n)) atTop (nhds (1 / I.c)) := by
    simpa using (tendsto_const_nhds (x := 1 / I.c)).mul I.tendsto_U_add_one_div_U
  refine h.congr' ?_
  filter_upwards [Eventually.of_forall I.U_pos, Eventually.of_forall I.logU_pos] with n hU hl
  have hT2 := I.T_sq n
  have hc : (0 : ℝ) < I.c := I.c_pos
  have hT : (0 : ℝ) < I.T n := I.T_pos n
  have hrw : I.r n = (I.U n + 1) / (I.c * I.T n) := rfl
  rw [hrw]
  calc
    (1 / I.c) * ((I.U n + 1) / I.U n)
        = (I.U n + 1) * Real.log (I.U n) /
            (I.c * (I.U n * Real.log (I.U n))) := by
          field_simp [hc.ne', hU.ne', hl.ne']
    _ = (I.U n + 1) * Real.log (I.U n) / (I.c * I.T n ^ 2) := by rw [hT2]
    _ = ((I.U n + 1) / (I.c * I.T n)) / I.T n * Real.log (I.U n) := by
          field_simp [hc.ne', hT.ne']

theorem tendsto_k_div_T : Tendsto (fun n => I.k n / I.T n) atTop (nhds 0) := by
  have h := I.tendsto_k_div_r.mul I.tendsto_r_div_T
  have hlim : Tendsto (fun n => (I.k n / I.r n) * (I.r n / I.T n)) atTop (nhds 0) := by
    simpa using h
  refine hlim.congr' ?_
  filter_upwards [Eventually.of_forall I.r_pos] with n hr
  field_simp [hr.ne']

theorem tendsto_k_div_T_mul_logU :
    Tendsto (fun n => I.k n / I.T n * Real.log (I.U n)) atTop (nhds (1 / I.c)) := by
  have h := I.tendsto_k_div_r.mul I.tendsto_r_div_T_mul_logU
  have hlim : Tendsto
      (fun n => (I.k n / I.r n) * (I.r n / I.T n * Real.log (I.U n)))
      atTop (nhds (1 / I.c)) := by
    convert h using 1
    ring_nf
  refine hlim.congr' ?_
  filter_upwards [Eventually.of_forall I.r_pos] with n hr
  field_simp [hr.ne']

theorem tendsto_log_one_add_logk_div_log_U :
    Tendsto (fun n => Real.log (1 + Real.log (I.k n)) / Real.log (I.U n))
      atTop (nhds 0) := by
  have hlogU := Scale.tendsto_log I.U_grows
  have hk1 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (I.k n) :=
    I.tendsto_log_k_atTop.eventually_ge_atTop 1
  have hupper : ∀ᶠ n : ℕ in atTop,
      Real.log (1 + Real.log (I.k n)) / Real.log (I.U n) ≤
        (Real.log 2 + Real.log (Real.log (I.k n))) / Real.log (I.U n) := by
    filter_upwards [hk1, Eventually.of_forall I.logU_pos] with n hk hl
    apply div_le_div_of_nonneg_right ?_ hl.le
    calc
      Real.log (1 + Real.log (I.k n)) ≤ Real.log (2 * Real.log (I.k n)) := by
        apply Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 2 + Real.log (Real.log (I.k n)) := by
        rw [Real.log_mul (by norm_num) (by linarith)]
  have hlower : ∀ᶠ n : ℕ in atTop,
      0 ≤ Real.log (1 + Real.log (I.k n)) / Real.log (I.U n) := by
    filter_upwards [hk1, Eventually.of_forall I.logU_pos] with n hk hl
    exact div_nonneg (Real.log_nonneg (by linarith)) hl.le
  have hbound : Tendsto
      (fun n => (Real.log 2 + Real.log (Real.log (I.k n))) / Real.log (I.U n))
      atTop (nhds 0) := by
    have hconst : Tendsto (fun n => Real.log 2 / Real.log (I.U n)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hlogU
    have h := hconst.add I.tendsto_loglogk_div_log_U
    convert h using 1
    · ext n
      rw [add_div]
    · ring_nf
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound hlower hupper

theorem b_div_two_spacing (n : ℕ) :
    I.b n / (2 * I.spacing n) = (1 + Real.log (I.k n)) / 2 := by
  simp only [b, bOf, spacing, spacingOf, mOf]
  have hk : I.k n ≠ 0 := (I.k_pos n).ne'
  have hl : Real.log (I.k n) ≠ 0 := (I.logk_pos n).ne'
  have hm : (I.U n + Real.log 2 / 2) ≠ 0 := by
    have := I.U_pos n
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have h2u : I.U n * 2 + Real.log 2 ≠ 0 := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith [I.U_pos n]
  field_simp [hk, hl, hm, h2u]
  ring

theorem tendsto_k_mul_log_b_ratio_div_T :
    Tendsto (fun n => I.k n * Real.log (I.b n / (2 * I.spacing n)) / I.T n)
      atTop (nhds 0) := by
  have hprod : Tendsto
      (fun n => ((I.k n / I.T n) * Real.log (I.U n)) *
        (Real.log (1 + Real.log (I.k n)) / Real.log (I.U n)))
      atTop (nhds 0) := by
    have h := I.tendsto_k_div_T_mul_logU.mul I.tendsto_log_one_add_logk_div_log_U
    simpa using h
  have hklog : Tendsto
      (fun n => (I.k n / I.T n) * Real.log (1 + Real.log (I.k n)))
      atTop (nhds 0) := by
    refine hprod.congr' ?_
    filter_upwards [Eventually.of_forall I.logU_pos] with n hl
    field_simp [hl.ne']
  have hk2 : Tendsto (fun n => (I.k n / I.T n) * Real.log 2) atTop (nhds 0) := by
    have h := I.tendsto_k_div_T.mul_const (Real.log 2)
    simpa using h
  have hmain : Tendsto
      (fun n => (I.k n / I.T n) * Real.log (1 + Real.log (I.k n)) -
        (I.k n / I.T n) * Real.log 2) atTop (nhds 0) := by
    simpa using hklog.sub hk2
  refine hmain.congr' ?_
  filter_upwards [Eventually.of_forall I.logk_pos] with n hl
  rw [I.b_div_two_spacing n, Real.log_div (by linarith) (by norm_num)]
  ring

theorem kLogB (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      I.k n * Real.log (I.b n / (2 * I.spacing n)) ≤ δ * I.T n := by
  have hlt : ∀ᶠ n : ℕ in atTop,
      I.k n * Real.log (I.b n / (2 * I.spacing n)) / I.T n < δ :=
    (tendsto_order.mp I.tendsto_k_mul_log_b_ratio_div_T).2 δ hδ
  filter_upwards [hlt] with n hn
  rw [div_lt_iff₀ (I.T_pos n)] at hn
  exact hn.le

theorem tendsto_r_mul_log_r_div_T :
    Tendsto (fun n => I.r n * Real.log (I.r n) / I.T n)
      atTop (nhds (1 / (2 * I.c))) := by
  have hprod : Tendsto
      (fun n => (1 / I.c) * ((I.U n + 1) / I.U n) *
        (Real.log (I.r n) / Real.log (I.U n)))
      atTop (nhds ((1 / I.c) * 1 * (1 / 2))) :=
    ((tendsto_const_nhds (x := 1 / I.c)).mul I.tendsto_U_add_one_div_U).mul
      I.tendsto_log_r_div_log_U
  have hlim : Tendsto
      (fun n => (1 / I.c) * ((I.U n + 1) / I.U n) *
        (Real.log (I.r n) / Real.log (I.U n)))
      atTop (nhds (1 / (2 * I.c))) := by
    convert hprod using 1
    field_simp [I.c_pos.ne']
  refine hlim.congr' ?_
  filter_upwards [Eventually.of_forall I.U_pos, Eventually.of_forall I.logU_pos]
    with n hU hl
  have hT2 := I.T_sq n
  have hc : (0 : ℝ) < I.c := I.c_pos
  have hT : (0 : ℝ) < I.T n := I.T_pos n
  have hrw : I.r n = (I.U n + 1) / (I.c * I.T n) := rfl
  calc
    (1 / I.c) * ((I.U n + 1) / I.U n) *
        (Real.log (I.r n) / Real.log (I.U n))
        = (I.U n + 1) * Real.log (I.r n) /
            (I.c * (I.U n * Real.log (I.U n))) := by
          field_simp [hc.ne', hU.ne', hl.ne']
    _ = (I.U n + 1) * Real.log (I.r n) / (I.c * I.T n ^ 2) := by rw [hT2]
    _ = ((I.U n + 1) / (I.c * I.T n)) * Real.log (I.r n) / I.T n := by
          field_simp [hc.ne', hT.ne']
    _ = I.r n * Real.log (I.r n) / I.T n := by rw [hrw]

theorem tendsto_k_mul_log_k_div_T :
    Tendsto (fun n => I.k n * Real.log (I.k n) / I.T n)
      atTop (nhds (1 / (2 * I.c))) := by
  have h1 : Tendsto
      (fun n => (I.k n / I.r n) * (Real.log (I.k n) / Real.log (I.r n)))
      atTop (nhds 1) := by
    have h := I.tendsto_k_div_r.mul I.tendsto_log_k_div_log_r
    simpa using h
  have h2 : Tendsto
      (fun n => ((I.k n / I.r n) * (Real.log (I.k n) / Real.log (I.r n))) *
        (I.r n * Real.log (I.r n) / I.T n))
      atTop (nhds (1 * (1 / (2 * I.c)))) :=
    h1.mul I.tendsto_r_mul_log_r_div_T
  have hlim : Tendsto
      (fun n => ((I.k n / I.r n) * (Real.log (I.k n) / Real.log (I.r n))) *
        (I.r n * Real.log (I.r n) / I.T n))
      atTop (nhds (1 / (2 * I.c))) := by
    simpa using h2
  refine hlim.congr' ?_
  filter_upwards [Eventually.of_forall I.r_pos, Eventually.of_forall I.logr_pos]
    with n hr hl
  field_simp [hr.ne', hl.ne']

theorem kLogK (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      I.k n * Real.log (I.k n) ≤ ((1 / (2 * I.c)) + δ) * I.T n := by
  have hlt : ∀ᶠ n : ℕ in atTop,
      I.k n * Real.log (I.k n) / I.T n < (1 / (2 * I.c)) + δ :=
    (tendsto_order.mp I.tendsto_k_mul_log_k_div_T).2 ((1 / (2 * I.c)) + δ)
      (by linarith)
  filter_upwards [hlt] with n hn
  rw [div_lt_iff₀ (I.T_pos n)] at hn
  exact hn.le

theorem k_mul_spacing (n : ℕ) :
    I.k n * I.spacing n = (I.U n + Real.log 2 / 2) / Real.log (I.k n) := by
  simp only [spacing, spacingOf, mOf]
  have hk : I.k n ≠ 0 := (I.k_pos n).ne'
  have hl : Real.log (I.k n) ≠ 0 := (I.logk_pos n).ne'
  field_simp [hk, hl]

theorem tendsto_log_U_add_log2_half_div_log_U :
    Tendsto (fun n => Real.log (I.U n + Real.log 2 / 2) / Real.log (I.U n))
      atTop (nhds 1) := by
  have hlogU := Scale.tendsto_log I.U_grows
  have hconst : Tendsto (fun n => (Real.log 2 / 2) / I.U n) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop I.U_grows
  have harg : Tendsto (fun n => 1 + (Real.log 2 / 2) / I.U n) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hconst
  have hlogarg : Tendsto (fun n => Real.log (1 + (Real.log 2 / 2) / I.U n))
      atTop (nhds 0) := by
    have h := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp harg
    simpa [Function.comp_def] using h
  have hzero : Tendsto
      (fun n => Real.log (1 + (Real.log 2 / 2) / I.U n) / Real.log (I.U n))
      atTop (nhds 0) :=
    hlogarg.div_atTop hlogU
  have hone : Tendsto
      (fun n => 1 + Real.log (1 + (Real.log 2 / 2) / I.U n) / Real.log (I.U n))
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hzero
  refine hone.congr' ?_
  filter_upwards [Eventually.of_forall I.U_pos, Eventually.of_forall I.logU_pos]
    with n hU hl
  have htpos : 0 < 1 + (Real.log 2 / 2) / I.U n := by positivity
  rw [show I.U n + Real.log 2 / 2 =
      I.U n * (1 + (Real.log 2 / 2) / I.U n) by field_simp]
  rw [Real.log_mul hU.ne' htpos.ne', add_div]
  field_simp [hl.ne']

theorem tendsto_log_k_spacing_add_div_T :
    Tendsto (fun n => (Real.log (I.k n * I.spacing n) + Real.log 40) / I.T n)
      atTop (nhds 0) := by
  have hlogU := Scale.tendsto_log I.U_grows
  have h1 : Tendsto
      (fun n => Real.log (I.U n + Real.log 2 / 2) / I.T n) atTop (nhds 0) := by
    have h := I.tendsto_log_U_add_log2_half_div_log_U.mul
      (Scale.tendsto_log_div_t I.U_grows)
    have hlim : Tendsto
        (fun n => (Real.log (I.U n + Real.log 2 / 2) / Real.log (I.U n)) *
          (Real.log (I.U n) / I.T n)) atTop (nhds 0) := by
      simpa [I.Scale_t_eq_T] using h
    refine hlim.congr' ?_
    filter_upwards [Eventually.of_forall I.logU_pos] with n hl
    field_simp [hl.ne']
  have h2 : Tendsto (fun n => Real.log (Real.log (I.k n)) / I.T n)
      atTop (nhds 0) := by
    have h := I.tendsto_loglogk_div_log_U.mul (Scale.tendsto_log_div_t I.U_grows)
    have hlim : Tendsto
        (fun n => (Real.log (Real.log (I.k n)) / Real.log (I.U n)) *
          (Real.log (I.U n) / I.T n)) atTop (nhds 0) := by
      simpa [I.Scale_t_eq_T] using h
    refine hlim.congr' ?_
    filter_upwards [Eventually.of_forall I.logU_pos] with n hl
    field_simp [hl.ne']
  have h3 : Tendsto (fun n => Real.log 40 / I.T n) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop I.T_grows
  have hmain : Tendsto
      (fun n => Real.log (I.U n + Real.log 2 / 2) / I.T n
        - Real.log (Real.log (I.k n)) / I.T n + Real.log 40 / I.T n)
      atTop (nhds 0) := by
    simpa using (h1.sub h2).add h3
  refine hmain.congr' ?_
  filter_upwards [Eventually.of_forall I.logk_pos] with n hl
  have hnum : 0 < I.U n + Real.log 2 / 2 := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith [I.U_pos n]
  rw [I.k_mul_spacing n, Real.log_div hnum.ne' hl.ne']
  ring

theorem kDeltaLog (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (I.k n * I.spacing n) + Real.log 40 ≤ δ * I.T n := by
  have hlt : ∀ᶠ n : ℕ in atTop,
      (Real.log (I.k n * I.spacing n) + Real.log 40) / I.T n < δ :=
    (tendsto_order.mp I.tendsto_log_k_spacing_add_div_T).2 δ hδ
  filter_upwards [hlt] with n hn
  rw [div_lt_iff₀ (I.T_pos n)] at hn
  exact hn.le

theorem polyAbsorbs (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, I.polyFactor n ≤ Real.exp (δ * I.T n) := by
  have hlog1U : Tendsto (fun n => Real.log (1 + I.U n) / Real.log (I.U n))
      atTop (nhds 1) := by
    simpa [add_comm] using Scale.tendsto_log_add_one_div_log I.U_grows
  have hprod : Tendsto
      (fun n => I.polyExp * (Real.log (1 + I.U n) / Real.log (I.U n)) *
        (Real.log (I.U n) / I.T n)) atTop (nhds 0) := by
    have h := ((tendsto_const_nhds (x := I.polyExp)).mul hlog1U).mul
      (Scale.tendsto_log_div_t I.U_grows)
    simpa [I.Scale_t_eq_T] using h
  have hratio : Tendsto (fun n => I.polyExp * Real.log (1 + I.U n) / I.T n)
      atTop (nhds 0) := by
    refine hprod.congr' ?_
    filter_upwards [Eventually.of_forall I.logU_pos] with n hl
    field_simp [hl.ne']
  have hlt : ∀ᶠ n : ℕ in atTop,
      I.polyExp * Real.log (1 + I.U n) / I.T n < δ :=
    (tendsto_order.mp hratio).2 δ hδ
  filter_upwards [hlt] with n hn
  rw [div_lt_iff₀ (I.T_pos n)] at hn
  unfold polyFactor polyFactorOf
  exact Real.exp_le_exp.mpr hn.le

theorem B_le_U : ∀ᶠ n : ℕ in atTop, I.B n ≤ I.U n / 3 := by
  have hTU : Tendsto (fun n => I.T n / I.U n) atTop (nhds 0) := by
    have h := Scale.tendsto_t_div_u I.U_grows
    convert h using 1
    ext n
    unfold Scale.t T TOf paperRate U UOf
    rfl
  have hcTU : Tendsto (fun n => I.c * (I.T n / I.U n)) atTop (nhds 0) := by
    have h := (tendsto_const_nhds (x := I.c)).mul hTU
    simpa using h
  have hev : ∀ᶠ n : ℕ in atTop, I.c * (I.T n / I.U n) < 1 / 3 :=
    (tendsto_order.mp hcTU).2 (1 / 3) (by norm_num)
  filter_upwards [hev] with n hn
  have hmul := mul_lt_mul_of_pos_right hn (I.U_pos n)
  have hmul' : I.c * I.T n < (1 / 3) * I.U n := by
    calc
      I.c * I.T n = I.c * (I.T n / I.U n) * I.U n := by
        rw [mul_assoc, div_mul_cancel₀ _ (I.U_pos n).ne']
      _ < (1 / 3) * I.U n := hmul
  have hB : I.B n = I.c * I.T n := rfl
  rw [hB]
  nlinarith

/-! ### Density-normalization arithmetic -/

theorem loss_nonneg (n : ℕ) : 0 ≤ I.loss n := by
  unfold loss badFraction
  exact div_nonneg (I.badCount_nonneg n) (by linarith [I.X_gt_one n])

theorem polyFactor_pos (n : ℕ) : 0 < I.polyFactor n := by
  unfold polyFactor polyFactorOf
  exact Real.exp_pos _

/-- The density-normalization log budget `R ≤ ((1/(2c)) + δ) T` from the three
parameter identities. -/
theorem representationLog_le (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      representationLog I.k I.spacing I.b n ≤ ((1 / (2 * I.c)) + δ) * I.T n := by
  have h3 : 0 < δ / 3 := by linarith
  filter_upwards [I.kLogK (δ / 3) h3, I.kLogB (δ / 3) h3,
    I.kDeltaLog (δ / 3) h3] with n hk hb hkd
  unfold representationLog
  nlinarith

/-- The manuscript's smooth-count lower bound, now derived from the reduced
density-normalization count and the proved parameter identities. -/
theorem smoothCount_ge (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      Real.sqrt (I.X n) * Real.exp (-((1 / (2 * I.c)) + δ) * I.T n) ≤
        I.smoothCount n := by
  filter_upwards [I.densityNormalization, I.representationLog_le δ hδ] with n hd hr
  refine (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.sqrt_nonneg _)).trans hd
  linarith

/-! ## Assembly into `L21_2Inputs` -/

/-- The reduced inputs satisfy every field of `L21_2Inputs`: the paper-level
analytic fields are passed through, and `k_pos`, `spacing_pos`, `b_pos`,
`k_gt_one`, `kLogK`, `kLogB`, `kDeltaLog`, `B_le_U` and `polyAbsorbs` are
proved above from the explicit parameter definitions. -/
def toInputs : L21_2Inputs where
  X := I.X
  c := I.c
  Kper := I.Kper
  Cper := I.Cper
  Ceps := I.Ceps
  fourierGap := I.fourierGap
  k := I.k
  m := I.m
  spacing := I.spacing
  a := I.a
  b := I.b
  smoothCount := I.smoothCount
  badCount := I.badCount
  l2Term := I.l2Term
  lowTerm := I.lowTerm
  middleTerm := I.middleTerm
  tailTerm := I.tailTerm
  polyFactor := I.polyFactor
  X_gt_one := I.X_gt_one
  c_pos := I.c_pos
  c_le_one := I.c_le_one
  Kper_nonneg := I.Kper_nonneg
  Cper_ge_two := I.Cper_ge_two
  Ceps_nonneg := I.Ceps_nonneg
  k_pos := I.k_pos
  spacing_pos := I.spacing_pos
  b_pos := I.b_pos
  smoothCount_nonneg := I.smoothCount_nonneg
  badCount_nonneg := I.badCount_nonneg
  l2Term_nonneg := I.l2Term_nonneg
  polyFactor_pos := I.polyFactor_pos
  perronShift := I.perronShift
  U_ge_three := Eventually.of_forall I.U_ge_three'
  b_le_B := I.b_le_B
  B_le_U := I.B_le_U
  fourierSupBound := I.fourierSupBound
  k_gt_one := Eventually.of_forall I.one_lt_k
  kLogK := I.kLogK
  kLogB := I.kLogB
  kDeltaLog := I.kDeltaLog
  tentSmoothing := I.tentSmoothing
  densityNormalization := I.densityNormalization
  plancherelSplit := I.plancherelSplit
  fourierLow := I.fourierLow
  fourierMiddle := I.fourierMiddle
  fourierTail := I.fourierTail
  polyAbsorbs := I.polyAbsorbs
  U_dominates := I.U_dominates
  U_le_exp := I.U_le_exp

theorem loss_le_paper :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-((I.c / 64) * I.T n)) :=
  (L21_2ReducedInputs.toInputs I).loss_le_paper

theorem loss_le_exp_neg (B : ℝ) (hB : 0 < B) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-B * scale n) :=
  (L21_2ReducedInputs.toInputs I).loss_le_exp_neg B hB

theorem loss_le_ledger :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  (L21_2ReducedInputs.toInputs I).loss_le_ledger

theorem badCount_le_polynomial (A : ℝ) (hA : 0 < A) :
    ∀ᶠ n : ℕ in atTop,
      I.badCount n ≤ 2 * I.X n * Real.exp (-(A * Real.log (I.U n))) :=
  (L21_2ReducedInputs.toInputs I).badCount_le_polynomial A hA

theorem smooth_numbers_near_centres (A δ : ℝ) (hA : 0 < A) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      I.badCount n ≤ 2 * I.X n * Real.exp (-(A * Real.log (I.U n))) ∧
        Real.sqrt (I.X n) * Real.exp (-((1 / (2 * I.c)) + δ) * I.T n) ≤
          I.smoothCount n :=
  (L21_2ReducedInputs.toInputs I).smooth_numbers_near_centres A δ hA hδ

/-- The L21.2 `RatedLeaf` produced by the reduced inputs. -/
def toRatedLeaf : RatedLeaf := L21_2Inputs.toRatedLeaf (L21_2ReducedInputs.toInputs I)

/-- The `D^{-B}` form also packages the same loss as a `SubexpLeaf`. -/
def toSubexpLeaf : SubexpLeaf where
  loss := I.loss
  loss_nonneg := I.loss_nonneg
  paper := I.loss_le_exp_neg

/-- The `C5Leaf.ellipticExceptional` slot, when identified with this loss, is
eventually at most `exp (-2 * scale n)`. -/
theorem slot_le {slots : C5LossSlots}
    (h : slots .ellipticExceptional = I.loss) :
    ∀ᶠ n : ℕ in atTop,
      slots .ellipticExceptional n ≤ Real.exp (-(2 : ℝ) * scale n) := by
  rw [h]
  exact I.loss_le_ledger

/-- The eleven remaining leaves plus the reduced L21.2 inputs give the full
paper assumptions. -/
def paperAssumptions_of_reduced
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (P : PaperAnalyticAssumptionsWithoutL21_2 E C) :
    PaperAnalyticAssumptions E C :=
  paperAssumptions_of_L21_2Inputs P (L21_2ReducedInputs.toInputs I)

end L21_2ReducedInputs

/-! ## Axiom audit -/

#print axioms Cogentic.RandomizedL21_2Sub.L21_2ReducedInputs.kLogK
#print axioms Cogentic.RandomizedL21_2Sub.L21_2ReducedInputs.kLogB
#print axioms Cogentic.RandomizedL21_2Sub.L21_2ReducedInputs.kDeltaLog
#print axioms Cogentic.RandomizedL21_2Sub.L21_2ReducedInputs.polyAbsorbs
#print axioms Cogentic.RandomizedL21_2Sub.L21_2ReducedInputs.B_le_U
#print axioms Cogentic.RandomizedL21_2Sub.L21_2ReducedInputs.representationLog_le
#print axioms Cogentic.RandomizedL21_2Sub.L21_2ReducedInputs.smoothCount_ge
#print axioms Cogentic.RandomizedL21_2Sub.L21_2ReducedInputs.toInputs
#print axioms Cogentic.RandomizedL21_2Sub.L21_2ReducedInputs.toRatedLeaf
#print axioms Cogentic.RandomizedL21_2Sub.L21_2ReducedInputs.toSubexpLeaf
#print axioms Cogentic.RandomizedL21_2Sub.L21_2ReducedInputs.slot_le
#print axioms Cogentic.RandomizedL21_2Sub.L21_2ReducedInputs.paperAssumptions_of_reduced

end Cogentic.RandomizedL21_2Sub
