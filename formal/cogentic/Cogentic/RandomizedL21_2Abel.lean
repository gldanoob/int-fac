import Cogentic.RandomizedL21_2Fourier

set_option linter.style.haveILetI false

/-!
# L21.2: discharging the Abel / Perron constant / parameter fields

`Cogentic.RandomizedL21_2Fourier.L21_2FourierInputs` reduces the Fourier and
tent steps to explicit estimates, but still carries four elementary parameter
fields:

* `fourierGap_eq_abel`: an abstract `fourierGap` is the Abel transform
  `abelGapOf` of the twisted error;
* `Kper_bdd`: the Perron constant is bounded in `n`;
* `Ceps_ge`: `Ceps ≥ Cper + 2`;
* `k_le_U`: `k = kOf X c ≤ log X = U` eventually.

The present file removes all four by *defining* the objects:

* the Fourier gap is `abelGapOf X c n t`, so `fourierGap_eq_abel` is `rfl`;
* the Perron constant is a single real `KperAbs`, so `Kper_bdd` holds with
  `K = 3 KperAbs` (and `KperAbs ≥ 0` is recorded once);
* the exponent is `Ceps = Cper + 2`, so `Ceps_ge` is `rfl` and
  `Ceps_nonneg` follows from `2 ≤ Cper`;
* `k ≤ U` is *proved* from the explicit definitions
  `k = r (1 + 2/log r)`, `r = (U+1)/(c T)`, `T = sqrt (U log U)` and the
  growth `U → ∞` supplied by `U_dominates`.  The proof first shows
  `r → ∞` (so eventually `log r ≥ 1` and the factor `1 + 2/log r ≤ 3`),
  and then uses `T → ∞` to get `3 r = 3(U+1)/(cT) ≤ U`.

The resulting bundle `L21_2AbelInputs` builds `L21_2FourierInputs`, hence also
the Perron, reduced, ledger and paper-assumption bundles.  No `sorry`, `admit`,
`axiom` or `native_decide` is used; the loss remains the genuine quotient
`badCount/(X+1)`.
-/

noncomputable section

namespace Cogentic.RandomizedL21_2Abel

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Sub
open Cogentic.RandomizedL21_2Perron
open Cogentic.RandomizedL21_2Fourier
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedOneThirdAsymptotic

/-! ## The bundle with the elementary fields discharged -/

/-- `L21_2FourierInputs` with the four elementary parameter fields removed.

Compared with `L21_2FourierInputs`:

* `fourierGap` is not a field: it is *defined* as `abelGapOf X c`;
* `Kper : ℕ → ℝ` is replaced by a single absolute real `KperAbs`;
* `Ceps` is not a field: it is defined as `Cper + 2`;
* `Kper_bdd`, `fourierGap_eq_abel`, `Ceps_ge`, `Ceps_nonneg` and `k_le_U`
  are proved below from these definitions and `U_dominates`.

The genuinely analytic inputs (`perronShift`, `b_le_B`, the density count, the
three frequency bounds and `tentMeanSquare`) are unchanged. -/
structure L21_2AbelInputs where
  /-- The dyadic centre bound `X`. -/
  X : ℕ → ℝ
  /-- The stage-one constant `c` (the paper takes `c = 1/√2`). -/
  c : ℝ
  /-- The **absolute** Perron constant in the vertical error
  `O (v^{2/3} U^C)`; independent of `n`. -/
  KperAbs : ℝ
  /-- The absolute exponent `C` of the Perron/twisted-sum errors. -/
  Cper : ℝ
  smoothCount : ℕ → ℝ
  lowTerm : ℕ → ℝ
  middleTerm : ℕ → ℝ
  tailTerm : ℕ → ℝ
  /-- Exponent of the explicit polynomial factor `(1 + U)^{polyExp}`. -/
  polyExp : ℝ
  /-- The size of the finite centre sample. -/
  N : ℕ → ℕ
  /-- The explicit smoothed-density discrepancy at each sampled centre. -/
  deficit : (n : ℕ) → Fin (N n) → ℝ
  X_gt_one : ∀ n, 1 < X n
  c_pos : 0 < c
  c_le_one : c ≤ 1
  /-- `log X ≥ 3` for every band. -/
  U_ge_three : ∀ n, 3 ≤ bandLog X n
  /-- The absolute Perron constant is nonnegative. -/
  KperAbs_nonneg : 0 ≤ KperAbs
  Cper_ge_two : 2 ≤ Cper
  polyExp_ge_three : 3 ≤ polyExp
  smoothCount_nonneg : ∀ n, 0 ≤ smoothCount n
  lowTerm_nonneg : ∀ n, 0 ≤ lowTerm n
  middleTerm_nonneg : ∀ n, 0 ≤ middleTerm n
  tailTerm_nonneg : ∀ n, 0 ≤ tailTerm n
  /-- The finite centre sample is nonempty. -/
  N_pos : ∀ n, 0 < N n
  /-- **Perron at `Re s = 2/3`** with the absolute constant `KperAbs`. -/
  perronShift : ∀ᶠ n : ℕ in atTop, ∀ (v t : ℝ), 2 ≤ v →
    v ≤ smoothCutoff c X n → |t| ≤ X n ^ 3 →
      ‖twistedPrimeSum v t - twistedMain v t‖ ≤
        KperAbs * (v ^ (2 / 3 : ℝ) * (bandLog X n) ^ Cper
          + v * (bandLog X n) ^ Cper / X n ^ 3
          + Real.sqrt v * (Real.log (2 * v)) ^ 2)
  /-- The lower band edge satisfies `e^a ≥ 2`. -/
  a_ge_log_two : ∀ᶠ n : ℕ in atTop, Real.log 2 ≤ aOf X c n
  /-- `b ≤ B` eventually, the paper's prime-product cutoff below `B = c T_X`. -/
  b_le_B : ∀ᶠ n : ℕ in atTop, bOf X c n ≤ logCutoff c X n
  /-- **The density-normalization count** (unchanged paper input). -/
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
  /-- **Mean-square / Plancherel comparison**: the deficit energy at the sampled
  centres is at most the sum of the three frequency contributions. -/
  tentMeanSquare : ∀ᶠ n : ℕ in atTop,
    (1 / (N n : ℝ)) * ∑ i : Fin (N n), (deficit n i) ^ 2 ≤
      lowTerm n + middleTerm n + tailTerm n
  /-- **Two-scale separation**. -/
  U_dominates : ∀ m : ℝ, 0 < m →
    ∀ᶠ n : ℕ in atTop, m * scale n ^ 2 ≤ bandLog X n
  /-- `log X ≤ exp (scale n)`. -/
  U_le_exp : ∀ᶠ n : ℕ in atTop, bandLog X n ≤ Real.exp (scale n)

namespace L21_2AbelInputs

variable (A : L21_2AbelInputs)

/-! ### The explicit parameters -/

abbrev U (n : ℕ) : ℝ := UOf A.X n

abbrev T (n : ℕ) : ℝ := TOf A.X n

abbrev B (n : ℕ) : ℝ := BOf A.c A.X n

abbrev r (n : ℕ) : ℝ := rOf A.X A.c n

abbrev k (n : ℕ) : ℝ := kOf A.X A.c n

abbrev Kper (_n : ℕ) : ℝ := A.KperAbs

/-- The exponent `Ceps = Cper + 2` is *defined*, not assumed. -/
abbrev Ceps : ℝ := A.Cper + 2

/-- The Fourier gap is *defined* as the Abel transform of the twisted error. -/
def fourierGap (n : ℕ) (t : ℝ) : ℂ := abelGapOf A.X A.c n t

/-! ### Elementary parameter bounds -/

theorem U_pos (n : ℕ) : 0 < A.U n := lt_of_lt_of_le (by norm_num) (A.U_ge_three n)

theorem U_gt_one (n : ℕ) : 1 < A.U n := lt_of_lt_of_le (by norm_num) (A.U_ge_three n)

theorem logU_pos (n : ℕ) : 0 < Real.log (A.U n) := Real.log_pos (A.U_gt_one n)

theorem T_pos (n : ℕ) : 0 < A.T n := by
  unfold T TOf paperRate
  exact Real.sqrt_pos.mpr (mul_pos (A.U_pos n) (A.logU_pos n))

theorem T_nonneg (n : ℕ) : 0 ≤ A.T n := (A.T_pos n).le

theorem r_pos (n : ℕ) : 0 < A.r n := by
  have hden : 0 < A.c * A.T n := mul_pos A.c_pos (A.T_pos n)
  have hnum : 0 < A.U n + 1 := by linarith [A.U_pos n]
  unfold r rOf BOf logCutoff
  exact div_pos hnum hden

/-- `r = (U + 1)/(c T)` definitionally. -/
theorem r_eq (n : ℕ) : A.r n = (A.U n + 1) / (A.c * A.T n) := by
  unfold r rOf BOf logCutoff
  rfl

/-! ### Growth of the scale `U` and of `T` -/

/-- `U = log X → ∞`, from the two-scale separation `U_dominates`. -/
theorem U_grows : Tendsto A.U atTop atTop := by
  refine tendsto_atTop_mono' atTop (A.U_dominates 1 zero_lt_one) ?_
  simpa [pow_two, U] using scale_grows.atTop_mul_atTop₀ scale_grows

/-- `T = sqrt (U log U) → ∞`. -/
theorem T_grows : Tendsto A.T atTop atTop := by
  have h := Scale.tendsto_t (u := A.U) A.U_grows
  refine h.congr' ?_
  filter_upwards with n
  unfold Scale.t T TOf paperRate U UOf bandLog
  rfl

/-- `T/U → 0`, from `T = sqrt (U log U)`. -/
theorem T_div_U_tendsto_zero :
    Tendsto (fun n => A.T n / A.U n) atTop (nhds 0) := by
  have h := Scale.tendsto_t_div_u (u := A.U) A.U_grows
  refine h.congr' ?_
  filter_upwards with n
  unfold Scale.t T TOf paperRate U UOf bandLog
  rfl

/-- `U/T → ∞`, the reciprocal of `T/U → 0`. -/
theorem U_div_T_tendsto_atTop :
    Tendsto (fun n => A.U n / A.T n) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  by_cases hb : b ≤ 0
  · filter_upwards [A.U_grows.eventually_gt_atTop 0] with n hU0
    have hT0 : 0 < A.T n := A.T_pos n
    have hnonneg : 0 ≤ A.U n / A.T n := div_nonneg hU0.le hT0.le
    linarith
  · have hbpos : 0 < b := lt_of_not_ge hb
    have hsmall : ∀ᶠ n : ℕ in atTop, A.T n / A.U n < 1 / (b + 1) :=
      A.T_div_U_tendsto_zero.eventually
        (Iio_mem_nhds (one_div_pos.mpr (by linarith)))
    filter_upwards [hsmall, A.U_grows.eventually_gt_atTop 0] with n hn hU0
    have hT0 : 0 < A.T n := A.T_pos n
    have hb1 : 0 < b + 1 := by linarith
    rw [div_lt_iff₀ hU0] at hn
    have hfrac : b / (b + 1) < 1 := by
      rw [div_lt_one hb1]
      linarith
    have hbT : b * A.T n < A.U n := by
      calc
        b * A.T n < b * (1 / (b + 1) * A.U n) :=
          mul_lt_mul_of_pos_left hn hbpos
        _ = (b / (b + 1)) * A.U n := by field_simp [hb1.ne']
        _ < 1 * A.U n := mul_lt_mul_of_pos_right hfrac hU0
        _ = A.U n := by ring
    rw [le_div_iff₀ hT0]
    exact le_of_lt hbT

/-- `r = (U+1)/(c T) → ∞`. -/
theorem r_tendsto_atTop : Tendsto A.r atTop atTop := by
  have hlow : Tendsto (fun n => (1 / A.c) * (A.U n / A.T n)) atTop atTop :=
    Tendsto.const_mul_atTop (one_div_pos.mpr A.c_pos) A.U_div_T_tendsto_atTop
  refine tendsto_atTop_mono' atTop ?_ hlow
  filter_upwards [A.U_grows.eventually_gt_atTop 0] with n hU0
  have hden : 0 < A.c * A.T n := mul_pos A.c_pos (A.T_pos n)
  rw [A.r_eq n]
  calc
    (1 / A.c) * (A.U n / A.T n) = A.U n / (A.c * A.T n) := by field_simp
    _ ≤ (A.U n + 1) / (A.c * A.T n) :=
      div_le_div_of_nonneg_right (by linarith) hden.le

/-! ### `k ≤ U` -/

/-- **The coarse absorption `k ≤ log X`.**  From `r → ∞` the factor
`1 + 2/log r` is eventually at most `3`; from `T → ∞` the quotient
`3r = 3(U+1)/(cT)` is eventually at most `U`. -/
theorem k_le_U : ∀ᶠ n : ℕ in atTop, A.k n ≤ bandLog A.X n := by
  filter_upwards [A.r_tendsto_atTop.eventually_ge_atTop (Real.exp 1),
    A.T_grows.eventually_ge_atTop (4 / A.c)] with n hr hT
  have hU3 : 3 ≤ A.U n := A.U_ge_three n
  have hU0 : 0 < A.U n := lt_of_lt_of_le (by norm_num) hU3
  have hrpos : 0 < A.r n := A.r_pos n
  have hlogr1 : 1 ≤ Real.log (A.r n) := by
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (A.r n) := Real.log_le_log (Real.exp_pos 1) hr
  have hlogrpos : 0 < Real.log (A.r n) := lt_of_lt_of_le zero_lt_one hlogr1
  have hfactor : 1 + 2 / Real.log (A.r n) ≤ 3 := by
    have h2 : 2 / Real.log (A.r n) ≤ 2 := by
      rw [div_le_iff₀ hlogrpos]
      nlinarith
    linarith
  have hk : A.k n ≤ 3 * A.r n := by
    unfold k kOf
    calc
      A.r n * (1 + 2 / Real.log (A.r n)) ≤ A.r n * 3 :=
        mul_le_mul_of_nonneg_left hfactor (le_of_lt hrpos)
      _ = 3 * A.r n := by ring
  have hcT : 4 ≤ A.c * A.T n := by
    have hle : A.c * (4 / A.c) ≤ A.c * A.T n :=
      mul_le_mul_of_nonneg_left hT A.c_pos.le
    have h4 : A.c * (4 / A.c) = 4 := by field_simp [A.c_pos.ne']
    rw [h4] at hle
    exact hle
  have hrle : A.r n ≤ A.U n / 3 := by
    rw [A.r_eq n]
    rw [div_le_iff₀ (mul_pos A.c_pos (A.T_pos n))]
    have h1 : 4 * (A.U n / 3) ≤ (A.U n / 3) * (A.c * A.T n) := by
      calc
        4 * (A.U n / 3) = (A.U n / 3) * 4 := by ring
        _ ≤ (A.U n / 3) * (A.c * A.T n) :=
          mul_le_mul_of_nonneg_left hcT (by positivity)
    have h2 : A.U n + 1 ≤ 4 * (A.U n / 3) := by
      nlinarith
    linarith
  calc
    A.k n ≤ 3 * A.r n := hk
    _ ≤ 3 * (A.U n / 3) := by gcongr
    _ = A.U n := by ring
    _ = bandLog A.X n := rfl

/-! ### The four formerly abstract fields -/

/-- The absolute Perron constant is bounded: `K = 3 KperAbs` works. -/
theorem Kper_bdd : ∃ K : ℝ, ∀ n, 3 * A.Kper n ≤ K :=
  ⟨3 * A.KperAbs, fun _ => le_rfl⟩

/-- The abstract Fourier gap is the Abel transform by definition. -/
theorem fourierGap_eq_abel :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      A.fourierGap n t = abelGapOf A.X A.c n t := by
  filter_upwards with n t
  rfl

/-- `Ceps = Cper + 2` by definition. -/
theorem Ceps_ge : A.Cper + 2 ≤ A.Ceps := le_rfl

/-- `Ceps ≥ 0`, from `Cper ≥ 2`. -/
theorem Ceps_nonneg : 0 ≤ A.Ceps := by
  unfold Ceps
  linarith [A.Cper_ge_two]

/-! ### Assembly into `L21_2FourierInputs` -/

/-- The Abel bundle builds the Fourier bundle: the four removed fields are the
theorems above; every analytic field passes through. -/
def toFourierInputs : L21_2FourierInputs where
  X := A.X
  c := A.c
  Kper := A.Kper
  Cper := A.Cper
  Ceps := A.Ceps
  fourierGap := A.fourierGap
  smoothCount := A.smoothCount
  lowTerm := A.lowTerm
  middleTerm := A.middleTerm
  tailTerm := A.tailTerm
  polyExp := A.polyExp
  N := A.N
  deficit := A.deficit
  X_gt_one := A.X_gt_one
  c_pos := A.c_pos
  c_le_one := A.c_le_one
  U_ge_three := A.U_ge_three
  Kper_nonneg := fun _ => A.KperAbs_nonneg
  Cper_ge_two := A.Cper_ge_two
  Ceps_nonneg := A.Ceps_nonneg
  polyExp_ge_three := A.polyExp_ge_three
  smoothCount_nonneg := A.smoothCount_nonneg
  lowTerm_nonneg := A.lowTerm_nonneg
  middleTerm_nonneg := A.middleTerm_nonneg
  tailTerm_nonneg := A.tailTerm_nonneg
  N_pos := A.N_pos
  perronShift := A.perronShift
  Kper_bdd := A.Kper_bdd
  fourierGap_eq_abel := A.fourierGap_eq_abel
  Ceps_ge := A.Ceps_ge
  k_le_U := A.k_le_U
  a_ge_log_two := A.a_ge_log_two
  b_le_B := A.b_le_B
  densityNormalization := A.densityNormalization
  fourierLow := A.fourierLow
  fourierMiddle := A.fourierMiddle
  fourierTail := A.fourierTail
  tentMeanSquare := A.tentMeanSquare
  U_dominates := A.U_dominates
  U_le_exp := A.U_le_exp

/-- The Perron bundle, with the Fourier and tent steps already proved. -/
def toPerronInputs : L21_2PerronInputs := A.toFourierInputs.toPerronInputs

/-- The reduced L21.2 bundle. -/
def toReducedInputs : L21_2ReducedInputs := A.toFourierInputs.toReducedInputs

/-- The parent `L21_2Inputs`. -/
def toInputs : L21_2Inputs := A.toFourierInputs.toInputs

/-- The L21.2 `RatedLeaf`. -/
def toRatedLeaf : RatedLeaf := A.toFourierInputs.toRatedLeaf

/-- The `D^{-B}` form packaged as a `SubexpLeaf`. -/
def toSubexpLeaf : SubexpLeaf := A.toFourierInputs.toSubexpLeaf

theorem loss_nonneg (n : ℕ) : 0 ≤ A.toPerronInputs.toReducedInputs.loss n :=
  A.toPerronInputs.toReducedInputs.loss_nonneg n

theorem loss_le_ledger :
    ∀ᶠ n : ℕ in atTop,
      A.toPerronInputs.toReducedInputs.loss n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  A.toPerronInputs.toReducedInputs.loss_le_ledger

/-- The `C5Leaf.ellipticExceptional` slot, when identified with this loss, is
eventually at most `exp (-2 * scale n)`. -/
theorem slot_le {slots : C5LossSlots}
    (h : slots .ellipticExceptional = A.toPerronInputs.toReducedInputs.loss) :
    ∀ᶠ n : ℕ in atTop,
      slots .ellipticExceptional n ≤ Real.exp (-(2 : ℝ) * scale n) :=
  L21_2ReducedInputs.slot_le A.toPerronInputs.toReducedInputs h

/-- The eleven remaining leaves plus the Abel L21.2 inputs give the full paper
assumptions. -/
def paperAssumptions_of_abel
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ}
    (P : PaperAnalyticAssumptionsWithoutL21_2 E C) :
    PaperAnalyticAssumptions E C :=
  L21_2PerronInputs.paperAssumptions_of_perron A.toPerronInputs P

end L21_2AbelInputs

/-! ## Axiom audit -/

#print axioms Cogentic.RandomizedL21_2Abel.L21_2AbelInputs.Kper_bdd
#print axioms Cogentic.RandomizedL21_2Abel.L21_2AbelInputs.fourierGap_eq_abel
#print axioms Cogentic.RandomizedL21_2Abel.L21_2AbelInputs.Ceps_ge
#print axioms Cogentic.RandomizedL21_2Abel.L21_2AbelInputs.Ceps_nonneg
#print axioms Cogentic.RandomizedL21_2Abel.L21_2AbelInputs.k_le_U
#print axioms Cogentic.RandomizedL21_2Abel.L21_2AbelInputs.U_grows
#print axioms Cogentic.RandomizedL21_2Abel.L21_2AbelInputs.T_grows
#print axioms Cogentic.RandomizedL21_2Abel.L21_2AbelInputs.r_tendsto_atTop
#print axioms Cogentic.RandomizedL21_2Abel.L21_2AbelInputs.toFourierInputs
#print axioms Cogentic.RandomizedL21_2Abel.L21_2AbelInputs.toPerronInputs
#print axioms Cogentic.RandomizedL21_2Abel.L21_2AbelInputs.toReducedInputs
#print axioms Cogentic.RandomizedL21_2Abel.L21_2AbelInputs.toInputs
#print axioms Cogentic.RandomizedL21_2Abel.L21_2AbelInputs.toRatedLeaf
#print axioms Cogentic.RandomizedL21_2Abel.L21_2AbelInputs.toSubexpLeaf
#print axioms Cogentic.RandomizedL21_2Abel.L21_2AbelInputs.paperAssumptions_of_abel

end Cogentic.RandomizedL21_2Abel
