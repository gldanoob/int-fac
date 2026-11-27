import Cogentic.RandomizedL20_2Saddle

set_option linter.style.haveILetI false

/-!
# L20.2: a concrete lower bound for the smooth reciprocal mass

`Cogentic.RandomizedL20_2Saddle` reduces the saddle mean to the explicit
logarithmic lower bound

`SmoothNumberMassLogLower X y α Λ η`,
i.e. `0 < η` and `η * Λ n ≤ log (∑_{m ≤ X, P⁺(m) ≤ y} m^(-α))`.

This file supplies the missing mass estimate from a counting estimate.  The
only pointwise input used is the elementary monotonicity of `m ↦ m^(-α)`:

* on the whole smooth set every term is at least `X^(-α)`, so
  `mass ≥ #smooth · X^(-α)`
  (`smoothNumberMass_ge_count_mul_endpoint`);
* on a smooth window `m ≤ T` every term is at least `T^(-α)`, so
  `mass ≥ #window · T^(-α)`
  (`smoothNumberMass_ge_windowCount_mul_rpow`).

Consequently the saddle-mean inequality reduces to a genuine counting
inequality.  The main reduction, `smoothNumberMassLogLower_of_windowCountLower`,
takes an explicit lower bound `R n ≤ log (#window)` and the arithmetic budget
`α log T + η log X ≤ R`.  Since the total smooth count is at most `X`, the same
budget with `T = X` gives `SmoothNumberMassLogLower` from the existing
`SmoothNumberCountLower` input plus `(α + η) log X ≤ c D log D`
(`smoothNumberMassLogLower_of_countLower`).

The density form `smoothNumberMassLogLower_of_windowDensity` consumes the
conclusion of the existing prime-bin construction,
`#window ≥ P^m · exp (-(1 + ε) u log u)`, and reduces the mass estimate to the
explicit arithmetic budget
`α log T + η log X + (1 + ε) u log u ≤ m log P`.

Two unconditional concrete instances are proved:

* `smoothNumberMassLogLower_selfSmooth` takes the self-smooth mass `y = X`:
  the smooth set is all integers in `[1, ⌊X⌋]`, the reciprocal mass is at least
  `√⌊X⌋`, and `η = 1/2` works;
* `smoothNumberMassLogLower_halfSmooth` takes the genuinely restricted cutoff
  `y = X/2`: every `m ≤ ⌊X/2⌋` is smooth, the reciprocal mass is at least
  `⌊X/2⌋ · X^(-1/4)`, and again `η = 1/2` works for `X ≥ 256`.

`paperSmoothMassLogLower` instantiates the self-smooth case at the manuscript's
scale `X = exp (max 0 (log D))`, and `saddlePointMeanLower_paperSmoothMass`
feeds it into the existing `SaddlePointMeanLower` reduction.

No `sorry`, `admit`, `axiom`, or `native_decide` is used, and no mass is set to
zero.
-/

namespace Cogentic.RandomizedL20_2SmoothMass

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedL20_2
open Cogentic.RandomizedL20_2Saddle
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## 1. The elementary mass/count inequalities -/

/-- The smooth-number count is positive, because `1` is smooth. -/
theorem smoothNumberCount_pos {X y : ℕ → ℝ} {n : ℕ} (hX : 1 ≤ X n) :
    0 < smoothNumberCount X y n := by
  unfold smoothNumberCount
  have hmem : 1 ∈ smoothNumberSet X y n := one_mem_smoothNumberSet (y := y) hX
  have hcard : 0 < (smoothNumberSet X y n).card := Finset.card_pos.mpr ⟨1, hmem⟩
  exact_mod_cast hcard

/-- The total smooth count is at most the endpoint `X`. -/
theorem smoothNumberCount_le_endpoint {X y : ℕ → ℝ} {n : ℕ} (hX : 1 ≤ X n) :
    smoothNumberCount X y n ≤ X n := by
  have hXpos : 0 ≤ X n := by linarith
  have hsub : smoothNumberSet X y n ⊆ Finset.Icc 1 ⌊X n⌋₊ :=
    Finset.filter_subset _ _
  have hcard : (smoothNumberSet X y n).card ≤ ⌊X n⌋₊ := by
    have h := Finset.card_le_card hsub
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at h
  calc
    smoothNumberCount X y n = ((smoothNumberSet X y n).card : ℝ) := rfl
    _ ≤ (⌊X n⌋₊ : ℝ) := by exact_mod_cast hcard
    _ ≤ X n := Nat.floor_le hXpos

/-- **Mass from the whole smooth set.**  Every smooth `m ≤ X` satisfies
`m^(-α) ≥ X^(-α)`, so the reciprocal mass is at least the count times the
uniform endpoint weight. -/
theorem smoothNumberMass_ge_count_mul_endpoint {X y α : ℕ → ℝ} {n : ℕ}
    (hX : 1 ≤ X n) (hα : 0 ≤ α n) :
    smoothNumberCount X y n * (X n) ^ (-(α n)) ≤ smoothNumberMass X y α n := by
  have hXpos : 0 < X n := by linarith
  have hterm : ∀ m ∈ smoothNumberSet X y n,
      (X n) ^ (-(α n)) ≤ (m : ℝ) ^ (-(α n)) := by
    intro m hm
    obtain ⟨hmIcc, _⟩ := Finset.mem_filter.mp hm
    obtain ⟨hm1, hmX⟩ := Finset.mem_Icc.mp hmIcc
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hmle : (m : ℝ) ≤ X n := (Nat.cast_le.mpr hmX).trans (Nat.floor_le hXpos.le)
    exact Real.rpow_le_rpow_of_nonpos hmpos hmle (by linarith only [hα])
  calc
    smoothNumberCount X y n * (X n) ^ (-(α n))
        = ∑ _m ∈ smoothNumberSet X y n, (X n) ^ (-(α n)) := by
            rw [Finset.sum_const, nsmul_eq_mul, smoothNumberCount]
    _ ≤ ∑ m ∈ smoothNumberSet X y n, (m : ℝ) ^ (-(α n)) :=
        Finset.sum_le_sum hterm
    _ = smoothNumberMass X y α n := rfl

/-- **Logarithmic mass from the whole smooth set.** -/
theorem log_smoothNumberMass_ge_log_count_sub {X y α : ℕ → ℝ} {n : ℕ}
    (hX : 1 ≤ X n) (hα : 0 ≤ α n) :
    Real.log (smoothNumberCount X y n) - α n * Real.log (X n) ≤
      Real.log (smoothNumberMass X y α n) := by
  have hXpos : 0 < X n := by linarith
  have hcountpos : 0 < smoothNumberCount X y n := smoothNumberCount_pos hX
  have hprodpos : 0 < smoothNumberCount X y n * (X n) ^ (-(α n)) :=
    mul_pos hcountpos (Real.rpow_pos_of_pos hXpos _)
  have hle := smoothNumberMass_ge_count_mul_endpoint (y := y) hX hα
  have hlog := Real.log_le_log hprodpos hle
  rw [Real.log_mul hcountpos.ne' (Real.rpow_pos_of_pos hXpos _).ne',
    Real.log_rpow hXpos] at hlog
  nlinarith only [hlog]

/-- The smooth integers in `[1, X]` whose size is at most the window endpoint
`T`. -/
def smoothNumberWindow (X y T : ℕ → ℝ) (n : ℕ) : Finset ℕ :=
  (smoothNumberSet X y n).filter (fun m : ℕ => (m : ℝ) ≤ T n)

/-- The cardinality of a smooth window, as a real number. -/
def smoothNumberWindowCount (X y T : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((smoothNumberWindow X y T n).card : ℝ)

/-- **Mass from a smooth window.**  Every element of the window is at most `T`,
so its reciprocal weight is at least `T^(-α)`. -/
theorem smoothNumberMass_ge_windowCount_mul_rpow {X y α T : ℕ → ℝ} {n : ℕ}
    (_hT : 0 < T n) (hα : 0 ≤ α n) :
    smoothNumberWindowCount X y T n * (T n) ^ (-(α n)) ≤
      smoothNumberMass X y α n := by
  have hterm : ∀ m ∈ smoothNumberWindow X y T n,
      (T n) ^ (-(α n)) ≤ (m : ℝ) ^ (-(α n)) := by
    intro m hm
    obtain ⟨hmS, hmT⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmIcc, _⟩ := Finset.mem_filter.mp hmS
    obtain ⟨hm1, _⟩ := Finset.mem_Icc.mp hmIcc
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hmT' : (m : ℝ) ≤ T n := hmT
    exact Real.rpow_le_rpow_of_nonpos hmpos hmT' (by linarith only [hα])
  calc
    smoothNumberWindowCount X y T n * (T n) ^ (-(α n))
        = ∑ _m ∈ smoothNumberWindow X y T n, (T n) ^ (-(α n)) := by
            rw [Finset.sum_const, nsmul_eq_mul, smoothNumberWindowCount]
    _ ≤ ∑ m ∈ smoothNumberWindow X y T n, (m : ℝ) ^ (-(α n)) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ m ∈ smoothNumberSet X y n, (m : ℝ) ^ (-(α n)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro m _ _
        exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    _ = smoothNumberMass X y α n := rfl

/-- **Logarithmic mass from a smooth window.** -/
theorem log_smoothNumberMass_ge_log_windowCount_sub {X y α T : ℕ → ℝ} {n : ℕ}
    (hT : 0 < T n) (hα : 0 ≤ α n)
    (hwin : 0 < smoothNumberWindowCount X y T n) :
    Real.log (smoothNumberWindowCount X y T n) - α n * Real.log (T n) ≤
      Real.log (smoothNumberMass X y α n) := by
  have hprodpos : 0 < smoothNumberWindowCount X y T n * (T n) ^ (-(α n)) :=
    mul_pos hwin (Real.rpow_pos_of_pos hT _)
  have hle := smoothNumberMass_ge_windowCount_mul_rpow (X := X) (y := y)
    (α := α) (T := T) hT hα
  have hlog := Real.log_le_log hprodpos hle
  rw [Real.log_mul hwin.ne' (Real.rpow_pos_of_pos hT _).ne',
    Real.log_rpow hT] at hlog
  nlinarith only [hlog]

/-! ## 2. The counting reductions -/

/-- **`SmoothNumberMassLogLower` from a smooth-window count and a budget.**

The explicit counting input is `R n ≤ log #window`.  The arithmetic budget
`α log T + η log X ≤ R` then gives the saddle mean.  The endpoint `log X`
appears rather than `Λ` because the total smooth count is at most `X`, so
`Λ ≤ log X`. -/
theorem smoothNumberMassLogLower_of_windowCountLower
    {X y α T R : ℕ → ℝ} {η : ℝ}
    (hX : ∀ n, 1 ≤ X n) (hT : ∀ n, 0 < T n) (hα : ∀ n, 0 ≤ α n)
    (hη0 : 0 < η) (_hη1 : η < 1)
    (hwin : ∀ n, 0 < smoothNumberWindowCount X y T n)
    (hR : ∀ n, R n ≤ Real.log (smoothNumberWindowCount X y T n))
    (hbudget : ∀ n, α n * Real.log (T n) + η * Real.log (X n) ≤ R n) :
    SmoothNumberMassLogLower X y α (smoothSaddleScale X y) η := by
  refine ⟨hη0, fun n => ?_⟩
  have hlogmass := log_smoothNumberMass_ge_log_windowCount_sub
    (X := X) (y := y) (α := α) (T := T) (hT n) (hα n) (hwin n)
  have hΛ : smoothSaddleScale X y n ≤ Real.log (X n) := by
    unfold smoothSaddleScale
    exact Real.log_le_log (smoothNumberCount_pos (hX n))
      (smoothNumberCount_le_endpoint (hX n))
  have hcount : α n * Real.log (T n) + η * smoothSaddleScale X y n ≤
      Real.log (smoothNumberWindowCount X y T n) := by
    have hXterm : α n * Real.log (T n) + η * smoothSaddleScale X y n ≤
        α n * Real.log (T n) + η * Real.log (X n) := by
      nlinarith only [hΛ, hη0.le]
    exact hXterm.trans ((hbudget n).trans (hR n))
  nlinarith only [hlogmass, hcount]

/-- **`SmoothNumberMassLogLower` from a smooth-window density bound.**

This is the form produced by the existing prime-bin construction
`Cogentic.Randomized.centeredBinProducts_density_from_critical_line`: the
window contains at least `P^m · exp (-(1+ε) u log u)` smooth integers.  The
arithmetic budget then controls the uniform per-element weight. -/
theorem smoothNumberMassLogLower_of_windowDensity
    {X y α T P : ℕ → ℝ} {m : ℕ → ℕ} {u ε : ℕ → ℝ} {η : ℝ}
    (hX : ∀ n, 1 ≤ X n) (hT : ∀ n, 0 < T n) (hα : ∀ n, 0 ≤ α n)
    (hη0 : 0 < η) (_hη1 : η < 1)
    (hP : ∀ n, 0 < P n)
    (hdens : ∀ n, exp (-(1 + ε n) * u n * Real.log (u n)) ≤
      smoothNumberWindowCount X y T n / (P n) ^ (m n))
    (hbudget : ∀ n, α n * Real.log (T n) + η * Real.log (X n) +
      (1 + ε n) * u n * Real.log (u n) ≤ (m n : ℝ) * Real.log (P n)) :
    SmoothNumberMassLogLower X y α (smoothSaddleScale X y) η := by
  refine ⟨hη0, fun n => ?_⟩
  let D : ℝ := -(1 + ε n) * u n * Real.log (u n)
  let Q : ℝ := (P n) ^ (m n)
  have hQpos : 0 < Q := by
    dsimp only [Q]
    exact pow_pos (hP n) _
  have hdensn : exp D ≤ smoothNumberWindowCount X y T n / Q := by
    simpa only [D, Q] using hdens n
  have hDneg : -D = (1 + ε n) * u n * Real.log (u n) := by
    dsimp only [D]
    ring
  have hbudgetn : α n * Real.log (T n) + η * Real.log (X n) + (-D) ≤
      (m n : ℝ) * Real.log (P n) := by
    rw [hDneg]
    exact hbudget n
  have hcount_ge : Q * exp D ≤ smoothNumberWindowCount X y T n := by
    have h := hdensn
    rw [le_div_iff₀ hQpos] at h
    rwa [mul_comm] at h
  have hwinpos : 0 < smoothNumberWindowCount X y T n :=
    lt_of_lt_of_le (mul_pos hQpos (exp_pos D)) hcount_ge
  have hlogwin : Real.log Q + D ≤ Real.log (smoothNumberWindowCount X y T n) := by
    have h := Real.log_le_log (mul_pos hQpos (exp_pos D)) hcount_ge
    rw [Real.log_mul hQpos.ne' (exp_pos D).ne', Real.log_exp] at h
    linarith only [h]
  have hlogQ : Real.log Q = (m n : ℝ) * Real.log (P n) := by
    dsimp only [Q]
    exact Real.log_pow (P n) (m n)
  have hlogmass := log_smoothNumberMass_ge_log_windowCount_sub
    (X := X) (y := y) (α := α) (T := T) (hT n) (hα n) hwinpos
  have hΛ : smoothSaddleScale X y n ≤ Real.log (X n) := by
    unfold smoothSaddleScale
    exact Real.log_le_log (smoothNumberCount_pos (hX n))
      (smoothNumberCount_le_endpoint (hX n))
  have hcount : α n * Real.log (T n) + η * smoothSaddleScale X y n ≤
      Real.log (smoothNumberWindowCount X y T n) := by
    have hD : α n * Real.log (T n) + η * smoothSaddleScale X y n + (-D) ≤
        (m n : ℝ) * Real.log (P n) := by
      nlinarith only [hbudgetn, hΛ, hη0.le]
    nlinarith only [hlogwin, hlogQ, hD]
  nlinarith only [hlogmass, hcount]

/-- **`SmoothNumberMassLogLower` from the existing smooth-count lower bound.**

The only inputs are the existing `SmoothNumberCountLower X y c` and the explicit
arithmetic budget `(α + η) log X ≤ c D log D`.  This is the form consumed by
`L20_2SaddleInputs.mass_log_lower`, whose `Λ` is `log (#smooth)`. -/
theorem smoothNumberMassLogLower_of_countLower
    {X y α : ℕ → ℝ} {c η : ℝ}
    (hX : ∀ n, 1 ≤ X n) (hα : ∀ n, 0 ≤ α n)
    (hη0 : 0 < η) (_hη1 : η < 1)
    (hcount : SmoothNumberCountLower X y c)
    (hbudget : ∀ n, (α n + η) * Real.log (X n) ≤ c * paperD n * scale n) :
    SmoothNumberMassLogLower X y α (smoothSaddleScale X y) η := by
  refine ⟨hη0, fun n => ?_⟩
  have hcountpos : 0 < smoothNumberCount X y n := smoothNumberCount_pos (hX n)
  have hlogcount : c * paperD n * scale n ≤ Real.log (smoothNumberCount X y n) := by
    have h := Real.log_le_log (exp_pos (c * paperD n * scale n)) (hcount.2 n)
    rwa [Real.log_exp] at h
  have hΛ : smoothSaddleScale X y n ≤ Real.log (X n) := by
    unfold smoothSaddleScale
    exact Real.log_le_log hcountpos (smoothNumberCount_le_endpoint (hX n))
  have hcombined : α n * Real.log (X n) + η * smoothSaddleScale X y n ≤
      Real.log (smoothNumberCount X y n) := by
    have h1 : α n * Real.log (X n) + η * smoothSaddleScale X y n ≤
        (α n + η) * Real.log (X n) := by
      nlinarith only [hΛ, hη0.le]
    exact h1.trans ((hbudget n).trans hlogcount)
  have hlogmass := log_smoothNumberMass_ge_log_count_sub (y := y) (hX n) (hα n)
  nlinarith only [hcombined, hlogmass]

/-! ## 3. The concrete self-smooth mass `y = X` -/

/-- For `y = X` and `1 ≤ X`, every integer in `[1, ⌊X⌋]` is smooth, so the
smooth set is the full initial interval. -/
theorem smoothNumberSet_self {X : ℕ → ℝ} {n : ℕ} (hX : 1 ≤ X n) :
    smoothNumberSet X X n = Finset.Icc 1 ⌊X n⌋₊ := by
  have hXpos : 0 < X n := by linarith
  ext m
  simp only [smoothNumberSet, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨h, _⟩
    exact h
  · intro hm
    refine ⟨hm, ?_⟩
    intro p hp
    have hmpos : 0 < m := by omega
    have hp_le_m : p ≤ m := Nat.le_of_dvd hmpos (Nat.dvd_of_mem_primeFactors hp)
    have hm_le_X : (m : ℝ) ≤ X n := (Nat.cast_le.mpr hm.2).trans (Nat.floor_le hXpos.le)
    exact (Nat.cast_le.mpr hp_le_m).trans hm_le_X

/-- The self-smooth count is `⌊X⌋`. -/
theorem smoothNumberCount_self {X : ℕ → ℝ} {n : ℕ} (hX : 1 ≤ X n) :
    smoothNumberCount X X n = (⌊X n⌋₊ : ℝ) := by
  unfold smoothNumberCount
  rw [smoothNumberSet_self hX, Nat.card_Icc, Nat.add_sub_cancel]

/-- **The concrete self-smooth reciprocal mass is at least `√⌊X⌋`.**  There are
`⌊X⌋` terms and each is at least `⌊X⌋^(-1/2)`. -/
theorem smoothNumberMass_self_ge_sqrt {X : ℕ → ℝ} {n : ℕ} (hX : 1 ≤ X n) :
    Real.sqrt (⌊X n⌋₊ : ℝ) ≤ smoothNumberMass X X (fun _ => (1 / 2 : ℝ)) n := by
  set N : ℕ := ⌊X n⌋₊ with hNdef
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hX)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcard : ((Finset.Icc 1 N).card : ℝ) = (N : ℝ) := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
  have hterm : ∀ m ∈ Finset.Icc 1 N,
      (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
    intro m hm
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hmN' : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN
    exact Real.rpow_le_rpow_of_nonpos hmpos hmN' (by norm_num)
  have hbase : (N : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) = (N : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      (N : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ))
          = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
              rw [Real.rpow_one]
      _ = (N : ℝ) ^ ((1 : ℝ) + -(1 / 2)) := (Real.rpow_add hNpos _ _).symm
      _ = (N : ℝ) ^ (1 / 2 : ℝ) := by norm_num
  unfold smoothNumberMass
  rw [smoothNumberSet_self hX, ← hNdef]
  calc
    Real.sqrt (N : ℝ) = (N : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, hbase]
    _ = ∑ _m ∈ Finset.Icc 1 N, (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ ≤ ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Finset.sum_le_sum hterm

/-- **The concrete self-smooth mass satisfies the saddle mean.**  For every
`X ≥ 1`, the smooth mass with `y = X` and `α = 1/2` obeys
`(1/2) log (#smooth) ≤ log mass`. -/
theorem smoothNumberMassLogLower_selfSmooth {X : ℕ → ℝ} (hX : ∀ n, 1 ≤ X n) :
    SmoothNumberMassLogLower X X (fun _ => (1 / 2 : ℝ))
      (smoothSaddleScale X X) (1 / 2) := by
  refine ⟨by norm_num, fun n => ?_⟩
  set N : ℕ := ⌊X n⌋₊ with hNdef
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hX n)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hge := smoothNumberMass_self_ge_sqrt (X := X) (n := n) (hX n)
  have hlog := Real.log_le_log (Real.sqrt_pos.mpr hNpos) hge
  rw [Real.log_sqrt hNpos.le] at hlog
  have hΛ : smoothSaddleScale X X n = Real.log (N : ℝ) := by
    unfold smoothSaddleScale
    rw [smoothNumberCount_self (hX n), ← hNdef]
  rw [hΛ]
  nlinarith only [hlog]

/-! ## 4. A genuinely restricted concrete mass: `y = X / 2` -/

/-- When `y = X / 2`, every integer `m ≤ X / 2` is smooth, because each prime
factor of `m` is at most `m`.  Hence the smooth count is at least `⌊X/2⌋`. -/
theorem smoothNumberCount_half_ge_floor {X : ℕ → ℝ} {n : ℕ} (hX : 2 ≤ X n) :
    (⌊X n / 2⌋₊ : ℝ) ≤ smoothNumberCount X (fun m => X m / 2) n := by
  have hXpos : 0 < X n := by linarith
  have hhalf_nonneg : 0 ≤ X n / 2 := by positivity
  have hsub : Finset.Icc 1 ⌊X n / 2⌋₊ ⊆ smoothNumberSet X (fun m => X m / 2) n := by
    intro m hm
    obtain ⟨hm1, hmT⟩ := Finset.mem_Icc.mp hm
    have hmT' : (m : ℝ) ≤ X n / 2 := (Nat.cast_le.mpr hmT).trans (Nat.floor_le hhalf_nonneg)
    rw [smoothNumberSet, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hm1, ?_⟩, ?_⟩
    · apply Nat.le_floor
      linarith only [hmT', hXpos.le]
    · intro p hp
      have hmpos : 0 < m := by omega
      have hp_le_m : p ≤ m := Nat.le_of_dvd hmpos (Nat.dvd_of_mem_primeFactors hp)
      exact (Nat.cast_le.mpr hp_le_m).trans hmT'
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard
  unfold smoothNumberCount
  exact_mod_cast hcard

/-- The `y = X / 2` reciprocal mass is at least `⌊X/2⌋ · X^(-1/4)`. -/
theorem smoothNumberMass_half_ge_floor {X : ℕ → ℝ} {n : ℕ} (hX : 256 ≤ X n) :
    (⌊X n / 2⌋₊ : ℝ) * (X n) ^ (-(1 / 4 : ℝ)) ≤
      smoothNumberMass X (fun m => X m / 2) (fun _ => (1 / 4 : ℝ)) n := by
  have hXpos : 0 < X n := by linarith
  have hcount := smoothNumberCount_half_ge_floor (X := X) (n := n) (by linarith : 2 ≤ X n)
  have hmass := smoothNumberMass_ge_count_mul_endpoint
    (X := X) (y := fun m => X m / 2) (α := fun _ => (1 / 4 : ℝ))
    (n := n) (by linarith : 1 ≤ X n) (by norm_num : 0 ≤ (1 / 4 : ℝ))
  have hweight : 0 ≤ (X n) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hXpos.le _
  calc
    (⌊X n / 2⌋₊ : ℝ) * (X n) ^ (-(1 / 4 : ℝ))
        ≤ smoothNumberCount X (fun m => X m / 2) n * (X n) ^ (-(1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_right hcount hweight
    _ ≤ smoothNumberMass X (fun m => X m / 2) (fun _ => (1 / 4 : ℝ)) n := hmass

/-- **The concrete `y = X / 2` mass satisfies the saddle mean.**  For every
`X ≥ 256`, the smooth reciprocal mass with `y = X/2` and `α = 1/4` obeys
`(1/2) log (#smooth) ≤ log mass`.  The proof uses only `⌊X/2⌋ ≥ X/4` and
`{1, …, ⌊X/2⌋} ⊆ {y-smooth}`; no analytic estimate enters. -/
theorem smoothNumberMassLogLower_halfSmooth {X : ℕ → ℝ} (hX : ∀ n, 256 ≤ X n) :
    SmoothNumberMassLogLower X (fun m => X m / 2) (fun _ => (1 / 4 : ℝ))
      (smoothSaddleScale X (fun m => X m / 2)) (1 / 2) := by
  refine ⟨by norm_num, fun n => ?_⟩
  have hXn : 256 ≤ X n := hX n
  have hXpos : 0 < X n := by linarith
  have hTpos : 0 < (⌊X n / 2⌋₊ : ℝ) := by
    have hhalf1 : ((1 : ℕ) : ℝ) ≤ X n / 2 := by
      norm_num
      linarith
    have : 1 ≤ ⌊X n / 2⌋₊ := Nat.le_floor hhalf1
    exact_mod_cast this
  have hmass_ge := smoothNumberMass_half_ge_floor (X := X) (n := n) hXn
  have hprodpos : 0 < (⌊X n / 2⌋₊ : ℝ) * (X n) ^ (-(1 / 4 : ℝ)) :=
    mul_pos hTpos (Real.rpow_pos_of_pos hXpos _)
  have hlogmass : Real.log (⌊X n / 2⌋₊ : ℝ) - (1 / 4 : ℝ) * Real.log (X n) ≤
      Real.log (smoothNumberMass X (fun m => X m / 2) (fun _ => (1 / 4 : ℝ)) n) := by
    have h := Real.log_le_log hprodpos hmass_ge
    rw [Real.log_mul hTpos.ne' (Real.rpow_pos_of_pos hXpos _).ne',
      Real.log_rpow hXpos] at h
    linarith only [h]
  have hfloor_gt : X n / 2 - 1 < (⌊X n / 2⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (X n / 2)
    linarith only [this]
  have hTge : X n / 4 ≤ (⌊X n / 2⌋₊ : ℝ) := by
    nlinarith only [hfloor_gt, hXn]
  have hlogTge : Real.log (X n / 4) ≤ Real.log (⌊X n / 2⌋₊ : ℝ) :=
    Real.log_le_log (by positivity) hTge
  rw [Real.log_div hXpos.ne' (by norm_num : (4 : ℝ) ≠ 0)] at hlogTge
  have hlogX : Real.log (256 : ℝ) ≤ Real.log (X n) :=
    Real.log_le_log (by norm_num) hXn
  have hlog256 : Real.log (256 : ℝ) = 4 * Real.log 4 := by
    rw [show (256 : ℝ) = 4 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hTstrong : (3 / 4 : ℝ) * Real.log (X n) ≤ Real.log (⌊X n / 2⌋₊ : ℝ) := by
    nlinarith only [hlogTge, hlogX, hlog256]
  have hΛ : smoothSaddleScale X (fun m => X m / 2) n ≤ Real.log (X n) := by
    unfold smoothSaddleScale
    exact Real.log_le_log
      (smoothNumberCount_pos (by linarith : 1 ≤ X n))
      (smoothNumberCount_le_endpoint (by linarith : 1 ≤ X n))
  nlinarith only [hlogmass, hTstrong, hΛ]

/-! ## 5. The paper-scale instance -/

/-- The manuscript-scale endpoint, clipped at one so that the self-smooth set is
nonempty at every index.  For `n ≥ 3` it is exactly `paperD n`. -/
noncomputable def paperSmoothEndpoint (n : ℕ) : ℝ :=
  exp (max 0 (scale n))

theorem paperSmoothEndpoint_ge_one (n : ℕ) : 1 ≤ paperSmoothEndpoint n :=
  Real.one_le_exp (le_max_left 0 (scale n))

/-- The concrete paper-scale smooth mass obeys `SmoothNumberMassLogLower`. -/
theorem paperSmoothMassLogLower :
    SmoothNumberMassLogLower paperSmoothEndpoint paperSmoothEndpoint
      (fun _ => (1 / 2 : ℝ))
      (smoothSaddleScale paperSmoothEndpoint paperSmoothEndpoint) (1 / 2) :=
  smoothNumberMassLogLower_selfSmooth paperSmoothEndpoint_ge_one

/-- The concrete paper-scale mass feeds the existing `SaddlePointMeanLower`
reduction of `RandomizedL20_2Saddle`. -/
theorem saddlePointMeanLower_paperSmoothMass :
    SaddlePointMeanLower
      (smoothNumberMass paperSmoothEndpoint paperSmoothEndpoint (fun _ => (1 / 2 : ℝ)))
      (smoothSaddleScale paperSmoothEndpoint paperSmoothEndpoint) (1 / 2) :=
  saddlePointMeanLower_of_smoothNumberMassLogLower paperSmoothEndpoint_ge_one
    paperSmoothMassLogLower

/-! ## Axiom audit -/

#print axioms smoothNumberCount_pos
#print axioms smoothNumberCount_le_endpoint
#print axioms smoothNumberMass_ge_count_mul_endpoint
#print axioms log_smoothNumberMass_ge_log_count_sub
#print axioms smoothNumberMass_ge_windowCount_mul_rpow
#print axioms log_smoothNumberMass_ge_log_windowCount_sub
#print axioms smoothNumberMassLogLower_of_windowCountLower
#print axioms smoothNumberMassLogLower_of_windowDensity
#print axioms smoothNumberMassLogLower_of_countLower
#print axioms smoothNumberSet_self
#print axioms smoothNumberCount_self
#print axioms smoothNumberMass_self_ge_sqrt
#print axioms smoothNumberMassLogLower_selfSmooth
#print axioms smoothNumberCount_half_ge_floor
#print axioms smoothNumberMass_half_ge_floor
#print axioms smoothNumberMassLogLower_halfSmooth
#print axioms paperSmoothMassLogLower
#print axioms saddlePointMeanLower_paperSmoothMass

end

end Cogentic.RandomizedL20_2SmoothMass
