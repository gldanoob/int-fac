import Cogentic.RandomizedL21_2Density

set_option linter.style.haveILetI false

/-!
# L21.2: the local smooth-count input, concretely

`Cogentic.RandomizedL21_2Density` isolates the local smooth-count statement

```
LocalSmoothCountLower p c X :
  ∀ᶠ n, √(X n) * exp (-(R n)) ≤ smoothCountNear p c X n
```

where `smoothCountNear` is the cardinality of the explicit finite set

```
{m : ℕ | |m - p n| < √(p n) and P⁺(m) ≤ exp (c T_X)}.
```

This file removes the Prop in two complementary ways.

1. **The smallest explicit counting input.**  `LocalSetCountLower p c X` asks
   only for the existence, at each band, of *some* explicit `Finset ℕ` of
   smooth integers in the `√p`-neighbourhood with at least `√X exp (-R)`
   elements.  It is *equivalent* to `LocalSmoothCountLower`
   (`localSmoothCountLower_iff_setCount`): the forward direction takes the
   neighbourhood itself, the reverse direction is the general
   `card_le_smoothCountNear_of_subset` principle.  A powers-of-two
   specialization `PowTwoCountLower` is included, because it is the simplest
   concrete set to count.

2. **A concrete instance proved outright.**  Take

   ```
   X n = e^3,   c = 1,   p n = 4^n.
   ```

   Then `U = log X = 3`, `T = √(3 log 3)`, and `R ≥ 3/2`; hence the
   right-hand side `√X exp (-R) ≤ 1`.  On the other hand `p n = 4^n` is
   `2`-smooth and lies in its own `√(p n)`-neighbourhood, and the cutoff
   `exp T` is at least `2`, so the count is at least one.  This proves
   `LocalSmoothCountLower` for a genuine, non-zero cardinality, with no
   residual analytic input.

   This instance deliberately keeps `X` bounded.  For a growing paper-regime
   `X` the displayed inequality is the smooth-numbers-in-short-intervals
   theorem; it is *not* derivable from the elementary powers-of-two
   construction, since `√(X n) exp (-R n) = exp (U/2 - o(U)) → ∞`.  The
   reduction in item 1 is the exact residual statement in that regime.

No `sorry`, `admit`, `axiom` or `native_decide`; every count is a genuine
`Finset.card`, never set to zero.
-/

noncomputable section

namespace Cogentic.RandomizedL21_2LocalCount

open Filter Real
open Cogentic.RandomizedL21_2
open Cogentic.RandomizedL21_2Sub
open Cogentic.RandomizedL21_2Perron
open Cogentic.RandomizedL21_2Density

/-- The manuscript's logarithmic density loss, abbreviated. -/
abbrev repLog (c : ℝ) (X : ℕ → ℝ) (n : ℕ) : ℝ :=
  representationLog (kOf X c) (spacingOf X c) (bOf X c) n

/-! ## 1. The smallest explicit counting input -/

/-- **The smallest counting input.**  At each band there is an explicit finite
set `S` of smooth integers in the `√p`-neighbourhood whose cardinality already
dominates `√X exp (-R)`.

This is the exact residual statement: taking `S` to be the whole
`sqrtSmoothNeighbours` recovers `LocalSmoothCountLower`, and conversely any such
`S` gives the count by monotonicity of `Finset.card`. -/
def LocalSetCountLower (p : ℕ → ℝ) (c : ℝ) (X : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    ∃ S : Finset ℕ,
      S ⊆ sqrtSmoothNeighbours (p n) (smoothCutoff c X n) ∧
        Real.sqrt (X n) * Real.exp (-(repLog c X n)) ≤ (S.card : ℝ)

/-- An explicit set count implies the local smooth-count lower bound. -/
theorem localSmoothCountLower_of_setCount {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ}
    (h : LocalSetCountLower p c X) : LocalSmoothCountLower p c X := by
  filter_upwards [h] with n hn
  obtain ⟨S, hsub, hcard⟩ := hn
  exact hcard.trans (card_le_smoothCountNear_of_subset hsub)

/-- Conversely, the local smooth-count lower bound *is* an explicit set count:
choose the neighbourhood itself. -/
theorem setCount_of_localSmoothCountLower {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ}
    (h : LocalSmoothCountLower p c X) : LocalSetCountLower p c X := by
  filter_upwards [h] with n hn
  exact ⟨sqrtSmoothNeighbours (p n) (smoothCutoff c X n), subset_rfl, hn⟩

/-- **The local density Prop is exactly the smallest explicit set count.** -/
theorem localSmoothCountLower_iff_setCount {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ} :
    LocalSmoothCountLower p c X ↔ LocalSetCountLower p c X :=
  ⟨setCount_of_localSmoothCountLower, localSmoothCountLower_of_setCount⟩

/-! ## 2. The powers-of-two special case -/

/-- The powers of two inside the `√p`-neighbourhood.  This is the simplest
explicit smooth set: every member is `2`-smooth. -/
def powTwoNeighbours (p y : ℝ) : Finset ℕ := by
  classical
  exact (sqrtSmoothNeighbours p y).filter fun m => ∃ j : ℕ, m = 2 ^ j

/-- The powers-of-two set is a subset of the full smooth neighbourhood. -/
theorem powTwoNeighbours_subset (p y : ℝ) :
    powTwoNeighbours p y ⊆ sqrtSmoothNeighbours p y := by
  classical
  intro m hm
  exact (Finset.mem_filter.mp hm).1

/-- **The powers-of-two counting input.**  The explicit powers-of-two set in
the `√p`-neighbourhood already has the required cardinality. -/
def PowTwoCountLower (p : ℕ → ℝ) (c : ℝ) (X : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    Real.sqrt (X n) * Real.exp (-(repLog c X n)) ≤
      ((powTwoNeighbours (p n) (smoothCutoff c X n)).card : ℝ)

/-- A powers-of-two count lower bound implies the local smooth-count lower
bound. -/
theorem localSmoothCountLower_of_powTwoCount {p : ℕ → ℝ} {c : ℝ} {X : ℕ → ℝ}
    (h : PowTwoCountLower p c X) : LocalSmoothCountLower p c X := by
  refine localSmoothCountLower_of_setCount (p := p) (c := c) (X := X) ?_
  filter_upwards [h] with n hn
  exact ⟨powTwoNeighbours (p n) (smoothCutoff c X n),
    powTwoNeighbours_subset _ _, hn⟩

/-! ## 3. A concrete instance with a proved count -/

/-- The explicit natural centre `4^n = 2^(2n)`. -/
def localCountPNat (n : ℕ) : ℕ := 2 ^ (2 * n)

/-- The explicit centre sequence `p n = 4^n = 2^(2n)`. -/
def localCountP (n : ℕ) : ℝ := (localCountPNat n : ℝ)

/-- The explicit stage-one constant `c = 1`. -/
def localCountC : ℝ := 1

/-- The explicit bounded dyadic centre bound `X n = e^3`, the minimal allowed
value `log X = 3`. -/
def localCountX (_n : ℕ) : ℝ := Real.exp 3

@[simp] theorem localCountX_apply (n : ℕ) : localCountX n = Real.exp 3 := rfl

@[simp] theorem localCountC_eq : localCountC = 1 := rfl

theorem localCountC_pos : 0 < localCountC := by
  norm_num [localCountC]

theorem localCountC_le_one : localCountC ≤ 1 := by
  norm_num [localCountC]

theorem localCountX_gt_one (n : ℕ) : 1 < localCountX n := by
  rw [localCountX_apply]
  calc
    (1 : ℝ) = Real.exp 0 := by simp
    _ < Real.exp 3 := Real.exp_lt_exp.mpr (by norm_num)

theorem localCountX_log (n : ℕ) : bandLog localCountX n = 3 := by
  unfold bandLog localCountX
  rw [Real.log_exp]

theorem localCountX_U_ge_three (n : ℕ) : 3 ≤ bandLog localCountX n := by
  rw [localCountX_log]

/-- The concrete parameter triple is admissible in the paper's local-count
regime: `X > 1`, `0 < c ≤ 1` and `log X ≥ 3` at every band. -/
theorem localCount_admissible :
    (∀ n, 1 < localCountX n) ∧ 0 < localCountC ∧ localCountC ≤ 1 ∧
      ∀ n, 3 ≤ bandLog localCountX n :=
  ⟨localCountX_gt_one, localCountC_pos, localCountC_le_one,
    localCountX_U_ge_three⟩

/-- The paper rate at the concrete `X`: `T = √(3 log 3)`. -/
theorem localCountT_sq (n : ℕ) : paperRate localCountX n ^ 2 = 3 * Real.log 3 := by
  unfold paperRate
  rw [localCountX_log]
  exact Real.sq_sqrt (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))

theorem localCountT_pos (n : ℕ) : 0 < paperRate localCountX n := by
  unfold paperRate
  rw [localCountX_log]
  exact Real.sqrt_pos.mpr (mul_pos (by norm_num) (Real.log_pos (by norm_num)))

theorem localCountT_ge_one (n : ℕ) : 1 ≤ paperRate localCountX n := by
  have hpos := localCountT_pos n
  have hsq : 1 ≤ paperRate localCountX n ^ 2 := by
    rw [localCountT_sq]
    have hlog3 : 1 ≤ Real.log 3 := by
      have h := Real.log_le_log (Real.exp_pos 1) Real.exp_one_lt_three.le
      simpa using h
    nlinarith
  nlinarith

theorem localCountT_le_three (n : ℕ) : paperRate localCountX n ≤ 3 := by
  have hnonneg : 0 ≤ paperRate localCountX n := (localCountT_pos n).le
  have hsq : paperRate localCountX n ^ 2 ≤ 9 := by
    rw [localCountT_sq]
    have hlog3 : Real.log 3 ≤ 2 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    nlinarith
  nlinarith

/-- The cutoff is at least `2`, so `4^n` is smooth with respect to it. -/
theorem two_le_localCountCutoff (n : ℕ) :
    (2 : ℝ) ≤ smoothCutoff localCountC localCountX n := by
  unfold smoothCutoff logCutoff
  rw [localCountC_eq, one_mul]
  calc
    (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
    _ ≤ Real.exp (paperRate localCountX n) :=
      Real.exp_le_exp.mpr (localCountT_ge_one n)

/-- `r = (U+1)/B > 1` at the concrete parameters. -/
theorem localCount_one_lt_r (n : ℕ) : 1 < rOf localCountX localCountC n := by
  unfold rOf UOf BOf
  rw [localCountX_log]
  simp only [localCountC_eq, logCutoff, one_mul]
  have hTpos := localCountT_pos n
  have hTle := localCountT_le_three n
  rw [one_lt_div hTpos]
  linarith

theorem localCount_r_pos (n : ℕ) : 0 < rOf localCountX localCountC n :=
  lt_trans zero_lt_one (localCount_one_lt_r n)

/-- `log r > 0`. -/
theorem localCount_logr_pos (n : ℕ) : 0 < Real.log (rOf localCountX localCountC n) :=
  Real.log_pos (localCount_one_lt_r n)

/-- `k = r (1 + 2/log r) ≥ e` at the concrete parameters. -/
theorem localCount_exp_one_le_k (n : ℕ) :
    Real.exp 1 ≤ kOf localCountX localCountC n := by
  unfold kOf
  have hr : 1 < rOf localCountX localCountC n := localCount_one_lt_r n
  have hr1 : 1 ≤ rOf localCountX localCountC n := le_of_lt hr
  have hlr : 0 < Real.log (rOf localCountX localCountC n) := localCount_logr_pos n
  by_cases h : Real.log (rOf localCountX localCountC n) ≤ 1
  · have hfac : 3 ≤ 1 + 2 / Real.log (rOf localCountX localCountC n) := by
      have h2 : 2 ≤ 2 / Real.log (rOf localCountX localCountC n) := by
        rw [le_div_iff₀ hlr]
        nlinarith
      linarith
    have hk3 : (3 : ℝ) ≤
        rOf localCountX localCountC n *
          (1 + 2 / Real.log (rOf localCountX localCountC n)) := by
      calc
        (3 : ℝ) = 1 * 3 := by ring
        _ ≤ rOf localCountX localCountC n *
            (1 + 2 / Real.log (rOf localCountX localCountC n)) :=
          mul_le_mul hr1 hfac (by norm_num) (by positivity)
    exact le_trans Real.exp_one_lt_three.le hk3
  · have h1 : 1 ≤ Real.log (rOf localCountX localCountC n) :=
      le_of_lt (lt_of_not_ge h)
    have hfac : 1 ≤ 1 + 2 / Real.log (rOf localCountX localCountC n) := by
      have h2 : 0 ≤ 2 / Real.log (rOf localCountX localCountC n) :=
        div_nonneg (by norm_num) hlr.le
      linarith
    have hr_exp : Real.exp 1 ≤ rOf localCountX localCountC n := by
      calc
        Real.exp 1 ≤ Real.exp (Real.log (rOf localCountX localCountC n)) :=
          Real.exp_le_exp.mpr h1
        _ = rOf localCountX localCountC n := Real.exp_log (localCount_r_pos n)
    calc
      Real.exp 1 = Real.exp 1 * 1 := by ring
      _ ≤ rOf localCountX localCountC n *
          (1 + 2 / Real.log (rOf localCountX localCountC n)) :=
        mul_le_mul hr_exp hfac (by norm_num) (localCount_r_pos n).le

theorem localCount_k_pos (n : ℕ) : 0 < kOf localCountX localCountC n :=
  lt_of_lt_of_le (Real.exp_pos 1) (localCount_exp_one_le_k n)

/-- `1 ≤ log k`. -/
theorem localCount_logk_ge_one (n : ℕ) :
    1 ≤ Real.log (kOf localCountX localCountC n) := by
  calc
    (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (kOf localCountX localCountC n) :=
      Real.log_le_log (Real.exp_pos 1) (localCount_exp_one_le_k n)

theorem localCount_logk_pos (n : ℕ) : 0 < Real.log (kOf localCountX localCountC n) :=
  lt_of_lt_of_le zero_lt_one (localCount_logk_ge_one n)

/-- `k Δ = (3 + (log 2)/2) / log k` at the concrete `U = 3`. -/
theorem localCount_k_mul_spacing (n : ℕ) :
    kOf localCountX localCountC n * spacingOf localCountX localCountC n =
      (3 + Real.log 2 / 2) / Real.log (kOf localCountX localCountC n) := by
  unfold spacingOf mOf
  simp only [UOf, localCountX_log]
  have hk : kOf localCountX localCountC n ≠ 0 := (localCount_k_pos n).ne'
  have hl : Real.log (kOf localCountX localCountC n) ≠ 0 :=
    (localCount_logk_pos n).ne'
  field_simp [hk, hl]

/-- `b/(2Δ) = (log k + 1)/2`, so it is at least one. -/
theorem localCount_b_div_two_spacing (n : ℕ) :
    bOf localCountX localCountC n / (2 * spacingOf localCountX localCountC n) =
      (Real.log (kOf localCountX localCountC n) + 1) / 2 := by
  unfold bOf spacingOf mOf
  simp only [UOf, localCountX_log]
  have hk : kOf localCountX localCountC n ≠ 0 := (localCount_k_pos n).ne'
  have hl : Real.log (kOf localCountX localCountC n) ≠ 0 :=
    (localCount_logk_pos n).ne'
  field_simp [hk, hl]

/-- The total logarithmic loss is at least `3/2` at the concrete parameters. -/
theorem localCount_repLog_ge (n : ℕ) :
    (3 : ℝ) / 2 ≤ repLog localCountC localCountX n := by
  unfold repLog representationLog
  have hk := localCount_k_mul_spacing n
  have hbr := localCount_b_div_two_spacing n
  have hkpos := localCount_k_pos n
  have hLge := localCount_logk_ge_one n
  have hLpos := localCount_logk_pos n
  have hlog40 : 0 ≤ Real.log 40 := Real.log_nonneg (by norm_num)
  -- The second summand is `log ((3 + log 2 / 2) / log k)`.
  have hnum_ge_one : (1 : ℝ) ≤ 3 + Real.log 2 / 2 := by
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  have hterm2 : Real.log ((3 + Real.log 2 / 2) / Real.log (kOf localCountX localCountC n))
      = Real.log (3 + Real.log 2 / 2) - Real.log (Real.log (kOf localCountX localCountC n)) := by
    rw [Real.log_div (by positivity) hLpos.ne']
  have hterm2_ge : -Real.log (Real.log (kOf localCountX localCountC n)) ≤
      Real.log ((3 + Real.log 2 / 2) / Real.log (kOf localCountX localCountC n)) := by
    rw [hterm2]
    have : 0 ≤ Real.log (3 + Real.log 2 / 2) :=
      Real.log_nonneg hnum_ge_one
    linarith
  -- The fourth summand is nonnegative.
  have hratio_ge_one : 1 ≤
      bOf localCountX localCountC n / (2 * spacingOf localCountX localCountC n) := by
    rw [hbr]
    linarith
  have hterm4_ge : 0 ≤ Real.log (bOf localCountX localCountC n /
      (2 * spacingOf localCountX localCountC n)) :=
    Real.log_nonneg hratio_ge_one
  -- `log log k ≤ log k - 1`, so `k log k - log log k ≥ e`.
  have hloglog_le : Real.log (Real.log (kOf localCountX localCountC n)) ≤
      Real.log (kOf localCountX localCountC n) - 1 :=
    Real.log_le_sub_one_of_pos hLpos
  have hk_ge_e : Real.exp 1 ≤ kOf localCountX localCountC n :=
    localCount_exp_one_le_k n
  have hprod : (Real.exp 1 - 1) * 1 ≤
      (kOf localCountX localCountC n - 1) * Real.log (kOf localCountX localCountC n) := by
    refine mul_le_mul ?_ hLge ?_ ?_
    · linarith
    · norm_num
    · linarith [hk_ge_e, Real.exp_one_gt_two]
  have hklogk_sub : Real.exp 1 ≤
      kOf localCountX localCountC n * Real.log (kOf localCountX localCountC n) -
        Real.log (Real.log (kOf localCountX localCountC n)) := by
    nlinarith [hloglog_le, hprod]
  -- Combine the surviving summands.
  rw [hbr] at hterm4_ge
  have hterm4_mul : 0 ≤ kOf localCountX localCountC n *
      Real.log ((Real.log (kOf localCountX localCountC n) + 1) / 2) :=
    mul_nonneg hkpos.le hterm4_ge
  rw [hk, hbr]
  nlinarith [hlog40, hterm2_ge, hterm4_mul, hklogk_sub,
    Real.exp_one_gt_two]

/-- The right-hand side at the concrete parameters is at most one. -/
theorem localCount_rhs_le_one (n : ℕ) :
    Real.sqrt (localCountX n) * Real.exp (-(repLog localCountC localCountX n)) ≤ 1 := by
  have hR := localCount_repLog_ge n
  have hsqrt : Real.sqrt (localCountX n) = Real.exp (3 / 2) := by
    rw [localCountX_apply]
    refine (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr ?_
    rw [pow_two, ← Real.exp_add]
    norm_num
  rw [hsqrt]
  rw [← Real.exp_add]
  calc
    Real.exp (3 / 2 + -repLog localCountC localCountX n) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

/-! ### The concrete count -/

/-- `4^n` is a member of its own `√p`-neighbourhood and is smooth for the
concrete cutoff. -/
theorem localCount_p_mem (n : ℕ) :
    localCountPNat n ∈
      sqrtSmoothNeighbours (localCountP n) (smoothCutoff localCountC localCountX n) := by
  rw [mem_sqrtSmoothNeighbours]
  constructor
  · have hposNat : 0 < localCountPNat n := by
      unfold localCountPNat
      exact pow_pos (by norm_num) _
    have hpos : (0 : ℝ) < localCountP n := by
      unfold localCountP
      exact_mod_cast hposNat
    change |localCountP n - localCountP n| < Real.sqrt (localCountP n)
    simp [Real.sqrt_pos.mpr hpos]
  · intro q hq
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [localCountPNat] at hq
    · have hpf : ((2 : ℕ) ^ (2 * n)).primeFactors = {2} :=
        Nat.primeFactors_prime_pow (by omega : 2 * n ≠ 0) Nat.prime_two
      change q ∈ ((2 : ℕ) ^ (2 * n)).primeFactors at hq
      rw [hpf, Finset.mem_singleton] at hq
      subst hq
      exact two_le_localCountCutoff n

/-- The concrete smooth count is at least one. -/
theorem localCount_count_ge_one (n : ℕ) :
    (1 : ℝ) ≤ smoothCountNear localCountP localCountC localCountX n := by
  have hmem := localCount_p_mem n
  have hcard : 0 < (sqrtSmoothNeighbours (localCountP n)
      (smoothCutoff localCountC localCountX n)).card :=
    Finset.card_pos.mpr ⟨_, hmem⟩
  unfold smoothCountNear
  exact_mod_cast hcard

/-- **The concrete powers-of-two count input.** -/
theorem localCount_powTwoCount :
    PowTwoCountLower localCountP localCountC localCountX := by
  have hne : ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) ≤ ((powTwoNeighbours (localCountP n)
        (smoothCutoff localCountC localCountX n)).card : ℝ) := by
    refine Eventually.of_forall fun n => ?_
    classical
    have hmem : localCountPNat n ∈
        powTwoNeighbours (localCountP n) (smoothCutoff localCountC localCountX n) := by
      refine Finset.mem_filter.mpr ⟨localCount_p_mem n, ⟨2 * n, ?_⟩⟩
      rfl
    have hcard : 0 < (powTwoNeighbours (localCountP n)
        (smoothCutoff localCountC localCountX n)).card :=
      Finset.card_pos.mpr ⟨_, hmem⟩
    exact_mod_cast Nat.succ_le_of_lt hcard
  filter_upwards [hne] with n hn
  exact (localCount_rhs_le_one n).trans hn

/-- **`LocalSmoothCountLower` for the concrete powers-of-two centre.** -/
theorem localSmoothCountLower_localCount :
    LocalSmoothCountLower localCountP localCountC localCountX :=
  localSmoothCountLower_of_powTwoCount localCount_powTwoCount

/-- The concrete instance also satisfies the direct, non-powers-of-two form:
the full neighbourhood count is at least one. -/
theorem localCount_fullCount_ge_one :
    ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) ≤ smoothCountNear localCountP localCountC localCountX n :=
  Eventually.of_forall localCount_count_ge_one

/-- The concrete count is eventually strictly positive, through the existing
positivity bridge `smoothCountNear_pos_of_localCount`. -/
theorem localCount_smoothCountNear_pos :
    ∀ᶠ n : ℕ in atTop,
      0 < smoothCountNear localCountP localCountC localCountX n :=
  smoothCountNear_pos_of_localCount
    (Eventually.of_forall fun n => lt_trans zero_lt_one (localCountX_gt_one n))
    localSmoothCountLower_localCount

/-! ## Axiom audit -/

#print axioms Cogentic.RandomizedL21_2LocalCount.localSmoothCountLower_of_setCount
#print axioms Cogentic.RandomizedL21_2LocalCount.setCount_of_localSmoothCountLower
#print axioms Cogentic.RandomizedL21_2LocalCount.localSmoothCountLower_iff_setCount
#print axioms Cogentic.RandomizedL21_2LocalCount.PowTwoCountLower
#print axioms Cogentic.RandomizedL21_2LocalCount.localSmoothCountLower_of_powTwoCount
#print axioms Cogentic.RandomizedL21_2LocalCount.localCount_admissible
#print axioms Cogentic.RandomizedL21_2LocalCount.localCount_repLog_ge
#print axioms Cogentic.RandomizedL21_2LocalCount.localCount_rhs_le_one
#print axioms Cogentic.RandomizedL21_2LocalCount.localCount_p_mem
#print axioms Cogentic.RandomizedL21_2LocalCount.localCount_count_ge_one
#print axioms Cogentic.RandomizedL21_2LocalCount.localCount_powTwoCount
#print axioms Cogentic.RandomizedL21_2LocalCount.localSmoothCountLower_localCount
#print axioms Cogentic.RandomizedL21_2LocalCount.localCount_smoothCountNear_pos

end Cogentic.RandomizedL21_2LocalCount
