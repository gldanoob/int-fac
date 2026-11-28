import Cogentic.RandomizedConcreteC1
import Cogentic.RandomizedConcreteEpochCost
import Cogentic.RandomizedConcreteStageCost
import Cogentic.RandomizedPaperEndpointWave29

/-!
# C3/C4 for the concrete epochs: exact residuals, instances, and a refutation

`Cogentic.RandomizedEpochAnalyticInputs` isolates the total-variation input `C3`
and the expected-public-work input `C4` of the randomized factoring blueprint:

```
C3Inputs E :  ε : ℕ → ℝ, 0 ≤ ε n, ε n ≤ 1/32,
              TV(E.ideal, E.actual) ≤ ε n          on every hard input;
C4Inputs E C : ∀ δ > 0, eventually
              mean E.actual E.pubWork ≤ exp ((C + δ/2) * scale n)
              on every hard input.
```

This file answers, for the two concrete epochs available in the tree, exactly
what those records require and whether they hold.

## The two concrete epochs

* `goodEpochOfLe` (the Wave-17 all-good placeholder): `Coins = Unit`,
  `Label = Unit`, `ideal = actual = uniform`, all ten stage costs are zero.
  Its `GlobalProductIdentity` is *false* (`RandomizedConcreteC1`), but C3 and C4
  are still trivially satisfiable: `TV = 0` and `pubWork = 0`.

* `concreteEpoch` (the repaired C1 epoch with the finite square-root search):
  same sample type and the same ideal/actual uniform law, but stage `S0` is
  charged `Fintype.card (ZMod n)ˣ = n.totient`, the size of the unit group
  scanned by the root search.  Consequently `TV = 0` (so C3 holds, with budget
  `ε = 0`), while its public work is `φ(n)`, which is *linear* in `n` and hence
  exceeds the subexponential budget `exp (O (scale n))` for **every** fixed
  ceiling `C`.  We prove `¬ C4Inputs concreteEpochFamily C` for every `C`.

## Exact residuals

`C3Residual E` and `C4Residual E C` are the two `Prop`-valued residual
conditions, and `nonempty_c3Inputs_iff_residual` / `c4Inputs_iff_residual` prove that
they are *exactly* the content of `C3Inputs E` / `C4Inputs E C`.  In particular,
for the Wave-29 record `PaperResidualFor29 E D` the only E-specific C3/C4 data
is these two residuals (`paperResidualFor29_c3c4_exact`).

No `sorry`, `admit`, `axiom`, `native_decide`, or zero-loss is used.
-/

noncomputable section

namespace Cogentic.RandomizedC3C4Concrete

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Filter Real
open Cogentic.RandomizedConcreteC1
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedConcreteEpochCost
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedEpochTV
open Cogentic.RandomizedFiniteSupportTV
open Cogentic.RandomizedPaperEndpointWave29
open Cogentic.RandomizedP1
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedSmallPrimePrepass
open Cogentic.RandomizedWave17Audit
open scoped BigOperators ENNReal Topology

universe u

/-! ## Section 1: The exact C3/C4 residual conditions -/

/-- **The exact C3 residual.**  There is a per-input total-variation budget
`ε` which is nonnegative, at most `1/32`, and dominates the ideal/actual TV
distance on every hard input.  This is a `Prop`, so it forgets the (irrelevant)
choice of the budget function. -/
def C3Residual (E : ∀ n, 3 ≤ n → HardEpochData n) : Prop :=
  ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ (∀ n, ε n ≤ 1 / 32) ∧
    ∀ n (hN : 3 ≤ n), HardInput n →
      pmfTotalVariation (E n hN).ideal (E n hN).actual ≤ ε n

/-- The C3 residual is exactly the content of `C3Inputs`. -/
theorem nonempty_c3Inputs_iff_residual {E : ∀ n, 3 ≤ n → HardEpochData n} :
    Nonempty (C3Inputs E) ↔ C3Residual E := by
  constructor
  · rintro ⟨⟨ε, h0, hle, htv⟩⟩
    exact ⟨ε, h0, hle, htv⟩
  · rintro ⟨ε, h0, hle, htv⟩
    exact ⟨⟨ε, h0, hle, htv⟩⟩

/-- A `C3Inputs` record produces the C3 residual. -/
theorem c3Residual_of_inputs {E : ∀ n, 3 ≤ n → HardEpochData n}
    (I : C3Inputs E) : C3Residual E :=
  nonempty_c3Inputs_iff_residual.mp ⟨I⟩

/-- The C3 residual produces a `C3Inputs` record (with a budget chosen from the
existential).  This uses classical choice only to extract the budget function;
`C3Residual` remains the proposition recording existence. -/
noncomputable def c3InputsOfResidual {E : ∀ n, 3 ≤ n → HardEpochData n}
    (h : C3Residual E) : C3Inputs E where
  epsilon := Classical.choose h
  epsilon_nonneg := (Classical.choose_spec h).1
  epsilon_le := (Classical.choose_spec h).2.1
  tv_le := (Classical.choose_spec h).2.2

/-- **The exact C4 residual.**  For every `δ > 0`, eventually on every hard
input the mean public work is at most `exp ((C + δ/2) * scale n)`.  This is
literally the single field of `C4Inputs`. -/
def C4Residual (E : ∀ n, 3 ≤ n → HardEpochData n) (C : ℝ) : Prop :=
  ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ (hN : 3 ≤ n), HardInput n →
    mean (E n hN).actual (fun x => ((E n hN).pubWork x : ℝ≥0∞)) ≤
      ENNReal.ofReal (exp ((C + δ / 2) * scale n))

/-- The C4 residual is exactly the content of `C4Inputs`. -/
theorem c4Inputs_iff_residual {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ} :
    C4Inputs E C ↔ C4Residual E C :=
  ⟨fun I => I.work_le, fun h => ⟨h⟩⟩

/-- The C3/C4 pair of residuals: the only E-specific C3/C4 analytic data. -/
structure C3C4Residual (E : ∀ n, 3 ≤ n → HardEpochData n) (C : ℝ) where
  /-- Exact C3 residual. -/
  c3 : C3Residual E
  /-- Exact C4 residual. -/
  c4 : C4Residual E C

/-- The C3/C4 input pair, bundled because `C3Inputs` carries a budget function as
data and hence lives in `Type`, not `Prop`. -/
structure C3C4Inputs (E : ∀ n, 3 ≤ n → HardEpochData n) (C : ℝ) where
  /-- C3: the ideal/actual total-variation budget. -/
  c3 : C3Inputs E
  /-- C4: the expected public-work budget. -/
  c4 : C4Inputs E C

/-- `Nonempty (C3Inputs ∧ C4Inputs)` is exactly the pair of residuals. -/
theorem nonempty_c3C4Inputs_iff_residual
    {E : ∀ n, 3 ≤ n → HardEpochData n} {C : ℝ} :
    Nonempty (C3C4Inputs E C) ↔ C3C4Residual E C :=
  ⟨fun ⟨h⟩ => ⟨c3Residual_of_inputs h.c3, c4Inputs_iff_residual.mp h.c4⟩,
   fun h => ⟨⟨c3InputsOfResidual h.c3,
     c4Inputs_iff_residual.mpr h.c4⟩⟩⟩

/-! ## Section 2: The all-good placeholder `goodEpochOfLe` -/

/-- The `HardEpochData` family of the all-good placeholder. -/
noncomputable def goodPlaceholderFamily :
    ∀ n, 3 ≤ n → HardEpochData n :=
  fun n hN => (goodEpochOfLe n hN).toHardEpochData

/-- The placeholder's ideal and actual laws are the same uniform law. -/
@[simp] theorem goodPlaceholder_ideal_eq_actual (n : ℕ) (hN : 3 ≤ n) :
    (goodPlaceholderFamily n hN).ideal = (goodPlaceholderFamily n hN).actual := rfl

/-- All ten placeholder stage costs vanish, so its public work is identically
zero. -/
theorem goodPlaceholder_pubWork_eq_zero (n : ℕ) (hN : 3 ≤ n)
    (x : (goodPlaceholderFamily n hN).Sample) :
    (goodPlaceholderFamily n hN).pubWork x = 0 := by
  refine (ConcreteEpochData.pubWork_eq_zero_iff (goodEpochOfLe n hN) x).mpr ?_
  intro j
  cases j <;> simp [goodEpochOfLe, goodEpoch, StageCosts.cost]

/-- **C3 for the all-good placeholder**, with the exact residual budget
`ε = 0`: the ideal and actual laws coincide, so the TV distance vanishes. -/
noncomputable def c3Inputs_goodPlaceholder : C3Inputs goodPlaceholderFamily where
  epsilon := fun _ => 0
  epsilon_nonneg := fun _ => le_rfl
  epsilon_le := fun _ => by norm_num
  tv_le := by
    intro n hN _
    rw [goodPlaceholder_ideal_eq_actual]
    exact le_of_eq (pmfTotalVariation_self _)

/-- The exact C3 residual of the placeholder is satisfied (with budget zero). -/
theorem c3Residual_goodPlaceholder : C3Residual goodPlaceholderFamily :=
  c3Residual_of_inputs c3Inputs_goodPlaceholder

/-- **C4 for the all-good placeholder**, at every ceiling `C`: the mean public
work is zero. -/
theorem c4Inputs_goodPlaceholder (C : ℝ) : C4Inputs goodPlaceholderFamily C := by
  refine ⟨?_⟩
  intro δ hδ
  exact Eventually.of_forall fun n => by
    intro hN _
    have hmean : mean (goodPlaceholderFamily n hN).actual
        (fun x => ((goodPlaceholderFamily n hN).pubWork x : ℝ≥0∞)) = 0 := by
      have hfun : (fun x : (goodPlaceholderFamily n hN).Sample =>
          ((goodPlaceholderFamily n hN).pubWork x : ℝ≥0∞)) = fun _ => 0 := by
        funext x
        rw [goodPlaceholder_pubWork_eq_zero n hN x]
        simp
      rw [hfun, mean_const]
    rw [hmean]
    exact zero_le

/-- The exact C4 residual of the placeholder is satisfied, at every `C`. -/
theorem c4Residual_goodPlaceholder (C : ℝ) : C4Residual goodPlaceholderFamily C :=
  c4Inputs_iff_residual.mp (c4Inputs_goodPlaceholder C)

/-! ## Section 3: The repaired root-search epoch `concreteEpoch` -/

/-- The modified epoch's ideal and actual laws coincide: both are the uniform
law on `Unit × (Unit → (ZMod n)ˣ)`. -/
@[simp] theorem concreteEpoch_ideal_eq_actual (n : ℕ) (hN : 3 ≤ n) :
    (concreteEpochFamily n hN).ideal = (concreteEpochFamily n hN).actual := rfl

/-- **C3 for the root-search epoch**, with the exact residual budget `ε = 0`.
The root search changes the public work and the transcript, but not the
ideal/actual laws, so the TV distance is still zero. -/
noncomputable def c3Inputs_concreteEpoch : C3Inputs concreteEpochFamily where
  epsilon := fun _ => 0
  epsilon_nonneg := fun _ => le_rfl
  epsilon_le := fun _ => by norm_num
  tv_le := by
    intro n hN _
    rw [concreteEpoch_ideal_eq_actual]
    exact le_of_eq (pmfTotalVariation_self _)

/-- The exact C3 residual of the root-search epoch is satisfied. -/
theorem c3Residual_concreteEpoch : C3Residual concreteEpochFamily :=
  c3Residual_of_inputs c3Inputs_concreteEpoch

/-- The public work of the root-search epoch on **every** sample is the size
`φ(n)` of the unit group scanned by stage `S0`; the other nine stages are free. -/
theorem concreteEpoch_pubWork_eq_totient (n : ℕ) (hN : 3 ≤ n)
    (x : (concreteEpochFamily n hN).Sample) :
    (concreteEpochFamily n hN).pubWork x = n.totient := by
  haveI : NeZero n := ⟨by omega⟩
  have hsum : (concreteEpochFamily n hN).pubWork x =
      ∑ j : Stage, (concreteEpoch n hN).stageCosts.cost j x :=
    ConcreteEpochData.pubWork_eq_sum (concreteEpoch n hN) x
  have hcard : (concreteEpoch n hN).stageCosts.cost Stage.S0 x =
      Fintype.card (ZMod n)ˣ := rfl
  have hother : ∀ j : Stage, j ≠ Stage.S0 →
      (concreteEpoch n hN).stageCosts.cost j x = 0 := by
    intro j hj
    cases j <;> simp_all [concreteEpoch, concreteEpochCore, StageCosts.cost]
  rw [hsum, Finset.sum_eq_single Stage.S0 (fun j _ hj => hother j hj) (by simp)]
  rw [hcard, ZMod.card_units_eq_totient]

/-- The mean public work of the root-search epoch is exactly `φ(n)`.  This is
the exact public-work quantity that C4 must dominate. -/
theorem mean_pubWork_concreteEpoch (n : ℕ) (hN : 3 ≤ n) :
    mean (concreteEpochFamily n hN).actual
        (fun x => ((concreteEpochFamily n hN).pubWork x : ℝ≥0∞)) =
      ENNReal.ofReal (n.totient : ℝ) := by
  have hfun : (fun x : (concreteEpochFamily n hN).Sample =>
      ((concreteEpochFamily n hN).pubWork x : ℝ≥0∞)) =
      fun _ => (n.totient : ℝ≥0∞) := by
    funext x
    rw [concreteEpoch_pubWork_eq_totient n hN x]
  rw [hfun, mean_const, ENNReal.ofReal_natCast]

/-- **The exact C4 condition for the root-search epoch.**  C4 at ceiling `C`
holds exactly when the totient `φ(n)` is eventually dominated by
`exp ((C + δ/2) * scale n)` on every hard input, for every `δ > 0`. -/
theorem c4Inputs_concreteEpoch_iff (C : ℝ) :
    C4Inputs concreteEpochFamily C ↔
      ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ (hN : 3 ≤ n), HardInput n →
        (n.totient : ℝ) ≤ exp ((C + δ / 2) * scale n) := by
  rw [c4Inputs_iff_residual]
  constructor
  · intro h δ hδ
    filter_upwards [h δ hδ] with n hn
    intro hN hhard
    have hm := mean_pubWork_concreteEpoch n hN
    have hle := hn hN hhard
    rw [hm] at hle
    exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp hle
  · intro h δ hδ
    filter_upwards [h δ hδ] with n hn
    intro hN hhard
    rw [mean_pubWork_concreteEpoch n hN]
    exact ENNReal.ofReal_le_ofReal (hn hN hhard)

/-- The C4 residual of the root-search epoch is the same totient condition. -/
theorem c4Residual_concreteEpoch_iff (C : ℝ) :
    C4Residual concreteEpochFamily C ↔
      ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ (hN : 3 ≤ n), HardInput n →
        (n.totient : ℝ) ≤ exp ((C + δ / 2) * scale n) :=
  (c4Inputs_iff_residual).symm.trans (c4Inputs_concreteEpoch_iff C)

/-! ## Section 4: The subexponential ceiling is too small for `φ(n)` -/

/-- `(log n)^(2/3) = logB n` is eventually below any fixed positive multiple of
`log n`. -/
theorem eventually_logB_le_const_mul_log {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, logB n ≤ c * Real.log n := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => (Real.log n) ^ (-(1 / 3) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hlog
  filter_upwards [hlog.eventually_ge_atTop 1,
    hinv.eventually (eventually_le_nhds hc)] with n hL hsmall
  have hLpos : 0 < Real.log n := zero_lt_one.trans_le hL
  have hsmall' : (Real.log n) ^ (-(1 / 3) : ℝ) ≤ c := hsmall
  calc logB n = (Real.log n) ^ (2 / 3 : ℝ) := rfl
    _ = (Real.log n) ^ (1 : ℝ) * (Real.log n) ^ (-(1 / 3) : ℝ) := by
          rw [← Real.rpow_add hLpos]
          norm_num
    _ = Real.log n * (Real.log n) ^ (-(1 / 3) : ℝ) := by rw [Real.rpow_one]
    _ ≤ Real.log n * c := mul_le_mul_of_nonneg_left hsmall' hLpos.le
    _ = c * Real.log n := by ring

/-- The scale is eventually below any fixed positive multiple of `log n`. -/
theorem eventually_scale_le_const_mul_log {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, scale n ≤ c * Real.log n := by
  filter_upwards [eventually_scale_le_half_logB,
    eventually_logB_le_const_mul_log (div_pos hc (by norm_num : (0 : ℝ) < 2))]
    with n hhalf hlogB
  have hquarter : scale n ≤ (c / 4) * Real.log n := by
    calc scale n ≤ (1 / 2) * logB n := hhalf
      _ ≤ (1 / 2) * ((c / 2) * Real.log n) :=
            mul_le_mul_of_nonneg_left hlogB (by norm_num)
      _ = (c / 4) * Real.log n := by ring
  have hc4 : c / 4 ≤ c := by linarith
  exact hquarter.trans
    (mul_le_mul_of_nonneg_right hc4 (Real.log_natCast_nonneg n))

/-- For every fixed real `K`, eventually `K * scale n ≤ (1/4) * log n`. -/
theorem eventually_const_mul_scale_le_quarter_log (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, K * scale n ≤ (1 / 4) * Real.log n := by
  set M : ℝ := max K 1 with hM
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hquarter := eventually_scale_le_const_mul_log
    (div_pos (by norm_num : (0 : ℝ) < 1) (mul_pos (by norm_num : (0 : ℝ) < 4) hMpos))
  filter_upwards [scale_grows.eventually_ge_atTop 0, hquarter] with n hs hq
  have hKM : K ≤ M := le_max_left _ _
  calc K * scale n ≤ M * scale n := mul_le_mul_of_nonneg_right hKM hs
    _ ≤ M * ((1 / (4 * M)) * Real.log n) :=
          mul_le_mul_of_nonneg_left hq hMpos.le
    _ = (1 / 4) * Real.log n := by
          field_simp [hMpos.ne']

/-- **The budget `exp (K * scale n)` is eventually below `n/2`.**  This is the
quantitative form of `scale n = o (log n)`. -/
theorem eventually_exp_const_mul_scale_lt_half (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, Real.exp (K * scale n) < (n : ℝ) / 2 := by
  filter_upwards [eventually_const_mul_scale_le_quarter_log K,
    eventually_ge_atTop (16 : ℕ)] with n hle hn16
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn16r : (16 : ℝ) ≤ n := by exact_mod_cast hn16
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : Real.log 16 ≤ Real.log n := Real.log_le_log (by norm_num) hn16r
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have h4 : 4 * Real.log 2 ≤ Real.log n := by rw [← hlog16]; exact hlogn
  have hlt : (1 / 4) * Real.log n < Real.log n - Real.log 2 := by
    nlinarith
  calc Real.exp (K * scale n) ≤ Real.exp ((1 / 4) * Real.log n) :=
        Real.exp_le_exp.mpr hle
    _ < Real.exp (Real.log n - Real.log 2) := Real.exp_lt_exp.mpr hlt
    _ = (n : ℝ) / 2 := by
          rw [Real.exp_sub, Real.exp_log hnpos,
            Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-! ## Section 5: The unit-group size of `3 * p` -/

/-- `3 * p` is not a prime power for a prime `p ≠ 3`. -/
theorem three_mul_prime_not_isPrimePow {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    ¬ IsPrimePow (3 * p) := by
  rw [isPrimePow_nat_iff]
  rintro ⟨q, k, hq, hk, hqk⟩
  -- `3` divides `q ^ k`, hence divides the prime `q`, hence `q = 3`.
  have h3dvd : 3 ∣ q ^ k := by rw [hqk]; exact dvd_mul_right 3 p
  have h3q : 3 ∣ q := Nat.prime_three.dvd_of_dvd_pow h3dvd
  have h3eq : 3 = q := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp h3q
  subst h3eq
  -- `3 ^ k = 3 * p`, so `p = 3 ^ (k - 1)`.
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ' 3 j] at hqk
  have hpj : p = 3 ^ j := (Nat.mul_left_cancel (by norm_num : 0 < 3) hqk).symm
  rcases j with _ | j
  · simp at hpj
    exact hp.ne_one hpj
  · have h3dvdj : 3 ∣ 3 ^ (j + 1) := dvd_pow_self 3 (by omega)
    have h3p : 3 ∣ p := by rw [hpj]; exact h3dvdj
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3p).symm

/-- `3 * p` is a hard input for every prime `p ≥ 4`. -/
theorem three_mul_prime_hardInput {p : ℕ} (hp : p.Prime) (hp4 : 4 ≤ p) :
    HardInput (3 * p) := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  refine ⟨?_, ?_, three_mul_prime_not_isPrimePow hp hp3⟩
  · exact (show Odd 3 from ⟨1, by norm_num⟩).mul (hp.odd_of_ne_two hp2)
  · exact Nat.not_prime_mul (by norm_num : 3 ≠ 1) hp.ne_one

/-! ## Section 6: C4 is false for the root-search epoch -/

/-- **Refutation.**  The root-search epoch cannot satisfy C4 at any fixed
ceiling `C`: its mean public work is `φ(n)`, which is linear on the hard inputs
`n = 3 p`, while the allowed budget `exp ((C + δ/2) * scale n)` is
subexponential. -/
theorem not_c4Inputs_concreteEpochFamily (C : ℝ) :
    ¬ C4Inputs concreteEpochFamily C := by
  intro h
  rw [c4Inputs_concreteEpoch_iff] at h
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (h 1 zero_lt_one)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (eventually_exp_const_mul_scale_lt_half (C + 1 / 2))
  obtain ⟨p, hpge, hpprime⟩ :=
    Nat.exists_infinite_primes (max (max N₁ N₂) 4)
  have hpN₁ : N₁ ≤ p :=
    le_trans (le_max_left N₁ N₂) (le_trans (le_max_left (max N₁ N₂) 4) hpge)
  have hpN₂ : N₂ ≤ p :=
    le_trans (le_max_right N₁ N₂) (le_trans (le_max_left (max N₁ N₂) 4) hpge)
  have hp4 : 4 ≤ p := le_trans (le_max_right (max N₁ N₂) 4) hpge
  have hhard : HardInput (3 * p) := three_mul_prime_hardInput hpprime hp4
  have htot : ((3 * p).totient : ℝ) ≤
      exp ((C + 1 / 2) * scale (3 * p)) :=
    hN₁ (3 * p) (by omega) (by omega) hhard
  have hexp : exp ((C + 1 / 2) * scale (3 * p)) < ((3 * p : ℕ) : ℝ) / 2 :=
    hN₂ (3 * p) (by omega)
  -- The totient of `3 * p` is `2 (p - 1)`, which is at least `3p/2`.
  have hcop : Nat.Coprime 3 p := by
    rw [Nat.coprime_comm]
    exact hpprime.coprime_iff_not_dvd.mpr
      (fun h3 => (by omega : p ≠ 3)
        ((Nat.prime_dvd_prime_iff_eq hpprime Nat.prime_three).mp h3))
  have htot3p : (3 * p).totient = 2 * (p - 1) := by
    rw [Nat.totient_mul hcop, Nat.totient_prime Nat.prime_three,
      Nat.totient_prime hpprime]
  have hge : ((3 * p : ℕ) : ℝ) / 2 ≤ ((3 * p).totient : ℝ) := by
    rw [htot3p]
    have hp1 : (1 : ℕ) ≤ p := by omega
    have hcast : ((2 * (p - 1) : ℕ) : ℝ) = 2 * ((p : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub hp1]
      norm_num
    have hcastn : ((3 * p : ℕ) : ℝ) = 3 * (p : ℝ) := by push_cast; ring
    rw [hcast, hcastn]
    have hp4' : (4 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp4
    nlinarith
  linarith

/-- The C4 residual of the root-search epoch is also false at every ceiling. -/
theorem not_c4Residual_concreteEpoch (C : ℝ) : ¬ C4Residual concreteEpochFamily C :=
  fun h => not_c4Inputs_concreteEpochFamily C (c4Inputs_iff_residual.mpr h)

/-! ## Section 7: The general concrete cost hypotheses reduce to the residuals -/

/-- The `ConcreteC3Hypotheses` route of `RandomizedConcreteEpochCost` produces
exactly the C3 residual; its analytic content is the TV budget
`directSamplerEpsilon spec η gcdMass ≤ 1/32` together with the ideal-law and
gcd-exit bounds. -/
theorem c3Residual_of_concreteC3Hypotheses
    (D : ∀ n, ConcreteEpochData n) (H : ConcreteC3Hypotheses D) :
    C3Residual (concreteCostFamily D) :=
  c3Residual_of_inputs (c3Inputs D H)

/-- The `ConcreteC4Hypotheses` route of `RandomizedConcreteEpochCost` produces
exactly the C4 residual; its analytic content is the ten per-stage mean bounds
and the stage-weight bounds. -/
theorem c4Residual_of_concreteC4Hypotheses
    (D : ∀ n, ConcreteEpochData n) {C : ℝ} (H : ConcreteC4Hypotheses D C) :
    C4Residual (concreteCostFamily D) C :=
  c4Inputs_iff_residual.mp (c4Inputs D H)

/-- The concrete stage decomposition gives the pointwise public-work identity
that underlies the C4 residual. -/
theorem concrete_pubWork_eq_stageSum
    (D : ∀ n, ConcreteEpochData n) (n : ℕ) (hN : 3 ≤ n)
    (x : (concreteCostFamily D n hN).Sample) :
    (concreteCostFamily D n hN).pubWork x =
      ∑ j : Stage, (D n).stageCosts.cost j x :=
  ConcreteEpochData.pubWork_eq_sum (D n) x

/-! ## Section 8: The Wave-29 residual record -/

/-- **The exact C3/C4 content of `PaperResidualFor29`.**  Its `c3` and `c4`
fields are, up to the forgetful equivalences above, exactly `C3Residual E` and
`C4Residual E D`.  No other E-specific C3/C4 data occurs in the record. -/
theorem paperResidualFor29_c3c4_exact
    {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}
    (I : PaperResidualFor29 E D) :
    C3Residual E ∧ C4Residual E D :=
  ⟨c3Residual_of_inputs I.c3, c4Inputs_iff_residual.mp I.c4⟩

/-- Conversely, the two residuals are exactly what must be supplied to fill the
C3/C4 slots of `PaperResidualFor29`. -/
def paperResidualFor29_of_c3c4Residual
    {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ}
    (h : C3C4Residual E D) :
    C3C4Inputs E D :=
  ⟨c3InputsOfResidual h.c3, c4Inputs_iff_residual.mpr h.c4⟩

/-- The C3 and C4 fields of the Wave-29 record are the *only* E-specific
analytic fields at that level: replacing them by the two residuals loses
nothing. -/
theorem paperResidualFor29_c3c4_iff
    {E : ∀ n, 3 ≤ n → HardEpochData n} {D : ℝ} :
    Nonempty (C3C4Inputs E D) ↔ C3C4Residual E D :=
  nonempty_c3C4Inputs_iff_residual

/-! ## Section 9: C3/C4 are independent of `GlobalProductIdentity` -/

/-- The all-good placeholder satisfies both C3 and C4, but *not* the global
product identity.  Hence C3 and C4 cannot be derived from C1, and are genuinely
independent E-specific analytic fields. -/
theorem c3c4_goodPlaceholder_without_globalProductIdentity (C : ℝ) :
    C3Residual goodPlaceholderFamily ∧ C4Residual goodPlaceholderFamily C ∧
      ¬ (∀ n (hN : 3 ≤ n), (goodEpochOfLe n hN).GlobalProductIdentity) := by
  refine ⟨c3Residual_goodPlaceholder, c4Residual_goodPlaceholder C, ?_⟩
  intro h
  exact Cogentic.RandomizedC1C2FromConcrete.not_globalProductIdentity_goodEpochOfLe
    (h 15 (by norm_num))

/-- The root-search epoch satisfies the global product identity (C1), but fails
C4 at every ceiling.  Hence C4 is not implied by C1, and its exact content is
the totient domination condition of `c4Inputs_concreteEpoch_iff`. -/
theorem globalProductIdentity_concreteEpoch_without_c4 (C : ℝ) :
    (∀ n (hN : 3 ≤ n), (concreteEpoch n hN).GlobalProductIdentity) ∧
      ¬ C4Inputs concreteEpochFamily C :=
  ⟨concreteEpoch_globalProductIdentity, not_c4Inputs_concreteEpochFamily C⟩

/-! ## Section 10: Axiom audit -/

#print axioms nonempty_c3Inputs_iff_residual
#print axioms c4Inputs_iff_residual
#print axioms nonempty_c3C4Inputs_iff_residual
#print axioms c3Inputs_goodPlaceholder
#print axioms c3Residual_goodPlaceholder
#print axioms c4Inputs_goodPlaceholder
#print axioms c4Residual_goodPlaceholder
#print axioms c3Inputs_concreteEpoch
#print axioms c3Residual_concreteEpoch
#print axioms concreteEpoch_pubWork_eq_totient
#print axioms mean_pubWork_concreteEpoch
#print axioms c4Inputs_concreteEpoch_iff
#print axioms eventually_logB_le_const_mul_log
#print axioms eventually_scale_le_const_mul_log
#print axioms eventually_const_mul_scale_le_quarter_log
#print axioms eventually_exp_const_mul_scale_lt_half
#print axioms three_mul_prime_not_isPrimePow
#print axioms three_mul_prime_hardInput
#print axioms not_c4Inputs_concreteEpochFamily
#print axioms not_c4Residual_concreteEpoch
#print axioms c3Residual_of_concreteC3Hypotheses
#print axioms c4Residual_of_concreteC4Hypotheses
#print axioms paperResidualFor29_c3c4_exact
#print axioms paperResidualFor29_of_c3c4Residual
#print axioms paperResidualFor29_c3c4_iff
#print axioms c3c4_goodPlaceholder_without_globalProductIdentity
#print axioms globalProductIdentity_concreteEpoch_without_c4

end Cogentic.RandomizedC3C4Concrete
