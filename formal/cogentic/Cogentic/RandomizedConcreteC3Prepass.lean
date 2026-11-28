import Cogentic.RandomizedConcreteC3Rough

/-!
# The all-modulus C3 budget: prepass-filtered law and the rough branch

`Cogentic.RandomizedConcreteC3Rough` proves the real reduced-class C3 budget

`realBudget n hN ≤ 1/32`

unconditionally (under `DirichletLZerosOnLine`) only on the *rough* branch
`IsRough (roughThreshold n) n`, i.e. when every prime factor of `n` exceeds
`exp ((log n)^(2/3))`.  The literal all-`n` statement is false for large `n`
divisible by `3` under the crude missing-root bound: a factor `3` contributes
`2` to the reciprocal-prime sum `∑_{p ∣ n} 4/(p-1)`, while the class-number
lower bound only saves `√n / log n` against the `(log (2n))^80` numerator.

This file formalizes the intended manuscript composition.

* On the **small-prime branch** `HasSmallPrimeFactor (roughThreshold n) n`, the
  counted trial-division prepass `trialPrepass` (with the integer cutoff
  `prepassCutoff n = ⌊roughThreshold n⌋₊ + 1`) splits `n` with probability one
  (`prepass_splits_of_small`).  Its charged work `prepassCharge n` is strictly
  positive (`one_le_prepassCharge`) and is eventually bounded by
  `exp (ε * scale n)` whenever the prepass work hypothesis of
  `RandomizedSmallPrimePrepass` holds (`eventually_prepassCharge_le_exp`).
  On this branch the C3 slot only carries the fixed nonzero TV cap
  `prepassTVCharge = 1/32`; the main class-group epoch is not needed because
  the prepass already returns the factor.

* On the **rough branch** the filtered budget is exactly the real budget
  `realBudget n hN`, which `RandomizedConcreteC3Rough` proves is eventually at
  most `1/32`.

The two branches are complementary (`hasSmallPrimeFactor_or_isRough`), so the
combined budget

`prepassBudget n hN = if IsRough (roughThreshold n) n then realBudget n hN else prepassTVCharge`

is a genuine all-modulus budget `0 < prepassBudget n hN ≤ 1/32`
(`prepassBudget_pos`, `prepassBudget_le_one_div_thirty_two`).  The structure
`PrepassFilteredC3Inputs` records exactly the remaining all-modulus obligation,
and `eventually_prepassFilteredC3Inputs` discharges it from
`eventually_realBudget_le_of_rough`.

Finally, the epoch family `prepassFilteredFamily N₀` uses the real reduced-class
epoch *only* on rough inputs (and on the finite initial segment `n < N₀`, which
is absorbed into preprocessing), while every other input is the deterministic
prepass sink with `ideal = actual`.  The `C3Inputs` record `prepassC3Inputs`
packages the resulting honest all-input TV budget; on a rough input its value is
exactly `realBudget n hN` (`prepassC3Inputs_epsilon_rough`,
`prepassC3Inputs_tv_le_rough`), and it is strictly positive at every input
(`prepassC3Inputs_epsilon_pos`).

There is no `sorry`, `admit`, `axiom`, `native_decide`, or `Classical.choose`.
-/

noncomputable section

namespace Cogentic.RandomizedConcreteC3Prepass

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Finset Filter
open scoped Classical
open Cogentic.RandomizedConcreteC3Budget
open Cogentic.RandomizedConcreteC3Real
open Cogentic.RandomizedConcreteC3Real.ConcreteC3RealInputs
open Cogentic.RandomizedConcreteC3Rough
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedConcreteEpochCost
open Cogentic.RandomizedConcreteFormSpec
open Cogentic.RandomizedCostedFactorLaw
open Cogentic.RandomizedDirectClassSampler
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedEpochTV
open Cogentic.RandomizedFiniteSupportTV
open Cogentic.RandomizedFormGroup
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedSmallPrimePrepass
open scoped BigOperators ENNReal Topology

/-! ## Section 1: The trial-division prepass at the rough threshold -/

/-- The integer trial-division cutoff reaching the rough threshold. -/
noncomputable def prepassCutoff (n : ℕ) : ℕ := ⌊roughThreshold n⌋₊ + 1

/-- The integer prepass cutoff really reaches `roughThreshold`. -/
theorem roughThreshold_le_prepassCutoff (n : ℕ) :
    roughThreshold n ≤ (prepassCutoff n : ℝ) := by
  have h := Nat.lt_floor_add_one (roughThreshold n)
  calc
    roughThreshold n ≤ ((⌊roughThreshold n⌋₊ : ℝ) + 1) := h.le
    _ = ((prepassCutoff n : ℕ) : ℝ) := by
      unfold prepassCutoff
      push_cast
      ring

/-- The counted trial-division prepass splits every composite input with a prime
factor below the rough threshold. -/
theorem prepass_splits_of_small {n : ℕ} (hn : 2 ≤ n) (hcomp : ¬ n.Prime)
    (hsmall : HasSmallPrimeFactor (roughThreshold n) n) :
    (trialPrepass (prepassCutoff n) n).1 ≠ none := by
  have hsmall' : HasSmallPrimeFactor ((prepassCutoff n : ℕ) : ℝ) n := by
    obtain ⟨p, hp, hpB⟩ := hsmall
    exact ⟨p, hp, hpB.trans (roughThreshold_le_prepassCutoff n)⟩
  exact trialPrepass_splits_of_hasSmallPrimeFactor hn hcomp hsmall'

/-- The charged prepass work on `n`, in the epoch-work convention of
`RandomizedSmallPrimePrepass`: the attempt cost plus the branch's `+1`. -/
noncomputable def prepassCharge (n : ℕ) : ℝ :=
  (((trialPrepass (prepassCutoff n) n).2 + 1 : ℕ) : ℝ) + 1

/-- The prepass charge is at least one, hence genuinely nonzero. -/
theorem one_le_prepassCharge (n : ℕ) : 1 ≤ prepassCharge n := by
  unfold prepassCharge
  have h : (0 : ℝ) ≤ ((trialPrepass (prepassCutoff n) n).2 : ℝ) := Nat.cast_nonneg _
  push_cast
  linarith

/-- The prepass charge is strictly positive. -/
theorem prepassCharge_pos (n : ℕ) : 0 < prepassCharge n :=
  lt_of_lt_of_le zero_lt_one (one_le_prepassCharge n)

/-- The prepass charge is eventually `exp (ε * scale n)` under the prepass-work
hypothesis of `RandomizedSmallPrimePrepass`.  This records the small-prime
branch's cost as an actual charged quantity, not as zero. -/
theorem eventually_prepassCharge_le_exp
    (hPre : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬ n.Prime → ¬ IsPrimePow n →
      mean (trialPrepassEpoch n)
        (fun a => ((trialPrepassAttempt prepassCutoff n a).2 + 1 : ℕ)) + 1 ≤
        ENNReal.ofReal (Real.exp (ε * scale n)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Odd n → ¬ n.Prime → ¬ IsPrimePow n →
      prepassCharge n ≤ Real.exp (ε * scale n) := by
  filter_upwards [hPre ε hε] with n hn ho hp hpp
  have h := hn ho hp hpp
  simp only [trialPrepassEpoch, trialPrepassAttempt, mean_pure] at h
  have hcast : ((((trialPrepass (prepassCutoff n) n).2 + 1 : ℕ) : ℝ≥0∞) + 1) =
      ENNReal.ofReal (prepassCharge n) := by
    unfold prepassCharge
    rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast,
      ENNReal.ofReal_one]
  rw [hcast] at h
  exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp h

/-! ## Section 2: The two complementary branches -/

/-- `n` has a prime factor at most `B` exactly when it is not `B`-rough. -/
theorem hasSmallPrimeFactor_iff_not_isRough (B : ℝ) (n : ℕ) :
    HasSmallPrimeFactor B n ↔ ¬ IsRough B n := by
  constructor
  · intro hh hr
    exact ((not_hasSmallPrimeFactor_iff_isRough B n).mpr hr) hh
  · intro hnr
    by_contra hh
    exact hnr ((not_hasSmallPrimeFactor_iff_isRough B n).mp hh)

/-- The nonzero total-variation cap charged on the small-prime (prepass) branch. -/
def prepassTVCharge : ℝ := 1 / 32

theorem prepassTVCharge_pos : 0 < prepassTVCharge := by
  norm_num [prepassTVCharge]

theorem prepassTVCharge_le_one_div_thirty_two : prepassTVCharge ≤ 1 / 32 :=
  le_rfl

/-! ## Section 3: The all-modulus filtered budget -/

/-- The all-modulus C3 budget of the prepass-filtered law.  On the rough branch
it is the real reduced-class budget; on the small-prime branch it is the fixed
nonzero prepass TV cap. -/
noncomputable def prepassBudget (N : ℕ) (hN : Odd N) : ℝ :=
  if IsRough (roughThreshold N) N then realBudget N hN else prepassTVCharge

/-- On a rough modulus the filtered budget is the real budget. -/
theorem prepassBudget_of_rough {N : ℕ} {hN : Odd N}
    (hrough : IsRough (roughThreshold N) N) :
    prepassBudget N hN = realBudget N hN := by
  unfold prepassBudget
  rw [if_pos hrough]

/-- On the small-prime branch the filtered budget is the prepass TV cap. -/
theorem prepassBudget_of_small {N : ℕ} {hN : Odd N}
    (hsmall : HasSmallPrimeFactor (roughThreshold N) N) :
    prepassBudget N hN = prepassTVCharge := by
  have hnr : ¬ IsRough (roughThreshold N) N :=
    (hasSmallPrimeFactor_iff_not_isRough (roughThreshold N) N).mp hsmall
  unfold prepassBudget
  rw [if_neg hnr]

/-- The real C3 budget is *strictly* positive for every odd modulus `N ≥ 2`: the
missing-root numerator is a positive product and the gcd-exit mass is
nonnegative. -/
theorem realBudget_pos (N : ℕ) (hN : Odd N) (h2 : 2 ≤ N) :
    0 < realBudget N hN := by
  rw [realBudget_eq]
  have hU1 : (1 : ℝ) ≤ (leadingBound N : ℝ) := by
    exact_mod_cast one_le_leadingBound h2
  have hUpos : (0 : ℝ) < (leadingBound N : ℝ) := lt_of_lt_of_le zero_lt_one hU1
  have h1logU : (0 : ℝ) < 1 + Real.log (leadingBound N : ℝ) := by
    have := Real.log_nonneg hU1
    linarith
  have hL : (0 : ℝ) < Real.log (2 * (N : ℝ)) :=
    zero_lt_one.trans (one_lt_log_two_mul h2)
  have hsum : 0 < ∑ p ∈ N.primeFactors, 4 / ((p : ℝ) - 1) := by
    apply Finset.sum_pos'
    · intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity
    · obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr (show 1 < N by omega)
      refine ⟨p, hp, ?_⟩
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity
  have hmiss : 0 < directMissingRootMass (realSpec N hN) := by
    rw [directMissingRootMass_realSpec]
    have hpow : (0 : ℝ) < (Real.log (2 * (N : ℝ))) ^ (80 : ℕ) := pow_pos hL _
    exact mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hUpos) h1logU) hsum) hpow
  have hcardNat : 0 < (ReducedForms N).card := by
    rw [← realSpec_allForms_card N hN]
    exact (realSpec_allForms_nonempty N hN h2).card_pos
  have hcard : (0 : ℝ) < ((ReducedForms N).card : ℝ) := by
    exact_mod_cast hcardNat
  have hgcd : 0 ≤ realGcdMass N hN := ENNReal.toReal_nonneg
  exact add_pos_of_pos_of_nonneg (div_pos hmiss hcard) hgcd

/-- The real C3 budget is nonnegative for every odd modulus `N ≥ 2`. -/
theorem realBudget_nonneg (N : ℕ) (hN : Odd N) (h2 : 2 ≤ N) :
    0 ≤ realBudget N hN :=
  (realBudget_pos N hN h2).le

/-- The filtered all-modulus budget is strictly positive. -/
theorem prepassBudget_pos {N : ℕ} (hN : Odd N) (h2 : 2 ≤ N) :
    0 < prepassBudget N hN := by
  unfold prepassBudget
  split_ifs with hrough
  · exact realBudget_pos N hN h2
  · exact prepassTVCharge_pos

/-- The filtered all-modulus budget is at most `1/32` as soon as the real budget
is at most `1/32` on the rough branch. -/
theorem prepassBudget_le_one_div_thirty_two {N : ℕ} {hN : Odd N}
    (hbudget : realBudget N hN ≤ 1 / 32) :
    prepassBudget N hN ≤ 1 / 32 := by
  unfold prepassBudget
  split_ifs with hrough
  · exact hbudget
  · exact prepassTVCharge_le_one_div_thirty_two

/-! ## Section 4: The all-modulus input structure -/

/-- The all-modulus C3 budget input of the prepass-filtered law.  Only the rough
branch needs the real reduced-class budget; the small-prime branch is covered by
the prepass and carries the fixed nonzero TV cap. -/
structure PrepassFilteredC3Inputs (N : ℕ) (hN : Odd N) (h2 : 2 ≤ N) : Prop where
  /-- The filtered budget is at most `1/32`. -/
  budget_le : prepassBudget N hN ≤ 1 / 32

namespace PrepassFilteredC3Inputs

variable {N : ℕ} {hN : Odd N} {h2 : 2 ≤ N}

/-- On the rough branch the real `RealC3BudgetInputs` gives a filtered input. -/
theorem of_rough (hrough : IsRough (roughThreshold N) N)
    (B : RealC3BudgetInputs N hN h2) : PrepassFilteredC3Inputs N hN h2 :=
  ⟨by
    rw [prepassBudget_of_rough hrough]
    exact B.budget_le⟩

/-- On the small-prime branch the prepass covers the input, so the filtered input
holds unconditionally. -/
theorem of_small (hsmall : HasSmallPrimeFactor (roughThreshold N) N) :
    PrepassFilteredC3Inputs N hN h2 :=
  ⟨by
    rw [prepassBudget_of_small hsmall]
    exact prepassTVCharge_le_one_div_thirty_two⟩

/-- The filtered budget is strictly positive. -/
theorem budget_pos (_P : PrepassFilteredC3Inputs N hN h2) :
    0 < prepassBudget N hN :=
  prepassBudget_pos hN h2

/-- The filtered budget is nonnegative. -/
theorem budget_nonneg (P : PrepassFilteredC3Inputs N hN h2) :
    0 ≤ prepassBudget N hN :=
  (budget_pos P).le

/-- On the rough branch a filtered input *is* a `RealC3BudgetInputs`, so the full
real reduced-class TV estimate applies. -/
theorem toRealC3BudgetInputs (P : PrepassFilteredC3Inputs N hN h2)
    (hrough : IsRough (roughThreshold N) N) : RealC3BudgetInputs N hN h2 :=
  ⟨by
    have h := P.budget_le
    rwa [prepassBudget_of_rough hrough] at h⟩

/-- On the rough branch the filtered input yields the full concrete real C3
inputs of `RandomizedConcreteC3Real`. -/
def toConcreteC3RealInputs (P : PrepassFilteredC3Inputs N hN h2)
    (hrough : IsRough (roughThreshold N) N) : ConcreteC3RealInputs N hN h2 :=
  (P.toRealC3BudgetInputs hrough).toConcreteC3RealInputs

/-- On the rough branch the filtered input is a fully discharged
`ConcreteC3RealInputs` instance. -/
theorem concreteC3RealInputs_nonempty (P : PrepassFilteredC3Inputs N hN h2)
    (hrough : IsRough (roughThreshold N) N) :
    Nonempty (ConcreteC3RealInputs N hN h2) :=
  ⟨P.toConcreteC3RealInputs hrough⟩

end PrepassFilteredC3Inputs

/-! ## Section 5: The all-modulus budget from the rough branch -/

/-- **The all-modulus C3 budget.**  Under the critical-line class-number input,
for every sufficiently large modulus the prepass-filtered budget holds: every
modulus is either rough (and obeys the real reduced-class budget) or has a prime
factor below the rough threshold (and is charged to the prepass). -/
theorem eventually_prepassFilteredC3Inputs (line : DirichletLZerosOnLine) :
    ∀ᶠ N : ℕ in atTop, ∀ (hN : Odd N) (h2 : 2 ≤ N),
      PrepassFilteredC3Inputs N hN h2 := by
  filter_upwards [eventually_realBudget_le_of_rough line] with N hreal hN h2
  have h3 : 3 ≤ N := by
    rcases hN with ⟨k, hk⟩
    omega
  by_cases hrough : IsRough (roughThreshold N) N
  · exact PrepassFilteredC3Inputs.of_rough hrough ⟨hreal hN h3 hrough⟩
  · exact PrepassFilteredC3Inputs.of_small
      ((hasSmallPrimeFactor_iff_not_isRough (roughThreshold N) N).mpr hrough)

/-- The all-modulus split with both branches made explicit.  On the rough branch
the filtered budget is the real budget and is at most `1/32`; on the small-prime
branch it is the nonzero prepass TV cap while the prepass charge is strictly
positive. -/
theorem eventually_prepass_c3_split (line : DirichletLZerosOnLine) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → ∀ (hN : Odd n) (h2 : 2 ≤ n),
      PrepassFilteredC3Inputs n hN h2 ∧
        (IsRough (roughThreshold n) n → prepassBudget n hN = realBudget n hN) ∧
        (HasSmallPrimeFactor (roughThreshold n) n →
          prepassBudget n hN = prepassTVCharge ∧ 0 < prepassCharge n) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (eventually_prepassFilteredC3Inputs line)
  refine ⟨N₀, fun n hn hN h2 => ⟨hN₀ n hn hN h2, ?_, ?_⟩⟩
  · intro hrough
    exact prepassBudget_of_rough hrough
  · intro hsmall
    exact ⟨prepassBudget_of_small hsmall, prepassCharge_pos n⟩

/-! ## Section 6: The prepass-filtered epoch family and its `C3Inputs` -/

/-- The prepass-filtered epoch at `n`.  On rough inputs with `n ≥ N₀` it is the
real reduced-class epoch; on the complementary region (small-prime inputs, and
the finite initial segment `n < N₀` absorbed into preprocessing) it is the
deterministic sink with `ideal = actual`, since the prepass already returns the
factor there. -/
noncomputable def prepassFilteredEpoch (N₀ n : ℕ) (hN : 3 ≤ n) : ConcreteEpochData n :=
  if Odd n ∧ 3 ≤ n ∧ N₀ ≤ n ∧ IsRough (roughThreshold n) n then
    realFamily n hN
  else
    trivialEpoch n

/-- The per-input TV budget of the filtered family.  Rough inputs carry the real
budget; every other input carries the nonzero prepass TV cap. -/
noncomputable def prepassFilteredEpsilon (N₀ n : ℕ) : ℝ :=
  if h : Odd n ∧ 3 ≤ n ∧ N₀ ≤ n ∧ IsRough (roughThreshold n) n then
    realBudget n h.1
  else
    prepassTVCharge

/-- On the rough branch (above the threshold) the filtered epoch is the real
reduced-class epoch. -/
theorem prepassFilteredEpoch_of_rough {N₀ n : ℕ} (hN : 3 ≤ n) (ho : Odd n)
    (hN₀ : N₀ ≤ n) (hrough : IsRough (roughThreshold n) n) :
    prepassFilteredEpoch N₀ n hN = realFamily n hN := by
  unfold prepassFilteredEpoch
  rw [if_pos ⟨ho, hN, hN₀, hrough⟩]

/-- Off the rough branch the filtered epoch is the deterministic prepass sink. -/
theorem prepassFilteredEpoch_of_not {N₀ n : ℕ} (hN : 3 ≤ n)
    (h : ¬ (Odd n ∧ 3 ≤ n ∧ N₀ ≤ n ∧ IsRough (roughThreshold n) n)) :
    prepassFilteredEpoch N₀ n hN = trivialEpoch n := by
  unfold prepassFilteredEpoch
  rw [if_neg h]

/-- On the rough branch the filtered budget is exactly the real budget. -/
theorem prepassFilteredEpsilon_of_rough {N₀ n : ℕ} (ho : Odd n) (hN : 3 ≤ n)
    (hN₀ : N₀ ≤ n) (hrough : IsRough (roughThreshold n) n) :
    prepassFilteredEpsilon N₀ n = realBudget n ho := by
  unfold prepassFilteredEpsilon
  rw [dif_pos ⟨ho, hN, hN₀, hrough⟩]

/-- Off the rough branch the filtered budget is the prepass TV cap. -/
theorem prepassFilteredEpsilon_of_not {N₀ n : ℕ}
    (h : ¬ (Odd n ∧ 3 ≤ n ∧ N₀ ≤ n ∧ IsRough (roughThreshold n) n)) :
    prepassFilteredEpsilon N₀ n = prepassTVCharge := by
  unfold prepassFilteredEpsilon
  rw [dif_neg h]

/-- The filtered budget is nonnegative at every input. -/
theorem prepassFilteredEpsilon_nonneg (N₀ n : ℕ) :
    0 ≤ prepassFilteredEpsilon N₀ n := by
  unfold prepassFilteredEpsilon
  split_ifs with h
  · exact realBudget_nonneg n h.1 (by omega)
  · exact prepassTVCharge_pos.le

/-- The filtered budget is strictly positive at every input. -/
theorem prepassFilteredEpsilon_pos (N₀ n : ℕ) :
    0 < prepassFilteredEpsilon N₀ n := by
  unfold prepassFilteredEpsilon
  split_ifs with h
  · exact realBudget_pos n h.1 (by omega)
  · exact prepassTVCharge_pos

/-- The packaged hard-epoch family of the filtered epochs. -/
noncomputable def prepassFilteredFamily (N₀ : ℕ) :
    ∀ n, 3 ≤ n → HardEpochData n :=
  fun n hN => (prepassFilteredEpoch N₀ n hN).toHardEpochData

/-- On the rough branch the filtered family's sample space is exactly the real
class-group sample space `RealSample n` of `RandomizedConcreteC3Real`. -/
theorem prepassFilteredFamily_sample_of_rough {N₀ n : ℕ} (hN : 3 ≤ n) (ho : Odd n)
    (hN₀ : N₀ ≤ n) (hrough : IsRough (roughThreshold n) n) :
    (prepassFilteredFamily N₀ n hN).Sample = RealSample n := by
  unfold prepassFilteredFamily HardEpochData.Sample
  rw [prepassFilteredEpoch_of_rough hN ho hN₀ hrough, realFamily_odd hN ho]
  rfl

/-- On the rough branch the filtered family's public coin type is exactly the
type of reduced forms. -/
theorem prepassFilteredFamily_Coins_of_rough {N₀ n : ℕ} (hN : 3 ≤ n) (ho : Odd n)
    (hN₀ : N₀ ≤ n) (hrough : IsRough (roughThreshold n) n) :
    (prepassFilteredFamily N₀ n hN).Coins = RealCoins n := by
  unfold prepassFilteredFamily
  rw [prepassFilteredEpoch_of_rough hN ho hN₀ hrough, realFamily_odd hN ho]
  rfl

/-- Off the rough branch the filtered family is the deterministic sink, whose
sample space is a singleton. -/
theorem prepassFilteredFamily_Coins_of_not {N₀ n : ℕ} (hN : 3 ≤ n)
    (h : ¬ (Odd n ∧ 3 ≤ n ∧ N₀ ≤ n ∧ IsRough (roughThreshold n) n)) :
    (prepassFilteredFamily N₀ n hN).Coins = Unit := by
  unfold prepassFilteredFamily
  rw [prepassFilteredEpoch_of_not hN h]
  rfl

/-- **The all-input `C3Inputs` of the prepass-filtered law.**  The threshold `N₀`
is where the all-modulus budget holds; below it the finite initial segment is the
deterministic sink.  The resulting TV error is strictly positive everywhere and
never exceeds `1/32`. -/
noncomputable def prepassC3Inputs (N₀ : ℕ)
    (hbudget : ∀ n, N₀ ≤ n → ∀ (hN : Odd n) (h2 : 2 ≤ n),
      PrepassFilteredC3Inputs n hN h2) :
    C3Inputs (prepassFilteredFamily N₀) where
  epsilon := prepassFilteredEpsilon N₀
  epsilon_nonneg := prepassFilteredEpsilon_nonneg N₀
  epsilon_le := by
    intro n
    unfold prepassFilteredEpsilon
    split_ifs with h
    · have hb : prepassBudget n h.1 ≤ 1 / 32 :=
        (hbudget n h.2.2.1 h.1 (by omega)).budget_le
      rwa [prepassBudget_of_rough h.2.2.2] at hb
    · exact prepassTVCharge_le_one_div_thirty_two
  tv_le := by
    intro n hN hhard
    have ho : Odd n := hhard.1
    by_cases hN₀ : N₀ ≤ n
    · by_cases hrough : IsRough (roughThreshold n) n
      · have hcond : Odd n ∧ 3 ≤ n ∧ N₀ ≤ n ∧ IsRough (roughThreshold n) n :=
          ⟨ho, hN, hN₀, hrough⟩
        have hb : realBudget n ho ≤ 1 / 32 := by
          have hb' : prepassBudget n ho ≤ 1 / 32 :=
            (hbudget n hN₀ ho (by omega)).budget_le
          rwa [prepassBudget_of_rough hrough] at hb'
        have htv : pmfTotalVariation (realEpoch n ho (by omega)).ideal
            (realEpoch n ho (by omega)).actual ≤ realBudget n ho :=
          RealC3BudgetInputs.tv_le (B := ⟨hb⟩)
        change pmfTotalVariation (prepassFilteredEpoch N₀ n hN).ideal
          (prepassFilteredEpoch N₀ n hN).actual ≤ prepassFilteredEpsilon N₀ n
        rw [prepassFilteredEpoch, if_pos hcond, prepassFilteredEpsilon, dif_pos hcond,
          realFamily_odd hN ho]
        exact htv
      · have hcond : ¬ (Odd n ∧ 3 ≤ n ∧ N₀ ≤ n ∧ IsRough (roughThreshold n) n) :=
          fun hc => hrough hc.2.2.2
        change pmfTotalVariation (prepassFilteredEpoch N₀ n hN).ideal
          (prepassFilteredEpoch N₀ n hN).actual ≤ prepassFilteredEpsilon N₀ n
        rw [prepassFilteredEpoch, if_neg hcond, prepassFilteredEpsilon, dif_neg hcond]
        rw [show (trivialEpoch n).ideal = (trivialEpoch n).actual from rfl,
          pmfTotalVariation_self]
        exact prepassTVCharge_pos.le
    · have hcond : ¬ (Odd n ∧ 3 ≤ n ∧ N₀ ≤ n ∧ IsRough (roughThreshold n) n) :=
          fun hc => hN₀ hc.2.2.1
      change pmfTotalVariation (prepassFilteredEpoch N₀ n hN).ideal
        (prepassFilteredEpoch N₀ n hN).actual ≤ prepassFilteredEpsilon N₀ n
      rw [prepassFilteredEpoch, if_neg hcond, prepassFilteredEpsilon, dif_neg hcond]
      rw [show (trivialEpoch n).ideal = (trivialEpoch n).actual from rfl,
        pmfTotalVariation_self]
      exact prepassTVCharge_pos.le

/-- On a rough input above the threshold, the packaged C3 budget is exactly the
real reduced-class budget. -/
theorem prepassC3Inputs_epsilon_rough (N₀ : ℕ)
    (hbudget : ∀ n, N₀ ≤ n → ∀ (hN : Odd n) (h2 : 2 ≤ n),
      PrepassFilteredC3Inputs n hN h2)
    {n : ℕ} (hN : 3 ≤ n) (ho : Odd n) (hN₀ : N₀ ≤ n)
    (hrough : IsRough (roughThreshold n) n) :
    (prepassC3Inputs N₀ hbudget).epsilon n = realBudget n ho := by
  change prepassFilteredEpsilon N₀ n = realBudget n ho
  exact prepassFilteredEpsilon_of_rough ho hN hN₀ hrough

/-- Off the rough branch, the packaged C3 budget is the prepass TV cap. -/
theorem prepassC3Inputs_epsilon_of_small (N₀ : ℕ)
    (hbudget : ∀ n, N₀ ≤ n → ∀ (hN : Odd n) (h2 : 2 ≤ n),
      PrepassFilteredC3Inputs n hN h2)
    {n : ℕ} (hsmall : HasSmallPrimeFactor (roughThreshold n) n) :
    (prepassC3Inputs N₀ hbudget).epsilon n = prepassTVCharge := by
  change prepassFilteredEpsilon N₀ n = prepassTVCharge
  unfold prepassFilteredEpsilon
  rw [dif_neg]
  intro hc
  exact ((not_hasSmallPrimeFactor_iff_isRough (roughThreshold n) n).mpr hc.2.2.2) hsmall

/-- The packaged C3 budget is strictly positive at *every* input. -/
theorem prepassC3Inputs_epsilon_pos (N₀ : ℕ)
    (hbudget : ∀ n, N₀ ≤ n → ∀ (hN : Odd n) (h2 : 2 ≤ n),
      PrepassFilteredC3Inputs n hN h2) (n : ℕ) :
    0 < (prepassC3Inputs N₀ hbudget).epsilon n := by
  change 0 < prepassFilteredEpsilon N₀ n
  exact prepassFilteredEpsilon_pos N₀ n

/-- The packaged C3 budget is at most `1/32` at every input. -/
theorem prepassC3Inputs_epsilon_bounds (N₀ : ℕ)
    (hbudget : ∀ n, N₀ ≤ n → ∀ (hN : Odd n) (h2 : 2 ≤ n),
      PrepassFilteredC3Inputs n hN h2) (n : ℕ) :
    0 < (prepassC3Inputs N₀ hbudget).epsilon n ∧
      (prepassC3Inputs N₀ hbudget).epsilon n ≤ 1 / 32 :=
  ⟨prepassC3Inputs_epsilon_pos N₀ hbudget n, (prepassC3Inputs N₀ hbudget).epsilon_le n⟩

/-- On the rough branch the packaged TV estimate is exactly the real budget. -/
theorem prepassC3Inputs_tv_le_rough (N₀ : ℕ)
    (hbudget : ∀ n, N₀ ≤ n → ∀ (hN : Odd n) (h2 : 2 ≤ n),
      PrepassFilteredC3Inputs n hN h2)
    {n : ℕ} (hN : 3 ≤ n) (hhard : HardInput n) (hN₀ : N₀ ≤ n)
    (hrough : IsRough (roughThreshold n) n) :
    pmfTotalVariation (prepassFilteredFamily N₀ n hN).ideal
      (prepassFilteredFamily N₀ n hN).actual ≤ realBudget n hhard.1 := by
  have h := (prepassC3Inputs N₀ hbudget).tv_le n hN hhard
  rwa [prepassC3Inputs_epsilon_rough N₀ hbudget hN hhard.1 hN₀ hrough] at h

/-- **Existence of the all-input `C3Inputs`.**  The rough-branch theorem of
`RandomizedConcreteC3Rough` supplies the threshold and the filtered budget, and
`prepassC3Inputs` packages the all-input TV record. -/
theorem exists_prepassC3Inputs (line : DirichletLZerosOnLine) :
    ∃ N₀ : ℕ, Nonempty (C3Inputs (prepassFilteredFamily N₀)) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (eventually_prepassFilteredC3Inputs line)
  exact ⟨N₀, ⟨prepassC3Inputs N₀ hN₀⟩⟩

/-! ## Section 7: Axiom audit -/

#print axioms Cogentic.RandomizedConcreteC3Prepass.prepass_splits_of_small
#print axioms Cogentic.RandomizedConcreteC3Prepass.one_le_prepassCharge
#print axioms Cogentic.RandomizedConcreteC3Prepass.eventually_prepassCharge_le_exp
#print axioms Cogentic.RandomizedConcreteC3Prepass.realBudget_pos
#print axioms Cogentic.RandomizedConcreteC3Prepass.prepassBudget_pos
#print axioms Cogentic.RandomizedConcreteC3Prepass.prepassBudget_le_one_div_thirty_two
#print axioms Cogentic.RandomizedConcreteC3Prepass.eventually_prepassFilteredC3Inputs
#print axioms Cogentic.RandomizedConcreteC3Prepass.eventually_prepass_c3_split
#print axioms Cogentic.RandomizedConcreteC3Prepass.prepassC3Inputs
#print axioms Cogentic.RandomizedConcreteC3Prepass.prepassC3Inputs_epsilon_pos
#print axioms Cogentic.RandomizedConcreteC3Prepass.prepassC3Inputs_epsilon_bounds
#print axioms Cogentic.RandomizedConcreteC3Prepass.prepassC3Inputs_tv_le_rough
#print axioms Cogentic.RandomizedConcreteC3Prepass.exists_prepassC3Inputs

end Cogentic.RandomizedConcreteC3Prepass
