import Cogentic.RandomizedConcreteC3Real
import Cogentic.RandomizedFormGroup

/-!
# The real C3 budget: definitional fields and the residual numeric inequality

`Cogentic.RandomizedConcreteC3Real.ConcreteC3RealInputs` isolates six analytic
fields for the real reduced-class C3 instantiation.  This file discharges *three
of them definitionally* and reduces the remaining one to a single explicit
numeric inequality.

## The definitional fields

* `realEta = 0` and `hideal`: the epoch's ideal law is *definitionally* the
  uniform law on `(realSpec N hN).allForms`, so its total variation to itself is
  zero (`realEta_hideal`).
* `realGcdMass N hN = (gcdExitProb (realSpec N hN) (realJ N)).toReal` and
  `hgcd`: this is `le_rfl` (`realGcdMass_hgcd`).
* `hactual`: `(realEpoch N hN h2).actual` is *definitionally* the conditional
  direct-sampler law (`realEpoch_actual_eq`).

## The residual numeric inequality

The only remaining field of `ConcreteC3RealInputs` is

`directSamplerEpsilon (realSpec N hN) 0 gcdMass ≤ 1 / 32`,

which, after the above choices, is the single real inequality
`realBudget N hN ≤ 1/32` with

`realBudget N hN = directMissingRootMass (realSpec N hN) / #(ReducedForms N)
                  + (gcdExitProb (realSpec N hN) (realJ N)).toReal`.

`RealC3BudgetInputs` packs exactly this inequality and
`RealC3BudgetInputs.toConcreteC3RealInputs` produces the full
`ConcreteC3RealInputs` record from it.

Two further reductions sharpen the residual inequality:

* `criticalLineBudget`: the class-number lower bound
  `√N / (8 log N) ≤ #(ReducedForms N)` proved in
  `Cogentic.RandomizedFormGroup.reducedForms_card_lower_from_critical_line`
  replaces `#(ReducedForms N)` in the denominator.  This is the *smallest*
  inequality that still uses the critical-line input
  (`heps_le_of_criticalLineBudget`).
* `criticalLineGcdBudget`: the explicit one-attempt gcd-exit bound
  `(gcdExitProb ...).toReal ≤ ∑_{p | N} 1/p` removes the sampler entirely, so
  only `leadingBound N`, `log`, the prime factors of `N`, and `√N` remain
  (`heps_le_of_criticalLineGcdBudget`).

## Why "eventually for all `N`" is not claimed

The explicit missing-root numerator carries a `(log (2N))^80` factor, while the
critical-line lower bound is only `√N / log N`.  If `3 ∣ N` the
reciprocal-prime sum is at least `2`, so the explicit budget grows like
`(log N)^82`; it is therefore *not* bounded by `1/32` for all large `N`, and the
inequality is not derivable from the class-number lower bound.  This file
records it as the exact residual hypothesis `RealC3BudgetInputs` instead of
asserting it.

For prime `N` the reciprocal-prime sum is `4/(N-1)`, which beats the
`(log N)^80` factor, and Section 5 proves the resulting eventual inequality
unconditionally under `DirichletLZerosOnLine`
(`eventually_heps_le_of_prime`, `exists_concreteC3RealInputs_of_prime`).

There is no `sorry`, `admit`, `axiom`, `native_decide`, or `Classical.choose`.
-/

noncomputable section

namespace Cogentic.RandomizedConcreteC3Budget

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Finset Filter
open Cogentic.RandomizedConcreteC3Real
open Cogentic.RandomizedConcreteC3Real.ConcreteC3RealInputs
open Cogentic.RandomizedConcreteFormSpec
open Cogentic.RandomizedDirectClassSampler
open Cogentic.RandomizedEpochTV
open Cogentic.RandomizedFiniteSupportTV
open Cogentic.RandomizedFormGroup
open scoped BigOperators ENNReal Topology

/-! ## Section 1: The canonical zero and exact budgets -/

/-- The canonical ideal-law budget.  The real epoch's ideal law is
definitionally the uniform law on the canonical form set, so no `η > 0` is
needed. -/
def realEta : ℝ := 0

@[simp] theorem realEta_eq_zero : realEta = 0 := rfl

/-- The canonical gcd-exit budget: exactly the one-attempt gcd-exit mass of the
real direct sampler. -/
def realGcdMass (N : ℕ) (hN : Odd N) : ℝ :=
  (gcdExitProb (realSpec N hN) (realJ N)).toReal

/-- `hideal` at `η = 0`: the epoch's ideal law and the canonical uniform law are
the same object. -/
theorem realEta_hideal (N : ℕ) (hN : Odd N) (h2 : 2 ≤ N) :
    pmfTotalVariation (realEpoch N hN h2).ideal
        (PMF.uniformOfFinset (realSpec N hN).allForms
          (realSpec_allForms_nonempty N hN h2)) ≤ realEta := by
  rw [realEpoch_ideal]
  exact le_of_eq (pmfTotalVariation_self _)

/-- `hgcd` at the exact gcd-exit mass. -/
theorem realGcdMass_hgcd (N : ℕ) (hN : Odd N) :
    (gcdExitProb (realSpec N hN) (realJ N)).toReal ≤ realGcdMass N hN :=
  le_rfl

/-- `hactual`: the epoch's actual law is definitionally the conditional direct
sampler. -/
theorem realEpoch_actual_eq (N : ℕ) (hN : Odd N) (h2 : 2 ≤ N) :
    (realEpoch N hN h2).actual =
      directRetryConditionalPMF (realSpec N hN) (J := realJ N) (J₀ := realJ₀)
        (realSpec_hUJ N hN) realJ₀_le (realSpec_coprimeForms_nonempty N hN h2) :=
  realEpoch_actual N hN h2

/-! ## Section 2: The residual budget -/

/-- The residual real C3 budget after the three definitional discharges:
missing-root mass over the class-set cardinality, plus the exact gcd-exit
mass. -/
def realBudget (N : ℕ) (hN : Odd N) : ℝ :=
  directSamplerEpsilon (realSpec N hN) realEta (realGcdMass N hN)

/-- The budget with `η = 0` written out. -/
theorem realBudget_eq (N : ℕ) (hN : Odd N) :
    realBudget N hN =
      directMissingRootMass (realSpec N hN) / ((ReducedForms N).card : ℝ) +
        realGcdMass N hN := by
  unfold realBudget directSamplerEpsilon realEta
  rw [realSpec_allForms_card]
  ring

/-- The budget with both the `η = 0` simplification and the missing-root
numerator fully unfolded: `U = leadingBound N`, modulus `N`, and the prime
factors of `N`. -/
theorem realBudget_explicit (N : ℕ) (hN : Odd N) :
    realBudget N hN =
      2 * (leadingBound N : ℝ) * (1 + Real.log (leadingBound N : ℝ)) *
          (∑ p ∈ N.primeFactors, 4 / ((p : ℝ) - 1)) *
          (Real.log (2 * (N : ℝ))) ^ (80 : ℕ) /
          ((ReducedForms N).card : ℝ) + realGcdMass N hN := by
  rw [realBudget_eq, directMissingRootMass_realSpec]

/-- `heps_le` at the canonical budgets is *exactly* the residual inequality
`realBudget N hN ≤ 1/32`. -/
theorem heps_le_iff_realBudget (N : ℕ) (hN : Odd N) :
    directSamplerEpsilon (realSpec N hN) realEta (realGcdMass N hN) ≤ 1 / 32 ↔
      realBudget N hN ≤ 1 / 32 :=
  Iff.rfl

/-- The same equivalence with the literal `η = 0` appearing in the residual
condition of `ConcreteC3RealInputs`. -/
theorem heps_le_zero_iff_realBudget (N : ℕ) (hN : Odd N) :
    directSamplerEpsilon (realSpec N hN) 0 (realGcdMass N hN) ≤ 1 / 32 ↔
      realBudget N hN ≤ 1 / 32 :=
  Iff.rfl

/-- **The exact residual numeric input of the real C3 slot.**  Everything else
in `ConcreteC3RealInputs` is discharged unconditionally in this file. -/
structure RealC3BudgetInputs (N : ℕ) (hN : Odd N) (h2 : 2 ≤ N) : Prop where
  /-- The single remaining inequality: the explicit real C3 budget is at most
  `1/32`. -/
  budget_le : realBudget N hN ≤ 1 / 32

namespace RealC3BudgetInputs

variable {N : ℕ} {hN : Odd N} {h2 : 2 ≤ N}

/-- **Reduction from the residual numeric input.**  The exact inequality
`realBudget N hN ≤ 1/32` is the only analytic content needed to build the full
real C3 input record. -/
def toConcreteC3RealInputs (B : RealC3BudgetInputs N hN h2) :
    ConcreteC3RealInputs N hN h2 where
  eta := realEta
  gcdMass := realGcdMass N hN
  hideal := realEta_hideal N hN h2
  hgcd := realGcdMass_hgcd N hN
  hactual := realEpoch_actual_eq N hN h2
  heps_le := B.budget_le

/-- The corresponding TV bound, obtained from the residual budget through the
fully proved structural estimate of `RandomizedConcreteC3Real`. -/
theorem tv_le (B : RealC3BudgetInputs N hN h2) :
    pmfTotalVariation (realEpoch N hN h2).ideal (realEpoch N hN h2).actual ≤
      realBudget N hN :=
  ConcreteC3RealInputs.tv_le B.toConcreteC3RealInputs

/-- The budget is nonnegative whenever the residual inequality holds (it is a
sum of a nonnegative ratio and a nonnegative gcd mass). -/
theorem budget_nonneg (B : RealC3BudgetInputs N hN h2) :
    0 ≤ realBudget N hN :=
  ConcreteC3RealInputs.epsilon_nonneg B.toConcreteC3RealInputs

end RealC3BudgetInputs

/-! ## Section 3: Replacing the class-set cardinality by its lower bound -/

/-- The budget with an arbitrary positive lower bound `c` on the class-set
cardinality substituted into the denominator. -/
def budgetFromCardLower (N : ℕ) (hN : Odd N) (c : ℝ) : ℝ :=
  directMissingRootMass (realSpec N hN) / c + realGcdMass N hN

/-- Substituting any positive lower bound for `#(ReducedForms N)` can only
increase the explicit budget. -/
theorem realBudget_le_budgetFromCardLower {N : ℕ} {hN : Odd N} {c : ℝ}
    (h2 : 2 ≤ N) (hc0 : 0 < c) (hc : c ≤ ((ReducedForms N).card : ℝ)) :
    realBudget N hN ≤ budgetFromCardLower N hN c := by
  unfold budgetFromCardLower
  rw [realBudget_eq]
  have hmiss : 0 ≤ directMissingRootMass (realSpec N hN) :=
    directMissingRootMass_nonneg (realSpec N hN) (realSpec_hNspec N hN h2)
      (realSpec_hUspec N hN h2)
  have hdiv : directMissingRootMass (realSpec N hN) / ((ReducedForms N).card : ℝ) ≤
      directMissingRootMass (realSpec N hN) / c :=
    div_le_div_of_nonneg_left hmiss hc0 hc
  linarith

/-- The critical-line budget: the class-number lower bound
`√N / (8 log N)` of `reducedForms_card_lower_from_critical_line` substituted for
the class-set cardinality. -/
def criticalLineBudget (N : ℕ) (hN : Odd N) : ℝ :=
  budgetFromCardLower N hN ((1 / 8 : ℝ) * Real.sqrt N / Real.log N)

/-- The critical-line budget in multiplicative form. -/
theorem criticalLineBudget_eq (N : ℕ) (hN : Odd N) (hN2 : 2 ≤ N) :
    criticalLineBudget N hN =
      8 * Real.log N * directMissingRootMass (realSpec N hN) / Real.sqrt N +
        realGcdMass N hN := by
  unfold criticalLineBudget budgetFromCardLower
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have h1 : (1 : ℝ) < N := by
    have : 1 < N := by omega
    exact_mod_cast this
  have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos h1).ne'
  have hsqrt : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hNpos).ne'
  field_simp

/-- The fully explicit critical-line budget: the missing-root numerator written
in terms of `leadingBound N`, `log`, the prime factors of `N`, and `√N`, with
the class set replaced by the critical-line lower bound. -/
theorem criticalLineBudget_explicit (N : ℕ) (hN : Odd N) (hN2 : 2 ≤ N) :
    criticalLineBudget N hN =
      8 * Real.log N *
          (2 * (leadingBound N : ℝ) * (1 + Real.log (leadingBound N : ℝ)) *
            (∑ p ∈ N.primeFactors, 4 / ((p : ℝ) - 1)) *
            (Real.log (2 * (N : ℝ))) ^ (80 : ℕ)) / Real.sqrt N +
        realGcdMass N hN := by
  rw [criticalLineBudget_eq N hN hN2, directMissingRootMass_realSpec]

/-- **Reduction to the class-number inequality.**  Under the critical-line
class-number lower bound, `heps_le` follows from the single explicit inequality
`criticalLineBudget N hN ≤ 1/32`. -/
theorem heps_le_of_criticalLineBudget (line : DirichletLZerosOnLine) :
    ∃ N₀ : ℕ, ∀ (N : ℕ), N₀ ≤ N → ∀ (hN : Odd N) (h2 : 2 ≤ N),
      criticalLineBudget N hN ≤ 1 / 32 →
        directSamplerEpsilon (realSpec N hN) realEta (realGcdMass N hN) ≤ 1 / 32 := by
  obtain ⟨N₀, hcard⟩ := reducedForms_card_lower_from_critical_line line
  refine ⟨max N₀ 2, ?_⟩
  intro N hNge hN h2 hbudget
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans hNge
  have hc : (1 / 8 : ℝ) * Real.sqrt N / Real.log N ≤ ((ReducedForms N).card : ℝ) :=
    hcard N hN0 hN
  have hc0 : 0 < (1 / 8 : ℝ) * Real.sqrt N / Real.log N := by
    have hNpos : (0 : ℝ) < N := by
      have : 0 < N := by omega
      exact_mod_cast this
    have h1 : (1 : ℝ) < N := by
      have : 1 < N := by omega
      exact_mod_cast this
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos h1
    have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
    positivity
  have hle : realBudget N hN ≤ criticalLineBudget N hN :=
    realBudget_le_budgetFromCardLower h2 hc0 hc
  exact (heps_le_iff_realBudget N hN).mpr (hle.trans hbudget)

/-! ## Section 4: Removing the sampler from the gcd-exit term -/

/-- The exact one-attempt gcd-exit mass is at most the reciprocal-prime sum. -/
theorem realGcdMass_le_recip_sum (N : ℕ) (hN : Odd N) (h2 : 2 ≤ N) :
    realGcdMass N hN ≤ ∑ p ∈ N.primeFactors, (1 : ℝ) / (p : ℝ) := by
  unfold realGcdMass
  refine gcdExitProb_toReal_le (realSpec N hN) ?_ (realSpec_hUspec N hN h2)
    (realSpec_hUJ N hN)
  have hNpos : 0 < N := by
    rcases hN with ⟨k, hk⟩
    omega
  simpa using hNpos.ne'

/-- The sampler-free critical-line budget: the missing-root ratio against the
class-number lower bound plus the reciprocal-prime gcd bound. -/
def criticalLineGcdBudget (N : ℕ) (hN : Odd N) : ℝ :=
  directMissingRootMass (realSpec N hN) /
      ((1 / 8 : ℝ) * Real.sqrt N / Real.log N) +
    (∑ p ∈ N.primeFactors, (1 : ℝ) / (p : ℝ))

/-- The explicit form of the sampler-free critical-line budget. -/
theorem criticalLineGcdBudget_eq (N : ℕ) (hN : Odd N) (hN2 : 2 ≤ N) :
    criticalLineGcdBudget N hN =
      8 * Real.log N * directMissingRootMass (realSpec N hN) / Real.sqrt N +
        (∑ p ∈ N.primeFactors, (1 : ℝ) / (p : ℝ)) := by
  unfold criticalLineGcdBudget
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have h1 : (1 : ℝ) < N := by
    have : 1 < N := by omega
    exact_mod_cast this
  have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos h1).ne'
  have hsqrt : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hNpos).ne'
  field_simp

/-- The critical-line budget is at most the sampler-free budget. -/
theorem criticalLineBudget_le_gcd (N : ℕ) (hN : Odd N) (h2 : 2 ≤ N) :
    criticalLineBudget N hN ≤ criticalLineGcdBudget N hN := by
  unfold criticalLineGcdBudget
  have h := realGcdMass_le_recip_sum N hN h2
  unfold criticalLineBudget budgetFromCardLower
  linarith

/-- **Reduction to the smallest explicit numeric inequality.**  Under the
critical-line class-number lower bound and the explicit gcd-exit bound, `heps_le`
follows from the sampler-free inequality `criticalLineGcdBudget N hN ≤ 1/32`,
which mentions only `leadingBound N`, `log`, the prime factors of `N`, and
`√N`. -/
theorem heps_le_of_criticalLineGcdBudget (line : DirichletLZerosOnLine) :
    ∃ N₀ : ℕ, ∀ (N : ℕ), N₀ ≤ N → ∀ (hN : Odd N) (h2 : 2 ≤ N),
      criticalLineGcdBudget N hN ≤ 1 / 32 →
        directSamplerEpsilon (realSpec N hN) realEta (realGcdMass N hN) ≤ 1 / 32 := by
  obtain ⟨N₀, h⟩ := heps_le_of_criticalLineBudget line
  refine ⟨N₀, ?_⟩
  intro N hNge hN h2 hbudget
  exact h N hNge hN h2 ((criticalLineBudget_le_gcd N hN h2).trans hbudget)

/-- **Eventual reduction.**  If the sampler-free critical-line inequality holds
for every odd `N ≥ N₀`, then the real C3 slot is fully discharged from `N₀`
on, i.e. `ConcreteC3RealInputs` is inhabited there. -/
theorem exists_concreteC3RealInputs_of_criticalLineGcd (line : DirichletLZerosOnLine)
    (N₀ : ℕ)
    (hbudget : ∀ (N : ℕ), N₀ ≤ N → ∀ (hN : Odd N) (h2 : 2 ≤ N),
      criticalLineGcdBudget N hN ≤ 1 / 32) :
    ∃ N₁ : ℕ, ∀ (N : ℕ), N₁ ≤ N → ∀ (hN : Odd N) (h2 : 2 ≤ N),
      Nonempty (ConcreteC3RealInputs N hN h2) := by
  obtain ⟨N₁, h⟩ := heps_le_of_criticalLineGcdBudget line
  refine ⟨max N₁ N₀, ?_⟩
  intro N hNge hN h2
  have h1 : N₁ ≤ N := (le_max_left _ _).trans hNge
  have h0 : N₀ ≤ N := (le_max_right _ _).trans hNge
  exact ⟨RealC3BudgetInputs.toConcreteC3RealInputs
    ⟨h N h1 hN h2 (hbudget N h0 hN h2)⟩⟩

/-! ## Section 5: The prime-modulus case

For prime `N` the reciprocal-prime sum is `4/(N-1)`, so the `(log (2N))^80`
numerator is divided by `N` and the explicit budget does tend to zero along the
primes.  This gives a genuine *eventual* discharge of `heps_le` under
`DirichletLZerosOnLine`, restricted to prime moduli. -/

/-- The leading-coefficient bound is at most `2 √N`. -/
theorem leadingBound_le_two_sqrt {N : ℕ} (hN : 0 < N) :
    (leadingBound N : ℝ) ≤ 2 * Real.sqrt N := by
  have hU2 : leadingBound N * leadingBound N ≤ 8 * N / 3 := Nat.sqrt_le _
  have hcast : ((8 * N / 3 : ℕ) : ℝ) ≤ 8 * (N : ℝ) / 3 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    have h := Nat.div_mul_le_self (8 * N) 3
    have h' : ((8 * N / 3 : ℕ) : ℝ) * 3 ≤ ((8 * N : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h' ⊢
    linarith
  have hsq : (leadingBound N : ℝ) ^ 2 ≤ 8 * (N : ℝ) / 3 := by
    have h' := (Nat.cast_le (α := ℝ)).mpr hU2
    push_cast at h'
    linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrt : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt hNpos.le
  have htarget : (leadingBound N : ℝ) ^ 2 ≤ (2 * Real.sqrt (N : ℝ)) ^ 2 := by
    rw [mul_pow, hsqrt]
    nlinarith
  have hle := (sq_le_sq.mp htarget)
  rwa [abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt (N : ℝ))] at hle

/-- The leading-coefficient bound is at least one for `N ≥ 2`. -/
theorem one_le_leadingBound {N : ℕ} (h2 : 2 ≤ N) : 1 ≤ leadingBound N := by
  rw [leadingBound, Nat.le_sqrt]
  have h : 1 * 1 ≤ 8 * N / 3 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3)]
    omega
  simpa using h

/-- For a prime modulus, the sampler-free critical-line budget is at most
`512 (log (2N))^82 / N + 1/N`. -/
theorem criticalLineGcdBudget_le_prime {N : ℕ} (hN : Odd N) (h2 : 2 ≤ N)
    (hp : N.Prime) :
    criticalLineGcdBudget N hN ≤
      512 * (Real.log (2 * (N : ℝ))) ^ (82 : ℕ) / (N : ℝ) + 1 / (N : ℝ) := by
  have hNne2 : N ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hN
    omega
  have hN3 : 3 ≤ N := by
    have := hp.two_le
    omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hN1pos : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    linarith
  have hL1 : 1 ≤ Real.log (2 * (N : ℝ)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h4 : (4 : ℝ) ≤ 2 * (N : ℝ) := by
      have : (2 : ℝ) ≤ N := by exact_mod_cast h2
      linarith
    nlinarith [Real.exp_one_lt_d9]
  have hLpos : 0 < Real.log (2 * (N : ℝ)) := by linarith
  have hlogN0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hlogN_le : Real.log (N : ℝ) ≤ Real.log (2 * (N : ℝ)) := by
    apply Real.log_le_log hNpos
    linarith
  have hU1 : (1 : ℝ) ≤ (leadingBound N : ℝ) := by
    exact_mod_cast one_le_leadingBound h2
  have hU0 : (0 : ℝ) < (leadingBound N : ℝ) := by linarith
  have hU_le : (leadingBound N : ℝ) ≤ 2 * Real.sqrt (N : ℝ) :=
    leadingBound_le_two_sqrt (by omega)
  have hlogU0 : 0 ≤ Real.log (leadingBound N : ℝ) := Real.log_nonneg hU1
  have hlogU_le : Real.log (leadingBound N : ℝ) ≤ Real.log (2 * (N : ℝ)) := by
    have hsqrt_le : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
      nlinarith [Real.sq_sqrt hNpos.le, Real.sqrt_nonneg (N : ℝ), hNpos]
    calc
      Real.log (leadingBound N : ℝ) ≤ Real.log (2 * Real.sqrt (N : ℝ)) :=
        Real.log_le_log hU0 hU_le
      _ ≤ Real.log (2 * (N : ℝ)) := by
        apply Real.log_le_log (by positivity)
        linarith
  have hsum1 : (∑ p ∈ N.primeFactors, (1 : ℝ) / (p : ℝ)) = 1 / (N : ℝ) := by
    rw [hp.primeFactors, Finset.sum_singleton]
  have hsum4 : (∑ p ∈ N.primeFactors, 4 / ((p : ℝ) - 1)) = 4 / ((N : ℝ) - 1) := by
    rw [hp.primeFactors, Finset.sum_singleton]
  have hmiss :
      directMissingRootMass (realSpec N hN) =
        2 * (leadingBound N : ℝ) * (1 + Real.log (leadingBound N : ℝ)) *
          (4 / ((N : ℝ) - 1)) * (Real.log (2 * (N : ℝ))) ^ (80 : ℕ) := by
    rw [directMissingRootMass_realSpec, hsum4]
  rw [criticalLineGcdBudget_eq N hN h2, hsum1, hmiss]
  have hx2 : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hNpos.le
  have hxpos : (0 : ℝ) < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hS_nonneg : (0 : ℝ) ≤ 4 / ((N : ℝ) - 1) := by positivity
  have hS_le : 4 / ((N : ℝ) - 1) ≤ 8 / (N : ℝ) := by
    rw [div_le_div_iff₀ hN1pos hNpos]
    have h2R : (2 : ℝ) ≤ N := by exact_mod_cast h2
    nlinarith
  have hLnn : (0 : ℝ) ≤ Real.log (2 * (N : ℝ)) := hLpos.le
  -- Step 1: bound the missing-root factor.
  have hM : 2 * (leadingBound N : ℝ) *
        (1 + Real.log (leadingBound N : ℝ)) * (4 / ((N : ℝ) - 1)) *
        (Real.log (2 * (N : ℝ))) ^ (80 : ℕ) ≤
      2 * (2 * Real.sqrt (N : ℝ)) * (2 * Real.log (2 * (N : ℝ))) *
        (4 / ((N : ℝ) - 1)) * (Real.log (2 * (N : ℝ))) ^ (80 : ℕ) := by
    have h1log : 1 + Real.log (leadingBound N : ℝ) ≤
        2 * Real.log (2 * (N : ℝ)) := by linarith
    have hUL : (leadingBound N : ℝ) * (1 + Real.log (leadingBound N : ℝ)) ≤
        (2 * Real.sqrt (N : ℝ)) * (2 * Real.log (2 * (N : ℝ))) :=
      mul_le_mul hU_le h1log (by linarith) (by positivity)
    have hpow : (0 : ℝ) ≤ (Real.log (2 * (N : ℝ))) ^ (80 : ℕ) := pow_nonneg hLnn _
    calc
      2 * (leadingBound N : ℝ) *
          (1 + Real.log (leadingBound N : ℝ)) * (4 / ((N : ℝ) - 1)) *
          (Real.log (2 * (N : ℝ))) ^ (80 : ℕ)
        = 2 * ((leadingBound N : ℝ) * (1 + Real.log (leadingBound N : ℝ))) *
            (4 / ((N : ℝ) - 1)) * (Real.log (2 * (N : ℝ))) ^ (80 : ℕ) := by ring
      _ ≤ 2 * ((2 * Real.sqrt (N : ℝ)) * (2 * Real.log (2 * (N : ℝ)))) *
            (4 / ((N : ℝ) - 1)) * (Real.log (2 * (N : ℝ))) ^ (80 : ℕ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hUL (by norm_num)) hS_nonneg) hpow
      _ = 2 * (2 * Real.sqrt (N : ℝ)) * (2 * Real.log (2 * (N : ℝ))) *
            (4 / ((N : ℝ) - 1)) * (Real.log (2 * (N : ℝ))) ^ (80 : ℕ) := by ring
  -- Step 2: multiply by the logarithmic prefactor.
  have hstep1 : 8 * Real.log (N : ℝ) *
        (2 * (leadingBound N : ℝ) *
          (1 + Real.log (leadingBound N : ℝ)) * (4 / ((N : ℝ) - 1)) *
          (Real.log (2 * (N : ℝ))) ^ (80 : ℕ)) / Real.sqrt (N : ℝ) ≤
      8 * Real.log (2 * (N : ℝ)) *
        (2 * (2 * Real.sqrt (N : ℝ)) * (2 * Real.log (2 * (N : ℝ))) *
          (4 / ((N : ℝ) - 1)) * (Real.log (2 * (N : ℝ))) ^ (80 : ℕ)) /
        Real.sqrt (N : ℝ) := by
    rw [div_le_div_iff_of_pos_right hxpos]
    have h8log : 8 * Real.log (N : ℝ) ≤ 8 * Real.log (2 * (N : ℝ)) := by
      linarith
    have hMnn : (0 : ℝ) ≤ 2 * (leadingBound N : ℝ) *
        (1 + Real.log (leadingBound N : ℝ)) * (4 / ((N : ℝ) - 1)) *
        (Real.log (2 * (N : ℝ))) ^ (80 : ℕ) := by
      have hpow : (0 : ℝ) ≤ (Real.log (2 * (N : ℝ))) ^ (80 : ℕ) := pow_nonneg hLnn _
      have : (0 : ℝ) ≤ 1 + Real.log (leadingBound N : ℝ) := by linarith
      positivity
    exact mul_le_mul h8log hM hMnn (by positivity)
  -- Step 3: simplify the middle expression.
  have hstep2 :
      8 * Real.log (2 * (N : ℝ)) *
        (2 * (2 * Real.sqrt (N : ℝ)) * (2 * Real.log (2 * (N : ℝ))) *
          (4 / ((N : ℝ) - 1)) * (Real.log (2 * (N : ℝ))) ^ (80 : ℕ)) /
        Real.sqrt (N : ℝ) =
      64 * (4 / ((N : ℝ) - 1)) * (Real.log (2 * (N : ℝ))) ^ (82 : ℕ) := by
    have hxne : Real.sqrt (N : ℝ) ≠ 0 := hxpos.ne'
    field_simp
    ring
  -- Step 4: absorb `4/(N-1) ≤ 8/N`.
  have hstep3 : 64 * (4 / ((N : ℝ) - 1)) * (Real.log (2 * (N : ℝ))) ^ (82 : ℕ) ≤
      512 * (Real.log (2 * (N : ℝ))) ^ (82 : ℕ) / (N : ℝ) := by
    have hpow : (0 : ℝ) ≤ (Real.log (2 * (N : ℝ))) ^ (82 : ℕ) := pow_nonneg hLnn _
    calc
      64 * (4 / ((N : ℝ) - 1)) * (Real.log (2 * (N : ℝ))) ^ (82 : ℕ)
        ≤ 64 * (8 / (N : ℝ)) * (Real.log (2 * (N : ℝ))) ^ (82 : ℕ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hS_le (by norm_num)) hpow
      _ = 512 * (Real.log (2 * (N : ℝ))) ^ (82 : ℕ) / (N : ℝ) := by ring
  have hmain :
      8 * Real.log (N : ℝ) *
        (2 * (leadingBound N : ℝ) *
          (1 + Real.log (leadingBound N : ℝ)) * (4 / ((N : ℝ) - 1)) *
          (Real.log (2 * (N : ℝ))) ^ (80 : ℕ)) / Real.sqrt (N : ℝ) ≤
      512 * (Real.log (2 * (N : ℝ))) ^ (82 : ℕ) / (N : ℝ) :=
    hstep1.trans (hstep2.trans_le hstep3)
  linarith

/-- **Eventual `heps_le` for prime moduli.**  Under `DirichletLZerosOnLine`,
for every sufficiently large odd prime `N` the canonical real C3 inputs satisfy
the small-budget inequality `heps_le` unconditionally. -/
theorem eventually_heps_le_of_prime (line : DirichletLZerosOnLine) :
    ∃ N₀ : ℕ, ∀ (N : ℕ), N₀ ≤ N → ∀ (hN : Odd N) (h2 : 2 ≤ N), N.Prime →
      directSamplerEpsilon (realSpec N hN) realEta (realGcdMass N hN) ≤ 1 / 32 := by
  obtain ⟨N₁, hred⟩ := heps_le_of_criticalLineGcdBudget line
  have hbase : Tendsto (fun x : ℝ => Real.log x ^ (82 : ℕ) / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 82 one_ne_zero
  have harg : Tendsto (fun N : ℕ => (2 : ℝ) * (N : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
      tendsto_natCast_atTop_atTop
  have hcomp : Tendsto
      (fun N : ℕ => Real.log (2 * (N : ℝ)) ^ (82 : ℕ) / (2 * (N : ℝ)))
      atTop (𝓝 0) :=
    hbase.comp harg
  have hscaled : Tendsto
      (fun N : ℕ => 512 * Real.log (2 * (N : ℝ)) ^ (82 : ℕ) / (N : ℝ))
      atTop (𝓝 0) := by
    have h := hcomp.const_mul (1024 : ℝ)
    have hfun : (fun N : ℕ => 512 * Real.log (2 * (N : ℝ)) ^ (82 : ℕ) / (N : ℝ))
        =ᶠ[atTop]
        (fun N : ℕ => 1024 * (Real.log (2 * (N : ℝ)) ^ (82 : ℕ) / (2 * (N : ℝ)))) := by
      filter_upwards [eventually_ne_atTop (0 : ℕ)] with N hN
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
      field_simp
      ring
    simpa using (tendsto_congr' hfun).mpr h
  have hbig : ∀ᶠ N : ℕ in atTop,
      512 * Real.log (2 * (N : ℝ)) ^ (82 : ℕ) / (N : ℝ) ≤ 1 / 64 :=
    hscaled.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 64))
  have hsmall : ∀ᶠ N : ℕ in atTop, (1 : ℝ) / (N : ℝ) ≤ 1 / 64 := by
    filter_upwards [eventually_ge_atTop (64 : ℕ)] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have : 0 < N := by omega
      exact_mod_cast this
    rw [div_le_div_iff₀ hNpos (by norm_num : (0 : ℝ) < 64)]
    norm_num
    exact_mod_cast hN
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hbig.and hsmall)
  refine ⟨max N₁ N₂, ?_⟩
  intro N hNge hN h2 hp
  have h1 : N₁ ≤ N := (le_max_left _ _).trans hNge
  have h2' : N₂ ≤ N := (le_max_right _ _).trans hNge
  obtain ⟨hb, hs⟩ := hN₂ N h2'
  exact hred N h1 hN h2
    ((criticalLineGcdBudget_le_prime hN h2 hp).trans (by linarith))


/-- **Eventual real C3 inputs for prime moduli.**  Under
`DirichletLZerosOnLine`, every sufficiently large odd prime modulus carries a
fully discharged `ConcreteC3RealInputs` record. -/
theorem exists_concreteC3RealInputs_of_prime (line : DirichletLZerosOnLine) :
    ∃ N₀ : ℕ, ∀ (N : ℕ), N₀ ≤ N → ∀ (hN : Odd N) (h2 : 2 ≤ N), N.Prime →
      Nonempty (ConcreteC3RealInputs N hN h2) := by
  obtain ⟨N₀, h⟩ := eventually_heps_le_of_prime line
  exact ⟨N₀, fun N hNge hN h2 hp =>
    ⟨RealC3BudgetInputs.toConcreteC3RealInputs ⟨h N hNge hN h2 hp⟩⟩⟩

/-! ## Section 6: Axiom audit -/

#print axioms Cogentic.RandomizedConcreteC3Budget.realEta_hideal
#print axioms Cogentic.RandomizedConcreteC3Budget.realGcdMass_hgcd
#print axioms Cogentic.RandomizedConcreteC3Budget.realEpoch_actual_eq
#print axioms Cogentic.RandomizedConcreteC3Budget.realBudget_eq
#print axioms Cogentic.RandomizedConcreteC3Budget.realBudget_explicit
#print axioms Cogentic.RandomizedConcreteC3Budget.RealC3BudgetInputs.toConcreteC3RealInputs
#print axioms Cogentic.RandomizedConcreteC3Budget.RealC3BudgetInputs.tv_le
#print axioms Cogentic.RandomizedConcreteC3Budget.realBudget_le_budgetFromCardLower
#print axioms Cogentic.RandomizedConcreteC3Budget.criticalLineBudget_explicit
#print axioms Cogentic.RandomizedConcreteC3Budget.heps_le_of_criticalLineBudget
#print axioms Cogentic.RandomizedConcreteC3Budget.realGcdMass_le_recip_sum
#print axioms Cogentic.RandomizedConcreteC3Budget.heps_le_of_criticalLineGcdBudget
#print axioms Cogentic.RandomizedConcreteC3Budget.exists_concreteC3RealInputs_of_criticalLineGcd
#print axioms Cogentic.RandomizedConcreteC3Budget.leadingBound_le_two_sqrt
#print axioms Cogentic.RandomizedConcreteC3Budget.one_le_leadingBound
#print axioms Cogentic.RandomizedConcreteC3Budget.criticalLineGcdBudget_le_prime
#print axioms Cogentic.RandomizedConcreteC3Budget.eventually_heps_le_of_prime
#print axioms Cogentic.RandomizedConcreteC3Budget.exists_concreteC3RealInputs_of_prime

end Cogentic.RandomizedConcreteC3Budget
