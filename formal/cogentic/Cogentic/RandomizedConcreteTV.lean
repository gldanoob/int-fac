import Cogentic.RandomizedConcreteEpochCost

/-!
# A concrete `DirectFormSpec` and C3 TV instance (wave 3, W19)

This file instantiates the C3 total-variation slot of
`Cogentic.RandomizedConcreteEpochCost` with a completely explicit, tiny form
specification.  It is a *structural* toy instance, not the paper's class-group
sampler: it exists to exhibit a concrete `DirectFormSpec`, a concrete epoch
whose `actual` law is literally `directRetryConditionalPMF` and whose `ideal`
law is literally `PMF.uniformOfFinset` on the specification's canonical forms,
and a concrete `C3Inputs` for it.

## The specification

`singletonSpec Form f₀` is a `DirectFormSpec` on an arbitrary type with a
distinguished element `f₀`:

* modulus `N = 2`;
* leading-coefficient range `U = 1`;
* `roots A = {0}` for `A = 1` and `∅` otherwise;
* `buildForm A b = some f₀` exactly at `(A, b) = (1, 0)`;
* the single canonical form `allForms = {f₀}`, with `leadCoeff = 1` and
  `midCoeff = 0`.

All `DirectFormSpec` fields are proved directly; no `Classical.choose` is used
for the form, its coefficients, or `buildForm`.

## The epoch

The concrete epoch family `toyEpoch : ∀ n, ConcreteEpochData n` has one public
coin and one hidden label, so its sample space is `Unit × (Unit → (ZMod n)ˣ)`;
its solver always rejects, its public universe is `{none}`, and all ten named
stage costs are zero.  The laws are

* `ideal = PMF.uniformOfFinset (toySpec n).allForms _`;
* `actual = directRetryConditionalPMF (toySpec n) _ _ _`.

Because `toySpec n` has a single canonical form of leading coefficient `1`,
which is coprime to `N = 2`, the direct sampler is already exactly uniform on
its (singleton) coprime-form set.  We prove the exact identity
`toy_tv_eq_zero : pmfTotalVariation ideal actual = 0` and obtain a genuine
`C3Inputs` with `ε = 0`.  The zero is *not* assumed: it is the true TV distance
of the chosen pair (`toyActual_eq_ideal`).

## What is and is not proved

All structural fields of `ConcreteC3Hypotheses` are proved, as the fields of
the local record `ToyC3Structural`, stated directly for `toySpec`:

`hUJ`, `hJ₀`, `hcop`, `hall`, `hNspec`, `hUspec`, the root-count majorant
`R ≡ 1` together with `hR_ge`, `hR1`, `hRmul`, `hRcop`, `hRloc`, the exact-law
field `hactual`, and the ideal-law field `hideal`.

The local record omits the specification field itself, because the external
`ConcreteC3Hypotheses` bakes in a `DecidableEq` instance argument for
`(D n).Sample`; specializing to the concrete `toySpec` avoids transporting a
structure across different instance arguments.  Every *mathematical* field of
`ConcreteC3Hypotheses` is present with the same type.

The only field of `ConcreteC3Hypotheses` that is **not** instantiated for the
tiny `N = 2` spec is the crude small-budget inequality `heps_le` for
`directSamplerEpsilon`.  That expression contains the loss factor
`(log (2N))^80`, which at the toy scale `N = 2`, `U = 1` is astronomically
larger than `1/32`; it is a genuine numeric inequality that does not follow
from the structural fields.  For the tiny spec the structural fields are
bundled in `ToyC3Structural` and the bridge `c3Inputs_of_structural` produces a
`C3Inputs` as soon as a caller supplies a TV bound.  The *true* TV estimate,
which is what C3 actually needs, is proved unconditionally
(`toy_tv_le_zero`) and gives `toyC3Inputs` with the honest error `ε = 0`.

## Section 5: a genuine full `ConcreteC3Hypotheses`

The small-budget obstruction is removed by a large-prime modulus.  `bigPrime`
is the least prime factor of `bigBound! + 1` (Euclid's argument, no
`Classical.choose`), hence prime and at least `bigBound`.  For a prime modulus
`P` the missing-root sum is `4/(P-1)`, and the elementary bound
`(log x)^80 ≤ 160^80 * sqrt x` shows

```
directMissingRootMass (modSpec P n) / #allForms ≤ 1/32     (P ≥ bigBound).
```

The proof is parametric in `P` (`modSpec_missing_div_le`) so the huge
`bigPrime` term is never unfolded by the arithmetic tactics.  The epoch
`bigEpoch` uses a one-point coin type `BigCoins` whose canonical `DecidableEq`
instance is *itself* `Classical.decEq`; this makes the instance argument match
the private `instDecEqCoins` used by the external `ConcreteC3Hypotheses`
declaration, so the literal instance

```lean
bigConcreteC3 : ConcreteC3Hypotheses bigEpoch
```

is constructed with `heps_le := big_heps_le`.  `bigC3Inputs` is its `C3Inputs`
via the existing bridge.

No `sorry`, `admit`, `axiom`, `native_decide`, or `Classical.choose` occurs in
this file.
-/

namespace Cogentic.RandomizedConcreteTV

set_option linter.style.haveILetI false

open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedConcreteEpochCost
open Cogentic.RandomizedDirectClassSampler
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochTV
open Cogentic.RandomizedFiniteSupportTV
open scoped BigOperators ENNReal

/-! ## Section 1: A one-form `DirectFormSpec` -/

/-- The toy sample space at modulus `n`: one public coin and one hidden label.
This is definitionally `Unit × (Unit → (ZMod n)ˣ)`, the sample space of the
concrete epoch below. -/
abbrev ToySample (n : ℕ) : Type := Unit × (Unit → (ZMod n)ˣ)

/-- The unique toy form. -/
def toyForm (n : ℕ) : ToySample n := ((), fun _ => 1)

/-- A `DirectFormSpec` with a single canonical form.  The modulus is `2`, the
leading-coefficient range is `{1}`, and `f₀` is the only canonical form, with
leading coefficient `1` and middle coefficient `0`. -/
noncomputable def singletonSpec (Form : Type*) [DecidableEq Form] (f₀ : Form) :
    DirectFormSpec Form where
  N := 2
  U := 1
  roots := fun A => if A = 1 then {0} else ∅
  roots_card_le := by
    intro A hA1 hAU _
    have hA : A = 1 := by omega
    subst hA
    simp
  buildForm := fun A b => if A = 1 ∧ b = 0 then some f₀ else none
  allForms := {f₀}
  leadCoeff := fun _ => 1
  midCoeff := fun _ => 0
  leadCoeff_pos := by
    intro f _
    simp
  leadCoeff_le := by
    intro f _
    simp
  midCoeff_mem_roots := by
    intro f _
    simp
  coeff_injective := by
    intro f hf g hg _
    have hf' : f = f₀ := by simpa using hf
    have hg' : g = f₀ := by simpa using hg
    rw [hf', hg']
  buildForm_eq_some_iff := by
    intro A b f hA1 hAU _ hb
    have hA : A = 1 := by omega
    subst hA
    have hb0 : b = 0 := by
      simpa using hb
    subst hb0
    simp [eq_comm]

/-- The toy specification on the epoch's sample space. -/
noncomputable def toySpec (n : ℕ) : DirectFormSpec (ToySample n) :=
  singletonSpec (ToySample n) (toyForm n)

@[simp] theorem toySpec_N (n : ℕ) : (toySpec n).N = 2 := rfl

@[simp] theorem toySpec_U (n : ℕ) : (toySpec n).U = 1 := rfl

@[simp] theorem toySpec_allForms (n : ℕ) :
    (toySpec n).allForms = {toyForm n} := rfl

@[simp] theorem toySpec_roots_one (n : ℕ) : (toySpec n).roots 1 = {0} := rfl

@[simp] theorem toySpec_leadCoeff (n : ℕ) (f : ToySample n) :
    (toySpec n).leadCoeff f = 1 := rfl

@[simp] theorem toySpec_midCoeff (n : ℕ) (f : ToySample n) :
    (toySpec n).midCoeff f = 0 := rfl

/-- The toy canonical-form set is nonempty. -/
theorem toySpec_allForms_nonempty (n : ℕ) : (toySpec n).allForms.Nonempty :=
  ⟨toyForm n, by simp⟩

/-- The coprime canonical-form set of the toy spec is the full canonical set. -/
theorem toySpec_coprimeForms_eq (n : ℕ) :
    (toySpec n).coprimeForms = {toyForm n} := by
  simp [DirectFormSpec.coprimeForms, toySpec, singletonSpec]

/-- The toy coprime-form set is nonempty. -/
theorem toySpec_coprimeForms_nonempty (n : ℕ) :
    (toySpec n).coprimeForms.Nonempty := by
  rw [toySpec_coprimeForms_eq]
  exact ⟨toyForm n, Finset.mem_singleton_self _⟩

/-- The dyadic proposal depth used by the toy sampler. -/
def toyJ : ℕ := 0

/-- The retry count used by the toy sampler. -/
def toyJ₀ : ℕ := 1

/-- The leading-coefficient bound `U = 1` is below `2 ^ 0`. -/
theorem toySpec_hUJ (n : ℕ) : (toySpec n).U ≤ 2 ^ toyJ := by
  simp [toySpec, singletonSpec, toyJ]

/-- The retry count is positive. -/
theorem toySpec_hJ₀ : 1 ≤ toyJ₀ := le_rfl

/-! ## Section 2: The concrete epoch with the requested laws -/

/-- The ideal law: uniform on the toy canonical forms. -/
noncomputable def toyIdeal (n : ℕ) : PMF (ToySample n) :=
  PMF.uniformOfFinset (toySpec n).allForms (toySpec_allForms_nonempty n)

/-- The actual law: the conditional direct-sampler law of the toy spec. -/
noncomputable def toyActual (n : ℕ) : PMF (ToySample n) :=
  directRetryConditionalPMF (toySpec n) (toySpec_hUJ n) toySpec_hJ₀
    (toySpec_coprimeForms_nonempty n)

/-- The concrete S0–S9 epoch family.  The sample space is `ToySample n`, the
solver always rejects, the explicit public universe is `{none}`, and every
named stage costs zero. -/
noncomputable def toyEpoch (n : ℕ) : ConcreteEpochData n where
  Coins := Unit
  Label := Unit
  FieldId := Unit
  ideal := toyIdeal n
  actual := toyActual n
  solver := fun _ _ => none
  publicCandidates := {none}
  solver_mem_candidates := by
    intro _
    simp
  candidates_complete := by
    intro t ht hsome
    obtain rfl : t = none := by simpa using ht
    simp at hsome
  stageCosts :=
    { s0 := fun _ => 0
      s1 := fun _ => 0
      s2 := fun _ => 0
      s3 := fun _ => 0
      s4 := fun _ => 0
      s5 := fun _ => 0
      s6 := fun _ => 0
      s7 := fun _ => 0
      s8 := fun _ => 0
      s9 := fun _ => 0 }

@[simp] theorem toyEpoch_ideal (n : ℕ) : (toyEpoch n).ideal = toyIdeal n := rfl

@[simp] theorem toyEpoch_actual (n : ℕ) : (toyEpoch n).actual = toyActual n := rfl

/-- The direct sampler is exactly uniform on the toy coprime-form set.  This is
`directRetryConditionalPMF_eq_uniform` at the toy spec. -/
theorem toyActual_eq_uniform (n : ℕ) :
    toyActual n =
      PMF.uniformOfFinset (toySpec n).coprimeForms
        (toySpec_coprimeForms_nonempty n) :=
  directRetryConditionalPMF_eq_uniform (toySpec n) (toySpec_hUJ n) toySpec_hJ₀
    (toySpec_coprimeForms_nonempty n)

/-- The actual law equals the ideal law: both are uniform on the single toy
form.  The zero TV distance below is therefore genuine, not a bookkeeping
assumption. -/
theorem toyActual_eq_ideal (n : ℕ) : toyActual n = toyIdeal n := by
  rw [toyActual_eq_uniform]
  ext f
  simp only [toyIdeal, PMF.uniformOfFinset_apply]
  rw [toySpec_coprimeForms_eq, toySpec_allForms]

/-- The ideal-to-actual TV distance of the concrete epoch is exactly zero. -/
theorem toy_tv_eq_zero (n : ℕ) :
    pmfTotalVariation (toyEpoch n).ideal (toyEpoch n).actual = 0 := by
  have h : (toyEpoch n).ideal = (toyEpoch n).actual := by
    change toyIdeal n = toyActual n
    exact (toyActual_eq_ideal n).symm
  rw [h, pmfTotalVariation_self]

/-- The ideal-to-actual TV distance of the concrete epoch is at most zero. -/
theorem toy_tv_le_zero (n : ℕ) :
    pmfTotalVariation (toyEpoch n).ideal (toyEpoch n).actual ≤ 0 :=
  le_of_eq (toy_tv_eq_zero n)

/-! ## Section 3: The structural C3 fields -/

/-- The structural fields of `ConcreteC3Hypotheses`
(`Cogentic.RandomizedConcreteEpochCost`), specialized to the concrete toy
specification and with the crude small-budget inequality `heps_le` removed.

The specification field is not stored here: `toySpec` is a fixed concrete
definition.  Every other field of `ConcreteC3Hypotheses` appears with the same
type.  `c3Inputs_of_structural` is the C3 bridge. -/
structure ToyC3Structural where
  /-- Dyadic proposal depth. -/
  J : ℕ
  /-- Retry count. -/
  J₀ : ℕ
  /-- The leading-coefficient bound is below the proposal range. -/
  hUJ : ∀ n, (toySpec n).U ≤ 2 ^ J
  /-- The retry count is positive. -/
  hJ₀ : 1 ≤ J₀
  /-- Accepted coprime forms exist. -/
  hcop : ∀ n, (toySpec n).coprimeForms.Nonempty
  /-- The canonical form universe is nonempty. -/
  hall : ∀ n, (toySpec n).allForms.Nonempty
  /-- The modulus is at least `2`. -/
  hNspec : ∀ n, 2 ≤ (toySpec n).N
  /-- The leading-coefficient bound is at least `1`. -/
  hUspec : ∀ n, 1 ≤ (toySpec n).U
  /-- Root-count majorant. -/
  R : ℕ → ℕ → ℕ
  /-- `R` dominates the number of canonical roots. -/
  hR_ge : ∀ n (A : ℕ), A ∈ Finset.Icc 1 ((toySpec n).U) →
    ((toySpec n).roots A).card ≤ R n A
  /-- Normalization `R n 1 = 1`. -/
  hR1 : ∀ n, R n 1 = 1
  /-- Multiplicativity of `R n` on coprime arguments. -/
  hRmul : ∀ n (a b : ℕ), Nat.Coprime a b → R n (a * b) = R n a * R n b
  /-- Coprime root-count majorant. -/
  hRcop : ∀ n (m : ℕ), 1 ≤ m → Nat.Coprime m ((toySpec n).N) →
    R n m ≤ 2 * 2 ^ m.primeFactors.card
  /-- Prime-power root-count majorant. -/
  hRloc : ∀ n (p : ℕ), p ∈ ((toySpec n).N).primeFactors → ∀ k, 1 ≤ k →
    R n (p ^ k) ≤ 2 * p ^ (k / 2)
  /-- Ideal-law distance to uniform on the canonical forms. -/
  eta : ℕ → ℝ
  /-- One-attempt gcd-exit budget. -/
  gcdMass : ℕ → ℝ
  /-- The ideal law is within `eta n` of uniform. -/
  hideal : ∀ n,
    pmfTotalVariation (toyIdeal n)
      (PMF.uniformOfFinset (toySpec n).allForms
        (toySpec_allForms_nonempty n)) ≤ eta n
  /-- The gcd-exit probability is bounded by `gcdMass n`. -/
  hgcd : ∀ n, (gcdExitProb (toySpec n) J).toReal ≤ gcdMass n
  /-- Exact-law hypothesis. -/
  hactual : ∀ n,
    toyActual n = directRetryConditionalPMF (toySpec n) (hUJ n) hJ₀ (hcop n)

/-- The structural C3 fields of the concrete toy epoch, all proved. -/
noncomputable def toyStructural : ToyC3Structural where
  J := toyJ
  J₀ := toyJ₀
  hUJ := toySpec_hUJ
  hJ₀ := toySpec_hJ₀
  hcop := toySpec_coprimeForms_nonempty
  hall := toySpec_allForms_nonempty
  hNspec := by
    intro _
    simp
  hUspec := by
    intro _
    simp
  R := fun _ _ => 1
  hR_ge := by
    intro n A hA
    obtain ⟨hA1, hAU⟩ := Finset.mem_Icc.mp hA
    have hAU' : A ≤ 1 := by simpa using hAU
    have hAeq : A = 1 := by omega
    subst hAeq
    rw [toySpec_roots_one]
    simp
  hR1 := by
    intro _
    rfl
  hRmul := by
    intro _ a b _
    rfl
  hRcop := by
    intro _ m _ _
    have hpos : 0 < 2 ^ m.primeFactors.card := pow_pos (by norm_num) _
    omega
  hRloc := by
    intro n p hp k hk
    have hp2 : p = 2 := by
      have hN : (toySpec n).N = 2 := rfl
      rw [hN] at hp
      have hpf : p ∈ (2 ^ 1 : ℕ).primeFactors := by simpa using hp
      rw [Nat.primeFactors_prime_pow (p := 2) (k := 1) (by norm_num) Nat.prime_two] at hpf
      simpa using hpf
    subst hp2
    have hpos : 0 < 2 ^ (k / 2) := pow_pos (by norm_num) _
    omega
  eta := fun _ => 0
  gcdMass := fun _ => 0
  hideal := by
    intro n
    exact le_of_eq (pmfTotalVariation_self (toyIdeal n))
  hgcd := by
    intro n
    have hzero : gcdExitProb (toySpec n) toyJ = 0 := by
      rw [gcdExitProb_eq_dyadic_noncoprime]
      simp [toySpec, singletonSpec, toyJ]
    rw [hzero]
    simp
  hactual := by
    intro n
    rfl

/-- **The standard C3 estimate from the structural fields.**  Given a
`ToyC3Structural` record and the crude small-budget inequality `heps_le`, the
ideal-to-actual TV distance is bounded by the standard
`directSamplerEpsilon` budget.  This is exactly the estimate proved by
`ConcreteC3Hypotheses.tv_le`, reproduced here from the local record. -/
theorem structural_tv_le_directSamplerEpsilon (H : ToyC3Structural)
    {n : ℕ} (hN : 3 ≤ n) :
    pmfTotalVariation (toyIdeal n) (toyActual n) ≤
      directSamplerEpsilon (toySpec n) (H.eta n) (H.gcdMass n) := by
  haveI : NeZero n := ⟨by omega⟩
  have hTV := pmfTotalVariation_le_directSamplerEpsilon (toySpec n) (H.hUJ n) H.hJ₀
    (H.hcop n) (H.hall n) (H.hNspec n) (H.hUspec n) (H.R n)
    (fun A hA => H.hR_ge n A hA) (H.hR1 n) (fun a b h => H.hRmul n a b h)
    (fun m hm hc => H.hRcop n m hm hc) (fun p hp k hk => H.hRloc n p hp k hk)
    (H.hideal n) (H.hgcd n)
  rwa [← H.hactual n] at hTV

/-! ## Section 4: The C3 bridge and a concrete `C3Inputs` -/

/-- **C3 bridge from the structural fields.**  A `ToyC3Structural` record, an
explicit per-`n` error `ε` with `0 ≤ ε n ≤ 1/32`, and the true TV bound produce
`C3Inputs` for the concrete epoch. -/
noncomputable def c3Inputs_of_structural (_H : ToyC3Structural)
    (ε : ℕ → ℝ) (hε0 : ∀ n, 0 ≤ ε n) (hε : ∀ n, ε n ≤ 1 / 32)
    (htv : ∀ n, pmfTotalVariation (toyEpoch n).ideal (toyEpoch n).actual ≤ ε n) :
    C3Inputs (concreteCostFamily toyEpoch) where
  epsilon := ε
  epsilon_nonneg := hε0
  epsilon_le := hε
  tv_le := by
    intro n hN _
    change pmfTotalVariation (toyEpoch n).ideal (toyEpoch n).actual ≤ ε n
    exact htv n

/-- **The concrete C3 inputs.**  For the toy epoch the true ideal-to-actual TV
distance is exactly zero (`toy_tv_eq_zero`), so the concrete budget is
`ε = 0`.  The error is not assumed small: it is proved to vanish for this
actual/ideal pair. -/
noncomputable def toyC3Inputs : C3Inputs (concreteCostFamily toyEpoch) :=
  c3Inputs_of_structural toyStructural (fun _ => 0)
    (by intro _; norm_num) (by intro _; norm_num) toy_tv_le_zero

/-- The concrete C3 budget of `toyC3Inputs` really is the true TV distance:
it equals `pmfTotalVariation ideal actual` at every index. -/
theorem toyC3Inputs_epsilon_eq_tv (n : ℕ) :
    toyC3Inputs.epsilon n =
      pmfTotalVariation (toyEpoch n).ideal (toyEpoch n).actual := by
  rw [toy_tv_eq_zero]
  rfl

/-- The toy C3 input record has zero budget, and this budget is the actual TV
distance of the chosen pair. -/
theorem toyC3Inputs_epsilon_zero (n : ℕ) : toyC3Inputs.epsilon n = 0 := rfl

/-! ## Section 5: A large-prime modulus and the full C3 instance -/

/-- General-modulus version of `singletonSpec`: one canonical form, leading
coefficient `1`, with modulus `N` and leading-coefficient range `1`. -/
noncomputable def singletonSpecMod (N : ℕ) (Form : Type*) [DecidableEq Form] (f₀ : Form) :
    DirectFormSpec Form where
  N := N
  U := 1
  roots := fun A => if A = 1 then {0} else ∅
  roots_card_le := by
    intro A hA1 hAU _
    have hA : A = 1 := by omega
    subst hA
    simp
  buildForm := fun A b => if A = 1 ∧ b = 0 then some f₀ else none
  allForms := {f₀}
  leadCoeff := fun _ => 1
  midCoeff := fun _ => 0
  leadCoeff_pos := by
    intro f _
    simp
  leadCoeff_le := by
    intro f _
    simp
  midCoeff_mem_roots := by
    intro f _
    simp
  coeff_injective := by
    intro f hf g hg _
    have hf' : f = f₀ := by simpa using hf
    have hg' : g = f₀ := by simpa using hg
    rw [hf', hg']
  buildForm_eq_some_iff := by
    intro A b f hA1 hAU _ hb
    have hA : A = 1 := by omega
    subst hA
    have hb0 : b = 0 := by
      simpa using hb
    subst hb0
    simp [eq_comm]

/-- A one-point coin type whose canonical decidable equality is the classical
one.  Using a fresh type (rather than `Unit`) makes the `DecidableEq` instance
synthesized here definitionally equal to the private
`RandomizedConcreteEpochCost.instDecEqCoins` instance used by the external
`ConcreteC3Hypotheses` declaration, which is `Classical.decEq` on the coin
type. -/
inductive BigCoins : Type
  | mk

instance : Fintype BigCoins where
  elems := {BigCoins.mk}
  complete := by
    intro x
    cases x
    simp

noncomputable instance bigCoinsDecEq : DecidableEq BigCoins :=
  Classical.decEq _

/-- The sample space of the large-modulus toy epoch. -/
abbrev BigSample (n : ℕ) : Type := BigCoins × (Unit → (ZMod n)ˣ)

/-- The unique large-modulus toy form. -/
def bigForm (n : ℕ) : BigSample n := (BigCoins.mk, fun _ => 1)

/-- The modulus threshold above which the crude missing-root numerator is
dominated by the one-form class set. -/
def bigBound : ℕ := 2 * 512 ^ 2 * 160 ^ 160

/-- A prime above `bigBound`, constructed as the least prime factor of
`bigBound! + 1` (Euclid's argument).  This is an explicit term, not a
`Classical.choose`. -/
def bigPrime : ℕ := Nat.minFac (Nat.factorial bigBound + 1)

theorem bigPrime_prime : bigPrime.Prime := by
  apply Nat.minFac_prime
  have h := Nat.factorial_pos bigBound
  omega

theorem bigBound_le_bigPrime : bigBound ≤ bigPrime := by
  apply Nat.le_of_not_gt
  intro hlt
  have hdvd_fact : bigPrime ∣ Nat.factorial bigBound :=
    Nat.dvd_factorial (Nat.minFac_pos _) (Nat.le_of_lt hlt)
  have hdvd : bigPrime ∣ Nat.factorial bigBound + 1 := Nat.minFac_dvd _
  have h1 : bigPrime ∣ 1 := (Nat.dvd_add_iff_right hdvd_fact).2 hdvd
  exact bigPrime_prime.not_dvd_one h1

theorem bigPrime_primeFactors : bigPrime.primeFactors = {bigPrime} := by
  have h := Nat.primeFactors_prime_pow (p := bigPrime) (k := 1) (by norm_num) bigPrime_prime
  simpa using h

/-- The one-form specification with modulus parameter `P`. -/
noncomputable def modSpec (P : ℕ) (n : ℕ) : DirectFormSpec (BigSample n) :=
  singletonSpecMod P (BigSample n) (bigForm n)

@[simp] theorem modSpec_N (P n : ℕ) : (modSpec P n).N = P := rfl

@[simp] theorem modSpec_U (P n : ℕ) : (modSpec P n).U = 1 := rfl

@[simp] theorem modSpec_allForms (P n : ℕ) :
    (modSpec P n).allForms = {bigForm n} := rfl

@[simp] theorem modSpec_roots_one (P n : ℕ) : (modSpec P n).roots 1 = {0} := rfl

theorem modSpec_allForms_nonempty (P n : ℕ) : (modSpec P n).allForms.Nonempty := by
  simp

theorem modSpec_coprimeForms_eq (P n : ℕ) :
    (modSpec P n).coprimeForms = {bigForm n} := by
  simp [DirectFormSpec.coprimeForms, modSpec, singletonSpecMod]

theorem modSpec_coprimeForms_nonempty (P n : ℕ) :
    (modSpec P n).coprimeForms.Nonempty := by
  rw [modSpec_coprimeForms_eq]
  exact ⟨bigForm n, Finset.mem_singleton_self _⟩

/-- The dyadic proposal depth of the large toy sampler. -/
def bigJ : ℕ := 0

/-- The retry count of the large toy sampler. -/
def bigJ₀ : ℕ := 1

theorem modSpec_hUJ (P n : ℕ) : (modSpec P n).U ≤ 2 ^ bigJ := by
  simp [modSpec, singletonSpecMod, bigJ]

theorem bigJ₀_le : 1 ≤ bigJ₀ := le_rfl

/-- Ideal law: uniform on the one-form canonical set. -/
noncomputable def bigIdeal (n : ℕ) : PMF (BigSample n) :=
  PMF.uniformOfFinset (modSpec bigPrime n).allForms
    (modSpec_allForms_nonempty bigPrime n)

/-- Actual law: the conditional direct sampler of the large spec. -/
noncomputable def bigActual (n : ℕ) : PMF (BigSample n) :=
  directRetryConditionalPMF (modSpec bigPrime n) (modSpec_hUJ bigPrime n) bigJ₀_le
    (modSpec_coprimeForms_nonempty bigPrime n)

/-- The concrete epoch family with modulus `bigPrime` in the specification. -/
noncomputable def bigEpoch (n : ℕ) : ConcreteEpochData n where
  Coins := BigCoins
  Label := Unit
  FieldId := Unit
  ideal := bigIdeal n
  actual := bigActual n
  solver := fun _ _ => none
  publicCandidates := {none}
  solver_mem_candidates := by
    intro _
    simp
  candidates_complete := by
    intro t ht hsome
    obtain rfl : t = none := by simpa using ht
    simp at hsome
  stageCosts :=
    { s0 := fun _ => 0
      s1 := fun _ => 0
      s2 := fun _ => 0
      s3 := fun _ => 0
      s4 := fun _ => 0
      s5 := fun _ => 0
      s6 := fun _ => 0
      s7 := fun _ => 0
      s8 := fun _ => 0
      s9 := fun _ => 0 }

@[simp] theorem bigEpoch_ideal (n : ℕ) : (bigEpoch n).ideal = bigIdeal n := rfl

@[simp] theorem bigEpoch_actual (n : ℕ) : (bigEpoch n).actual = bigActual n := rfl

/-- Elementary log-power bound: `(log x)^80 ≤ 160^80 * sqrt x` for `x ≥ 1`. -/
theorem log_pow80_le_sqrt_mul {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ 80 ≤ 160 ^ 80 * Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  have hlog : Real.log x ≤ 160 * x ^ (1 / 160 : ℝ) := by
    have h := Real.log_le_rpow_div hx0 (by norm_num : (0 : ℝ) < 1 / 160)
    have heq : x ^ (1 / 160 : ℝ) / (1 / 160 : ℝ) = 160 * x ^ (1 / 160 : ℝ) := by
      ring
    linarith
  have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx
  have hrpow : (x ^ (1 / 160 : ℝ)) ^ 80 = x ^ ((1 / 160 : ℝ) * 80) := by
    rw [← Real.rpow_natCast (x ^ (1 / 160 : ℝ)) 80]
    exact (Real.rpow_mul hx0 (1 / 160) 80).symm
  calc
    (Real.log x) ^ 80 ≤ (160 * x ^ (1 / 160 : ℝ)) ^ 80 :=
      pow_le_pow_left₀ hlog_nn hlog 80
    _ = 160 ^ 80 * (x ^ (1 / 160 : ℝ)) ^ 80 := by rw [mul_pow]
    _ = 160 ^ 80 * x ^ ((1 / 160 : ℝ) * 80) := by rw [hrpow]
    _ = 160 ^ 80 * Real.sqrt x := by
        have h : (1 / 160 : ℝ) * 80 = 1 / 2 := by norm_num
        rw [h, ← Real.sqrt_eq_rpow]

/-- **The small-budget inequality, in parametric form.**  For any prime
`P ≥ bigBound`, the crude missing-root numerator divided by the one-form class
cardinality is at most `1/32`.  Proving this with `P` as a variable keeps the
huge `bigPrime` term from being unfolded by the arithmetic tactics. -/
theorem modSpec_missing_div_le {P : ℕ} (hP : P.Prime) (hPge : bigBound ≤ P)
    (n : ℕ) :
    directMissingRootMass (modSpec P n) / ((modSpec P n).allForms.card : ℝ) ≤ 1 / 32 := by
  have hP2 : 2 ≤ P := hP.two_le
  have hPpos_nat : 0 < P := hP.pos
  have hPpos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hPpos_nat
  have hcard : (modSpec P n).allForms.card = 1 := by
    simp [modSpec, singletonSpecMod]
  have hprimeFactors : P.primeFactors = {P} := by
    have h := Nat.primeFactors_prime_pow (p := P) (k := 1) (by norm_num) hP
    simpa using h
  have hmiss : directMissingRootMass (modSpec P n) =
      8 * (Real.log (2 * (P : ℝ))) ^ 80 / ((P : ℝ) - 1) := by
    unfold directMissingRootMass
    simp only [modSpec, singletonSpecMod]
    rw [hprimeFactors]
    simp [Real.log_one]
    ring
  rw [hmiss, hcard]
  simp only [Nat.cast_one, div_one]
  have hx1 : (1 : ℝ) ≤ 2 * (P : ℝ) := by
    have hP2R : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP2
    nlinarith
  have hlog := log_pow80_le_sqrt_mul hx1
  have hPboundR : (2 * 512 ^ 2 * 160 ^ 160 : ℝ) ≤ (P : ℝ) := by
    have h : (bigBound : ℝ) ≤ (P : ℝ) := by exact_mod_cast hPge
    have hB : (bigBound : ℝ) = 2 * 512 ^ 2 * 160 ^ 160 := by
      unfold bigBound
      push_cast
      ring
    rwa [hB] at h
  have hsqrt : 512 * 160 ^ 80 * Real.sqrt (2 * (P : ℝ)) ≤ (P : ℝ) := by
    have h2P : (0 : ℝ) ≤ 2 * (P : ℝ) := by positivity
    have hsq : (512 * 160 ^ 80 * Real.sqrt (2 * (P : ℝ))) ^ 2 ≤ (P : ℝ) ^ 2 := by
      have hsqrt_sq : (Real.sqrt (2 * (P : ℝ))) ^ 2 = 2 * (P : ℝ) :=
        Real.sq_sqrt h2P
      have h160 : ((160 : ℝ) ^ 80) ^ 2 = (160 : ℝ) ^ 160 := by
        rw [← pow_mul]
      calc
        (512 * 160 ^ 80 * Real.sqrt (2 * (P : ℝ))) ^ 2
            = 512 ^ 2 * (160 ^ 80) ^ 2 * (Real.sqrt (2 * (P : ℝ))) ^ 2 := by ring
        _ = 512 ^ 2 * (160 ^ 80) ^ 2 * (2 * (P : ℝ)) := by rw [hsqrt_sq]
        _ = 512 ^ 2 * 160 ^ 160 * (2 * (P : ℝ)) := by rw [h160]
        _ ≤ (P : ℝ) ^ 2 := by
            have hmul : (2 * 512 ^ 2 * 160 ^ 160) * (P : ℝ) ≤
                (P : ℝ) * (P : ℝ) :=
              mul_le_mul_of_nonneg_right hPboundR (le_of_lt hPpos)
            nlinarith [hmul]
    have hnn : 0 ≤ 512 * 160 ^ 80 * Real.sqrt (2 * (P : ℝ)) := by positivity
    have hPnn : 0 ≤ (P : ℝ) := le_of_lt hPpos
    have h := sq_le_sq.mp hsq
    rwa [abs_of_nonneg hnn, abs_of_nonneg hPnn] at h
  have hsmall : 256 * 160 ^ 80 * Real.sqrt (2 * (P : ℝ)) ≤ (P : ℝ) - 1 := by
    nlinarith [hsqrt, hPpos]
  have hden : 0 < (P : ℝ) - 1 := by nlinarith
  rw [div_le_iff₀ hden]
  nlinarith [hlog, hsmall]

/-- The small-budget inequality at `bigPrime`. -/
theorem big_missing_div_le (n : ℕ) :
    directMissingRootMass (modSpec bigPrime n) / ((modSpec bigPrime n).allForms.card : ℝ) ≤
      1 / 32 :=
  modSpec_missing_div_le bigPrime_prime bigBound_le_bigPrime n

/-- The small-budget inequality in the exact shape required by
`ConcreteC3Hypotheses.heps_le`, with `η = gcdMass = 0`. -/
theorem big_heps_le (n : ℕ) :
    directSamplerEpsilon (modSpec bigPrime n) 0 0 ≤ 1 / 32 := by
  have h := big_missing_div_le n
  simpa [directSamplerEpsilon] using h

/-- **The full `ConcreteC3Hypotheses` instance for the large-modulus toy
epoch.**  All structural fields are explicit; `heps_le` is the genuine
numeric inequality `big_heps_le`, not an assumption. -/
noncomputable def bigConcreteC3 : ConcreteC3Hypotheses bigEpoch where
  spec := fun n => modSpec bigPrime n
  J := bigJ
  J₀ := bigJ₀
  hUJ := fun n => modSpec_hUJ bigPrime n
  hJ₀ := bigJ₀_le
  hcop := fun n => modSpec_coprimeForms_nonempty bigPrime n
  hall := fun n => modSpec_allForms_nonempty bigPrime n
  hNspec := by
    intro n
    simpa using bigPrime_prime.two_le
  hUspec := by
    intro n
    simp
  R := fun _ _ => 1
  hR_ge := by
    intro n A hA
    obtain ⟨hA1, hAU⟩ := Finset.mem_Icc.mp hA
    have hAU' : A ≤ 1 := by simpa using hAU
    have hAeq : A = 1 := by omega
    subst hAeq
    rw [modSpec_roots_one]
    simp
  hR1 := by
    intro _
    rfl
  hRmul := by
    intro _ a b _
    rfl
  hRcop := by
    intro _ m _ _
    have hpos : 0 < 2 ^ m.primeFactors.card := pow_pos (by norm_num) _
    omega
  hRloc := by
    intro n p hp k hk
    rw [modSpec_N] at hp
    rw [bigPrime_primeFactors] at hp
    have hp' : p = bigPrime := by simpa using hp
    rw [hp']
    have hpos : 0 < bigPrime ^ (k / 2) := pow_pos bigPrime_prime.pos _
    omega
  eta := fun _ => 0
  gcdMass := fun _ => 0
  hideal := by
    intro n
    exact le_of_eq (pmfTotalVariation_self (bigIdeal n))
  hgcd := by
    intro n
    have hfilter : ((Finset.Icc 1 (modSpec bigPrime n).U).filter
        (fun A => ¬ Nat.Coprime A (modSpec bigPrime n).N)) = ∅ := by
      rw [modSpec_U, modSpec_N, Finset.filter_eq_empty_iff]
      intro A hA
      obtain ⟨hA1, hA2⟩ := Finset.mem_Icc.mp hA
      have hAeq : A = 1 := by omega
      subst hAeq
      simp
    have hzero : gcdExitProb (modSpec bigPrime n) bigJ = 0 := by
      rw [gcdExitProb_eq_dyadic_noncoprime, hfilter]
      simp
    change (gcdExitProb (modSpec bigPrime n) bigJ).toReal ≤ 0
    rw [hzero]
    simp
  hactual := by
    intro n
    rfl
  heps_le := big_heps_le

/-- The `C3Inputs` obtained from the full `ConcreteC3Hypotheses` instance via
the existing bridge `ConcreteC3Hypotheses.c3Inputs`. -/
noncomputable def bigC3Inputs : C3Inputs (concreteCostFamily bigEpoch) :=
  c3Inputs bigEpoch bigConcreteC3

/-- Sanity check: the `bigC3Inputs` budget is the crude `directSamplerEpsilon`
budget, which `big_heps_le` proves is at most `1/32`. -/
theorem bigC3Inputs_epsilon_le (n : ℕ) : bigC3Inputs.epsilon n ≤ 1 / 32 :=
  bigConcreteC3.heps_le n

/-! ## Section 6: Axiom audit -/

#print axioms Cogentic.RandomizedConcreteTV.singletonSpec
#print axioms Cogentic.RandomizedConcreteTV.toySpec_coprimeForms_eq
#print axioms Cogentic.RandomizedConcreteTV.toyActual_eq_uniform
#print axioms Cogentic.RandomizedConcreteTV.toyActual_eq_ideal
#print axioms Cogentic.RandomizedConcreteTV.toy_tv_eq_zero
#print axioms Cogentic.RandomizedConcreteTV.toyStructural
#print axioms Cogentic.RandomizedConcreteTV.structural_tv_le_directSamplerEpsilon
#print axioms Cogentic.RandomizedConcreteTV.c3Inputs_of_structural
#print axioms Cogentic.RandomizedConcreteTV.toyC3Inputs
#print axioms Cogentic.RandomizedConcreteTV.toyC3Inputs_epsilon_eq_tv
#print axioms Cogentic.RandomizedConcreteTV.bigPrime_prime
#print axioms Cogentic.RandomizedConcreteTV.bigBound_le_bigPrime
#print axioms Cogentic.RandomizedConcreteTV.log_pow80_le_sqrt_mul
#print axioms Cogentic.RandomizedConcreteTV.modSpec_missing_div_le
#print axioms Cogentic.RandomizedConcreteTV.big_missing_div_le
#print axioms Cogentic.RandomizedConcreteTV.big_heps_le
#print axioms Cogentic.RandomizedConcreteTV.bigConcreteC3
#print axioms Cogentic.RandomizedConcreteTV.bigC3Inputs
#print axioms Cogentic.RandomizedConcreteTV.bigC3Inputs_epsilon_le

end Cogentic.RandomizedConcreteTV
