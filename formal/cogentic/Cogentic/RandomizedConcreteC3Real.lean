import Cogentic.RandomizedConcreteEpochCost
import Cogentic.RandomizedConcreteFormSpec
import Cogentic.RandomizedEpochTV

/-!
# The real reduced-class C3 instantiation

`Cogentic.RandomizedConcreteTV.bigConcreteC3` instantiates the C3 total-variation
slot of `Cogentic.RandomizedConcreteEpochCost` with a one-form specification at a
large prime modulus.  This file replaces that toy specification by the *actual*
canonical primitive reduced forms of discriminant `-8 * N`, i.e. by
`Cogentic.RandomizedConcreteFormSpec.concreteFormSpec N hN` over
`Cogentic.RandomizedFormGroup.ReducedForms N`.

## The sample space

`ConcreteEpochData N` fixes its sample space to be
`Coins × (Label → (ZMod N)ˣ)`.  We take `Coins` to be the finite type of reduced
forms `↥(ReducedForms N)` and `Label` to be `Empty`, so that the hidden-label
factor is a singleton and the sample space is equivalent to the class group.
The direct sampler specification `realSpec N hN` is built directly on this
sample space, with `allForms = univ`, `roots = concreteRoots N`, `N = N` and
`U = leadingBound N`.  The form constructor is the concrete inverse
`concreteBuildForm` restricted to the reduced forms.

## What is proved and what is a hypothesis

Every *structural* field of the direct-sampler TV estimate is proved from
`concreteFormSpec`:

* `J`, `J₀`, `hUJ`, `hJ₀`;
* `hcop`, `hall`, `hNspec`, `hUspec`;
* the root-count majorant `realR` together with `hR_ge`, `hR1`, `hRmul`,
  `hRcop`, `hRloc`.

The six *analytic* inputs stay explicit fields of the local structure
`ConcreteC3RealInputs`:

* `eta` and `hideal` (distance of the ideal law to uniform on the class group);
* `gcdMass` and `hgcd` (one-attempt gcd-exit budget);
* `hactual` (exact identification of the epoch's actual law with the direct
  sampler);
* `heps_le`, the small-budget inequality
  `directSamplerEpsilon (realSpec N hN) eta gcdMass ≤ 1/32`.

The small-budget inequality is the real class-number TV budget.  It is *not*
proved here: it is the exact remaining numeric inequality, and
`ConcreteC3RealInputs.heps_le_explicit` / `heps_le_unfolded_iff` restate it in
fully unfolded form.  `ConcreteC3RealInputs.tv_le` is the reduction from the six
analytic fields to the concrete TV bound, and `c3Inputs` assembles the `C3Inputs`
record for the concrete epoch family.

The constructor `realBuildForm` is the concrete `concreteBuildForm` restricted to
`ReducedForms N` (`realBuildForm_map_val`), and `realSpec_eq_concreteFormSpec_data`
records that `realSpec` carries exactly the modulus, leading bound and root set
of `concreteFormSpec N hN`.

There is no `sorry`, `admit`, `axiom`, `native_decide`, or `Classical.choose`.
-/

noncomputable section

namespace Cogentic.RandomizedConcreteC3Real

set_option linter.style.haveILetI false

open Finset
open Cogentic.RandomizedConcreteFormSpec
open Cogentic.RandomizedConcreteEpoch
open Cogentic.RandomizedConcreteEpochCost
open Cogentic.RandomizedDirectClassSampler
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedEpochAssembly
open Cogentic.RandomizedEpochTV
open Cogentic.RandomizedFiniteSupportTV
open Cogentic.RandomizedFormGroup
open Cogentic.RandomizedHiddenOutputLaw
open scoped BigOperators ENNReal

/-! ## Section 1: The real sample space -/

/-- The finite type of canonical primitive reduced forms of discriminant
`-8 * N`.  This is the public coin type of the concrete epoch. -/
abbrev RealCoins (N : ℕ) : Type := ↥(ReducedForms N)

/-- The sample space of the real epoch: a reduced form together with the
(singleton) hidden-label data. -/
abbrev RealSample (N : ℕ) : Type := RealCoins N × (Empty → (ZMod N)ˣ)

/-- The canonical (empty) hidden-label function. -/
def realCanon (N : ℕ) : Empty → (ZMod N)ˣ := fun e => e.elim

/-- Embed a reduced form into the full sample space. -/
def realSampleOfCoin {N : ℕ} (g : RealCoins N) : RealSample N := (g, realCanon N)

@[simp] theorem realSampleOfCoin_fst {N : ℕ} (x : RealSample N) :
    realSampleOfCoin x.1 = x := by
  obtain ⟨g, u⟩ := x
  have hu : u = realCanon N := by
    funext e
    exact e.elim
  simp [realSampleOfCoin, hu]

@[simp] theorem realSampleOfCoin_fst_fst {N : ℕ} (g : RealCoins N) :
    (realSampleOfCoin g).1 = g := rfl

/-- The hidden-label component is a subsingleton, so the sample space is
equivalent to the type of reduced forms. -/
def realSampleEquiv (N : ℕ) : RealSample N ≃ RealCoins N where
  toFun x := x.1
  invFun g := realSampleOfCoin g
  left_inv x := realSampleOfCoin_fst x
  right_inv _g := rfl

/-! ## Section 2: The concrete form constructor on the reduced-form subtype -/

/-- The concrete constructor of `RandomizedConcreteFormSpec`, restricted to the
subtype of reduced forms.  It returns `some f` exactly when `(A, b)` determines
the canonical reduced form `f`. -/
def realBuildForm (N : ℕ) (A : ℕ) (b : ℤ) : Option (RealCoins N) :=
  match concreteBuildForm N A b with
  | none => none
  | some f => if hf : f ∈ ReducedForms N then some ⟨f, hf⟩ else none

/-- Exact characterization of the restricted constructor. -/
theorem realBuildForm_eq_some_iff (N A : ℕ) (b : ℤ) (g : RealCoins N) :
    realBuildForm N A b = some g ↔ g.1.1 = A ∧ g.1.2.1 = b := by
  constructor
  · intro h
    unfold realBuildForm at h
    split at h
    · exact absurd h (by simp)
    · rename_i f hf
      split at h
      · rename_i hfmem
        injection h with hg
        subst hg
        have hf' := (concreteBuildForm_eq_some_iff.mp hf).2
        exact ⟨hf'.1, hf'.2⟩
      · exact absurd h (by simp)
  · rintro ⟨h1, h2⟩
    unfold realBuildForm
    rw [concreteBuildForm_eq_some_iff.mpr ⟨g.2, h1, h2⟩]
    simp

/-- The restricted constructor is exactly the concrete constructor
`concreteBuildForm` followed by the subtype embedding. -/
theorem realBuildForm_map_val (N A : ℕ) (b : ℤ) :
    (realBuildForm N A b).map Subtype.val = concreteBuildForm N A b := by
  unfold realBuildForm
  split
  · rename_i heq
    rw [heq]
    rfl
  · rename_i f hf
    have hfmem : f ∈ ReducedForms N := (concreteBuildForm_eq_some_iff.mp hf).1
    simp [hf, hfmem]

/-- The canonical root set of the concrete specification is exactly the
`rootCount` set; in particular their cardinalities agree. -/
theorem concreteRoots_card_eq_rootCount {N A : ℕ} (hA : A ≠ 0) :
    (concreteRoots N A).card = rootCount N A := by
  haveI : NeZero A := ⟨hA⟩
  rw [concreteRoots, dif_neg hA,
    Finset.card_image_of_injective _ ZMod.injective_valMinAbs]
  exact (rootCount_eq_card N A).symm

/-! ## Section 3: The root-count majorant for the real specification -/

/-- Per-prime component of the root-count majorant.  For a prime `p` dividing
the modulus, the local root count is at most `2 * p ^ (k / 2)`; for a prime not
dividing the modulus it is at most `2`. -/
def realTerm (N p k : ℕ) : ℕ :=
  if p ∣ N then 2 * p ^ (k / 2) else 2

/-- A multiplicative majorant for `concreteRoots N A` on the whole range
`1 ≤ A ≤ leadingBound N`, including the non-coprime leading coefficients. -/
def realR (N : ℕ) : ℕ → ℕ :=
  fun A => ∏ p ∈ A.primeFactors, realTerm N p (A.factorization p)

@[simp] theorem realR_one (N : ℕ) : realR N 1 = 1 := by
  simp [realR, Nat.primeFactors_one]

theorem realR_mul_coprime (N a b : ℕ) (hab : Nat.Coprime a b) :
    realR N (a * b) = realR N a * realR N b := by
  unfold realR
  rw [hab.primeFactors_mul, Finset.prod_union hab.disjoint_primeFactors]
  have hleft : ∀ p ∈ a.primeFactors,
      realTerm N p ((a * b).factorization p) = realTerm N p (a.factorization p) := by
    intro p hp
    have hnot : p ∉ b.primeFactors :=
      Finset.disjoint_left.mp hab.disjoint_primeFactors hp
    have hbzero : b.factorization p = 0 := by
      by_contra hne
      exact hnot (by simpa [Nat.support_factorization] using Finsupp.mem_support_iff.mpr hne)
    rw [Nat.factorization_mul_apply_of_coprime hab, hbzero, add_zero]
  have hright : ∀ p ∈ b.primeFactors,
      realTerm N p ((a * b).factorization p) = realTerm N p (b.factorization p) := by
    intro p hp
    have hnot : p ∉ a.primeFactors :=
      Finset.disjoint_right.mp hab.disjoint_primeFactors hp
    have hazero : a.factorization p = 0 := by
      by_contra hne
      exact hnot (by simpa [Nat.support_factorization] using Finsupp.mem_support_iff.mpr hne)
    rw [Nat.factorization_mul_apply_of_coprime hab, hazero, zero_add]
  rw [Finset.prod_congr rfl hleft, Finset.prod_congr rfl hright]

theorem realR_coprime_le (N m : ℕ) (_hm : 1 ≤ m) (hcop : Nat.Coprime m N) :
    realR N m ≤ 2 * 2 ^ m.primeFactors.card := by
  have hterm : ∀ p ∈ m.primeFactors, realTerm N p (m.factorization p) = 2 := by
    intro p hp
    have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hp
    have hnot : ¬ p ∣ N := by
      intro hpN
      have hg : p ∣ Nat.gcd m N := Nat.dvd_gcd hpm hpN
      rw [hcop.gcd_eq_one] at hg
      exact (Nat.prime_of_mem_primeFactors hp).ne_one (Nat.dvd_one.mp hg)
    simp [realTerm, hnot]
  unfold realR
  rw [Finset.prod_congr rfl hterm, Finset.prod_const]
  have hpos : 0 < 2 ^ m.primeFactors.card := pow_pos (by norm_num) _
  omega

theorem realR_prime_pow_le (N p : ℕ) (hp : p ∈ N.primeFactors) (k : ℕ) (hk : 1 ≤ k) :
    realR N (p ^ k) ≤ 2 * p ^ (k / 2) := by
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ N := Nat.dvd_of_mem_primeFactors hp
  have hk0 : k ≠ 0 := by omega
  unfold realR
  rw [Nat.primeFactors_prime_pow hk0 hp_prime, Finset.prod_singleton,
    Nat.factorization_pow_self hp_prime]
  simp [realTerm, hpdvd]

/-- The majorant dominates the concrete root count at every admissible leading
coefficient, with no coprimality restriction. -/
theorem concreteRoots_card_le_realR {N : ℕ} (hN : Odd N) (A : ℕ) (hA : 1 ≤ A) :
    (concreteRoots N A).card ≤ realR N A := by
  have hA0 : A ≠ 0 := by omega
  have hN0 : N ≠ 0 := by
    rcases hN with ⟨k, hk⟩
    omega
  rw [concreteRoots_card_eq_rootCount hA0, rootCount_eq_prod_primeFactors hA0]
  unfold realR
  refine Finset.prod_le_prod' ?_
  intro p hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  by_cases hpdvd : p ∣ N
  · have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨t, ht⟩ := hpdvd
      rcases hN with ⟨k, hk⟩
      omega
    have hle := rootCount_prime_pow_le_two_mul_half hp_prime hp2 hN0
      (k := A.factorization p)
    simpa [realTerm, hpdvd] using hle
  · by_cases hp2 : p = 2
    · subst hp2
      have hle1 := rootCount_two_pow_le_one hN (A.factorization 2)
      simp [realTerm, hpdvd]
      omega
    · have hle2 := rootCount_prime_pow_le_two hp_prime hp2 hpdvd (A.factorization p)
      simpa [realTerm, hpdvd] using hle2

/-! ## Section 4: The real `DirectFormSpec` on the sample space -/

/-- Exact characterization of the restricted constructor after embedding into
the full sample space. -/
theorem realBuildForm_map_eq_some_iff (N A : ℕ) (b : ℤ) (x : RealSample N) :
    (realBuildForm N A b).map realSampleOfCoin = some x ↔
      x.1.1.1 = A ∧ x.1.1.2.1 = b := by
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [realBuildForm_eq_some_iff] at hg
    simpa using hg
  · rintro ⟨h1, h2⟩
    refine ⟨x.1, ?_, realSampleOfCoin_fst x⟩
    rw [realBuildForm_eq_some_iff]
    exact ⟨h1, h2⟩

/-- The concrete `DirectFormSpec` on `RealSample N`.  Its canonical forms are all
of `ReducedForms N` (the hidden-label factor is a singleton), its root set is
`concreteRoots N`, and its constructor is the restricted concrete constructor. -/
def realSpec (N : ℕ) (hN : Odd N) : DirectFormSpec (RealSample N) where
  N := N
  U := leadingBound N
  roots := concreteRoots N
  roots_card_le := by
    intro A hA1 hAU hcop
    exact concreteRoots_card_le hN A hA1 hAU hcop
  buildForm := fun A b => (realBuildForm N A b).map realSampleOfCoin
  allForms := Finset.univ
  leadCoeff := fun x => x.1.1.1
  midCoeff := fun x => x.1.1.2.1
  leadCoeff_pos := by
    intro x _
    exact (mem_reducedForms.mp x.1.2).2.1
  leadCoeff_le := by
    intro x _
    exact leading_le_sqrt (mem_reducedForms.mp x.1.2)
  midCoeff_mem_roots := by
    intro x _
    exact concreteRoots_mem_of_isReduced (mem_reducedForms.mp x.1.2)
  coeff_injective := by
    intro x _ y _ hxy
    have hsub_val : x.1.1 = y.1.1 :=
      concreteCoeff_injOn N x.1.2 y.1.2 hxy
    have hsub : x.1 = y.1 := Subtype.ext hsub_val
    obtain ⟨gx, ux⟩ := x
    obtain ⟨gy, uy⟩ := y
    simp only at hsub
    subst hsub
    have huxy : ux = uy := Subsingleton.elim _ _
    subst huxy
    rfl
  buildForm_eq_some_iff := by
    intro A b x _hA1 _hAU _hcop _hb
    refine (realBuildForm_map_eq_some_iff N A b x).trans ?_
    simp

@[simp] theorem realSpec_N (N : ℕ) (hN : Odd N) : (realSpec N hN).N = N := rfl

@[simp] theorem realSpec_U (N : ℕ) (hN : Odd N) :
    (realSpec N hN).U = leadingBound N := rfl

@[simp] theorem realSpec_roots (N : ℕ) (hN : Odd N) (A : ℕ) :
    (realSpec N hN).roots A = concreteRoots N A := rfl

@[simp] theorem realSpec_allForms (N : ℕ) (hN : Odd N) :
    (realSpec N hN).allForms = Finset.univ := rfl

/-- The real class-set cardinality is exactly the cardinality of
`ReducedForms N`. -/
theorem realSpec_allForms_card (N : ℕ) (hN : Odd N) :
    (realSpec N hN).allForms.card = (ReducedForms N).card := by
  rw [realSpec_allForms, Finset.card_univ, Fintype.card_prod, Fintype.card_coe]
  simp

/-- The real specification carries exactly the data of the concrete form
specification `concreteFormSpec N hN`: same modulus, same leading bound, same
root set.  Its canonical-form set is `ReducedForms N` transported to the sample
space (the hidden-label factor is a singleton). -/
theorem realSpec_eq_concreteFormSpec_data (N : ℕ) (hN : Odd N) :
    (realSpec N hN).N = (concreteFormSpec N hN).N ∧
      (realSpec N hN).U = (concreteFormSpec N hN).U ∧
      (realSpec N hN).roots = (concreteFormSpec N hN).roots :=
  ⟨rfl, rfl, rfl⟩

@[simp] theorem realSpec_leadCoeff (N : ℕ) (hN : Odd N) (x : RealSample N) :
    (realSpec N hN).leadCoeff x = x.1.1.1 := rfl

@[simp] theorem realSpec_midCoeff (N : ℕ) (hN : Odd N) (x : RealSample N) :
    (realSpec N hN).midCoeff x = x.1.1.2.1 := rfl

/-- The dyadic proposal depth of the real sampler: the leading-coefficient
bound itself. -/
def realJ (N : ℕ) : ℕ := leadingBound N

/-- The retry count of the real sampler. -/
def realJ₀ : ℕ := 1

theorem realSpec_hUJ (N : ℕ) (hN : Odd N) :
    (realSpec N hN).U ≤ 2 ^ realJ N := by
  simp only [realSpec_U, realJ]
  exact (Nat.lt_two_pow_self (n := leadingBound N)).le

theorem realJ₀_le : 1 ≤ realJ₀ := le_rfl

/-- The principal reduced form is a canonical form, so the class set is
nonempty. -/
theorem realSpec_allForms_nonempty (N : ℕ) (hN : Odd N) (_h2 : 2 ≤ N) :
    (realSpec N hN).allForms.Nonempty := by
  have hNpos : 0 < N := by
    rcases hN with ⟨k, hk⟩
    omega
  exact ⟨realSampleOfCoin ⟨(1, (0 : ℤ), 2 * N), principal_mem_reducedForms hNpos⟩,
    Finset.mem_univ _⟩

/-- The principal form has coprime leading coefficient `1`, so the accepted
coprime-form set is nonempty. -/
theorem realSpec_coprimeForms_nonempty (N : ℕ) (hN : Odd N) (h2 : 2 ≤ N) :
    (realSpec N hN).coprimeForms.Nonempty := by
  have hNpos : 0 < N := by
    rcases hN with ⟨k, hk⟩
    omega
  refine ⟨realSampleOfCoin ⟨(1, (0 : ℤ), 2 * N), principal_mem_reducedForms hNpos⟩,
    ?_⟩
  rw [DirectFormSpec.coprimeForms]
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  simp [realSpec, realSampleOfCoin]

theorem realSpec_hNspec (N : ℕ) (hN : Odd N) (h2 : 2 ≤ N) :
    2 ≤ (realSpec N hN).N := by
  simpa using h2

theorem realSpec_hUspec (N : ℕ) (hN : Odd N) (h2 : 2 ≤ N) :
    1 ≤ (realSpec N hN).U := by
  simp only [realSpec_U, leadingBound]
  apply Nat.le_sqrt.mpr
  have h : 3 ≤ 8 * N / 3 := by
    rw [Nat.le_div_iff_mul_le (by decide)]
    omega
  omega

/-! ## Section 5: The concrete real epoch -/

/-- The zero stage-cost record used by the real structural epoch.  The costs are
irrelevant to the C3 total-variation slot and are left at zero here. -/
def realStageCosts (N : ℕ) : StageCosts N (RealCoins N) Empty where
  s0 := fun _ => 0
  s1 := fun _ => 0
  s2 := fun _ => 0
  s3 := fun _ => 0
  s4 := fun _ => 0
  s5 := fun _ => 0
  s6 := fun _ => 0
  s7 := fun _ => 0
  s8 := fun _ => 0
  s9 := fun _ => 0

/-- The concrete epoch at modulus `N`: public coins are reduced forms, the hidden
label set is empty (a singleton function type), the solver always rejects, and
the ideal/actual laws are the uniform law and the restricted direct sampler. -/
def realEpoch (N : ℕ) (hN : Odd N) (h2 : 2 ≤ N) : ConcreteEpochData N where
  Coins := RealCoins N
  Label := Empty
  FieldId := Unit
  ideal := PMF.uniformOfFinset (realSpec N hN).allForms
    (realSpec_allForms_nonempty N hN h2)
  actual := directRetryConditionalPMF (realSpec N hN) (J := realJ N) (J₀ := realJ₀)
    (realSpec_hUJ N hN) realJ₀_le (realSpec_coprimeForms_nonempty N hN h2)
  solver := fun _ _ => none
  publicCandidates := {none}
  solver_mem_candidates := by
    intro _
    simp
  candidates_complete := by
    intro t ht hsome
    obtain rfl : t = none := by simpa using ht
    simp at hsome
  stageCosts := realStageCosts N

@[simp] theorem realEpoch_ideal (N : ℕ) (hN : Odd N) (h2 : 2 ≤ N) :
    (realEpoch N hN h2).ideal =
      PMF.uniformOfFinset (realSpec N hN).allForms
        (realSpec_allForms_nonempty N hN h2) := rfl

@[simp] theorem realEpoch_actual (N : ℕ) (hN : Odd N) (h2 : 2 ≤ N) :
    (realEpoch N hN h2).actual =
      directRetryConditionalPMF (realSpec N hN) (J := realJ N) (J₀ := realJ₀)
        (realSpec_hUJ N hN) realJ₀_le (realSpec_coprimeForms_nonempty N hN h2) := rfl

/-- A trivial epoch with `ideal = actual`, used for even moduli where the real
odd-modulus construction does not apply. -/
def trivialEpoch (N : ℕ) : ConcreteEpochData N where
  Coins := Unit
  Label := Empty
  FieldId := Unit
  ideal := PMF.pure ((), realCanon N)
  actual := PMF.pure ((), realCanon N)
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

@[simp] theorem trivialEpoch_ideal (N : ℕ) :
    (trivialEpoch N).ideal = PMF.pure ((), realCanon N) := rfl

@[simp] theorem trivialEpoch_actual (N : ℕ) :
    (trivialEpoch N).actual = PMF.pure ((), realCanon N) := rfl

/-- The concrete epoch family used for C3: the real reduced-class epoch at odd
moduli and the trivial `ideal = actual` epoch at even moduli. -/
def realFamily (n : ℕ) (hN : 3 ≤ n) : ConcreteEpochData n :=
  if ho : Odd n then realEpoch n ho (by omega) else trivialEpoch n

theorem realFamily_odd {n : ℕ} (hN : 3 ≤ n) (ho : Odd n) :
    realFamily n hN = realEpoch n ho (by omega) := by
  simp only [realFamily, dif_pos ho]

theorem realFamily_even {n : ℕ} (hN : 3 ≤ n) (ho : ¬ Odd n) :
    realFamily n hN = trivialEpoch n := by
  simp only [realFamily, dif_neg ho]

/-! ## Section 6: The explicit analytic C3 inputs at one modulus -/

/-- The six analytic inputs of the real C3 slot at a fixed odd modulus `N`.

Every structural field of the direct-sampler estimate is supplied by
`realSpec`/`realR`; only these six fields are hypotheses:

* `eta`, `hideal`: distance of the ideal law to uniform on `ReducedForms N`;
* `gcdMass`, `hgcd`: one-attempt gcd-exit budget;
* `hactual`: exact identification of the epoch law with the direct sampler;
* `heps_le`: the small-budget inequality, i.e. the real class-number TV budget.

`heps_le_explicit` and `heps_le_unfolded_iff` state `heps_le` in fully unfolded
forms. -/
structure ConcreteC3RealInputs (N : ℕ) (hN : Odd N) (h2 : 2 ≤ N) where
  /-- L6-L10: distance of the ideal law to uniform on the class group. -/
  eta : ℝ
  /-- L6-L10: one-attempt gcd-exit budget. -/
  gcdMass : ℝ
  /-- L6-L10: the ideal law is within `eta` of uniform on the canonical forms. -/
  hideal : pmfTotalVariation (realEpoch N hN h2).ideal
    (PMF.uniformOfFinset (realSpec N hN).allForms
      (realSpec_allForms_nonempty N hN h2)) ≤ eta
  /-- L6-L10: the gcd-exit probability is bounded by `gcdMass`. -/
  hgcd : (gcdExitProb (realSpec N hN) (realJ N)).toReal ≤ gcdMass
  /-- Exact-law hypothesis: the real epoch's actual law is exactly the
  conditional direct-sampler law. -/
  hactual : (realEpoch N hN h2).actual =
    directRetryConditionalPMF (realSpec N hN) (J := realJ N) (J₀ := realJ₀)
      (realSpec_hUJ N hN) realJ₀_le (realSpec_coprimeForms_nonempty N hN h2)
  /-- L6-L10: the explicit TV budget is at most `1/32`. -/
  heps_le : directSamplerEpsilon (realSpec N hN) eta gcdMass ≤ 1 / 32

namespace ConcreteC3RealInputs

variable {N : ℕ} {hN : Odd N} {h2 : 2 ≤ N}

/-- The real C3 budget is nonnegative.  The missing-root mass is nonnegative,
the form set is nonempty, and `eta`, `gcdMass` are nonnegative by the explicit
hypotheses. -/
theorem epsilon_nonneg (H : ConcreteC3RealInputs N hN h2) :
    0 ≤ directSamplerEpsilon (realSpec N hN) H.eta H.gcdMass := by
  have hmiss : 0 ≤ directMissingRootMass (realSpec N hN) :=
    directMissingRootMass_nonneg (realSpec N hN) (realSpec_hNspec N hN h2)
      (realSpec_hUspec N hN h2)
  have hcardNat : 0 < (realSpec N hN).allForms.card :=
    (realSpec_allForms_nonempty N hN h2).card_pos
  have hcard : (0 : ℝ) < ((realSpec N hN).allForms.card : ℝ) := by
    exact_mod_cast hcardNat
  have hgcd_nonneg : 0 ≤ H.gcdMass := ENNReal.toReal_nonneg.trans H.hgcd
  have heta : 0 ≤ H.eta :=
    (ConcreteC3Hypotheses.pmfTotalVariation_nonneg (realEpoch N hN h2).ideal _).trans
      H.hideal
  unfold directSamplerEpsilon
  exact add_nonneg (add_nonneg (div_nonneg hmiss hcard.le) hgcd_nonneg) heta

/-- **The real C3 TV estimate.**  The structural fields are all proved from
`concreteFormSpec`; the only inputs are the six analytic fields. -/
theorem tv_le (H : ConcreteC3RealInputs N hN h2) :
    pmfTotalVariation (realEpoch N hN h2).ideal (realEpoch N hN h2).actual ≤
      directSamplerEpsilon (realSpec N hN) H.eta H.gcdMass := by
  rw [H.hactual]
  exact pmfTotalVariation_le_directSamplerEpsilon (realSpec N hN)
    (J := realJ N) (J₀ := realJ₀) (realSpec_hUJ N hN) realJ₀_le
    (realSpec_coprimeForms_nonempty N hN h2)
    (realSpec_allForms_nonempty N hN h2)
    (realSpec_hNspec N hN h2) (realSpec_hUspec N hN h2)
    (realR N)
    (by
      intro A hA
      have hA1 : 1 ≤ A := (Finset.mem_Icc.mp hA).1
      simpa using concreteRoots_card_le_realR hN A hA1)
    (realR_one N)
    (fun a b hab => realR_mul_coprime N a b hab)
    (fun m hm hc => realR_coprime_le N m hm hc)
    (fun p hp k hk => realR_prime_pow_le N p hp k hk)
    H.hideal H.hgcd

/-- The small-budget inequality in the exact unfolded shape
`missing-root + gcd-exit + eta ≤ 1/32`. -/
theorem heps_le_explicit (eta gcdMass : ℝ) :
    (directSamplerEpsilon (realSpec N hN) eta gcdMass ≤ 1 / 32) ↔
      directMissingRootMass (realSpec N hN) /
          ((realSpec N hN).allForms.card : ℝ) + gcdMass + eta ≤ 1 / 32 := by
  rfl

/-- The missing-root numerator of the real specification, written out with
`U = leadingBound N` and `N` itself. -/
theorem directMissingRootMass_realSpec (N : ℕ) (hN : Odd N) :
    directMissingRootMass (realSpec N hN) =
      2 * (leadingBound N : ℝ) * (1 + Real.log (leadingBound N : ℝ)) *
        (∑ p ∈ N.primeFactors, 4 / ((p : ℝ) - 1)) *
        (Real.log (2 * (N : ℝ))) ^ (80 : ℕ) := rfl

/-- **The exact remaining numeric inequality.**  The small-budget condition,
fully unfolded in terms of `leadingBound N`, the prime factors of `N`, the
class-set cardinality `(ReducedForms N).card`, and the explicit `eta`/`gcdMass`
budgets. -/
theorem heps_le_unfolded_iff (N : ℕ) (hN : Odd N) (eta gcdMass : ℝ) :
    (directSamplerEpsilon (realSpec N hN) eta gcdMass ≤ 1 / 32) ↔
      (2 * (leadingBound N : ℝ) * (1 + Real.log (leadingBound N : ℝ)) *
          (∑ p ∈ N.primeFactors, 4 / ((p : ℝ) - 1)) *
          (Real.log (2 * (N : ℝ))) ^ (80 : ℕ)) /
          ((ReducedForms N).card : ℝ) + gcdMass + eta ≤ 1 / 32 := by
  rw [heps_le_explicit, directMissingRootMass_realSpec, realSpec_allForms_card]

end ConcreteC3RealInputs

/-- **Epoch-level hit-probability bridge for the real epoch.**  The six real C3
inputs, the already-proved C1/C2 predicates, and the ideal good-mass lower bound
`γ` give the verified-split lower bound `γ / 2 - directSamplerEpsilon`. -/
theorem hit_prob_ge (H : ConcreteC3RealInputs N hN h2) (hN3 : 3 ≤ N)
    (hnot : ¬ IsPrimePow N)
    (hcheck : (realEpoch N hN h2).toHardEpochData.CongruenceCheck)
    (huniform : (realEpoch N hN h2).toHardEpochData.HiddenUniform)
    {γ : ℝ} (hγ₀ : 0 ≤ γ)
    (hγ : γ ≤ ((realEpoch N hN h2).toHardEpochData.ideal.toOuterMeasure
      {x | observe (realEpoch N hN h2).toHardEpochData.trace x ∈
        (realEpoch N hN h2).toHardEpochData.good}).toReal) :
    γ / 2 - directSamplerEpsilon (realSpec N hN) H.eta H.gcdMass ≤
      (((realEpoch N hN h2).toHardEpochData.actual.map
        ((realEpoch N hN h2).toHardEpochData.assembledAttempt hN3)).toOuterMeasure
        {o | o.1 ≠ none}).toReal :=
  (realEpoch N hN h2).toHardEpochData.assembledAttempt_hit_prob_ge hN3 hN hnot
    hcheck huniform hγ₀ hγ (ConcreteC3RealInputs.tv_le H)

/-! ## Section 7: The C3 input record for the concrete real epoch family -/

/-- The packaged hard-epoch family of the concrete real epochs. -/
def realHardFamily (n : ℕ) (hN : 3 ≤ n) : HardEpochData n :=
  (realFamily n hN).toHardEpochData

/-- **The real C3 inputs.**  For every odd `n ≥ 3` the caller supplies the six
analytic fields; at even `n` the epoch has `ideal = actual`, so the budget is
`0`.  This is the reduction from the explicit real inputs to `C3Inputs`. -/
def c3Inputs
    (H : ∀ (n : ℕ) (hN : 3 ≤ n) (ho : Odd n),
      ConcreteC3RealInputs n ho (by omega)) :
    C3Inputs realHardFamily where
  epsilon := fun n =>
    if h : 3 ≤ n ∧ Odd n then
      let I : ConcreteC3RealInputs n h.2 (by omega) := H n h.1 h.2
      directSamplerEpsilon (realSpec n h.2) I.eta I.gcdMass
    else 0
  epsilon_nonneg := by
    intro n
    by_cases h : 3 ≤ n ∧ Odd n
    · rw [dif_pos h]
      dsimp only
      exact ConcreteC3RealInputs.epsilon_nonneg (H n h.1 h.2)
    · rw [dif_neg h]
  epsilon_le := by
    intro n
    by_cases h : 3 ≤ n ∧ Odd n
    · rw [dif_pos h]
      dsimp only
      exact (H n h.1 h.2).heps_le
    · rw [dif_neg h]
      norm_num
  tv_le := by
    intro n hN hhard
    by_cases ho : Odd n
    · have hmem : 3 ≤ n ∧ Odd n := ⟨hN, ho⟩
      have hfam : realFamily n hN = realEpoch n ho (by omega) := realFamily_odd hN ho
      rw [dif_pos hmem]
      dsimp only
      change pmfTotalVariation (realHardFamily n hN).ideal
        (realHardFamily n hN).actual ≤
        directSamplerEpsilon (realSpec n ho)
          (H n hN ho).eta (H n hN ho).gcdMass
      dsimp only [realHardFamily]
      rw [hfam]
      exact ConcreteC3RealInputs.tv_le (H n hN ho)
    · have hmem : ¬ (3 ≤ n ∧ Odd n) := fun h => ho h.2
      have hfam : realFamily n hN = trivialEpoch n := realFamily_even hN ho
      rw [dif_neg hmem]
      change pmfTotalVariation (realHardFamily n hN).ideal
        (realHardFamily n hN).actual ≤ 0
      dsimp only [realHardFamily]
      rw [hfam]
      change pmfTotalVariation (trivialEpoch n).ideal (trivialEpoch n).actual ≤ 0
      rw [show (trivialEpoch n).ideal = (trivialEpoch n).actual from rfl,
        pmfTotalVariation_self]

/-- The real C3 inputs at budget `ε = directSamplerEpsilon ...` really are the
explicit per-`n` direct-sampler budget at odd `n ≥ 3`. -/
theorem c3Inputs_epsilon_odd (H : ∀ (n : ℕ) (hN : 3 ≤ n) (ho : Odd n),
      ConcreteC3RealInputs n ho (by omega))
    {n : ℕ} (hN : 3 ≤ n) (ho : Odd n) :
    (c3Inputs H).epsilon n =
      directSamplerEpsilon (realSpec n ho)
        (H n hN ho).eta (H n hN ho).gcdMass := by
  simp only [c3Inputs]
  exact dif_pos (show 3 ≤ n ∧ Odd n from ⟨hN, ho⟩)

/-- At an odd index, the assembled `C3Inputs` bound is exactly the real
direct-sampler TV bound. -/
theorem c3Inputs_tv_le_odd (H : ∀ (n : ℕ) (hN : 3 ≤ n) (ho : Odd n),
      ConcreteC3RealInputs n ho (by omega))
    {n : ℕ} (hN : 3 ≤ n) (ho : Odd n) :
    pmfTotalVariation (realHardFamily n hN).ideal (realHardFamily n hN).actual ≤
      (c3Inputs H).epsilon n := by
  rw [c3Inputs_epsilon_odd H hN ho]
  dsimp only [realHardFamily]
  rw [realFamily_odd hN ho]
  exact ConcreteC3RealInputs.tv_le (H n hN ho)

/-! ## Section 8: Axiom audit -/

#print axioms Cogentic.RandomizedConcreteC3Real.realBuildForm_eq_some_iff
#print axioms Cogentic.RandomizedConcreteC3Real.realBuildForm_map_val
#print axioms Cogentic.RandomizedConcreteC3Real.concreteRoots_card_eq_rootCount
#print axioms Cogentic.RandomizedConcreteC3Real.realR_mul_coprime
#print axioms Cogentic.RandomizedConcreteC3Real.realR_coprime_le
#print axioms Cogentic.RandomizedConcreteC3Real.realR_prime_pow_le
#print axioms Cogentic.RandomizedConcreteC3Real.concreteRoots_card_le_realR
#print axioms Cogentic.RandomizedConcreteC3Real.realSpec
#print axioms Cogentic.RandomizedConcreteC3Real.realSpec_allForms_card
#print axioms Cogentic.RandomizedConcreteC3Real.realSpec_coprimeForms_nonempty
#print axioms Cogentic.RandomizedConcreteC3Real.realEpoch
#print axioms Cogentic.RandomizedConcreteC3Real.ConcreteC3RealInputs.epsilon_nonneg
#print axioms Cogentic.RandomizedConcreteC3Real.ConcreteC3RealInputs.tv_le
#print axioms Cogentic.RandomizedConcreteC3Real.ConcreteC3RealInputs.heps_le_unfolded_iff
#print axioms Cogentic.RandomizedConcreteC3Real.hit_prob_ge
#print axioms Cogentic.RandomizedConcreteC3Real.c3Inputs
#print axioms Cogentic.RandomizedConcreteC3Real.c3Inputs_tv_le_odd

end Cogentic.RandomizedConcreteC3Real
