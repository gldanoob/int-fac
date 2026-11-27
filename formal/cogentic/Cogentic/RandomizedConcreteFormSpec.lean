import Cogentic.RandomizedDirectClassSampler
import Cogentic.RandomizedFormGroup
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic

/-!
# A concrete `DirectFormSpec` for the reduced forms of discriminant `-8 * N`

This file instantiates `Cogentic.RandomizedDirectClassSampler.DirectFormSpec` with
the *actual* canonical primitive reduced binary quadratic forms of discriminant
`-8 * N`, represented as `[A, 2b, C]` and defined by
`Cogentic.RandomizedFormGroup.ReducedForms N`.

The instantiation is completely explicit:

* `Form = ℕ × ℤ × ℕ`, where `(A, b, C)` represents the form
  `A * x ^ 2 + 2 * b * x * y + C * y ^ 2`;
* `N` is the modulus (assumed odd, which is the case relevant to the sampler);
* `U = Nat.sqrt (8 * N / 3)` is the exact leading-coefficient bound of
  `RandomizedFormGroup.leading_le_sqrt`;
* `allForms = ReducedForms N`;
* `leadCoeff (A, b, C) = A` and `midCoeff (A, b, C) = b`;
* `roots N A` is the finite set of canonical balanced representatives
  `ZMod.valMinAbs x` of the solutions `x ^ 2 = -2 * N` in `ZMod A`;
* `buildForm N A b` constructs `C = (b.natAbs ^ 2 + 2 * N) / A` and accepts
  exactly when `IsReducedForm N A b C` holds.

Every field is proved.  In particular:

* `concreteRoots_card_le` uses `RandomizedFormGroup.rootCount_coprime_le`;
* `concreteRoots_mem_of_isReduced` uses the discriminant identity
  `A * C - b ^ 2 = 2 * N` and `ZMod.valMinAbs_spec`;
* `concreteBuildForm_eq_some_iff` shows that the constructor is inverse to
  `(leadCoeff, midCoeff)` on `ReducedForms N`;
* `concreteCoeff_injOn` shows that `(leadCoeff, midCoeff)` is injective on
  `ReducedForms N`.

No `Classical.choose`, `sorry`, `admit`, `axiom`, or `native_decide` is used.
-/

namespace Cogentic.RandomizedConcreteFormSpec

set_option linter.style.haveILetI false

open Finset
open Cogentic.RandomizedDirectClassSampler
open Cogentic.RandomizedFormGroup

/-- The concrete form representation `[A, 2b, C]`. -/
abbrev ConcreteForm : Type := ℕ × ℤ × ℕ

/-- The exact leading-coefficient bound for reduced forms of discriminant `-8 * N`. -/
noncomputable def leadingBound (N : ℕ) : ℕ := Nat.sqrt (8 * N / 3)

/-- The canonical roots of `b ^ 2 ≡ -2 * N (mod A)`, represented by
`ZMod.valMinAbs`, i.e. the unique representative in `(-A / 2, A / 2]`. -/
noncomputable def concreteRoots (N A : ℕ) : Finset ℤ :=
  if h : A = 0 then ∅
  else
    haveI : NeZero A := ⟨h⟩
    (Finset.univ.filter (fun x : ZMod A => x ^ 2 = (-2 * (N : ZMod A)))).image
      ZMod.valMinAbs

/-- The root-count bound `R(A) ≤ 2 ^ (ω(A) + 1)` for odd `N` and `A` coprime to `N`. -/
theorem concreteRoots_card_le {N : ℕ} (hN : Odd N) :
    ∀ A, 1 ≤ A → A ≤ leadingBound N → Nat.Coprime A N →
      (concreteRoots N A).card ≤ 2 ^ (A.primeFactors.card + 1) := by
  intro A hA1 _ hcop
  have hA0 : A ≠ 0 := by omega
  haveI : NeZero A := ⟨hA0⟩
  rw [concreteRoots, dif_neg hA0]
  rw [Finset.card_image_of_injective _ ZMod.injective_valMinAbs]
  have hroot : (Finset.univ.filter
      (fun x : ZMod A => x ^ 2 = (-2 * (N : ZMod A)))).card ≤
      2 ^ A.primeFactors.card := by
    rw [← rootCount_eq_card]
    exact rootCount_coprime_le hN hA0 hcop
  exact hroot.trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))

/-- The canonical primitive reduced form of discriminant `-8 * N` attached to
`(A, b)`, or `none` if `(A, b)` is not reduced.  The trailing coefficient is
forced by the discriminant: `C = (b ^ 2 + 2 * N) / A`. -/
noncomputable def concreteBuildForm (N : ℕ) (A : ℕ) (b : ℤ) : Option ConcreteForm :=
  let C := (b.natAbs ^ 2 + 2 * N) / A
  if IsReducedForm N A b C then some (A, b, C) else none

/-- The canonical balanced representative of the residue of `b` modulo `A` is `b`
whenever `b` lies in the reduced half-open interval `(-A, A]` for `2 * b`. -/
theorem valMinAbs_intCast_eq_of_bounds {A : ℕ} (hA : 0 < A) {b : ℤ}
    (hlo : -(A : ℤ) < 2 * b) (hhi : 2 * b ≤ (A : ℤ)) :
    ZMod.valMinAbs (b : ZMod A) = b := by
  haveI : NeZero A := ⟨hA.ne'⟩
  refine (ZMod.valMinAbs_spec (b : ZMod A) b).mpr ⟨rfl, ?_⟩
  constructor <;> linarith

/-- Exact characterization of `concreteRoots N A` for `A > 0`: it is precisely
the set of balanced representatives in `(-A/2, A/2]` of the solutions of
`b ^ 2 ≡ -2 * N (mod A)`. -/
theorem mem_concreteRoots_iff {N A : ℕ} (hA : 0 < A) {b : ℤ} :
    b ∈ concreteRoots N A ↔
      (b : ZMod A) ^ 2 = (-2 * (N : ZMod A)) ∧
        b * 2 ∈ Set.Ioc (-(A : ℤ)) (A : ℤ) := by
  haveI : NeZero A := ⟨hA.ne'⟩
  rw [concreteRoots, dif_neg hA.ne']
  constructor
  · intro hb
    obtain ⟨x, hx, hxb⟩ := Finset.mem_image.mp hb
    have hxroot := (Finset.mem_filter.mp hx).2
    have hspec := (ZMod.valMinAbs_spec x b).mp hxb
    rw [hspec.1] at hxroot
    exact ⟨hxroot, hspec.2⟩
  · rintro ⟨hroot, hbounds⟩
    refine Finset.mem_image.mpr ⟨(b : ZMod A), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hroot⟩
    · exact (ZMod.valMinAbs_spec (b : ZMod A) b).mpr ⟨rfl, hbounds⟩

/-- Every reduced form's middle coefficient belongs to `concreteRoots N A`. -/
theorem concreteRoots_mem_of_isReduced {N A : ℕ} {b : ℤ} {C : ℕ}
    (h : IsReducedForm N A b C) : b ∈ concreteRoots N A := by
  obtain ⟨hdisc, hA, hlo, hhi, _⟩ := h
  have hA0 : A ≠ 0 := by omega
  haveI : NeZero A := ⟨hA0⟩
  rw [concreteRoots, dif_neg hA0]
  refine Finset.mem_image.mpr ⟨(b : ZMod A), ?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hcast : -(((b : ZMod A) ^ 2)) = 2 * (N : ZMod A) := by
      have h := congrArg (fun z : ℤ => (z : ZMod A)) hdisc
      push_cast at h
      simpa using h
    calc
      (b : ZMod A) ^ 2 = -(-(((b : ZMod A) ^ 2))) := by ring
      _ = -(2 * (N : ZMod A)) := by rw [hcast]
      _ = -2 * (N : ZMod A) := by ring
  · exact valMinAbs_intCast_eq_of_bounds hA hlo hhi

/-- `concreteBuildForm` is exactly the inverse of `(leadCoeff, midCoeff)` on
`ReducedForms N`.  This equivalence is unconditional. -/
theorem concreteBuildForm_eq_some_iff {N A : ℕ} {b : ℤ} {f : ConcreteForm} :
    concreteBuildForm N A b = some f ↔
      f ∈ ReducedForms N ∧ f.1 = A ∧ f.2.1 = b := by
  constructor
  · intro hbuild
    unfold concreteBuildForm at hbuild
    dsimp only at hbuild
    split_ifs at hbuild with hred
    have hf : f = (A, b, (b.natAbs ^ 2 + 2 * N) / A) :=
      (Option.some.inj hbuild).symm
    subst hf
    exact ⟨mem_reducedForms.mpr hred, rfl, rfl⟩
  · rintro ⟨hfmem, hlead, hmid⟩
    rcases f with ⟨A', b', C'⟩
    simp only at hlead hmid
    subst A'
    subst b'
    have hred : IsReducedForm N A b C' := by
      simpa using mem_reducedForms.mp hfmem
    have hAC : A * C' = b.natAbs ^ 2 + 2 * N := by
      have hZ : (A : ℤ) * (C' : ℤ) =
          (b.natAbs : ℤ) ^ 2 + 2 * (N : ℤ) := by
        have hd := hred.1
        rw [Int.natAbs_sq]
        linarith
      exact_mod_cast hZ
    have hC : (b.natAbs ^ 2 + 2 * N) / A = C' := by
      rw [← hAC, Nat.mul_div_cancel_left C' hred.2.1]
    have hred' : IsReducedForm N A b ((b.natAbs ^ 2 + 2 * N) / A) := by
      rwa [hC]
    unfold concreteBuildForm
    dsimp only
    rw [if_pos hred', hC]

/-- `(leadCoeff, midCoeff)` is injective on `ReducedForms N`. -/
theorem concreteCoeff_injOn (N : ℕ) :
    Set.InjOn (fun f : ConcreteForm => (f.1, f.2.1)) (ReducedForms N : Set ConcreteForm) := by
  rintro ⟨A, b, C⟩ hf ⟨A', b', C'⟩ hg heq
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  have hApos : (0 : ℤ) < A := by
    simpa using (mem_reducedForms.mp hf).2.1
  have hAne : (A : ℤ) ≠ 0 := ne_of_gt hApos
  have hdisc₁ : (A : ℤ) * (C : ℤ) - (b : ℤ) ^ 2 = 2 * (N : ℤ) := by
    simpa using (mem_reducedForms.mp hf).1
  have hdisc₂ : (A : ℤ) * (C' : ℤ) - (b : ℤ) ^ 2 = 2 * (N : ℤ) := by
    simpa using (mem_reducedForms.mp hg).1
  have hmul : (A : ℤ) * (C : ℤ) = (A : ℤ) * (C' : ℤ) := by linarith
  have hCC' : (C : ℤ) = (C' : ℤ) := mul_left_cancel₀ hAne hmul
  have hCC : C = C' := by exact_mod_cast hCC'
  subst hCC
  rfl

/-- **The concrete `DirectFormSpec`** for the canonical primitive reduced forms
of discriminant `-8 * N`, for odd `N`. -/
noncomputable def concreteFormSpec (N : ℕ) (hN : Odd N) :
    DirectFormSpec ConcreteForm where
  N := N
  U := leadingBound N
  roots := concreteRoots N
  roots_card_le := concreteRoots_card_le hN
  buildForm := concreteBuildForm N
  allForms := ReducedForms N
  leadCoeff := fun f => f.1
  midCoeff := fun f => f.2.1
  leadCoeff_pos := by
    intro f hf
    have h := (mem_reducedForms.mp hf).2.1
    omega
  leadCoeff_le := by
    intro f hf
    exact leading_le_sqrt (mem_reducedForms.mp hf)
  midCoeff_mem_roots := by
    intro f hf
    exact concreteRoots_mem_of_isReduced (mem_reducedForms.mp hf)
  coeff_injective := concreteCoeff_injOn N
  buildForm_eq_some_iff := by
    intro A b f _hA1 _hAU _hcop _hb
    exact concreteBuildForm_eq_some_iff

@[simp] theorem concreteFormSpec_N (N : ℕ) (hN : Odd N) :
    (concreteFormSpec N hN).N = N := rfl

@[simp] theorem concreteFormSpec_U (N : ℕ) (hN : Odd N) :
    (concreteFormSpec N hN).U = leadingBound N := rfl

@[simp] theorem concreteFormSpec_roots (N : ℕ) (hN : Odd N) (A : ℕ) :
    (concreteFormSpec N hN).roots A = concreteRoots N A := rfl

@[simp] theorem concreteFormSpec_allForms (N : ℕ) (hN : Odd N) :
    (concreteFormSpec N hN).allForms = ReducedForms N := rfl

@[simp] theorem concreteFormSpec_leadCoeff (N : ℕ) (hN : Odd N) (f : ConcreteForm) :
    (concreteFormSpec N hN).leadCoeff f = f.1 := rfl

@[simp] theorem concreteFormSpec_midCoeff (N : ℕ) (hN : Odd N) (f : ConcreteForm) :
    (concreteFormSpec N hN).midCoeff f = f.2.1 := rfl

@[simp] theorem concreteFormSpec_buildForm (N : ℕ) (hN : Odd N) (A : ℕ) (b : ℤ) :
    (concreteFormSpec N hN).buildForm A b = concreteBuildForm N A b := rfl

/-- The principal reduced form `[1, 0, 2N]` is in `allForms`. -/
theorem principal_mem_reducedForms {N : ℕ} (hN : 0 < N) :
    (1, (0 : ℤ), 2 * N) ∈ ReducedForms N := by
  refine mem_reducedForms.mpr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · push_cast; ring
  · norm_num
  · norm_num
  · norm_num
  · exact_mod_cast (show 1 ≤ 2 * N by omega)
  · intro _; norm_num
  · simp

/-- `allForms` is nonempty for every positive modulus. -/
theorem concreteFormSpec_allForms_nonempty {N : ℕ} (hN : Odd N) :
    (concreteFormSpec N hN).allForms.Nonempty := by
  have hNpos : 0 < N := by rcases hN with ⟨k, rfl⟩; omega
  exact ⟨(1, (0 : ℤ), 2 * N), principal_mem_reducedForms hNpos⟩

/-! ## Axiom audit -/

#print axioms concreteRoots_card_le
#print axioms mem_concreteRoots_iff
#print axioms concreteRoots_mem_of_isReduced
#print axioms concreteBuildForm_eq_some_iff
#print axioms concreteCoeff_injOn
#print axioms concreteFormSpec
#print axioms concreteFormSpec_allForms_nonempty

end Cogentic.RandomizedConcreteFormSpec
