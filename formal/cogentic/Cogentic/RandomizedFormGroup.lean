import Cogentic.RandomizedPrimeBinSupply
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Cogentic.RandomizedFormGroup

open Finset
open scoped BigOperators

/-! ### Section 1: Canonical primitive reduced forms of discriminant `-8 * N` -/

/-- Canonical primitive reduced binary quadratic form `[A, 2b, C]` of discriminant `-8 * N`. -/
def IsReducedForm (N : ℕ) (A : ℕ) (b : ℤ) (C : ℕ) : Prop :=
  (A : ℤ) * (C : ℤ) - b ^ 2 = 2 * (N : ℤ) ∧
  0 < A ∧
  -(A : ℤ) < 2 * b ∧
  2 * b ≤ (A : ℤ) ∧
  A ≤ C ∧
  (A = C → 0 ≤ b) ∧
  Nat.gcd (Nat.gcd A (2 * b.natAbs)) C = 1

instance (N A : ℕ) (b : ℤ) (C : ℕ) : Decidable (IsReducedForm N A b C) := by
  unfold IsReducedForm
  infer_instance

/-- Every reduced form of discriminant `-8 * N` satisfies `3 * A^2 ≤ 8 * N`. -/
theorem leading_square_bound {N A : ℕ} {b : ℤ} {C : ℕ} (h : IsReducedForm N A b C) :
    3 * A ^ 2 ≤ 8 * N := by
  obtain ⟨hdisc, hA, hlo, hhi, hAC, _, _⟩ := h
  have h2b : |2 * b| ≤ (A : ℤ) := abs_le.mpr ⟨hlo.le, hhi⟩
  have hsq : 4 * b ^ 2 ≤ (A : ℤ) ^ 2 := by
    have hpow := pow_le_pow_left₀ (abs_nonneg (2 * b)) h2b 2
    rw [sq_abs] at hpow
    linarith
  have hACz : (A : ℤ) ^ 2 ≤ (A : ℤ) * (C : ℤ) := by
    have : (A : ℤ) ≤ (C : ℤ) := by exact_mod_cast hAC
    nlinarith
  have hZ : 3 * (A : ℤ) ^ 2 ≤ 8 * (N : ℤ) := by linarith
  exact_mod_cast hZ

/-- Every reduced form of discriminant `-8 * N` satisfies `A ≤ Nat.sqrt (8 * N / 3)`. -/
theorem leading_le_sqrt {N A : ℕ} {b : ℤ} {C : ℕ} (h : IsReducedForm N A b C) :
    A ≤ Nat.sqrt (8 * N / 3) := by
  apply Nat.le_sqrt.mpr
  rw [← sq]
  exact Nat.le_div_iff_mul_le (by decide : 0 < 3) |>.mpr (by linarith [leading_square_bound h])

/-- The finite set of canonical primitive reduced binary quadratic forms `[A, 2b, C]`
of discriminant `-8 * N`. -/
noncomputable def ReducedForms (N : ℕ) : Finset (ℕ × ℤ × ℕ) :=
  let U := Nat.sqrt (8 * N / 3)
  (((Finset.Icc 1 U) ×ˢ (Finset.Icc (-(U : ℤ)) (U : ℤ))).image
      fun p => (p.1, p.2, (p.2.natAbs ^ 2 + 2 * N) / p.1)).filter
    fun f => IsReducedForm N f.1 f.2.1 f.2.2

theorem mem_reducedForms {N : ℕ} {f : ℕ × ℤ × ℕ} :
    f ∈ ReducedForms N ↔ IsReducedForm N f.1 f.2.1 f.2.2 := by
  rcases f with ⟨A, b, C⟩
  constructor
  · intro hf
    exact (Finset.mem_filter.mp hf).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ?_, h⟩
    dsimp only at h
    have hAU : A ≤ Nat.sqrt (8 * N / 3) := leading_le_sqrt h
    obtain ⟨hdisc, hA, hlo, hhi, _, _, _⟩ := h
    refine ⟨(A, b), Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hA, hAU⟩,
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩, ?_⟩
    have hAC : A * C = b.natAbs ^ 2 + 2 * N := by
      have hZ : (A : ℤ) * (C : ℤ) = (b.natAbs : ℤ) ^ 2 + 2 * (N : ℤ) := by
        rw [Int.natAbs_sq]
        linarith
      exact_mod_cast hZ
    simp only [Prod.mk.injEq, true_and]
    rw [← hAC, Nat.mul_div_cancel_left C hA]

/-! ### Section 2: Modular square root count `rootCount` and multiplicativity -/

/-- The number of solutions `b mod A` to `b^2 ≡ -2 * N (mod A)`. -/
def rootCount (N A : ℕ) : ℕ :=
  if h : A = 0 then 0 else
    haveI : NeZero A := ⟨h⟩
    (Finset.univ.filter (fun b : ZMod A => b ^ 2 = (-2 * (N : ZMod A)))).card

lemma rootCount_eq_card (N A : ℕ) [NeZero A] :
    rootCount N A = (Finset.univ.filter (fun b : ZMod A => b ^ 2 = (-2 * (N : ZMod A)))).card := by
  simp [rootCount, NeZero.ne A]

@[simp] lemma rootCount_zero (N : ℕ) : rootCount N 0 = 0 := by
  simp [rootCount]

@[simp] lemma rootCount_one (N : ℕ) : rootCount N 1 = 1 := by
  rw [rootCount_eq_card]
  have h : (Finset.univ.filter (fun b : ZMod 1 => b ^ 2 = (-2 * (N : ZMod 1)))) = Finset.univ := by
    ext x
    simp [Subsingleton.elim (x ^ 2) (-2 * (N : ZMod 1))]
  rw [h, Finset.card_univ, ZMod.card]

/-- Multiplicativity of `rootCount N` on coprime moduli via CRT. -/
theorem rootCount_mul_of_coprime {N m n : ℕ} (h : m.Coprime n) :
    rootCount N (m * n) = rootCount N m * rootCount N n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  have : NeZero m := ⟨hm⟩
  have : NeZero n := ⟨hn⟩
  have : NeZero (m * n) := ⟨mul_ne_zero hm hn⟩
  rw [rootCount_eq_card, rootCount_eq_card, rootCount_eq_card]
  let e := ZMod.chineseRemainder h
  let Sm := Finset.univ.filter (fun b : ZMod m => b ^ 2 = (-2 * (N : ZMod m)))
  let Sn := Finset.univ.filter (fun b : ZMod n => b ^ 2 = (-2 * (N : ZMod n)))
  let Smn := Finset.univ.filter (fun b : ZMod (m * n) => b ^ 2 = (-2 * (N : ZMod (m * n))))
  change Smn.card = Sm.card * Sn.card
  rw [← Finset.card_product]
  refine Finset.card_bij (fun b _ => e b) ?_ ?_ ?_
  · intro b hb
    have hsq : b ^ 2 = (-2 * (N : ZMod (m * n))) := (Finset.mem_filter.mp hb).2
    have he := congrArg e hsq
    rw [map_pow, map_mul, map_neg, map_ofNat, map_natCast] at he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using h1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using h2⟩⟩
  · intro b₁ _ b₂ _ heq
    exact e.injective heq
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    have h1 : p.1 ^ 2 = (-2 * (N : ZMod m)) := (Finset.mem_filter.mp hp1).2
    have h2 : p.2 ^ 2 = (-2 * (N : ZMod n)) := (Finset.mem_filter.mp hp2).2
    refine ⟨e.symm p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, e.apply_symm_apply p⟩
    apply e.injective
    rw [map_pow, e.apply_symm_apply, map_mul, map_neg, map_ofNat, map_natCast]
    ext
    · simpa using h1
    · simpa using h2

/-- Multiplicativity of `rootCount N` over a pairwise coprime product. -/
theorem rootCount_finset_prod {ι : Type*} (N : ℕ) (s : Finset ι) (f : ι → ℕ)
    (hcop : (s : Set ι).Pairwise fun i j => (f i).Coprime (f j)) :
    rootCount N (∏ i ∈ s, f i) = ∏ i ∈ s, rootCount N (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hcop_a : (f a).Coprime (∏ i ∈ s, f i) :=
      Nat.Coprime.prod_right fun i hi =>
        hcop (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi) (fun h => ha (h ▸ hi))
    rw [rootCount_mul_of_coprime hcop_a, ih (hcop.mono (by intro x hx; exact Finset.mem_insert_of_mem hx))]

/-- Every nonzero modulus factors `rootCount N A` over its prime-power components. -/
theorem rootCount_eq_prod_primeFactors {N A : ℕ} (hA : A ≠ 0) :
    rootCount N A = ∏ p ∈ A.primeFactors, rootCount N (p ^ A.factorization p) := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hA]
  rw [Finsupp.prod, Nat.support_factorization]
  apply rootCount_finset_prod
  intro p hp q hq hpq
  exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
    (Nat.prime_of_mem_primeFactors hq)).mpr hpq).pow _ _

/-- Each leading coefficient `A ≥ 1` has at most `rootCount N A` reduced forms in `ReducedForms N`. -/
theorem reducedForms_fiber_card_le_rootCount (N A : ℕ) (hA : 0 < A) :
    ((ReducedForms N).filter (fun f => f.1 = A)).card ≤ rootCount N A := by
  have : NeZero A := ⟨hA.ne'⟩
  rw [rootCount_eq_card]
  refine Finset.card_le_card_of_injOn (fun f => (f.2.1 : ZMod A)) ?_ ?_
  · intro f hf
    obtain ⟨hfR, hfA⟩ := Finset.mem_filter.mp hf
    have h := mem_reducedForms.mp hfR
    rw [hfA] at h
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hdisc : (f.2.1 : ℤ) ^ 2 + 2 * (N : ℤ) = (A : ℤ) * (f.2.2 : ℤ) := by linarith [h.1]
    have hcast := congrArg (Int.cast : ℤ → ZMod A) hdisc
    simp only [Int.cast_add, Int.cast_pow, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      ZMod.natCast_self, zero_mul] at hcast
    linear_combination hcast
  · intro f₁ hf₁ f₂ hf₂ heq
    dsimp only at heq
    obtain ⟨hf₁R, hf₁A⟩ := Finset.mem_filter.mp hf₁
    obtain ⟨hf₂R, hf₂A⟩ := Finset.mem_filter.mp hf₂
    have h₁ := mem_reducedForms.mp hf₁R
    have h₂ := mem_reducedForms.mp hf₂R
    rw [hf₁A] at h₁
    rw [hf₂A] at h₂
    have hsub : ((f₁.2.1 - f₂.2.1 : ℤ) : ZMod A) = 0 := by
      rw [Int.cast_sub, heq, sub_self]
    have hdvd : (A : ℤ) ∣ f₁.2.1 - f₂.2.1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hsub
    have hlt : |f₁.2.1 - f₂.2.1| < (A : ℤ) := by
      have hlo₁ := h₁.2.2.1
      have hhi₁ := h₁.2.2.2.1
      have hlo₂ := h₂.2.2.1
      have hhi₂ := h₂.2.2.2.1
      rw [abs_lt]
      omega
    have hbeq : f₁.2.1 = f₂.2.1 := by
      have h0 := Int.eq_zero_of_dvd_of_nonneg_of_lt (abs_nonneg _) hlt ((dvd_abs _ _).mpr hdvd)
      have := abs_eq_zero.mp h0
      omega
    have hCeq : f₁.2.2 = f₂.2.2 := by
      have h1 := h₁.1
      have h2 := h₂.1
      rw [hbeq] at h1
      have hZ : (A : ℤ) * (f₁.2.2 : ℤ) = (A : ℤ) * (f₂.2.2 : ℤ) := by linarith
      have hAz : (A : ℤ) ≠ 0 := by exact_mod_cast hA.ne'
      exact_mod_cast mul_left_cancel₀ hAz hZ
    rcases f₁ with ⟨A₁, b₁, C₁⟩
    rcases f₂ with ⟨A₂, b₂, C₂⟩
    dsimp only at hf₁A hf₂A hbeq hCeq
    simp [hf₁A, hf₂A, hbeq, hCeq]

/-- Summing `rootCount N A` up to `Nat.sqrt (8 * N / 3)` bounds `(ReducedForms N).card`. -/
theorem reducedForms_card_le_sum_rootCount (N : ℕ) :
    (ReducedForms N).card ≤ ∑ A ∈ Finset.Icc 1 (Nat.sqrt (8 * N / 3)), rootCount N A := by
  have hmaps : ∀ f ∈ ReducedForms N, f.1 ∈ Finset.Icc 1 (Nat.sqrt (8 * N / 3)) := by
    intro f hf
    have h := mem_reducedForms.mp hf
    exact Finset.mem_Icc.mpr ⟨h.2.1, leading_le_sqrt h⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_le_sum fun A hA => ?_
  exact reducedForms_fiber_card_le_rootCount N A (Finset.mem_Icc.mp hA).1

/-! ### Section 3: Exact local prime-power bounds -/

/-- For an odd prime `p ∤ N`, `b^2 ≡ -2N (mod p^k)` has at most 2 solutions. -/
theorem rootCount_prime_pow_le_two {N p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hndvd : ¬ p ∣ N)
    (k : ℕ) : rootCount N (p ^ k) ≤ 2 := by
  rcases k with _ | k
  · simp
  have hpk : p ^ (k + 1) ≠ 0 := pow_ne_zero (k + 1) hp.ne_zero
  have : NeZero (p ^ (k + 1)) := ⟨hpk⟩
  rw [rootCount_eq_card]
  let S := Finset.univ.filter (fun b : ZMod (p ^ (k + 1)) => b ^ 2 = (-2 * (N : ZMod (p ^ (k + 1)))))
  change S.card ≤ 2
  rcases S.eq_empty_or_nonempty with hS | ⟨b₀, hb₀⟩
  · simp [hS]
  · have hsub : S ⊆ {b₀, -b₀} := by
      intro b hb
      rw [Finset.mem_insert, Finset.mem_singleton]
      have hsq₀ : b₀ ^ 2 = (-2 * (N : ZMod (p ^ (k + 1)))) := (Finset.mem_filter.mp hb₀).2
      have hsq : b ^ 2 = (-2 * (N : ZMod (p ^ (k + 1)))) := (Finset.mem_filter.mp hb).2
      have hdiff : ((b.val : ℤ) - (b₀.val : ℤ)) * ((b.val : ℤ) + (b₀.val : ℤ)) =
          (b.val : ℤ) ^ 2 - (b₀.val : ℤ) ^ 2 := by ring
      have hcast : (((b.val : ℤ) ^ 2 - (b₀.val : ℤ) ^ 2 : ℤ) : ZMod (p ^ (k + 1))) = 0 := by
        simp [hsq, hsq₀]
      have hdvd : ((p ^ (k + 1) : ℕ) : ℤ) ∣
          ((b.val : ℤ) - (b₀.val : ℤ)) * ((b.val : ℤ) + (b₀.val : ℤ)) := by
        rw [hdiff]
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
      have hnotboth : ¬ ((p : ℤ) ∣ (b.val : ℤ) - (b₀.val : ℤ) ∧
          (p : ℤ) ∣ (b.val : ℤ) + (b₀.val : ℤ)) := by
        rintro ⟨hm, hp'⟩
        have h2b : (p : ℤ) ∣ 2 * (b.val : ℤ) := by
          have := dvd_add hm hp'
          rwa [show (b.val : ℤ) - (b₀.val : ℤ) + ((b.val : ℤ) + (b₀.val : ℤ)) =
            2 * (b.val : ℤ) by ring] at this
        have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
        have hp_ndvd2 : ¬ (p : ℤ) ∣ 2 := by
          intro h2
          have : p ∣ 2 := by exact_mod_cast h2
          have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
          exact hp2 this
        have hpb : (p : ℤ) ∣ (b.val : ℤ) := (hp_int.dvd_mul.mp h2b).resolve_left hp_ndvd2
        have hpb2 : (p : ℤ) ∣ (b.val : ℤ) ^ 2 := dvd_pow hpb (by decide)
        have hcast2 : (((b.val : ℤ) ^ 2 + 2 * (N : ℤ) : ℤ) : ZMod (p ^ (k + 1))) = 0 := by
          simp [hsq]
        have hdvd2 : ((p ^ (k + 1) : ℕ) : ℤ) ∣ (b.val : ℤ) ^ 2 + 2 * (N : ℤ) :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast2
        have hp_dvd_pk : (p : ℤ) ∣ ((p ^ (k + 1) : ℕ) : ℤ) := by
          exact_mod_cast dvd_pow_self p (Nat.succ_ne_zero k)
        have hp2N : (p : ℤ) ∣ 2 * (N : ℤ) := by
          have hsum := hp_dvd_pk.trans hdvd2
          simpa using dvd_sub hsum hpb2
        have hpN : (p : ℤ) ∣ (N : ℤ) := (hp_int.dvd_mul.mp hp2N).resolve_left hp_ndvd2
        exact hndvd (by exact_mod_cast hpN)
      have hcop_or : IsCoprime ((p ^ (k + 1) : ℕ) : ℤ) ((b.val : ℤ) + (b₀.val : ℤ)) ∨
          IsCoprime ((p ^ (k + 1) : ℕ) : ℤ) ((b.val : ℤ) - (b₀.val : ℤ)) := by
        have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
        by_cases h1 : (p : ℤ) ∣ (b.val : ℤ) + (b₀.val : ℤ)
        · right
          have h2 : ¬ (p : ℤ) ∣ (b.val : ℤ) - (b₀.val : ℤ) := fun hm => hnotboth ⟨hm, h1⟩
          push_cast
          exact (hp_int.irreducible.coprime_iff_not_dvd.mpr h2).pow_left
        · left
          push_cast
          exact (hp_int.irreducible.coprime_iff_not_dvd.mpr h1).pow_left
      rcases hcop_or with hcop | hcop
      · left
        have hdiv : ((p ^ (k + 1) : ℕ) : ℤ) ∣ (b.val : ℤ) - (b₀.val : ℤ) :=
          hcop.dvd_of_dvd_mul_right hdvd
        have hz : (((b.val : ℤ) - (b₀.val : ℤ) : ℤ) : ZMod (p ^ (k + 1))) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv
        simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, sub_eq_zero] at hz
        exact hz
      · right
        have hdiv : ((p ^ (k + 1) : ℕ) : ℤ) ∣ (b.val : ℤ) + (b₀.val : ℤ) :=
          hcop.dvd_of_dvd_mul_left hdvd
        have hz : (((b.val : ℤ) + (b₀.val : ℤ) : ℤ) : ZMod (p ^ (k + 1))) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv
        simp only [Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val] at hz
        exact eq_neg_of_add_eq_zero_left hz
    calc
      S.card ≤ ({b₀, -b₀} : Finset (ZMod (p ^ (k + 1)))).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two

/-- For odd `N` and `k ≥ 2`, `b^2 ≡ -2N (mod 2^k)` has no solutions (since `-2N ≡ 2 mod 4`). -/
theorem rootCount_two_pow_eq_zero {N k : ℕ} (hN : Odd N) (hk : 2 ≤ k) :
    rootCount N (2 ^ k) = 0 := by
  have : NeZero (2 ^ k) := ⟨pow_ne_zero k (by decide)⟩
  rw [rootCount_eq_card, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro b _ hsq
  have h4dvd : 4 ∣ 2 ^ k := by
    have : (2 : ℕ) ^ 2 ∣ 2 ^ k := Nat.pow_dvd_pow 2 hk
    simpa using this
  have hcast := congrArg (ZMod.castHom h4dvd (ZMod 4)) hsq
  rw [map_pow, map_mul, map_neg, map_ofNat, map_natCast] at hcast
  obtain ⟨m, rfl⟩ := hN
  have hrhs : (-2 * ((2 * m + 1 : ℕ) : ZMod 4)) = 2 := by
    push_cast
    have h4 : (4 : ZMod 4) = 0 := rfl
    have hneg2 : (-2 : ZMod 4) = 2 := by decide
    calc
      -2 * (2 * (m : ZMod 4) + 1) = -(4 : ZMod 4) * (m : ZMod 4) + (-2 : ZMod 4) := by ring
      _ = 2 := by rw [h4, neg_zero, zero_mul, zero_add, hneg2]
  rw [hrhs] at hcast
  have hno : ∀ x : ZMod 4, x ^ 2 ≠ 2 := by decide
  exact hno (ZMod.castHom h4dvd (ZMod 4) b) hcast

/-- For odd `N`, `rootCount N (2^k) ≤ 1` for every `k : ℕ`. -/
theorem rootCount_two_pow_le_one {N : ℕ} (hN : Odd N) (k : ℕ) :
    rootCount N (2 ^ k) ≤ 1 := by
  match k with
  | 0 => simp
  | 1 =>
    rw [pow_one, rootCount_eq_card]
    have h : (Finset.univ.filter (fun b : ZMod 2 => b ^ 2 = (-2 * (N : ZMod 2)))) = {0} := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      have h2 : (2 : ZMod 2) = 0 := rfl
      rw [h2, neg_zero, zero_mul]
      revert b; decide
    rw [h, Finset.card_singleton]
  | k + 2 =>
    rw [rootCount_two_pow_eq_zero hN (by omega)]
    exact Nat.zero_le 1

/-- For odd `N` and `A ≠ 0` coprime to `N`, `rootCount N A ≤ 2 ^ A.primeFactors.card`. -/
theorem rootCount_coprime_le {N A : ℕ} (hN : Odd N) (hA : A ≠ 0) (hcop : A.Coprime N) :
    rootCount N A ≤ 2 ^ A.primeFactors.card := by
  rw [rootCount_eq_prod_primeFactors hA]
  calc
    ∏ p ∈ A.primeFactors, rootCount N (p ^ A.factorization p)
      ≤ ∏ _p ∈ A.primeFactors, 2 := by
        refine Finset.prod_le_prod' fun p hp => ?_
        have hprime := Nat.prime_of_mem_primeFactors hp
        have hpdvd := Nat.dvd_of_mem_primeFactors hp
        by_cases hp2 : p = 2
        · rw [hp2]; exact (rootCount_two_pow_le_one hN _).trans (by decide)
        · have hndvd : ¬ p ∣ N := fun h =>
            hprime.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hpdvd h)
          exact rootCount_prime_pow_le_two hprime hp2 hndvd _
    _ = 2 ^ A.primeFactors.card := by simp

private lemma zmod_sq_eq_neg_two_mul_iff {N A : ℕ} [NeZero A] (b : ZMod A) :
    b ^ 2 = (-2 * (N : ZMod A)) ↔ A ∣ b.val ^ 2 + 2 * N := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [ZMod.natCast_zmod_val]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- Local root count for a prime `p` when `k ≤ padicValNat p N`:
`rootCount N (p^k) ≤ p^(k / 2)`. -/
theorem rootCount_prime_pow_le_of_le_val {N p k : ℕ} (hp : p.Prime)
    (hk : k ≤ padicValNat p N) : rootCount N (p ^ k) ≤ p ^ (k / 2) := by
  have : Fact p.Prime := ⟨hp⟩
  have hpk : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  have : NeZero (p ^ k) := ⟨hpk⟩
  rw [rootCount_eq_card]
  have hdvdN : p ^ k ∣ N := by
    by_cases hN : N = 0
    · simp [hN]
    · exact (padicValNat_dvd_iff_le hN).mpr hk
  let r := (k + 1) / 2
  have hrk : r + k / 2 = k := by omega
  have hinj : ∀ b ∈ Finset.univ.filter (fun b : ZMod (p ^ k) => b ^ 2 = (-2 * (N : ZMod (p ^ k)))),
      b.val / p ^ r ∈ Finset.range (p ^ (k / 2)) := by
    intro b _
    rw [Finset.mem_range, Nat.div_lt_iff_lt_mul (pow_pos hp.pos r)]
    rw [← pow_add, add_comm, hrk]
    exact b.val_lt
  calc
    (Finset.univ.filter (fun b : ZMod (p ^ k) => b ^ 2 = (-2 * (N : ZMod (p ^ k))))).card
      ≤ (Finset.range (p ^ (k / 2))).card := by
        refine Finset.card_le_card_of_injOn (fun b => b.val / p ^ r) hinj ?_
        intro b₁ hb₁ b₂ hb₂ heq
        dsimp only at heq
        have hdvd_r (b : ZMod (p ^ k))
            (hb : b ∈ Finset.univ.filter (fun b : ZMod (p ^ k) => b ^ 2 = (-2 * (N : ZMod (p ^ k))))) :
            p ^ r ∣ b.val := by
          have h1 := (zmod_sq_eq_neg_two_mul_iff b).mp (Finset.mem_filter.mp hb).2
          have h2 : p ^ k ∣ 2 * N := dvd_mul_of_dvd_right hdvdN 2
          have hsq : p ^ k ∣ b.val ^ 2 := (Nat.dvd_add_left h2).mp h1
          by_cases h0 : b.val = 0
          · simp [h0]
          · rw [padicValNat_dvd_iff_le h0]
            have hv := (padicValNat_dvd_iff_le (pow_ne_zero 2 h0)).mp hsq
            rw [sq, padicValNat.mul h0 h0] at hv
            omega
        have h1 := Nat.mul_div_cancel' (hdvd_r b₁ hb₁)
        have h2 := Nat.mul_div_cancel' (hdvd_r b₂ hb₂)
        apply ZMod.val_injective (p ^ k)
        rw [← h1, ← h2, heq]
    _ = p ^ (k / 2) := Finset.card_range _

/-- For an odd prime `p`, if `padicValNat p N < k` and `Odd (padicValNat p N)`,
then `rootCount N (p^k) = 0`. -/
theorem rootCount_prime_pow_eq_zero_of_odd_val {N p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : N ≠ 0) (hk : padicValNat p N < k) (hodd : Odd (padicValNat p N)) :
    rootCount N (p ^ k) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hpk : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  have : NeZero (p ^ k) := ⟨hpk⟩
  rw [rootCount_eq_card, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro b _ hsq
  have hdiv : p ^ k ∣ b.val ^ 2 + 2 * N := (zmod_sq_eq_neg_two_mul_iff b).mp hsq
  have h2Nne : 2 * N ≠ 0 := mul_ne_zero (by decide) hN
  have hval2N : padicValNat p (2 * N) = padicValNat p N := by
    rw [padicValNat.mul (by decide) hN]
    have hndvd2 : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    rw [padicValNat.eq_zero_of_not_dvd hndvd2, zero_add]
  set w := padicValNat p N
  have hwk : p ^ (w + 1) ∣ b.val ^ 2 + 2 * N := (Nat.pow_dvd_pow p hk).trans hdiv
  by_cases hb0 : b.val = 0
  · rw [hb0, zero_pow (by decide), zero_add] at hwk
    have := (padicValNat_dvd_iff_le h2Nne).mp hwk
    omega
  · set v := padicValNat p b.val
    have hval_sq : padicValNat p (b.val ^ 2) = 2 * v := by
      rw [sq, padicValNat.mul hb0 hb0, two_mul]
    have hne : 2 * v ≠ w := by
      rcases hodd with ⟨m, hm⟩
      omega
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hd1 : p ^ (2 * v + 1) ∣ 2 * N := by
        rw [padicValNat_dvd_iff_le h2Nne, hval2N]
        omega
      have hd2 : p ^ (2 * v + 1) ∣ b.val ^ 2 + 2 * N :=
        (Nat.pow_dvd_pow p (by omega : 2 * v + 1 ≤ k)).trans hdiv
      have hd3 : p ^ (2 * v + 1) ∣ b.val ^ 2 := (Nat.dvd_add_left hd1).mp hd2
      have := (padicValNat_dvd_iff_le (pow_ne_zero 2 hb0)).mp hd3
      omega
    · have hd1 : p ^ (w + 1) ∣ b.val ^ 2 := by
        rw [padicValNat_dvd_iff_le (pow_ne_zero 2 hb0), hval_sq]
        omega
      have hd3 : p ^ (w + 1) ∣ 2 * N := (Nat.dvd_add_right hd1).mp hwk
      have := (padicValNat_dvd_iff_le h2Nne).mp hd3
      omega

/-- For an odd prime `p` and `padicValNat p N < k`, `rootCount N (p^k) ≤ 2 * p^(padicValNat p N / 2)`. -/
theorem rootCount_prime_pow_le_of_gt_val {N p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : N ≠ 0) (hk : padicValNat p N < k) :
    rootCount N (p ^ k) ≤ 2 * p ^ (padicValNat p N / 2) := by
  have : Fact p.Prime := ⟨hp⟩
  set w := padicValNat p N
  rcases Nat.even_or_odd w with ⟨j, hw⟩ | hodd
  · have hpk : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
    have : NeZero (p ^ k) := ⟨hpk⟩
    have hj : w / 2 = j := by omega
    have hw2 : w = 2 * j := by omega
    have hpw_dvd : p ^ w ∣ N := (padicValNat_dvd_iff_le hN).mpr le_rfl
    let M := N / p ^ w
    have hNM : p ^ w * M = N := Nat.mul_div_cancel' hpw_dvd
    have hpndvdM : ¬ p ∣ M := by
      intro hdiv
      have hpw1 : p ^ (w + 1) ∣ N := by
        rw [← hNM, pow_succ]
        exact mul_dvd_mul_left (p ^ w) hdiv
      have := (padicValNat_dvd_iff_le hN).mp hpw1
      omega
    have : NeZero (p ^ (k - w)) := ⟨pow_ne_zero (k - w) hp.ne_zero⟩
    rw [rootCount_eq_card, hj]
    let S := Finset.univ.filter (fun b : ZMod (p ^ k) => b ^ 2 = (-2 * (N : ZMod (p ^ k))))
    let SM := Finset.univ.filter (fun r : ZMod (p ^ (k - w)) => r ^ 2 = (-2 * (M : ZMod (p ^ (k - w)))))
    have hSM_card : SM.card ≤ 2 := by
      have := rootCount_prime_pow_le_two hp hp2 hpndvdM (k - w)
      rwa [rootCount_eq_card] at this
    have hdvd_j : ∀ b ∈ S, p ^ j ∣ b.val := by
      intro b hb
      have h1 := (zmod_sq_eq_neg_two_mul_iff b).mp (Finset.mem_filter.mp hb).2
      have h2 : p ^ w ∣ b.val ^ 2 + 2 * N := (Nat.pow_dvd_pow p hk.le).trans h1
      have h3 : p ^ w ∣ 2 * N := dvd_mul_of_dvd_right hpw_dvd 2
      have h4 : p ^ w ∣ b.val ^ 2 := (Nat.dvd_add_left h3).mp h2
      by_cases hb0 : b.val = 0
      · simp [hb0]
      · rw [padicValNat_dvd_iff_le hb0]
        have := (padicValNat_dvd_iff_le (pow_ne_zero 2 hb0)).mp h4
        rw [sq, padicValNat.mul hb0 hb0] at this
        omega
    have hcard_le : S.card ≤ (SM ×ˢ Finset.range (p ^ j)).card := by
      refine Finset.card_le_card_of_injOn
        (fun b => ((b.val / p ^ j : ZMod (p ^ (k - w))), (b.val / p ^ j) / p ^ (k - w))) ?_ ?_
      · intro b hb
        have hbj := hdvd_j b hb
        set y := b.val / p ^ j
        have hby : p ^ j * y = b.val := Nat.mul_div_cancel' hbj
        have h1 := (zmod_sq_eq_neg_two_mul_iff b).mp (Finset.mem_filter.mp hb).2
        have hpw_eq : p ^ k = p ^ w * p ^ (k - w) := by
          rw [← pow_add, Nat.add_sub_of_le hk.le]
        have hsq_eq : b.val ^ 2 + 2 * N = p ^ w * (y ^ 2 + 2 * M) := by
          rw [← hby, ← hNM, mul_pow, ← pow_mul, show j * 2 = w by omega]
          ring
        have h1' : p ^ w * p ^ (k - w) ∣ p ^ w * (y ^ 2 + 2 * M) := by
          rw [← hpw_eq, ← hsq_eq]
          exact h1
        have hy_dvd : p ^ (k - w) ∣ y ^ 2 + 2 * M :=
          (Nat.mul_dvd_mul_iff_left (pow_pos hp.pos w)).mp h1'
        have hy_mem : (y : ZMod (p ^ (k - w))) ∈ SM := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have hz : ((y ^ 2 + 2 * M : ℕ) : ZMod (p ^ (k - w))) = 0 :=
            (ZMod.natCast_eq_zero_iff _ _).mpr hy_dvd
          push_cast at hz
          linear_combination hz
        have hy_lt : y < p ^ (k - w) * p ^ j := by
          have hblt := b.val_lt
          rw [← hby] at hblt
          have hpow : p ^ k = p ^ j * (p ^ (k - w) * p ^ j) := by
            rw [← mul_assoc, mul_comm (p ^ j) (p ^ (k - w)), mul_assoc, ← pow_add, ← pow_add]
            congr 1; omega
          rw [hpow] at hblt
          exact (Nat.mul_lt_mul_left (pow_pos hp.pos j)).mp hblt
        have hdiv_lt : y / p ^ (k - w) < p ^ j :=
          (Nat.div_lt_iff_lt_mul (pow_pos hp.pos (k - w))).mpr (by simpa [mul_comm] using hy_lt)
        exact Finset.mem_product.mpr ⟨hy_mem, Finset.mem_range.mpr hdiv_lt⟩
      · intro b₁ hb₁ b₂ hb₂ heq
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hmod, hdiv⟩ := heq
        have hmod_eq : (b₁.val / p ^ j) % p ^ (k - w) = (b₂.val / p ^ j) % p ^ (k - w) :=
          (ZMod.natCast_eq_natCast_iff' _ _ (p ^ (k - w))).mp hmod
        have hy_eq : b₁.val / p ^ j = b₂.val / p ^ j := by
          rw [← Nat.div_add_mod (b₁.val / p ^ j) (p ^ (k - w)),
            ← Nat.div_add_mod (b₂.val / p ^ j) (p ^ (k - w)), hdiv, hmod_eq]
        apply ZMod.val_injective (p ^ k)
        rw [← Nat.mul_div_cancel' (hdvd_j b₁ hb₁), ← Nat.mul_div_cancel' (hdvd_j b₂ hb₂), hy_eq]
    calc
      S.card ≤ (SM ×ˢ Finset.range (p ^ j)).card := hcard_le
      _ = SM.card * p ^ j := by rw [Finset.card_product, Finset.card_range]
      _ ≤ 2 * p ^ j := Nat.mul_le_mul_right _ hSM_card
  · rw [rootCount_prime_pow_eq_zero_of_odd_val hp hp2 hN hk hodd]
    exact Nat.zero_le _

/-- Unified bound for an odd prime `p` and nonzero `N`: `rootCount N (p^k) ≤ 2 * p^(k / 2)`. -/
theorem rootCount_prime_pow_le_two_mul_half {N p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : N ≠ 0) : rootCount N (p ^ k) ≤ 2 * p ^ (k / 2) := by
  by_cases hk : k ≤ padicValNat p N
  · calc
      rootCount N (p ^ k) ≤ p ^ (k / 2) := rootCount_prime_pow_le_of_le_val hp hk
      _ ≤ 2 * p ^ (k / 2) := by omega
  · have hlt : padicValNat p N < k := Nat.lt_of_not_ge hk
    calc
      rootCount N (p ^ k) ≤ 2 * p ^ (padicValNat p N / 2) :=
        rootCount_prime_pow_le_of_gt_val hp hp2 hN hlt
      _ ≤ 2 * p ^ (k / 2) :=
        Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hp.pos (by omega))

/-- Finite reciprocal-weighted prime-power sum bound:
`∑_{1 ≤ k ≤ K} rootCount N (p^k) / p^k ≤ 4 / (p - 1)`. -/
theorem sum_rootCount_prime_pow_div_le {N p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : N ≠ 0) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, (rootCount N (p ^ k) : ℝ) / (p : ℝ) ^ k ≤ 4 / ((p : ℝ) - 1) := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have hterm (k : ℕ) :
      (rootCount N (p ^ k) : ℝ) / (p : ℝ) ^ k ≤ 2 / (p : ℝ) ^ ((k + 1) / 2) := by
    have h1 : (rootCount N (p ^ k) : ℝ) ≤ 2 * (p : ℝ) ^ (k / 2) := by
      exact_mod_cast rootCount_prime_pow_le_two_mul_half hp hp2 hN (k := k)
    have hpow : (p : ℝ) ^ k = (p : ℝ) ^ (k / 2) * (p : ℝ) ^ ((k + 1) / 2) := by
      rw [← pow_add]
      congr 1; omega
    rw [hpow, div_le_div_iff₀ (by positivity) (by positivity)]
    calc
      (rootCount N (p ^ k) : ℝ) * (p : ℝ) ^ ((k + 1) / 2)
        ≤ (2 * (p : ℝ) ^ (k / 2)) * (p : ℝ) ^ ((k + 1) / 2) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 2 * ((p : ℝ) ^ (k / 2) * (p : ℝ) ^ ((k + 1) / 2)) := by ring
  let M := (K + 1) / 2
  have hpair : ∑ k ∈ Finset.Icc 1 K, (2 : ℝ) / (p : ℝ) ^ ((k + 1) / 2) ≤
      ∑ m ∈ Finset.Icc 1 M, (4 : ℝ) / (p : ℝ) ^ m := by
    have hsub : Finset.Icc 1 K ⊆ Finset.Icc 1 (2 * M) :=
      Finset.Icc_subset_Icc_right (by omega)
    calc
      ∑ k ∈ Finset.Icc 1 K, (2 : ℝ) / (p : ℝ) ^ ((k + 1) / 2)
        ≤ ∑ k ∈ Finset.Icc 1 (2 * M), (2 : ℝ) / (p : ℝ) ^ ((k + 1) / 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = ∑ m ∈ Finset.Icc 1 M, (4 : ℝ) / (p : ℝ) ^ m := by
        clear hsub hterm
        induction M with
        | zero => simp
        | succ m ih =>
          have hsplit : Finset.Icc 1 (2 * (m + 1)) =
              insert (2 * m + 2) (insert (2 * m + 1) (Finset.Icc 1 (2 * m))) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          have hsplit2 : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          have hnot1 : 2 * m + 2 ∉ insert (2 * m + 1) (Finset.Icc 1 (2 * m)) := by
            simp only [Finset.mem_insert, Finset.mem_Icc]; omega
          have hnot2 : 2 * m + 1 ∉ Finset.Icc 1 (2 * m) := by
            simp only [Finset.mem_Icc]; omega
          have hnot3 : m + 1 ∉ Finset.Icc 1 m := by
            simp only [Finset.mem_Icc]; omega
          rw [hsplit, Finset.sum_insert hnot1, Finset.sum_insert hnot2,
            ih, hsplit2, Finset.sum_insert hnot3]
          have h1 : (2 * m + 2 + 1) / 2 = m + 1 := by omega
          have h2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
          rw [h1, h2]
          ring
  have hgeom : ∑ m ∈ Finset.Icc 1 M, (4 : ℝ) / (p : ℝ) ^ m ≤ 4 / ((p : ℝ) - 1) := by
    have hshift : ∑ m ∈ Finset.Icc 1 M, (4 : ℝ) / (p : ℝ) ^ m =
        (4 / (p : ℝ)) * ∑ j ∈ Finset.range M, ((p : ℝ)⁻¹) ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun m _ => m - 1) ?_ ?_ ?_ ?_
      · intro m hm
        rw [Finset.mem_range]
        have := Finset.mem_Icc.mp hm
        omega
      · intro m₁ hm₁ m₂ hm₂ heq
        have h1 := (Finset.mem_Icc.mp hm₁).1
        have h2 := (Finset.mem_Icc.mp hm₂).1
        omega
      · intro j hj
        refine ⟨j + 1, Finset.mem_Icc.mpr ⟨by omega, by have := Finset.mem_range.mp hj; omega⟩,
          by omega⟩
      · intro m hm
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        rw [inv_pow, div_eq_mul_inv, div_eq_mul_inv, mul_assoc, ← mul_inv,
          ← pow_succ', Nat.sub_add_cancel hm1]
    rw [hshift, geom_sum_eq (by exact ne_of_lt (inv_lt_one_of_one_lt₀ hpR))]
    have hden : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hpR)
    have hnum : ((p : ℝ)⁻¹ ^ M - 1) / ((p : ℝ)⁻¹ - 1) = (1 - (p : ℝ)⁻¹ ^ M) / (1 - (p : ℝ)⁻¹) := by
      rw [← neg_div_neg_eq, neg_sub, neg_sub]
    rw [hnum]
    have hle1 : (1 - (p : ℝ)⁻¹ ^ M) / (1 - (p : ℝ)⁻¹) ≤ 1 / (1 - (p : ℝ)⁻¹) := by
      apply div_le_div_of_nonneg_right _ hden.le
      have : (0 : ℝ) ≤ (p : ℝ)⁻¹ ^ M := by positivity
      linarith
    calc
      4 / (p : ℝ) * ((1 - (p : ℝ)⁻¹ ^ M) / (1 - (p : ℝ)⁻¹))
        ≤ 4 / (p : ℝ) * (1 / (1 - (p : ℝ)⁻¹)) := mul_le_mul_of_nonneg_left hle1 (by positivity)
      _ = 4 / ((p : ℝ) - 1) := by
        have hp0 : (p : ℝ) ≠ 0 := hp_pos.ne'
        have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp
  exact (Finset.sum_le_sum fun k _ => hterm k).trans (hpair.trans hgeom)

/-- Infinite reciprocal-weighted prime-power sum bound:
`∑' k, rootCount N (p^(k+1)) / p^(k+1) ≤ 4 / (p - 1)`. -/
theorem tsum_rootCount_prime_pow_div_le {N p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hN : N ≠ 0) :
    (∑' k : ℕ, (rootCount N (p ^ (k + 1)) : ℝ) / (p : ℝ) ^ (k + 1)) ≤ 4 / ((p : ℝ) - 1) := by
  have hnonneg : ∀ k : ℕ, 0 ≤ (rootCount N (p ^ (k + 1)) : ℝ) / (p : ℝ) ^ (k + 1) :=
    fun _ => by positivity
  have hfin (s : Finset ℕ) :
      ∑ k ∈ s, (rootCount N (p ^ (k + 1)) : ℝ) / (p : ℝ) ^ (k + 1) ≤ 4 / ((p : ℝ) - 1) := by
    let K := s.sup id + 1
    have hsub : s.image (· + 1) ⊆ Finset.Icc 1 K := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_Icc.mpr ⟨by omega, Nat.add_le_add_right (Finset.le_sup (f := id) hk) 1⟩
    calc
      ∑ k ∈ s, (rootCount N (p ^ (k + 1)) : ℝ) / (p : ℝ) ^ (k + 1)
        = ∑ m ∈ s.image (· + 1), (rootCount N (p ^ m) : ℝ) / (p : ℝ) ^ m := by
          rw [Finset.sum_image (fun _ _ _ _ h => Nat.succ.inj h)]
      _ ≤ ∑ m ∈ Finset.Icc 1 K, (rootCount N (p ^ m) : ℝ) / (p : ℝ) ^ m :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ 4 / ((p : ℝ) - 1) := sum_rootCount_prime_pow_div_le hp hp2 hN K
  exact Real.tsum_le_of_sum_le hnonneg hfin

/-! ### Section 4: Elementary divisor-sum bound and upper class number bound -/

/-- For every `m ≠ 0`, `2 ^ ω(m) ≤ d(m)`. -/
theorem two_pow_primeFactors_le_card_divisors {m : ℕ} (hm : m ≠ 0) :
    2 ^ m.primeFactors.card ≤ m.divisors.card := by
  rw [← Finset.card_powerset]
  refine Finset.card_le_card_of_injOn (fun S => ∏ p ∈ S, p) ?_ ?_
  · intro S hS
    have hsub : S ⊆ m.primeFactors := Finset.mem_powerset.mp hS
    refine Nat.mem_divisors.mpr ⟨?_, hm⟩
    have hcop : (S : Set ℕ).Pairwise (Function.onFun IsCoprime (fun p : ℕ => (p : ℤ))) := by
      intro p hp q hq hpq
      exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors (hsub hp))
        (Nat.prime_of_mem_primeFactors (hsub hq))).mpr hpq).isCoprime
    have hdvdZ := Finset.prod_dvd_of_coprime hcop fun p hp =>
      Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mem_primeFactors (hsub hp))
    rw [← Nat.cast_prod] at hdvdZ
    exact Int.natCast_dvd_natCast.mp hdvdZ
  · intro S₁ hS₁ S₂ hS₂ heq
    have h1 := Nat.primeFactors_prod (fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hS₁ hp))
    have h2 := Nat.primeFactors_prod (fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hS₂ hp))
    exact h1.symm.trans ((congrArg Nat.primeFactors heq).trans h2)

/-- Elementary divisor-sum bound: `∑_{1 ≤ m ≤ U} 2^{ω(m)} ≤ U * (1 + log U)` for `U ≥ 1`. -/
theorem sum_two_pow_primeFactors_le {U : ℕ} (_hU : 1 ≤ U) :
    ∑ m ∈ Finset.Icc 1 U, (2 : ℝ) ^ m.primeFactors.card ≤ (U : ℝ) * (1 + Real.log U) := by
  have hnat : ∑ m ∈ Finset.Icc 1 U, 2 ^ m.primeFactors.card ≤ ∑ d ∈ Finset.Icc 1 U, U / d := by
    calc
      ∑ m ∈ Finset.Icc 1 U, 2 ^ m.primeFactors.card
        ≤ ∑ m ∈ Finset.Icc 1 U, m.divisors.card := by
          refine Finset.sum_le_sum fun m hm =>
            two_pow_primeFactors_le_card_divisors (by have := (Finset.mem_Icc.mp hm).1; omega)
      _ = ∑ m ∈ Finset.Icc 1 U, ∑ d ∈ Finset.Icc 1 U, if d ∣ m then 1 else 0 := by
          refine Finset.sum_congr rfl fun m hm => ?_
          obtain ⟨hm1, hmU⟩ := Finset.mem_Icc.mp hm
          rw [← Finset.card_filter]
          congr 1
          ext d
          simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
          constructor
          · rintro ⟨hdvd, _⟩
            have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hm1
            exact ⟨⟨hdpos, (Nat.le_of_dvd hm1 hdvd).trans hmU⟩, hdvd⟩
          · rintro ⟨⟨_, _⟩, hdvd⟩
            exact ⟨hdvd, by omega⟩
      _ = ∑ d ∈ Finset.Icc 1 U, ∑ m ∈ Finset.Icc 1 U, if d ∣ m then 1 else 0 := Finset.sum_comm
      _ = ∑ d ∈ Finset.Icc 1 U, U / d := by
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [← Finset.card_filter]
          have hIoc : Finset.Icc 1 U = Finset.Ioc 0 U := by ext x; simp; omega
          rw [hIoc, Nat.Ioc_filter_dvd_card_eq_div]
  have hcast : ∑ m ∈ Finset.Icc 1 U, (2 : ℝ) ^ m.primeFactors.card ≤
      ∑ d ∈ Finset.Icc 1 U, ((U / d : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hdiv : ∑ d ∈ Finset.Icc 1 U, ((U / d : ℕ) : ℝ) ≤ (U : ℝ) * (harmonic U : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    rw [← div_eq_mul_inv, le_div_iff₀ hdpos]
    exact_mod_cast Nat.div_mul_le_self U d
  have hharm : (harmonic U : ℝ) ≤ 1 + Real.log U := harmonic_le_one_add_log U
  exact hcast.trans (hdiv.trans (mul_le_mul_of_nonneg_left hharm (Nat.cast_nonneg U)))

/-- Upper class number bound in product form for discriminant `-8 * N`. -/
theorem reducedForms_card_le_product {N : ℕ} (hN : Odd N) :
    ((ReducedForms N).card : ℝ) ≤
      2 * Real.sqrt N * (1 + Real.log (2 * N)) *
        ∏ p ∈ N.primeFactors, (1 + 4 / ((p : ℝ) - 1)) := by
  have hNpos : 0 < N := by rcases hN with ⟨k, rfl⟩; omega
  have hNne : N ≠ 0 := hNpos.ne'
  set U := Nat.sqrt (8 * N / 3)
  have hU1 : 1 ≤ U := by
    apply Nat.le_sqrt.mpr
    omega
  let smoothPart (A : ℕ) : ℕ := ∏ p ∈ N.primeFactors, p ^ (A.factorization p)
  let coprimePart (A : ℕ) : ℕ := A / smoothPart A
  have hsmooth_dvd (A : ℕ) : smoothPart A ∣ A := by
    dsimp only [smoothPart]
    have hcop : (N.primeFactors : Set ℕ).Pairwise
        (Function.onFun IsCoprime fun p => ((p ^ A.factorization p : ℕ) : ℤ)) := by
      intro p hp q hq hpq
      exact (((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).mpr hpq).pow _ _).isCoprime
    have hdvdZ := Finset.prod_dvd_of_coprime hcop fun p _ =>
      Int.natCast_dvd_natCast.mpr (Nat.ordProj_dvd A p)
    rw [← Nat.cast_prod] at hdvdZ
    exact Int.natCast_dvd_natCast.mp hdvdZ
  have hsmooth_pos (A : ℕ) : 0 < smoothPart A := by
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  have hcop_N (A : ℕ) (hA : A ≠ 0) : (coprimePart A).Coprime N := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hpm : p ∣ coprimePart A := hpdvd.trans (Nat.gcd_dvd_left _ _)
    have hpN : p ∣ N := hpdvd.trans (Nat.gcd_dvd_right _ _)
    have hp_mem : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpN, hNne⟩
    have hpw_dvd : p ^ A.factorization p ∣ smoothPart A :=
      Finset.dvd_prod_of_mem (fun q => q ^ A.factorization q) hp_mem
    have hmul : smoothPart A * coprimePart A = A := Nat.mul_div_cancel' (hsmooth_dvd A)
    have hpw1' : p ^ (A.factorization p + 1) ∣ smoothPart A * coprimePart A := by
      rw [pow_succ]
      exact mul_dvd_mul hpw_dvd hpm
    rw [hmul] at hpw1'
    have := (hp.pow_dvd_iff_le_factorization hA).mp hpw1'
    omega
  have hcop_sm (A : ℕ) (hA : A ≠ 0) : (smoothPart A).Coprime (coprimePart A) := by
    apply Nat.Coprime.prod_left
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpN := Nat.dvd_of_mem_primeFactors hp
    have hndvd : ¬ p ∣ coprimePart A := fun h =>
      hprime.not_dvd_one ((hcop_N A hA).gcd_eq_one ▸ Nat.dvd_gcd h hpN)
    exact (hprime.coprime_iff_not_dvd.mpr hndvd).pow_left _
  let SN := (Finset.Icc 1 U).filter (fun a => a.primeFactors ⊆ N.primeFactors)
  have hsmooth_mem (A : ℕ) (hA : A ∈ Finset.Icc 1 U) : smoothPart A ∈ SN := by
    obtain ⟨hA1, hAU⟩ := Finset.mem_Icc.mp hA
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hsmooth_pos A,
      (Nat.le_of_dvd hA1 (hsmooth_dvd A)).trans hAU⟩, ?_⟩
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    obtain ⟨q, hq, hpq⟩ := ((Nat.prime_iff.mp hprime).dvd_finsetProd_iff _).mp hdvd
    have hqprime := Nat.prime_of_mem_primeFactors hq
    have hpeq := (Nat.prime_dvd_prime_iff_eq hprime hqprime).mp (hprime.dvd_of_dvd_pow hpq)
    exact hpeq ▸ hq
  have hsum_split :
      (∑ A ∈ Finset.Icc 1 U, (rootCount N A : ℝ)) ≤
        ∑ a ∈ SN, (rootCount N a : ℝ) * ∑ m ∈ Finset.Icc 1 (U / a), (2 : ℝ) ^ m.primeFactors.card := by
    rw [← Finset.sum_fiberwise_of_maps_to hsmooth_mem]
    refine Finset.sum_le_sum fun a ha => ?_
    rw [Finset.mul_sum]
    have hmaps : ∀ A ∈ (Finset.Icc 1 U).filter (fun A => smoothPart A = a),
        coprimePart A ∈ Finset.Icc 1 (U / a) := by
      intro A hA
      obtain ⟨hAIcc, hAs⟩ := Finset.mem_filter.mp hA
      obtain ⟨hA1, hAU⟩ := Finset.mem_Icc.mp hAIcc
      have hmul : a * coprimePart A = A := by
        rw [← hAs]; exact Nat.mul_div_cancel' (hsmooth_dvd A)
      refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
      · by_contra h0
        have : coprimePart A = 0 := by omega
        rw [this, mul_zero] at hmul; omega
      · exact (Nat.le_div_iff_mul_le (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1).mpr
          (by linarith)
    have hinj : Set.InjOn coprimePart
        ↑((Finset.Icc 1 U).filter (fun A => smoothPart A = a)) := by
      intro A₁ hA₁ A₂ hA₂ heq
      obtain ⟨_, hA₁s⟩ := Finset.mem_filter.mp hA₁
      obtain ⟨_, hA₂s⟩ := Finset.mem_filter.mp hA₂
      have hm1 : a * coprimePart A₁ = A₁ := by
        rw [← hA₁s]; exact Nat.mul_div_cancel' (hsmooth_dvd A₁)
      have hm2 : a * coprimePart A₂ = A₂ := by
        rw [← hA₂s]; exact Nat.mul_div_cancel' (hsmooth_dvd A₂)
      rw [← hm1, ← hm2, heq]
    calc
      ∑ A ∈ (Finset.Icc 1 U).filter (fun A => smoothPart A = a), (rootCount N A : ℝ)
        ≤ ∑ A ∈ (Finset.Icc 1 U).filter (fun A => smoothPart A = a),
            (rootCount N a : ℝ) * (2 : ℝ) ^ (coprimePart A).primeFactors.card := by
          refine Finset.sum_le_sum fun A hA => ?_
          obtain ⟨hAIcc, hAs⟩ := Finset.mem_filter.mp hA
          have hAne : A ≠ 0 := by have := (Finset.mem_Icc.mp hAIcc).1; omega
          have hm : a * coprimePart A = A := by
            rw [← hAs]; exact Nat.mul_div_cancel' (hsmooth_dvd A)
          have hcmne : coprimePart A ≠ 0 := by intro h0; rw [h0, mul_zero] at hm; exact hAne hm.symm
          have hmul_rc : rootCount N A = rootCount N a * rootCount N (coprimePart A) := by
            conv_lhs => rw [← hm]
            exact rootCount_mul_of_coprime (hAs ▸ hcop_sm A hAne)
          rw [hmul_rc, Nat.cast_mul]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact_mod_cast rootCount_coprime_le hN hcmne (hcop_N A hAne)
      _ = ∑ m ∈ ((Finset.Icc 1 U).filter (fun A => smoothPart A = a)).image coprimePart,
            (rootCount N a : ℝ) * (2 : ℝ) ^ m.primeFactors.card := by
          rw [Finset.sum_image hinj]
      _ ≤ ∑ m ∈ Finset.Icc 1 (U / a), (rootCount N a : ℝ) * (2 : ℝ) ^ m.primeFactors.card := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          intro m hm
          obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hm
          exact hmaps A hA
  have hsum_inner :
      ∑ a ∈ SN, (rootCount N a : ℝ) * ∑ m ∈ Finset.Icc 1 (U / a), (2 : ℝ) ^ m.primeFactors.card ≤
        (U : ℝ) * (1 + Real.log U) * ∑ a ∈ SN, (rootCount N a : ℝ) / (a : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a ha => ?_
    obtain ⟨ha1, haU⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1
    have hUa1 : 1 ≤ U / a := Nat.div_pos haU ha1
    have hinner := sum_two_pow_primeFactors_le hUa1
    have hUa_le : ((U / a : ℕ) : ℝ) ≤ (U : ℝ) / (a : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast ha1 : (0 : ℝ) < a)]
      exact_mod_cast Nat.div_mul_le_self U a
    have hlog_le : Real.log ((U / a : ℕ) : ℝ) ≤ Real.log U :=
      Real.log_le_log (by exact_mod_cast hUa1) (by exact_mod_cast Nat.div_le_self U a)
    calc
      (rootCount N a : ℝ) * ∑ m ∈ Finset.Icc 1 (U / a), (2 : ℝ) ^ m.primeFactors.card
        ≤ (rootCount N a : ℝ) * (((U / a : ℕ) : ℝ) * (1 + Real.log ((U / a : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg _)
      _ ≤ (rootCount N a : ℝ) * (((U : ℝ) / (a : ℝ)) * (1 + Real.log U)) := by
          gcongr
      _ = (U : ℝ) * (1 + Real.log U) * ((rootCount N a : ℝ) / (a : ℝ)) := by ring
  have hsum_smooth :
      ∑ a ∈ SN, (rootCount N a : ℝ) / (a : ℝ) ≤
        ∏ p ∈ N.primeFactors, (1 + 4 / ((p : ℝ) - 1)) := by
    let E := Finset.pi N.primeFactors (fun _ => Finset.range (U + 1))
    let eval (e : ∀ p ∈ N.primeFactors, ℕ) : ℕ :=
      ∏ p ∈ N.primeFactors.attach, p.1 ^ e p.1 p.2
    have hSN_sub : SN ⊆ E.image eval := by
      intro a ha
      obtain ⟨haI, hapf⟩ := Finset.mem_filter.mp ha
      obtain ⟨ha1, haU⟩ := Finset.mem_Icc.mp haI
      have hane : a ≠ 0 := by omega
      refine Finset.mem_image.mpr ⟨fun p _ => a.factorization p, ?_, ?_⟩
      · refine Finset.mem_pi.mpr fun p hp => Finset.mem_range.mpr ?_
        have hprime := Nat.prime_of_mem_primeFactors hp
        have hpow_le : p ^ a.factorization p ≤ a := Nat.le_of_dvd ha1 (Nat.ordProj_dvd a p)
        have hlt : a.factorization p < 2 ^ a.factorization p := Nat.lt_two_pow_self
        have h2p : 2 ^ a.factorization p ≤ p ^ a.factorization p :=
          Nat.pow_le_pow_left hprime.two_le _
        omega
      · dsimp only [eval]
        rw [Finset.prod_attach N.primeFactors (fun p => p ^ a.factorization p)]
        have hsup : a.factorization.support ⊆ N.primeFactors := by
          rw [Nat.support_factorization]; exact hapf
        rw [← Finset.prod_subset hsup (fun p _ hp => by
          rw [Finsupp.notMem_support_iff.mp hp, pow_zero])]
        exact Nat.prod_factorization_pow_eq_self hane
    have hsum_eval :
        ∑ a ∈ SN, (rootCount N a : ℝ) / (a : ℝ) ≤
          ∑ e ∈ E, (rootCount N (eval e) : ℝ) / (eval e : ℝ) := by
      calc
        ∑ a ∈ SN, (rootCount N a : ℝ) / (a : ℝ)
          ≤ ∑ a ∈ E.image eval, (rootCount N a : ℝ) / (a : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hSN_sub (fun _ _ _ => by positivity)
        _ ≤ ∑ e ∈ E, (rootCount N (eval e) : ℝ) / (eval e : ℝ) :=
            Finset.sum_image_le_of_nonneg (fun _ _ => by positivity)
    have hterm_prod (e : ∀ p ∈ N.primeFactors, ℕ) :
        (rootCount N (eval e) : ℝ) / (eval e : ℝ) =
          ∏ p ∈ N.primeFactors.attach, (rootCount N (p.1 ^ e p.1 p.2) : ℝ) / (p.1 : ℝ) ^ e p.1 p.2 := by
      dsimp only [eval]
      have hcop : (N.primeFactors.attach : Set {x // x ∈ N.primeFactors}).Pairwise fun p q =>
          (p.1 ^ e p.1 p.2).Coprime (q.1 ^ e q.1 q.2) := by
        intro p _ q _ hpq
        have hne : p.1 ≠ q.1 := fun h => hpq (Subtype.ext h)
        exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors p.2)
          (Nat.prime_of_mem_primeFactors q.2)).mpr hne).pow _ _
      rw [rootCount_finset_prod N N.primeFactors.attach _ hcop, Nat.cast_prod, Nat.cast_prod,
        ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun p _ => by simp
    have hprod_expand :
        ∑ e ∈ E, (rootCount N (eval e) : ℝ) / (eval e : ℝ) =
          ∏ p ∈ N.primeFactors, ∑ k ∈ Finset.range (U + 1), (rootCount N (p ^ k) : ℝ) / (p : ℝ) ^ k := by
      rw [Finset.sum_congr rfl (fun e _ => hterm_prod e), Finset.prod_sum]
    rw [hprod_expand] at hsum_eval
    refine hsum_eval.trans ?_
    refine Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun _ _ => by positivity) fun p hp => ?_
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      intro h2
      have h2N : 2 ∣ N := h2 ▸ Nat.dvd_of_mem_primeFactors hp
      rcases hN with ⟨k, rfl⟩
      omega
    have hsplit : Finset.range (U + 1) = insert 0 (Finset.Icc 1 U) := by
      ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hsplit, Finset.sum_insert (by simp), pow_zero, pow_zero, rootCount_one, Nat.cast_one, div_one]
    have := sum_rootCount_prime_pow_div_le hprime hp2 hNne U
    linarith
  have hU_sq : 3 * U ^ 2 ≤ 8 * N := by
    have hU2 : U ^ 2 ≤ 8 * N / 3 := by simpa [sq] using Nat.sqrt_le (8 * N / 3)
    have := (Nat.le_div_iff_mul_le (by decide : 0 < 3)).mp hU2
    linarith
  have hU_le_sqrt : (U : ℝ) ≤ 2 * Real.sqrt N := by
    have hsq : (U : ℝ) ^ 2 ≤ (2 * Real.sqrt N) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
      have h3R : (3 : ℝ) * (U : ℝ) ^ 2 ≤ 8 * (N : ℝ) := by exact_mod_cast hU_sq
      linarith
    nlinarith [Nat.cast_nonneg (α := ℝ) U, Real.sqrt_nonneg N]
  have hU_le_2N : (U : ℝ) ≤ 2 * (N : ℝ) := by
    have hU2N : U ≤ 2 * N := by nlinarith
    exact_mod_cast hU2N
  have hlog_le : 1 + Real.log U ≤ 1 + Real.log (2 * (N : ℝ)) := by
    have hUpos : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU1
    linarith [Real.log_le_log hUpos hU_le_2N]
  have hprod_nonneg : 0 ≤ ∏ p ∈ N.primeFactors, (1 + 4 / ((p : ℝ) - 1)) := by
    refine Finset.prod_nonneg fun p hp => ?_
    have h1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  have hmain : ((ReducedForms N).card : ℝ) ≤
      (U : ℝ) * (1 + Real.log U) * ∏ p ∈ N.primeFactors, (1 + 4 / ((p : ℝ) - 1)) := by
    have h0 : ((ReducedForms N).card : ℝ) ≤ ∑ A ∈ Finset.Icc 1 U, (rootCount N A : ℝ) := by
      exact_mod_cast reducedForms_card_le_sum_rootCount N
    exact h0.trans ((hsum_split.trans hsum_inner).trans
      (mul_le_mul_of_nonneg_left hsum_smooth (mul_nonneg (Nat.cast_nonneg U)
        (by linarith [Real.log_nonneg (by exact_mod_cast hU1 : (1 : ℝ) ≤ U)]))))
  refine hmain.trans ?_
  have hlogU_nonneg : 0 ≤ 1 + Real.log U := by
    linarith [Real.log_nonneg (by exact_mod_cast hU1 : (1 : ℝ) ≤ U)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hU_le_sqrt hlog_le hlogU_nonneg (by positivity)) hprod_nonneg

/-- Bound the local product `∏_{p ∣ N} (1 + 4 / (p - 1))` by a power of `1 + log (2 * N)`. -/
theorem prod_local_factor_le_log_pow {N : ℕ} (hN : Odd N) :
    ∏ p ∈ N.primeFactors, (1 + 4 / ((p : ℝ) - 1)) ≤
      Real.exp 18 * (1 + Real.log (2 * N)) ^ 6 := by
  have hNpos : 0 < N := by rcases hN with ⟨k, rfl⟩; omega
  by_cases hN1 : N = 1
  · subst hN1
    simp only [Nat.primeFactors_one, Finset.prod_empty, Nat.cast_one, mul_one]
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h1 : (1 : ℝ) ≤ (1 + Real.log 2) ^ 6 := one_le_pow₀ (by linarith)
    have he : (1 : ℝ) ≤ Real.exp 18 := Real.one_le_exp (by norm_num)
    nlinarith
  have hN3 : 3 ≤ N := by
    rcases hN with ⟨k, rfl⟩
    omega
  set X : ℝ := Real.log (2 * (N : ℝ))
  have hX1 : 1 ≤ X := by
    dsimp only [X]
    rw [Real.le_log_iff_exp_le (by positivity)]
    have hN3R : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    linarith [Real.exp_one_lt_d9]
  have hXpos : 0 < X := by linarith
  have hprod_exp :
      ∏ p ∈ N.primeFactors, (1 + 4 / ((p : ℝ) - 1)) ≤
        Real.exp (6 * ∑ p ∈ N.primeFactors, (p : ℝ)⁻¹) := by
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod (fun p hp => ?_) fun p hp => ?_
    · have h1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
      have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity
    · have hprime := Nat.prime_of_mem_primeFactors hp
      have hp2 : p ≠ 2 := by
        intro h2
        have h2N : 2 ∣ N := h2 ▸ Nat.dvd_of_mem_primeFactors hp
        rcases hN with ⟨k, rfl⟩; omega
      have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
        have := hprime.two_le
        exact_mod_cast (show 3 ≤ p by omega)
      have hstep : 4 / ((p : ℝ) - 1) ≤ 6 * (p : ℝ)⁻¹ := by
        rw [← div_eq_mul_inv, div_le_div_iff₀ (by linarith) (by linarith)]
        linarith
      linarith [Real.add_one_le_exp (6 * (p : ℝ)⁻¹)]
  let P_lo := N.primeFactors.filter (fun p => p ≤ ⌊X⌋₊)
  let P_hi := N.primeFactors.filter (fun p => ¬ p ≤ ⌊X⌋₊)
  have hsplit : ∑ p ∈ N.primeFactors, (p : ℝ)⁻¹ =
      (∑ p ∈ P_lo, (p : ℝ)⁻¹) + (∑ p ∈ P_hi, (p : ℝ)⁻¹) :=
    (Finset.sum_filter_add_sum_filter_not N.primeFactors (fun p => p ≤ ⌊X⌋₊) _).symm
  have hlo : ∑ p ∈ P_lo, (p : ℝ)⁻¹ ≤ 1 + Real.log X := by
    have hsub : P_lo ⊆ Finset.Icc 1 ⌊X⌋₊ := by
      intro p hp
      obtain ⟨hpf, hple⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hpf).pos, hple⟩
    have hH := harmonic_floor_le_one_add_log X hX1
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hH
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans hH
  have hcard_pf : (N.primeFactors.card : ℝ) ≤ X / Real.log 2 := by
    have hpow : (2 : ℕ) ^ N.primeFactors.card ≤ N := by
      calc
        2 ^ N.primeFactors.card = ∏ _p ∈ N.primeFactors, 2 := by simp
        _ ≤ ∏ p ∈ N.primeFactors, p :=
          Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
        _ ≤ N := Nat.le_of_dvd hNpos (Nat.prod_primeFactors_dvd N)
    have hpowR : (2 : ℝ) ^ N.primeFactors.card ≤ 2 * (N : ℝ) := by
      have : (2 : ℝ) ^ N.primeFactors.card ≤ (N : ℝ) := by exact_mod_cast hpow
      linarith
    have hlog := Real.log_le_log (by positivity) hpowR
    rw [Real.log_pow] at hlog
    exact (le_div_iff₀ (Real.log_pos (by norm_num))).mpr hlog
  have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have hsq : Real.exp (1 / 2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
      linarith [Real.exp_one_lt_d9]
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  have hhi : ∑ p ∈ P_hi, (p : ℝ)⁻¹ ≤ 2 := by
    have hterm (p : ℕ) (hp : p ∈ P_hi) : (p : ℝ)⁻¹ ≤ X⁻¹ := by
      have hgt : ⌊X⌋₊ < p := Nat.lt_of_not_ge (Finset.mem_filter.mp hp).2
      have hXlt : X < (p : ℝ) := (Nat.lt_floor_add_one X).trans_le (by exact_mod_cast hgt)
      exact (inv_le_inv₀ (hXpos.trans hXlt) hXpos).mpr hXlt.le
    calc
      ∑ p ∈ P_hi, (p : ℝ)⁻¹
        ≤ ∑ _p ∈ P_hi, X⁻¹ := Finset.sum_le_sum hterm
      _ = (P_hi.card : ℝ) * X⁻¹ := by simp
      _ ≤ (N.primeFactors.card : ℝ) * X⁻¹ := by
          gcongr
          exact Finset.filter_subset _ _
      _ ≤ (X / Real.log 2) * X⁻¹ := by gcongr
      _ = (Real.log 2)⁻¹ := by field_simp [hXpos.ne']
      _ ≤ 2 := by
          rw [inv_le_comm₀ (Real.log_pos (by norm_num)) (by norm_num)]
          linarith
  have hsum_le : 6 * ∑ p ∈ N.primeFactors, (p : ℝ)⁻¹ ≤ 18 + 6 * Real.log X := by
    rw [hsplit]
    linarith
  calc
    ∏ p ∈ N.primeFactors, (1 + 4 / ((p : ℝ) - 1))
      ≤ Real.exp (6 * ∑ p ∈ N.primeFactors, (p : ℝ)⁻¹) := hprod_exp
    _ ≤ Real.exp (18 + 6 * Real.log X) := Real.exp_le_exp.mpr hsum_le
    _ = Real.exp 18 * Real.exp (6 * Real.log X) := Real.exp_add _ _
    _ = Real.exp 18 * X ^ 6 := by
        rw [show (6 : ℝ) * Real.log X = ((6 : ℕ) : ℝ) * Real.log X by norm_num,
          Real.exp_nat_mul, Real.exp_log hXpos]
    _ ≤ Real.exp 18 * (1 + X) ^ 6 := by
        gcongr
        linarith

/-- Explicit polylogarithmic upper bound on the reduced form count:
`(ReducedForms N).card ≤ 2 * e^18 * √N * (1 + log(2N))^7` for every odd `N`. -/
theorem reducedForms_card_le_sqrt_mul_log_pow {N : ℕ} (hN : Odd N) :
    ((ReducedForms N).card : ℝ) ≤
      (2 * Real.exp 18) * Real.sqrt N * (1 + Real.log (2 * N)) ^ 7 := by
  have h1 := reducedForms_card_le_product hN
  have h2 := prod_local_factor_le_log_pow hN
  have hNpos : 0 < N := by rcases hN with ⟨k, rfl⟩; omega
  have hlog0 : 0 ≤ 1 + Real.log (2 * (N : ℝ)) := by
    have : (1 : ℝ) ≤ 2 * (N : ℝ) := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
      linarith
    linarith [Real.log_nonneg this]
  calc
    ((ReducedForms N).card : ℝ)
      ≤ 2 * Real.sqrt N * (1 + Real.log (2 * N)) *
          (Real.exp 18 * (1 + Real.log (2 * N)) ^ 6) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = (2 * Real.exp 18) * Real.sqrt N * (1 + Real.log (2 * N)) ^ 7 := by ring

/-! ### Section 5: Split primes, quadratic character mod `8 * N`, and lower class number bound -/

/-- Every odd prime `p ∤ N` with `p^2 < 2 * N` and `legendreSym p (-2 * N) = 1`
produces a canonical primitive strictly reduced form `(p, b, C) ∈ ReducedForms N`. -/
theorem exists_reducedForm_of_legendreSym_eq_one {N p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hndvd : ¬ p ∣ N) (hp_small : p ^ 2 < 2 * N)
    (hleg : legendreSym p (-2 * (N : ℤ)) = 1) :
    ∃ (b : ℤ) (C : ℕ), (p, b, C) ∈ ReducedForms N := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  have hjac : jacobiSym (-2 * (N : ℤ)) p = 1 := by
    rwa [← jacobiSym.legendreSym.to_jacobiSym]
  obtain ⟨r, hr⟩ := ZMod.isSquare_of_jacobiSym_eq_one hjac
  have hr2 : r ^ 2 = ((-2 * (N : ℤ) : ℤ) : ZMod p) := by
    rw [sq, ← hr]
  let b : ℤ := if 2 * r.val ≤ p then (r.val : ℤ) else (r.val : ℤ) - (p : ℤ)
  have hb_bounds : -(p : ℤ) < 2 * b ∧ 2 * b ≤ (p : ℤ) := by
    dsimp only [b]
    have hlt := r.val_lt
    split_ifs <;> omega
  have hb_cast : (b : ZMod p) = r := by
    dsimp only [b]
    split_ifs <;> simp
  have hdivZ : (p : ℤ) ∣ b ^ 2 + 2 * (N : ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    rw [hb_cast, hr2]
    push_cast
    ring
  have hdivN : p ∣ b.natAbs ^ 2 + 2 * N := by
    have hZ : (p : ℤ) ∣ ((b.natAbs ^ 2 + 2 * N : ℕ) : ℤ) := by
      push_cast
      rw [sq_abs]
      exact hdivZ
    exact_mod_cast hZ
  let C : ℕ := (b.natAbs ^ 2 + 2 * N) / p
  have hpC : p * C = b.natAbs ^ 2 + 2 * N := Nat.mul_div_cancel' hdivN
  have hdisc : (p : ℤ) * (C : ℤ) - b ^ 2 = 2 * (N : ℤ) := by
    have hZ : (p : ℤ) * (C : ℤ) = (b.natAbs : ℤ) ^ 2 + 2 * (N : ℤ) := by exact_mod_cast hpC
    rw [Int.natAbs_sq] at hZ
    linarith
  have hp_lt_C : p < C := by
    have hlt : p * p < p * C := by
      rw [hpC, ← sq]
      omega
    exact (Nat.mul_lt_mul_left hp.pos).mp hlt
  have hprim : Nat.gcd (Nat.gcd p (2 * b.natAbs)) C = 1 := by
    set g := Nat.gcd (Nat.gcd p (2 * b.natAbs)) C
    have hgp : g ∣ p := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
    rcases (Nat.dvd_prime hp).mp hgp with hg1 | hgp_eq
    · exact hg1
    · exfalso
      have hp2b : p ∣ 2 * b.natAbs := hgp_eq ▸ (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
      have hpb : p ∣ b.natAbs := (hp.dvd_mul.mp hp2b).resolve_left
        (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))
      have hpb2 : p ∣ b.natAbs ^ 2 := dvd_pow hpb (by decide)
      have hp2N : p ∣ 2 * N := by
        have hsum : p ∣ b.natAbs ^ 2 + 2 * N := hpC ▸ dvd_mul_right p C
        exact (Nat.dvd_add_right hpb2).mp hsum
      have hpN : p ∣ N := (hp.dvd_mul.mp hp2N).resolve_left
        (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))
      exact hndvd hpN
  refine ⟨b, C, mem_reducedForms.mpr ?_⟩
  exact ⟨hdisc, hp.pos, hb_bounds.1, hb_bounds.2, hp_lt_C.le, fun heq => (hp_lt_C.ne heq).elim, hprim⟩

/-- The 2-part of the quadratic splitting character for `-2 * N`:
`χ₈'` when `N ≡ 1 (mod 4)` and `χ₈` when `N ≡ 3 (mod 4)`. -/
def twoChar (N : ℕ) : DirichletCharacter ℂ 8 where
  toFun a := if N % 4 = 1 then (ZMod.χ₈' a : ℂ) else (ZMod.χ₈ a : ℂ)
  map_one' := by split_ifs <;> simp
  map_mul' a b := by
    split_ifs <;> simp [map_mul]
  map_nonunit' a ha := by
    split_ifs <;> simp [MulChar.map_nonunit _ ha]

theorem twoChar_apply (N : ℕ) (a : ZMod 8) :
    twoChar N a = if N % 4 = 1 then (ZMod.χ₈' a : ℂ) else (ZMod.χ₈ a : ℂ) := rfl

/-- The odd-part Jacobi Dirichlet character modulo `N`. -/
def jacobiChar (N : ℕ) [NeZero N] : DirichletCharacter ℂ N where
  toFun a := (jacobiSym (a.val : ℤ) N : ℂ)
  map_one' := by
    have hmod : ((1 : ZMod N).val : ℤ) % (N : ℤ) = (1 : ℤ) % (N : ℤ) := by
      have h1 : (1 : ZMod N).val = 1 % N := ZMod.val_one_eq_one_mod N
      rw [h1, ← Int.natCast_one, ← Int.natCast_emod, ← Int.natCast_emod, Nat.mod_mod]
    rw [jacobiSym.mod_left' hmod, jacobiSym.one_left]
    simp
  map_mul' a b := by
    have hmod : (((a * b).val : ℤ) % (N : ℤ)) = ((a.val : ℤ) * (b.val : ℤ)) % (N : ℤ) := by
      rw [← Int.natCast_mul, ← Int.natCast_emod, ← Int.natCast_emod]
      congr 1
      rw [ZMod.val_mul]
      exact Nat.mod_mod _ N
    rw [jacobiSym.mod_left' hmod, jacobiSym.mul_left, Int.cast_mul]
  map_nonunit' a ha := by
    have hncop : ¬ a.val.Coprime N := fun h => ha (by
      rw [← ZMod.natCast_zmod_val a]
      exact (ZMod.isUnit_iff_coprime a.val N).mpr h)
    have hgcd : (a.val : ℤ).gcd N ≠ 1 := by
      rwa [Int.gcd_natCast_natCast]
    rw [jacobiSym.eq_zero_iff.mpr ⟨NeZero.ne N, hgcd⟩, Int.cast_zero]

theorem jacobiChar_apply_def (N : ℕ) [NeZero N] (a : ZMod N) :
    jacobiChar N a = (jacobiSym (a.val : ℤ) N : ℂ) := rfl

/-- The quadratic Dirichlet character modulo `8 * N` giving the splitting of `-2 * N`. -/
noncomputable def splitChar (N : ℕ) [NeZero N] : DirichletCharacter ℂ (8 * N) :=
  DirichletCharacter.changeLevel (dvd_mul_right 8 N) (twoChar N) *
  DirichletCharacter.changeLevel (dvd_mul_left N 8) (jacobiChar N)

/-- For every odd `N`, `splitChar N` is nonprincipal (its value at `u ≡ 5 mod 8, u ≡ 1 mod N` is `-1`). -/
theorem splitChar_ne_one {N : ℕ} [NeZero N] (hN : Odd N) : splitChar N ≠ 1 := by
  have hcop : Nat.Coprime 8 N := by
    have h2 : Nat.Coprime 2 N := hN.coprime_two_left
    simpa [show (8 : ℕ) = 2 ^ 3 by decide] using h2.pow_left 3
  let e := ZMod.chineseRemainder hcop
  let u : ZMod (8 * N) := e.symm ((5 : ZMod 8), (1 : ZMod N))
  have hu_unit : IsUnit u := by
    have h5 : IsUnit (5 : ZMod 8) := by decide
    have h1 : IsUnit (1 : ZMod N) := isUnit_one
    have hp : IsUnit ((5 : ZMod 8), (1 : ZMod N)) := Prod.isUnit_iff.mpr ⟨h5, h1⟩
    exact hp.map e.symm.toRingHom
  have heu : e u = ((5 : ZMod 8), (1 : ZMod N)) := e.apply_symm_apply _
  have hcast8 : (ZMod.cast u : ZMod 8) = 5 := by
    have h1 := congrArg Prod.fst heu
    simpa only [e, ZMod.chineseRemainder, RingEquiv.coe_mk, Equiv.coe_fn_mk,
      ZMod.castHom_apply, Prod.fst_zmod_cast] using h1
  have hcastN : (ZMod.cast u : ZMod N) = 1 := by
    have h2 := congrArg Prod.snd heu
    simpa only [e, ZMod.chineseRemainder, RingEquiv.coe_mk, Equiv.coe_fn_mk,
      ZMod.castHom_apply, Prod.snd_zmod_cast] using h2
  intro hEq
  have hval := congrArg (fun χ : DirichletCharacter ℂ (8 * N) => χ u) hEq
  rw [MulChar.one_apply hu_unit] at hval
  have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd (twoChar N) (dvd_mul_right 8 N) hu_unit.unit
  have h2 := DirichletCharacter.changeLevel_eq_cast_of_dvd (jacobiChar N) (dvd_mul_left N 8) hu_unit.unit
  simp only [IsUnit.unit_spec, hcast8, hcastN] at h1 h2
  have htwo5 : twoChar N 5 = -1 := by
    dsimp only [twoChar]
    split_ifs <;> simp [ZMod.χ₈', ZMod.χ₈]
  have hjac1 : jacobiChar N 1 = 1 := map_one (jacobiChar N)
  simp only [splitChar, MulChar.mul_apply, h1, h2, htwo5, hjac1, mul_one] at hval
  norm_num at hval

/-- For odd `N` and any odd prime `p ∤ N`, `splitChar N p = legendreSym p (-2 * N)`. -/
theorem splitChar_apply_prime {N p : ℕ} [NeZero N] (hN : Odd N)
    (hp : p.Prime) (hp2 : p ≠ 2) (hndvd : ¬ p ∣ N) :
    splitChar N (p : ZMod (8 * N)) = (@legendreSym p ⟨hp⟩ (-2 * (N : ℤ)) : ℂ) := by
  have hp_odd : Odd p := hp.odd_of_ne_two hp2
  have hcop_nat : p.Coprime (8 * N) := by
    refine Nat.Coprime.mul_right ?_ (hp.coprime_iff_not_dvd.mpr hndvd)
    simpa [show (8 : ℕ) = 2 ^ 3 by decide] using hp_odd.coprime_two_right.pow_right 3
  have hcop_int : IsCoprime (p : ℤ) ((8 * N : ℕ) : ℤ) := by
    exact_mod_cast hcop_nat.isCoprime
  have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd' (twoChar N) (dvd_mul_right 8 N) hcop_int
  have h2 := DirichletCharacter.changeLevel_eq_cast_of_dvd' (jacobiChar N) (dvd_mul_left N 8) hcop_int
  simp only [Int.cast_natCast] at h1 h2
  have hsc : splitChar N (p : ZMod (8 * N)) = twoChar N (p : ZMod 8) * jacobiChar N (p : ZMod N) := by
    simp only [splitChar, MulChar.mul_apply, h1, h2]
  rw [hsc]
  have hjac_eval : jacobiChar N (p : ZMod N) = (jacobiSym (p : ℤ) N : ℂ) := by
    rw [jacobiChar_apply_def]
    congr 1
    rw [ZMod.val_natCast, jacobiSym.mod_left (p : ℤ) N]
    simp [Int.natCast_emod]
  rw [hjac_eval]
  have : Fact p.Prime := ⟨hp⟩
  rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.mul_left, jacobiSym.at_neg_two hp_odd]
  have hqr : jacobiSym (N : ℤ) p =
      (if N % 4 = 1 then 1 else ZMod.χ₄ (p : ZMod 4)) * jacobiSym (p : ℤ) N := by
    have hNmod : N % 4 = 1 ∨ N % 4 = 3 := by
      rcases hN with ⟨k, rfl⟩; omega
    rcases hNmod with h1 | h3
    · rw [if_pos h1, one_mul]
      exact jacobiSym.quadratic_reciprocity_one_mod_four h1 hp_odd
    · rw [if_neg (by omega)]
      have hqr' := jacobiSym.quadratic_reciprocity hN hp_odd
      rw [hqr', pow_mul]
      have hN2 : (-1 : ℤ) ^ (N / 2) = -1 := ZMod.neg_one_pow_div_two_of_three_mod_four h3
      rw [hN2, ← ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hp_odd)]
  rw [hqr, twoChar_apply]
  have hχ4_sq : (ZMod.χ₄ (p : ZMod 4)) ^ 2 = 1 := by
    have h4 : p % 4 = 1 ∨ p % 4 = 3 := by rcases hp_odd with ⟨k, rfl⟩; omega
    rcases h4 with h | h
    · rw [ZMod.χ₄_nat_one_mod_four h]; norm_num
    · rw [ZMod.χ₄_nat_three_mod_four h]; norm_num
  split_ifs with hN1
  · push_cast; ring
  · have h8 : ZMod.χ₈' (p : ZMod 8) = ZMod.χ₄ (p : ZMod 4) * ZMod.χ₈ (p : ZMod 8) := by
      simpa using ZMod.χ₈'_int_eq_χ₄_mul_χ₈ (p : ℤ)
    rw [h8]
    have hsimp : ZMod.χ₄ (p : ZMod 4) * ZMod.χ₈ (p : ZMod 8) * (ZMod.χ₄ (p : ZMod 4) * jacobiSym (p : ℤ) N) =
        ZMod.χ₈ (p : ZMod 8) * jacobiSym (p : ℤ) N := by
      calc
        _ = (ZMod.χ₄ (p : ZMod 4)) ^ 2 * (ZMod.χ₈ (p : ZMod 8) * jacobiSym (p : ℤ) N) := by ring
        _ = _ := by rw [hχ4_sq, one_mul]
    rw [hsimp, Int.cast_mul]

/-- Auxiliary bound: for odd `N` and `2 ≤ A ≤ B` with `B^2 < 2 * N`, the split primes in `(A, B]`
give a lower bound on `(ReducedForms N).card` via `primeBin A B` and `splitChar N`. -/
private theorem two_mul_reducedForms_ge_primeBin_sub {N A B : ℕ} [NeZero N] (hN : Odd N)
    (hA2 : 2 ≤ A) (hB_small : B ^ 2 < 2 * N) :
    ((Randomized.primeBin A B).card : ℝ) -
        ‖∑ p ∈ Randomized.primeBin A B, splitChar N (p : ZMod (8 * N))‖ -
        (N.primeFactors.card : ℝ) ≤
      2 * ((ReducedForms N).card : ℝ) := by
  let P := Randomized.primeBin A B
  let P_split := P.filter (fun p => ¬ p ∣ N ∧ jacobiSym (-2 * (N : ℤ)) p = 1)
  have hP_odd : ∀ p ∈ P, p ≠ 2 := by
    intro p hp
    have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    omega
  have hsplit_le_RF : P_split.card ≤ (ReducedForms N).card := by
    have hex : ∀ p ∈ P_split, ∃ f ∈ ReducedForms N, f.1 = p := by
      intro p hp
      obtain ⟨hpP, hndvd, hjac⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpIoc, hpPrime⟩ := Finset.mem_filter.mp hpP
      have : Fact p.Prime := ⟨hpPrime⟩
      have hp_small : p ^ 2 < 2 * N :=
        (Nat.pow_le_pow_left (Finset.mem_Ioc.mp hpIoc).2 2).trans_lt hB_small
      have hleg : legendreSym p (-2 * (N : ℤ)) = 1 := by
        rwa [jacobiSym.legendreSym.to_jacobiSym]
      obtain ⟨b, C, hmem⟩ := exists_reducedForm_of_legendreSym_eq_one (hP_odd p hpP) hndvd hp_small hleg
      exact ⟨(p, b, C), hmem, rfl⟩
    choose f hf_mem hf_fst using hex
    refine Finset.card_le_card_of_injOn (fun p => if h : p ∈ P_split then f p h else (0, 0, 0)) ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe] at hp ⊢
      rw [dif_pos hp]
      exact hf_mem p hp
    · intro p₁ hp₁ p₂ hp₂ heq
      dsimp only at heq
      simp only [Finset.mem_coe] at hp₁ hp₂
      rw [dif_pos hp₁, dif_pos hp₂] at heq
      have := congrArg Prod.fst heq
      rwa [hf_fst p₁ hp₁, hf_fst p₂ hp₂] at this
  have hsum_le :
      (∑ p ∈ P, (1 + (splitChar N (p : ZMod (8 * N))).re)) ≤
        2 * (P_split.card : ℝ) + ((P.filter (fun p => p ∣ N)).card : ℝ) := by
    have hterm : ∀ p ∈ P,
        1 + (splitChar N (p : ZMod (8 * N))).re ≤
          (if ¬ p ∣ N ∧ jacobiSym (-2 * (N : ℤ)) p = 1 then (2 : ℝ) else 0) +
          (if p ∣ N then (1 : ℝ) else 0) := by
      intro p hp
      have hpPrime := (Finset.mem_filter.mp hp).2
      have hp2 := hP_odd p hp
      by_cases hdiv : p ∣ N
      · have hnotcop : ¬ IsCoprime (p : ℤ) ((8 * N : ℕ) : ℤ) := by
          intro hcop
          have hp8N : (p : ℤ) ∣ ((8 * N : ℕ) : ℤ) := by
            exact_mod_cast dvd_mul_of_dvd_right hdiv 8
          have h1 := hcop.isUnit_of_dvd' dvd_rfl hp8N
          have habs : |(p : ℤ)| = 1 := Int.isUnit_iff_abs_eq.mp h1
          rw [abs_of_nonneg (Nat.cast_nonneg p)] at habs
          have hp1 : p = 1 := by exact_mod_cast habs
          exact hpPrime.ne_one hp1
        have hzero : splitChar N (p : ZMod (8 * N)) = 0 := by
          have := (DirichletCharacter.apply_eq_zero_iff (splitChar N) (p : ℤ)).mpr hnotcop
          simpa using this
        simp [hdiv, hzero]
      · have hval := splitChar_apply_prime hN hpPrime hp2 hdiv
        have : Fact p.Prime := ⟨hpPrime⟩
        rw [hval, Complex.intCast_re, jacobiSym.legendreSym.to_jacobiSym]
        have hgcd : (-2 * (N : ℤ)).gcd p = 1 := by
          rw [Int.gcd_comm]
          have hcop2N : p.Coprime (2 * N) :=
            (hpPrime.coprime_iff_not_dvd.mpr (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hpPrime Nat.prime_two).mp h))).mul_right
              (hpPrime.coprime_iff_not_dvd.mpr hdiv)
          simpa [Int.gcd, Nat.Coprime, Int.natAbs_mul] using hcop2N
        rcases jacobiSym.eq_one_or_neg_one hgcd with h1 | hm1
        · rw [h1]; norm_num [hdiv]
        · rw [hm1]; norm_num [hdiv]
    calc
      ∑ p ∈ P, (1 + (splitChar N (p : ZMod (8 * N))).re)
        ≤ ∑ p ∈ P, ((if ¬ p ∣ N ∧ jacobiSym (-2 * (N : ℤ)) p = 1 then (2 : ℝ) else 0) +
            (if p ∣ N then (1 : ℝ) else 0)) := Finset.sum_le_sum hterm
      _ = 2 * (P_split.card : ℝ) + ((P.filter (fun p => p ∣ N)).card : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
          simp [P_split, nsmul_eq_mul, mul_comm]
  have hdiv_le : (P.filter (fun p => p ∣ N)).card ≤ N.primeFactors.card := by
    apply Finset.card_le_card
    intro p hp
    obtain ⟨hpP, hdiv⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(Finset.mem_filter.mp hpP).2, hdiv, NeZero.ne N⟩
  have hre : (∑ p ∈ P, (1 + (splitChar N (p : ZMod (8 * N))).re)) =
      (P.card : ℝ) + (∑ p ∈ P, splitChar N (p : ZMod (8 * N))).re := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Complex.re_sum]
  have hnorm : -(‖∑ p ∈ P, splitChar N (p : ZMod (8 * N))‖) ≤
      (∑ p ∈ P, splitChar N (p : ZMod (8 * N))).re := by
    linarith [Complex.abs_re_le_norm (∑ p ∈ P, splitChar N (p : ZMod (8 * N))),
      neg_abs_le (∑ p ∈ P, splitChar N (p : ZMod (8 * N))).re]
  have h1 : (P_split.card : ℝ) ≤ ((ReducedForms N).card : ℝ) := by exact_mod_cast hsplit_le_RF
  have h2 : ((P.filter (fun p => p ∣ N)).card : ℝ) ≤ (N.primeFactors.card : ℝ) := by
    exact_mod_cast hdiv_le
  linarith

/-- Lower class number bound from `DirichletLZerosOnLine`:
there exists `N₀` such that for every odd `N ≥ N₀`,
`(ReducedForms N).card ≥ (1 / 8) * √N / log N`. -/
theorem reducedForms_card_lower_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Odd N →
      (1 / 8 : ℝ) * Real.sqrt N / Real.log N ≤ ((ReducedForms N).card : ℝ) := by
  obtain ⟨K₁, hK₁, hsupply⟩ := Randomized.primeBin_supply_from_critical_line line
  obtain ⟨K₂, hK₂, hchar⟩ := Window.nonprincipal_prime_count_from_critical_line line
  let M_const : ℝ := 1 + K₁ + 2 * K₂
  have hMpos : 0 < M_const := by dsimp only [M_const]; linarith
  let C_big : ℝ := 16 * 49 * (24 : ℝ) ^ 3 * (M_const + 4) + 100
  let N₀ : ℕ := max 10000 ⌈C_big ^ 8⌉₊
  refine ⟨N₀, fun N hNge hNodd => ?_⟩
  have hN10000 : 10000 ≤ N := (le_max_left _ _).trans hNge
  have hNpos : 0 < N := by omega
  have : NeZero N := ⟨hNpos.ne'⟩
  have hNR : (10000 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN10000
  have hNRpos : (0 : ℝ) < (N : ℝ) := by linarith only [hNR]
  have hsqrtN_ge : (100 : ℝ) ≤ Real.sqrt N := by
    have := Real.sqrt_le_sqrt hNR
    rw [show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
    exact this
  have hsqrtN_le : Real.sqrt N ≤ (N : ℝ) := by
    nlinarith only [Real.sq_sqrt hNRpos.le, hsqrtN_ge]
  have hlogN_ge : (2 : ℝ) ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hNRpos]
    have hexp2 : Real.exp 2 ≤ 9 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
      have h3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      nlinarith only [h3, Real.exp_pos 1]
    linarith only [hexp2, hNR]
  have hlogN_pos : 0 < Real.log N := by linarith only [hlogN_ge]
  let A : ℕ := ⌊Real.sqrt N / 4⌋₊
  let B : ℕ := ⌊Real.sqrt N / 2⌋₊
  have hA2 : 2 ≤ A := by
    apply Nat.le_floor
    push_cast
    linarith only [hsqrtN_ge]
  have hAB : A ≤ B := Nat.floor_mono (by linarith only [hsqrtN_ge])
  have hB_le : (B : ℝ) ≤ Real.sqrt N / 2 := Nat.floor_le (by positivity)
  have hA_le : (A : ℝ) ≤ Real.sqrt N / 4 := Nat.floor_le (by positivity)
  have hB_gt : Real.sqrt N / 2 - 1 < (B : ℝ) := by
    linarith only [Nat.lt_floor_add_one (Real.sqrt N / 2)]
  have hB_ge : (49 : ℝ) ≤ (B : ℝ) := by linarith only [hB_gt, hsqrtN_ge]
  have hB_le_N : (B : ℝ) ≤ (N : ℝ) := by linarith only [hB_le, hsqrtN_le]
  have hB_small : B ^ 2 < 2 * N := by
    have hBR : (B : ℝ) ^ 2 < 2 * (N : ℝ) := by
      have hsq : (B : ℝ) ^ 2 ≤ (Real.sqrt N / 2) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg B) hB_le 2
      rw [div_pow, Real.sq_sqrt hNRpos.le] at hsq
      linarith only [hsq, hNRpos]
    exact_mod_cast hBR
  have hlogB_le : Real.log B ≤ Real.log N / 2 := by
    have hBN : (B : ℝ) ≤ Real.sqrt N := by linarith only [hB_le, hsqrtN_ge]
    have h := Real.log_le_log (by linarith only [hB_ge] : (0 : ℝ) < B) hBN
    rwa [Real.log_sqrt hNRpos.le] at h
  have hsup := hsupply A B hA2 hAB
  have : NeZero (8 * N) := ⟨by omega⟩
  have hAr : (2 : ℝ) ≤ A := by exact_mod_cast hA2
  have hABr : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hBr : (2 : ℝ) ≤ B := hAr.trans hABr
  have hch_A := hchar (8 * N) (splitChar N) (splitChar_ne_one hNodd) B A hAr hABr
  have hch_B := hchar (8 * N) (splitChar N) (splitChar_ne_one hNodd) B B hBr le_rfl
  rw [← Real.sqrt_eq_rpow] at hch_A hch_B
  have hchar_sum :
      ‖∑ p ∈ Randomized.primeBin A B, splitChar N (p : ZMod (8 * N))‖ ≤
        2 * K₂ * (1 + Real.log (3 * ((8 * N : ℕ) : ℝ) * B)) ^ 2 * Real.sqrt B := by
    have heq : (∑ p ∈ Randomized.primeBin A B, splitChar N (p : ZMod (8 * N))) =
        Window.primeCount (splitChar N) B - Window.primeCount (splitChar N) A := by
      have hdisj : Disjoint (Finset.Icc 0 A) (Finset.Ioc A B) := Finset.disjoint_left.mpr (by
        intro p hp hq
        exact (not_lt_of_ge (Finset.mem_Icc.mp hp).2) (Finset.mem_Ioc.mp hq).1)
      have hunion : Finset.Icc 0 A ∪ Finset.Ioc A B = Finset.Icc 0 B := by
        ext p; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
      unfold Randomized.primeBin Window.primeCount
      simp only [Nat.floor_natCast, Finset.sum_filter]
      rw [← hunion, Finset.sum_union hdisj, add_sub_cancel_left]
    rw [heq]
    have hsc : K₂ * (1 + Real.log (3 * ((8 * N : ℕ) : ℝ) * B)) ^ 2 * Real.sqrt A ≤
        K₂ * (1 + Real.log (3 * ((8 * N : ℕ) : ℝ) * B)) ^ 2 * Real.sqrt B := by
      gcongr
    calc
      ‖Window.primeCount (splitChar N) B - Window.primeCount (splitChar N) A‖
        ≤ ‖Window.primeCount (splitChar N) B‖ + ‖Window.primeCount (splitChar N) A‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add hch_B (hch_A.trans hsc)
      _ = _ := by ring
  have hpf_le : (N.primeFactors.card : ℝ) ≤ 2 * Real.log N := by
    have hpow : (2 : ℕ) ^ N.primeFactors.card ≤ N := by
      calc
        2 ^ N.primeFactors.card = ∏ _p ∈ N.primeFactors, 2 := by simp
        _ ≤ ∏ p ∈ N.primeFactors, p :=
          Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
        _ ≤ N := Nat.le_of_dvd hNpos (Nat.prod_primeFactors_dvd N)
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ N.primeFactors.card)
      (by exact_mod_cast hpow : (2 : ℝ) ^ N.primeFactors.card ≤ N)
    rw [Real.log_pow] at hlog
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have hsq : Real.exp (1 / 2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ 2 := by
        rw [← Real.exp_nat_mul]; norm_num; linarith [Real.exp_one_lt_d9]
      nlinarith only [hsq, Real.exp_pos (1 / 2 : ℝ)]
    nlinarith only [hlog, hlog2, Nat.cast_nonneg (α := ℝ) N.primeFactors.card]
  have hcore := two_mul_reducedForms_ge_primeBin_sub hNodd hA2 hB_small
  have hlog3B : 1 + Real.log (3 * (B : ℝ)) ≤ 7 * Real.log N := by
    have h3B : 3 * (B : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hB_le_N, hNR]
    have h1 : Real.log (3 * (B : ℝ)) ≤ 2 * Real.log N := by
      calc
        Real.log (3 * (B : ℝ)) ≤ Real.log ((N : ℝ) ^ 2) := Real.log_le_log (by linarith only [hB_ge]) h3B
        _ = 2 * Real.log N := by rw [Real.log_pow]; norm_num
    linarith only [h1, hlogN_ge]
  have hlog24NB : 1 + Real.log (3 * ((8 * N : ℕ) : ℝ) * B) ≤ 7 * Real.log N := by
    have hle : 3 * ((8 * N : ℕ) : ℝ) * B ≤ (N : ℝ) ^ 3 := by
      push_cast
      have hBN : (B : ℝ) * N ≤ (N : ℝ) * N := mul_le_mul_of_nonneg_right hB_le_N hNRpos.le
      have hN24 : ((N : ℝ) * N) * 24 ≤ ((N : ℝ) * N) * N :=
        mul_le_mul_of_nonneg_left (by linarith only [hNR] : (24 : ℝ) ≤ N) (by positivity)
      nlinarith only [hBN, hN24]
    have hpos24 : 0 < 3 * ((8 * N : ℕ) : ℝ) * B := by
      push_cast; positivity
    have h1 : Real.log (3 * ((8 * N : ℕ) : ℝ) * B) ≤ 3 * Real.log N := by
      calc
        Real.log (3 * ((8 * N : ℕ) : ℝ) * B) ≤ Real.log ((N : ℝ) ^ 3) :=
          Real.log_le_log hpos24 hle
        _ = 3 * Real.log N := by rw [Real.log_pow]; norm_num
    linarith only [h1, hlogN_ge]
  have hsqrtB : Real.sqrt B ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      Real.sqrt B ≤ Real.sqrt (Real.sqrt N) := Real.sqrt_le_sqrt (by linarith only [hB_le, hsqrtN_ge])
      _ = (N : ℝ) ^ (1 / 4 : ℝ) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hNRpos.le]
        norm_num
  have hlogN_rpow : (Real.log N) ^ 3 ≤ (24 : ℝ) ^ 3 * (N : ℝ) ^ (1 / 8 : ℝ) := by
    have hl := Real.log_le_rpow_div hNRpos.le (by norm_num : (0 : ℝ) < 1 / 24)
    have hl' : Real.log N ≤ 24 * (N : ℝ) ^ (1 / 24 : ℝ) := by linarith only [hl]
    have hpow := pow_le_pow_left₀ hlogN_pos.le hl' 3
    rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (1 / 24 : ℝ)) 3,
      ← Real.rpow_mul hNRpos.le, show (1 / 24 : ℝ) * (3 : ℕ) = 1 / 8 by norm_num] at hpow
    exact hpow
  have hCbig_le : C_big ≤ (N : ℝ) ^ (1 / 8 : ℝ) := by
    have hNceil : (⌈C_big ^ 8⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast (le_max_right _ _).trans hNge
    have hCpos : 0 ≤ C_big := by dsimp only [C_big]; positivity
    have hC8 : C_big ^ 8 ≤ (N : ℝ) := (Nat.le_ceil _).trans hNceil
    calc
      C_big = (C_big ^ 8) ^ (1 / 8 : ℝ) := by
        rw [← Real.rpow_natCast C_big 8, ← Real.rpow_mul hCpos]
        norm_num
      _ ≤ (N : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_le_rpow (by positivity) hC8 (by norm_num)
  have hN14_eq : (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) = Real.sqrt N := by
    rw [← Real.rpow_add hNRpos, Real.sqrt_eq_rpow]
    norm_num
  have hN18_sq : (N : ℝ) ^ (1 / 8 : ℝ) * (N : ℝ) ^ (1 / 8 : ℝ) = (N : ℝ) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hNRpos]
    norm_num
  have herr_small :
      (49 * (K₁ + 2 * K₂) * (Real.log N) ^ 2 * (N : ℝ) ^ (1 / 4 : ℝ) + 2 * Real.log N) * Real.log N ≤
        Real.sqrt N / 16 := by
    have hlog2_le : 2 * (Real.log N) ^ 2 ≤ (Real.log N) ^ 3 := by
      have : 0 ≤ (Real.log N) ^ 2 := sq_nonneg _
      nlinarith only [hlogN_ge, this]
    have h1_le_N14 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
      Real.one_le_rpow (by linarith only [hNR]) (by norm_num)
    have hlog3_nonneg : 0 ≤ (Real.log N) ^ 3 := pow_nonneg hlogN_pos.le 3
    have hN14_nonneg : 0 ≤ (N : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hNRpos.le _
    have hterm1 :
        49 * (K₁ + 2 * K₂) * (Real.log N) ^ 2 * (N : ℝ) ^ (1 / 4 : ℝ) * Real.log N ≤
          49 * M_const * (Real.log N) ^ 3 * (N : ℝ) ^ (1 / 4 : ℝ) := by
      have hKM : 49 * (K₁ + 2 * K₂) ≤ 49 * M_const := by dsimp only [M_const]; linarith
      have hm := mul_le_mul_of_nonneg_right hKM (mul_nonneg hlog3_nonneg hN14_nonneg)
      linarith only [hm]
    have hterm2 :
        2 * Real.log N * Real.log N ≤ 49 * 4 * (Real.log N) ^ 3 * (N : ℝ) ^ (1 / 4 : ℝ) := by
      have hsub : 2 * (Real.log N) ^ 2 ≤ (Real.log N) ^ 3 * (N : ℝ) ^ (1 / 4 : ℝ) :=
        hlog2_le.trans (le_mul_of_one_le_right hlog3_nonneg h1_le_N14)
      have hnonneg : 0 ≤ (Real.log N) ^ 3 * (N : ℝ) ^ (1 / 4 : ℝ) := mul_nonneg hlog3_nonneg hN14_nonneg
      linarith only [hsub, hnonneg]
    have h1 :
        (49 * (K₁ + 2 * K₂) * (Real.log N) ^ 2 * (N : ℝ) ^ (1 / 4 : ℝ) + 2 * Real.log N) * Real.log N ≤
          49 * (M_const + 4) * (Real.log N) ^ 3 * (N : ℝ) ^ (1 / 4 : ℝ) := by
      linarith only [hterm1, hterm2]
    calc
      (49 * (K₁ + 2 * K₂) * (Real.log N) ^ 2 * (N : ℝ) ^ (1 / 4 : ℝ) + 2 * Real.log N) * Real.log N
        ≤ 49 * (M_const + 4) * (Real.log N) ^ 3 * (N : ℝ) ^ (1 / 4 : ℝ) := h1
      _ ≤ 49 * (M_const + 4) * ((24 : ℝ) ^ 3 * (N : ℝ) ^ (1 / 8 : ℝ)) * (N : ℝ) ^ (1 / 4 : ℝ) := by
          gcongr
      _ = (49 * (24 : ℝ) ^ 3 * (M_const + 4)) * ((N : ℝ) ^ (1 / 8 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ)) := by ring
      _ ≤ (C_big / 16) * ((N : ℝ) ^ (1 / 8 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          dsimp only [C_big]; linarith
      _ ≤ ((N : ℝ) ^ (1 / 8 : ℝ) / 16) * ((N : ℝ) ^ (1 / 8 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ)) := by
          gcongr
      _ = ((N : ℝ) ^ (1 / 8 : ℝ) * (N : ℝ) ^ (1 / 8 : ℝ)) * (N : ℝ) ^ (1 / 4 : ℝ) / 16 := by ring
      _ = Real.sqrt N / 16 := by rw [hN18_sq, hN14_eq]
  have hlog3B_sq : (1 + Real.log (3 * (B : ℝ))) ^ 2 ≤ 49 * (Real.log N) ^ 2 := by
    have h0 : 0 ≤ 1 + Real.log (3 * (B : ℝ)) := by
      linarith [Real.log_nonneg (by linarith only [hB_ge] : (1 : ℝ) ≤ 3 * (B : ℝ))]
    have := pow_le_pow_left₀ h0 hlog3B 2
    linarith only [this]
  have hlog24_sq : (1 + Real.log (3 * ((8 * N : ℕ) : ℝ) * B)) ^ 2 ≤ 49 * (Real.log N) ^ 2 := by
    have h0 : 0 ≤ 1 + Real.log (3 * ((8 * N : ℕ) : ℝ) * B) := by
      have : (1 : ℝ) ≤ 3 * ((8 * N : ℕ) : ℝ) * B := by
        push_cast; nlinarith only [hNR, hB_ge]
      linarith [Real.log_nonneg this]
    have := pow_le_pow_left₀ h0 hlog24NB 2
    linarith only [this]
  have hP_card_lower :
      2 * ((B : ℝ) - (A : ℝ) - K₁ * (49 * (Real.log N) ^ 2) * (N : ℝ) ^ (1 / 4 : ℝ)) ≤
        ((Randomized.primeBin A B).card : ℝ) * Real.log N := by
    have h1 : K₁ * (1 + Real.log (3 * (B : ℝ))) ^ 2 * Real.sqrt B ≤
        K₁ * (49 * (Real.log N) ^ 2) * (N : ℝ) ^ (1 / 4 : ℝ) := by
      gcongr
    have h2 : (B : ℝ) - (A : ℝ) - K₁ * (49 * (Real.log N) ^ 2) * (N : ℝ) ^ (1 / 4 : ℝ) ≤
        ((Randomized.primeBin A B).card : ℝ) * Real.log B := by linarith only [hsup, h1]
    have h3 : ((Randomized.primeBin A B).card : ℝ) * Real.log B ≤
        ((Randomized.primeBin A B).card : ℝ) * (Real.log N / 2) :=
      mul_le_mul_of_nonneg_left hlogB_le (Nat.cast_nonneg _)
    linarith only [h2, h3]
  have hchar_le' :
      ‖∑ p ∈ Randomized.primeBin A B, splitChar N (p : ZMod (8 * N))‖ ≤
        2 * K₂ * (49 * (Real.log N) ^ 2) * (N : ℝ) ^ (1 / 4 : ℝ) := by
    refine hchar_sum.trans ?_
    gcongr
  have hBA : Real.sqrt N / 4 - 1 ≤ (B : ℝ) - (A : ℝ) := by linarith only [hB_gt, hA_le]
  have hfinal_mul : (1 / 4 : ℝ) * Real.sqrt N ≤ 2 * ((ReducedForms N).card : ℝ) * Real.log N := by
    have hK1_term_nonneg : 0 ≤ K₁ * (49 * (Real.log N) ^ 2) * (N : ℝ) ^ (1 / 4 : ℝ) := by positivity
    have h2 : 2 * (K₁ * (49 * (Real.log N) ^ 2) * (N : ℝ) ^ (1 / 4 : ℝ)) ≤
        (K₁ * (49 * (Real.log N) ^ 2) * (N : ℝ) ^ (1 / 4 : ℝ)) * Real.log N := by
      nlinarith only [hlogN_ge, hK1_term_nonneg]
    have h3 := mul_le_mul_of_nonneg_right hcore hlogN_pos.le
    have h4 : (2 * K₂ * (49 * (Real.log N) ^ 2) * (N : ℝ) ^ (1 / 4 : ℝ) + 2 * Real.log N) * Real.log N +
        2 * (K₁ * (49 * (Real.log N) ^ 2) * (N : ℝ) ^ (1 / 4 : ℝ)) ≤ Real.sqrt N / 16 := by
      linarith only [herr_small, h2]
    have h5 : (‖∑ p ∈ Randomized.primeBin A B, splitChar N (p : ZMod (8 * N))‖ +
        (N.primeFactors.card : ℝ)) * Real.log N ≤
        (2 * K₂ * (49 * (Real.log N) ^ 2) * (N : ℝ) ^ (1 / 4 : ℝ) + 2 * Real.log N) * Real.log N :=
      mul_le_mul_of_nonneg_right (add_le_add hchar_le' hpf_le) hlogN_pos.le
    linarith only [hP_card_lower, h3, h4, h5, hBA, hsqrtN_ge]
  exact (div_le_iff₀ hlogN_pos).mpr (by linarith only [hfinal_mul])

#print axioms leading_square_bound
#print axioms leading_le_sqrt
#print axioms rootCount_mul_of_coprime
#print axioms rootCount_prime_pow_le_two
#print axioms rootCount_two_pow_eq_zero
#print axioms rootCount_two_pow_le_one
#print axioms rootCount_prime_pow_le_of_le_val
#print axioms rootCount_prime_pow_eq_zero_of_odd_val
#print axioms rootCount_prime_pow_le_of_gt_val
#print axioms sum_rootCount_prime_pow_div_le
#print axioms tsum_rootCount_prime_pow_div_le
#print axioms sum_two_pow_primeFactors_le
#print axioms reducedForms_card_le_product
#print axioms prod_local_factor_le_log_pow
#print axioms reducedForms_card_le_sqrt_mul_log_pow
#print axioms exists_reducedForm_of_legendreSym_eq_one
#print axioms splitChar_ne_one
#print axioms splitChar_apply_prime
#print axioms reducedForms_card_lower_from_critical_line

end Cogentic.RandomizedFormGroup
