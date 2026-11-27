import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic

/-! A monogenic evaluation catalog either has at most the polynomial degree many
distinct generator images, or exposes a divisor through an image difference. -/

namespace Cogentic.RandomizedEvaluationMaps

open Polynomial

variable {N : ℕ} {ι : Type*} [Fintype ι]

/-- Unit differences make the list of roots inject into the roots modulo each prime divisor. -/
theorem card_le_degree_of_unit_differences (F : (ZMod N)[X]) (hmonic : F.Monic)
    (a : ι → ZMod N) (ha : ∀ i, F.IsRoot (a i))
    (hunit : ∀ i j, i ≠ j → IsUnit (a i - a j))
    {p : ℕ} [Fact p.Prime] (hp : p ∣ N) : Fintype.card ι ≤ F.natDegree := by
  let reduce := ZMod.castHom hp (ZMod p)
  let G := F.map reduce
  have hG : G.Monic := hmonic.map reduce
  let root (i : ι) : G.roots.toFinset :=
    ⟨reduce (a i), Multiset.mem_toFinset.mpr <| Polynomial.mem_roots'.mpr
      ⟨hG.ne_zero, by
        change (F.map reduce).eval (reduce (a i)) = 0
        rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, ha i, map_zero]⟩⟩
  have hinj : Function.Injective root := by
    intro i j hij
    by_contra hne
    have heq : reduce (a i) = reduce (a j) := congrArg Subtype.val hij
    have hu := (hunit i j hne).map reduce
    rw [map_sub, heq, sub_self] at hu
    exact not_isUnit_zero hu
  calc
    Fintype.card ι ≤ Fintype.card ↥G.roots.toFinset := Fintype.card_le_of_injective root hinj
    _ = G.roots.toFinset.card := Fintype.card_coe _
    _ ≤ G.roots.card := Multiset.toFinset_card_le _
    _ ≤ G.natDegree := Polynomial.card_roots' G
    _ = F.natDegree := hmonic.natDegree_map reduce

/-- A nonzero nonunit modulo a positive integer gives an explicit proper divisor. -/
theorem proper_gcd_of_ne_zero_of_not_isUnit [NeZero N] (x : ZMod N)
    (hne : x ≠ 0) (hnu : ¬ IsUnit x) :
    1 < x.val.gcd N ∧ x.val.gcd N < N ∧ x.val.gcd N ∣ N := by
  have hval : 0 < x.val := Nat.pos_of_ne_zero fun hz => hne ((ZMod.val_eq_zero x).mp hz)
  have hg := Nat.gcd_le_left N hval
  have hng : ¬ x.val.Coprime N := by
    intro hc
    apply hnu
    simpa only [ZMod.natCast_val, ZMod.cast_id] using
      (ZMod.isUnit_iff_coprime x.val N).mpr hc
  change x.val.gcd N ≠ 1 at hng
  have hpos := Nat.gcd_pos_of_pos_right x.val (NeZero.pos N)
  exact ⟨by omega, hg.trans_lt (ZMod.val_lt x), Nat.gcd_dvd_right _ _⟩

variable {A : Type*} [CommRing A]

/-- A common multiplier that becomes a unit preserves separation by the generator. -/
theorem generator_image_injective_of_unit_multiplier (θ : A) (k : ℕ)
    (hk : IsUnit (k : ZMod N))
    (hgen : ∀ y : A, ∃ f : ℤ[X], f.eval₂ (Int.castRingHom A) θ = (k : A) * y) :
    Function.Injective (fun e : A →+* ZMod N => e θ) := by
  intro e₁ e₂ he
  ext y
  obtain ⟨f, hf⟩ := hgen y
  change e₁ θ = e₂ θ at he
  have hpoly : e₁ (f.eval₂ (Int.castRingHom A) θ) =
      e₂ (f.eval₂ (Int.castRingHom A) θ) := by
    simp only [Polynomial.hom_eval₂, he]
    congr 1
    ext z
    simp
  rw [hf, map_mul, map_mul, map_natCast, map_natCast] at hpoly
  exact hk.mul_right_inj.mp hpoly

/-- Distinct homomorphisms of an integer-monogenic order have distinct generator images. -/
theorem generator_image_injective (θ : A)
    (hgen : Function.Surjective (fun f : ℤ[X] => f.eval₂ (Int.castRingHom A) θ)) :
    Function.Injective (fun e : A →+* ZMod N => e θ) := by
  apply generator_image_injective_of_unit_multiplier θ 1 (by simp)
  intro y
  simpa using hgen y

/-- A finite catalog of distinct evaluation maps is degree-bounded unless a generator
image difference gives a proper divisor of the input. -/
theorem card_le_degree_or_proper_gcd_of_injective_images [NeZero N] (hN : 1 < N)
    (F : ℤ[X]) (hmonic : F.Monic) (θ : A)
    (hroot : F.eval₂ (Int.castRingHom A) θ = 0)
    (e : ι → A →+* ZMod N) (he : Function.Injective (fun i => e i θ)) :
    Fintype.card ι ≤ F.natDegree ∨
      ∃ i j, let g := (e i θ - e j θ).val.gcd N
        1 < g ∧ g < N ∧ g ∣ N := by
  classical
  let a (i : ι) := e i θ
  by_cases hunit : ∀ i j, i ≠ j → IsUnit (a i - a j)
  · left
    obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd (by omega : N ≠ 1)
    let : Fact p.Prime := ⟨hp⟩
    let G := F.map (Int.castRingHom (ZMod N))
    have hG : G.Monic := hmonic.map _
    have ha (i : ι) : G.IsRoot (a i) := by
      change G.eval (e i θ) = 0
      have hh := congrArg (e i) hroot
      rw [Polynomial.hom_eval₂, map_zero] at hh
      have hcomp : (e i).comp (Int.castRingHom A) = Int.castRingHom (ZMod N) := by
        ext z
        simp
      rw [hcomp] at hh
      rwa [Polynomial.eval_map]
    have hcard := card_le_degree_of_unit_differences G hG a ha hunit hdiv
    exact hcard.trans Polynomial.natDegree_map_le
  · right
    push Not at hunit
    obtain ⟨i, j, hij, hnu⟩ := hunit
    exact ⟨i, j, proper_gcd_of_ne_zero_of_not_isUnit _ (sub_ne_zero.mpr (he.ne hij)) hnu⟩

/-- In an integer-monogenic order, distinct evaluation maps satisfy the image separation hypothesis. -/
theorem card_le_degree_or_proper_gcd [NeZero N] (hN : 1 < N)
    (F : ℤ[X]) (hmonic : F.Monic) (θ : A)
    (hroot : F.eval₂ (Int.castRingHom A) θ = 0)
    (hgen : Function.Surjective (fun f : ℤ[X] => f.eval₂ (Int.castRingHom A) θ))
    (e : ι → A →+* ZMod N) (he : Function.Injective e) :
    Fintype.card ι ≤ F.natDegree ∨
      ∃ i j, let g := (e i θ - e j θ).val.gcd N
        1 < g ∧ g < N ∧ g ∣ N :=
  card_le_degree_or_proper_gcd_of_injective_images hN F hmonic θ hroot e
    ((generator_image_injective θ hgen).comp he)

end Cogentic.RandomizedEvaluationMaps
