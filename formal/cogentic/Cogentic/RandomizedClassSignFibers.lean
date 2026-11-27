import Cogentic.RandomizedSignCount
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.SetTheory.Cardinal.Finite

namespace Cogentic.RandomizedClassSignFibers

open Cogentic.RandomizedSignCount

variable {G H K Q X : Type*}

/-- Conditioning on a square gives a translate of the subgroup of elements
of order dividing two. The inverse equivalence sends `t` to `a*t`. -/
def squareFiberEquivTwoTorsion [CommGroup G] (a : G) :
    SquareFiber a ≃ (powMonoidHom (α := G) 2).ker :=
  (powMonoidHom (α := G) 2).fiberEquivKer a

theorem squareFiberEquivTwoTorsion_symm_apply [CommGroup G] (a : G)
    (t : (powMonoidHom (α := G) 2).ker) :
    ((squareFiberEquivTwoTorsion a).symm t : G) = a*(t : G) := rfl

/-- A surjective sign map on the kernel of the conditioning homomorphism
gives equally sized sign fibers on each nonempty conditioning fiber. -/
theorem card_equivariant_tag_fiber [Group G] [Group H] [Group Q]
    (φ : G →* H) (a : G) (σ : φ.ker →* Q) (hσ : Function.Surjective σ)
    (tag : (φ ⁻¹' {φ a} : Set G) → Q)
    (heq : ∀ t, tag ((φ.fiberEquivKer a).symm t) = σ t*tag ⟨a,rfl⟩)
    (q : Q) :
    Nat.card {x : (φ ⁻¹' {φ a} : Set G) // tag x = q} = Nat.card σ.ker := by
  let e := (φ.fiberEquivKer a).symm
  let q₀ := tag ⟨a,rfl⟩
  have hf (t : φ.ker) : tag (e t) = q ↔ σ t = q/q₀ := by
    rw [heq]
    exact eq_div_iff_mul_eq'.symm
  exact (Nat.card_congr (e.subtypeEquiv fun t => (hf t).symm)).symm.trans
    (Nat.card_congr (σ.fiberEquivKerOfSurjective hσ (q/q₀)))

/-- The relative signs on a fixed square fiber are uniform whenever the
two-torsion sign homomorphism is onto the relative sign group. -/
theorem card_square_tag_fiber [CommGroup G] [Group Q] (a : G)
    (σ : (powMonoidHom (α := G) 2).ker →* Q) (hσ : Function.Surjective σ)
    (tag : SquareFiber a → Q)
    (heq : ∀ t, tag ((squareFiberEquivTwoTorsion a).symm t) = σ t*tag ⟨a,rfl⟩)
    (q : Q) : Nat.card {x : SquareFiber a // tag x = q} = Nat.card σ.ker :=
  card_equivariant_tag_fiber (powMonoidHom (α := G) 2) a σ hσ tag heq q

/-- Multiplying a chosen lift by a global sign yields one lift of each
absolute sign in its coset. The inverse sends `x` to the unique pair
with global sign `(lift x)⁻¹*z`. -/
def globalSignFiberEquiv [CommGroup K] (D : Subgroup K) (lift : X → K)
    (tag : X → K ⧸ D) (hlift : ∀ x, QuotientGroup.mk' D (lift x) = tag x) (z : K) :
    {y : X × D // lift y.1*(y.2 : K) = z} ≃
      {x : X // tag x = QuotientGroup.mk' D z} where
  toFun y := ⟨y.1.1, by
    have hD : QuotientGroup.mk' D (y.1.2 : K) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr y.1.2.property
    have he := congrArg (QuotientGroup.mk' D) y.property
    simpa only [map_mul, hlift, hD, mul_one] using he⟩
  invFun x := ⟨(x.1, ⟨(lift x.1)⁻¹*z, by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' D ((lift x.1)⁻¹*z) = 1
    rw [map_mul, map_inv, hlift, x.property, inv_mul_cancel]⟩), by simp⟩
  left_inv y := by
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · rfl
    · apply Subtype.ext
      change (lift y.1.1)⁻¹*z = (y.1.2 : K)
      calc
        (lift y.1.1)⁻¹*z = (lift y.1.1)⁻¹*(lift y.1.1*(y.1.2 : K)) :=
          congrArg (fun w => (lift y.1.1)⁻¹*w) y.property.symm
        _ = _ := by simp
  right_inv x := Subtype.ext rfl

/-- The independent global sign preserves the common relative fiber count
and gives that count to every absolute sign. In the CRT sign group, take
`D` to be the two-element subgroup of global signs. -/
theorem card_square_global_sign_fiber [CommGroup G] [CommGroup K] (a : G) (D : Subgroup K)
    (σ : (powMonoidHom (α := G) 2).ker →* K ⧸ D) (hσ : Function.Surjective σ)
    (tag : SquareFiber a → K ⧸ D)
    (heq : ∀ t, tag ((squareFiberEquivTwoTorsion a).symm t) = σ t*tag ⟨a,rfl⟩)
    (lift : SquareFiber a → K) (hlift : ∀ x, QuotientGroup.mk' D (lift x) = tag x) (z : K) :
    Nat.card {y : SquareFiber a × D // lift y.1*(y.2 : K) = z} = Nat.card σ.ker :=
  (Nat.card_congr (globalSignFiberEquiv D lift tag hlift z)).trans
    (card_square_tag_fiber a σ hσ tag heq (QuotientGroup.mk' D z))

private theorem uniform_fiber_card_mul [Finite X] [Finite Q] (f : X → Q) {n : ℕ}
    (h : ∀ q, Nat.card {x : X // f x = q} = n) (q : Q) :
    Nat.card {x : X // f x = q} * Nat.card Q = Nat.card X := by
  classical
  let : Fintype Q := Fintype.ofFinite Q
  rw [h, ← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  simp [h, Nat.card_eq_fintype_card, Nat.mul_comm]

/-- The exact relative-sign probability is the reciprocal of the size of
the relative sign group, expressed by cross-multiplying finite counts. -/
theorem square_tag_uniform [CommGroup G] [Finite G] [Group Q] (a : G)
    (σ : (powMonoidHom (α := G) 2).ker →* Q) (hσ : Function.Surjective σ)
    (tag : SquareFiber a → Q)
    (heq : ∀ t, tag ((squareFiberEquivTwoTorsion a).symm t) = σ t*tag ⟨a,rfl⟩)
    (q : Q) :
    Nat.card {x : SquareFiber a // tag x = q} * Nat.card Q = Nat.card (SquareFiber a) := by
  let : Finite Q := Finite.of_surjective σ hσ
  exact uniform_fiber_card_mul tag (card_square_tag_fiber a σ hσ tag heq) q

/-- Independent uniform sampling of a square-root class and a global sign
gives an exactly uniform absolute sign on the full finite group. -/
theorem square_global_sign_uniform [CommGroup G] [Finite G] [CommGroup K] [Finite K]
    (a : G) (D : Subgroup K)
    (σ : (powMonoidHom (α := G) 2).ker →* K ⧸ D) (hσ : Function.Surjective σ)
    (tag : SquareFiber a → K ⧸ D)
    (heq : ∀ t, tag ((squareFiberEquivTwoTorsion a).symm t) = σ t*tag ⟨a,rfl⟩)
    (lift : SquareFiber a → K) (hlift : ∀ x, QuotientGroup.mk' D (lift x) = tag x) (z : K) :
    Nat.card {y : SquareFiber a × D // lift y.1*(y.2 : K) = z} * Nat.card K =
      Nat.card (SquareFiber a × D) :=
  uniform_fiber_card_mul (fun y : SquareFiber a × D => lift y.1*(y.2 : K))
    (card_square_global_sign_fiber a D σ hσ tag heq lift hlift) z

end Cogentic.RandomizedClassSignFibers
