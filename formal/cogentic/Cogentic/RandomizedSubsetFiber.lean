import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod

open scoped Finset

namespace Cogentic.RandomizedSubsetFiber

variable {Input Output Candidate Guard : Type*} [DecidableEq Output]

/-- Within an output fiber, the selected k-subset and a guard determine the input. -/
theorem card_fiber_le_subset_choices
    {s : Finset Input} {f : Input → Output}
    {candidates : Output → Finset Candidate} {selected : Input → Finset Candidate}
    {guards : Output → Finset Guard} {tag : Input → Guard} {k : ℕ}
    (hsubset : ∀ x ∈ s, selected x ⊆ candidates (f x))
    (hsize : ∀ x ∈ s, (selected x).card = k)
    (htag : ∀ x ∈ s, tag x ∈ guards (f x))
    (hdecode : ∀ ⦃x x'⦄, x ∈ s → x' ∈ s → f x = f x' →
      selected x = selected x' → tag x = tag x' → x = x')
    (y : Output) :
    (s.filter (fun x => f x = y)).card ≤ ((candidates y).card.choose k) * (guards y).card := by
  rw [← Finset.card_powersetCard, ← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun x => (selected x, tag x))
  · intro x hx
    obtain ⟨hxs, hxy⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
    rw [Finset.mem_coe, ← hxy]
    exact Finset.mem_product.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨hsubset x hxs, hsize x hxs⟩, htag x hxs⟩
  · intro x hx x' hx' heq
    obtain ⟨hxs, hxy⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
    obtain ⟨hx's, hx'y⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hx')
    exact hdecode hxs hx's (hxy.trans hx'y.symm)
      (congrArg Prod.fst heq) (congrArg Prod.snd heq)

/-- A uniform bound on candidate and guard counts gives an image-size lower bound. -/
theorem card_le_mul_card_image
    {s : Finset Input} {f : Input → Output}
    {candidates : Output → Finset Candidate} {selected : Input → Finset Candidate}
    {guards : Output → Finset Guard} {tag : Input → Guard} {k m g : ℕ}
    (hsubset : ∀ x ∈ s, selected x ⊆ candidates (f x))
    (hsize : ∀ x ∈ s, (selected x).card = k)
    (htag : ∀ x ∈ s, tag x ∈ guards (f x))
    (hdecode : ∀ ⦃x x'⦄, x ∈ s → x' ∈ s → f x = f x' →
      selected x = selected x' → tag x = tag x' → x = x')
    (hcandidates : ∀ y ∈ s.image f, (candidates y).card ≤ k + m)
    (hguards : ∀ y ∈ s.image f, (guards y).card ≤ g) :
    s.card ≤ ((k + m).choose m * g) * (s.image f).card := by
  apply Finset.card_le_mul_card_image
  intro y hy
  calc
    _ ≤ ((candidates y).card.choose k) * (guards y).card :=
      card_fiber_le_subset_choices hsubset hsize htag hdecode y
    _ ≤ (k + m).choose k * g :=
      Nat.mul_le_mul (Nat.choose_le_choose k (hcandidates y hy)) (hguards y hy)
    _ = _ := by rw [Nat.choose_symm_add]

/-- If the subset alone determines the input inside each fiber, no guard
factor is needed. -/
theorem card_le_choose_mul_card_image
    {s : Finset Input} {f : Input → Output}
    {candidates : Output → Finset Candidate} {selected : Input → Finset Candidate}
    {k m : ℕ}
    (hsubset : ∀ x ∈ s, selected x ⊆ candidates (f x))
    (hsize : ∀ x ∈ s, (selected x).card = k)
    (hdecode : ∀ ⦃x x'⦄, x ∈ s → x' ∈ s → f x = f x' → selected x = selected x' → x = x')
    (hcandidates : ∀ y ∈ s.image f, (candidates y).card ≤ k + m) :
    s.card ≤ (k + m).choose m * (s.image f).card := by
  simpa only [Nat.mul_one] using
    (card_le_mul_card_image (guards := fun _ => ({()} : Finset Unit)) (tag := fun _ => ())
      (g := 1) hsubset hsize (by simp)
      (fun {_ _} hx hx' hfx hsel _ => hdecode hx hx' hfx hsel) hcandidates (by simp))

#print axioms card_fiber_le_subset_choices
#print axioms card_le_mul_card_image
#print axioms card_le_choose_mul_card_image

end Cogentic.RandomizedSubsetFiber
