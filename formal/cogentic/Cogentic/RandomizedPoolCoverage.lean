import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

open scoped BigOperators

namespace Cogentic.RandomizedPoolCoverage

variable {Ω Label : Type*} [Fintype Ω]

/-- The mass of an event under a finite law with explicit real weights. -/
noncomputable def eventMass (weight : Ω → ℝ) (event : Ω → Prop) : ℝ := by
  classical
  exact ∑ x, if event x then weight x else 0

/-- The product law for k independent draws from the same finite law. -/
noncomputable def iidWeight (weight : Ω → ℝ) (k : ℕ) (draw : Fin k → Ω) : ℝ :=
  ∏ i, weight (draw i)

/-- At least one retained label is missed by every entry in the pool. -/
noncomputable def poolMissMass (weight : Ω → ℝ) (k : ℕ) (labels : Finset Label)
    (hit : Label → Ω → Prop) : ℝ :=
  eventMass (iidWeight weight k) (fun draw => ∃ l ∈ labels, ∀ i, ¬ hit l (draw i))

omit [Fintype Ω] in
theorem iidWeight_nonneg (weight : Ω → ℝ) (k : ℕ) (hweight : ∀ x, 0 ≤ weight x) :
    ∀ draw : Fin k → Ω, 0 ≤ iidWeight weight k draw := by
  intro draw
  exact Finset.prod_nonneg fun i _ => hweight (draw i)

theorem iidWeight_total (weight : Ω → ℝ) (k : ℕ) (htotal : (∑ x, weight x) = 1) :
    (∑ draw : Fin k → Ω, iidWeight weight k draw) = 1 := by
  classical
  simp only [iidWeight, ← Fintype.sum_pow, htotal, one_pow]

private theorem eventMass_nonneg (weight : Ω → ℝ) (event : Ω → Prop)
    (hweight : ∀ x, 0 ≤ weight x) : 0 ≤ eventMass weight event := by
  classical
  unfold eventMass
  exact Finset.sum_nonneg fun x _ => by split <;> simp [hweight]

private theorem eventMass_compl (weight : Ω → ℝ) (event : Ω → Prop)
    (htotal : (∑ x, weight x) = 1) :
    eventMass weight (fun x => ¬ event x) = 1 - eventMass weight event := by
  classical
  have hadd : eventMass weight (fun x => ¬ event x) + eventMass weight event = 1 := by
    rw [← htotal]
    unfold eventMass
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by by_cases h : event x <;> simp [h]
  exact eq_sub_of_add_eq hadd

private theorem eventMass_exists_le_sum (weight : Ω → ℝ) (labels : Finset Label)
    (event : Label → Ω → Prop) (hweight : ∀ x, 0 ≤ weight x) :
    eventMass weight (fun x => ∃ l ∈ labels, event l x) ≤ ∑ l ∈ labels, eventMass weight (event l) := by
  classical
  unfold eventMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  have hterm (l : Label) : 0 ≤ if event l x then weight x else 0 := by
    split <;> simp [hweight]
  by_cases hexists : ∃ l ∈ labels, event l x
  · rw [if_pos hexists]
    obtain ⟨l, hl, hevent⟩ := hexists
    have hsingle := Finset.single_le_sum (f := fun l => if event l x then weight x else 0)
      (fun l _ => hterm l) hl
    simpa only [if_pos hevent] using hsingle
  · rw [if_neg hexists]
    exact Finset.sum_nonneg fun l _ => hterm l

/-- All k independent draws lie in a fixed event with probability equal to
the k-th power of its one-draw probability. -/
theorem iid_eventMass_eq_pow (weight : Ω → ℝ) (k : ℕ) (event : Ω → Prop) :
    eventMass (iidWeight weight k) (fun draw => ∀ i, event (draw i)) =
      eventMass weight event ^ k := by
  classical
  unfold eventMass
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro draw _
  by_cases hall : ∀ i, event (draw i)
  · rw [if_pos hall]
    exact Finset.prod_congr rfl fun i _ => (if_pos (hall i)).symm
  · rw [if_neg hall]
    obtain ⟨i, hi⟩ := not_forall.mp hall
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).symm

/-- A single label misses every draw with probability given by its one-draw
miss probability to the k-th power. -/
theorem iid_missMass_eq_pow (weight : Ω → ℝ) (k : ℕ) (hit : Ω → Prop)
    (htotal : (∑ x, weight x) = 1) :
    eventMass (iidWeight weight k) (fun draw => ∀ i, ¬ hit (draw i)) =
      (1 - eventMass weight hit) ^ k := by
  rw [iid_eventMass_eq_pow weight k (fun x => ¬ hit x), eventMass_compl weight hit htotal]

/-- The pool union bound uses independence of draws only. The same draw
may hit an arbitrary set of labels. -/
theorem poolMissMass_le_sum (weight : Ω → ℝ) (k : ℕ) (labels : Finset Label)
    (hit : Label → Ω → Prop) (hweight : ∀ x, 0 ≤ weight x)
    (htotal : (∑ x, weight x) = 1) :
    poolMissMass weight k labels hit ≤
      ∑ l ∈ labels, (1 - eventMass weight (hit l)) ^ k := by
  classical
  unfold poolMissMass
  calc
    _ ≤ ∑ l ∈ labels, eventMass (iidWeight weight k) (fun draw => ∀ i, ¬ hit l (draw i)) :=
      eventMass_exists_le_sum _ labels _ (iidWeight_nonneg weight k hweight)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _
      exact iid_missMass_eq_pow weight k (hit l) htotal

/-- A common lower bound p on individual hit probabilities yields the
cardinality form of the union bound. -/
theorem poolMissMass_le_card_mul (weight : Ω → ℝ) (k : ℕ) (labels : Finset Label)
    (hit : Label → Ω → Prop) (p : ℝ) (hweight : ∀ x, 0 ≤ weight x)
    (htotal : (∑ x, weight x) = 1) (hhit : ∀ l ∈ labels, p ≤ eventMass weight (hit l)) :
    poolMissMass weight k labels hit ≤ (labels.card : ℝ) * (1 - p) ^ k := by
  calc
    _ ≤ ∑ l ∈ labels, (1 - eventMass weight (hit l)) ^ k :=
      poolMissMass_le_sum weight k labels hit hweight htotal
    _ ≤ ∑ _l ∈ labels, (1 - p) ^ k := by
      apply Finset.sum_le_sum
      intro l hl
      have hmiss : 0 ≤ 1 - eventMass weight (hit l) := by
        rw [← eventMass_compl weight (hit l) htotal]
        exact eventMass_nonneg weight _ hweight
      exact pow_le_pow_left₀ hmiss (sub_le_sub_left (hhit l hl) 1) k
    _ = _ := by simp [nsmul_eq_mul]

theorem poolMissMass_empty_labels (weight : Ω → ℝ) (k : ℕ) (hit : Label → Ω → Prop) :
    poolMissMass weight k ∅ hit = 0 := by
  classical
  simp [poolMissMass, eventMass]

/-- The unique empty draw misses every label, so failure is exactly the
indicator that at least one label was retained. -/
theorem poolMissMass_empty_pool (weight : Ω → ℝ) (labels : Finset Label)
    (hit : Label → Ω → Prop) [Decidable labels.Nonempty] :
    poolMissMass weight 0 labels hit = if labels.Nonempty then 1 else 0 := by
  classical
  by_cases h : labels.Nonempty
  · have h' : ∃ l, l ∈ labels := h
    simp [poolMissMass, eventMass, iidWeight, h, h']
  · have h' : ∀ l, l ∉ labels := fun l hl => h ⟨l, hl⟩
    simp [poolMissMass, eventMass, h, h']

#print axioms iidWeight_total
#print axioms iid_missMass_eq_pow
#print axioms poolMissMass_le_sum
#print axioms poolMissMass_le_card_mul
#print axioms poolMissMass_empty_labels
#print axioms poolMissMass_empty_pool

end Cogentic.RandomizedPoolCoverage
