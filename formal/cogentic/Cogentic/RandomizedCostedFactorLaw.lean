import Cogentic.RandomizedSplitWork

namespace Cogentic.RandomizedCostedFactorLaw

open scoped ArithmeticFunction.Omega ENNReal

/-- One completed splitter call, with its actual work and both proper factors. -/
structure SplitOutcome (n : ℕ) where
  left : ℕ
  right : ℕ
  work : ℕ
  left_ge : 2 ≤ left
  right_ge : 2 ≤ right
  product : left * right = n

theorem SplitOutcome.left_lt {n : ℕ} (s : SplitOutcome n) : s.left < n :=
  (lt_mul_of_one_lt_right (by have := s.left_ge; omega)
    (by have := s.right_ge; omega)).trans_eq s.product

theorem SplitOutcome.right_lt {n : ℕ} (s : SplitOutcome n) : s.right < n :=
  (lt_mul_of_one_lt_left (by have := s.right_ge; omega)
    (by have := s.left_ge; omega)).trans_eq s.product

/-- The input kernel records the joint distribution of the factors and the
full work of the splitter call. -/
abbrev SplitKernel := ∀ n : ℕ, 2 ≤ n → ¬n.Prime → PMF (SplitOutcome n)

/-- Sample both recursive calls with fresh randomness and record their combined
work, including splitter work at internal nodes and testing work at prime leaves. -/
noncomputable def factorLaw (split : SplitKernel) (leafWork : ℕ → ℕ)
    (n : ℕ) (hn : 2 ≤ n) : PMF (List ℕ × ℕ) :=
  if hp : n.Prime then PMF.pure ([n], leafWork n)
  else (split n hn hp).bind fun s =>
    (factorLaw split leafWork s.left s.left_ge).bind fun left =>
      (factorLaw split leafWork s.right s.right_ge).map fun right =>
        (left.1 ++ right.1, s.work + left.2 + right.2)
termination_by n
decreasing_by
  all_goals first | exact s.left_lt | exact s.right_lt

theorem factorLaw_of_prime (split : SplitKernel) (leafWork : ℕ → ℕ)
    {n : ℕ} (hn : 2 ≤ n) (hp : n.Prime) :
    factorLaw split leafWork n hn = PMF.pure ([n], leafWork n) := by
  rw [factorLaw, dif_pos hp]

theorem factorLaw_of_composite (split : SplitKernel) (leafWork : ℕ → ℕ)
    {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime) :
    factorLaw split leafWork n hn = (split n hn hp).bind fun s =>
      (factorLaw split leafWork s.left s.left_ge).bind fun left =>
        (factorLaw split leafWork s.right s.right_ge).map fun right =>
          (left.1 ++ right.1, s.work + left.2 + right.2) := by
  conv_lhs => rw [factorLaw, dif_neg hp]

/-- Every outcome of the joint law is a complete prime factorization. -/
theorem factorLaw_support_correct (split : SplitKernel) (leafWork : ℕ → ℕ) :
    ∀ (n : ℕ) (hn : 2 ≤ n) (out : List ℕ × ℕ),
      out ∈ (factorLaw split leafWork n hn).support →
        out.1.prod = n ∧ ∀ p ∈ out.1, p.Prime := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn out hout
    by_cases hp : n.Prime
    · rw [factorLaw_of_prime split leafWork hn hp, PMF.mem_support_pure_iff] at hout
      rw [hout]
      simp [hp]
    · rw [factorLaw_of_composite split leafWork hn hp, PMF.mem_support_bind_iff] at hout
      obtain ⟨s, _, hs⟩ := hout
      obtain ⟨left, hl, hl'⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
      obtain ⟨right, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hl'
      obtain ⟨hlprod, hlprime⟩ := ih s.left s.left_lt s.left_ge left hl
      obtain ⟨hrprod, hrprime⟩ := ih s.right s.right_lt s.right_ge right hr
      refine ⟨?_, ?_⟩
      · change (left.1 ++ right.1).prod = n
        rw [List.prod_append, hlprod, hrprod, s.product]
      · intro p h
        rcases List.mem_append.mp h with h | h
        · exact hlprime p h
        · exact hrprime p h

theorem factorLaw_support_perm (split : SplitKernel) (leafWork : ℕ → ℕ)
    {n : ℕ} (hn : 2 ≤ n) {out : List ℕ × ℕ}
    (hout : out ∈ (factorLaw split leafWork n hn).support) :
    out.1.Perm n.primeFactorsList :=
  (factorLaw_support_correct split leafWork n hn out hout).elim Nat.primeFactorsList_unique

/-- Expectation of a nonnegative observable under a discrete law. -/
noncomputable def mean {α : Type*} (p : PMF α) (cost : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a, p a * cost a

theorem mean_pure {α : Type*} (a : α) (cost : α → ℝ≥0∞) :
    mean (PMF.pure a) cost = cost a := by
  unfold mean
  rw [tsum_eq_single a]
  · simp [PMF.pure_apply]
  · intro b hb
    simp [PMF.pure_apply, hb]

theorem mean_bind {α β : Type*} (p : PMF α) (q : α → PMF β)
    (cost : β → ℝ≥0∞) :
    mean (p.bind q) cost = mean p (fun a => mean (q a) cost) := by
  simp only [mean, PMF.bind_apply, ← ENNReal.tsum_mul_right, mul_assoc]
  rw [ENNReal.tsum_comm]
  simp only [ENNReal.tsum_mul_left]

theorem mean_map {α β : Type*} (p : PMF α) (f : α → β) (cost : β → ℝ≥0∞) :
    mean (p.map f) cost = mean p (fun a => cost (f a)) := by
  rw [← PMF.bind_pure_comp, mean_bind]
  simp only [Function.comp_apply, mean_pure]

theorem mean_const {α : Type*} (p : PMF α) (c : ℝ≥0∞) :
    mean p (fun _ => c) = c := by
  rw [mean, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem mean_add {α : Type*} (p : PMF α) (f g : α → ℝ≥0∞) :
    mean p (fun a => f a + g a) = mean p f + mean p g := by
  simp only [mean, mul_add, ENNReal.tsum_add]

private theorem mean_mono {α : Type*} (p : PMF α) {f g : α → ℝ≥0∞} (h : ∀ a, f a ≤ g a) :
    mean p f ≤ mean p g := by
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul_right (h a) (p a)

noncomputable def expectedCost (split : SplitKernel) (leafWork : ℕ → ℕ)
    (n : ℕ) (hn : 2 ≤ n) : ℝ≥0∞ :=
  mean (factorLaw split leafWork n hn) (fun out => out.2)

theorem expectedCost_of_prime (split : SplitKernel) (leafWork : ℕ → ℕ)
    {n : ℕ} (hn : 2 ≤ n) (hp : n.Prime) :
    expectedCost split leafWork n hn = leafWork n := by
  rw [expectedCost, factorLaw_of_prime split leafWork hn hp, mean_pure]

/-- The expected-work recurrence follows from the bind and map of the joint law. -/
theorem expectedCost_of_composite (split : SplitKernel) (leafWork : ℕ → ℕ)
    {n : ℕ} (hn : 2 ≤ n) (hp : ¬ n.Prime) :
    expectedCost split leafWork n hn =
      mean (split n hn hp) (fun s => s.work) +
      mean (split n hn hp) (fun s =>
        expectedCost split leafWork s.left s.left_ge +
          expectedCost split leafWork s.right s.right_ge) := by
  rw [expectedCost, factorLaw_of_composite split leafWork hn hp, mean_bind, ← mean_add]
  congr 1
  funext s
  simp only [expectedCost, mean_bind, mean_map, Nat.cast_add, mean_add, mean_const]
  rw [add_assoc]

/-- A per-call expected splitter budget, including charged prime tests and
verification, lifts to an expected budget for the recursive joint law. -/
theorem expectedCost_le_cardFactors (split : SplitKernel) (leafWork : ℕ → ℕ)
    (T : ℕ → ℝ≥0∞) (hT : Monotone T)
    (hleaf : ∀ n, n.Prime → (leafWork n : ℝ≥0∞) ≤ T n)
    (hsplit : ∀ n (hn : 2 ≤ n) (hp : ¬ n.Prime),
      mean (split n hn hp) (fun s => s.work) ≤ T n) :
    ∀ (n : ℕ) (hn : 2 ≤ n),
      expectedCost split leafWork n hn ≤ (↑(2 * Ω n - 1 : ℕ) : ℝ≥0∞) * T n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hp : n.Prime
    · rw [expectedCost_of_prime split leafWork hn hp]
      simpa [ArithmeticFunction.cardFactors_apply_prime hp] using hleaf n hp
    · have hchild (s : SplitOutcome n) :
          expectedCost split leafWork s.left s.left_ge +
            expectedCost split leafWork s.right s.right_ge ≤
              (↑(2 * Ω n - 2 : ℕ) : ℝ≥0∞) * T n := by
        have hleft : 1 ≤ Ω s.left :=
          ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr (by have := s.left_ge; omega)
        have hright : 1 ≤ Ω s.right :=
          ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr (by have := s.right_ge; omega)
        have hsum : Ω n = Ω s.left + Ω s.right := by
          exact (congrArg ArithmeticFunction.cardFactors s.product.symm).trans
            (ArithmeticFunction.cardFactors_mul (by have := s.left_ge; omega)
              (by have := s.right_ge; omega))
        calc
          _ ≤ (↑(2 * Ω s.left - 1 : ℕ) : ℝ≥0∞) * T s.left +
              (↑(2 * Ω s.right - 1 : ℕ) : ℝ≥0∞) * T s.right :=
            add_le_add (ih s.left s.left_lt s.left_ge) (ih s.right s.right_lt s.right_ge)
          _ ≤ (↑(2 * Ω s.left - 1 : ℕ) : ℝ≥0∞) * T n +
              (↑(2 * Ω s.right - 1 : ℕ) : ℝ≥0∞) * T n :=
            add_le_add (mul_le_mul_right (hT s.left_lt.le) _) (mul_le_mul_right (hT s.right_lt.le) _)
          _ = _ := by
            rw [← add_mul, ← Nat.cast_add]
            congr 2
            omega
      have hΩ : 1 ≤ Ω n :=
        ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr (by omega)
      rw [expectedCost_of_composite split leafWork hn hp]
      calc
        _ ≤ T n + (↑(2 * Ω n - 2 : ℕ) : ℝ≥0∞) * T n := by
          refine add_le_add (hsplit n hn hp) ?_
          exact (mean_mono (split n hn hp) hchild).trans_eq (mean_const _ _)
        _ = _ := by
          conv_lhs => enter [1]; rw [← one_mul (T n)]
          rw [← add_mul, ← Nat.cast_one (R := ℝ≥0∞), ← Nat.cast_add]
          congr 2
          omega

theorem expectedCost_le_log2 (split : SplitKernel) (leafWork : ℕ → ℕ)
    (T : ℕ → ℝ≥0∞) (hT : Monotone T)
    (hleaf : ∀ n, n.Prime → (leafWork n : ℝ≥0∞) ≤ T n)
    (hsplit : ∀ n (hn : 2 ≤ n) (hp : ¬ n.Prime),
      mean (split n hn hp) (fun s => s.work) ≤ T n)
    {n : ℕ} (hn : 2 ≤ n) :
    expectedCost split leafWork n hn ≤ (↑(2 * n.log2 - 1 : ℕ) : ℝ≥0∞) * T n := by
  refine (expectedCost_le_cardFactors split leafWork T hT hleaf hsplit n hn).trans ?_
  have hΩ := RandomizedSplitWork.cardFactors_le_log2 n
  have h : 2 * Ω n - 1 ≤ 2 * n.log2 - 1 := by omega
  exact mul_le_mul_left (Nat.cast_le.mpr h) (T n)

#print axioms factorLaw_support_perm
#print axioms expectedCost_of_composite
#print axioms expectedCost_le_log2

end Cogentic.RandomizedCostedFactorLaw
