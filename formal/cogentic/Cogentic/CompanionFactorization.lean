import Cogentic.CompanionReduction
import Cogentic.CompanionFactorCost

namespace Cogentic.Companion
open Concrete TwoThirdsFactor TwoThirdsSearch TwoThirdsFinish CompanionSplitCost Real Filter

/-- These are the gates before the search in `Concrete.totalStepWith`. -/
abbrev ReachesSearch (k n : ℕ) : Prop :=
  let b := n.log2+1
  2 ≤ n ∧ 8 < b ∧ primeCheck n (List.range' 1 (polyCutoff k b)) = false ∧ ¬2 ∣ n ∧
    powerDivisor n b = none ∧ presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n) = none

/-- A hit after the guards is the exact split returned by the executable driver. -/
theorem step_of_search_hit (search : (a : ℕ) → 2 ≤ a → List ℕ → Option {d // ProperDivisor a d})
    {k n : ℕ} (h : ReachesSearch k n)
    (gen : generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1))))
    (d : {d // ProperDivisor n d}) (hit : search n h.1 (List.range' 1 (polyCutoff k (n.log2+1))) = some d) :
    totalStepWith search k n h.1 gen = .split d.val ⟨d.property.1,d.property.2.1⟩ d.property.2.2 := by
  obtain ⟨hn,large,primality,odd,power,sieve⟩ := h
  simp [totalStepWith,not_le.mpr large,primality,odd,power,sieve,hit]
  rfl

/-- One node's companion charge. An early return or a divisor from the fixed
search incurs no companion call. -/
def backendWork (split : Splitter) (k n : ℕ) : ℕ :=
  if h : ReachesSearch k n then splitterWork split n h.1 else 0

/-- The guarded factorizer accepts any sufficiently large set of verified targets. -/
theorem factorization_of_dense_box_hits (line : DirichletLZerosOnLine)
    (split : Splitter) {C₁ A : ℝ} (hc : 0 ≤ C₁) (ha : 0 ≤ A) (spec : SplitterSpec split C₁ A) :
    ∃ (k : ℕ) (gen : ∀ n, 2 ≤ n → generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1)))),
    (∀ᶠ n : ℕ in atTop, ReachesSearch k n → DenseBoxHits n) →
    ∀ (frontWork : ℕ → ℕ) (D : ℝ), 0 ≤ D → (∀ᶠ n : ℕ in atTop, (frontWork n : ℝ) ≤ exp (D*scale n)) →
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      (∀ n ≥ n₀, ∀ h : ReachesSearch k n, tryDivisorWith n h.1 (fun m => (split n m).1) ≠ none) ∧
      ∀ n (hn : 2 ≤ n),
        let tree := factor (fun a h => totalStepWith (fun x hx _ => tryDivisorWith x hx (fun m => (split x m).1))
          k a h (gen a h)) n hn
        tree.factors.prod = n ∧ (∀ p ∈ tree.factors, p.Prime) ∧
        (∀ p, p.Prime → ∀ j, p^j ∣ n ↔ j ≤ tree.factors.count p) ∧
        (n₀ ≤ n → (tree.work (fun a => frontWork a + backendWork split k a) : ℝ) ≤
          exp ((max D (C₁+12*A+131117) + ε) * scale n)) := by
  obtain ⟨k,supply⟩ := polynomial_generators_from_critical_line line
  have gen (n : ℕ) (hn : 2 ≤ n) : generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1))) := by
    have : NeZero n := ⟨by omega⟩
    exact supply n _ Nat.lt_log2_self
  refine ⟨k,gen,?_⟩
  intro ranks frontWork D hD front ε he
  let T := max D (C₁+12*A+131117)
  have onSearch : ∀ᶠ n : ℕ in atTop, ∀ h : ReachesSearch k n,
      tryDivisorWith n h.1 (fun m => (split n m).1) ≠ none ∧
      (splitterWork split n h.1 : ℝ) ≤ exp ((C₁+12*A+131117)*scale n) := by
    filter_upwards [ranks,eventually_ge_atTop 64] with n rank large h
    have comp : ¬n.Prime := fun prime => by
      have yes := (primeCheck_correct _ _ (gen n h.1)).mpr prime
      simp [h.2.2.1] at yes
    exact split_of_dense_box_hits split hc ha spec large h.1 comp h.2.2.2.2.1 (rank h)
  have logs : Tendsto (fun n : ℕ => log n) atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have growth := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<2/3)).comp logs
  have εpos : 0<ε/2 := by linarith
  have perCall : ∀ᶠ n : ℕ in atTop, ((frontWork n + backendWork split k n : ℕ):ℝ) ≤ exp ((T+ε/2)*scale n) := by
    filter_upwards [front,onSearch,logs.eventually_ge_atTop (exp 1), growth.eventually_ge_atTop (1/(ε/2))]
      with n f success lnLarge powLarge
    have lp := (exp_pos 1).trans_le lnLarge
    have z := (le_log_iff_exp_le lp).mpr lnLarge
    have vs : (log n)^(2/3:ℝ) ≤ scale n :=
      le_mul_of_one_le_right (rpow_nonneg lp.le _) (one_le_rpow z (by norm_num))
    have pos := (rpow_pos_of_pos lp (2/3:ℝ)).trans_le vs
    have extra := (div_le_iff₀ εpos).mp (powLarge.trans vs)
    have two : 2 ≤ exp ((ε/2)*scale n) := by linarith only [extra,add_one_le_exp ((ε/2)*scale n),mul_comm (ε/2) (scale n)]
    have back : (backendWork split k n:ℝ) ≤ exp ((C₁+12*A+131117)*scale n) := by
      by_cases h : ReachesSearch k n
      · simpa only [backendWork,dif_pos h] using (success h).2
      · simpa only [backendWork,dif_neg h,Nat.cast_zero] using (exp_pos ((C₁+12*A+131117)*scale n)).le
    have f' : (frontWork n:ℝ) ≤ exp (T*scale n) := f.trans (exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left ..) pos.le))
    have b' : (backendWork split k n:ℝ) ≤ exp (T*scale n) := back.trans (exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right ..) pos.le))
    rw [Nat.cast_add,add_mul,exp_add]
    exact (add_le_add f' b').trans
      (by linarith only [mul_le_mul_of_nonneg_left two (exp_pos (T*scale n)).le])
  have total := CompanionFactorCost.recursive_factorization_cost
    (fun a => frontWork a + backendWork split k a) (by dsimp [T]; positivity : 0 ≤ T+ε/2) perCall (ε/2) εpos
  obtain ⟨n₀,results⟩ := eventually_atTop.mp (onSearch.and total)
  refine ⟨n₀,fun n large h => ((results n large).1 h).1,?_⟩
  intro n hn tree
  refine ⟨tree.correct.1,fun p hp => Nat.prime_def.mpr (tree.correct.2 p hp),
    fun p hp j => tree.multiplicity (Nat.prime_def.mp hp) j,?_⟩
  intro large
  have cost := ((results n large).2 tree).2.2.2
  rwa [show T+ε/2+ε/2 = T+ε by ring] at cost

/-- Complete factorization by the guarded driver with the companion backend.
The supplied front charge covers the other local operations. Full rank is only
required where the executable gates reach the fixed search. -/
theorem factorization_of_box_rank (line : DirichletLZerosOnLine)
    (split : Splitter) {C₁ A : ℝ} (hc : 0 ≤ C₁) (ha : 0 ≤ A) (spec : SplitterSpec split C₁ A) :
    ∃ (k : ℕ) (gen : ∀ n, 2 ≤ n → generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1)))),
    (∀ᶠ n : ℕ in atTop, ReachesSearch k n → ∀ ell ∈ dyadicTargets (Fixed.beta (n.log2+1)), BoxHasRank n ell) →
    ∀ (frontWork : ℕ → ℕ) (D : ℝ), 0 ≤ D → (∀ᶠ n : ℕ in atTop, (frontWork n : ℝ) ≤ exp (D*scale n)) →
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      (∀ n ≥ n₀, ∀ h : ReachesSearch k n, tryDivisorWith n h.1 (fun m => (split n m).1) ≠ none) ∧
      ∀ n (hn : 2 ≤ n),
        let tree := factor (fun a h => totalStepWith (fun x hx _ => tryDivisorWith x hx (fun m => (split x m).1))
          k a h (gen a h)) n hn
        tree.factors.prod = n ∧ (∀ p ∈ tree.factors, p.Prime) ∧
        (∀ p, p.Prime → ∀ j, p^j ∣ n ↔ j ≤ tree.factors.count p) ∧
        (n₀ ≤ n → (tree.work (fun a => frontWork a + backendWork split k a) : ℝ) ≤
          exp ((max D (C₁+12*A+131117) + ε) * scale n)) := by
  obtain ⟨k,gen,finish⟩ := factorization_of_dense_box_hits line split hc ha spec
  obtain ⟨b₀,grow⟩ := Fixed.degree_grows 130000
  refine ⟨k,gen,fun ranks=>finish ?_⟩
  obtain ⟨n₁,dense⟩ := dense_of_all_hits line
  filter_upwards [ranks,eventually_ge_atTop (2^b₀),eventually_ge_atTop n₁] with n rank large enough gate
  apply dense n enough
  intro ell ht
  have hn := gate.1
  have bits := (Nat.le_log2 (show n≠0 by omega)).mpr large
  have composite : ¬n.Prime := fun hp=>by
    have yes := (primeCheck_correct _ _ (gen n hn)).mpr hp
    simp [gate.2.2.1] at yes
  exact witness_of_box_rank hn (grow _ (by omega)) composite ht gate.2.2.2.2.2 (rank gate ell ht)

end Cogentic.Companion

#print axioms Cogentic.Companion.factorization_of_box_rank
