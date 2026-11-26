import Cogentic.LocalFactorizationCost
import Cogentic.DriverSetupCost
import Cogentic.BoxAxisCost
import Cogentic.GeneratorListCost
import Cogentic.RecursionGates
import Cogentic.SearchTraceCost

namespace Cogentic.Companion
open Concrete TwoThirdsFactor TwoThirdsSearch TwoThirdsFinish CompanionSplitCost Real Filter

/-- Trial division is performed exactly on the small-input branch or after
the guards and the exponent backend have exhausted the fixed search. -/
def fallbackWork (split : Splitter) (k n : ℕ) : ℕ :=
  if h : 2 ≤ n then
    if n.log2+1 ≤ 8 then (BinaryPresieve.trialFactor n.bits).2
    else if ReachesSearch k n ∧ tryDivisorWith n h (fun m => (split n m).1) = none then
      (BinaryPresieve.trialFactor n.bits).2
    else 0
  else 0

/-- The saturated exponent is constructed only on the collector's orders branch. -/
def saturationWork (n : ℕ) (hn : 2≤n) : ℕ :=
  let b := n.log2+1
  match (fixedCollection n hn).1 with
  | .divisor .. => 0
  | .orders e .. => (BinarySaturation.build e.bits (indexCap b (Fixed.beta b)).bits).2

private theorem saturation_bound (n : ℕ) (hn : 2≤n) :
    saturationWork n hn ≤ 2^(8079*TwoThirdsCost.scale (n.log2+1)) := by
  have spec := BinarySaturation.driver_saturation n hn
  change (match (fixedCollection n hn).1 with
    | .divisor .. => True
    | .orders e .. => _ ∧ _) at spec
  unfold saturationWork
  cases eq : (fixedCollection n hn).1 with
  | divisor => exact Nat.zero_le _
  | orders => rw [eq] at spec; exact spec.2

/-- The shared words, guards, loop axes and tree-output budget at a node.
Paying the setup even on early returns gives a uniform upper bound. -/
def commonWork (k n : ℕ) : ℕ :=
  let b := n.log2+1
  (BinarySchedule.setup n.bits).2 + (BinaryGenerators.run k b.bits).2 +
    (BinarySplitter.primality n (List.range' 1 (polyCutoff k b))).2 +
    (BinaryIndexCap.presieveBits n.bits b.bits (Fixed.beta b).bits (Fixed.A b).bits (Fixed.rootBase n).bits).2 +
    (BinaryBox.axes b.bits (Fixed.U b).bits (Fixed.A b).bits).2 +
    BinaryRecursion.nodeBudget n + b + 8

def driverWork (split : Splitter) (k n : ℕ) : ℕ :=
  commonWork k n + (if h : ReachesSearch k n then
    additionalSearchWork n + saturationWork n h.1 else 0) +
    fallbackWork split k n

theorem driver_work_bound (split : Splitter) {k : ℕ} {C₁ A : ℝ}
    (hc : 0≤C₁) (ha : 0≤A) (spec : SplitterSpec split C₁ A)
    (gen : ∀ n, 2 ≤ n → generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1))))
    (hits : ∀ᶠ n : ℕ in atTop, ReachesSearch k n → DenseBoxHits n) :
    ∀ᶠ n : ℕ in atTop, (driverWork split k n:ℝ) ≤ exp (715000000*scale n) := by
  obtain ⟨b₀,grows⟩ := Fixed.degree_grows 10004
  filter_upwards [hits,eventually_ge_atTop (2^(max 9 (max k b₀))),eventually_ge_atTop 64] with n cover big large
  let b := n.log2+1
  let S := TwoThirdsCost.scale b
  let X := 2^(10441015*S)
  have two : 2≤n := by omega
  have len := (Nat.le_log2 (show n≠0 by omega)).mpr big
  have hk : k≤b := by dsimp [b]; omega
  have bp : 0<b := Nat.succ_pos _
  have d := grows b (by dsimp [b]; omega)
  have small : ¬n.log2+1≤8 := by omega
  have ds := Fixed.degree_pos bp
  have zs : Fixed.z b≤S := (Nat.le_mul_of_pos_left _ ds).trans
    ((Nat.le_mul_of_pos_left _ ds).trans (Fixed.scale_bounds bp).1)
  have sp : 0<S := (Nat.succ_pos _).trans_le zs
  have weaken {j w : ℕ} (bound : w≤2^(j*S)) (coef : j≤10441015) : w≤X :=
    bound.trans (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_right S coef))
  have sc := weaken (BinarySchedule.setup_spec two (le_trans (by decide : 2≤10004) d)).2 (by decide)
  have gs := weaken (BinaryGenerators.fixed_list k b bp hk).2 (by decide)
  have pr := weaken ((BinarySplitter.driver_primality n k).2.trans
    (BinarySplitter.driver_budgets_scale b k bp hk).1) (by decide)
  have pre := weaken (BinaryIndexCap.fixed_presieve_with_cap two).2 (by decide)
  have axes := weaken (BinaryBox.fixed_axes bp).2 (by decide)
  have emit := weaken (BinaryRecursion.budget_scale n) (by decide)
  have bits : b≤X := (Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right Nat.zero_lt_two zs) : b≤2^S).trans
    (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
  have one : 8≤X := (show 8=2^3 by decide).le.trans (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
  have common : commonWork k n≤8*X := by
    dsimp only [commonWork]
    dsimp only [b] at bits gs axes
    omega
  have guarded : (if h : ReachesSearch k n then additionalSearchWork n+saturationWork n h.1 else 0) ≤ 2*X := by
    split
    next h =>
      have solve := additional_search_bound two d
      have sat := weaken (saturation_bound n h.1) (by decide)
      exact (Nat.add_le_add solve sat).trans_eq (two_mul _).symm
    next => exact Nat.zero_le _
  have fallback : fallbackWork split k n=0 := by
    simp only [fallbackWork,dif_pos two,if_neg small]
    apply if_neg
    rintro ⟨h,miss⟩
    have composite : ¬n.Prime := fun p => by
      have yes := (primeCheck_correct _ _ (gen n two)).mpr p
      simp [h.2.2.1] at yes
    exact (split_of_dense_box_hits split hc ha spec large two composite h.2.2.2.2.1 (cover h)).1 miss
  have work : driverWork split k n ≤ 2^(11000000*S) := calc
    _ ≤ 2^4*X := by unfold driverWork; rw [fallback,Nat.add_zero]; omega
    _ = 2^(4+10441015*S) := (pow_add ..).symm
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  simpa only [Nat.cast_ofNat,show (11000000:ℝ)*65=715000000 by norm_num] using natural_cost large work

/-- The recursive cost over the measured stages, including the actual
trial-division fallback, follows from coverage alone and the companion splitter. -/
theorem factor_tree_of_accounted_stages (line : DirichletLZerosOnLine)
    (split : Splitter) {C₁ A : ℝ} (hc : 0≤C₁) (ha : 0≤A) (spec : SplitterSpec split C₁ A) :
    ∃ (k : ℕ) (gen : ∀ n, 2 ≤ n → generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1)))),
    (∀ᶠ n : ℕ in atTop, ReachesSearch k n → DenseBoxHits n) →
    ∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in atTop, ∀ hn : 2≤n,
      let tree := factor (fun a h => totalStepWith (fun x hx _ => tryDivisorWith x hx (fun m => (split x m).1))
        k a h (gen a h)) n hn
      (tree.work (fun a => guardedLocalWork k a + driverWork split k a + backendWork split k a):ℝ) ≤
        exp ((max 6528665845 (C₁+12*A+131117)+ε)*scale n) := by
  obtain ⟨k,gen,finish⟩ := factor_tree_of_local_bounds line split hc ha spec
  refine ⟨k,gen,fun hits => ?_⟩
  have result := finish hits (driverWork split k) 715000000 (by norm_num)
    (driver_work_bound split hc ha spec gen hits)
  norm_num only [max_eq_right (by norm_num : (715000000:ℝ)≤6528665845)] at result
  exact result

end Cogentic.Companion

#print axioms Cogentic.Companion.factor_tree_of_accounted_stages
