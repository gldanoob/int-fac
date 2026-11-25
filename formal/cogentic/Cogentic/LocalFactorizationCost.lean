import Cogentic.CompanionFactorization
import Cogentic.ExhaustiveMarkCost
import Cogentic.PowerScanCost

namespace Cogentic.Companion
open Concrete TwoThirdsFactor TwoThirdsSearch TwoThirdsFinish CompanionSplitCost Real Filter

/-- Count the root setup and power scan on each driver input and the whole
candidate box only when its executable guards reach the search. -/
def guardedLocalWork (k n : ℕ) : ℕ :=
  (if 2 ≤ n then (BinaryPowerScan.run n.bits).2+(BinaryPowerScan.computedBase n.bits).2 else 0) +
  (if ReachesSearch k n then measuredSearchWork n else 0)

private theorem scale_grows : Tendsto scale atTop atTop := by
  have logs : Tendsto (fun n : ℕ => log n) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<2/3)).comp logs).atTop_mul_atTop₀
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).comp (tendsto_log_atTop.comp logs))

private theorem root_cost {n : ℕ} (hn : 64 ≤ n) :
    (((BinaryPowerScan.run n.bits).2+(BinaryPowerScan.computedBase n.bits).2 : ℕ):ℝ) ≤ exp (975*scale n) := by
  let e := 15*TwoThirdsCost.scale (n.log2+1)
  have bound := (BinaryPowerScan.driver_root_setup (n:=n) (by omega)).2.2
  have sc := binary_scale_le hn
  have ex : (e:ℝ) ≤ 975*scale n := by dsimp [e]; push_cast; linarith
  have logTwo : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _  ≤  (2:ℝ)^e := by exact_mod_cast bound
    _ = exp ((e:ℝ)*log 2) := by rw [exp_nat_mul,exp_log (by norm_num : (0:ℝ)<2)]
    _  ≤  _ := exp_le_exp.mpr (((mul_le_mul_of_nonneg_left logTwo (Nat.cast_nonneg e)).trans_eq (mul_one _)).trans ex)

/-- This supplies the front-work hypothesis at the k chosen by the companion
factorizer. The residual charge is the remaining per-node implementation work. -/
theorem guarded_front_bound {k : ℕ}
    (gen : ∀ n, 2 ≤ n → generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1))))
    (residual : ℕ → ℕ) {D δ : ℝ} (positive : 0<δ)
    (unpaid : ∀ᶠ n : ℕ in atTop, (residual n:ℝ) ≤ exp (D*scale n)) :
    ∀ᶠ n : ℕ in atTop, ((guardedLocalWork k n+residual n : ℕ):ℝ) ≤
      exp ((max D 6528665845+δ)*scale n) := by
  let T := max D 6528665845
  obtain ⟨b₀,grow⟩ := Fixed.degree_grows 130000
  filter_upwards [unpaid,eventually_ge_atTop 64,eventually_ge_atTop (2^b₀),
    scale_grows.eventually_ge_atTop (2/δ)] with n residualBound hn bitBound enough
  have hn' : 2 ≤ n := by omega
  have sv : 0 ≤ scale n := (div_nonneg (by norm_num) positive.le).trans enough
  have mono {c : ℝ} (hc : c ≤ T) : exp (c*scale n) ≤ exp (T*scale n) :=
    exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc sv)
  have root := (root_cost hn).trans (mono ((by norm_num : (975:ℝ) ≤ 6528665845).trans (le_max_right ..)))
  have search : ((if ReachesSearch k n then measuredSearchWork n else 0 : ℕ):ℝ) ≤ exp (T*scale n) := by
    by_cases gate : ReachesSearch k n
    · rw [if_pos gate]
      have bits := (Nat.le_log2 (show n≠0 by omega)).mpr bitBound
      have composite : ¬n.Prime := fun p => by
        have yes := (primeCheck_correct _ _ (gen n hn')).mpr p
        simp [gate.2.2.1] at yes
      apply (measured_search_L_two_thirds hn (grow _ (by omega)) composite gate.2.2.2.2.2).trans
      apply mono
      exact le_trans (by norm_num) (le_max_right D 6528665845)
    · simp only [if_neg gate,Nat.cast_zero]; exact (exp_pos _).le
  have slack : 3 ≤ exp (δ*scale n) := by
    have extra := (div_le_iff₀ positive).mp enough
    linarith only [extra,add_one_le_exp (δ*scale n),mul_comm δ (scale n)]
  simp only [guardedLocalWork,if_pos hn',Nat.cast_add] at root search ⊢
  calc
    _  ≤  exp (T*scale n)+exp (T*scale n)+exp (T*scale n) :=
      add_le_add (add_le_add root search) (residualBound.trans (mono (le_max_left ..)))
    _  ≤  exp ((T+δ)*scale n) := by
      rw [add_mul,exp_add]
      linarith only [mul_le_mul_of_nonneg_left slack (exp_pos (T*scale n)).le]

/-- Only the runtime conclusion of the guarded factorization theorem is
specialized here. The hit hypothesis and the residual bound are both explicit. -/
theorem factor_tree_of_local_bounds (line : DirichletLZerosOnLine)
    (split : Splitter) {C₁ A : ℝ} (hc : 0 ≤ C₁) (ha : 0 ≤ A) (spec : SplitterSpec split C₁ A) :
    ∃ (k : ℕ) (gen : ∀ n, 2 ≤ n → generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1)))),
    (∀ᶠ n : ℕ in atTop, ReachesSearch k n → DenseBoxHits n) →
    ∀ (residual : ℕ → ℕ) (D : ℝ), 0 ≤ D → (∀ᶠ n : ℕ in atTop, (residual n:ℝ) ≤ exp (D*scale n)) →
    ∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
      let tree := factor (fun a h => totalStepWith (fun x hx _ => tryDivisorWith x hx (fun m => (split x m).1))
        k a h (gen a h)) n hn
      (tree.work (fun a => guardedLocalWork k a+residual a+backendWork split k a):ℝ) ≤
        exp ((max (max D 6528665845) (C₁+12*A+131117)+ε)*scale n) := by
  obtain ⟨k,gen,finish⟩ := factorization_of_dense_box_hits line split hc ha spec
  refine ⟨k,gen,?_⟩
  intro hits residual D hD unpaid ε ep
  let T := max D 6528665845
  let B := C₁+12*A+131117
  have δp : 0<ε/2 := by linarith
  have tp : 0 ≤ T := hD.trans (le_max_left ..)
  have front := guarded_front_bound gen residual δp unpaid
  obtain ⟨n₀,_,result⟩ := finish hits (fun n => guardedLocalWork k n+residual n)
    (T+ε/2) (add_nonneg tp δp.le) front (ε/2) δp
  filter_upwards [eventually_ge_atTop n₀,scale_grows.eventually_ge_atTop 0] with n large sv
  intro hn tree
  have cost := ((result n hn).2.2.2 large)
  have coef : max (T+ε/2) B+ε/2 ≤ max T B+ε := by
    have upper : max (T+ε/2) B ≤ max T B+ε/2 :=
      max_le (add_le_add (le_max_left T B) (le_refl (ε/2))) ((le_max_right T B).trans (by linarith))
    linarith
  exact cost.trans (exp_le_exp.mpr (mul_le_mul_of_nonneg_right coef sv))

end Cogentic.Companion

#print axioms Cogentic.Companion.guarded_front_bound
#print axioms Cogentic.Companion.factor_tree_of_local_bounds
