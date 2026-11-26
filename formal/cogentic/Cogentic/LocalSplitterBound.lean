import Cogentic.SplitterCost
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Cogentic.BinarySplitter

open Real BinaryModularPower

private theorem width_le_log {n : ℕ} (hn : 2 ≤ n) :
    ((n.log2+1 : ℕ) : ℝ) ≤ 4*log n := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have ln := log_le_log (by norm_num : (0:ℝ) < 2) hn'
  have base := log2_le_logb n
  rw [logb,le_div_iff₀ (log_pos (by norm_num))] at base
  have twice := mul_le_mul_of_nonneg_left (show (1/2:ℝ) ≤ log 2 by linarith [log_two_gt_d9])
    (Nat.cast_nonneg (α:=ℝ) n.log2)
  push_cast
  linarith [log_two_gt_d9]

private theorem budget_bound (B E : ℕ) (bp : 0 < B) (ep : 0 < E) :
    E+B*(baseBudget B E B+1)+8 ≤ 2048*E*B^4 := by
  obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero bp.ne'
  obtain ⟨e,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ep.ne'
  simp only [Nat.succ_eq_add_one,baseBudget,scanStepBudget,powerBudget,gcdBudget]
  ring_nf
  omega

set_option maxHeartbeats 600000 in
/-- The bit-linear exponent cost and any polynomial setup cost fit the
local splitter time bound. -/
theorem local_splitter_bound (k M D : ℕ) :
    ∃ C₁ A : ℝ, 0 ≤ C₁ ∧ 0 ≤ A ∧ (∀ n m : ℕ, 4 ≤ n → 2 ≤ m →
      (((splitter n m (List.range' 1 (polyCutoff k (n.log2+1)))).2 +
        (M*(k+(n.log2+1)+1))^D : ℕ) : ℝ) ≤
        C₁ * exp (A * sqrt (log n) * log (log ((n : ℝ)+16))) * log m * (log n)^2) := by
  let K : ℝ := 1000*((k:ℝ)+5)
  let J : ℝ := (M:ℝ)*((k:ℝ)+5)
  refine ⟨8192*K^24+2*J^D,22+D,by positivity,by positivity,?_⟩
  intro n m hn hm
  let b := n.log2+1
  let B := polyCutoff k b
  let gs := List.range' 1 B
  have one : 1 ≤ log n := by
    have lo := log_le_log (by norm_num : (0:ℝ) < 4) (show (4:ℝ) ≤ n by exact_mod_cast hn)
    rw [show (4:ℝ)=2^2 by norm_num,log_pow] at lo
    norm_num at lo
    linarith [log_two_gt_d9]
  have cap : b ≤ B := by
    unfold B polyCutoff
    have step : b ≤ 1000*(k+b+1) := by omega
    have one' : 1 ≤ 1000*(k+b+1) := by omega
    exact step.trans (by simpa using Nat.pow_le_pow_right one' (show 1 ≤ 6 by decide))
  have bp : 0 < B := (Nat.succ_pos n.log2).trans_le cap
  have ns : n.size ≤ B := (Nat.size_le.mpr Nat.lt_log2_self).trans cap
  have gsBound (g : ℕ) (hg : g∈gs) : g.size ≤ B := by
    have hi := (List.mem_range'_1.mp hg).2
    exact (Nat.size_le_size (by omega : g ≤ B)).trans (Nat.size_le.mpr Nat.lt_two_pow_self)
  have raw := (splitter_spec n m B gs (by omega) (by omega) gsBound).2
  rw [show gs.length=B from List.length_range'] at raw
  have budget : baseBudget B m.size n.size ≤ baseBudget B m.size B := by
    unfold baseBudget scanStepBudget powerBudget gcdBudget
    gcongr
  have ep : 0 < m.size := by
    by_contra! h
    have h' := Nat.size_le.mp h
    simp at h'
    omega
  have charge : (splitter n m gs).2 ≤ 2048*m.size*B^4 := by
    have raw' : (splitter n m gs).2 ≤ m.size+B*(baseBudget B m.size B+1) := raw.trans (by gcongr)
    exact (raw'.trans (Nat.le_add_right _ 8)).trans (budget_bound B m.size bp ep)
  have expo : (m.size:ℝ) ≤ 4*log m :=
    (Nat.cast_le.mpr (Nat.size_le.mpr Nat.lt_log2_self)).trans (width_le_log hm)
  have bnd : (b:ℝ) ≤ 4*log n := width_le_log (by omega)
  have basic : (k:ℝ)+b+1 ≤ ((k:ℝ)+5)*log n := by
    have hk := mul_le_mul_of_nonneg_left one (show 0 ≤ (k:ℝ)+1 by positivity)
    linarith only [hk,bnd]
  have base : (1000:ℝ)*((k:ℝ)+b+1) ≤ K*log n := by
    dsimp only [K]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left basic (by norm_num)
  have Bnd : (B:ℝ)^4 ≤ K^24*(log n)^24 := by
    change (((1000*(k+b+1))^6 : ℕ):ℝ)^4 ≤ _
    push_cast
    rw [←pow_mul,show 6*4=24 by decide,←mul_pow]
    exact pow_le_pow_left₀ (by positivity) base _
  have shift : log (log n) ≤ log (log ((n:ℝ)+16)) := by
    have np : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
    apply log_le_log (by linarith)
    exact log_le_log np (by linarith)
  let t := sqrt (log n)*log (log ((n:ℝ)+16))
  have sq : 1 ≤ sqrt (log n) := by simpa using sqrt_le_sqrt one
  have ln : 0 ≤ log (log ((n:ℝ)+16)) := (log_nonneg one).trans shift
  have tp : 0 ≤ t := mul_nonneg (sqrt_nonneg _) ln
  have inner : log (log n) ≤ t :=
    shift.trans (by simpa using mul_le_mul_of_nonneg_right sq ln)
  have absorbed (d : ℕ) : (log n)^d ≤ exp ((d:ℝ)*t) := by
    rw [←exp_log (show 0 < log n by linarith),←exp_nat_mul]
    apply exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left inner (Nat.cast_nonneg _)
  let F := exp ((22+(D:ℝ))*t)
  have F22 : (log n)^22 ≤ F := (absorbed 22).trans (exp_le_exp.mpr (by
    norm_num
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Nat.cast_nonneg D)) tp))
  have FD : (log n)^D ≤ F := (absorbed D).trans (exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by norm_num)) tp))
  have lm : 1/2 ≤ log m :=
    (by linarith [log_two_gt_d9] : (1/2:ℝ) ≤ log 2).trans
      (log_le_log (by norm_num : (0:ℝ) < 2) (Nat.cast_le.mpr hm))
  have mp : 0 ≤ log m := by linarith
  have rawBound : ((splitter n m gs).2:ℝ) ≤ (8192*K^24)*F*log m*(log n)^2 := by
    calc
      _ ≤ 2048*(m.size:ℝ)*(B:ℝ)^4 := by exact_mod_cast charge
      _ ≤ 2048*(4*log m)*(K^24*(log n)^24) := by gcongr
      _ = (8192*K^24)*(log n)^22*log m*(log n)^2 := by ring
      _ ≤ _ := by gcongr
  have setup : (((M*(k+b+1))^D : ℕ):ℝ) ≤ (2*J^D)*F*log m*(log n)^2 := by
    calc
      _ ≤ (J*log n)^D := by
        push_cast
        apply pow_le_pow_left₀ (by positivity)
        dsimp only [J]
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left basic (Nat.cast_nonneg _)
      _ = J^D*(log n)^D := mul_pow _ _ _
      _ ≤ J^D*F := by gcongr
      _ = (2*J^D)*F*(1/2)*1^2 := by ring
      _ ≤ _ := by
        have left := mul_le_mul_of_nonneg_left lm (show 0 ≤ (2*J^D)*F by positivity)
        have right := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) one 2
        exact mul_le_mul left right (by norm_num) (by positivity)
  rw [mul_assoc (22+(D:ℝ)) (sqrt (log n)) (log (log ((n:ℝ)+16)))]
  change (((splitter n m gs).2+(M*(k+b+1))^D : ℕ):ℝ) ≤
    (8192*K^24+2*J^D)*F*log m*(log n)^2
  rw [Nat.cast_add]
  exact (add_le_add rawBound setup).trans_eq (by ring)

end Cogentic.BinarySplitter

#print axioms Cogentic.BinarySplitter.local_splitter_bound
