import Cogentic.Concrete

namespace Cogentic.Concrete
open TwoThirdsSearch Real

private theorem log2_bound {n : ℕ} (hn : 0 < n) :
    (n.log2:ℝ) ≤ 2*log n := by
  have lower := log_le_log (by positivity : (0:ℝ)<2^n.log2)
    (by exact_mod_cast Nat.log2_self_le hn.ne' : (2:ℝ)^n.log2 ≤ n)
  rw [log_pow] at lower
  have half : (1/2:ℝ) ≤ log 2 := by
    have t := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1/2)
    rw [log_div (by norm_num) (by norm_num),log_one] at t
    linarith
  linarith [mul_le_mul_of_nonneg_left half (Nat.cast_nonneg (α := ℝ) n.log2)]

/-- Convert the rounded binary search scale to the natural logarithms in
the definition of L_N. -/
theorem two_thirds_scale {n : ℕ} (large : 3 ≤ log n) :
    (Fixed.v (n.log2+1):ℝ) ≤ 5*(log n)^(2/3:ℝ)*(log (log n))^(1/3:ℝ) := by
  have np : 0 < n := by
    by_contra! h
    have eq : n=0 := by omega
    rw [eq] at large
    norm_num at large
  let L := log n
  let b := n.log2+1
  let z := Fixed.z b
  have lp : 0 < L := by dsimp [L]; linarith
  have ll : 1 ≤ log L := (le_log_iff_exp_le lp).mpr (by
    dsimp [L]; linarith [exp_one_lt_d9])
  have bb : (b:ℝ) ≤ 3*L := by dsimp [b,L]; push_cast; linarith [log2_bound np]
  have bp : 0 < b := Nat.succ_pos _
  have logb := log_le_log (by exact_mod_cast bp : (0:ℝ)<b) bb
  rw [log_mul (by norm_num) lp.ne'] at logb
  have zz : (z:ℝ) ≤ 9*log L := by
    dsimp [z,Fixed.z]; push_cast
    linarith [log2_bound bp,log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)]
  have top : (Fixed.v b:ℝ)^3 ≤ (b:ℝ)^2*z := by exact_mod_cast (Fixed.rounding_bounds bp).2.2.1
  apply le_of_pow_le_pow_left₀ (n := 3) (by decide) (by positivity)
  change (Fixed.v b:ℝ)^3 ≤ (5*L^(2/3:ℝ)*(log L)^(1/3:ℝ))^3
  have powr (x : ℝ) (hx : 0 ≤ x) (a : ℝ) : (x^a)^3 = x^(a*3) := by
    rw [← rpow_natCast (x^a) 3,← rpow_mul hx]; norm_num
  rw [mul_pow,mul_pow,powr _ lp.le,powr _ (by linarith : 0 ≤ log L)]
  norm_num
  calc
    _ ≤ (b:ℝ)^2*z := top
    _ ≤ (3*L)^2*(9*log L) := by gcongr
    _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg L) (by linarith : 0 ≤ log L)]

/-- The total number of outer trials times the maximum inner minor count,
expressed directly in standard L notation for the input N. -/
theorem candidate_count_L_two_thirds :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ hn : 2 ≤ n,
      let b := n.log2+1
      let calls := (collect hn (searchBox n (2*b^2*Fixed.U b*Fixed.A b) (2*b^2*Fixed.U b)
        (candidate n)) (dyadicTargets (Fixed.beta b)).sort).2
      ((calls*2^(20000*Fixed.v b):ℕ):ℝ) ≤
        exp (2100005*(log n)^(2/3:ℝ)*(log (log n))^(1/3:ℝ)) := by
  obtain ⟨b₀,estimate⟩ := search_with_minor_choices 1 (by decide)
  refine ⟨max (2^b₀) 64,fun n big hn => ?_⟩
  let b := n.log2+1
  have bp : b₀ ≤ b := Nat.le_trans ((Nat.le_log2 (by omega : n ≠ 0)).mpr ((le_max_left ..).trans big)) (Nat.le_succ _)
  have n64 : 64 ≤ n := (le_max_right ..).trans big
  have large : 3 ≤ log n := (le_log_iff_exp_le (by exact_mod_cast (show 0<n by omega))).mpr (by
    have cube := pow_le_pow_left₀ (exp_pos 1).le (le_of_lt exp_one_lt_d9) 3
    have e : exp 3 = (exp 1)^3 := by rw [← exp_nat_mul]; norm_num
    rw [e]; refine cube.trans ?_; have ax : (64:ℝ) ≤ n := by exact_mod_cast n64
    linarith)
  have count := estimate b bp n hn
  dsimp only
  refine (show _ ≤ (2:ℝ)^(420001*Fixed.v b) by
    exact_mod_cast (by simpa only [Nat.div_one,show 420000*Fixed.v b+Fixed.v b=420001*Fixed.v b by omega] using count)).trans ?_
  conv_lhs => rw [← exp_log (by norm_num : (0:ℝ)<2),← exp_nat_mul]
  apply exp_le_exp.mpr
  push_cast
  have changeScale := two_thirds_scale large
  have ln2 : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    420001*(Fixed.v b:ℝ)*log 2 ≤ 420001*(Fixed.v b:ℝ) := by nlinarith [mul_le_mul_of_nonneg_left ln2 (Nat.cast_nonneg (α:=ℝ) (Fixed.v b))]
    _ ≤ 420001*(5*(log n)^(2/3:ℝ)*(log (log n))^(1/3:ℝ)) := by gcongr
    _ = _ := by ring

end Cogentic.Concrete
