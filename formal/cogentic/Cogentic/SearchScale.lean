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


/-- Rounding the two binary logarithms contributes only constant additive
errors before taking the cube root of the search scale. -/
theorem sharp_binary_scale (δ : ℝ) (pos : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (Fixed.v (n.log2+1):ℝ)*log 2 ≤
        (1+δ)*((log n)^(2/3:ℝ)*(log (log n))^(1/3:ℝ)) := by
  have logs : Filter.Tendsto (fun n : ℕ => log n) Filter.atTop Filter.atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have logs₂ := tendsto_log_atTop.comp logs
  have lp : 0 < log (2:ℝ) := log_pos (by norm_num)
  have length (a : ℕ) (ha : 0<a) :
      ((a.log2+1:ℕ):ℝ)*log 2 ≤ log a + log 2 := by
    have le := log_le_log (by positivity : (0:ℝ)<2^a.log2)
      (by exact_mod_cast Nat.log2_self_le ha.ne' : (2:ℝ)^a.log2 ≤ a)
    rw [log_pow] at le
    push_cast; linarith
  filter_upwards [Filter.eventually_ge_atTop 2,logs.eventually_ge_atTop 1,
    logs.eventually_ge_atTop (log 2/δ),logs₂.eventually_ge_atTop ((log 3+log 2)/δ)] with n hn hL h₁ h₂
  let L := log n
  let b := n.log2+1
  let z := Fixed.z b
  change 1≤L at hL
  change log 2/δ≤L at h₁
  change (log 3+log 2)/δ≤log L at h₂
  have bp : 0<b := Nat.succ_pos _
  have bit := length n (by omega)
  change (b:ℝ)*log 2 ≤ L+log 2 at bit
  have bit' : (b:ℝ)*log 2 ≤ (1+δ)*L := by linarith [(div_le_iff₀ pos).mp h₁]
  have bb : (b:ℝ) ≤ 3*L := by
    dsimp only [b,L] at *; push_cast
    linarith [log2_bound (show 0<n by omega)]
  have zlog := length b bp
  have logb := log_le_log (by exact_mod_cast bp : (0:ℝ)<b) bb
  rw [log_mul (by norm_num) (by linarith : L≠0)] at logb
  have z' : (z:ℝ)*log 2 ≤ (1+δ)*log L := by
    change (z:ℝ)*log 2 ≤ _ at zlog
    linarith [(div_le_iff₀ pos).mp h₂]
  have rnd : (Fixed.v b:ℝ)^3 ≤ (b:ℝ)^2*z := by exact_mod_cast (Fixed.rounding_bounds bp).2.2.1
  have logpos : 0≤log L := log_nonneg hL
  have realpow (x : ℝ) (hx : 0≤x) (a : ℝ) : (x^a)^3=x^(a*3) := by
    rw [←rpow_natCast (x^a) 3,←rpow_mul hx]; norm_num
  change _ ≤ (1+δ)*(L^(2/3:ℝ)*(log L)^(1/3:ℝ))
  apply le_of_pow_le_pow_left₀ (n:=3) (by decide) (by positivity)
  calc
    ((Fixed.v b:ℝ)*log 2)^3 ≤ ((b:ℝ)^2*z)*(log 2)^3 := by rw [mul_pow]; gcongr
    _ = ((b:ℝ)*log 2)^2*((z:ℝ)*log 2) := by ring
    _ ≤ ((1+δ)*L)^2*((1+δ)*log L) := by gcongr
    _ = _ := by
      rw [mul_pow (1+δ) (_*_ : ℝ) 3,mul_pow _ _ 3,realpow _ (by linarith : 0≤L),realpow _ logpos]
      norm_num
      ring

/-- A uniformly polynomial-time extractor on the fixed schedule has per-call
charge 2^(O(h)). Such a charge preserves the leading 400000 coefficient of
the exhaustive search, including rounding to the binary schedule. -/
theorem search_work_leading (attempt : ℕ → TryPair) (k : ℕ) (ε : ℝ) (pos : 0<ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ hn : 2≤n,
      let b := n.log2+1
      let calls := (collect hn (searchBox n (2*b^2*Fixed.U b*Fixed.A b) (2*b^2*Fixed.U b)
        (attempt n)) (dyadicTargets (Fixed.beta b)).sort).2
      (calls:ℝ)*(2:ℝ)^(k*Fixed.h b) ≤
        exp ((400000+ε)*((log n)^(2/3:ℝ)*(log (log n))^(1/3:ℝ))) := by
  let η := min (ε/800004) (1/2)
  have hp : 0<η := lt_min (by positivity) (by norm_num)
  obtain ⟨j,hj⟩ := exists_nat_gt (1/η)
  have jp : 0<j := by exact_mod_cast (by positivity : (0:ℝ)<1/η).trans hj
  obtain ⟨b₀,estimate⟩ := Fixed.search_calls_leading j jp
  obtain ⟨b₁,degree⟩ := Fixed.degree_grows (j*k)
  filter_upwards [sharp_binary_scale η hp, Filter.eventually_ge_atTop (2^(max b₀ b₁)),
    Filter.eventually_ge_atTop 3] with n scaleBound size big
  intro hn b calls
  have bb := (Nat.le_log2 (show n≠0 by omega)).mpr size
  have cost := estimate b (by dsimp [b]; omega) n hn (attempt n)
  have deg := degree b (by dsimp [b]; omega)
  have times : (k*Fixed.h b)*j ≤ Fixed.v b := by
    change _ ≤ Fixed.d b*Fixed.h b
    calc _ = (j*k)*Fixed.h b := by ring
         _ ≤ _ := Nat.mul_le_mul_right _ deg
  have ep : (Fixed.v b/j:ℕ) ≤ (η*(Fixed.v b:ℝ)) := by
    have a : ((Fixed.v b/j:ℕ):ℝ)*j ≤ Fixed.v b := by exact_mod_cast Nat.div_mul_le_self (Fixed.v b) j
    have b' := (div_lt_iff₀ hp).mp hj
    have t := mul_le_mul_of_nonneg_right b'.le (Nat.cast_nonneg (α:=ℝ) (Fixed.v b))
    apply (mul_le_mul_iff_left₀ (show 0<(j:ℝ) by exact_mod_cast jp)).mp
    nlinarith only [a,t]
  have kh : (k*Fixed.h b:ℕ) ≤ η*(Fixed.v b:ℝ) := by
    exact (Nat.cast_le.mpr ((Nat.le_div_iff_mul_le jp).mpr times)).trans ep
  let V := (log n)^(2/3:ℝ)*(log (log n))^(1/3:ℝ)
  have vpos : 0≤V := mul_nonneg (rpow_nonneg (log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))) _)
    (rpow_nonneg (log_nonneg (by
      apply (le_log_iff_exp_le (by positivity)).mpr
      have : (3:ℝ)≤n := by exact_mod_cast big
      linarith [exp_one_lt_d9])) _)
  have cap : (400000+2*η)*(1+η) ≤ 400000+ε := by
    have e := min_le_left (ε/800004) (1/2:ℝ)
    have u := min_le_right (ε/800004) (1/2:ℝ)
    change η≤_ at e u
    nlinarith [mul_le_mul_of_nonneg_left u hp.le]
  have bin : calls*2^(k*Fixed.h b) ≤ 2^(400000*Fixed.v b+Fixed.v b/j+k*Fixed.h b) := by
    rw [pow_add]; exact Nat.mul_le_mul_right _ cost
  calc
    _ ≤ (2:ℝ)^(400000*Fixed.v b+Fixed.v b/j+k*Fixed.h b) := by exact_mod_cast bin
    _ = exp ((((400000*Fixed.v b+Fixed.v b/j+k*Fixed.h b:ℕ):ℝ))*log 2) := by rw [exp_nat_mul,exp_log (by norm_num : (0:ℝ)<2)]
    _ ≤ exp ((400000+2*η)*((Fixed.v b:ℝ)*log 2)) := by
      apply exp_le_exp.mpr
      push_cast
      rw [←mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (log_pos (by norm_num)).le
      push_cast at kh
      linarith [ep,kh]
    _ ≤ exp ((400000+ε)*V) := by
      apply exp_le_exp.mpr
      calc _ ≤ (400000+2*η)*((1+η)*V) := mul_le_mul_of_nonneg_left scaleBound (by positivity)
           _ ≤ _ := by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right cap vpos

end Cogentic.Concrete
