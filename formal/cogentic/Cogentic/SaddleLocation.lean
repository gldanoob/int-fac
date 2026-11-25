import Cogentic.PrincipalDecay

namespace Cogentic.Window
open Real Set MeasureTheory

/-- The exact positive-prime weights and the oscillatory integral agree at
    frequency zero, uniformly in the real tilt and the deleted primes. -/
theorem tilted_prime_mass (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B α : ℝ) (D : Finset ℕ), 16 ≤ B → 199/200 ≤ α → α ≤ 1 →
      let J := (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
      D ⊆ J →
      |(∑ p ∈ J \ D, (p:ℝ)^(-α)) - (∫ v in Real.log B/2..Real.log B, Real.exp ((1-α)*v)/v)| ≤
        C*(1+Real.log (3*B))^2*B^(-19/400:ℝ) + D.card*B^(-199/400:ℝ) := by
  obtain ⟨C,hC,main⟩ := fixed_principal_prime_band line
  refine ⟨C,hC,fun B α D hB lo hi => ?_⟩
  let H := Real.log B
  let J := (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
  dsimp only
  intro hD
  have pos : 0 < B := by linarith
  have hH : 0 < H := Real.log_pos (by linarith)
  have approx := main B (α:ℂ) hB lo hi (by simp; positivity)
  have r := (Complex.abs_re_le_norm _).trans approx
  rw [Complex.sub_re,Complex.re_sum] at r
  have sumReal (p : ℕ) (hp : p ∈ J) : ((p:ℂ)^(-(α:ℂ))).re = (p:ℝ)^(-α) := by
    simpa only [Complex.ofReal_zero, zero_mul, sub_zero, Real.cos_zero, mul_one] using
      prime_phase_re p (Finset.mem_filter.mp hp).2 α 0
  have integ : (∫ x in H/2..H, Real.exp ((1-α)*x)/x) =
      (∫ x in H/2..H, Complex.exp ((1-(α:ℂ))*x)/(x:ℂ)).re := by
    have ci := (primeWave_continuousOn (a := H/2) (b := H) (by linarith) (by linarith) α 0).intervalIntegrable (μ := volume)
    have eq : (∫ x in H/2..H, (primeWave α 0 x).re) = (∫ x in H/2..H, primeWave α 0 x).re :=
      intervalIntegral.intervalIntegral_re ci
    simp_rw [primeWave_re,zero_mul,Real.cos_zero,mul_one] at eq
    simpa only [primeWave,Complex.ofReal_zero,zero_mul,sub_zero] using eq
  rw [show (∑ p ∈ J, ((p:ℂ)^(-(α:ℂ))).re) = ∑ p ∈ J, (p:ℝ)^(-α) from Finset.sum_congr rfl sumReal,
    ← integ] at r
  have single (p : ℕ) (hp : p ∈ D) : (p:ℝ)^(-α) ≤ B^(-199/400:ℝ) := by
    have low := Nat.lt_of_floor_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hD hp)).1).1
    refine (Real.rpow_le_rpow_of_nonpos (Real.sqrt_pos.mpr pos) low.le (by linarith : -α ≤ 0)).trans ?_
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul pos.le]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have del : (∑ p ∈ D, (p:ℝ)^(-α)) ≤ D.card*B^(-199/400:ℝ) := by simpa using Finset.sum_le_sum single
  have d0 := Finset.sum_nonneg (s := D) (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) (-α))
  change |(∑ p ∈ J \ D, _) - _| ≤ _
  rw [Finset.sum_sdiff_eq_sub hD, abs_le]
  rw [abs_le] at r
  dsimp only [H] at r
  constructor <;> linarith [r.1,r.2]

/-- On a log band [H/2,H], the mean of the genuine Bernoulli factors is
    comparable with H times the unnormalized tilted prime mass. -/
theorem tilted_mean_bounds (J : Finset ℕ) (H α : ℝ) (hH : 0 ≤ H) (ha : 0 ≤ α)
    (band : ∀ p ∈ J, 1 ≤ p ∧ H/2 ≤ Real.log p ∧ Real.log p ≤ H) :
    H/4*(∑ p ∈ J, (p:ℝ)^(-α)) ≤ saddleMean J α ∧ saddleMean J α ≤ H*(∑ p ∈ J, (p:ℝ)^(-α)) := by
  have point (p : ℕ) (mem : p ∈ J) :
      H/4*(p:ℝ)^(-α) ≤ primeProbability α p*Real.log p ∧
      primeProbability α p*Real.log p ≤ H*(p:ℝ)^(-α) := by
    obtain ⟨hp,lo,hi⟩ := band p mem
    let w := (p:ℝ)^(-α)
    have w0 : 0 ≤ w := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have w1 : w ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp) (by linarith)
    have den : 0 < 1+w := by linarith
    have pl : w/2 ≤ primeProbability α p := by
      change w/2 ≤ w/(1+w)
      rw [le_div_iff₀ den]
      nlinarith [mul_nonneg w0 (sub_nonneg.mpr w1)]
    have pu : primeProbability α p ≤ w := by
      change w/(1+w) ≤ w
      rw [div_le_iff₀ den]; nlinarith [sq_nonneg w]
    have p0 : 0 ≤ primeProbability α p := (by linarith : 0 ≤ w/2).trans pl
    constructor
    · calc _ = w/2*(H/2) := by dsimp [w]; ring
           _ ≤ _ := mul_le_mul pl lo (by linarith) p0
    · calc _ ≤ w*H := mul_le_mul pu hi (by linarith) w0
           _ = _ := mul_comm _ _
  rw [Finset.mul_sum,Finset.mul_sum]
  exact ⟨Finset.sum_le_sum (fun p hp => (point p hp).1),Finset.sum_le_sum (fun p hp => (point p hp).2)⟩

private theorem mean_integral_bounds (H γ : ℝ) (hH : 0 < H) (hγ : 0 ≤ γ) :
    Real.exp (γ*(H/2))/2 ≤ (∫ x in H/2..H, Real.exp (γ*x)/x) ∧
      (∫ x in H/2..H, Real.exp (γ*x)/x) ≤ Real.exp (γ*H) := by
  have order : H/2 ≤ H := by linarith
  let f (x : ℝ) := Real.exp (γ*x)/x
  have continuous : ContinuousOn f (uIcc (H/2) H) := by
    intro x hx
    rw [uIcc_of_le order] at hx
    have h : x ≠ 0 := (by linarith [hx.1] : 0 < x).ne'
    dsimp [f]; fun_prop (disch := assumption)
  have hi := intervalIntegral.integral_mono_on (μ := volume) order continuous.intervalIntegrable
    (g := fun _ => Real.exp (γ*H)/(H/2)) intervalIntegrable_const (by
      intro x hx
      exact div_le_div₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.2 hγ)) (by linarith) hx.1)
  have lo := intervalIntegral.integral_mono_on (μ := volume) order
    (f := fun _ => Real.exp (γ*(H/2))/H) intervalIntegrable_const continuous.intervalIntegrable (by
      intro x hx
      exact div_le_div₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.1 hγ))
        (by linarith [hx.1]) hx.2)
  simp only [intervalIntegral.integral_const,smul_eq_mul] at lo hi
  constructor
  · convert lo using 1
    field_simp; ring
  · convert hi using 1
    field_simp; ring

/-- A genuine real saddle exists for every admissible center and deletion
    set. Its variance is between one quarter and one times log(B) log(Y). -/
theorem prime_saddle_exists (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B X : ℝ) (D : Finset ℕ), 16 ≤ B →
      C*(1+Real.log (3*B))^2*B^(-19/400:ℝ) + D.card*B^(-199/400:ℝ) ≤ 1/4 →
      2*Real.log B ≤ X → X ≤ Real.log B*B^(1/400:ℝ)/32 →
      let J := (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
      D ⊆ J →
      ∃ α ∈ Icc (199/200:ℝ) 1, saddleMean (J \ D) α = X ∧
        Real.log B*X/4 ≤ saddleVariance (J \ D) (primeProbability α) (fun p => Real.log p) ∧
        saddleVariance (J \ D) (primeProbability α) (fun p => Real.log p) ≤ Real.log B*X ∧
        Real.log B/4*(Real.exp ((1-α)*(Real.log B/2))/2-1/4) ≤ X ∧
        X ≤ Real.log B*(Real.exp ((1-α)*Real.log B)+1/4) := by
  obtain ⟨C,hC,mass⟩ := tilted_prime_mass line
  refine ⟨C,hC,fun B X D hB err xlo xhi => ?_⟩
  let H := Real.log B
  let J := (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
  let P := J \ D
  dsimp only
  intro hD
  have pos : 0 < B := by linarith
  have hH : 0 < H := Real.log_pos (by linarith)
  have band (p : ℕ) (hp : p ∈ P) : 1 ≤ p ∧ H/2 ≤ Real.log p ∧ Real.log p ≤ H := by
    obtain ⟨range,prime⟩ := Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1
    obtain ⟨low,high⟩ := Finset.mem_Ioc.mp range
    refine ⟨prime.one_le,?_,?_⟩
    · dsimp [H]; rw [← Real.log_sqrt pos.le]
      exact Real.log_le_log (Real.sqrt_pos.mpr pos) (Nat.lt_of_floor_lt low).le
    · exact Real.log_le_log (by exact_mod_cast prime.pos) ((Nat.cast_le.mpr high).trans (Nat.floor_le pos.le))
  have bounds (a : ℝ) (al : 199/200 ≤ a) (ah : a ≤ 1) :
      H/4*(Real.exp ((1-a)*(H/2))/2-1/4) ≤ saddleMean P a ∧
      saddleMean P a ≤ H*(Real.exp ((1-a)*H)+1/4) := by
    have m := (mass B a D hB al ah hD).trans err
    have i := mean_integral_bounds H (1-a) hH (sub_nonneg.mpr ah)
    have cmp := tilted_mean_bounds P H a hH.le (by linarith) band
    change |(∑ p ∈ P, (p:ℝ)^(-a)) - (∫ v in H/2..H, Real.exp ((1-a)*v)/v)| ≤ _ at m
    have ⟨l,u⟩ := abs_le.mp m
    exact ⟨(mul_le_mul_of_nonneg_left (by linarith [i.1]) (by linarith : 0 ≤ H/4)).trans cmp.1,
      cmp.2.trans (mul_le_mul_of_nonneg_left (by linarith [i.2]) hH.le)⟩
  have upper := (bounds 1 (by norm_num) le_rfl).2
  norm_num at upper
  have lower := (bounds (199/200) le_rfl (by norm_num)).1
  have poweq : Real.exp ((1-199/200)*(H/2)) = B^(1/400:ℝ) := by
    rw [Real.rpow_def_of_pos pos]; dsimp [H]; congr 1; ring
  rw [poweq] at lower
  have one := Real.one_le_rpow (by linarith : 1 ≤ B) (by norm_num : (0:ℝ) ≤ 1/400)
  have positive (p : ℕ) (hp : p ∈ P) : 0 < p := (band p hp).1
  have continuous : Continuous (saddleMean P) := continuous_iff_continuousAt.mpr
    (fun a => (saddleMean_derivative P positive a).continuousAt)
  obtain ⟨a,ha,e⟩ := intermediate_value_Icc' (by norm_num : (199/200:ℝ) ≤ 1) continuous.continuousOn
    (show X ∈ Icc (saddleMean P 1) (saddleMean P (199/200)) by
      change 2*H ≤ X at xlo
      change X ≤ H*B^(1/400:ℝ)/32 at xhi
      constructor
      · linarith
      · nlinarith [mul_nonneg hH.le (sub_nonneg.mpr one)])
  have var := prime_saddle_variance_bounds P a H (by linarith [ha.1]) hH.le
    (fun p hp => (band p hp).1) (fun p hp => (band p hp).2)
  rw [e] at var
  have place := bounds a ha.1 ha.2
  rw [e] at place
  exact ⟨a,ha,e,var.1,var.2,place⟩

private theorem located_saddle_loss (lam u : ℝ) (hu : 10 ≤ u)
    (upper : u ≤ Real.exp lam + 1/4) (lower : Real.exp (lam/2) ≤ 8*u+1) :
    2 ≤ lam ∧ u/(1152*(Real.log (8*u+1))^3) ≤ Real.exp (lam-1)/(36*lam^3) := by
  have exp1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have exp2 : Real.exp 2 < 9 := by
    rw [show (2:ℝ) = 1+1 by norm_num,Real.exp_add]
    nlinarith [mul_pos (sub_pos.mpr exp1) (by linarith [Real.exp_pos 1] : 0 < 3+Real.exp 1)]
  have hl : 2 ≤ lam := Real.exp_le_exp.mp (by linarith)
  have hlog : lam ≤ 2*Real.log (8*u+1) := by
    have lp := Real.log_le_log (Real.exp_pos _) lower
    rw [Real.log_exp] at lp
    linarith
  have lg : 0 < Real.log (8*u+1) := Real.log_pos (by linarith)
  have numer : u/4 ≤ Real.exp (lam-1) := by
    rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos 1)]
    nlinarith [mul_nonneg (by linarith : 0 ≤ u) (sub_nonneg.mpr exp1.le)]
  have denom : 36*lam^3 ≤ 288*(Real.log (8*u+1))^3 := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ lam) hlog 3
    nlinarith
  refine ⟨hl,?_⟩
  calc _ = (u/4)/(288*(Real.log (8*u+1))^3) := by ring
       _ ≤ _ := div_le_div₀ (by linarith) numer (by positivity) denom

/-- A saddle for the actual prime set and an off-center bound expressed only
    in its input scale u = log(Y)/log(B). The rate u/(log u)^3 suffices for
    the moderate-frequency exclusion at the fixed schedule. -/
theorem prime_saddle_nonresonance (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B u : ℝ) (D : Finset ℕ), 16 ≤ B →
      C*(1+Real.log (3*B))^2*B^(-19/400:ℝ) + 2*D.card*B^(-199/400:ℝ) ≤ 1/4 →
      10 ≤ u → u ≤ B^(1/400:ℝ)/32 →
      let J := (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
      D ⊆ J →
      ∃ α ∈ Icc (199/200:ℝ) 1, saddleMean (J \ D) α = Real.log B*u ∧
        2 ≤ (1-α)*Real.log B ∧ ∀ t : ℝ, 1 ≤ |t*Real.log B| → |t| ≤ B^(1/5:ℝ) →
        ‖saddleCharacteristic (J \ D) (primeProbability α) (fun p => Real.log p) t‖ ≤
          Real.exp ((1/4 - u/(1152*(Real.log (8*u+1))^3))/4) := by
  obtain ⟨c,hc,existsSaddle⟩ := prime_saddle_exists line
  obtain ⟨k,hk,bound⟩ := principal_product_off_center line
  refine ⟨max c k,le_trans hc (le_max_left ..),fun B u D hB small uLo uHi => ?_⟩
  dsimp only
  intro omitted
  have pos : 0 < B := by linarith
  have hH := Real.log_pos (by linarith : 1 < B)
  let H := Real.log B
  let eps (k : ℝ) := k*(1+Real.log (3*B))^2*B^(-19/400:ℝ)
  let del := (D.card:ℝ)*B^(-199/400:ℝ)
  have d0 : 0 ≤ del := by dsimp [del]; positivity
  have common : eps (max c k) + 2*del ≤ 1/4 := by dsimp [eps,del]; linarith
  have mono : Monotone eps := by
    intro a b hab
    dsimp [eps]; gcongr
  have ce : eps c+del ≤ 1/4 := by linarith [mono (le_max_left c k)]
  have ke : eps k+2*del ≤ 1/4 := by linarith [mono (le_max_right c k)]
  have ulo : 2*H ≤ H*u := by dsimp [H]; nlinarith [mul_nonneg hH.le (by linarith : 0 ≤ u-2)]
  have uhi : H*u ≤ H*B^(1/400:ℝ)/32 := by
    have b := mul_le_mul_of_nonneg_left uHi hH.le
    dsimp [H]; linarith
  obtain ⟨a,ha,eq,_,_,lo,hi⟩ := existsSaddle B (H*u) D hB ce ulo uhi omitted
  let lam := (1-a)*H
  have hh : 0 < H := hH
  have l : Real.exp (lam/2) ≤ 8*u+1 := by
    rw [show lam/2 = (1-a)*(H/2) by dsimp [lam]; ring]
    change H/4*(_/2-1/4) ≤ H*u at lo
    have hh' : H*(Real.exp ((1-a)*(H/2))/8-1/16) ≤ H*u := by linarith
    linarith [(mul_le_mul_iff_right₀ hh).mp hh']
  have r : u ≤ Real.exp lam+1/4 := (mul_le_mul_iff_right₀ hh).mp hi
  have ⟨ge,rate⟩ := located_saddle_loss lam u uLo r l
  refine ⟨a,ha,eq,ge,fun t th tl => ?_⟩
  refine (bound B a t D hB ha.1 ha.2 tl ge th omitted).trans (Real.exp_le_exp.mpr ?_)
  change (eps k + 2*D.card*B^(-199/400:ℝ) - Real.exp (lam-1)/(36*lam^3))/4 ≤ _
  dsimp only [del] at ke
  linarith

end Cogentic.Window
