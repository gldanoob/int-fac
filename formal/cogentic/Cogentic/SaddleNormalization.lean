import Cogentic.FixedPrincipalMass

namespace Cogentic.Window
open Real

/-- Normalize the explicit central-arc remainder using the mean and the
largest prime probability. The first two terms charge deletions and
Bernoulli squares, and the last term charges the saddle expansion. -/
theorem insertion_error_bound {J : Finset ℕ} (r ell : ℕ → ℝ) {H u omitted m : ℝ}
    (hp : 0 < H) (up : 0 < u) (dp : 0 ≤ omitted) (mp : 0 ≤ m)
    (r0 : ∀ p ∈ J, 0 ≤ r p) (rmax : ∀ p ∈ J, r p ≤ m)
    (band : ∀ p ∈ J, H/2 ≤ ell p ∧ ell p ≤ H)
    (mean : ∑ p ∈ J, r p*ell p = H*u) :
    let V := poissonMoment J r ell 2
    H^2*u/2 ≤ V ∧ V ≤ H^2*u ∧
    insertionError J r ell H omitted ≤ (4*omitted+16*u*m)*sqrt u +
      (8000*(exp 1+3)*saddleEdgeworthConstant)/u^2 ∧
    4*(H^2/V)+insertionError J r ell H omitted ≤ 8/u+
      (4*omitted+16*u*m)*sqrt u +
      (8000*(exp 1+3)*saddleEdgeworthConstant)/u^2 := by
  intro V
  have pos (p) (h : p ∈ J) : 0 ≤ ell p := (by linarith : 0 ≤ H/2).trans (band p h).1
  have vlo : H/2*(∑ p ∈ J, r p*ell p) ≤ V := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p h
    have t := mul_le_mul_of_nonneg_right (band p h).1 (mul_nonneg (r0 p h) (pos p h))
    nlinarith only [t]
  have vhi : V ≤ H*(∑ p ∈ J, r p*ell p) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p h
    have t := mul_le_mul_of_nonneg_right (band p h).2 (mul_nonneg (r0 p h) (pos p h))
    nlinarith only [t]
  have mass : H/2*(∑ p ∈ J, r p) ≤ ∑ p ∈ J, r p*ell p := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun p h => by simpa [mul_comm] using mul_le_mul_of_nonneg_left (band p h).1 (r0 p h))
  rw [mean] at vlo vhi mass
  have v0 : H^2*u/2 ≤ V := by linarith only [vlo]
  have v1 : V ≤ H^2*u := by linarith only [vhi]
  have vp : 0 < V := (by positivity : 0 < H^2*u/2).trans_le v0
  have sum : (∑ p ∈ J, r p) ≤ 2*u := by
    apply (mul_le_mul_iff_right₀ hp).mp
    linarith only [mass]
  have sq : (∑ p ∈ J, (r p)^2) ≤ 2*u*m := by
    calc _ ≤ ∑ p ∈ J, r p*m := Finset.sum_le_sum (fun p h => by rw [sq]; exact mul_le_mul_of_nonneg_left (rmax p h) (r0 p h))
         _ = (∑ p ∈ J, r p)*m := (Finset.sum_mul ..).symm
         _ ≤ _ := mul_le_mul_of_nonneg_right sum mp
  let s := sqrt (2*π/V)
  have sp : 0 < s := sqrt_pos.mpr (by positivity)
  have sv := sq_sqrt (show 0 ≤ 2*π/V by positivity)
  change s^2=2*π/V at sv
  have id : 2*π=V*s^2 := by rw [sv]; field_simp
  have scale : 1 ≤ s*(H*sqrt u) := by
    apply le_of_pow_le_pow_left₀ (n:=2) (by decide) (by positivity)
    rw [mul_pow,mul_pow,sq_sqrt up.le,one_pow]
    nlinarith only [id,mul_le_mul_of_nonneg_right v1 (sq_nonneg s),pi_gt_three]
  have z : H^2/V ≤ 2/u := (div_le_div_iff₀ vp up).mpr (by linarith only [v0])
  have z2 : H^4/V^2 ≤ 4/u^2 := by
    have pow := pow_le_pow_left₀ (by positivity : 0≤H^2/V) z 2
    norm_num [div_pow,←pow_mul] at pow ⊢
    exact pow
  have pair : sqrt (3*π/V) ≤ 2*s := by
    apply le_of_pow_le_pow_left₀ (n:=2) (by decide) (by positivity)
    rw [sq_sqrt (by positivity),mul_pow,sv]
    have t := div_nonneg pi_pos.le vp.le
    simpa only [div_eq_mul_inv] using (show 3*π*V⁻¹ ≤ 2^2*(2*π*V⁻¹) by
      rw [div_eq_mul_inv] at t
      linarith only [t])
  let c := 1000*(exp 1+3)*saddleEdgeworthConstant
  have c0 : 0 ≤ c := mul_nonneg (by positivity) saddleEdgeworthConstant_nonneg
  have sums : 4/H*omitted+8/H*(∑ p ∈ J, (r p)^2) ≤ ((4*omitted+16*u*m)*sqrt u)*s := by
    apply (mul_le_mul_iff_left₀ hp).mp
    have rhs := mul_le_mul_of_nonneg_left scale (show 0≤4*omitted+16*u*m by positivity)
    have clearH : (4/H*omitted+8/H*(∑ p ∈ J, (r p)^2))*H =
        4*omitted+8*(∑ p ∈ J, (r p)^2) := by field_simp
    rw [clearH]
    nlinarith only [rhs,sq]
  have edge := mul_le_mul_of_nonneg_left (mul_le_mul z2 pair (sqrt_nonneg _) (by positivity)) c0
  have total : (4/H*omitted+8/H*(∑ p ∈ J, (r p)^2)+c*(H^4/V^2*sqrt (3*π/V)))/s ≤
      (4*omitted+16*u*m)*sqrt u+8*c/u^2 := by
    apply (div_le_iff₀ sp).mpr
    exact (add_le_add sums edge).trans_eq (by ring)
  refine ⟨v0,v1,total.trans_eq (by dsimp only [c]; ring),?_⟩
  exact (add_le_add (mul_le_mul_of_nonneg_left z (by norm_num : (0:ℝ) ≤ 4)) total).trans_eq (by dsimp only [c]; ring)

/-- Uniform lower bound for the central mass on the fixed prime band.
The shift permits the removal of up to two specified prime factors. -/
theorem fixed_central_mass_lower (k : ℕ) :
    ∃ b₀ : ℕ, ∀ b ≥ b₀, ∀ (u α a : ℝ) (D : Finset ℕ),
      let B := (Fixed.B b:ℝ)
      let H := log B
      let J := (Finset.Ioc ⌊sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
      90*(Fixed.d b:ℝ) ≤ u → u ≤ 110*(Fixed.d b:ℝ) → 199/200 ≤ α →
      saddleMean J α = H*u → |a| ≤ 2*H → D.card ≤ b^k → D ⊆ J →
      1/(2*H*sqrt u) ≤ omittedMass J D (primeProbability α) (fun p => log p) H a := by
  let C := 8000*(exp 1+3)*saddleEdgeworthConstant
  have c0 : 0 ≤ C := mul_nonneg (by positivity) saddleEdgeworthConstant_nonneg
  obtain ⟨n₀,overhead⟩ := fixed_prime_overhead 0 le_rfl (k+4)
  obtain ⟨n₁,deg⟩ := Fixed.degree_grows (max 50000 ⌈8*C⌉₊)
  refine ⟨max n₀ n₁,?_⟩
  intro b big u α a D B H J ulo uhi ha mean shift card sub
  obtain ⟨b₀,b₁⟩ := max_le_iff.mp big
  have hdeg := deg b b₁
  have hd : 50000 ≤ Fixed.d b := (le_max_left ..).trans hdeg
  have hb := Fixed.degree_le_bits b
  have d0 : 50000 ≤ (Fixed.d b:ℝ) := by exact_mod_cast hd
  have bs : 50000 ≤ (b:ℝ) := by exact_mod_cast hd.trans hb
  have db : (Fixed.d b:ℝ) ≤ b := by exact_mod_cast hb
  have c1 : 8*C ≤ (Fixed.d b:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right ..).trans hdeg)
  have up : 0 < u := by linarith
  have hp : 0 < H := by
    have := (fixed_band_log_bounds b (by omega) (by omega)).1
    change 1000*(Fixed.d b:ℝ) ≤ H at this
    linarith
  have bp : 0 < B := by dsimp [B,Fixed.B]; positivity
  have b1 : 1 ≤ B := (one_le_exp hp.le).trans_eq (exp_log bp)
  let m := B^(-199/400:ℝ)
  let r := primeProbability α
  have mp : 0 ≤ m := rpow_nonneg bp.le _
  have r0 (p) (_ : p ∈ J) : 0 ≤ r p := by dsimp [r,primeProbability]; positivity
  have rmax (p) (mem : p ∈ J) : r p ≤ m := by
    let w := (p:ℝ)^(-α)
    have w0 : 0 ≤ w := rpow_nonneg (Nat.cast_nonneg _) _
    have low := Nat.lt_of_floor_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp mem).1).1
    have bound := rpow_le_rpow_of_nonpos (sqrt_pos.mpr bp) low.le (by linarith : -α ≤ 0)
    rw [sqrt_eq_rpow,←rpow_mul bp.le] at bound
    change w/(1+w) ≤ m
    refine le_trans ((div_le_iff₀ (by linarith : 0 < 1+w)).mpr (by nlinarith [sq_nonneg w]) : w/(1+w)≤w) ?_
    exact bound.trans (rpow_le_rpow_of_exponent_le b1 (by linarith))
  have band (p) (mem : p ∈ J) : H/2 ≤ log p ∧ log p ≤ H := by
    obtain ⟨h,pp⟩ := Finset.mem_filter.mp mem
    obtain ⟨lo,hi⟩ := Finset.mem_Ioc.mp h
    constructor
    · dsimp [H]; rw [←log_sqrt bp.le]
      exact log_le_log (sqrt_pos.mpr bp) (Nat.lt_of_floor_lt lo).le
    · exact log_le_log (by exact_mod_cast pp.pos) ((Nat.cast_le.mpr hi).trans (Nat.floor_le bp.le))
  have cap := overhead b b₀ (Finset.range (b^(k+4))) (by simp)
  simp only [Finset.card_range,Nat.cast_pow,zero_mul,zero_add] at cap
  change (b:ℝ)^(k+4)*m ≤ 1/4 at cap
  have bpow : 1 ≤ (b:ℝ)^k := one_le_pow₀ (by linarith)
  have pc : (D.card:ℝ) ≤ (b:ℝ)^k := by exact_mod_cast card
  have root : sqrt u ≤ b := by
    apply (sqrt_le_left (Nat.cast_nonneg (α:=ℝ) b)).mpr
    have large := mul_nonneg (show 0 ≤ (b:ℝ)-110 by linarith only [bs]) (Nat.cast_nonneg (α:=ℝ) b)
    nlinarith only [uhi,db,large]
  have p4 : (4*(D.card:ℝ)+16*u)*sqrt u ≤ (b:ℝ)^(k+4) := by
    have ub : u ≤ 110*b := by linarith only [uhi,db]
    have coeff : 4*(D.card:ℝ)+16*u ≤ (b:ℝ)^k*(4+1760*b) := by
      nlinarith only [pc,ub,mul_le_mul_of_nonneg_right bpow (show 0≤4+1760*(b:ℝ) by positivity),
        mul_le_mul_of_nonneg_right bpow (show 0≤1760*(b:ℝ) by positivity)]
    refine (mul_le_mul coeff root (sqrt_nonneg _) (by positivity)).trans ?_
    rw [pow_add,mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith only [bs,mul_nonneg (by linarith only [bs] : 0≤(b:ℝ)-2000) (Nat.cast_nonneg (α:=ℝ) b),
      pow_le_pow_right₀ (by linarith only [bs] : 1≤(b:ℝ)) (by decide : 3≤4),
      mul_nonneg (by linarith only [bs] : 0≤(b:ℝ)-2000) (sq_nonneg (b:ℝ))]
  let delta := (D.card:ℝ)*m
  have deletions : (∑ p ∈ J, if p ∈ D then r p else 0) ≤ delta := by
    rw [←Finset.sum_filter]
    have eq : J.filter (· ∈ D) = D := by ext p; simp only [Finset.mem_filter]; exact ⟨And.right,fun h => ⟨sub h,h⟩⟩
    rw [eq]
    simpa [delta] using Finset.sum_le_sum (s:=D) (fun p h => rmax p (sub h))
  have mhalf : m ≤ 1/2 := by
    have p := mul_le_mul_of_nonneg_right (one_le_pow₀ (n:=k+4) (by linarith : 1≤(b:ℝ))) mp
    linarith only [cap,p]
  have bounds := insertion_error_bound r (fun p => log p) hp up
    (show 0 ≤ delta from mul_nonneg (Nat.cast_nonneg _) mp) mp r0 rmax band mean
  let V := poissonMoment J r (fun p => log p) 2
  obtain ⟨v0,v1,_,err⟩ := bounds
  have vp : 0 < V := (by positivity : 0 < H^2*u/2).trans_le v0
  have small := (mul_le_mul_of_nonneg_right p4 mp).trans cap
  have e1 : 8/u ≤ 1/8 := (div_le_iff₀ up).mpr (by linarith only [d0,ulo])
  have e2 : C/u^2 ≤ 1/8 := (div_le_iff₀ (by positivity)).mpr (by
    nlinarith only [c1,ulo,d0,mul_nonneg (show 0 ≤ u-1 by linarith only [ulo,d0]) up.le])
  have near := normalized_omitted_near_one J D r (fun p => log p) H a delta hp r0
    (fun p h => (rmax p h).trans mhalf) (fun p h => (abs_le.mpr ⟨by linarith [(band p h).1],(band p h).2⟩))
    vp shift deletions
  have tiny : 4*(H^2/V)+insertionError J r (fun p => log p) H delta ≤ 1/2 := by
    refine err.trans ?_
    change 8/u + (4*delta+16*u*m)*sqrt u + C/u^2 ≤ _
    dsimp only [delta]
    linarith only [e1,e2,small]
  have lower := (abs_le.mp (near.trans tiny)).1
  let s := sqrt (2*π/V)
  have sp : 0 < s := sqrt_pos.mpr (by positivity)
  have sq : s^2=2*π/V := sq_sqrt (by positivity)
  have identity : 2*π=V*s^2 := by rw [sq]; field_simp
  have scale : 1 ≤ s*(H*sqrt u) := by
    apply le_of_pow_le_pow_left₀ (n:=2) (by decide) (by positivity)
    rw [mul_pow,mul_pow,sq_sqrt up.le,one_pow]
    nlinarith only [identity,mul_le_mul_of_nonneg_right v1 (sq_nonneg s),pi_gt_three]
  have hs : 1/2 ≤ omittedMass J D r (fun p => log p) H a /s := by linarith only [lower]
  refine le_trans ?_ ((le_div_iff₀ sp).mp hs)
  apply (div_le_iff₀ (by positivity : 0 < 2*H*sqrt u)).mpr
  linarith only [scale]

end Cogentic.Window
