import Cogentic.ConstructionCofactors
import Cogentic.PrincipalBand
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Cogentic.Construction
open Real Filter MeasureTheory Set
open scoped Topology

/-- One GRH prime band, including its integral and the finite cutoff, bounds
    the reciprocal mass of all primes from d through d³. -/
theorem cubic_reciprocal_band (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℕ, 4 ≤ d →
      |(∑ q ∈ (Finset.Ioc d (d^3)).filter Nat.Prime, (q:ℝ)⁻¹)-Real.log 3| ≤
        6*C*(1+Real.log (3*(d:ℝ)^3))^2*(d:ℝ)^(-(1/2:ℝ)) := by
  obtain ⟨C,cp,band⟩ := Window.principal_prime_integral line
  refine ⟨C,cp,?_⟩
  intro d big
  have large : (4:ℝ) ≤ d := by exact_mod_cast big
  have pos : (0:ℝ) < d := by linarith
  have cube : d ≤ d^3 := Nat.le_self_pow (by decide : 3 ≠ 0) _
  have bound := band d (d^3) 1 large (by exact_mod_cast cube) (by norm_num)
  have integ : (∫ x in (d:ℝ)..(d:ℝ)^3, (x:ℂ)^(-(1:ℂ))/((Real.log x:ℝ):ℂ)) =
      (Real.log 3 : ℂ) := by
    simp only [Complex.cpow_neg_one,←Complex.ofReal_inv,←Complex.ofReal_div,intervalIntegral.integral_ofReal]
    rw [integral_inv_div_log (by linarith) (by nlinarith [show (d:ℝ) ≤ (d:ℝ)^3 by exact_mod_cast cube]),
      Real.log_pow,Real.log_mul (by norm_num) (Real.log_pos (by linarith : (1:ℝ)<d)).ne']
    push_cast; ring
  rw [integ] at bound
  have floor : ⌊(d:ℝ)^3⌋₊ = d^3 := by exact_mod_cast Nat.floor_natCast (R := ℝ) (d^3)
  simp only [Nat.floor_natCast,floor,Complex.cpow_neg_one,Complex.one_re, norm_one] at bound
  have same : (∑ q ∈ (Finset.Ioc d (d^3)).filter Nat.Prime, (q:ℂ)⁻¹) =
      ((∑ q ∈ (Finset.Ioc d (d^3)).filter Nat.Prime, (q:ℝ)⁻¹):ℝ) := by push_cast; rfl
  rw [same,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at bound
  convert bound using 1; norm_num; ring

private theorem degree_dominates_log (k : ℕ) : ∃ b₀, ∀ b ≥ b₀, k*Fixed.z b ≤ Fixed.d b := by
  have small := tendsto_pow_const_div_const_pow_of_one_lt 4 (by norm_num : (1:ℝ)<2)
  have limit : Tendsto (fun j : ℕ => ((16*k^3:ℕ):ℝ)*((j:ℝ)^4/2^j)) atTop (𝓝 0) := by
    simpa [Nat.cast_mul,Nat.cast_pow] using (tendsto_const_nhds (x := (16*(k:ℝ)^3))).mul small
  obtain ⟨j₀,hj⟩ := eventually_atTop.mp (limit.eventually_lt_const (by norm_num : (0:ℝ)<1))
  refine ⟨2^(max j₀ 1),?_⟩
  intro b hb
  have bp := (Nat.pow_pos (by decide : 0<2)).trans_le hb
  have jm := (Nat.le_log2 bp.ne').mpr hb
  have small := hj b.log2 ((le_max_left _ _).trans jm)
  rw [←mul_div_assoc,div_lt_one (by positivity)] at small
  have natBound : (16*k^3)*b.log2^4 ≤ 2^b.log2 := by exact_mod_cast small.le
  have zle : Fixed.z b ≤ 2*b.log2 := by unfold Fixed.z; omega
  apply (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).mpr
  apply (Nat.le_div_iff_mul_le (by simp [Fixed.z])).mpr
  calc (k*Fixed.z b)^3*Fixed.z b = k^3*(Fixed.z b)^4 := by ring
       _ ≤ k^3*(2*b.log2)^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left zle 4)
       _ = (16*k^3)*b.log2^4 := by ring
       _ ≤ 2^b.log2 := natBound
       _ ≤ b := Nat.log2_self_le bp.ne'

theorem mark_factor_count {n ell : ℕ} (hn : 2 ≤ n)
    (pos : 0 < markModulus n ell) (size : markModulus n ell < (2*leadingCoefficient n)^2) :
    (markModulus n ell).primeFactors.card ≤ 2+222240*Fixed.v (n.log2+1) := by
  let k := markModulus n ell
  let v := Fixed.v (n.log2+1)
  have rad : 2^k.primeFactors.card ≤ k := by
    calc _ = ∏ _q ∈ k.primeFactors, 2 := by simp
         _ ≤ ∏ q ∈ k.primeFactors, q := Finset.prod_le_prod' (fun q hq => (Nat.prime_of_mem_primeFactors hq).two_le)
         _ ≤ k := Nat.le_of_dvd pos (Nat.prod_primeFactors_dvd _)
  have width := Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 (leading_size hn)) 2
  have eq : (2*2^(111120*v))^2 = 2^(2+222240*v) := by
    calc _ = (2^(1+111120*v))^2 := by rw [Nat.pow_add]
         _ = _ := by rw [←Nat.pow_mul]; congr 1; ring
  apply (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
  exact rad.trans (size.le.trans (width.trans eq.le))

theorem band_eventually (line : DirichletLZerosOnLine) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, (∑ q ∈ (Finset.Ioc d (d^3)).filter Nat.Prime, (q:ℝ)⁻¹) ≤ Real.log 3+1/32 := by
  obtain ⟨C,hC,band⟩ := cubic_reciprocal_band line
  have little := (isLittleO_log_rpow_rpow_atTop 2 (show (0:ℝ)<1/2 by norm_num)).tendsto_div_nhds_zero
  have lim : Tendsto (fun d : ℕ => (216*C)*((Real.log d)^2/(d:ℝ)^(1/2:ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := 216*C)).mul (little.comp tendsto_natCast_atTop_atTop)
  obtain ⟨q,hq⟩ := eventually_atTop.mp (lim.eventually_lt_const (by norm_num : (0:ℝ)<1/32))
  refine ⟨max q 4,?_⟩
  intro d hd
  have big := (le_max_right q 4).trans hd
  have dr : (4:ℝ) ≤ d := by exact_mod_cast big
  have positive : (0:ℝ) < d := by linarith
  have log1 : 1 ≤ Real.log d := (Real.le_log_iff_exp_le positive).mpr (by linarith [Real.exp_one_lt_d9])
  have log3 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
  have approx := band d big
  have bound : 0 ≤ 1+Real.log (3*(d:ℝ)^3) := by
    linarith [Real.log_nonneg (show (1:ℝ) ≤ 3*(d:ℝ)^3 by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤4) dr 3])]
  have logBound : 1+Real.log (3*(d:ℝ)^3) ≤ 6*Real.log d := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ positive.ne'),Real.log_pow]; norm_num; linarith
  have square := pow_le_pow_left₀ bound logBound 2
  have err := mul_le_mul_of_nonneg_left square (show (0:ℝ) ≤ 6*C by positivity)
  have err' := mul_le_mul_of_nonneg_right err (Real.rpow_nonneg positive.le (-(1/2:ℝ)))
  have numeric := hq d ((le_max_left _ _).trans hd)
  rw [Real.rpow_neg positive.le] at err' approx
  rw [div_eq_mul_inv] at numeric
  linarith [abs_le.mp approx,show (6*C*(6*Real.log d)^2)*((d:ℝ)^(1/2:ℝ))⁻¹ =
    (216*C)*((Real.log d)^2*((d:ℝ)^(1/2:ℝ))⁻¹) by ring]

private theorem reciprocal_split {k d : ℕ} (big : 1 ≤ d) (excluded : ∀ q ∈ k.primeFactors, d < q) :
    (∑ q ∈ k.primeFactors, (q:ℝ)⁻¹) ≤
      (∑ q ∈ (Finset.Ioc d (d^3)).filter Nat.Prime, (q:ℝ)⁻¹) + k.primeFactors.card / (d:ℝ)^3 := by
  let S := k.primeFactors
  have small : S.filter (fun q => q ≤ d^3) ⊆ (Finset.Ioc d (d^3)).filter Nat.Prime := by
    intro q hit
    obtain ⟨mem,size⟩ := Finset.mem_filter.mp hit
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨excluded q mem,size⟩,Nat.prime_of_mem_primeFactors mem⟩
  have lo := Finset.sum_le_sum_of_subset_of_nonneg (f := fun q : ℕ => (q:ℝ)⁻¹) small
    (fun q hq _ => by positivity)
  let T := S.filter (fun q => ¬q ≤ d^3)
  have hi : ∑ q ∈ T, (q:ℝ)⁻¹ ≤ ∑ _q ∈ T, ((d:ℝ)^3)⁻¹ := by
    apply Finset.sum_le_sum
    intro q hq
    have nn := (Finset.mem_filter.mp hq).2
    exact inv_anti₀ (by positivity) (by exact_mod_cast (by omega : d^3≤q))
  have card : (T.card:ℝ) ≤ S.card := by exact_mod_cast Finset.card_filter_le ..
  have hi' := hi.trans (by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right card (show 0 ≤ ((d:ℝ)^3)⁻¹ by positivity) :
      (∑ _q ∈ T, ((d:ℝ)^3)⁻¹) ≤ S.card / (d:ℝ)^3)
  rw [←Finset.sum_filter_add_sum_filter_not S (fun q => q≤d^3)]
  exact add_le_add lo hi'

private theorem euler_density {k d : ℕ} (big : 64 ≤ d) (excluded : ∀ q ∈ k.primeFactors, d < q)
    (mass : (∑ q ∈ k.primeFactors, (q:ℝ)⁻¹) ≤ Real.log 3+1/16) :
    (1/4:ℝ) ≤ ∏ q ∈ k.primeFactors, (1-(q:ℝ)⁻¹) := by
  let S := k.primeFactors
  have factor (q : ℕ) (h : q ∈ S) : 0 < 1-(q:ℝ)⁻¹ := by
    have qhi := excluded q h
    have qr : (1:ℝ)<q := by exact_mod_cast (by omega : 1<q)
    exact sub_pos.mpr ((inv_lt_one₀ (by linarith)).mpr qr)
  have lo (q : ℕ) (hq : q ∈ S) : -(65/64:ℝ)*(q:ℝ)⁻¹ ≤ Real.log (1-(q:ℝ)⁻¹) := by
    refine le_trans ?_ (Real.one_sub_inv_le_log_of_pos (factor q hq))
    have qhi := excluded q hq
    have qr : (65:ℝ) ≤ q := by exact_mod_cast (by omega : 65≤q)
    have qpos : 0 < (q:ℝ) := by linarith
    have qm : 0 < (q:ℝ)-1 := by linarith
    have eq : (1-(q:ℝ)⁻¹)⁻¹ = q/(q-1:ℝ) := by field_simp
    rw [eq]
    field_simp
    linarith
  have avg := Finset.sum_le_sum lo
  rw [←Finset.mul_sum] at avg
  have sums := mul_le_mul_of_nonpos_left mass (show -(65/64:ℝ)≤0 by norm_num)
  have delta := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<4/3)
  rw [Real.log_div (by norm_num) (by norm_num)] at delta
  have log3 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
  apply (Real.log_le_log_iff (by norm_num) (Finset.prod_pos factor)).mp
  rw [Real.log_prod (fun q h => (factor q h).ne'),Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub]
  norm_num at delta
  change _ ≤ ∑ q ∈ S, _ at avg
  linarith

/-- The prime divisors of the actual two-cofactor product remove a bounded
    proportion in the first Brun sieve, uniformly for every selected target. -/
theorem mark_density_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ ell ∈ dyadicTargets (Fixed.beta (n.log2+1)),
      ¬n.Prime → presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n) = Option.none →
      let k := markModulus n ell
      (∑ q ∈ k.primeFactors, (q:ℝ)⁻¹) ≤ Real.log 3+1/16 ∧
      (1/4:ℝ) ≤ ∏ q ∈ k.primeFactors, (1-(q:ℝ)⁻¹) := by
  obtain ⟨d₀,band⟩ := band_eventually line
  obtain ⟨b₀,degree⟩ := Fixed.degree_grows (max d₀ 10004)
  obtain ⟨b₁,aux⟩ := degree_dominates_log 8000000
  refine ⟨2^(max (max b₀ b₁) 1),?_⟩
  intro n hn ell target composite none
  have np := (Nat.pow_pos (by decide : 0<2)).trans_le hn
  have nb := (Nat.le_log2 np.ne').mpr hn
  have nbig : 2 ≤ n := (by decide : 2 ≤ 2^1).trans ((Nat.pow_le_pow_right (by decide) (le_max_right _ _)).trans hn)
  let b := n.log2+1
  let d := Fixed.d b
  let k := markModulus n ell
  have dbig := degree b (by dsimp [b]; omega)
  have aux := aux b (by dsimp [b]; omega)
  have hg : 10004 ≤ d := (le_max_right _ _).trans dbig
  have ⟨kp,cap,_,support⟩ := markModulus_spec nbig hg composite target none
  have excl (q : ℕ) (hq : q ∈ k.primeFactors) : d < q := (support q hq).1
  have count := mark_factor_count nbig kp cap
  change k.primeFactors.card ≤ 2+222240*(d*(d*Fixed.z b)) at count
  have dp : 0 < d := by omega
  have zp : 0 < Fixed.z b := by simp [Fixed.z]
  have one := Nat.mul_pos dp (Nat.mul_pos dp zp)
  have countHi : k.primeFactors.card ≤ 250000*(d*(d*Fixed.z b)) := by omega
  have tail : 32*k.primeFactors.card ≤ d^3 := by
    calc _ ≤ 32*(250000*(d*(d*Fixed.z b))) := Nat.mul_le_mul_left _ countHi
         _ = d*d*(8000000*Fixed.z b) := by ring
         _ ≤ d*d*d := Nat.mul_le_mul_left _ aux
         _ = _ := by ring
  have tailR : (k.primeFactors.card:ℝ)/(d:ℝ)^3 ≤ 1/32 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have := (show (32:ℝ)*k.primeFactors.card ≤ (d:ℝ)^3 by exact_mod_cast tail)
    linarith
  have splits := reciprocal_split (by omega : 1≤d) excl
  have band := band d ((le_max_left _ _).trans dbig)
  have mass : (∑ q ∈ k.primeFactors, (q:ℝ)⁻¹) ≤ Real.log 3+1/16 := by linarith
  exact ⟨mass,euler_density (by omega : 64≤d) excl mass⟩

end Cogentic.Construction

#print axioms Cogentic.Construction.mark_density_from_critical_line
