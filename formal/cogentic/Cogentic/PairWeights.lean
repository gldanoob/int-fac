import Cogentic.PairGridSieve

namespace Cogentic.Construction
open Finset Real

private theorem prime_correction (p : ℕ) (prime : p.Prime) :
    0 ≤ (2*(p:ℝ)-1)/((p:ℝ)-1)^2 ∧ (2*(p:ℝ)-1)/((p:ℝ)-1)^2 ≤ 8/(p:ℝ) := by
  have p2 : (2:ℝ) ≤ p := by exact_mod_cast prime.two_le
  have pp : (0:ℝ) < p := by linarith
  refine ⟨div_nonneg (by linarith) (sq_nonneg _),(div_le_div_iff₀ (sq_pos_of_pos (by linarith)) pp).mpr ?_⟩
  nlinarith only [sq_nonneg ((p:ℝ)-2),p2]

private theorem inverse_squares (d : ℕ) (dp : 0 < d) (P : Finset ℕ) (large : ∀ p∈P, d < p) :
    (∑ p∈P, ((p:ℝ)⁻¹)^2) ≤ (d:ℝ)⁻¹ := by
  have interval (n : ℕ) (hn : d ≤ n) : (∑ p ∈ Ioc d n, ((p:ℝ)⁻¹)^2) ≤ (d:ℝ)⁻¹-(n:ℝ)⁻¹ := by
    induction n,hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [show Ioc d (n+1)=insert (n+1) (Ioc d n) by ext x; simp only [mem_Ioc,mem_insert]; omega,
        sum_insert (by simp)]
      have np : 0 < (n:ℝ) := by exact_mod_cast dp.trans_le hn
      have step : ((n+1:ℝ)⁻¹)^2 ≤ (n:ℝ)⁻¹-(n+1:ℝ)⁻¹ := by
        field_simp
        linarith
      push_cast
      linarith only [ih,step]
  let top := max d (P.sup id)
  have sub : P ⊆ Ioc d top := fun p h => mem_Ioc.mpr ⟨large p h,(le_sup (f:=id) h).trans (le_max_right ..)⟩
  have sum := sum_le_sum_of_subset_of_nonneg sub (f:=fun p : ℕ => ((p:ℝ)⁻¹)^2) (fun _ _ _ => sq_nonneg _)
  exact sum.trans ((interval top (le_max_left ..)).trans (sub_le_self _ (by positivity)))

/-- The divisor correction weighted by one inverse modulus has total
mass at most exp(8/d), including the empty divisor of mass one. -/
theorem pair_weight_inverse_sum (P : Finset ℕ) (pr : ∀ p∈P, p.Prime) (d : ℕ) (dp : 0<d)
    (large : ∀ p∈P, d<p) :
    (∑ T ∈ P.powerset, pairDivisorWeight T/(sieveProduct T:ℝ)) ≤ exp (8/(d:ℝ)) := by
  let e := fun p : ℕ => (2*(p:ℝ)-1)/((p:ℝ)-1)^2
  have eq (T : Finset ℕ) : pairDivisorWeight T/(sieveProduct T:ℝ) = ∏ p∈T, e p/(p:ℝ) := by
    simp [pairDivisorWeight,sieveProduct,e,prod_div_distrib]
  simp_rw [eq]
  rw [←prod_one_add]
  have bound (p : ℕ) (h : p∈P) : e p/(p:ℝ) ≤ 8*((p:ℝ)⁻¹)^2 := by
    exact (div_le_div_of_nonneg_right (prime_correction p (pr p h)).2 (by positivity)).trans_eq (by ring)
  refine le_trans (prod_le_prod (fun p h => show 0≤1+e p/(p:ℝ) by linarith [div_nonneg (prime_correction p (pr p h)).1 (Nat.cast_nonneg (α:=ℝ) p)])
    (fun p h => show 1+e p/(p:ℝ) ≤ exp (8*((p:ℝ)⁻¹)^2) by linarith [bound p h,add_one_le_exp (8*((p:ℝ)⁻¹)^2)])) ?_
  rw [←exp_sum,←mul_sum,exp_le_exp]
  exact (mul_le_mul_of_nonneg_left (inverse_squares d dp P large) (by norm_num)).trans_eq (by ring)

private theorem reciprocal_blocks (d₀ d j : ℕ) (big : d₀ ≤ d)
    (band : ∀ d ≥ d₀, (∑ p ∈ (Ioc d (d^3)).filter Nat.Prime, (p:ℝ)⁻¹) ≤ log 3+1/32) :
    (∑ p ∈ (Ioc d (d^(3^j))).filter Nat.Prime, (p:ℝ)⁻¹) ≤ (j:ℝ)*(log 3+1/32) := by
  induction j with
  | zero => simp
  | succ j ih =>
    let top := d^(3^j)
    have lt : d ≤ top := Nat.le_self_pow (pow_ne_zero _ (by decide : (3:ℕ)≠0)) d
    have tlo : top ≤ top^3 := Nat.le_self_pow (by decide) top
    rw [pow_succ (3:ℕ),pow_mul]
    change (∑ p ∈ (Ioc d (top^3)).filter Nat.Prime, _) ≤ _
    rw [←Ioc_union_Ioc_eq_Ioc lt tlo,filter_union,sum_union (Disjoint.mono (filter_subset ..) (filter_subset ..) (Ioc_disjoint_Ioc_of_le (a:=d) (d:=top^3) le_rfl))]
    push_cast
    exact (add_le_add ih (band top (big.trans lt))).trans_eq (by ring)

/-- The total unweighted singular-series divisor mass is only
exponential in the log bit length, uniformly for the full small-prime band. -/
theorem fixed_pair_weight_sum (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ b ≥ b₀, ∀ P : Finset ℕ,
      (∀ p∈P, p.Prime ∧ Fixed.d b < p ∧ p ≤ Fixed.B b) →
      (∑ T ∈ P.powerset, pairDivisorWeight T) ≤ exp (48*(Fixed.z b:ℝ)) := by
  obtain ⟨d₀,band⟩ := band_eventually line
  obtain ⟨b₀,grow⟩ := Fixed.degree_grows (max 1000 d₀)
  refine ⟨b₀,?_⟩
  intro b bbig P primes
  let d := Fixed.d b
  let z := Fixed.z b
  have deg := grow b bbig
  have hd : 1000 ≤ d := (le_max_left ..).trans deg
  have db := Fixed.degree_le_bits b
  have b1 : 0 < b := by change 1000≤Fixed.d b at hd; omega
  have zb : z ≤ b := by
    dsimp only [z,Fixed.z]
    exact (Nat.log2_lt b1.ne').mpr Nat.lt_two_pow_self
  have b2 : b ≤ 2^z := Nat.lt_log2_self.le
  have base : Fixed.B b ≤ d^(3^(2*z)) := by
    have cost : 1000*(d*z) ≤ b^3 := by
      exact (Nat.mul_le_mul (hd.trans db) (Nat.mul_le_mul db zb)).trans_eq (by ring)
    have ez : b^3 ≤ 3^(2*z) := by
      exact (Nat.pow_le_pow_left b2 3).trans (by rw [←Nat.pow_mul,Nat.mul_comm z 3,Nat.pow_mul,Nat.pow_mul]; exact Nat.pow_le_pow_left (by decide) z)
    exact (Nat.pow_le_pow_right (by decide : 0<2) (cost.trans ez)).trans (Nat.pow_le_pow_left (by omega) _)
  have sub : P ⊆ (Ioc d (d^(3^(2*z)))).filter Nat.Prime := fun p h => mem_filter.mpr
    ⟨mem_Ioc.mpr ⟨(primes p h).2.1,(primes p h).2.2.trans base⟩,(primes p h).1⟩
  have prob := sum_le_sum_of_subset_of_nonneg sub (f:=fun p : ℕ => (p:ℝ)⁻¹) (fun _ _ _ => by positivity)
  have blocks := reciprocal_blocks d₀ d (2*z) ((le_max_right ..).trans deg) band
  have sum : (∑ p∈P, (p:ℝ)⁻¹) ≤ 6*z := by
    have total := prob.trans blocks
    push_cast at total
    have lg : log 3+1/32 ≤ 3 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)]
    linarith only [total,mul_le_mul_of_nonneg_left lg (show 0 ≤ 2*(z:ℝ) by positivity)]
  unfold pairDivisorWeight
  rw [←prod_one_add]
  have e := prod_le_prod (s:=P) (fun p h => show 0 ≤ 1+(2*(p:ℝ)-1)/((p:ℝ)-1)^2 by linarith [(prime_correction p (primes p h).1).1])
    (fun p h => show 1+(2*(p:ℝ)-1)/((p:ℝ)-1)^2 ≤ exp (8*(p:ℝ)⁻¹) by
      have est := (prime_correction p (primes p h).1).2
      exact (add_le_add (le_refl 1) est).trans (by simpa only [div_eq_mul_inv,add_comm] using add_one_le_exp (8*(p:ℝ)⁻¹)))
  refine e.trans ?_
  rw [←exp_sum,←mul_sum,exp_le_exp]
  linarith only [sum]

end Cogentic.Construction
