import Cogentic.GridSieve
import Cogentic.FixedErrorBudget

namespace Cogentic.Construction
open Finset Real

/-- The band logarithm absorbs the endpoint loss from truncating the
grid sieve at a fixed multiple of the squared binary logarithm. -/
theorem fixed_sieve_scale (C : ℝ) (cp : 0 < C) :
    ∃ b₀ : ℕ, ∀ b ≥ b₀, C*(Fixed.z b:ℝ)^3 ≤ log (Fixed.B b) := by
  let K := C*4096
  have kp : 0 < K := by dsimp [K]; positivity
  have growth := (isLittleO_log_rpow_rpow_atTop 3 (by norm_num : (0:ℝ)<1)).bound (inv_pos.mpr kp)
  obtain ⟨t,poly⟩ := Filter.eventually_atTop.mp growth
  obtain ⟨n,above⟩ := exists_nat_ge t
  obtain ⟨b₀,grow⟩ := Fixed.degree_grows (max n 16)
  refine ⟨max 1 b₀,?_⟩
  intro b large
  obtain ⟨bp,bg⟩ := max_le_iff.mp large
  have deg := grow b bg
  have d16 : 16 ≤ Fixed.d b := (le_max_right ..).trans deg
  let d := (Fixed.d b:ℝ)
  have dp : 1 ≤ d := by dsimp [d]; exact_mod_cast (show 1≤Fixed.d b by omega)
  have p := poly d (above.trans (by dsimp [d]; exact_mod_cast (le_max_left ..).trans deg))
  simp only [Real.rpow_one,Real.rpow_ofNat,Real.norm_eq_abs,abs_of_nonneg (zero_le_one.trans dp),
    abs_of_nonneg (pow_nonneg (log_nonneg dp) 3)] at p
  have l := Window.log_scale_le bp d16
  have cub := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) (Fixed.z b)) l 3
  have scaled := mul_le_mul_of_nonneg_left p kp.le
  rw [←mul_assoc,mul_inv_cancel₀ kp.ne',one_mul] at scaled
  have low := (Window.fixed_band_log_bounds b bp d16).1
  change 1000*d ≤ _ at low
  refine le_trans ?_ low
  change (Fixed.z b:ℝ)^3 ≤ (16*log d)^3 at cub
  dsimp only [K] at scaled
  nlinarith only [mul_le_mul_of_nonneg_left cub cp.le,scaled,dp]

private theorem sieve_count_cost {b n t : ℕ} (bound : n ≤ b^3) :
    (∑ j ∈ range (t+2), n.choose j) ≤ 2^((t+2)+3*Fixed.z b*(t+1)) := by
  let z := Fixed.z b
  have b2 : b ≤ 2^z := Nat.lt_log2_self.le
  have n2 : n ≤ 2^(3*z) := bound.trans ((Nat.pow_le_pow_left b2 3).trans_eq (by rw [←Nat.pow_mul,Nat.mul_comm]))
  have each (j) (h : j ∈ range (t+2)) : n.choose j ≤ 2^(3*z*(t+1)) := by
    have hj : j ≤ t+1 := Nat.le_of_lt_succ (mem_range.mp h)
    rw [Nat.pow_mul]
    exact (Nat.choose_le_pow ..).trans ((Nat.pow_le_pow_left n2 j).trans
      (Nat.pow_le_pow_right (by positivity) hj))
  have sum := sum_le_sum each
  simp only [sum_const,card_range,nsmul_eq_mul] at sum
  rw [Nat.pow_add]
  exact sum.trans (Nat.mul_le_mul_right _ (Nat.lt_two_pow_self.le))

/-- The endpoint error is uniform in the interval length. On every
interval with L ≥ B, the relative count error decays exponentially. -/
theorem fixed_brun_interval (K : ℝ) (hK : 1 ≤ K) :
    ∃ b₀ : ℕ, ∀ b ≥ b₀, ∀ {a l q k : ℕ} (r m : ℕ), a ≤ l → 0 < q → 0 < k →
    (∀ p ∈ k.primeFactors, p ∣ q → ¬r ≡ m [MOD p]) →
    let P := k.primeFactors.filter (fun p => ¬p ∣ q)
    let L := ((l:ℝ)-a)/q
    P.card ≤ b^3 → (∑ p ∈ P, (p:ℝ)⁻¹) ≤ 3 →
    let X := (Ico a l).filter (fun x => x ≡ r [MOD q])
    |(((X.filter (fun x : ℕ => ((x:ℤ)-m).natAbs.Coprime k)).card):ℝ) -
      L*(∏ p ∈ P, (1-(p:ℝ)⁻¹))| ≤ ((Fixed.B b:ℝ)+2*L*exp 6)*exp (-K*(Fixed.z b:ℝ)^2) := by
  obtain ⟨v,bigv⟩ := exists_nat_ge (2*K)
  obtain ⟨b₀,scale⟩ := fixed_sieve_scale (4*(v:ℝ)+10+K) (by positivity)
  refine ⟨b₀,?_⟩
  intro b bs a l q k r m ab qp kp good P L size mass X
  let z := Fixed.z b
  let t := v*z^2
  let A := (t+2)+3*z*(t+1)
  let η := exp (-K*(z:ℝ)^2)
  have z1 : 1 ≤ (z:ℝ) := by change (1:ℝ) ≤ (↑(b.log2+1):ℝ); exact_mod_cast Nat.le_add_left 1 b.log2
  have z2 : (z:ℝ)^2 ≤ (z:ℝ)^3 := by nlinarith only [mul_nonneg (sq_nonneg (z:ℝ)) (sub_nonneg.mpr z1)]
  have z3 : (z:ℝ) ≤ (z:ℝ)^3 := (le_self_pow₀ z1 (by decide : 2≠0)).trans z2
  have cub : 1 ≤ (z:ℝ)^3 := z1.trans z3
  have Afit : (A:ℝ) ≤ (4*(v:ℝ)+10)*(z:ℝ)^3 := by
    dsimp [A,t]; push_cast
    nlinarith only [mul_le_mul_of_nonneg_left z2 (Nat.cast_nonneg (α:=ℝ) v),z3,cub]
  have Bp : (0:ℝ) < Fixed.B b := by unfold Fixed.B; positivity
  have Bfit := scale b bs
  have overhead := sieve_count_cost (t:=t) size
  have count : (∑ j ∈ range (t+2), (P.card.choose j:ℝ)) ≤ (Fixed.B b:ℝ)*η := by
    have c : (∑ j ∈ range (t+2), (P.card.choose j:ℝ)) ≤ (2:ℝ)^A := by exact_mod_cast overhead
    have e2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) (by linarith [exp_one_gt_d9] : (2:ℝ)≤exp 1) A
    rw [←exp_nat_mul,mul_one] at e2
    refine (c.trans e2).trans ?_
    change exp (A:ℝ) ≤ (Fixed.B b:ℝ)*exp (-K*(z:ℝ)^2)
    rw [←exp_log Bp,←exp_add,exp_le_exp]
    change (4*(v:ℝ)+10+K)*(z:ℝ)^3 ≤ _ at Bfit
    linarith only [Bfit,Afit,mul_le_mul_of_nonneg_left z2 (by linarith : 0 ≤ K)]
  have tail : 1/(2:ℝ)^(t+1) ≤ η := by
    rw [←exp_log (by norm_num : (0:ℝ)<2),←exp_nat_mul,one_div,←exp_neg]
    apply exp_le_exp.mpr
    have half : (1/2:ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
    have l := mul_le_mul_of_nonneg_left half (show 0 ≤ ((t+1:ℕ):ℝ) by positivity)
    dsimp only [t] at l ⊢
    push_cast at l ⊢
    nlinarith only [l,mul_le_mul_of_nonneg_right bigv (sq_nonneg (z:ℝ))]
  have term := brun_coprime_interval ab qp kp r m t good
  have lp : 0 ≤ L := div_nonneg (sub_nonneg.mpr (by exact_mod_cast ab)) (by positivity)
  have e := exp_le_exp.mpr (show 2*(∑ p ∈ P, (p:ℝ)⁻¹) ≤ 6 by linarith only [mass])
  have scaled := mul_le_mul (mul_le_mul_of_nonneg_left e (show 0 ≤ 2*L by positivity)) tail
    (by positivity) (show 0 ≤ 2*L*exp 6 by positivity)
  change _ ≤ _+2*L*exp (2*∑ p ∈ P, (p:ℝ)⁻¹)/(2:ℝ)^(t+1) at term
  refine term.trans ?_
  rw [div_eq_mul_one_div]
  exact (add_le_add count scaled).trans_eq (by dsimp only [η]; ring)

/-- On a grid subinterval, the count here is taken directly in the
executable constructor's mark list, uniformly in its coefficient tuple. -/
theorem constructed_interval_marks (line : DirichletLZerosOnLine) (K : ℝ) (hK : 1 ≤ K) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ ell ∈ dyadicTargets (Fixed.beta (n.log2+1)),
    ¬n.Prime → presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n) = none →
    ∀ (lo hi q r u₀ u₁ v₀ v₁ : ℕ),
    let b := n.log2+1
    let k := markModulus n ell
    let P := k.primeFactors.filter (fun p => ¬p ∣ q)
    let L := ((hi:ℝ)-lo)/q
    let ρ := ∏ p ∈ P, (1-(p:ℝ)⁻¹)
    let X := (Ico lo hi).filter (fun x => x ≡ r [MOD q])
    lo ≤ hi → 0 < q →
    (∀ p ∈ k.primeFactors, p ∣ q → ¬r ≡ Fixed.rootBase n [MOD p]) →
    (∀ x ∈ X, 1 ≤ x ∧ x ≤ Fixed.A b ∧ onGrid (Fixed.d b) (Fixed.A b) (Fixed.invWidth b) x) →
    1/4 ≤ ρ ∧ |(((X.filter (fun x => x ∈ (construct n ell u₀ u₁ v₀ v₁).marks)).card):ℝ)-L*ρ| ≤
      ((Fixed.B b:ℝ)+2*L*exp 6)*exp (-K*(Fixed.z b:ℝ)^2) := by
  obtain ⟨n₀,dens⟩ := mark_density_from_critical_line line
  obtain ⟨b₁,sieve⟩ := fixed_brun_interval K hK
  obtain ⟨b₂,grow⟩ := Fixed.degree_grows 10004
  refine ⟨max n₀ (2^max 250000 (max b₁ b₂)),?_⟩
  intro n nbig ell target comp absent lo hi q r u₀ u₁ v₀ v₁ b k P L ρ X ab qp eligible grid
  have high := (le_max_right ..).trans nbig
  have np := (Nat.pow_pos (by decide : 0 < 2)).trans_le high
  have logs := (Nat.le_log2 np.ne').mpr high
  have sizes : 250000 ≤ b ∧ b₁ ≤ b ∧ b₂ ≤ b := by dsimp only [b]; omega
  have hn : 2 ≤ n := (show 2^1 ≤ 2^max 250000 (max b₁ b₂) from
    Nat.pow_le_pow_right (by decide) (by omega)).trans high
  have big := grow b sizes.2.2
  have ⟨kp,cap,_,_⟩ := markModulus_spec hn big comp target absent
  have cnt := mark_factor_count hn kp cap
  have degree : 0 < Fixed.d b := by omega
  have vb : Fixed.v b ≤ b := by
    refine le_trans ?_ (Fixed.degree_floor b).1
    simpa only [Fixed.v,Fixed.h,pow_two,mul_assoc] using Nat.mul_le_mul_right (Fixed.z b)
      (Nat.pow_le_pow_right degree (by decide : 2 ≤ 3))
  have ps : P.card ≤ b^3 := by
    apply card_le_card (filter_subset ..) |>.trans
    change k.primeFactors.card ≤ 2+222240*Fixed.v b at cnt
    have small : 2+222240*b ≤ b^2 := by
      have eb := Nat.mul_le_mul_right b sizes.1
      nlinarith only [eb,sizes.1]
    exact cnt.trans ((Nat.add_le_add_left (Nat.mul_le_mul_left _ vb) _).trans
      (small.trans (Nat.pow_le_pow_right (by omega) (by decide : 2≤3))))
  obtain ⟨mass,rho⟩ := dens n ((le_max_left ..).trans nbig) ell target comp absent
  have sub : P ⊆ k.primeFactors := filter_subset ..
  have sum : (∑ p ∈ P, (p:ℝ)⁻¹) ≤ 3 := by
    have lim := sum_le_sum_of_subset_of_nonneg sub (f:=fun p : ℕ => (p:ℝ)⁻¹) (fun _ _ _ => by positivity)
    linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)]
  have rlo : 1/4 ≤ ρ := by
    refine rho.trans (prod_le_prod_of_subset_of_le_one sub ?_ ?_)
    · intro p h
      have one : (1:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors h).one_le
      linarith [inv_le_one_of_one_le₀ one]
    · intro p _ _; linarith [inv_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) p)]
  have count := sieve b sizes.2.1 r (Fixed.rootBase n) ab qp kp eligible ps sum
  have marks : X.filter (fun x => x ∈ (construct n ell u₀ u₁ v₀ v₁).marks) =
      X.filter (fun x : ℕ => ((x:ℤ)-Fixed.rootBase n).natAbs.Coprime k) := by
    apply filter_congr
    intro x hx
    obtain ⟨x1,xA,onG⟩ := grid x hx
    exact ⟨fun hx => ((constructed_marks_iff ..).mp hx).2.2.2,
      fun h => (constructed_marks_iff ..).mpr ⟨x1,xA,onG,h⟩⟩
  refine ⟨rlo,?_⟩
  rw [marks]
  exact count

end Cogentic.Construction
