import Cogentic.DifferencePrimes
import Cogentic.FirstResidueLoss

namespace Cogentic.Construction
open Finset

private theorem quotient_cast {n ell p : ℕ} (R : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (i : ℕ) (side : Bool)
    (u v : ℤ) (ok : R.compatible side u v) :
    (R.intercept i side u v : ZMod p)*(R.prefactor i side : ZMod p)=
    (signedBase n ell i side : ZMod p)+(signedSlope n ell i side : ZMod p)*((u:ZMod p)+i*v) := by
  have eq := Int.ediv_mul_cancel (dvd_mul_of_dvd_right (R.pre_dvd target i side u v ok) (markSign n i side))
  change R.intercept i side u v * (R.prefactor i side:ℤ) = _ at eq
  rw [signed_value] at eq
  exact_mod_cast congrArg (Int.cast (R:=ZMod p)) eq

/-- At a free prescribed prime, a second quotient vanishing modulo the prime
fixes both coefficient residues. In particular it fixes the first observation
and the first signed quotient, even when the marks agree modulo the prime. -/
theorem PrescribedRows.free_prime_residue {n ell p a y : ℕ} (R : PrescribedRows n ell)
    (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (mark : y∈(construct n ell 0 0 0 0).marks) (side : Bool) (free : p∈R.miss a \ R.hit y) :
    ∃ U V q₀ : ZMod p, ∀ u v : ℤ, R.compatible side u v → p∣(R.intercept y side u v).natAbs →
      (u:ZMod p)=U ∧ (v:ZMod p)=V ∧ ((u+(a:ℤ)*v:ℤ):ZMod p)=U+a*V ∧
        (R.intercept a side u v : ZMod p)=q₀ := by
  have ha := mem_sdiff.mp (mem_sdiff.mp free).1
  have hy := (mem_sdiff.mp free).2
  have pp := R.prime ha.1
  let : Fact p.Prime := ⟨pp⟩
  have pe : p≠ell := fun eq => R.excluded (eq ▸ ha.1)
  have eunit : (ell:ZMod p)≠0 := fun zero => pe ((Nat.prime_dvd_prime_iff_eq pp (mem_dyadicTargets.mp target).1).mp
    ((ZMod.natCast_eq_zero_iff ..).mp zero))
  have den : (R.prefactor a side : ZMod p)≠0 := by
    intro z
    have pm := Nat.mem_primeFactors.mpr ⟨pp,(ZMod.natCast_eq_zero_iff ..).mp z,(R.pre_bounds target a side).1.ne'⟩
    rw [R.prefactor_primeFactors target] at pm
    split at pm <;> exact ha.2 (by simpa [pe] using pm)
  have yr : (y:ZMod p) ≠ R.residue p := fun e => hy (mem_filter.mpr ⟨ha.1,e.symm⟩)
  obtain ⟨L,line⟩ := R.linear_equations target side
  by_cases hit : ∃ u v : ℤ, R.compatible side u v ∧ p∣(R.intercept y side u v).natAbs
  · obtain ⟨u₀,v₀,ok₀,dvd₀⟩ := hit
    refine ⟨u₀,v₀,R.intercept a side u₀ v₀,?_⟩
    have am := mark_range hn big ((constructed_marks_iff ..).mp mark).2.1
    have size := (firstStep_size am (mem_dyadicTargets.mp target).1.pos side).1
    have unit : (firstStep n ell y side : ZMod p)≠0 := by
      intro z
      have zd := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp z
      have pd : p∣(firstStep n ell y side).natAbs := by
        simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr zd
      rw [size] at pd
      exact Nat.not_coprime_of_dvd_of_dvd pp.one_lt dvd₀ pd (R.intercept_coprime hn big comp target absent mark side u₀ v₀ ok₀)
    have su : (signedSlope n ell y side : ZMod p)≠0 := by
      have h := congrArg (Int.cast (R:=ZMod p)) (scaled_first n ell y side)
      change _ = ((signedSlope n ell y side:ℤ):ZMod p) at h
      rw [←h,Int.cast_mul,Int.cast_natCast]
      apply mul_ne_zero unit
      unfold targetPart
      split <;> simp [eunit]
    have zAt (u v : ℤ) (ok : R.compatible side u v) (dv : p∣(R.intercept y side u v).natAbs) :
        (signedBase n ell y side : ZMod p)+(signedSlope n ell y side : ZMod p)*((u:ZMod p)+y*v)=0 := by
      have eq := quotient_cast (p:=p) R target y side u v ok
      have zero : (R.intercept y side u v : ZMod p)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr
        (Int.natAbs_dvd_natAbs.mp (by simpa only [Int.natAbs_natCast] using dv))
      rw [←eq,zero,zero_mul]
    intro u v ok dvd
    have Y := mul_left_cancel₀ su (add_left_cancel ((zAt u v ok dvd).trans (zAt u₀ v₀ ok₀ dvd₀).symm))
    have T := ((line u v).mp ok p ha.1).trans ((line u₀ v₀).mp ok₀ p ha.1).symm
    have V : (v:ZMod p)=(v₀:ZMod p) := by
      apply mul_left_cancel₀ (sub_ne_zero.mpr yr)
      linear_combination Y - T
    have U : (u:ZMod p)=(u₀:ZMod p) := by rw [V] at T; exact add_right_cancel T
    refine ⟨U,V,by push_cast; rw [U,V],?_⟩
    apply mul_right_cancel₀ den
    rw [quotient_cast R target a side u v ok,quotient_cast R target a side u₀ v₀ ok₀,U,V]
  · exact ⟨0,0,0,fun u v ok h => (hit ⟨u,v,ok,h⟩).elim⟩

/-- The same bad observations occupy a single lift of the ordinary quotient
class modulo the first step times p, also when p already divides that step. -/
theorem PrescribedRows.free_prime_lift {n ell p a y : ℕ} (R : PrescribedRows n ell)
    (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (mark : y∈(construct n ell 0 0 0 0).marks) (side : Bool) (free : p∈R.miss a \ R.hit y) :
    let q := (firstStep n ell a side).natAbs
    ∃ z : ℤ, ∀ u v : ℤ, R.compatible side u v → p∣(R.intercept y side u v).natAbs →
      (R.intercept a side u v : ZMod (q*p))=(z:ZMod (q*p)) := by
  intro q
  obtain ⟨U,V,r,fixed⟩ := R.free_prime_residue hn big comp target absent mark side free
  have ha := mem_sdiff.mp (mem_sdiff.mp free).1
  have pp := R.prime ha.1
  let : Fact p.Prime := ⟨pp⟩
  let H := R.hitProduct a
  have hu : (H:ZMod p)≠0 := by
    intro zero
    have dvd := (ZMod.natCast_eq_zero_iff ..).mp zero
    have hp : H.primeFactors=R.hit a := Nat.primeFactors_prod (fun t h => R.prime (mem_filter.mp h).1)
    have mem := Nat.mem_primeFactors.mpr ⟨pp,dvd,(R.subprod_bounds (s:=R.hit a) (filter_subset ..)).1.ne'⟩
    exact ha.2 (hp ▸ mem)
  obtain ⟨c,t,e,law⟩ := R.polynomial_lattice target side a
  have project (u v : ℤ) (ok : R.compatible side u v) :
      ∃ i : ℤ, u+(a:ℤ)*v=c+H*i := by
    let k : {w : ℤ×ℤ // R.compatible side w.1 w.2} := ⟨(u,v),ok⟩
    obtain ⟨⟨i,j⟩,h⟩ := e.surjective k
    have eq := law i j
    rw [h] at eq
    refine ⟨i,?_⟩
    obtain ⟨one,two⟩ := Prod.mk.inj eq
    rw [one,two,sub_add_cancel]
  by_cases hit : ∃ u v : ℤ, R.compatible side u v ∧ p∣(R.intercept y side u v).natAbs
  · obtain ⟨u₀,v₀,ok₀,d₀⟩ := hit
    obtain ⟨i₀,h₀⟩ := project u₀ v₀ ok₀
    refine ⟨R.intercept a side u₀ v₀,?_⟩
    intro u v ok dvd
    obtain ⟨i,hi⟩ := project u v ok
    have eq := ((fixed u v ok dvd).2.2.1).trans ((fixed u₀ v₀ ok₀ d₀).2.2.1).symm
    rw [hi,h₀] at eq
    push_cast at eq
    have idiff := (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp (mul_left_cancel₀ hu (add_left_cancel eq)).symm
    let s := firstStep n ell a side
    have diff : u+(a:ℤ)*v=(u₀+(a:ℤ)*v₀)+(H:ℤ)*(i-i₀) := by rw [hi,h₀]; ring
    have shifted := R.first_quotient target a side u₀ v₀ ok₀ (i-i₀)
    change markSign n a side*affineValue n ell a side ((u₀+(a:ℤ)*v₀)+(H:ℤ)*(i-i₀)) /
      (R.prefactor a side:ℤ)=R.intercept a side u₀ v₀+s*(i-i₀) at shifted
    rw [←diff] at shifted
    change R.intercept a side u v=R.intercept a side u₀ v₀+s*(i-i₀) at shifted
    symm
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mpr
    rw [shifted,add_sub_cancel_left, Nat.cast_mul]
    apply mul_dvd_mul _ idiff
    apply Int.natAbs_dvd_natAbs.mp
    simp [q,s]
  · exact ⟨0,fun u v ok h => (hit ⟨u,v,ok,h⟩).elim⟩

open Cogentic.Window Real

/-- A specified lift modulo qp costs at most 9/p of any ordinary reduced
class when p divides q. Both conductor estimates use the same deleted band. -/
private theorem lift_class_cost {q p : ℕ} (qp : 0<q) (pp : p.Prime) (pd : p∣q)
    (J : Finset ℕ) (Y S : ℝ) (sp : 0<S) (main : classBalanced J q Y S)
    (extra : classBalanced J (q*p) Y S) (r : (ZMod q)ˣ) (z : ZMod (q*p)) :
    classPart J Y S r (fun j : ℕ => z=(j:ZMod (q*p))) ≤ (9/(p:ℝ))*classWeight J Y S r := by
  classical
  have g (n : ℕ) : 0≤gaussian Y S n := div_nonneg (exp_pos _).le sp.le
  have w : 0≤classWeight J Y S r := sum_nonneg (fun n _=>by split <;> first | exact g n | rfl)
  by_cases unit : IsUnit z
  · obtain ⟨t,ht⟩ := unit
    have le : classPart J Y S r (fun j : ℕ => z=(j:ZMod (q*p))) ≤ classWeight J Y S t := by
      unfold classPart classWeight
      rw [sum_filter]
      apply sum_le_sum
      intro j hj
      rw [ht]
      by_cases yes : z=(j:ZMod (q*p))
      · rw [if_pos yes,if_pos yes]
        split <;> first | rfl | exact g j
      · rw [if_neg yes,if_neg yes]
    have upper := (extra t).2
    have lower := (main r).1
    have tot : (q*p).totient=p*q.totient := by rw [Nat.mul_comm q p,Nat.totient_mul_of_prime_of_dvd pp pd]
    rw [tot,Nat.cast_mul] at upper
    have tp : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr qp
    have pr : (0:ℝ)<p := by exact_mod_cast pp.pos
    apply le.trans
    rw [div_mul_eq_mul_div,le_div_iff₀ pr]
    apply (mul_le_mul_iff_of_pos_right tp).mp
    linarith only [upper,lower]
  · have nz (j : ℕ) (h : z=(j:ZMod (q*p))) : ¬(r:ZMod q)=j := by
      intro eq
      have co := (ZMod.isUnit_iff_coprime j q).mp (eq ▸ r.isUnit)
      have co' := Nat.Coprime.mul_right co (co.of_dvd_right pd)
      exact unit (h ▸ (ZMod.isUnit_iff_coprime j (q*p)).mpr co')
    unfold classPart
    rw [sum_eq_zero (fun j hj=>if_neg (nz j (mem_filter.mp hj).2))]
    positivity

/-- Coarse Gaussian mass of the exceptional qp lift at the actual first
polynomial, uniformly in its ordinary reduced class and the extra lift. -/
theorem PrescribedRows.first_lift_class_loss (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a : ℕ} (R : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → ∀ side : Bool,
    let pre := R.prefactor a side; let q := (firstStep n ell a side).natAbs
    let J := (sieveBand n ell pre).filter (fun t=>¬t∣q)
    let Y := (exactMean n ell a side:ℝ)/pre; let S := oneWidth n ell a/pre
    ∀ p : ℕ, p.Prime → p≤Fixed.A b → p∣q → ∀ (r : (ZMod q)ˣ) (z : ZMod (q*p)),
      classPart J Y S r (fun j : ℕ=>z=(j:ZMod (q*p))) ≤ (9/(p:ℝ))*classWeight J Y S r := by
  obtain ⟨b₁,bal⟩ := constructed_classes_balanced line
  obtain ⟨b₂,deg⟩ := Fixed.degree_grows 10004
  refine ⟨max b₁ b₂,?_⟩
  intro n ell a R b huge hn comp target absent mark side pre q J Y S p pp cap pd r z
  obtain ⟨large,degree⟩ := max_le_iff.mp huge
  have big := deg b degree
  obtain ⟨_,capA,grid,_⟩ := (constructed_marks_iff ..).mp mark
  have am := mark_range hn big capA
  have qp : 0<q := Int.natAbs_pos.mpr (firstStep_size am (mem_dyadicTargets.mp target).1.pos side).2
  have env := first_extra_conductor target cap am side
  have ⟨pos,bound⟩ := R.pre_bounds target a side
  have win : InWindow b Y S := by
    apply one_point_window hn big target capA grid side
    constructor
    · exact_mod_cast pos
    · exact_mod_cast (bound.trans ((Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)).trans
        (Nat.mul_le_mul_left (Fixed.A b) (Nat.pow_le_pow_right (Nat.two_pow_pos _) (by decide : 3≤40)))))
  have joint := bal large hn comp target absent pos bound (Nat.mul_pos qp pp.pos) dvd_rfl (Nat.mul_pos qp pp.pos) env win
  have base := bal large hn comp target absent pos bound qp (dvd_mul_right q p) (Nat.mul_pos qp pp.pos) env win
  have eq : (sieveBand n ell pre).filter (fun t=>¬t∣q*p)=J := by
    ext t
    simp only [J,mem_filter]
    apply and_congr_right
    intro ht
    have pr := (mem_primeBand.mp (mem_filter.mp ht).1).1
    rw [pr.dvd_mul]
    exact ⟨fun h d=>h (Or.inl d),fun h e => e.elim h (fun d=>h (d.trans pd))⟩
  change classBalanced (_ : Finset ℕ) (q*p) Y S at joint
  rw [eq] at joint
  change classBalanced (_ : Finset ℕ) q Y S at base
  rw [eq] at base
  exact lift_class_cost qp pp pd J Y S win.1 base joint r z

private theorem probability_instances {n ell : ℕ} (R : PrescribedRows n ell) (side : Bool)
    (E : ℤ×ℤ→Prop) (i j : DecidablePred E) :
    @prescribedProbability n ell R side E i = @prescribedProbability n ell R side E j := by
  cases Subsingleton.elim i j
  rfl

set_option maxHeartbeats 600000 in
/-- A bad free prime at the second quotient is detected by one residue
filter on the first quotient. Its cost is uniform whether the first conductor
is coprime to the prime or already contains it. -/
theorem PrescribedRows.free_prime_exception_filter (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a y : ℕ} (R : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → y∈(construct n ell 0 0 0 0).marks →
    ∀ (side : Bool) (p : ℕ), p∈R.miss a \ R.hit y →
    let val := fun k : ℤ×ℤ => R.intercept a side k.1 k.2
    let smooth := fun k => supportedValue (sieveBand n ell (R.prefactor a side)) (val k)
    ∃ F : ℤ→Prop, (∀ u v : ℤ, R.compatible side u v →
      p∣(R.intercept y side u v).natAbs → F (R.intercept a side u v)) ∧
      @prescribedProbability n ell R side (fun k=>smooth k ∧ F (val k)) (Classical.decPred _) ≤
        (1+270*exp (-(Fixed.U b:ℝ)))*(18*(Fixed.B b:ℝ)^(-199/400:ℝ))*prescribedProbability R side smooth := by
  classical
  obtain ⟨b₁,lift⟩ := PrescribedRows.first_lift_class_loss line
  obtain ⟨b₂,residue⟩ := PrescribedRows.first_residue_probability line
  obtain ⟨b₃,deg⟩ := Fixed.degree_grows 10004
  refine ⟨max b₁ (max b₂ b₃),?_⟩
  intro n ell a y R b huge hn comp target absent am ym side p free val smooth
  obtain ⟨large,other⟩ := max_le_iff.mp huge
  obtain ⟨small,degree⟩ := max_le_iff.mp other
  have big := deg b degree
  have hp := (mem_sdiff.mp (mem_sdiff.mp free).1).1
  have band := (mem_filter.mp (R.member hp)).1
  obtain ⟨pp,pb,low⟩ := mem_primeBand.mp band
  let q := (firstStep n ell a side).natAbs
  have capP : p≤Fixed.A b := pb.trans (Nat.pow_le_pow_right (by decide : 0<2) (show Fixed.beta b≤10000*Fixed.h b by
    dsimp [Fixed.beta]; omega))
  have pr : 0<(p:ℝ) := by exact_mod_cast pp.pos
  have tp : (2:ℝ)≤p := by exact_mod_cast pp.two_le
  have one : 1≤(p:ℝ) := by linarith only [tp]
  let δ := (Fixed.B b:ℝ)^(-199/400:ℝ)
  have bp : (0:ℝ)<Fixed.B b := by dsimp [Fixed.B]; positivity
  have powCap {α : ℝ} (ha : 199/200≤α) : (p:ℝ)^(-α)≤δ := calc
    _ ≤ (p:ℝ)^(-(199/200):ℝ) := rpow_le_rpow_of_exponent_le one (neg_le_neg ha)
    _ ≤ (sqrt (Fixed.B b:ℝ))^(-(199/200):ℝ) := by
      apply rpow_le_rpow_of_nonpos (sqrt_pos.mpr bp) _ (by norm_num)
      exact (sqrt_le_left pr.le).mpr (by exact_mod_cast low.le)
    _ = δ := by dsimp [δ]; rw [sqrt_eq_rpow,←rpow_mul bp.le]; norm_num
  have inv : (p:ℝ)⁻¹≤δ := by simpa only [rpow_neg_one] using powCap (α:=1) (by norm_num)
  have rate : 9/((p:ℝ)-1) ≤ 18*δ := calc
    _ ≤ 18/(p:ℝ) := by rw [div_le_div_iff₀ (by linarith only [tp]) pr]; linarith only [tp]
    _ ≤ _ := by rw [div_eq_mul_inv]; gcongr
  have pos : 0≤prescribedProbability R side smooth := by
    apply div_nonneg
    · apply tsum_nonneg; intro k; split <;> first | exact mul_nonneg (exp_pos _).le (exp_pos _).le | rfl
    · exact tsum_nonneg (fun _=>mul_nonneg (exp_pos _).le (exp_pos _).le)
  have factor : 0≤1+270*exp (-(Fixed.U b:ℝ)) := by positivity
  by_cases pd : p∣q
  · obtain ⟨z,detect⟩ := R.free_prime_lift hn big comp target absent ym side free
    let F := fun t : ℤ => (z:ZMod (q*p))=t
    refine ⟨F,fun u v ok h=>(detect u v ok h).symm,?_⟩
    obtain ⟨r,transfer⟩ := R.first_filter_transfer hn big comp target absent am side
    have cl := lift R large hn comp target absent am side p pp capP pd r (z:ZMod (q*p))
    have bound := transfer F (9/(p:ℝ)) (by positivity) (by simpa only [F,Int.cast_natCast] using cl)
    have rt : 9/(p:ℝ) ≤ 18*δ := by
      rw [div_eq_mul_inv]
      exact (mul_le_mul_of_nonneg_right (by norm_num : (9:ℝ)≤18) (inv_nonneg.mpr pr.le)).trans
        (mul_le_mul_of_nonneg_left inv (by norm_num))
    rw [probability_instances R side _ (Classical.decPred _) (fun k=>@instDecidableAnd (smooth k) (F (val k)) inferInstance inferInstance)]
    exact bound.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left rt factor) pos)
  · obtain ⟨U,V,z,detect⟩ := R.free_prime_residue hn big comp target absent ym side free
    let F := fun t : ℤ => z=(t:ZMod p)
    refine ⟨F,fun u v ok h=>(detect u v ok h).2.2.2.symm,?_⟩
    obtain ⟨α,range,_,cl⟩ := residue R small hn comp target absent am side
    have bound := cl p pp capP (pp.coprime_iff_not_dvd.mpr pd).symm z
    have rt : (if z=0 then 18*(p:ℝ)^(-α) else 9/((p:ℝ)-1))≤18*δ := by
      split
      · exact mul_le_mul_of_nonneg_left (powCap range.1) (by norm_num)
      · exact rate
    rw [probability_instances R side _ (Classical.decPred _) (fun k=>@instDecidableAnd (smooth k) (F (val k)) inferInstance inferInstance)]
    exact bound.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left rt factor) pos)

end Cogentic.Construction

#print axioms Cogentic.Construction.PrescribedRows.free_prime_residue

#print axioms Cogentic.Construction.PrescribedRows.free_prime_lift

#print axioms Cogentic.Construction.PrescribedRows.free_prime_exception_filter
