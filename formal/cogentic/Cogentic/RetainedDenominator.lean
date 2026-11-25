import Cogentic.CellCountConcentration
import Cogentic.RetainedCellSelection

namespace Cogentic.Construction
open Finset Real Window
open scoped Classical
noncomputable section

/-- Give each cell its specified nominal share and normalize by its actual
number of eligible marks. Each retained smooth mark uses the unrestricted
physical two-field marginal, independently of subsequent row tests. -/
def retainedCommonDenominator (n ell : ℕ) (mix : Option (Bool×Fin (Fixed.d (n.log2+1)))→ℝ)
    (x y : ℤ×ℤ) : ℝ :=
  let O := PrescribedRows.unrestricted n ell
  ∑ c, mix c*((∑ a∈constructorCellMarks n ell c, if keptSmoothMark O O a x y then
    (smoothMarkProbability O O a)⁻¹ else 0)/(constructorCellMarks n ell c).card)

/-- Both coefficient points lie in the actual search box, their executed
first stage returns a relation matrix, and its pooled smooth mass survives. -/
def retainedDenominatorGood (n ell : ℕ) (mix : Option (Bool×Fin (Fixed.d (n.log2+1)))→ℝ)
    (x y : ℤ×ℤ) : Prop :=
  inCoefficientBox n x ∧ inCoefficientBox n y ∧
    (∃ rel,Marking.stageOne (TryPair.fixedInput n ell
      (construct n ell x.1.toNat x.2.toNat y.1.toNat y.2.toNat))=some rel) ∧
    1/2≤retainedCommonDenominator n ell mix x y

/-- A fixed convex mixture of all constructor cells loses at most half of
its nominal physical denominator except on the stated vanishing probability.
The failure event includes both search-box tails and first-stage failure. -/
theorem retained_common_denominator_failure (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1; let O := PrescribedRows.unrestricted n ell
    ∀ mix : Option (Bool×Fin (Fixed.d b))→ℝ, (∀ c,0 ≤ mix c) → (∑ c,mix c)=1 →
    twoFieldProbability O O (fun x y=>¬retainedDenominatorGood n ell mix x y) ≤
      256/(Fixed.d b:ℝ)+4*exp (-(Fixed.z b:ℝ)^2)+1/(Fixed.B b:ℝ) := by
  classical
  obtain ⟨b₁,count⟩ := cell_count_score_error line 1 (by decide)
  obtain ⟨n₂,marks⟩ := grid_cells_have_marks line
  obtain ⟨b₃,deleted⟩ := rejected_score_loss line 1 le_rfl
  obtain ⟨b₄,degree⟩ := Fixed.degree_grows 10004
  let b₀ := max b₁ (max b₃ (max b₄ 1000))
  refine ⟨max n₂ (max 2 (2^b₀)),?_⟩
  intro n large ell target composite sieve b O mix mixpos mixtotal
  obtain ⟨old,rest⟩ := max_le_iff.mp large
  obtain ⟨hn,lim⟩ := max_le_iff.mp rest
  have big : b₀≤b := ((Nat.le_log2 (by omega : n≠0)).mpr lim).trans (Nat.le_succ _)
  obtain ⟨bcount,other⟩ := max_le_iff.mp big
  obtain ⟨bloss,other⟩ := max_le_iff.mp other
  obtain ⟨bdeg,bbig⟩ := max_le_iff.mp other
  let d : ℝ := Fixed.d b
  let M : ℝ := cellMarkCount b
  let e := exp (-(Fixed.z b:ℝ)^2)
  let I := Option (Bool×Fin (Fixed.d b))
  let X (c : I) := constructorCellMarks n ell c
  let N (c : I) := ((X c).card:ℝ)
  let Ω := O.CoeffPoint false×O.CoeffPoint true
  let W := twoFieldWeight O O
  let E := smoothMarkEvent O false; let F := smoothMarkEvent O true
  let w := fun a=>(smoothMarkProbability O O a)⁻¹
  let score (c : I) (t : Ω) := twoFieldScore (X c) w E F t.1.val t.2.val
  let loss (c : I) (t : Ω) := ∑ a∈X c,if rejectedSmoothMark O O a t.1.val t.2.val then w a else 0
  let kept (c : I) (t : Ω) := ∑ a∈X c,if keptSmoothMark O O a t.1.val t.2.val then w a else 0
  let cost (c : I) (t : Ω) := (score c t-N c)^2/(N c)^2+loss c t/N c
  let total (t : Ω) := ∑ c:I,mix c*cost c t
  have dp : 0<d := by dsimp only [d];exact_mod_cast Fixed.degree_pos (Nat.succ_pos n.log2)
  have mp : 0<M := by dsimp [M,cellMarkCount];positivity
  have cop (a : ℕ) : (O.prefactor a false).Coprime (O.prefactor a true) :=
    (O.prefactors_coprime_iff O ((by decide : 3≤10004).trans (degree b bdeg)) target a).mpr
      (by simp [O,PrescribedRows.unrestricted,PrescribedRows.hit])
  have dense (c : I) : M/8≤N c := by
    have c4 : 1≤(Fixed.B b)^4 := Nat.succ_le_of_lt (pow_pos (Nat.pow_pos (by decide)) _)
    have gc := marks n old ell target composite sieve 1 0 0 0 0 0 c (by decide) c4
      (fun p hp dvd=>((Nat.prime_of_mem_primeFactors hp).ne_one (Nat.eq_one_of_dvd_one dvd)).elim)
    simp only [Nat.modEq_one,filter_true,Nat.cast_one,div_one] at gc
    change M/8 ≤ N c at gc
    exact gc
  have np (c : I) : 0<N c := (by positivity : 0<M/8).trans_le (dense c)
  have wn (t : Ω) : 0≤W t := mul_nonneg (O.pointMass_nonneg ..) (O.pointMass_nonneg ..)
  have pn (a : ℕ) : 0≤w a := inv_nonneg.mpr (mul_nonneg (O.probability_unit target false _).1 (O.probability_unit target true _).1)
  have l0 (c : I) (t : Ω) : 0≤loss c t := sum_nonneg (fun a _=>by split <;> first | exact pn a | rfl)
  have c0 (t : Ω) : 0≤total t := sum_nonneg (fun c _=>mul_nonneg (mixpos c)
    (add_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (div_nonneg (l0 c t) (np c).le)))
  have expected (c : I) : ∃ v,HasSum (fun t:Ω=>W t*cost c t) v ∧ v≤64/d+e := by
    let V := twoFieldSecond O O (X c) w E F-2*N c*twoFieldMean O O (X c) w E F+(N c)^2
    have raw := (count O O bcount hn composite target sieve c).2
    simp only [Nat.cast_one,one_mul] at raw
    change V/M^2 ≤ 1/d at raw
    have square := pow_le_pow_left₀ (by positivity : 0≤M/8) (dense c) 2
    have fixed : V/(N c)^2≤64/d := by
      have v := (div_le_iff₀ (sq_pos_of_pos mp)).mp raw
      apply (div_le_iff₀ (sq_pos_of_pos (np c))).mpr
      apply v.trans
      have h := mul_le_mul_of_nonneg_left square (show 0≤64/d by positivity)
      exact (show 1/d*M^2=64/d*(M/8)^2 by ring).le.trans h
    obtain ⟨μ,ex,ub⟩ := deleted O O bloss hn composite target sieve (X c) (fun _=>1) (fun a ha=>(mem_filter.mp ha).2) (fun a _=>cop a)
    simp only [abs_one,one_div,sum_const,nsmul_one,neg_one_mul] at ex ub
    change μ≤e*N c at ub
    have h₁ := (twoField_score_error O O target (X c) w E F (N c)).div_const ((N c)^2)
    refine ⟨V/(N c)^2+μ/N c,?_,add_le_add fixed ((div_le_iff₀ (np c)).mpr ub)⟩
    apply (h₁.add (ex.div_const (N c))).congr_fun
    intro t
    change W t*((score c t-N c)^2/(N c)^2+loss c t/N c)=W t*(score c t-N c)^2/(N c)^2+W t*loss c t/N c
    ring
  choose μ hμ bound using expected
  have totalSum : HasSum (fun t:Ω=>W t*total t) (∑ c:I,mix c*μ c) := by
    apply (hasSum_sum (s:=(univ:Finset I)) (fun c _=>(hμ c).mul_left (mix c))).congr_fun
    intro t;dsimp only [total];rw [mul_sum];apply sum_congr rfl;intro c _;ring
  have totalBound : (∑ c:I,mix c*μ c)≤64/d+e := by
    have h := sum_le_sum (s:=(univ:Finset I)) (fun c _=>mul_le_mul_of_nonneg_left (bound c) (mixpos c))
    rw [←sum_mul,mixtotal,one_mul] at h;exact h
  have keep_near (t : Ω) (bx : inCoefficientBox n t.1.val) (by' : inCoefficientBox n t.2.val) :
      3/4-total t≤retainedCommonDenominator n ell mix t.1.val t.2.val := by
    have each (c : I) : 3/4-cost c t≤kept c t/N c := by
      have partition : score c t=kept c t+loss c t := by
        dsimp only [score,kept,loss,twoFieldScore]
        rw [←sum_add_distrib];apply sum_congr rfl;intro a _
        let ret := ∃ rel, Marking.stageOne (TryPair.fixedInput n ell
          (construct n ell t.1.val.1.toNat t.1.val.2.toNat t.2.val.1.toNat t.2.val.2.toNat))=some rel ∧ a∈rel.marks
        change _ = (if keptSmoothMark O O a t.1.val t.2.val then w a else 0)+(if rejectedSmoothMark O O a t.1.val t.2.val then w a else 0)
        by_cases smooth : E a t.1.val ∧ F a t.2.val <;> by_cases yes : ret <;>
          simp_all only [keptSmoothMark,rejectedSmoothMark,E,F,ret,and_true,and_false,
            if_true,if_false,not_true_eq_false,not_false_eq_true,mul_one,mul_zero,add_zero,zero_add]
      change 3/4-((score c t-N c)^2/(N c)^2+loss c t/N c)≤kept c t/N c
      have positive := np c
      rw [show kept c t=score c t-loss c t by linarith only [partition]]
      field_simp
      nlinarith only [sq_nonneg (2*score c t-N c)]
    have h := sum_le_sum (s:=(univ:Finset I)) (fun c _=>mul_le_mul_of_nonneg_left (each c) (mixpos c))
    simp_rw [mul_sub] at h;rw [sum_sub_distrib,←sum_mul,mixtotal,one_mul] at h
    exact h
  let outside (x : ℤ×ℤ) := ¬inCoefficientBox n x
  let l (t : Ω) : ℝ := if outside t.1.val then 1 else 0
  let r (t : Ω) : ℝ := if outside t.2.val then 1 else 0
  have unit (s : Bool) : prescribedProbability O s (fun _=>True)=1 := by
    unfold prescribedProbability
    simp only [if_true,div_self (O.weight_normalizer target s).1.ne']
  have left := twoField_rectangle O O target outside (fun _=>True)
  have right := twoField_rectangle O O target (fun _=>True) outside
  simp only [and_true,unit true,mul_one] at left
  simp only [true_and,unit false,one_mul] at right
  have budget := ((totalSum.mul_left 4).add left).add right
  have mass := twoField_total O O target
  let bad (t : Ω) := ¬retainedDenominatorGood n ell mix t.1.val t.2.val
  have each (t : Ω) : (if bad t then W t else 0)≤4*(W t*total t)+W t*l t+W t*r t := by
    have wp := wn t
    have tt := mul_nonneg wp (c0 t)
    by_cases bx : inCoefficientBox n t.1.val <;> by_cases by' : inCoefficientBox n t.2.val
    · simp only [l,r,outside,bx,by',not_true_eq_false,if_false,mul_zero,add_zero]
      by_cases bt : bad t
      · rw [if_pos bt]
        have floor : 1≤4*total t := by
          by_contra! cheap
          have enough := keep_near t bx by'
          have fraction : 1/2≤retainedCommonDenominator n ell mix t.1.val t.2.val := by linarith
          apply bt
          refine ⟨bx,by',?_,fraction⟩
          cases hs : Marking.stageOne (TryPair.fixedInput n ell (construct n ell t.1.val.1.toNat t.1.val.2.toNat t.2.val.1.toNat t.2.val.2.toNat)) with
          | some rel => exact ⟨rel,rfl⟩
          | none =>
            have empty (a : ℕ) : ¬keptSmoothMark O O a t.1.val t.2.val := by
              intro h;obtain ⟨rel,ok,_⟩ := h.2.2;rw [hs] at ok;contradiction
            simp [retainedCommonDenominator,empty,O] at fraction
            norm_num at fraction
        exact (le_mul_of_one_le_right wp floor).trans_eq (by ring)
      · simp only [if_neg bt];linarith only [tt]
    · simp [l,r,outside,bx,by'];split <;> linarith only [wp,tt]
    · simp [l,r,outside,bx,by'];split <;> linarith only [wp,tt]
    · simp [l,r,outside,bx,by'];split <;> linarith only [wp,tt]
  have summable : Summable (fun t:Ω=>if bad t then W t else 0) := Summable.of_nonneg_of_le
    (fun t=>by split <;> first | exact wn t | rfl) (fun t=>by split <;> first | exact le_rfl | exact wn t) mass.summable
  have compare := summable.tsum_le_tsum each budget.summable
  rw [budget.tsum_eq] at compare
  have tail := coefficient_tail_lt_half_mark (b:=b) bbig
  have tailBound (s : Bool) : prescribedProbability O s outside ≤
      1216*(Fixed.B b:ℝ)^2*exp (-π*((b:ℝ)^2)^2/2) := by
    by_contra! overflow
    obtain ⟨_,_,boxed,out⟩ := O.box_witness target s outside overflow
    exact out boxed
  have tl := tailBound false
  have tr := tailBound true
  have event_eq : twoFieldProbability O O (fun x y=>¬retainedDenominatorGood n ell mix x y) =
      ∑' t:Ω,if bad t then W t else 0 := by
    unfold twoFieldProbability
    apply tsum_congr;intro t;by_cases h : bad t <;> simp_all only [bad,W,if_false]
  rw [event_eq]
  change _ ≤ 256/d+4*e+1/(Fixed.B b:ℝ)
  rw [show 1/(2*(Fixed.B b:ℝ))=(1/(Fixed.B b:ℝ))/2 by ring] at tail
  apply compare.trans
  rw [show 256/d+4*e=4*(64/d+e) by ring]
  linarith only [totalBound,tail,tl,tr]

/-- Other nonnegative entry and deletion costs can be tested on the very
same boxed draw. Their total expectation may use all the remaining budget. -/
theorem retained_denominator_with_tests (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1; let O := PrescribedRows.unrestricted n ell
    ∀ mix : Option (Bool×Fin (Fixed.d b))→ℝ, (∀ c, 0 ≤ mix c) → (∑ c,mix c)=1 →
    ∀ (cost : O.CoeffPoint false × O.CoeffPoint true→ℝ) (budget : ℝ), (∀ t,0≤cost t) →
    HasSum (fun t=>twoFieldWeight O O t*cost t) budget →
    budget+(256/(Fixed.d b:ℝ)+4*exp (-(Fixed.z b:ℝ)^2)+1/(Fixed.B b:ℝ))<1 →
    ∃ t : O.CoeffPoint false × O.CoeffPoint true,
      retainedDenominatorGood n ell mix t.1.val t.2.val ∧ cost t<1 := by
  classical
  obtain ⟨n₀,failure⟩ := retained_common_denominator_failure line
  refine ⟨n₀,?_⟩
  intro n hn ell target comp sieve b O mix pos norm cost budget nonneg ex fit
  let Ω := O.CoeffPoint false × O.CoeffPoint true
  let W := twoFieldWeight O O
  let bad (t : Ω) := ¬retainedDenominatorGood n ell mix t.1.val t.2.val
  have wp (t : Ω) : 0≤W t := mul_nonneg (O.pointMass_nonneg ..) (O.pointMass_nonneg ..)
  have mass := twoField_total O O target
  have sumBad : Summable (fun t:Ω=>if bad t then W t else 0) := Summable.of_nonneg_of_le
    (fun t=>by split <;> first | exact wp t | rfl) (fun t=>by split <;> first | exact le_rfl | exact wp t) mass.summable
  have fail := failure n hn ell target comp sieve mix pos norm
  have event_eq : twoFieldProbability O O (fun x y=>¬retainedDenominatorGood n ell mix x y) =
      ∑' t:Ω,if bad t then W t else 0 := by
    unfold twoFieldProbability
    apply tsum_congr;intro t;by_cases h : bad t <;> simp_all only [bad,W,if_false]
  rw [event_eq] at fail
  by_contra! no
  have cmp (t : Ω) : W t ≤ (if bad t then W t else 0)+W t*cost t := by
    by_cases f : bad t
    · rw [if_pos f];exact le_add_of_nonneg_right (mul_nonneg (wp t) (nonneg t))
    · rw [if_neg f,zero_add]
      exact le_mul_of_one_le_right (wp t) (no t (Classical.not_not.mp f))
  have both := sumBad.hasSum.add ex
  have h := mass.summable.tsum_le_tsum cmp both.summable
  rw [mass.tsum_eq,both.tsum_eq] at h
  linarith only [h,fail,fit]

/-- The explicit failure budget tends to zero uniformly in the target and
the chosen mixture. -/
theorem retained_denominator_budget_vanishes (k : ℕ) (hk : 0<k) :
    ∃ b₀ : ℕ, ∀ b≥b₀, 256/(Fixed.d b:ℝ)+4*exp (-(Fixed.z b:ℝ)^2)+1/(Fixed.B b:ℝ) ≤ 1/(k:ℝ) := by
  obtain ⟨b₁,grows⟩ := Fixed.degree_grows (1024*k)
  obtain ⟨b₂,tiny⟩ := fixed_class_accuracy (8*(k:ℝ))
  refine ⟨max b₁ b₂,?_⟩
  intro b hb
  obtain ⟨left,right⟩ := max_le_iff.mp hb
  have high := grows b left
  have hi : 1024*(k:ℝ)≤(Fixed.d b:ℝ) := by exact_mod_cast high
  have kp : (0:ℝ)<k := Nat.cast_pos.mpr hk
  have dp : (0:ℝ)<Fixed.d b := by linarith
  have db : Fixed.d b ≤ Fixed.B b := by
    apply (Nat.lt_two_pow_self (n:=Fixed.d b)).le.trans
    apply Nat.pow_le_pow_right (by decide : 0<2)
    have zpos : 1≤Fixed.z b := Nat.succ_pos _
    dsimp only [Fixed.beta,Fixed.h]
    nlinarith only [Nat.mul_le_mul_left (Fixed.d b) zpos]
  have db' : (Fixed.d b:ℝ)≤Fixed.B b := Nat.cast_le.mpr db
  have bp : (0:ℝ)<Fixed.B b := dp.trans_le db'
  have one : 256/(Fixed.d b:ℝ)≤(1/(k:ℝ))/4 := by
    rw [div_div,div_le_div_iff₀ dp (by positivity)];linarith only [hi]
  have two : 4*exp (-(Fixed.z b:ℝ)^2)≤(1/(k:ℝ))/4 := by
    rw [div_div,le_div_iff₀ (by positivity)];nlinarith only [tiny b right]
  have three : 1/(Fixed.B b:ℝ)≤(1/(k:ℝ))/4 := by
    rw [div_div,div_le_div_iff₀ bp (by positivity)];linarith only [hi,db',kp]
  linarith only [one,two,three,one_div_pos.mpr kp]

end
end Cogentic.Construction
#print axioms Cogentic.Construction.retained_common_denominator_failure

#print axioms Cogentic.Construction.retained_denominator_with_tests
#print axioms Cogentic.Construction.retained_denominator_budget_vanishes
