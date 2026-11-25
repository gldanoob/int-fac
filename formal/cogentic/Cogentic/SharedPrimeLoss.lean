import Cogentic.PolynomialExceptions
import Cogentic.SmoothBox
import Cogentic.PolynomialSmooth

namespace Cogentic.Construction
open Real Cogentic.Window Finset

private theorem class_deletion (J P : Finset ℕ) (pr : ∀ p∈J, p.Prime) (Y S : ℝ)
    (sp : 0<S) {q : ℕ} (r : (ZMod q)ˣ) :
    classWeight J Y S r ≤ classWeight (J\P) Y S r +
      ∑ p∈J∩P, classPart J Y S r (p∣·) := by
  classical
  let D := J∩P
  let good := fun n : ℕ => ∀ p∈D, ¬p∣n
  have eq : squarefreeSupport (J\P) = (squarefreeSupport J).filter good := by
    ext n
    rw [mem_filter,mem_squarefreeSupport J pr,mem_squarefreeSupport _ (fun p h => pr p (mem_sdiff.mp h).1)]
    constructor
    · rintro ⟨sf,fac⟩
      refine ⟨⟨sf,fun p h => (mem_sdiff.mp (fac h)).1⟩,?_⟩
      intro p hp dv
      have pf := Nat.mem_primeFactors.mpr ⟨pr p (mem_inter.mp hp).1,dv,sf.ne_zero⟩
      exact (mem_sdiff.mp (fac pf)).2 (mem_inter.mp hp).2
    · rintro ⟨⟨sf,fac⟩,hg⟩
      exact ⟨sf,fun p hp => mem_sdiff.mpr ⟨fac hp,fun hP => hg p (mem_inter.mpr ⟨fac hp,hP⟩) (Nat.dvd_of_mem_primeFactors hp)⟩⟩
  let w := fun n : ℕ => if (r:ZMod q)=n then gaussian Y S n else 0
  have pos (n) : 0≤w n := by dsimp [w]; split <;> first | exact (div_pos (exp_pos _) sp).le | rfl
  change (∑ n ∈ squarefreeSupport J, w n) ≤ (∑ n ∈ squarefreeSupport (J\P), w n) +
    ∑ p ∈ D, ∑ n ∈ (squarefreeSupport J).filter (p∣·), w n
  rw [eq,sum_filter]
  simp_rw [sum_filter]
  rw [sum_comm,←sum_add_distrib]
  apply sum_le_sum
  intro n _
  by_cases clean : good n
  · rw [if_pos clean]
    exact le_add_of_nonneg_right (sum_nonneg (fun p _ => by split <;> first | exact pos n | rfl))
  · rw [if_neg clean,zero_add]
    change ¬∀ p∈D, ¬p∣n at clean
    push Not at clean
    obtain ⟨p,hp,divides⟩ := clean
    exact (show w n = (if p∣n then w n else 0) by rw [if_pos divides]).le.trans
      (single_le_sum (fun t _ => show 0 ≤ (if t∣n then w n else 0) by split <;> first | exact pos n | rfl) hp)

private theorem scalar_reduced_real (J : Finset ℕ) (pr : ∀ p∈J, p.Prime) (c s : ℤ) (sn : s≠0)
    (cop : commonDivisor c s=1) (Y S : ℝ) :
    let q := s.natAbs
    let r : (ZMod q)ˣ := ZMod.unitOfCoprime (scalarResidue c s) cop
    (scalarMass J c s Y S).re = (q:ℝ)*classWeight (J.filter (fun p => ¬p∣q)) Y S r := by
  let q := s.natAbs; let r := ZMod.unitOfCoprime (scalarResidue c s) cop
  let : NeZero q := ⟨Int.natAbs_ne_zero.mpr sn⟩
  have rr : (r:ZMod q)=c := (ZMod.coe_unitOfCoprime _ _).trans (ZMod.natCast_zmod_val _)
  have h := gaussian_affine_classMass J c s sn r rr Y S
  rw [←coe_classWeight] at h
  have e := congrArg Complex.re h
  simp only [←Complex.ofReal_natCast,←Complex.ofReal_mul,Complex.ofReal_re] at e
  change (scalarMass J c s Y S).re = (q:ℝ)*classWeight J Y S r at e
  have diff : J\q.primeFactors=J.filter (fun p => ¬p∣q) := by
    ext p; by_cases h : p∈J
    · simp [h,Nat.mem_primeFactors,pr p h,NeZero.ne q]
    · simp [h]
  exact e.trans (congrArg ((q:ℝ)*·) ((classWeight_coprime J pr Y S r).trans (by rw [diff])))

private theorem weight_cap {b p : ℕ} (mem : p∈primeBand b) {α : ℝ} (ha : 199/200≤α) :
    primeProbability α p ≤ (Fixed.B b:ℝ)^(-199/400:ℝ) := by
  obtain ⟨pp,_,hp⟩ := mem_primeBand.mp mem
  have pos : 0<(p:ℝ) := by exact_mod_cast pp.pos
  have one : 1≤(p:ℝ) := by exact_mod_cast pp.one_le
  have weight := rpow_nonneg pos.le (-α)
  have Bp : (0:ℝ)<Fixed.B b := by dsimp [Fixed.B]; positivity
  calc primeProbability α p ≤ (p:ℝ)^(-α) := div_le_self weight (by linarith only [weight])
       _ ≤ (p:ℝ)^(-(199/200):ℝ) := rpow_le_rpow_of_exponent_le one (neg_le_neg ha)
       _ ≤ (sqrt (Fixed.B b:ℝ))^(-(199/200):ℝ) := by
         apply rpow_le_rpow_of_nonpos (sqrt_pos.mpr Bp) _ (by norm_num)
         exact (sqrt_le_left pos.le).mpr (by exact_mod_cast hp.le)
       _ = _ := by rw [sqrt_eq_rpow,←rpow_mul Bp.le]; norm_num

/-- Deleting an arbitrary polynomial-sized set of primes leaves at least
three quarters of the true first smooth class at the constructed conductor. -/
theorem prescribed_class_exclusions_sharp (line : DirichletLZerosOnLine) (k : ℕ) :
    ∃ b₀ : ℕ, ∀ {n ell a : ℕ} (R : PrescribedRows n ell), b₀≤n.log2+1 → 2≤n → ¬n.Prime →
    ell∈dyadicTargets (Fixed.beta (n.log2+1)) →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → ∀ (side : Bool) (u v : ℤ), R.compatible side u v →
    let b := n.log2+1; let pre := R.prefactor a side; let q := (firstStep n ell a side).natAbs
    let Y := (exactMean n ell a side:ℝ)/pre; let S := oneWidth n ell a/pre
    let J := (sieveBand n ell pre).filter (fun t => ¬t∣q)
    ∀ (P : Finset ℕ), P.card≤b^k → ∀ r : (ZMod q)ˣ,
      3/4*classWeight J Y S r ≤ classWeight (J\P) Y S r ∧
      (1-18*(P.card:ℝ)*(Fixed.B b:ℝ)^(-199/400:ℝ))*classWeight J Y S r ≤ classWeight (J\P) Y S r := by
  classical
  obtain ⟨n₁,exception⟩ := first_polynomial_exceptional line
  obtain ⟨n₂,overhead⟩ := fixed_prime_overhead 0 le_rfl (k+1)
  obtain ⟨n₃,degree⟩ := Fixed.degree_grows 10004
  refine ⟨max n₁ (max n₂ (max 18 n₃)),?_⟩
  intro n ell a R huge hn comp target absent mark side u v ok b pre q Y S J P small r
  obtain ⟨i,rest⟩ := max_le_iff.mp huge
  obtain ⟨j,rest⟩ := max_le_iff.mp rest
  obtain ⟨b18,k₀⟩ := max_le_iff.mp rest
  obtain ⟨α,ha,_,exc⟩ := exception R i hn comp target absent mark side u v ok
  have big := degree b k₀
  obtain ⟨_,cap,grid,_⟩ := (constructed_marks_iff n ell 0 0 0 0 a).mp mark
  have data := (first_polynomial_data R hn big comp target absent mark side u v ok).2.2
  have sp : 0<S := div_pos data.width (by exact_mod_cast data.prepos)
  have band (p : ℕ) (h : p∈J) : p∈primeBand b := (mem_filter.mp (mem_filter.mp h).1).1
  have pr (p : ℕ) (h : p∈J) := (mem_primeBand.mp (band p h)).1
  let W := classWeight J Y S r
  let δ := (Fixed.B b:ℝ)^(-199/400:ℝ)
  have wp : 0≤W := sum_nonneg (fun n _ => by split <;> first | exact (div_pos (exp_pos _) sp).le | rfl)
  have δp : 0≤δ := rpow_nonneg (Nat.cast_nonneg _) _
  have sum : (∑ p∈J∩P, classPart J Y S r (p∣·)) ≤ (18*δ*W)*(J∩P).card := by
    calc _ ≤ ∑ _p∈J∩P, 18*δ*W := sum_le_sum (fun p h => by
           have pj := (mem_inter.mp h).1
           have Bcap : Fixed.B b ≤ Fixed.A b := Nat.pow_le_pow_right (by decide) (by dsimp [Fixed.beta]; omega)
           have cop := ((pr p pj).coprime_iff_not_dvd.mpr (mem_filter.mp pj).2).symm
           have hz := (exc p (pr p pj) ((mem_primeBand.mp (band p pj)).2.1.trans Bcap) cop r).2
           exact hz.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (weight_cap (band p pj) ha.1) (by norm_num)) wp))
         _ = _ := by simp [mul_comm]
  have fits : 18*(J∩P).card ≤ b^(k+1) := by
    rw [pow_succ, Nat.mul_comm (b^k)]
    exact Nat.mul_le_mul b18 ((card_le_card inter_subset_right).trans small)
  have overhead' := overhead b j (range (18*(J∩P).card)) (by simpa using fits)
  simp only [zero_mul,zero_add,card_range,Nat.cast_mul,Nat.cast_ofNat] at overhead'
  change 18*((J∩P).card:ℝ)*δ≤1/4 at overhead'
  have loss := class_deletion J P pr Y S sp r
  change W ≤ _+_ at loss
  constructor
  · linarith only [loss,sum,mul_le_mul_of_nonneg_right overhead' wp]
  · have card : ((J∩P).card:ℝ)≤P.card := by exact_mod_cast card_le_card inter_subset_right
    have bigSum := sum.trans (mul_le_mul_of_nonneg_left card (mul_nonneg (mul_nonneg (by norm_num) δp) wp))
    change (1-18*(P.card:ℝ)*δ)*W ≤ _
    linarith only [loss,bigSum]


theorem prescribed_class_exclusions (line : DirichletLZerosOnLine) (k : ℕ) :
    ∃ b₀ : ℕ, ∀ {n ell a : ℕ} (R : PrescribedRows n ell), b₀≤n.log2+1 → 2≤n → ¬n.Prime →
    ell∈dyadicTargets (Fixed.beta (n.log2+1)) →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → ∀ (side : Bool) (u v : ℤ), R.compatible side u v →
    let b := n.log2+1; let pre := R.prefactor a side; let q := (firstStep n ell a side).natAbs
    let Y := (exactMean n ell a side:ℝ)/pre; let S := oneWidth n ell a/pre
    let J := (sieveBand n ell pre).filter (fun t => ¬t∣q)
    ∀ (P : Finset ℕ), P.card≤b^k → ∀ r : (ZMod q)ˣ,
      3/4*classWeight J Y S r ≤ classWeight (J\P) Y S r := by
  obtain ⟨b₀,loss⟩ := prescribed_class_exclusions_sharp line k
  refine ⟨b₀,?_⟩
  intro n ell a R big hn comp target absent mark side u v ok b pre q Y S J P small r
  exact (loss R big hn comp target absent mark side u v ok P small r).1

/-- The actual first-mark coefficient law retains at least half its smooth
probability when any polynomial-sized set of primes is excluded from the
signed quotient. Both probabilities use the original compatible pairs. -/
theorem PrescribedRows.smooth_probability_avoid_sharp (line : DirichletLZerosOnLine) (k : ℕ) :
    ∃ b₀ : ℕ, ∀ {n ell a : ℕ} (R : PrescribedRows n ell),
    let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → ∀ (side : Bool) (P : Finset ℕ), P.card≤b^k →
    let J := sieveBand n ell (R.prefactor a side)
    let prob := fun T : Finset ℕ => prescribedProbability R side
      (fun x => supportedValue T (R.intercept a side x.1 x.2))
    1/(2*(Fixed.B b:ℝ)) ≤ prob (J\P) ∧ prob J/2 ≤ prob (J\P) ∧
      prob J - prob (J\P) ≤ (36*(P.card:ℝ)*(Fixed.B b:ℝ)^(-199/400:ℝ) +
        360*exp (-(Fixed.U b:ℝ)))*prob J := by
  classical
  obtain ⟨b₁,loss⟩ := prescribed_class_exclusions_sharp line k
  obtain ⟨b₂,floor⟩ := PrescribedRows.smooth_probability_lower line
  obtain ⟨b₃,degree⟩ := Fixed.degree_grows 10004
  refine ⟨max b₁ (max b₂ b₃),?_⟩
  intro n ell a R b huge hn comp target absent mark side P small J prob
  obtain ⟨one,two,three⟩ := (max_le_iff.trans (and_congr_right (fun _ => max_le_iff))).mp huge
  have big := degree b three
  obtain ⟨_,cap,_,_⟩ := (constructed_marks_iff n ell 0 0 0 0 a).mp mark
  obtain ⟨u,v,ok,estimate⟩ := R.first_band_probability ((by decide : 3≤10004).trans big)
    target cap (mark_range hn big cap) side
  let c := R.intercept a side u v
  let s := firstStep n ell a side
  let q := s.natAbs
  let pre : ℝ := R.prefactor a side
  let Y := (exactMean n ell a side:ℝ)/pre
  let S := oneWidth n ell a/pre
  let m := fun T => (scalarMass T c s Y S).re
  let ε := 90*exp (-(Fixed.U b:ℝ))
  obtain ⟨cop,_,data⟩ := first_polynomial_data R hn big comp target absent mark side u v ok
  change commonDivisor c s=1 at cop
  let r : (ZMod q)ˣ := ZMod.unitOfCoprime (scalarResidue c s) cop
  have pr (p : ℕ) (h : p∈J) := (mem_primeBand.mp (mem_filter.mp h).1).1
  have red (T : Finset ℕ) (sub : T⊆J) :
      m T=(q:ℝ)*classWeight (T.filter (fun p => ¬p∣q)) Y S r :=
    scalar_reduced_real T (fun p h => pr p (sub h)) c s data.nonzero cop Y S
  have diff : (J\P).filter (fun p => ¬p∣q)=(J.filter (fun p => ¬p∣q))\P := by
    ext p; simp; tauto
  have kept : 3/4*m J ≤ m (J\P) := by
    rw [red J Subset.rfl,red _ sdiff_subset,diff]
    have keptClass := loss R one hn comp target absent mark side u v ok P small r
    linarith only [mul_le_mul_of_nonneg_left keptClass.1 (Nat.cast_nonneg (α:=ℝ) q)]
  have ep : 0<ε := by dsimp [ε]; positivity
  have dp := Fixed.degree_pos (b:=b) (Nat.succ_pos _)
  have vp : 0<Fixed.v b := Nat.mul_pos dp (Nat.mul_pos dp (Nat.succ_pos _))
  have up : 720≤(Fixed.U b:ℝ) := by
    exact_mod_cast (by decide : 720≤2^10).trans (Nat.pow_le_pow_right (by decide : 0<2) (by omega))
  have shift : ε≤1/8 := by
    dsimp [ε]
    rw [exp_neg,←div_eq_mul_inv,div_le_iff₀ (exp_pos _)]
    linarith only [up,add_one_le_exp (Fixed.U b:ℝ)]
  have bounds (T) : -(1/8)*m T ≤ prob T-m T ∧ prob T-m T ≤ 1/8*m T := by
    have e : |prob T-m T|≤ε*m T := estimate T
    have mp : 0 ≤ m T := nonneg_of_mul_nonneg_right ((abs_nonneg _).trans e) ep
    simpa only [neg_mul] using abs_le.mp (e.trans (mul_le_mul_of_nonneg_right shift mp))
  have half : prob J/2≤prob (J\P) := by
    linarith only [(bounds J).2,(bounds (J\P)).1,kept,
      (show 0 ≤ m J from nonneg_of_mul_nonneg_right ((abs_nonneg _).trans (estimate J)) ep)]
  let lossRate : ℝ := 18*(P.card:ℝ)*(Fixed.B b:ℝ)^(-199/400:ℝ)
  have mpos (T : Finset ℕ) : 0 ≤ m T := nonneg_of_mul_nonneg_right ((abs_nonneg _).trans (estimate T)) ep
  have graded : (1-lossRate)*m J ≤ m (J\P) := by
    rw [red J Subset.rfl,red _ sdiff_subset,diff]
    have hl := (loss R one hn comp target absent mark side u v ok P small r).2
    change (1-lossRate)*_ ≤ _ at hl
    linarith only [mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α:=ℝ) q)]
  have upper : m J≤2*prob J := by linarith only [(bounds J).1,mpos J]
  have ratePos : 0≤lossRate := by dsimp [lossRate]; positivity
  have keepProb := (abs_le.mp (estimate (J\P))).1
  have fullProb := (abs_le.mp (estimate J)).2
  have good := mul_le_mul_of_nonneg_left graded (show 0≤1-ε by linarith only [shift])
  have sharp : prob J - prob (J\P) ≤ (2*lossRate+4*ε)*prob J := by
    have remain : 0≤ε*(lossRate*m J) := mul_nonneg ep.le (mul_nonneg ratePos (mpos J))
    linarith only [keepProb,fullProb,good,remain,mul_le_mul_of_nonneg_left upper (show 0≤lossRate+2*ε by positivity)]
  refine ⟨le_trans ?_ half,half,?_⟩
  · have h : 1/(Fixed.B b:ℝ) ≤ prob J := floor R two hn comp target absent mark side
    calc _ = (1/(Fixed.B b:ℝ))/2 := by rw [div_div,mul_comm]
         _ ≤ _ := div_le_div_of_nonneg_right h (by norm_num)
  · dsimp only [lossRate,ε] at sharp
    convert sharp using 1 <;> ring


theorem PrescribedRows.smooth_probability_avoid (line : DirichletLZerosOnLine) (k : ℕ) :
    ∃ b₀ : ℕ, ∀ {n ell a : ℕ} (R : PrescribedRows n ell),
    let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → ∀ (side : Bool) (P : Finset ℕ), P.card≤b^k →
    let J := sieveBand n ell (R.prefactor a side)
    let prob := fun T : Finset ℕ => prescribedProbability R side
      (fun x => supportedValue T (R.intercept a side x.1 x.2))
    1/(2*(Fixed.B b:ℝ)) ≤ prob (J\P) ∧ prob J/2 ≤ prob (J\P) := by
  obtain ⟨b₀,bound⟩ := PrescribedRows.smooth_probability_avoid_sharp line k
  refine ⟨b₀,?_⟩
  intro n ell a R b big hn comp target absent mark side P small J prob
  have h := bound R big hn comp target absent mark side P small
  exact ⟨h.1,h.2.1⟩

/-- Deleting the prime divisors of a nonzero integer from the support
imposes exactly coprimality of the signed quotient to that integer. -/
theorem supportedValue_exclude_primeFactors (J : Finset ℕ) (pr : ∀ p∈J, p.Prime)
    (z : ℤ) {m : ℕ} (hm : m≠0) :
    supportedValue (J\m.primeFactors) z ↔ supportedValue J z ∧ m.Coprime z.natAbs := by
  classical
  have pr' (p : ℕ) (h : p∈J\m.primeFactors) := pr p (mem_sdiff.mp h).1
  constructor
  · intro ev
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ev
    obtain ⟨sf,sub⟩ := (mem_squarefreeSupport _ pr' _).mp hx
    refine ⟨mem_image.mpr ⟨x,(mem_squarefreeSupport J pr _).mpr
      ⟨sf,fun p h => (mem_sdiff.mp (sub h)).1⟩,rfl⟩,?_⟩
    change m.Coprime x
    exact (Nat.disjoint_primeFactors hm sf.ne_zero).mp (Finset.disjoint_left.mpr
      (fun p hp hx => (mem_sdiff.mp (sub hx)).2 hp))
  · rintro ⟨ev,cop⟩
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ev
    change m.Coprime x at cop
    obtain ⟨sf,sub⟩ := (mem_squarefreeSupport _ pr _).mp hx
    exact mem_image.mpr ⟨x,(mem_squarefreeSupport _ pr' _).mpr
      ⟨sf,fun p h => mem_sdiff.mpr ⟨sub h,fun hp => Finset.disjoint_left.mp cop.disjoint_primeFactors hp h⟩⟩,rfl⟩

/-- On enumerated coefficients, excluding the prime factors of the other
field value gives exactly the executable smooth predicate and coprimality
of the full value, provided the prescribed prefactor is coprime to it. -/
theorem PrescribedRows.box_smooth_coprime_iff {n ell a u v m : ℕ} (R : PrescribedRows n ell)
    (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (cap : a≤Fixed.A (n.log2+1))
    (grid : onGrid (Fixed.d (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.invWidth (n.log2+1)) a)
    (box : let b := n.log2+1; u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b)
    (side : Bool) (ok : R.compatible side u v) (nonzero : m≠0) (forced : m.Coprime (R.prefactor a side)) :
    let inp := TryPair.fixedInput n ell (construct n ell u v u v)
    let z := Marking.value (inp.coeffs side) a
    supportedValue (sieveBand n ell (R.prefactor a side)\m.primeFactors) (R.intercept a side u v) ↔
      Marking.SquarefreeSmooth inp.base z ∧ m.Coprime z := by
  intro inp z
  let pre := R.prefactor a side
  let J := sieveBand n ell pre
  have pr (p : ℕ) (h : p∈J) := (mem_primeBand.mp (mem_filter.mp h).1).1
  have sign := signed_box_value hn big target cap grid box side
  change markSign n a side*affineValue n ell a side ((u:ℤ)+a*v)=(z:ℤ) at sign
  have div := dvd_mul_of_dvd_right (R.pre_dvd target a side u v ok) (markSign n a side)
  rw [sign] at div
  have ds : pre∣z := Int.natCast_dvd_natCast.mp div
  have quotient : (R.intercept a side u v).natAbs = z/pre := by
    unfold PrescribedRows.intercept
    rw [sign,←Int.natCast_ediv,Int.natAbs_natCast]
  have smooth : supportedValue J (R.intercept a side u v) ↔ Marking.SquarefreeSmooth inp.base z :=
    R.box_smooth_iff hn big comp target absent cap grid box side ok
  rw [supportedValue_exclude_primeFactors J pr _ nonzero,quotient,smooth]
  exact and_congr_right (fun _ => ⟨fun h => Nat.div_mul_cancel ds ▸ Nat.coprime_mul_iff_right.mpr ⟨h,forced⟩,
    fun h => h.of_dvd_right (Nat.div_dvd_of_dvd ds)⟩)

end Cogentic.Construction

#print axioms Cogentic.Construction.PrescribedRows.smooth_probability_avoid
#print axioms Cogentic.Construction.PrescribedRows.box_smooth_coprime_iff
