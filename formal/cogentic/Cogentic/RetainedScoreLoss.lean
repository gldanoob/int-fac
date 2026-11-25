import Cogentic.TwoFieldRetentionLoss
import Cogentic.SimpleMark
import Cogentic.RestrictedPairUpper
import Cogentic.NearVarianceComplete
import Cogentic.FarNominalPair
import Cogentic.AdmissionMoments

namespace Cogentic.Construction
open Finset Real Cogentic.Window
open scoped Classical
noncomputable section

private theorem probability_eq {n ell : ℕ} (R : PrescribedRows n ell) (side : Bool)
    (E F : ℤ×ℤ→Prop) [a : DecidablePred E] [b : DecidablePred F] (h : E=F) :
    prescribedProbability R side E = prescribedProbability R side F := by
  subst F
  cases Subsingleton.elim a b
  rfl

private def strideClean {n ell : ℕ} (R : PrescribedRows n ell) (side : Bool) (a : ℕ) (k : ℤ×ℤ) : Prop :=
  supportedValue (sieveBand n ell (R.prefactor a side) \ R.miss a) (R.intercept a side k.1 k.2)

private theorem stride_sub {n ell a : ℕ} (R : PrescribedRows n ell) (side : Bool) (k : ℤ×ℤ)
    (yes : strideClean R side a k) : smoothMarkEvent R side a k := by
  obtain ⟨x,hx,eq⟩ := mem_image.mp yes
  obtain ⟨ps,hp,eqp⟩ := mem_image.mp hx
  exact mem_image.mpr ⟨x,mem_image.mpr ⟨ps,mem_powerset.mpr ((mem_powerset.mp hp).trans sdiff_subset),eqp⟩,eq⟩

private theorem stride_miss_loss (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a : ℕ} (R : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → ∀ side : Bool,
    let E := smoothMarkEvent R side a
    prescribedProbability R side (fun k => E k ∧ ¬strideClean R side a k) ≤
      (72*(Fixed.B b:ℝ)^(-199/400:ℝ)+360*exp (-(Fixed.U b:ℝ)))*prescribedProbability R side E := by
  obtain ⟨b₁,avoid⟩ := PrescribedRows.smooth_probability_avoid_sharp line 1
  refine ⟨max b₁ 2,?_⟩
  intro n ell a R b large hn comp target absent am side E
  obtain ⟨one,two⟩ := max_le_iff.mp large
  have card := (card_le_card (show R.miss a⊆R.primes from sdiff_subset)).trans R.limit
  have loss := (avoid R one hn comp target absent am side (R.miss a) (by rw [pow_one];omega)).2.2
  rw [R.deleted_probability target side E (strideClean R side a) (stride_sub R side)]
  let J := sieveBand n ell (R.prefactor a side)
  let old (S : Finset ℕ) := prescribedProbability R side (fun x=>supportedValue S (R.intercept a side x.1 x.2))
  change old J-old (J \ R.miss a) ≤ (36*((R.miss a).card:ℝ)*(Fixed.B b:ℝ)^(-199/400:ℝ)+360*exp (-(Fixed.U b:ℝ)))*old J at loss
  have h1 : old J=prescribedProbability R side E := probability_eq R side _ _ rfl
  have h2 : old (J \ R.miss a)=prescribedProbability R side (strideClean R side a) := probability_eq R side _ _ rfl
  rw [h1,h2] at loss
  apply loss.trans
  have nn := (R.probability_unit target side E).1
  have pw : 0≤(Fixed.B b:ℝ)^(-199/400:ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  apply mul_le_mul_of_nonneg_right _ nn
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_right _ pw
  have cast : ((R.miss a).card:ℝ)≤2 := by exact_mod_cast card
  linarith only [cast]

private theorem boxed_regular_from_stride {n ell a : ℕ} (R : PrescribedRows n ell)
    (hn : 2≤n) (big : 130000≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (mark : a∈(construct n ell 0 0 0 0).marks) (s : Bool) (x : R.CoeffPoint s) (box : inCoefficientBox n x.val)
    (cut : strideClean R s a x.val) (simple : ¬boxedOrdinarySingular R s a x.val) :
    let inp := TryPair.fixedInput n ell (construct n ell x.val.1.toNat x.val.2.toNat x.val.1.toNat x.val.2.toNat)
    let value := Marking.value (inp.coeffs s) a
    Marking.SquarefreeSmooth inp.base value ∧ value.Coprime (Marking.horner (a:ℤ) (inp.coeffs s)).2.natAbs := by
  intro inp value
  let u := x.val.1.toNat; let v := x.val.2.toNat; let M := prodPrimes (R.miss a)
  have uu : (u:ℤ)=x.val.1 := Int.toNat_of_nonneg box.1.le
  have vv : (v:ℤ)=x.val.2 := Int.toNat_of_nonneg box.2.2.1.le
  have ok : R.compatible s u v := by rw [uu,vv]; exact x.property
  have bounds : u≤2*(n.log2+1)^2*Fixed.U (n.log2+1)*Fixed.A (n.log2+1) ∧ v≤2*(n.log2+1)^2*Fixed.U (n.log2+1) :=
    ⟨by exact_mod_cast uu.trans_le box.2.1,by exact_mod_cast vv.trans_le box.2.2.2⟩
  have nz := (R.subprod_bounds (s:=R.miss a) sdiff_subset).1.ne'
  have factors : M.primeFactors=R.miss a := Nat.primeFactors_prod (fun _ h=>R.prime (mem_sdiff.mp h).1)
  have cop : M.Coprime (R.prefactor a s) := by
    rw [←Nat.disjoint_primeFactors nz (R.pre_bounds target a s).1.ne',factors,R.prefactor_primeFactors target]
    have dis : Disjoint (R.miss a) (R.hit a) := disjoint_left.mpr (fun _ h hp=>(mem_sdiff.mp h).2 hp)
    have out : ell∉R.miss a := fun h=>R.excluded (mem_sdiff.mp h).1
    split <;> simp [dis,out]
  obtain ⟨_,cap,grid,_⟩ := (constructed_marks_iff ..).mp mark
  have large : 10004≤Fixed.d (n.log2+1) := (by decide : 10004≤130000).trans big
  have h := R.box_smooth_coprime_iff hn large comp target absent cap grid bounds s ok (m:=M) nz cop
  rw [factors,uu,vv] at h
  obtain ⟨smooth,stride⟩ := h.mp cut
  refine ⟨smooth,derivative_coprime_of_ordinary ((by decide : 3≤10004).trans large) target u v u v a s M smooth stride.symm ?_⟩
  intro p hp diff free der
  exact simple ⟨box,p,hp,diff,free,der⟩

/-- Both boxed values are smooth, but the enumerated tuple does not return
the mark in the relation matrix emitted by stage one. -/
def rejectedSmoothMark {n ell : ℕ} (R T : PrescribedRows n ell) (a : ℕ) (x y : ℤ×ℤ) : Prop :=
  smoothMarkEvent R false a x ∧ smoothMarkEvent T true a y ∧ inCoefficientBox n x ∧ inCoefficientBox n y ∧
    ¬∃ rel, Marking.stageOne (TryPair.fixedInput n ell
      (construct n ell x.1.toNat x.2.toNat y.1.toNat y.2.toNat))=some rel ∧ a∈rel.marks

private theorem rejection_cover {n ell a : ℕ} (R T : PrescribedRows n ell)
    (hn : 2≤n) (big : 130000≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (mark : a∈(construct n ell 0 0 0 0).marks)
    (x : R.CoeffPoint false) (y : T.CoeffPoint true) (bad : rejectedSmoothMark R T a x.val y.val) :
    boxedSharedOrSingular R T a x.val y.val ∨
    (smoothMarkEvent R false a x.val ∧ smoothMarkEvent T true a y.val ∧
      (¬strideClean R false a x.val ∨ ¬strideClean T true a y.val)) := by
  classical
  obtain ⟨ax,ay,bx,byBox,no⟩ := bad
  by_cases h : boxedSharedOrSingular R T a x.val y.val
  · exact Or.inl h
  right
  refine ⟨ax,ay,?_⟩
  by_contra! good
  have shared : (boxedFieldValue n ell a false x.val).Coprime (boxedFieldValue n ell a true y.val) :=
    by_contra (fun z => h ⟨ax,ay,bx,byBox,Or.inl z⟩)
  have l := boxed_regular_from_stride R hn big comp target absent mark false x bx good.1
    (fun z=>h ⟨ax,ay,bx,byBox,Or.inr (Or.inl z)⟩)
  have r := boxed_regular_from_stride T hn big comp target absent mark true y byBox good.2
    (fun z=>h ⟨ax,ay,bx,byBox,Or.inr (Or.inr z)⟩)
  let u := x.val.1.toNat; let v := x.val.2.toNat; let w := y.val.1.toNat; let z := y.val.2.toNat
  let b := n.log2+1
  have uu : (u:ℤ)=x.val.1 := Int.toNat_of_nonneg bx.1.le
  have vv : (v:ℤ)=x.val.2 := Int.toNat_of_nonneg bx.2.2.1.le
  have ww : (w:ℤ)=y.val.1 := Int.toNat_of_nonneg byBox.1.le
  have zz : (z:ℤ)=y.val.2 := Int.toNat_of_nonneg byBox.2.2.1.le
  have box : u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b ∧ w≤2*b^2*Fixed.U b*Fixed.A b ∧ z≤2*b^2*Fixed.U b :=
    ⟨by exact_mod_cast uu.trans_le bx.2.1,by exact_mod_cast vv.trans_le bx.2.2.2,
      by exact_mod_cast ww.trans_le byBox.2.1,by exact_mod_cast zz.trans_le byBox.2.2.2⟩
  obtain ⟨rel,stage⟩ := stageOne_succeeds hn big comp target absent box
  have actual := (constructed_marks_iff n ell u v w z a).mpr ((constructed_marks_iff ..).mp mark)
  apply no
  refine ⟨rel,stage,retained_of_regular_smooth R T hn big comp target absent actual box
    (by rw [uu,vv];exact x.property) (by rw [ww,zz];exact y.property) stage l.1 r.1 shared ?_⟩
  intro side
  cases side
  · exact l.2
  · exact r.2

set_option maxHeartbeats 800000 in
/-- Complete relative loss from a smooth mark to executable retention
inside the coefficient box, uniformly over both prescribed root sets. -/
theorem rejected_smooth_mark_loss (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a : ℕ} (R T : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks →
    (R.prefactor a false).Coprime (T.prefactor a true) →
    twoFieldProbability R T (rejectedSmoothMark R T a) ≤
      (36*(7+(b:ℝ)/4)*(Fixed.B b:ℝ)^(-199/400:ℝ)+1440*exp (-(Fixed.U b:ℝ))+
        2*((b:ℝ)/2^(500*Fixed.h b)))*smoothMarkProbability R T a := by
  classical
  obtain ⟨b₁,base⟩ := twoField_shared_or_singular_loss line
  obtain ⟨b₂,miss⟩ := stride_miss_loss line
  obtain ⟨b₃,degr⟩ := Fixed.degree_grows 130000
  refine ⟨max b₁ (max b₂ b₃),?_⟩
  intro n ell a R T b huge hn comp target absent mark forced
  obtain ⟨one,r⟩ := max_le_iff.mp huge
  obtain ⟨two,three⟩ := max_le_iff.mp r
  let A := smoothMarkEvent R false a; let B := smoothMarkEvent T true a
  let L := fun x=> A x ∧ ¬strideClean R false a x
  let D := fun y=> B y ∧ ¬strideClean T true a y
  let U (x y : ℤ×ℤ) := A x ∧ B y ∧ (¬strideClean R false a x ∨ ¬strideClean T true a y)
  let l := prescribedProbability R false A; let r := prescribedProbability T true B
  let power := (Fixed.B b:ℝ)^(-199/400:ℝ)
  let e := exp (-(Fixed.U b:ℝ)); let Δ := 72*power+360*e
  have other := twoField_probability_cover R T target U (fun x y=>L x ∧ B y) (fun x y=>A x ∧ D y) (by
    rintro x y ⟨u,v,h|h⟩
    · exact Or.inl ⟨⟨u,h⟩,v⟩
    · exact Or.inr ⟨u,v,h⟩)
  rw [twoField_probability_rectangle R T target L B,twoField_probability_rectangle R T target A D] at other
  have left := miss R two hn comp target absent mark false
  have right := miss T two hn comp target absent mark true
  change prescribedProbability R false L≤Δ*l at left
  change prescribedProbability T true D≤Δ*r at right
  have lp := mul_le_mul_of_nonneg_right left (T.probability_unit target true B).1
  have rp := mul_le_mul_of_nonneg_left right (R.probability_unit target false A).1
  have cover := twoField_probability_cover R T target (rejectedSmoothMark R T a) (boxedSharedOrSingular R T a) U
    (rejection_cover R T hn (degr b three) comp target absent mark)
  have known := base R T one hn comp target absent mark forced
  let l' := prescribedProbability R false (fun k=>supportedValue (sieveBand n ell (R.prefactor a false)) (R.intercept a false k.1 k.2))
  let r' := prescribedProbability T true (fun k=>supportedValue (sieveBand n ell (T.prefactor a true)) (T.intercept a true k.1 k.2))
  have hl : l'=l := probability_eq R false _ _ rfl
  have hr : r'=r := probability_eq T true _ _ rfl
  change twoFieldProbability R T (boxedSharedOrSingular R T a) ≤
    (36*(3+(b:ℝ)/4)*power+720*e+2*((b:ℝ)/2^(500*Fixed.h b)))*(l'*r') at known
  rw [hl,hr] at known
  change twoFieldProbability R T U ≤ prescribedProbability R false L*r+l*prescribedProbability T true D at other
  change prescribedProbability R false L*r≤Δ*l*r at lp
  change l*prescribedProbability T true D≤l*(Δ*r) at rp
  change _≤(36*(7+(b:ℝ)/4)*power+1440*e+2*((b:ℝ)/2^(500*Fixed.h b)))*(l*r)
  dsimp only [Δ] at lp rp
  linarith only [cover,other,known,lp,rp]

private theorem retention_rate_saving (v : ℝ) (hv : 1≤v) :
    ∃ b₀ : ℕ, ∀ b≥b₀, 36*(7+(b:ℝ)/4)*(Fixed.B b:ℝ)^(-199/400:ℝ)+1440*exp (-(Fixed.U b:ℝ))+
      2*((b:ℝ)/2^(500*Fixed.h b)) ≤ exp (-v*(Fixed.z b:ℝ)^2) := by
  obtain ⟨b₁,save⟩ := nominal_deletion_saving 0 v hv
  refine ⟨max 2000 b₁,?_⟩
  intro b huge
  obtain ⟨large,one⟩ := max_le_iff.mp huge
  let B : ℝ := Fixed.B b
  let X : ℝ := 2^(500*Fixed.h b)
  have bx : X^2=B := by
    simp only [X,B,Fixed.B,Fixed.beta,Nat.cast_pow,Nat.cast_ofNat,←pow_mul]
    congr 1; ring
  have xo : 1≤X := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  have bo : 1≤B := by rw [←bx]; exact one_le_pow₀ xo
  have bp := zero_lt_one.trans_le bo
  have bn : 0<b := by omega
  have deg := Fixed.degree_pos bn
  obtain ⟨_,_,_,bb,_,uu,_⟩ := dyadic_data bn
  have ub : Fixed.B b≤Fixed.U b := by
    rw [bb,uu]; apply Nat.pow_le_pow_right (Nat.pow_pos (by decide)); omega
  have bu : B≤(Fixed.U b:ℝ) := by dsimp only [B];exact_mod_cast ub
  have uf : exp (-(Fixed.U b:ℝ))≤B^(-199/400:ℝ) := by
    rw [rpow_def_of_pos bp,exp_le_exp]
    linarith only [log_le_self bp.le,log_nonneg bo,bu]
  have small : X⁻¹≤B^(-199/400:ℝ) := by
    rw [←bx,←rpow_natCast_mul (zero_le_one.trans xo)]
    refine (rpow_neg_one X).symm.le.trans (rpow_le_rpow_of_exponent_le xo (by norm_num))
  have lim : 17*(b:ℝ)*B^(-199/400:ℝ)≤exp (-v*(Fixed.z b:ℝ)^2) := by
    simpa only [zero_add,pow_one,B] using save b one
  have br : 2000≤(b:ℝ) := by exact_mod_cast large
  have lin : 36*(7+(b:ℝ)/4)+1440+2*b≤17*b := by linarith only [br]
  change 36*(7+(b:ℝ)/4)*B^(-199/400:ℝ)+1440*exp (-(Fixed.U b:ℝ))+2*((b:ℝ)/X) ≤ _
  rw [div_eq_mul_inv (b:ℝ) X]
  exact (show _≤17*(b:ℝ)*B^(-199/400:ℝ) by
    nlinarith only [mul_le_mul_of_nonneg_left uf (by norm_num : (0:ℝ)≤1440),
      mul_le_mul_of_nonneg_left small (by positivity : (0:ℝ)≤2*b),
      mul_le_mul_of_nonneg_right lin (rpow_nonneg bp.le (-199/400:ℝ))]).trans lim

private theorem coupled_event_sum {n ell : ℕ} (R T : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (G : (ℤ×ℤ)→(ℤ×ℤ)→Prop) :
    HasSum (fun k : R.CoeffPoint false × T.CoeffPoint true => if G k.1.val k.2.val then twoFieldWeight R T k else 0)
      (twoFieldProbability R T G) := by
  have wn (k : R.CoeffPoint false × T.CoeffPoint true) : 0≤twoFieldWeight R T k :=
    mul_nonneg (R.pointMass_nonneg ..) (T.pointMass_nonneg ..)
  apply Summable.hasSum
  apply Summable.of_nonneg_of_le _ _ (twoField_total R T target).summable
  · intro k;split <;> first | exact wn _ | rfl
  · intro k;split <;> first | exact wn _ | rfl

/-- The expected absolute score removed by the executable first stage on
boxed smooth marks is small relative to the sum of the mark weights. Each
mark is normalized by its own actual two-field marginal. -/
theorem rejected_score_loss (line : DirichletLZerosOnLine) (v : ℝ) (hv : 1≤v) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ} (R T : PrescribedRows n ell), let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    ∀ (X : Finset ℕ) (w : ℕ→ℝ), (∀ a∈X,a∈(construct n ell 0 0 0 0).marks) →
    (∀ a∈X,(R.prefactor a false).Coprime (T.prefactor a true)) →
    let score := fun x y => ∑ a∈X, if rejectedSmoothMark R T a x y then |w a|/smoothMarkProbability R T a else 0
    ∃ μ : ℝ, HasSum (fun k : R.CoeffPoint false × T.CoeffPoint true => twoFieldWeight R T k*score k.1.val k.2.val) μ ∧
      μ ≤ exp (-v*(Fixed.z b:ℝ)^2)*(∑ a∈X,|w a|) := by
  obtain ⟨b₁,bound⟩ := rejected_smooth_mark_loss line
  obtain ⟨b₂,decay⟩ := retention_rate_saving v hv
  refine ⟨max b₁ b₂,?_⟩
  intro n ell R T b large hn comp target absent X w marks cop score
  let p := smoothMarkProbability R T
  let m := fun a => twoFieldProbability R T (rejectedSmoothMark R T a)
  let e := exp (-v*(Fixed.z b:ℝ)^2)
  have mass (a : ℕ) := coupled_event_sum R T target (rejectedSmoothMark R T a)
  have total := hasSum_sum (s:=X) (fun a _ => (mass a).mul_right (|w a|/p a))
  refine ⟨_,total.congr_fun (fun k=>?_ ),?_⟩
  · dsimp only [score]; rw [mul_sum]
    apply sum_congr rfl
    intro a _
    by_cases h : rejectedSmoothMark R T a k.1.val k.2.val <;> simp [h,p]
  · rw [mul_sum]
    apply sum_le_sum
    intro a ha
    have np : 0≤p a := mul_nonneg (R.probability_unit target false _).1 (T.probability_unit target true _).1
    have est := (bound R T (max_le_iff.mp large).1 hn comp target absent (marks a ha) (cop a ha)).trans
      (mul_le_mul_of_nonneg_right (decay b (max_le_iff.mp large).2) np)
    change m a*(|w a|/p a)≤e*|w a|
    by_cases z : p a=0
    · rw [z,div_zero,mul_zero];exact mul_nonneg (exp_pos _).le (abs_nonneg _)
    · exact (mul_le_mul_of_nonneg_right est (div_nonneg (abs_nonneg _) np)).trans_eq (by
        change e*p a*(|w a|/p a)=e*|w a|
        field_simp)


/-- Restricting one unrestricted coefficient draw by both row prescriptions
transfers every coupled event with exactly the same admission factor. -/
theorem twoField_admission_probability {n ell : ℕ} (R T : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) :
    let S := PrescribedRows.unrestricted n ell
    let Q : ℝ := prodPrimes R.primes*prodPrimes T.primes
    let η := 72*exp (-(Fixed.U (n.log2+1):ℝ))
    ∃ A : ℝ, 0<A ∧ |Q*A-1|≤2*η+η^2 ∧ ∀ G : (ℤ×ℤ)→(ℤ×ℤ)→Prop,
      twoFieldProbability S S (fun x y=>R.compatible false x.1 x.2 ∧ T.compatible true y.1 y.2 ∧ G x y)=
        A*twoFieldProbability R T G := by
  intro S Q η
  let Z := ∑' k : ℤ×ℤ,coefficientWeight n k
  let z := fun (L : PrescribedRows n ell) (s : Bool) => ∑' k : L.CoeffPoint s,coefficientWeight n k.val
  have all (s : Bool) (k : ℤ×ℤ) : S.compatible s k.1 k.2 := by
    simp [S,PrescribedRows.unrestricted,PrescribedRows.compatible]
  let iso (s : Bool) : S.CoeffPoint s ≃ ℤ×ℤ :=
    ⟨Subtype.val,fun k=>⟨k,all s k⟩,fun _=>rfl,fun _=>rfl⟩
  have full (s : Bool) : z S s=Z := (iso s).tsum_eq (coefficientWeight n)
  let u := z R false/Z; let v := z T true/Z
  have ⟨zp,lp,le⟩ := R.admission_probability target false
  have ⟨_,rp,re⟩ := T.admission_probability target true
  change 0<Z at zp;change 0<z R false at lp;change 0<z T true at rp
  change |(prodPrimes R.primes:ℝ)*u-1|≤η at le
  change |(prodPrimes T.primes:ℝ)*v-1|≤η at re
  refine ⟨u*v,mul_pos (div_pos lp zp) (div_pos rp zp),?_,?_⟩
  · let x := (prodPrimes R.primes:ℝ)*u-1
    let y := (prodPrimes T.primes:ℝ)*v-1
    have xy := mul_le_mul le re (abs_nonneg _) ((abs_nonneg _).trans le)
    have eq : Q*(u*v)-1=(x+y)+x*y := by dsimp only [Q,x,y];ring
    rw [eq]
    calc |(x+y)+x*y| ≤ (|x|+|y|)+|x*y| := (abs_add_le ..).trans (add_le_add (abs_add_le ..) le_rfl)
         _ ≤ 2*η+η^2 := by
           rw [abs_mul]
           change |x|≤η at le; change |y|≤η at re
           change |x| * |y|≤η*η at xy
           linarith only [le,re,xy]
  intro G
  let C := R.CoeffPoint false × T.CoeffPoint true
  let D := S.CoeffPoint false × S.CoeffPoint true
  let f (k : C) : D := (⟨k.1.val,all false k.1.val⟩,⟨k.2.val,all true k.2.val⟩)
  let V (k : D) := @ite ℝ (R.compatible false k.1.val.1 k.1.val.2 ∧ T.compatible true k.2.val.1 k.2.val.2 ∧ G k.1.val k.2.val)
    (Classical.propDecidable _) (twoFieldWeight S S k) 0
  have inj : Function.Injective f := by
    intro a b e
    exact Prod.ext (Subtype.ext (congrArg (fun k : D=> k.1.val) e)) (Subtype.ext (congrArg (fun k : D=>k.2.val) e))
  have sup : Function.support V⊆Set.range f := by
    intro k hk
    change V k≠0 at hk
    dsimp only [V] at hk
    split at hk
    next yes => exact ⟨(⟨k.1.val,yes.1⟩,⟨k.2.val,yes.2.1⟩),rfl⟩
    next => exact (hk rfl).elim
  change (∑' k : D,V k)=(u*v)*(∑' k : C,if G k.1.val k.2.val then twoFieldWeight R T k else 0)
  rw [←inj.tsum_eq sup,←tsum_mul_left]
  apply tsum_congr
  intro k
  dsimp only [V,f,Function.comp_apply]
  simp only [k.1.property,k.2.property,true_and]
  split
  · change coefficientWeight n k.1.val/(z S false)*(coefficientWeight n k.2.val/(z S true))=
      (u*v)*(coefficientWeight n k.1.val/(z R false)*(coefficientWeight n k.2.val/(z T true)))
    rw [full,full]; dsimp only [u,v];field_simp
  · simp only [mul_zero]


/-- On one unrestricted coefficient draw, different score terms may have
different prescribed root sets. Each rejected term retains the inverse
row-admission modulus when its expected loss is summed. -/
theorem admitted_rejection_budget {ι : Type*} (line : DirichletLZerosOnLine) (v : ℝ) (hv : 1≤v) :
    ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    ∀ (J : Finset ι) (R T : ι→PrescribedRows n ell) (a : ι→ℕ) (w : ι→ℝ),
    (∀ i∈J,a i∈(construct n ell 0 0 0 0).marks) →
    (∀ i∈J,((R i).prefactor (a i) false).Coprime ((T i).prefactor (a i) true)) →
    let S := PrescribedRows.unrestricted n ell
    let Q := fun i => (prodPrimes (R i).primes:ℝ)*prodPrimes (T i).primes
    let p := fun i => smoothMarkProbability (R i) (T i) (a i)
    let bad := fun i (x y : ℤ×ℤ) => (R i).compatible false x.1 x.2 ∧ (T i).compatible true y.1 y.2 ∧
      rejectedSmoothMark (R i) (T i) (a i) x y
    let score := fun x y => ∑ i∈J,if bad i x y then |w i|/p i else 0
    ∃ μ : ℝ, HasSum (fun k : S.CoeffPoint false × S.CoeffPoint true =>
      twoFieldWeight S S k*score k.1.val k.2.val) μ ∧
      μ ≤ 4*exp (-v*(Fixed.z b:ℝ)^2)*(∑ i∈J,|w i|/Q i) := by
  obtain ⟨b₁,bound⟩ := rejected_smooth_mark_loss line
  obtain ⟨b₂,decay⟩ := retention_rate_saving v hv
  refine ⟨max b₁ b₂,?_⟩
  intro n ell b large hn comp target absent J R T a w marks cop S Q p bad score
  let e := exp (-v*(Fixed.z b:ℝ)^2)
  let m i := twoFieldProbability S S (bad i)
  have mass (i : ι) := coupled_event_sum S S target (bad i)
  have total := hasSum_sum (s:=J) (fun i _ => (mass i).mul_right (|w i|/p i))
  refine ⟨_,total.congr_fun (fun k => ?_),?_⟩
  · dsimp only [score];rw [mul_sum]
    apply sum_congr rfl
    intro i _
    by_cases yes : bad i k.1.val k.2.val <;> simp [yes]
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  obtain ⟨A,apos,close,events⟩ := twoField_admission_probability (R i) (T i) target
  let η := 72*exp (-(Fixed.U b:ℝ))
  have degree := Fixed.degree_pos (b:=b) (Nat.succ_pos _)
  have vpos : 0<Fixed.v b := Nat.mul_pos degree (Nat.mul_pos degree (Nat.succ_pos _))
  have uc : 72≤(Fixed.U b:ℝ) := by
    exact_mod_cast (by decide : 72≤2^7).trans (Nat.pow_le_pow_right (by decide : 0<2) (by omega))
  have en : 0≤η := by dsimp only [η];positivity
  have e1 : η≤1 := by
    dsimp only [η];rw [exp_neg,←div_eq_mul_inv,div_le_one (exp_pos _)]
    linarith only [add_one_le_exp (Fixed.U b),uc]
  change |Q i*A-1|≤2*η+η^2 at close
  have qa : Q i*A≤4 := by nlinarith only [(abs_le.mp close).2,mul_nonneg (sub_nonneg.mpr e1) en,e1]
  have qp : 0<Q i := by
    have l := ((R i).subprod_bounds (s:=(R i).primes) Subset.rfl).1
    have r := ((T i).subprod_bounds (s:=(T i).primes) Subset.rfl).1
    dsimp only [Q];positivity
  have nonneg : 0≤p i := mul_nonneg ((R i).probability_unit target false _).1 ((T i).probability_unit target true _).1
  have est := (bound (R i) (T i) (max_le_iff.mp large).1 hn comp target absent (marks i hi) (cop i hi)).trans
    (mul_le_mul_of_nonneg_right (decay b (max_le_iff.mp large).2) nonneg)
  have equality := events (rejectedSmoothMark (R i) (T i) (a i))
  change m i=A*twoFieldProbability (R i) (T i) (rejectedSmoothMark (R i) (T i) (a i)) at equality
  have ub : m i≤A*(e*p i) := equality.le.trans (mul_le_mul_of_nonneg_left est apos.le)
  change m i*(|w i|/p i)≤4*e*(|w i|/Q i)
  by_cases zero : p i=0
  · rw [zero,div_zero,mul_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (exp_pos _).le) (div_nonneg (abs_nonneg _) qp.le)
  apply (mul_le_mul_of_nonneg_right ub (div_nonneg (abs_nonneg _) nonneg)).trans
  rw [show A*(e*p i)*(|w i|/p i)=A*(e*|w i|) by field_simp]
  have cost := mul_le_mul_of_nonneg_right qa (mul_nonneg (exp_pos (-v*(Fixed.z b:ℝ)^2)).le (abs_nonneg (w i)))
  rw [mul_div_assoc',le_div_iff₀ qp]
  change Q i*A*(e*|w i|)≤4*(e*|w i|) at cost
  linarith only [cost]

end
end Cogentic.Construction

#print axioms Cogentic.Construction.rejected_smooth_mark_loss

#print axioms Cogentic.Construction.rejected_score_loss

#print axioms Cogentic.Construction.twoField_admission_probability

#print axioms Cogentic.Construction.admitted_rejection_budget
