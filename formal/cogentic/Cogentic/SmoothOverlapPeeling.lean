import Cogentic.RetainedOverlapEnvelope
import Cogentic.RejectedColumnPeeling

namespace Cogentic.Construction
open Finset Real Window
noncomputable section
open scoped Classical

/-- Prescribing ordinary rows never depresses the two-field smooth marginal
by more than a constant factor, including at ordinary and target hits. -/
theorem prescribed_marginal_lower (line : DirichletLZerosOnLine) :
    ∃ b₀ : ℕ, ∀ {n ell a : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    a∈(construct n ell 0 0 0 0).marks → ∀ R T : PrescribedRows n ell,
    let O := PrescribedRows.unrestricted n ell
    0<smoothMarkProbability O O a ∧ smoothMarkProbability O O a≤8*smoothMarkProbability R T a := by
  obtain ⟨C,_,b₁,ratio⟩ := hit_smooth_marginal_ratio line 1 le_rfl
  obtain ⟨b₂,accuracy⟩ := fixed_class_accuracy C
  obtain ⟨_,_,b₃,central⟩ := fixed_central_insertions 0
  obtain ⟨b₄,degrees⟩ := Fixed.degree_grows 10004
  refine ⟨max (max b₁ b₂) (max b₃ b₄),?_⟩
  intro n ell a b large hn comp target absent mark R T O
  obtain ⟨one,two⟩ := max_le_iff.mp large
  obtain ⟨br,ba⟩ := max_le_iff.mp one
  obtain ⟨bc,bd⟩ := max_le_iff.mp two
  have deg := degrees b bd
  obtain ⟨α,β,ha,hb,ma,mb,pos,rt⟩ := ratio br hn comp target absent mark
  obtain ⟨_,cap,grid,_⟩ := (constructed_marks_iff ..).mp mark
  let H := log (Fixed.B b:ℝ)
  have B1 : 1<(Fixed.B b:ℝ) := by exact_mod_cast (Nat.one_lt_pow
    (Nat.mul_ne_zero (by decide) (Nat.mul_ne_zero (Fixed.degree_pos (Nat.succ_pos n.log2)).ne' (Nat.succ_ne_zero _))) (by decide) : 1<Fixed.B b)
  have hpos : 0<H := log_pos B1
  have natJ : ((Ioc ⌊sqrt (Fixed.B b:ℝ)⌋₊ ⌊(Fixed.B b:ℝ)⌋₊).filter Nat.Prime)=primeBand b := by simp [primeBand]
  have insert_bound (U : PrescribedRows n ell) (side : Bool) (x : ℝ) (xs : x∈Set.Icc (199/200:ℝ) 1)
      (mu : saddleMean (primeBand b) x=log ((exactMean n ell a side:ℝ)/targetPart n ell a side)) :
      (1:ℝ)/2≤fullBandInsertion b (U.hitProduct a) x := by
    let D := (targetPart n ell a side:ℝ)
    let u := saddleMean (primeBand b) x/H
    have ep := (mem_dyadicTargets.mp target).1.pos
    have ec := (mem_dyadicTargets.mp target).2.2
    have src : 1≤targetPart n ell a side ∧ targetPart n ell a side≤Fixed.B b := by
      unfold targetPart;split <;> constructor <;> first | assumption | omega | exact Nat.pow_pos (by decide)
    have Ac : 1≤(Fixed.A b:ℝ) := by exact_mod_cast (Nat.pow_pos (by decide) : 0<Fixed.A b)
    have upper := pow_le_pow_right₀ B1.le (show 1≤40 by decide)
    rw [pow_one] at upper
    have win := one_point_window hn deg target cap grid side D
      ⟨by dsimp only [D];exact_mod_cast src.1,(by dsimp only [D];exact_mod_cast src.2 : D≤(Fixed.B b:ℝ)).trans
        (upper.trans (le_mul_of_one_le_left (by positivity) Ac))⟩
    have lo : 90*(Fixed.d b:ℝ)≤u := by dsimp only [u,H];rw [mu];exact win.2.2.1
    have hi : u≤110*(Fixed.d b:ℝ) := by dsimp only [u,H];rw [mu];exact win.2.2.2.1
    have up : (72:ℝ)≤u := by
      have d : (10004:ℝ)≤Fixed.d b := by exact_mod_cast deg
      linarith only [lo,d]
    let Q := U.hitProduct a
    obtain ⟨qp,qc⟩ := U.subprod_bounds (s:=U.hit a) (filter_subset ..)
    have qr : (1:ℝ)≤Q := by exact_mod_cast (show 1≤Q from qp)
    have shift : |log (Q:ℝ)|≤2*H := by
      rw [abs_of_nonneg (log_nonneg qr)]
      have est := log_le_log (zero_lt_one.trans_le qr) (by exact_mod_cast qc : (Q:ℝ)≤(Fixed.B b:ℝ)^2)
      simpa only [H,log_pow,Nat.cast_ofNat] using est
    have raw := central b bc u x 0 0 (fun _=>∅)
    dsimp only at raw
    rw [natJ] at raw
    have zero : |(0:ℝ)|≤H := by rw [abs_zero];exact hpos.le
    have eq : saddleMean (primeBand b) x=H*u := by dsimp only [u];field_simp
    have est := ((raw lo hi xs.1 eq zero zero (by simp)).2.1 (log Q) shift).1
    let M := shiftedMass (primeBand b) (primeProbability x) (fun p=>log p) H
    change |omittedMass (primeBand b) ∅ (primeProbability x) (fun p=>log p) H (log Q)/
      omittedMass (primeBand b) ∅ (primeProbability x) (fun p=>log p) H 0-1|≤36/u at est
    have om (s : ℝ) : omittedMass (primeBand b) ∅ (primeProbability x) (fun p=>log p) H s=M s := by
      simp only [M,omittedMass,omittedCharacteristic,saddleCharacteristic,shiftedMass,notMem_empty,ite_false]
    rw [om,om] at est
    have radius : 36/u≤1/2 := (div_le_iff₀ (by linarith only [up] : 0<u)).mpr (by linarith)
    have ratioLo : (1:ℝ)/2≤M (log Q)/M 0 := by linarith only [(abs_le.mp est).1,radius]
    have power := one_le_rpow qr (sub_nonneg.mpr xs.2)
    change _≤(Q:ℝ)^(1-x)*(M (log Q)/M 0)
    exact ratioLo.trans (le_mul_of_one_le_left (by linarith only [ratioLo]) power)
  let J := fullBandInsertion b (R.hitProduct a) α*fullBandInsertion b (T.hitProduct a) β
  have il := insert_bound R false α ha ma
  have ir := insert_bound T true β hb mb
  have jl : (1:ℝ)/4≤J := by
    have h := mul_le_mul il ir (by norm_num) (by linarith only [il])
    norm_num at h;exact h
  obtain ⟨jp,err⟩ := rt R T
  have tiny := accuracy b ba
  simp only [neg_one_mul] at err
  have lower : (1:ℝ)/2 ≤ (smoothMarkProbability R T a/smoothMarkProbability O O a)/J := by
    have h := (abs_le.mp err).1
    change -(C*exp (-(Fixed.z b:ℝ)^2))≤(smoothMarkProbability R T a/smoothMarkProbability O O a)/J-1 at h
    linarith
  have pj : 0<J := jp
  have cmp := (le_div_iff₀ pj).mp lower
  have fixed : (1:ℝ)/8 ≤ smoothMarkProbability R T a/smoothMarkProbability O O a := by linarith only [cmp,jl]
  exact ⟨pos,by linarith only [(le_div_iff₀ pos).mp fixed]⟩

/-- On boxed compatible coefficients the prescribed and original smooth tests
recognize the same full polynomial value. -/
theorem boxed_prescribed_smooth_iff {n ell a : ℕ} (R : PrescribedRows n ell) (side : Bool)
    (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (mark : a∈(construct n ell 0 0 0 0).marks) (x : R.CoeffPoint side) (box : inCoefficientBox n x.val) :
    smoothMarkEvent R side a x.val ↔ smoothMarkEvent (PrescribedRows.unrestricted n ell) side a x.val := by
  let b := n.log2+1
  have uu := Int.toNat_of_nonneg box.1.le
  have vv := Int.toNat_of_nonneg box.2.2.1.le
  have bounds : x.val.1.toNat≤2*b^2*Fixed.U b*Fixed.A b ∧ x.val.2.toNat≤2*b^2*Fixed.U b :=
    ⟨by exact_mod_cast uu.trans_le box.2.1,by exact_mod_cast vv.trans_le box.2.2.2⟩
  have ok : R.compatible side x.val.1.toNat x.val.2.toNat := by rw [uu,vv];exact x.property
  obtain ⟨_,cap,grid,_⟩ := (constructed_marks_iff ..).mp mark
  let O := PrescribedRows.unrestricted n ell
  have free : O.compatible side x.val.1.toNat x.val.2.toNat := by simp [O,PrescribedRows.unrestricted,PrescribedRows.compatible]
  have rr := R.box_smooth_iff hn big comp target absent cap grid bounds side ok
  have oo := O.box_smooth_iff hn big comp target absent cap grid bounds side free
  rw [uu,vv] at rr oo
  exact rr.trans oo.symm

/-- Actual common-weight smooth pair mass is dominated, on every compatible
boxed draw, by the same-draw physical total and the prescribed centered CRT
error whose admitted second moment is estimated by admitted_distinct_prime_overlap. -/
theorem physical_pair_upper_for_peeling (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0<C ∧ ∃ b₀ : ℕ, ∀ {n ell : ℕ}, let b := n.log2+1
    b₀≤b → 2≤n → ¬n.Prime → ell∈dyadicTargets (Fixed.beta b) →
    presieve n b (Fixed.beta b) (Fixed.A b) (Fixed.rootBase n)=none →
    ∀ (cell : Option (Bool×Fin (Fixed.d b))) (R T : PrescribedRows n ell) (x : R.CoeffPoint false) (y : T.CoeffPoint true),
    inCoefficientBox n x.val → inCoefficientBox n y.val → ∀ (p q r s : ℕ) (f : ℕ→ℝ),
    let X := constructorCellMarks n ell cell
    (∀ a∈X,0≤f a) →
    let O := PrescribedRows.unrestricted n ell
    let F := fun a=>residueEntry p r a*residueEntry q s a
    let P := smoothMarkProbability O O
    let gram := twoFieldScore X (fun a=>f a*F a/P a) (smoothMarkEvent O false) (smoothMarkEvent O true) x.val y.val
    let total := twoFieldScore X (fun a=>f a/P a) (smoothMarkEvent O false) (smoothMarkEvent O true) x.val y.val
    let err := twoFieldScore X (overlapContrast R T p q r s f) (smoothMarkEvent R false) (smoothMarkEvent T true) x.val y.val
    let A := (1+C)*(3*(1760*(Fixed.d b:ℝ)+4)^4)^2
    ((p*q:ℕ):ℝ)*gram≤A*(err+8*total) := by
  obtain ⟨C,cp,b₁,upper⟩ := cell_common_envelope line
  obtain ⟨b₂,lower⟩ := prescribed_marginal_lower line
  obtain ⟨b₃,deg⟩ := Fixed.degree_grows 10004
  refine ⟨C,cp,max b₁ (max b₂ b₃),?_⟩
  intro n ell b large hn comp target absent cell R T x y bx by' p q r s f X fn O F P gram total err A
  obtain ⟨bu,m⟩ := max_le_iff.mp large
  obtain ⟨bl,bd⟩ := max_le_iff.mp m
  have Ap : 0≤A := by dsimp only [A];positivity
  dsimp only [gram,total,err,twoFieldScore]
  rw [mul_sum,mul_sum,←sum_add_distrib,mul_sum]
  apply sum_le_sum
  intro a ha
  have mark := (mem_filter.mp ha).2
  have ul := upper bu hn comp target absent cell a ha R T
  change 1/P a ≤ A/smoothMarkProbability R T a at ul
  obtain ⟨pp,rate⟩ := lower bl hn comp target absent mark R T
  have eq0 := boxed_prescribed_smooth_iff R false hn (deg b bd) comp target absent mark x bx
  have eq1 := boxed_prescribed_smooth_iff T true hn (deg b bd) comp target absent mark y by'
  have same : (smoothMarkEvent R false a x.val ∧ smoothMarkEvent T true a y.val) ↔
      (smoothMarkEvent O false a x.val ∧ smoothMarkEvent O true a y.val) := and_congr eq0 eq1
  rw [if_congr same rfl rfl]
  by_cases smooth : smoothMarkEvent O false a x.val ∧ smoothMarkEvent O true a y.val
  · simp only [if_pos smooth,mul_one]
    let Q := smoothMarkProbability R T a
    have low : 1/Q ≤ 8/P a := (div_le_div_iff₀ (by change 0<smoothMarkProbability R T a; linarith only [pp,rate]) pp).mpr
      (by dsimp only [Q,P,O];linarith only [rate])
    have sign : 0≤F a := by dsimp only [F,residueEntry];split <;> split <;> norm_num
    let I := ((p*q:ℕ):ℝ)*f a*F a
    have ip : 0≤I := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (fn a ha)) sign
    have s₁ := mul_le_mul_of_nonneg_left ul ip
    have s₂ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left low (fn a ha)) Ap
    change I*(1/P a)≤I*(A/Q) at s₁
    dsimp only [I] at s₁
    dsimp only [overlapContrast]
    change ((p*q:ℕ):ℝ)*(f a*F a/P a)≤A*((((p*q:ℕ):ℝ)*F a-1)*f a/Q+8*(f a/P a))
    linear_combination s₁ + s₂
  · simp [smooth]

/-- Transfer a lower energy on smooth columns to the actually retained marks
avoiding deleted ordinary rows. Protected coordinates, the intercept and log
rows may contribute to g; their squared score on the deleted columns is
charged explicitly. -/
theorem retained_projected_energy (s : Marking.Input) (X : Finset ℕ)
    (rel : Marking.Relations) (_stage : Marking.stageOne s=some rel) (G D : Finset Marking.Row)
    (w : ℕ→ℝ) (scale : Marking.Row→ℝ) (k : ℕ) (δ₀ δ₁ m₀ m₁ : ℝ)
    (wn : ∀ a∈X,0≤w a)
    (support : ∀ a∈X,(G.filter (fun i=>a%i.q=i.r)).card≤k) :
    let hitD := fun a : ℕ=>∃ j∈D,a%j.q=j.r
    let R := X.filter (fun a=>a∉rel.marks)
    let H := X.filter hitD
    let J := X.filter (fun a=>a∈rel.marks ∧ ¬hitD a)
    let z := fun i : Marking.Row=>fun a : ℕ=>if a%i.q=i.r then scale i else 0
    (∑ a∈R,w a) ≤ m₀ → (∑ a∈H,w a) ≤ m₁ →
    (∀ i∈G,(∑ a∈R,w a*(z i a)^2)≤δ₀ ∧ (∑ a∈H,w a*(z i a)^2)≤δ₁) →
    ∀ (v : Marking.Row→ℝ) (g : ℕ→ℝ) (U : ℝ), 0≤U → (∀ a∈X, (g a)^2≤U) →
    let score := fun a=>g a+∑ i∈G, z i a*v i
    let lossBound := 2*(m₀+m₁)*U+2*k*(δ₀+δ₁)*(∑ i∈G,(v i)^2)
    (∑ a∈X,w a*(score a)^2)≤ (∑ a∈J,w a*(score a)^2)+lossBound ∧
      (lossBound < ∑ a∈X,w a*(score a)^2 →
        ∃ a∈X, a∈rel.marks ∧ (∀ j∈D,a%j.q≠j.r) ∧ 0<w a ∧ score a≠0) := by
  classical
  intro hitD R H J z rtot htot diag v g U up gcap score lossBound
  let Y := X\J
  have ysub : Y⊆X := sdiff_subset
  have unionY : Y=R∪H := by
    ext a;by_cases hx : a∈X <;> by_cases keep : a∈rel.marks <;> by_cases h : hitD a <;> simp [Y,R,H,J,hx,keep,h]
  have union_le (f : ℕ→ℝ) (pos : ∀ a∈X,0≤f a) :
      (∑ a∈Y,f a)≤(∑ a∈R,f a)+(∑ a∈H,f a) := by
    rw [unionY]
    exact (le_add_of_nonneg_right (sum_nonneg (s:=R∩H) (fun a ha=>pos a (mem_filter.mp (mem_inter.mp ha).1).1))).trans_eq
      (sum_union_inter (s₁:=R) (s₂:=H) (f:=f))
  have lossDiag (i) (ig : i∈G) : (∑ a∈Y,w a*(z i a)^2)≤δ₀+δ₁ :=
    (union_le _ (fun a ha=>mul_nonneg (wn a ha) (sq_nonneg _))).trans (add_le_add (diag i ig).1 (diag i ig).2)
  let sup := fun a : Y=> (univ : Finset G).filter (fun i=>a.val%i.val.q=i.val.r)
  have sparse := sparse_discard_energy (fun a : Y=>w a.val) (fun a : Y=>fun i : G=> z i.val a.val) sup
    (fun i : G=>v i.val) k (δ₀+δ₁) (fun a=>wn _ (ysub a.property))
    (by
      intro a
      refine (card_le_card_of_injOn (fun i : G=>i.val) (t:=G.filter (fun i=>a.val%i.q=i.r)) ?_ Subtype.val_injective.injOn).trans
        (support _ (ysub a.property))
      intro i hi;exact mem_filter.mpr ⟨i.property,(mem_filter.mp hi).2⟩)
    (by intro a i no;dsimp only [z];exact if_neg (fun eq=>no (mem_filter.mpr ⟨mem_univ _,eq⟩)))
    (by intro i;rw [sum_coe_sort Y (fun a=>w a*(z i.val a)^2)];exact lossDiag i.val i.property)
  let F := fun a=>∑ i∈G,z i a*v i
  have row (a) : (∑ i : G,z i.val a*v i.val)=F a := sum_coe_sort G (fun i=>z i a*v i)
  simp only [row] at sparse
  rw [sum_coe_sort Y (fun a=>w a*(F a)^2),sum_coe_sort G (fun i=>(v i)^2)] at sparse
  have gbound : (∑ a∈Y,w a*(g a)^2)≤(m₀+m₁)*U := by
    calc _ ≤ ∑ a∈Y,w a*U := sum_le_sum (fun a ha=>mul_le_mul_of_nonneg_left (gcap a (ysub ha)) (wn a (ysub ha)))
         _ = (∑ a∈Y,w a)*U := (sum_mul ..).symm
         _ ≤ _ := mul_le_mul_of_nonneg_right ((union_le w wn).trans (add_le_add rtot htot)) up
  have lost : (∑ a∈Y,w a*(score a)^2)≤lossBound := by
    have sum := sum_le_sum (s:=Y) (fun a ha=>mul_le_mul_of_nonneg_left
      (show (score a)^2≤2*(g a)^2+2*(F a)^2 by change (g a+F a)^2≤_;nlinarith only [sq_nonneg (g a-F a)]) (wn a (ysub ha)))
    simp only [mul_add,mul_left_comm (w _) (2:ℝ),sum_add_distrib,←mul_sum] at sum
    apply sum.trans
    dsimp only [lossBound]
    linarith only [gbound,sparse]
  have total := sum_sdiff (f:=fun a=>w a*(score a)^2) (filter_subset (fun a=>a∈rel.marks ∧ ¬hitD a) X)
  change (∑ a∈Y,w a*(score a)^2)+(∑ a∈J,w a*(score a)^2)=_ at total
  have transfer : (∑ a∈X,w a*(score a)^2)≤(∑ a∈J,w a*(score a)^2)+lossBound := by linarith only [total,lost]
  refine ⟨transfer,?_⟩
  intro margin
  have jp : 0 < ∑ a∈J,w a*(score a)^2 := by linarith only [margin,transfer]
  have witness : ∃ a∈J,0<w a*(score a)^2 := by
    by_contra! no
    exact jp.not_ge (sum_nonpos no)
  obtain ⟨a,ha,pos⟩ := witness
  obtain ⟨inX,retained,noHit⟩ := mem_filter.mp ha
  have wp := wn a inX
  exact ⟨a,inX,retained,fun j hj hit=>noHit ⟨j,hj,hit⟩,(lt_of_le_of_ne wp (fun zero=>by rw [←zero] at pos;simp at pos)),
    fun zero=>by simp [zero] at pos⟩

end
end Cogentic.Construction

#print axioms Cogentic.Construction.prescribed_marginal_lower
#print axioms Cogentic.Construction.physical_pair_upper_for_peeling
#print axioms Cogentic.Construction.retained_projected_energy
