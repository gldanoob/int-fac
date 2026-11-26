import Cogentic.ProtectedInteractions
import Cogentic.ProtectedDrawPeeling

namespace Cogentic.Construction
open Finset Real Window
open scoped Classical
noncomputable section

/-- The single-root admission events measured on one unrestricted coefficient draw. -/
def admittedOrdinaryRows (n ell : ℕ) (x y : ℤ×ℤ) : Finset (BandRow (n.log2+1)) :=
  univ.filter fun i => OrdinaryAdmissible (n:=n) (ell:=ell) i ∧
    (singleOrdinaryPrescription (n:=n) (ell:=ell) i false).compatible false x.1 x.2 ∧
    (singleOrdinaryPrescription (n:=n) (ell:=ell) i true).compatible true y.1 y.2

/-- The Gaussian admission test enumerates exactly the ordinary rows of the
executable on each positive boxed coefficient tuple. In particular the
excluded residue of the common evaluation point cannot be a missing root. -/
theorem admitted_ordinary_rows_eq {n ell : ℕ} (hn : 2≤n) (hd : 3≤Fixed.d (n.log2+1))
    (composite : ¬n.Prime) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (sieved : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (x y : ℤ×ℤ) (bx : inCoefficientBox n x) (by' : inCoefficientBox n y) :
    let pair := construct n ell x.1.toNat x.2.toNat y.1.toNat y.2.toNat
    let s := TryPair.fixedInput n ell pair
    (admittedOrdinaryRows n ell x y).image (fun i=>Marking.Row.mk i.1 (bandRowPrime i) i.2.2.val) =
      s.rows.toFinset.filter (fun r=>r.q≠ell) := by
  classical
  intro pair s
  let b := n.log2+1
  let m := Fixed.rootBase n
  let row := fun i : BandRow b=>Marking.Row.mk i.1 (bandRowPrime i) i.2.2.val
  have xn := Int.toNat_of_nonneg bx.1.le
  have xv := Int.toNat_of_nonneg bx.2.2.1.le
  have yn := Int.toNat_of_nonneg by'.1.le
  have yv := Int.toNat_of_nonneg by'.2.2.1.le
  have iff (i : BandRow b) (ok : OrdinaryAdmissible (n:=n) (ell:=ell) i) :
      i∈admittedOrdinaryRows n ell x y ↔ row i∈s.rows := by
    have law := single_admission_listed i ok hn hd composite sieved x.1.toNat x.2.toNat y.1.toNat y.2.toNat
    dsimp only at law
    rw [xn,xv,yn,yv] at law
    simpa only [admittedOrdinaryRows,mem_filter,mem_univ,true_and,ok] using law
  ext r
  constructor
  · rintro h
    obtain ⟨i,hi,rfl⟩ := mem_image.mp h
    have ok := (mem_filter.mp hi).2.1
    exact mem_filter.mpr ⟨List.mem_toFinset.mpr ((iff i ok).mp hi),ok.2.1⟩
  · intro h
    obtain ⟨inList,ordinary⟩ := mem_filter.mp h
    have listed := List.mem_toFinset.mp inList
    obtain ⟨base,small,zero⟩ := Marking.mem_rows.mp listed
    have band : r.q∈sieveBand n ell 1 := by
      rw [sieveBand_executable hn hd composite sieved x.1.toNat x.2.toNat y.1.toNat y.2.toNat]
      exact List.mem_toFinset.mpr base
    let i : BandRow b := (r.second,⟨⟨r.q,(mem_filter.mp band).1⟩,⟨r.r,small⟩⟩)
    have same : row i=r := rfl
    refine mem_image.mpr ⟨i,(iff i ?_).mpr (same ▸ listed),same⟩
    refine ⟨band,ordinary,?_⟩
    change (r.r:ZMod r.q) ≠ m
    intro eq
    have atBase : r.q∣Marking.value (s.coeffs r.second) m := by
      apply (Marking.zero_at_mark _ m r.q).1.mp
      simpa only [Marking.horner_correct,ZMod.natCast_mod,←eq] using zero
    rw [Marking.value,horner_eval_int] at atBase
    let val := eval (m:ℤ) (s.coeffs r.second)
    have evs := constructed_root hn (surviving_coprime hn composite target sieved)
      x.1.toNat x.2.toNat y.1.toNat y.2.toNat
    have dv : (n:ℤ)∣val := by
      dsimp only [val]; cases r.second <;> first | exact evs.1 | exact evs.2
    have id : val.natAbs=(val/(n:ℤ)).natAbs*n := by
      conv_lhs => rw [←Int.ediv_mul_cancel dv,Int.natAbs_mul]
      simp
    have baseSpec := Marking.mem_base.mp base
    have qn : ¬r.q∣n := baseSpec.2.1.coprime_iff_not_dvd.mp (Nat.coprime_mul_iff_right.mp baseSpec.2.2.2).2
    have excluded := ((constructed_factorBase_iff n ell x.1.toNat x.2.toNat y.1.toNat y.2.toNat r.q).mp baseSpec.1).2.2.2
    have cof : (val/(n:ℤ)).natAbs∣markModulus n ell := by
      rw [markModulus_eq n ell x.1.toNat x.2.toNat y.1.toNat y.2.toNat]
      dsimp only [val]; cases r.second <;> first | exact dvd_mul_left .. | exact dvd_mul_right ..
    change r.q∣val.natAbs at atBase
    rw [id] at atBase
    exact excluded (((baseSpec.2.1.dvd_mul.mp atBase).resolve_right qn).trans cof)

/-- The ordinary mass selected on the coefficient draw controls every subset
of executable ordinary rows left after peeling. -/
theorem surviving_ordinary_mass {n ell : ℕ} (hn : 2≤n) (hd : 3≤Fixed.d (n.log2+1))
    (composite : ¬n.Prime) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (sieved : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (x y : ℤ×ℤ) (bx : inCoefficientBox n x) (by' : inCoefficientBox n y) (β u : ℝ)
    (window : u≤110*(Fixed.d (n.log2+1):ℝ))
    (mass : (∑ i∈admittedOrdinaryRows n ell x y,(bandRowPrime i:ℝ)^(-β))<128*u) :
    let input := TryPair.fixedInput n ell (construct n ell x.1.toNat x.2.toNat y.1.toNat y.2.toNat)
    ∀ A : Finset Marking.Row, A⊆input.rows.toFinset → (∀ i∈A,i.q≠ell) →
      (∀ i∈A,i.q∈primeBand (n.log2+1)) ∧ (∑ i : A,(i.val.q:ℝ)^(-β))≤15000*(Fixed.d (n.log2+1):ℝ) := by
  classical
  intro input A sub ordinary
  let row := fun i : BandRow (n.log2+1)=>Marking.Row.mk i.1 (bandRowPrime i) i.2.2.val
  let S := admittedOrdinaryRows n ell x y
  have imageEq := admitted_ordinary_rows_eq hn hd composite target sieved x y bx by'
  change S.image row=input.rows.toFinset.filter (fun r=>r.q≠ell) at imageEq
  have cover : A⊆S.image row := by
    rw [imageEq]
    exact fun i hi=>mem_filter.mpr ⟨sub hi,ordinary i hi⟩
  constructor
  · intro i hi
    obtain ⟨j,_,rfl⟩ := mem_image.mp (cover hi)
    exact j.2.1.property
  · rw [sum_coe_sort A (fun r : Marking.Row=>(r.q:ℝ)^(-β))]
    have nn (r : Marking.Row) : 0≤(r.q:ℝ)^(-β) := rpow_nonneg (Nat.cast_nonneg _) _
    have small := sum_le_sum_of_subset_of_nonneg cover (f:=fun r : Marking.Row=>(r.q:ℝ)^(-β)) (fun r _ _=>nn r)
    have whole := sum_image_le_of_nonneg (s:=S) (g:=row) (f:=fun r : Marking.Row=>(r.q:ℝ)^(-β)) (fun r _=>nn r)
    exact (small.trans whole).trans (mass.le.trans (by linarith only [window,Nat.cast_nonneg (α:=ℝ) (Fixed.d (n.log2+1))]))

/-- Simultaneous admission of two distinct ordinary primes, on their indicated fields. -/
def ordinaryPairPrescription {n ell : ℕ} (i j : BandRow (n.log2+1))
    (hi : OrdinaryAdmissible (n:=n) (ell:=ell) i) (hj : OrdinaryAdmissible (n:=n) (ell:=ell) j)
    (pq : bandRowPrime i≠bandRowPrime j) (s : Bool) : PrescribedRows n ell where
  primes := (if i.1=s then {bandRowPrime i} else ∅) ∪ (if j.1=s then {bandRowPrime j} else ∅)
  residue := fun q=>if q=bandRowPrime i then i.2.2.val else j.2.2.val
  member := by
    intro q h
    split_ifs at h <;> simp only [union_empty,empty_union,mem_union,mem_singleton,notMem_empty] at h
    all_goals first
      | rcases h with rfl | rfl <;> first | exact hi.1 | exact hj.1
      | subst q; first | exact hi.1 | exact hj.1
      | contradiction
  limit := by split_ifs <;> simp [pq]
  excluded := by split_ifs <;> simp [Ne.symm hi.2.1,Ne.symm hj.2.1]
  away := by
    intro q h
    split_ifs at h <;> simp only [union_empty,empty_union,mem_union,mem_singleton,notMem_empty] at h
    all_goals first
      | rcases h with rfl | rfl <;> simp [pq.symm,hi.2.2,hj.2.2]
      | subst q; simp [pq.symm,hi.2.2,hj.2.2]
      | contradiction

/-- Row membership and the exact multiplicative admission modulus on both fields. -/
theorem ordinary_pair_admission {n ell : ℕ} (i j : BandRow (n.log2+1))
    (hi : OrdinaryAdmissible (n:=n) (ell:=ell) i) (hj : OrdinaryAdmissible (n:=n) (ell:=ell) j)
    (pq : bandRowPrime i≠bandRowPrime j) :
    let R := ordinaryPairPrescription i j hi hj pq
    (prodPrimes (R false).primes*prodPrimes (R true).primes=bandRowPrime i*bandRowPrime j) ∧
    (∀ s, (R s).primes⊆{bandRowPrime i,bandRowPrime j} ∧
      ((R s).residue (bandRowPrime i)=i.2.2.val) ∧ ((R s).residue (bandRowPrime j)=j.2.2.val)) ∧
    ∀ x y : ℤ×ℤ, (R false).compatible false x.1 x.2 ∧ (R true).compatible true y.1 y.2 ↔
      i∈admittedOrdinaryRows n ell x y ∧ j∈admittedOrdinaryRows n ell x y := by
  intro R
  refine ⟨?_,?_,?_⟩
  · cases s : i.1 <;> cases t : j.1 <;>
      simp [R,ordinaryPairPrescription,prodPrimes,s,t,pq,pq.symm,mul_comm]
  · intro s
    refine ⟨?_,by simp [R,ordinaryPairPrescription],by simp [R,ordinaryPairPrescription,pq.symm]⟩
    dsimp only [R,ordinaryPairPrescription]
    split_ifs <;> simp
  · intro x y
    simp only [admittedOrdinaryRows,mem_filter,mem_univ,true_and,hi,hj]
    cases s : i.1 <;> cases t : j.1 <;>
      simp [R,ordinaryPairPrescription,PrescribedRows.compatible,singleOrdinaryPrescription,
        PrescribedRows.unrestricted,hi,hj,s,t,pq,pq.symm] <;> tauto

/-- Each accepted residue contributes its saddle mass. The first moment pays
for the number of residues using their actual admission probabilities. -/
theorem admitted_ordinary_mass {n ell : ℕ} (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    {α u : ℝ} (ap : 0≤α)
    (saddle : saddleMean (primeBand (n.log2+1)) α=log (Fixed.B (n.log2+1))*u) :
    let O := PrescribedRows.unrestricted n ell; let Ω := O.CoeffPoint false × O.CoeffPoint true
    ∃ μ : ℝ, HasSum (fun k : Ω=>twoFieldWeight O O k*
      (∑ i∈admittedOrdinaryRows n ell k.1.val k.2.val,(bandRowPrime i:ℝ)^(-α))) μ ∧ μ≤32*u := by
  classical
  intro O Ω
  let b := n.log2+1
  let I := (univ : Finset (BandRow b)).filter (OrdinaryAdmissible (n:=n) (ell:=ell))
  let R := fun i=>singleOrdinaryPrescription (n:=n) (ell:=ell) i false
  let T := fun i=>singleOrdinaryPrescription (n:=n) (ell:=ell) i true
  let E := fun (i : BandRow b) (x : ℤ×ℤ)=>(R i).compatible false x.1 x.2
  let F := fun (i : BandRow b) (y : ℤ×ℤ)=>(T i).compatible true y.1 y.2
  let m := fun i : BandRow b=>(bandRowPrime i:ℝ)^(-α)
  let P := fun i=>prescribedProbability O false (E i)*prescribedProbability O true (F i)
  have total := twoField_score_mean O O target I m E F
  refine ⟨_,total.congr_fun (fun k=>?_ ),?_⟩
  · congr 1
    simp [twoFieldScore,admittedOrdinaryRows,I,E,F,R,T,m,sum_filter,mul_ite,ite_and]
  change (∑ i∈I,m i*P i) ≤ 32*u
  have one (i : BandRow b) (hi : i∈I) : P i≤4/(bandRowPrime i:ℝ) := by
    obtain ⟨A,pos,close,admit⟩ := twoField_admission_probability (R i) (T i) target
    have all : twoFieldProbability (R i) (T i) (fun _ _=>True)=1 := by
      simpa only [twoFieldProbability,if_true] using (twoField_total (R i) (T i) target).tsum_eq
    have eq := admit (fun _ _=>True)
    simp only [and_true,all,mul_one] at eq
    have pp : P i=A := (twoField_probability_rectangle O O target (E i) (F i)).symm.trans eq
    let η := 72*exp (-(Fixed.U b:ℝ))
    have dp := Fixed.degree_pos (b:=b) (Nat.succ_pos n.log2)
    have vp : 0<Fixed.v b := Nat.mul_pos dp (Nat.mul_pos dp (Nat.succ_pos _))
    have uc : 72≤(Fixed.U b:ℝ) := by
      exact_mod_cast (by decide : 72≤2^7).trans (Nat.pow_le_pow_right (by decide : 0<2) (by omega))
    have en : 0≤η := by dsimp [η];positivity
    have small : η≤1 := by
      dsimp only [η]; rw [exp_neg,←div_eq_mul_inv,div_le_one (exp_pos _)]
      linarith only [add_one_le_exp (Fixed.U b),uc]
    have modEq : (prodPrimes (R i).primes:ℝ)*prodPrimes (T i).primes=(bandRowPrime i:ℝ) := by
      exact_mod_cast single_modulus i (mem_filter.mp hi).2
    change |(↑(prodPrimes (R i).primes)*↑(prodPrimes (T i).primes))*A-1|≤2*η+η^2 at close
    rw [modEq] at close
    rw [pp,le_div_iff₀ (by exact_mod_cast (mem_primeBand.mp i.2.1.property).1.pos : (0:ℝ)<bandRowPrime i)]
    nlinarith only [(abs_le.mp close).2,mul_nonneg (sub_nonneg.mpr small) en,small]
  have each := sum_le_sum (s:=I) (fun i hi=>mul_le_mul_of_nonneg_left (one i hi)
    (rpow_nonneg (Nat.cast_nonneg (bandRowPrime i)) (-α)))
  have budget : (∑ i∈I,bandRowWeight α i)≤8*u :=
    (sum_le_sum_of_subset_of_nonneg (subset_univ I) (fun _ _ _=>div_nonneg (rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _))).trans
      (band_row_weight_sum (by exact_mod_cast (Nat.one_lt_pow
        (Nat.mul_ne_zero (by decide) (Nat.mul_ne_zero (Fixed.degree_pos (Nat.succ_pos _)).ne' (Nat.succ_ne_zero _)))
        (by decide) : 1<Fixed.B b)) ap saddle)
  apply each.trans
  calc
    _ = 4*∑ i∈I,bandRowWeight α i := by
      rw [mul_sum]
      apply sum_congr rfl; intro i _
      dsimp only [bandRowWeight]; ring
    _ ≤ _ := by linarith only [budget]

def admissibleOrdinaryPairs (n ell : ℕ) : Finset (BandRow (n.log2+1)×BandRow (n.log2+1)) :=
  univ.filter fun k=>OrdinaryAdmissible (n:=n) (ell:=ell) k.1 ∧
    OrdinaryAdmissible (n:=n) (ell:=ell) k.2 ∧ bandRowPrime k.1≠bandRowPrime k.2

theorem admissible_pair_spec {n ell : ℕ} (k : ↥(admissibleOrdinaryPairs n ell)) :
    OrdinaryAdmissible (n:=n) (ell:=ell) k.val.1 ∧ OrdinaryAdmissible (n:=n) (ell:=ell) k.val.2 ∧
    bandRowPrime k.val.1≠bandRowPrime k.val.2 := (mem_filter.mp k.property).2

def ordinaryPairOnField {n ell : ℕ} (a : ↥(admissibleOrdinaryPairs n ell)) (s : Bool) : PrescribedRows n ell :=
  ordinaryPairPrescription a.val.1 a.val.2 (admissible_pair_spec a).1 (admissible_pair_spec a).2.1 (admissible_pair_spec a).2.2 s

def boxedAdmittedScore {n ell : ℕ} (admit : (ℤ×ℤ)→(ℤ×ℤ)→Prop)
    (w : ℕ→ℝ) (x y : ℤ×ℤ) : ℝ :=
  let O := PrescribedRows.unrestricted n ell
  if inCoefficientBox n x ∧ inCoefficientBox n y ∧ admit x y then
    twoFieldScore (univ.biUnion (constructorCellMarks n ell)) w (smoothMarkEvent O false) (smoothMarkEvent O true) x y else 0

def boxedPhysicalPairScore {n ell : ℕ} (a : ↥(admissibleOrdinaryPairs n ell))
    (w : ℕ→ℝ) (x y : ℤ×ℤ) : ℝ :=
  boxedAdmittedScore (n:=n) (ell:=ell)
    (fun x y=>a.val.1∈admittedOrdinaryRows n ell x y ∧ a.val.2∈admittedOrdinaryRows n ell x y) w x y

def boxedPhysicalPairCost {n ell : ℕ} (α : ℝ) (w : ↥(admissibleOrdinaryPairs n ell)→ℕ→ℝ) (x y : ℤ×ℤ) : ℝ :=
  ∑ a : ↥(admissibleOrdinaryPairs n ell),(bandRowPrime a.val.1:ℝ)^(-α)*(bandRowPrime a.val.2:ℝ)^(-α)*(boxedPhysicalPairScore a (w a) x y)^2

/-- Restrict an unrestricted score to boxed draws admitting its prescriptions.
The zero extension still pays only the probability of the prescribed roots. -/
private theorem boxed_admitted_second {n ell : ℕ} (hn : 2≤n) (hd : 10004≤Fixed.d (n.log2+1))
    (comp : ¬n.Prime) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (R T : PrescribedRows n ell) (admit : (ℤ×ℤ)→(ℤ×ℤ)→Prop)
    (compat : ∀ x y, admit x y → R.compatible false x.1 x.2 ∧ T.compatible true y.1 y.2)
    (w : ℕ→ℝ) (ε : ℝ) (ep : 0≤ε) :
    let X := univ.biUnion (constructorCellMarks n ell)
    twoFieldSecond R T X w (smoothMarkEvent R false) (smoothMarkEvent T true) ≤ ε →
    let O := PrescribedRows.unrestricted n ell
    let Ω := O.CoeffPoint false × O.CoeffPoint true
    let err := fun (t : Ω)=>boxedAdmittedScore (n:=n) (ell:=ell) admit w t.1.val t.2.val
    let obs := fun t : Ω=>twoFieldWeight O O t*(err t)^2
    HasSum obs (∑' t,obs t) ∧ (∑' t,obs t) ≤ 4*ε/((prodPrimes R.primes:ℝ)*prodPrimes T.primes) := by
  classical
  intro X conditional O Ω err obs
  let W := twoFieldWeight O O
  let E := smoothMarkEvent O false
  let F := smoothMarkEvent O true
  let l := fun j (k : ℤ×ℤ)=>R.compatible false k.1 k.2 ∧ smoothMarkEvent R false j k
  let r := fun j (k : ℤ×ℤ)=>T.compatible true k.1 k.2 ∧ smoothMarkEvent T true j k
  have hs := twoField_score_second O O target X w l r
  have wp (t : Ω) : 0≤W t := mul_nonneg (O.pointMass_nonneg false _) (O.pointMass_nonneg true _)
  have dom (t : Ω) : obs t≤W t*(twoFieldScore X w l r t.1.val t.2.val)^2 := by
    apply mul_le_mul_of_nonneg_left _ (wp t)
    dsimp only [err,boxedAdmittedScore]
    split
    next h =>
      obtain ⟨left,right⟩ := compat _ _ h.2.2
      have eq : twoFieldScore X w E F t.1.val t.2.val=twoFieldScore X w l r t.1.val t.2.val := by
        apply sum_congr rfl
        intro j hj
        obtain ⟨c,_,hc⟩ := mem_biUnion.mp hj
        have mark := (mem_filter.mp hc).2
        have eqL := boxed_prescribed_smooth_iff R false hn hd comp target absent mark ⟨t.1.val,left⟩ h.1
        have eqR := boxed_prescribed_smooth_iff T true hn hd comp target absent mark ⟨t.2.val,right⟩ h.2.1
        simp only [l,r,left,right,true_and,eqL,eqR,E,F,O]
      exact (congrArg (·^2) eq).le
    next => simpa only [zero_pow (by decide : 2≠0)] using sq_nonneg (twoFieldScore X w l r t.1.val t.2.val)
  have sm := Summable.of_nonneg_of_le (fun t=>mul_nonneg (wp t) (sq_nonneg (err t))) dom hs.summable
  exact ⟨sm.hasSum,(hasSum_le dom sm.hasSum hs).trans
    (admitted_second_bound R T target X w (smoothMarkEvent R false) (smoothMarkEvent T true) ε ep conditional)⟩

/-- All distinct ordinary-pair estimates are paid for on the original coefficient
law, summing only the actual admitted rows of each boxed tuple. This cost can
be inserted directly in the protected-rank draw. -/
theorem admitted_physical_gram_budget {n ell : ℕ} (hn : 2≤n) (hd : 10004≤Fixed.d (n.log2+1))
    (comp : ¬n.Prime) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (α u ε : ℝ) (ap : 0≤α) (ep : 0≤ε)
    (saddle : saddleMean (primeBand (n.log2+1)) α=log (Fixed.B (n.log2+1))*u)
    (w : ↥(admissibleOrdinaryPairs n ell)→ℕ→ℝ)
    (conditional : ∀ a, twoFieldSecond (ordinaryPairOnField a false) (ordinaryPairOnField a true)
      (univ.biUnion (constructorCellMarks n ell)) (w a) (smoothMarkEvent (ordinaryPairOnField a false) false)
        (smoothMarkEvent (ordinaryPairOnField a true) true) ≤ ε) :
    let O := PrescribedRows.unrestricted n ell
    let Ω := O.CoeffPoint false × O.CoeffPoint true
    ∃ μ : ℝ, (∀ t : Ω,0≤boxedPhysicalPairCost α w t.1.val t.2.val) ∧
      HasSum (fun t : Ω=>twoFieldWeight O O t*boxedPhysicalPairCost α w t.1.val t.2.val) μ ∧ μ≤256*u^2*ε := by
  classical
  intro O Ω
  let b := n.log2+1; let X := univ.biUnion (constructorCellMarks n ell); let I := admissibleOrdinaryPairs n ell
  let valid := @admissible_pair_spec n ell
  let R := @ordinaryPairOnField n ell
  let m := fun i : BandRow b=>(bandRowPrime i:ℝ)^(-α)
  let err := fun (a : ↥I) (t : Ω)=>boxedPhysicalPairScore a (w a) t.1.val t.2.val
  let cost := fun (t : Ω)=>∑ a : ↥I,m a.val.1*m a.val.2*(err a t)^2
  change ∃ μ : ℝ, (∀ t : Ω,0≤cost t) ∧ HasSum (fun t : Ω=>twoFieldWeight O O t*cost t) μ ∧ _
  let W := twoFieldWeight O O
  have mn (i) : 0 ≤ m i := rpow_nonneg (Nat.cast_nonneg _) _
  let mass := fun (a : ↥I)=>m a.val.1*m a.val.2
  have massPos (a) : 0 ≤ mass a := mul_nonneg (mn _) (mn _)
  let V := fun a : ↥I=>∑' t : Ω,W t*(err a t)^2
  have est (a : ↥I) : HasSum (fun t : Ω=>W t*(err a t)^2) (V a) ∧
      V a ≤ 4*ε/((bandRowPrime a.val.1:ℝ)*bandRowPrime a.val.2) := by
    have pair := ordinary_pair_admission a.val.1 a.val.2 (valid a).1 (valid a).2.1 (valid a).2.2
    have est := boxed_admitted_second hn hd comp target absent (R a false) (R a true)
      (fun x y=>a.val.1∈admittedOrdinaryRows n ell x y ∧ a.val.2∈admittedOrdinaryRows n ell x y)
      (fun x y=>(pair.2.2 x y).mpr) (w a) ε ep (conditional a)
    have id : (prodPrimes (R a false).primes:ℝ)*prodPrimes (R a true).primes=
        (bandRowPrime a.val.1:ℝ)*bandRowPrime a.val.2 := by exact_mod_cast pair.1
    exact ⟨est.1,id ▸ est.2⟩
  let bw := bandRowWeight (b:=b) α
  have scale (a : ↥I) : mass a*V a≤4*ε*(bw a.val.1*bw a.val.2) :=
    (mul_le_mul_of_nonneg_left (est a).2 (massPos a)).trans_eq (by dsimp [mass,m,bw,bandRowWeight];ring)
  have bp : 1<(Fixed.B b:ℝ) := by exact_mod_cast (Nat.one_lt_pow
    (Nat.mul_ne_zero (by decide) (Nat.mul_ne_zero (Fixed.degree_pos (Nat.succ_pos n.log2)).ne' (Nat.succ_ne_zero _))) (by decide) : 1<Fixed.B b)
  have totals : (∑ a:↥I,bw a.val.1*bw a.val.2)≤(8*u)^2 := by
    rw [sum_coe_sort I (fun a : BandRow b×BandRow b=>bw a.1*bw a.2)]
    have bn (i : BandRow b) : 0≤bw i := div_nonneg (mn _) (Nat.cast_nonneg _)
    apply (sum_le_sum_of_subset_of_nonneg (subset_univ I) (fun i _ _=>mul_nonneg (bn i.1) (bn i.2))).trans
    rw [Fintype.sum_prod_type]; simp only [←mul_sum,←sum_mul,←sq]
    exact pow_le_pow_left₀ (sum_nonneg (fun i _=>bn i)) (band_row_weight_sum bp ap saddle) 2
  have sum := hasSum_sum (s:=univ) (fun a _=>(est a).1.mul_left (mass a))
  refine ⟨_,fun t=>sum_nonneg (fun a _=>mul_nonneg (massPos a) (sq_nonneg _)),sum.congr_fun (fun t=>?_ ),?_⟩
  · simp only [cost,mul_sum]; apply sum_congr rfl;intro a _;dsimp only [mass,W];ring
  · have bd := sum_le_sum (s:=univ) (fun a _=>scale a)
    rw [←mul_sum] at bd
    exact bd.trans ((mul_le_mul_of_nonneg_left totals (by positivity : 0≤4*ε)).trans_eq (by ring))

def admissibleOrdinaryRows (n ell : ℕ) := (univ : Finset (BandRow (n.log2+1))).filter
  (OrdinaryAdmissible (n:=n) (ell:=ell))

def ordinarySingleOnField {n ell : ℕ} (i : ↥(admissibleOrdinaryRows n ell)) : Bool→PrescribedRows n ell :=
  singleOrdinaryPrescription i.val

def boxedPhysicalSingleCost {n ell : ℕ} (α : ℝ) (w : ↥(admissibleOrdinaryRows n ell)→ℕ→ℝ)
    (x y : ℤ×ℤ) : ℝ :=
  ∑ i : ↥(admissibleOrdinaryRows n ell),(bandRowPrime i.val:ℝ)^(-α)*
    (boxedAdmittedScore (n:=n) (ell:=ell) (fun x y=>i.val∈admittedOrdinaryRows n ell x y) (w i) x y)^2

/-- The singleton version of the admission budget also controls the normalized
Gram diagonal. A row exceeding a diagonal tolerance is charged its saddle mass. -/
theorem admitted_physical_single_budget {n ell : ℕ} (hn : 2≤n) (hd : 10004≤Fixed.d (n.log2+1))
    (comp : ¬n.Prime) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (α u ε : ℝ) (ap : 0≤α) (ep : 0≤ε)
    (saddle : saddleMean (primeBand (n.log2+1)) α=log (Fixed.B (n.log2+1))*u)
    (w : ↥(admissibleOrdinaryRows n ell)→ℕ→ℝ)
    (conditional : ∀ i, twoFieldSecond (ordinarySingleOnField i false) (ordinarySingleOnField i true)
      (univ.biUnion (constructorCellMarks n ell)) (w i) (smoothMarkEvent (ordinarySingleOnField i false) false)
      (smoothMarkEvent (ordinarySingleOnField i true) true) ≤ ε) :
    let O := PrescribedRows.unrestricted n ell
    let Ω := O.CoeffPoint false × O.CoeffPoint true
    ∃ μ : ℝ, (∀ t : Ω,0≤boxedPhysicalSingleCost α w t.1.val t.2.val) ∧
      HasSum (fun t : Ω=>twoFieldWeight O O t*boxedPhysicalSingleCost α w t.1.val t.2.val) μ ∧ μ≤32*u*ε := by
  classical
  intro O Ω
  let b := n.log2+1; let I := admissibleOrdinaryRows n ell
  let R := @ordinarySingleOnField n ell
  let err := fun (i : ↥I) (t : Ω)=>boxedAdmittedScore (n:=n) (ell:=ell)
    (fun x y=>i.val∈admittedOrdinaryRows n ell x y) (w i) t.1.val t.2.val
  let cost := fun t : Ω=>∑ i : ↥I,(bandRowPrime i.val:ℝ)^(-α)*(err i t)^2
  change ∃ μ : ℝ, (∀ t : Ω,0≤cost t) ∧ HasSum (fun t : Ω=>twoFieldWeight O O t*cost t) μ ∧ _
  let m := fun i : ↥I=>(bandRowPrime i.val:ℝ)^(-α)
  let W := twoFieldWeight O O
  let v := fun i : ↥I=>∑' t : Ω,W t*(err i t)^2
  have mn (i : ↥I) : 0 ≤ m i := rpow_nonneg (Nat.cast_nonneg _) _
  have est (i : ↥I) : HasSum (fun t : Ω=>W t*(err i t)^2) (v i) ∧ v i≤4*ε/(bandRowPrime i.val:ℝ) := by
    have q := boxed_admitted_second hn hd comp target absent (R i false) (R i true)
      (fun x y=>i.val∈admittedOrdinaryRows n ell x y)
      (fun _ _ h=>(mem_filter.mp h).2.2) (w i) ε ep (conditional i)
    have modEq : (prodPrimes (R i false).primes:ℝ)*prodPrimes (R i true).primes=bandRowPrime i.val := by
      exact_mod_cast single_modulus i.val (mem_filter.mp i.property).2
    exact ⟨q.1,modEq ▸ q.2⟩
  have bp : 1<(Fixed.B b:ℝ) := by exact_mod_cast (Nat.one_lt_pow
    (Nat.mul_ne_zero (by decide) (Nat.mul_ne_zero (Fixed.degree_pos (Nat.succ_pos n.log2)).ne' (Nat.succ_ne_zero _))) (by decide) : 1<Fixed.B b)
  have mass : (∑ i : ↥I,bandRowWeight α i.val)≤8*u := by
    rw [sum_coe_sort I (bandRowWeight α)]
    exact (sum_le_sum_of_subset_of_nonneg (subset_univ I) (fun i _ _=>div_nonneg
      (rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _))).trans (band_row_weight_sum bp ap saddle)
  have both := hasSum_sum (s:=univ) (fun i _=>(est i).1.mul_left (m i))
  refine ⟨_,fun t=>sum_nonneg (fun i _=>mul_nonneg (mn i) (sq_nonneg _)),both.congr_fun (fun t=>?_ ),?_⟩
  · simp only [cost,mul_sum]
    apply sum_congr rfl
    intro i _
    dsimp only [m,W]
    ring
  · calc
      _ ≤ ∑ i : ↥I,4*ε*bandRowWeight α i.val := sum_le_sum fun i _=>
        (mul_le_mul_of_nonneg_left (est i).2 (mn i)).trans_eq (by dsimp [m,bandRowWeight];ring)
      _ ≤ 4*ε*(8*u) := by rw [←mul_sum];exact mul_le_mul_of_nonneg_left mass (by positivity)
      _ = _ := by ring

/-- Loss of ordinary-row mass and energy on the marks rejected by stage one. -/
def RejectedRowControl (n ell : ℕ) (mix : Option (Bool×Fin (Fixed.d (n.log2+1)))→ℝ)
    (mass scale : Marking.Row→ℝ) (x y : ℤ×ℤ) : Prop :=
  let b := n.log2+1; let e := exp (-(Fixed.z b:ℝ)^2)
  let O := PrescribedRows.unrestricted n ell
  let input := TryPair.fixedInput n ell (construct n ell x.1.toNat x.2.toNat y.1.toNat y.2.toNat)
  let rows := input.rows.toFinset.filter (fun i=>i.q≠ell)
  let X := univ.biUnion (constructorCellMarks n ell)
  let Y := X.filter (fun a=>rejectedSmoothMark O O a x y)
  let wt := fun a=>constructorMixturePrior n ell mix a/smoothMarkProbability O O a
  let z := fun (i : Marking.Row) (a : ℕ)=>if a%i.q=i.r then scale i else 0
  let bad := rows.filter (fun i=>e ≤ ∑ a∈Y,wt a*(z i a)^2)
  (∑ a∈Y,wt a)<e^3 ∧ (∑ i∈bad,mass i)≤b*e^2 ∧
  ∀ v : Marking.Row→ℝ, (∑ a∈Y,wt a*(∑ i∈rows\bad,z i a*v i)^2)≤
    (b:ℝ)*e*(∑ i∈rows\bad,(v i)^2)

/-- The same draw supports the protected rank and the ordinary mass bound.
Half the probability budget is available for further empirical Gram tests. -/
theorem protected_rank_ordinary_mass_peeling (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1
    let O := PrescribedRows.unrestricted n ell; let Ω := O.CoeffPoint false × O.CoeffPoint true
    ∀ (α u : ℝ), 0≤α → 0<u → saddleMean (primeBand b) α=log (Fixed.B b)*u →
    ∀ mix : Option (Bool×Fin (Fixed.d b))→ℝ, (∀ c,0 ≤ mix c) → (∑ c,mix c)=1 →
    ∀ (mass scale : Marking.Row→ℝ), (∀ i,i.q.Prime → mass i*scale i^2=1) →
    ∀ (cost : Ω→ℝ) (budget : ℝ), (∀ k,0 ≤ cost k) →
    HasSum (fun k=>twoFieldWeight O O k*cost k) budget → budget≤1/2 →
    ∃ k : Ω, retainedDenominatorGood n ell mix k.1.val k.2.val ∧
      protectedDrawRank n ell k.1.val k.2.val ∧ cost k<1 ∧
      (∑ i∈admittedOrdinaryRows n ell k.1.val k.2.val,(bandRowPrime i:ℝ)^(-α))<128*u ∧
      RejectedRowControl n ell mix mass scale k.1.val k.2.val := by
  obtain ⟨n₁,choose⟩ := protected_rank_denominator_peeling line 16 (by decide)
  obtain ⟨b₂,tiny⟩ := retained_denominator_budget_vanishes 16 (by decide)
  refine ⟨max n₁ (max 2 (2^b₂)),?_⟩
  intro n big ell target comp sieve b O Ω α u ap up saddle mix pos norm mass scale unit cost budget cn avg bound
  obtain ⟨old,lim⟩ := max_le_iff.mp big
  obtain ⟨hn,lg⟩ := max_le_iff.mp lim
  have small := tiny b (((Nat.le_log2 (by omega : n≠0)).mpr lg).trans (Nat.le_succ _))
  let e := exp (-(Fixed.z b:ℝ)^2)
  let M (k : Ω) := ∑ i∈admittedOrdinaryRows n ell k.1.val k.2.val,(bandRowPrime i:ℝ)^(-α)
  have nonneg (k : Ω) : 0≤M k := sum_nonneg (fun _ _=>rpow_nonneg (Nat.cast_nonneg _) _)
  obtain ⟨μ,measure,rate⟩ := admitted_ordinary_mass target ap saddle
  have cap : 0<128*u := by positivity
  have qbound : μ/(128*u)≤1/4 := (div_le_iff₀ cap).mpr (by linarith only [rate])
  have both : HasSum (fun k : Ω=>twoFieldWeight O O k*(cost k+M k/(128*u))) (budget+μ/(128*u)) := by
    apply (avg.add (measure.div_const (128*u))).congr_fun
    intro k; dsimp only [M]; ring
  have fit : (budget+μ/(128*u))+1/(16:ℝ)+256/(Fixed.d b:ℝ)+5*e+1/(Fixed.B b:ℝ)<1 := by
    change 256/(Fixed.d b:ℝ)+4*e+1/(Fixed.B b:ℝ)≤1/(16:ℝ) at small
    have d := div_nonneg (by norm_num : (0:ℝ)≤256) (Nat.cast_nonneg (α:=ℝ) (Fixed.d b))
    have B := one_div_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) (Fixed.B b))
    linarith only [small,d,B,bound,qbound]
  obtain ⟨k,den,rank,tests,loss,smallBad,energy⟩ := choose n old ell target comp sieve mix pos norm mass scale
    unit (fun k=>cost k+M k/(128*u)) _ (fun k=>add_nonneg (cn k) (div_nonneg (nonneg k) cap.le)) both fit
  refine ⟨k,den,rank,(le_add_of_nonneg_right (div_nonneg (nonneg k) cap.le)).trans_lt tests,?_,loss,smallBad,energy⟩
  have less := (le_add_of_nonneg_left (cn k)).trans_lt tests
  exact (div_lt_one cap).mp less

theorem protected_rank_ordinary_mass (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1
    let O := PrescribedRows.unrestricted n ell; let Ω := O.CoeffPoint false × O.CoeffPoint true
    ∀ (α u : ℝ), 0≤α → 0<u → saddleMean (primeBand b) α=log (Fixed.B b)*u →
    ∀ mix : Option (Bool×Fin (Fixed.d b))→ℝ, (∀ c,0 ≤ mix c) → (∑ c,mix c)=1 →
    ∀ (cost : Ω→ℝ) (budget : ℝ), (∀ k,0 ≤ cost k) →
    HasSum (fun k=>twoFieldWeight O O k*cost k) budget → budget≤1/2 →
    ∃ k : Ω, retainedDenominatorGood n ell mix k.1.val k.2.val ∧
      protectedDrawRank n ell k.1.val k.2.val ∧ cost k<1 ∧
      (∑ i∈admittedOrdinaryRows n ell k.1.val k.2.val,(bandRowPrime i:ℝ)^(-α))<128*u := by
  obtain ⟨m,draw⟩ := protected_rank_ordinary_mass_peeling line
  refine ⟨m,?_⟩
  intro n large ell target comp absent b O Ω α u ap up saddle mix pos norm cost budget cn avg bound
  obtain ⟨k,den,rank,cheap,mass,_⟩ := draw n large ell target comp absent α u ap up saddle mix pos norm
    (fun _=>1) (fun _=>1) (by simp) cost budget cn avg bound
  exact ⟨k,den,rank,cheap,mass⟩

end
end Cogentic.Construction

#print axioms Cogentic.Construction.admitted_ordinary_mass

#print axioms Cogentic.Construction.protected_rank_ordinary_mass
