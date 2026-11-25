import Cogentic.SingularSlopeMass
import Cogentic.CoefficientTail

namespace Cogentic.Construction
open Real Cogentic.Window

/-- A boxed constructor point has an ordinary prime dividing both its value
and its derivative, away from the slope progression modulus. -/
def boxedOrdinarySingular {n ell : ℕ} (R : PrescribedRows n ell) (side : Bool) (a : ℕ) (k : ℤ×ℤ) : Prop :=
  let s := TryPair.fixedInput n ell (construct n ell k.1.toNat k.2.toNat k.1.toNat k.2.toNat)
  inCoefficientBox n k ∧ ∃ p∈(Marking.value (s.coeffs side) a).primeFactors,
    p≠ell ∧ ¬p∣prodPrimes (R.miss a) ∧ p∣(Marking.horner (a:ℤ) (s.coeffs side)).2.natAbs

instance {n ell : ℕ} (R : PrescribedRows n ell) (side : Bool) (a : ℕ) (k : ℤ×ℤ) :
    Decidable (boxedOrdinarySingular R side a k) := by unfold boxedOrdinarySingular; infer_instance

/-- Among smooth first observations, a boxed derivative failure at an
ordinary factor prime away from the slope modulus costs at most b / 2^(500h)
of the original mass. This holds after restricting the observed
value by any predicate. -/
theorem PrescribedRows.boxed_ordinary_singular_loss_sharp {n ell a : ℕ} (R : PrescribedRows n ell)
    (hn : 2≤n) (big : 130000≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (mark : a∈(construct n ell 0 0 0 0).marks) (side : Bool) (F : ℤ→Prop) [DecidablePred F] :
    let J := sieveBand n ell (R.prefactor a side)
    let good := fun k : ℤ×ℤ => F (k.1+(a:ℤ)*k.2) ∧ supportedValue J (R.intercept a side k.1 k.2)
    prescribedProbability R side (fun k => good k ∧ boxedOrdinarySingular R side a k) ≤
      (((n.log2+1:ℕ):ℝ)/2^(500*Fixed.h (n.log2+1)))*prescribedProbability R side good := by
  classical
  intro J good
  let bad (k : ℤ×ℤ) := good k ∧ boxedOrdinarySingular R side a k
  let b := n.log2+1
  let δ : ℝ := (b:ℝ)/2^(500*Fixed.h b)
  have dp : 0≤δ := by dsimp [δ]; positivity
  let M := prodPrimes (R.miss a)
  let C := {k : ℤ×ℤ // R.compatible side k.1 k.2}
  let Z := ∑' k : C, coefficientWeight n k.val
  obtain ⟨_,cap,grid,_⟩ := (constructed_marks_iff ..).mp mark
  have large : 10004≤Fixed.d (n.log2+1) := le_trans (by decide) big
  obtain ⟨mp,mc⟩ := R.subprod_bounds (s:=R.miss a) Finset.sdiff_subset
  obtain ⟨c,r,e,coords,ws,zp,_,events⟩ := R.coefficient_law target side cap
  let x := fun i : ℤ => c+(R.hitProduct a:ℤ)*i
  let y := fun i j : ℤ => r i+(M:ℤ)*j
  let key (i j : ℤ) := (x i-(a:ℤ)*y i j,y i j)
  let W (k : ℤ×ℤ) := coefficientWeight n (key k.1 k.2)
  let V (E : ℤ×ℤ→Prop) [DecidablePred E] (k : ℤ×ℤ) := if E (key k.1 k.2) then W k else 0
  have wp (k : ℤ×ℤ) : 0<W k := mul_pos (exp_pos _) (exp_pos _)
  have summ : Summable W := by
    apply ws.congr
    intro k
    exact (coefficient_weight_projection ..).symm
  have vs (E : ℤ×ℤ→Prop) [DecidablePred E] : Summable (V E) := Summable.of_nonneg_of_le
    (fun k => by dsimp only [V]; split <;> first | exact (wp k).le | rfl)
    (fun k => by dsimp only [V]; split <;> first | exact (wp k).le | rfl) summ
  have prob (E : ℤ×ℤ→Prop) [DecidablePred E] :
      prescribedProbability R side E=(∑' k, V E k)/Z := by
    have h := events E
    change prescribedProbability R side E = _ at h
    rw [h]
    congr 1
    apply tsum_congr
    intro k
    dsimp only [V,W]
    split <;> first | exact (coefficient_weight_projection ..).symm | rfl
  have obs (i j : ℤ) : (key i j).1+(a:ℤ)*(key i j).2=x i := sub_add_cancel ..
  have fixed (i j l : ℤ) : good (key i j) ↔ good (key i l) := by simp only [good,intercept,obs]
  have compat (i j : ℤ) : R.compatible side (key i j).1 (key i j).2 := by
    have h := (e (i,j)).property
    rwa [coords] at h
  let inp (k : ℤ×ℤ) := TryPair.fixedInput n ell (construct n ell k.1.toNat k.2.toNat k.1.toNat k.2.toNat)
  let val (k : ℤ×ℤ) := Marking.value ((inp k).coeffs side) a
  have boxN (k : ℤ×ℤ) (h : inCoefficientBox n k) :
      k.1.toNat≤2*b^2*Fixed.U b*Fixed.A b ∧ k.2.toNat≤2*b^2*Fixed.U b := by
    constructor
    · exact_mod_cast ((Int.toNat_of_nonneg h.1.le).trans_le h.2.1)
    · exact_mod_cast ((Int.toNat_of_nonneg h.2.2.1.le).trans_le h.2.2.2)
  have boxedVal (i j : ℤ) (h : inCoefficientBox n (key i j)) :
      val (key i j)=(affineValue n ell a side (x i)).natAbs := by
    have id := congrArg Int.natAbs (signed_box_value hn large target cap grid (boxN _ h) side)
    have sign : (markSign n a side).natAbs=1 := by unfold markSign; split <;> decide
    simp only [Int.natAbs_mul,sign,one_mul,Int.natAbs_natCast,
      Int.toNat_of_nonneg h.1.le,Int.toNat_of_nonneg h.2.2.1.le,obs] at id
    exact id.symm
  have fiber (i : ℤ) : (∑' j : ℤ, V bad (i,j))≤δ*(∑' j : ℤ, V good (i,j)) := by
    by_cases witnessed : ∃ l, bad (key i l)
    · obtain ⟨l,gl,bl⟩ := witnessed
      let k := key i l
      have box : inCoefficientBox n k := bl.1
      have natU : (k.1.toNat:ℤ)=k.1 := Int.toNat_of_nonneg box.1.le
      have natV : (k.2.toNat:ℤ)=k.2 := Int.toNat_of_nonneg box.2.2.1.le
      have ok : R.compatible side k.1.toNat k.2.toNat := by rw [natU,natV]; exact compat i l
      have smooth := (R.box_smooth_iff hn large comp target absent cap grid (boxN _ box) side ok).mp
        (by rw [natU,natV]; exact gl.2)
      let P := (val k).primeFactors.filter (fun p => p≠ell ∧ ¬p∣M)
      let B := singularAtSlope n ell a M side (x i) (r i) P
      let U (j : ℤ) := if B j then W (i,j) else 0
      have loss := boxed_singular_slope_mass hn big comp target absent mark side (r i) mp mc (boxN _ box) smooth
      have zEq : (k.1.toNat:ℤ)+a*k.2.toNat=x i := by rw [natU,natV]; exact obs i l
      dsimp only at loss
      rw [zEq] at loss
      change (∑' j,U j)/(∑' j : ℤ, W (i,j))≤δ at loss
      have sub (j : ℤ) (h : bad (key i j)) : B j := by
        obtain ⟨hbox,p,pm,pe,pM,pd⟩ := h.2
        have eq : val (key i j)=val k := (boxedVal i j hbox).trans (boxedVal i l box).symm
        change p∈(val (key i j)).primeFactors at pm
        rw [eq] at pm
        exact ⟨hbox.1.le,hbox.2.2.1.le,p,Finset.mem_filter.mpr ⟨pm,pe,pM⟩,pd⟩
      have upper (j : ℤ) : V bad (i,j) ≤ U j := by
        by_cases f : bad (key i j)
        · simp only [V,U,if_pos f,if_pos (sub j f),le_refl]
        · simp only [V,U,if_neg f]; split <;> first | exact (wp _).le | rfl
      have us : Summable U := Summable.of_nonneg_of_le
        (fun j => by dsimp only [U]; split <;> first | exact (wp _).le | rfl)
        (fun j => by dsimp only [U]; split <;> first | exact (wp _).le | rfl) (summ.prod_factor i)
      have positive : 0<∑' j : ℤ, W (i,j) :=
        (wp (i,0)).trans_le ((summ.prod_factor i).le_tsum 0 (fun j _ => (wp _).le))
      have ge (j : ℤ) : V good (i,j)=W (i,j) := if_pos ((fixed i l j).mp gl)
      rw [tsum_congr ge]
      exact ((vs bad).prod_factor i|>.tsum_le_tsum upper us).trans ((div_le_iff₀ positive).mp loss)
    · have zero (j : ℤ) : V bad (i,j)=0 := if_neg (fun h => witnessed ⟨j,h⟩)
      rw [tsum_congr zero,tsum_zero]
      exact mul_nonneg dp (tsum_nonneg (fun j => by
        dsimp only [V]; split <;> first | exact (wp _).le | rfl))
  change prescribedProbability R side bad ≤ δ*prescribedProbability R side good
  rw [prob bad,prob good,←mul_div_assoc,div_le_div_iff_of_pos_right zp,
    (vs bad).tsum_prod,(vs good).tsum_prod,←tsum_mul_left]
  exact (vs bad).prod.tsum_le_tsum fiber ((vs good).prod.mul_left _)

theorem PrescribedRows.boxed_ordinary_singular_loss {n ell a : ℕ} (R : PrescribedRows n ell)
    (hn : 2≤n) (big : 130000≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (mark : a∈(construct n ell 0 0 0 0).marks) (side : Bool) (F : ℤ→Prop) [DecidablePred F] :
    let J := sieveBand n ell (R.prefactor a side)
    let good := fun k : ℤ×ℤ => F (k.1+(a:ℤ)*k.2) ∧ supportedValue J (R.intercept a side k.1 k.2)
    prescribedProbability R side (fun k => good k ∧ boxedOrdinarySingular R side a k) ≤
      (1/16)*prescribedProbability R side good := by
  intro J good
  have prob := R.boxed_ordinary_singular_loss_sharp hn big comp target absent mark side F
  refine prob.trans (mul_le_mul_of_nonneg_right (slope_loss_le_sixteenth (Nat.succ_pos n.log2)) ?_)
  unfold prescribedProbability
  apply div_nonneg
  · apply tsum_nonneg; intro k; split <;> first | exact mul_nonneg (exp_pos _).le (exp_pos _).le | rfl
  · exact tsum_nonneg (fun _ => mul_nonneg (exp_pos _).le (exp_pos _).le)

end Cogentic.Construction

#print axioms Cogentic.Construction.PrescribedRows.boxed_ordinary_singular_loss
