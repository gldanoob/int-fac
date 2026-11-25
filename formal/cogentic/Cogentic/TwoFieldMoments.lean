import Cogentic.BoxWitness

namespace Cogentic.Construction
open Real Cogentic.Window
open scoped Classical
noncomputable section

abbrev PrescribedRows.CoeffPoint {n ell : ℕ} (R : PrescribedRows n ell) (side : Bool) :=
  {k : ℤ×ℤ // R.compatible side k.1 k.2}

/-- The point mass of the original Gaussian conditioned on the prescribed rows. -/
def PrescribedRows.pointMass {n ell : ℕ} (R : PrescribedRows n ell) (side : Bool) (k : R.CoeffPoint side) : ℝ :=
  coefficientWeight n k.val/(∑' h : R.CoeffPoint side, coefficientWeight n h.val)

def twoFieldWeight {n ell : ℕ} (R T : PrescribedRows n ell)
    (k : R.CoeffPoint false × T.CoeffPoint true) : ℝ :=
  R.pointMass false k.1*T.pointMass true k.2

theorem PrescribedRows.point_event {n ell : ℕ} (R : PrescribedRows n ell) (side : Bool)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (E : ℤ×ℤ→Prop) [DecidablePred E] :
    HasSum (fun k : R.CoeffPoint side => if E k.val then R.pointMass side k else 0)
      (prescribedProbability R side E) := by
  let W := fun k : R.CoeffPoint side => coefficientWeight n k.val
  let Z := ∑' k,W k
  have zp : 0<Z := (R.weight_normalizer target side).1
  have ws : Summable W := by by_contra h; exact zp.ne' (tsum_eq_zero_of_not_summable h)
  have wp (k) : 0≤W k := mul_nonneg (exp_pos _).le (exp_pos _).le
  let V := fun k : R.CoeffPoint side => if E k.val then W k else 0
  have vs : Summable V := Summable.of_nonneg_of_le
    (fun k => by dsimp only [V]; split <;> first | exact wp k | rfl)
    (fun k => by dsimp only [V]; split <;> first | exact wp k | rfl) ws
  have h := vs.hasSum.div_const Z
  apply h.congr_fun
  intro k
  by_cases g : E k.val <;> simp [V,W,Z,PrescribedRows.pointMass,g]

theorem PrescribedRows.pointMass_nonneg {n ell : ℕ} (R : PrescribedRows n ell) (side : Bool) (k : R.CoeffPoint side) :
    0≤R.pointMass side k := by
  apply div_nonneg (mul_nonneg (exp_pos _).le (exp_pos _).le)
  exact tsum_nonneg (fun _ => mul_nonneg (exp_pos _).le (exp_pos _).le)

private theorem prob_true {n ell : ℕ} (R : PrescribedRows n ell) (side : Bool)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) :
    prescribedProbability R side (fun _ => True)=1 := by
  unfold prescribedProbability
  simp only [if_true,div_self (R.weight_normalizer target side).1.ne']

/-- The probability of a rectangular event under the independent left/right
coefficient laws is the product of its two actual prescribed probabilities. -/
theorem twoField_rectangle {n ell : ℕ} (R T : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (E F : ℤ×ℤ→Prop) [DecidablePred E] [DecidablePred F] :
    HasSum (fun k : R.CoeffPoint false × T.CoeffPoint true =>
      twoFieldWeight R T k*(if E k.1.val ∧ F k.2.val then 1 else 0))
      (prescribedProbability R false E*prescribedProbability T true F) := by
  have e := R.point_event false target E
  have f := T.point_event true target F
  have nonneg (Q : PrescribedRows n ell) (side : Bool) (P : ℤ×ℤ→Prop) [DecidablePred P] (k : Q.CoeffPoint side) :
      0≤ if P k.val then Q.pointMass side k else 0 := by split <;> first | exact PrescribedRows.pointMass_nonneg .. | rfl
  have h := e.mul f (e.summable.mul_of_nonneg f.summable (nonneg R false E) (nonneg T true F))
  apply h.congr_fun
  intro k
  by_cases l : E k.1.val <;> by_cases r : F k.2.val <;> simp [twoFieldWeight,l,r]

theorem twoField_total {n ell : ℕ} (R T : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) : HasSum (twoFieldWeight R T) 1 := by
  simpa only [true_and,if_true,mul_one,one_mul,prob_true R false target,prob_true T true target] using
    twoField_rectangle R T target (fun _ => True) (fun _ => True)

/-- A finite weighted score computed on one pair of left/right coefficient tuples. -/
def twoFieldScore {ι : Type*} (X : Finset ι) (w : ι→ℝ) (E F : ι→ℤ×ℤ→Prop) (u v : ℤ×ℤ) : ℝ :=
  ∑ i ∈ X, w i*(if E i u ∧ F i v then 1 else 0)

def twoFieldMean {ι : Type*} {n ell : ℕ} (R T : PrescribedRows n ell)
    (X : Finset ι) (w : ι→ℝ) (E F : ι→ℤ×ℤ→Prop) : ℝ :=
  ∑ i ∈ X,w i*(prescribedProbability R false (E i)*prescribedProbability T true (F i))

def twoFieldSecond {ι : Type*} {n ell : ℕ} (R T : PrescribedRows n ell)
    (X : Finset ι) (w : ι→ℝ) (E F : ι→ℤ×ℤ→Prop) : ℝ :=
  ∑ i ∈ X, ∑ j ∈ X,(w i*w j)*(prescribedProbability R false (fun k => E i k ∧ E j k)*
    prescribedProbability T true (fun k => F i k ∧ F j k))

theorem twoField_score_mean {ι : Type*} {n ell : ℕ} (R T : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (X : Finset ι) (w : ι→ℝ) (E F : ι→ℤ×ℤ→Prop) :
    HasSum (fun k : R.CoeffPoint false × T.CoeffPoint true => twoFieldWeight R T k*twoFieldScore X w E F k.1.val k.2.val)
      (twoFieldMean R T X w E F) := by
  have h := hasSum_sum (s:=X) (fun i _ => (twoField_rectangle R T target (E i) (F i)).mul_left (w i))
  apply h.congr_fun
  intro k
  rw [twoFieldScore,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => mul_left_comm ..)

theorem twoField_score_second {ι : Type*} {n ell : ℕ} (R T : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (X : Finset ι) (w : ι→ℝ) (E F : ι→ℤ×ℤ→Prop) :
    HasSum (fun k : R.CoeffPoint false × T.CoeffPoint true =>
      twoFieldWeight R T k*(twoFieldScore X w E F k.1.val k.2.val)^2) (twoFieldSecond R T X w E F) := by
  have h := hasSum_sum (s:=X) (fun i _ => hasSum_sum (s:=X) (fun j _ =>
    (twoField_rectangle R T target (fun k => E i k ∧ E j k) (fun k => F i k ∧ F j k)).mul_left (w i*w j)))
  apply h.congr_fun
  intro k
  rw [twoFieldScore,pow_two,Finset.sum_mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases ei : E i k.1.val <;> by_cases fi : F i k.2.val <;>
    by_cases ej : E j k.1.val <;> by_cases fj : F j k.2.val <;>
    simp [ei,fi,ej,fj,mul_comm,mul_assoc]

/-- Exact mean square about an arbitrary nominal cell or Gram-entry target. -/
theorem twoField_score_error {ι : Type*} {n ell : ℕ} (R T : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (X : Finset ι) (w : ι→ℝ) (E F : ι→ℤ×ℤ→Prop)
    (d : ℝ) : HasSum (fun k : R.CoeffPoint false × T.CoeffPoint true =>
      twoFieldWeight R T k*(twoFieldScore X w E F k.1.val k.2.val-d)^2)
      (twoFieldSecond R T X w E F-2*d*twoFieldMean R T X w E F+d^2) := by
  have h := ((twoField_score_second R T target X w E F).sub
    ((twoField_score_mean R T target X w E F).mul_left (2*d))).add ((twoField_total R T target).mul_right (d^2))
  simp only [one_mul] at h
  apply h.congr_fun
  intro k
  ring

/-- Exact bias and covariance decomposition of the score error. The ordered
sum retains signs from the weights and the covariance, including its diagonal. -/
theorem twoField_covariance_identity {ι : Type*} {n ell : ℕ} (R T : PrescribedRows n ell)
    (X : Finset ι) (w : ι→ℝ) (E F : ι→ℤ×ℤ→Prop) (d : ℝ) :
    let p := fun i => prescribedProbability R false (E i)*prescribedProbability T true (F i)
    let q := fun i j => prescribedProbability R false (fun k => E i k ∧ E j k)*
      prescribedProbability T true (fun k => F i k ∧ F j k)
    let μ := twoFieldMean R T X w E F
    twoFieldSecond R T X w E F-2*d*μ+d^2 =
      (μ-d)^2+∑ i ∈ X, ∑ j ∈ X,(w i*w j)*(q i j-p i*p j) := by
  intro p q μ
  have square : μ^2=∑ i ∈ X, ∑ j ∈ X, (w i*w j)*(p i*p j) := by
    change (∑ i ∈ X,w i*p i)^2=_
    rw [pow_two,Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  change (∑ i ∈ X, ∑ j ∈ X,(w i*w j)*q i j)-2*d*μ+d^2=_
  simp_rw [mul_sub,Finset.sum_sub_distrib]
  rw [←square]
  ring

private theorem outside_box_probability {n ell : ℕ} (R : PrescribedRows n ell)
    (side : Bool) (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) :
    let b := n.log2+1
    prescribedProbability R side (fun k => ¬inCoefficientBox n k) ≤
      1216*(Fixed.B b:ℝ)^2*exp (-π*((b:ℝ)^2)^2/2) := by
  intro b
  by_contra! lower
  obtain ⟨_,_,box,out⟩ := R.box_witness target side (fun k => ¬inCoefficientBox n k) lower
  exact out box

/-- A single boxed executable tuple satisfies every requested score tolerance
if the total normalized mean-square error and the two coefficient tails are
less than one. The input budget uses only single-field one- and two-event
probabilities, allowing different mark sets and signed weights for every entry. -/
theorem twoField_simultaneous_box {ι κ : Type*} {n ell : ℕ} (R T : PrescribedRows n ell)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1))) (J : Finset κ) (X : κ→Finset ι)
    (w : κ→ι→ℝ) (E F : κ→ι→ℤ×ℤ→Prop) (d δ : κ→ℝ) (dp : ∀ j∈J, 0<δ j) :
    let b := n.log2+1
    let budget := ∑ j ∈ J, (twoFieldSecond R T (X j) (w j) (E j) (F j)-
      2*d j*twoFieldMean R T (X j) (w j) (E j) (F j)+(d j)^2)/(δ j)^2
    budget+2432*(Fixed.B b:ℝ)^2*exp (-π*((b:ℝ)^2)^2/2)<1 →
    ∃ u v : ℤ×ℤ, R.compatible false u.1 u.2 ∧ T.compatible true v.1 v.2 ∧
      inCoefficientBox n u ∧ inCoefficientBox n v ∧
      ∀ j∈J, |twoFieldScore (X j) (w j) (E j) (F j) u v-d j|<δ j := by
  intro b budget small
  let C := R.CoeffPoint false × T.CoeffPoint true
  let W := twoFieldWeight R T
  let err (j : κ) (k : C) := twoFieldScore (X j) (w j) (E j) (F j) k.1.val k.2.val-d j
  let term (j : κ) (k : C) := (err j k)^2/(δ j)^2
  let cf (k : C) := ∑ j ∈ J,term j k
  let out := fun k : ℤ×ℤ => ¬inCoefficientBox n k
  let l (k : C) : ℝ := if out k.1.val then 1 else 0
  let r (k : C) : ℝ := if out k.2.val then 1 else 0
  let cost (k : C) := cf k+l k+r k
  let left := prescribedProbability R false out
  let right := prescribedProbability T true out
  have hs : HasSum (fun k : C => W k*cf k) budget := by
    have h := hasSum_sum (s:=J) (fun j _ =>
      (twoField_score_error R T target (X j) (w j) (E j) (F j) (d j)).div_const ((δ j)^2))
    apply h.congr_fun
    intro k
    dsimp only [cf]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => (mul_div_assoc ..).symm)
  have ls : HasSum (fun k : C => W k*l k) left := by
    simpa only [and_true,prob_true T true target,mul_one] using
      twoField_rectangle R T target out (fun _ => True)
  have rs : HasSum (fun k : C => W k*r k) right := by
    simpa only [true_and,prob_true R false target,one_mul] using
      twoField_rectangle R T target (fun _ => True) out
  have cs : HasSum (fun k : C => W k*cost k) (budget+left+right) := by
    apply ((hs.add ls).add rs).congr_fun
    intro k
    dsimp [cost]
    ring
  have pl : left≤1216*(Fixed.B b:ℝ)^2*exp (-π*((b:ℝ)^2)^2/2) := outside_box_probability R false target
  have pr : right≤1216*(Fixed.B b:ℝ)^2*exp (-π*((b:ℝ)^2)^2/2) := outside_box_probability T true target
  have cheap : ∃ k : C, cost k<1 := by
    by_contra! fail
    have tot := twoField_total R T target
    have cmp (k : C) : W k≤W k*cost k := by
      have wp : 0≤W k := mul_nonneg (PrescribedRows.pointMass_nonneg ..) (PrescribedRows.pointMass_nonneg ..)
      exact le_mul_of_one_le_right wp (fail k)
    have z := tot.summable.tsum_le_tsum cmp cs.summable
    rw [tot.tsum_eq,cs.tsum_eq] at z
    linarith only [small,pl,pr,z]
  obtain ⟨k,hk⟩ := cheap
  have leftnn : 0≤l k := by dsimp [l]; split <;> norm_num
  have rightnn : 0≤r k := by dsimp [r]; split <;> norm_num
  have terms (j : κ) : 0≤term j k := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have cfn : 0≤cf k := Finset.sum_nonneg (fun i _ => terms i)
  change cf k+l k+r k<1 at hk
  have lb : inCoefficientBox n k.1.val := by
    by_contra o
    have u : l k=1 := if_pos o
    linarith only [hk,u,cfn,rightnn]
  have rb : inCoefficientBox n k.2.val := by
    by_contra o
    have u : r k=1 := if_pos o
    linarith only [hk,u,cfn,leftnn]
  refine ⟨k.1.val,k.2.val,k.1.property,k.2.property,lb,rb,?_⟩
  intro j hj
  have localCost : term j k≤cf k := Finset.single_le_sum (fun i _ => terms i) hj
  have smallTerm : term j k<1 := by linarith only [localCost,hk,leftnn,rightnn]
  have bound := (div_lt_one (sq_pos_of_pos (dp j hj))).mp smallTerm
  change |err j k|<δ j
  apply (sq_lt_sq₀ (abs_nonneg _) (dp j hj).le).mp
  simpa only [sq_abs] using bound

end
end Cogentic.Construction

#print axioms Cogentic.Construction.twoField_score_error

#print axioms Cogentic.Construction.twoField_simultaneous_box
