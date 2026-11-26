import Cogentic.RawLogProfiles
import Cogentic.RawGridEnergy
import Cogentic.RawGramEntries
import Cogentic.MomentRows

namespace Cogentic.Construction
open Finset Real
noncomputable section

abbrev GridPosition (b : ℕ) := Option (Fin (2*Fixed.d b)) × Fin (cellMarkCount b)

/-- Enumerating physical cells by field and root gives exactly the normalized
raw-position average used for the reference entries. -/
theorem grid_position_average {b : ℕ} (f : Option (Bool×Fin (Fixed.d b)) → ℕ → ℝ) :
    (∑ a : GridPosition b,(cellMarkCount b:ℝ)⁻¹/(2*(Fixed.d b:ℝ)+1)*f (a.1.map gridPlace) a.2.val) =
      (∑ c : Option (Bool×Fin (Fixed.d b)),∑ j∈range (cellMarkCount b),f c j)/
        ((Fintype.card (Option (Bool×Fin (Fixed.d b))):ℝ)*cellMarkCount b) := by
  let e := (interleavePlaces (Fixed.d b)).symm.trans (Equiv.boolProdEquivSum (Fin (Fixed.d b))).symm
  have maps (c : Option (Fin (2*Fixed.d b))) : c.map gridPlace=e.optionCongr c := by cases c <;> rfl
  rw [Fintype.sum_prod_type]
  simp only [maps,←mul_sum,Fin.sum_univ_eq_sum_range]
  rw [e.optionCongr.sum_comp (fun c=>∑ j∈range (cellMarkCount b),f c j)]
  simp only [Fintype.card_option,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,Nat.cast_add,
    Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,div_eq_mul_inv,mul_inv_rev]
  ring

def gridLogColumn {b : ℕ} (a : GridPosition b) : Option (Fin (2*Fixed.d b)) → ℝ
  | none => 1
  | some i => log |rawGridPoint b a.1 a.2-nominalCenter (Fixed.d b) i|

/-- Unnormalized miss contribution. The factor `miss` is the density of marks
outside the target residue classes. Both the empirical numerator and denominator
are taken before removing these marks from the sample. -/
def missGridGram {b : ℕ} {I : Type*} (miss : ℝ) (m : GridPosition b → I → ℝ)
    (R : GridPosition b → I → I → ℝ) : Matrix (Option (Fin (2*Fixed.d b)) ⊕ I) (Option (Fin (2*Fixed.d b)) ⊕ I) ℝ :=
  fun i j => miss*∑ a,(cellMarkCount b:ℝ)⁻¹/(2*(Fixed.d b:ℝ)+1)*missMomentEntry (gridLogColumn a) (m a) (R a) i j

theorem grid_log_column_eq_nominal {b : ℕ} (a : GridPosition b) (i : Option (Fin (2*Fixed.d b))) :
    gridLogColumn a i = nominalLogFactor b (i.map gridPlace) (firstCellMark b (a.1.map gridPlace)+a.2.val) := by
  cases i with
  | none => rfl
  | some i =>
    rw [gridLogColumn,gridPlace_center]
    rcases eq : gridPlace i with ⟨side,j⟩
    simp only [Option.map_some,eq,nominalLogFactor,rawGridPoint]

/-- The physical target-miss center for two protected rows is their matrix entry
in the spatially interleaved raw reference. -/
theorem miss_grid_log_entry {b : ℕ} {I : Type*} (miss : ℝ) (m : GridPosition b → I → ℝ)
    (R : GridPosition b → I → I → ℝ) (i k : Option (Fin (2*Fixed.d b))) :
    let f := fun a=>nominalLogFactor b (i.map gridPlace) a*nominalLogFactor b (k.map gridPlace) a
    let count := (Fintype.card (Option (Bool×Fin (Fixed.d b))):ℝ)*cellMarkCount b
    missGridGram miss m R (.inl i) (.inl k) =
      miss*((∑ c : Option (Bool×Fin (Fixed.d b)),∑ j∈range (cellMarkCount b),f (firstCellMark b c+j))/count) := by
  intro f count
  simp only [missGridGram,missMomentEntry,grid_log_column_eq_nominal]
  exact congrArg (fun u : ℝ=>miss*u) (grid_position_average (fun c j=>f (firstCellMark b c+j)))

private theorem quad_sum {A I : Type*} [Fintype A] [Fintype I] (f : A → I → I → ℝ)
    (p : ℝ) (v : I → ℝ) : (∑ i,∑ j,v i*(∑ a,p*f a i j)*v j)=∑ a,p*(∑ i,∑ j,v i*f a i j*v j) := by
  simp only [mul_sum,sum_mul]
  rw [sum_comm]
  conv_lhs => enter [2,j];rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl;intro a _;rw [sum_comm];apply sum_congr rfl;intro i _;apply sum_congr rfl;intro j _;ring

/-- The nominal reference at all physical positions is coercive on every
vector satisfying the two ordinary field-norm equations. `margin` is the
pointwise miss-branch bound, so the statement applies after any row deletion. -/
theorem miss_grid_gram_energy {b : ℕ} (big : 130000≤Fixed.d b) {I : Type*} [Fintype I]
    (miss : ℝ) (hp : 1/2≤ miss) (m : GridPosition b → I → ℝ) (R : GridPosition b → I → I → ℝ)
    (v : Option (Fin (2*Fixed.d b)) ⊕ I → ℝ) :
    let F := ∑ i,(v (.inr i))^2
    let g := fun a => ∑ i,gridLogColumn (b:=b) a i*v (.inl i)
    let s := fun a => ∑ i,m a i*v (.inr i)
    let Q := fun a => (g a+s a)^2+((∑ i,∑ j,v (.inr i)*R a i j*v (.inr j))-(s a)^2)
    (∀ a,(s a)^2≤120000*(Fixed.d b:ℝ)*F ∧ (g a+s a)^2+(13/16)*F≤Q a) →
    (∑ i,(v i)^2)≤2*(768*(10000*(Fixed.d b:ℝ))*(2*(Fixed.d b:ℝ)+1))*(∑ i,∑ j,v i*missGridGram miss m R i j*v j) := by
  intro F g s Q margin
  let p := (cellMarkCount b:ℝ)⁻¹/(2*(Fixed.d b:ℝ)+1)
  let C := 768*(10000*(Fixed.d b:ℝ))*(2*(Fixed.d b:ℝ)+1)
  have fp : 0≤F := sum_nonneg fun _ _=>sq_nonneg _
  have gp (a : GridPosition b) : g a=v (.inl none)+∑ j,log |rawGridPoint b a.1 a.2-nominalCenter (Fixed.d b) j| *v (.inl (some j)) := by simp [g, Fintype.sum_option,gridLogColumn]
  have grid := raw_grid_average_energy big (v (.inl none)) (fun i=>v (.inl (some i))) s Q F fp
    (fun a=>by simpa only [←gp] using margin a)
  change F+_≤C*(∑ a,p*Q a) at grid
  have entry (a : GridPosition b) := miss_moment_quadratic (gridLogColumn a) (m a) (R a) v
  change ∀ a, _=Q a at entry
  have quad : (∑ i,∑ j,v i*missGridGram miss m R i j*v j)=miss*(∑ a,p*Q a) := by
    change (∑ i,∑ j,v i*(miss*(∑ a,p*missMomentEntry (gridLogColumn a) (m a) (R a) i j))*v j)=_
    simp_rw [mul_left_comm (v _) miss, mul_assoc miss, ←mul_sum _ _ miss]
    rw [quad_sum (fun a i j=>missMomentEntry (gridLogColumn a) (m a) (R a) i j) p v];simp only [entry]
  have xn : 0≤C*∑ a,p*Q a := (add_nonneg fp (add_nonneg (sq_nonneg _) (sum_nonneg fun _ _=>sq_nonneg _))).trans grid
  have double := mul_le_mul_of_nonneg_right hp xn
  rw [quad,Fintype.sum_sum_type,Fintype.sum_option]
  change _+F≤2*C*(miss*_)
  linarith only [grid,double]

/-- A diagonal threshold and a squared Frobenius budget for the remaining entries
pay for all surviving ordinary/log directions simultaneously. Deleting columns
costs their actual squared scores. This permits a separate sparse peeling bound. -/
theorem gram_survives_deletion {I X : Type*} [Fintype I] [DecidableEq I] [DecidableEq X]
    (model : Matrix I I ℝ) (Z : X → I → ℝ) (p : X → ℝ) (all keep : Finset X) (sub : keep⊆all)
    (v : I → ℝ) (C δ : ℝ) (cp : 0<C) (dp : 0≤δ) (tiny : 4*C*δ≤1) :
    let mass := ∑ i,(v i)^2
    let err := fun i j => model i j-∑ a∈all,p a*Z a i*Z a j
    let off := fun i j => if i=j then 0 else err i j
    mass≤C*(∑ i,∑ j,v i*model i j*v j) →
    (∀ i, |err i i|≤δ) → (∑ i,∑ j,(off i j)^2)≤δ^2 →
    (∑ a∈all\keep,p a*(∑ i,Z a i*v i)^2)≤δ*mass →
    mass≤4*C*(∑ a∈keep,p a*(∑ i,Z a i*v i)^2) := by
  classical
  intro mass err off coercive diag frob lost
  have sign : 0≤ mass := sum_nonneg fun _ _=>sq_nonneg _
  have diagBound : (∑ i,err i i*(v i)^2)≤δ*mass := by
    rw [show δ*mass=∑ i,δ*(v i)^2 by simp only [mass,mul_sum]]
    exact sum_le_sum fun i _=>mul_le_mul_of_nonneg_right ((le_abs_self _).trans (diag i)) (sq_nonneg _)
  have offBound := (le_abs_self _).trans (gram_frobenius_error off v δ dp frob)
  have decomposition (i j : I) : model i j=(if i=j then err i i else 0)+off i j+(∑ a∈all,p a*Z a i*Z a j) := by
    by_cases eq : i=j <;> simp [off,err,eq]
  have diagQ (i : I) : (∑ j,v i*(if i=j then err i i else 0)*v j)=err i i*(v i)^2 := by
    simp only [mul_ite,mul_zero,ite_mul,zero_mul,sum_ite_eq,mem_univ,if_true];ring
  have physical : (∑ i,∑ j,v i*(∑ a∈all,p a*Z a i*Z a j)*v j)=∑ a∈all,p a*(∑ i,Z a i*v i)^2 := by
    simp only [sq,mul_sum,sum_mul]
    rw [sum_comm];conv_lhs => enter [2,j];rw [sum_comm]
    rw [sum_comm];apply sum_congr rfl;intro a _;rw [sum_comm];apply sum_congr rfl;intro i _;apply sum_congr rfl;intro j _;ring
  simp_rw [decomposition,mul_add,add_mul,sum_add_distrib,diagQ,physical] at coercive
  have split := sum_sdiff (f:=fun a=>p a*(∑ i,Z a i*v i)^2) sub
  have charge := mul_le_mul_of_nonneg_right tiny sign
  change _≤δ*mass at offBound
  rw [←split] at coercive
  have estimates := mul_le_mul_of_nonneg_left (add_le_add (add_le_add diagBound offBound) lost) cp.le
  nlinarith only [estimates,coercive,split,charge]

/-- On retained marks the perturbation of all bracket roots costs only the
number of log coordinates. Ordinary rows and the intercept cancel in the
score difference, regardless of how many ordinary rows survive. -/
theorem retained_true_score_positive {n ell a c e f : ℕ} (hn : 2≤n)
    (big : 10004≤Fixed.d (n.log2+1)) :
    let b := n.log2+1; let d := Fixed.d b
    let input := TryPair.fixedInput n ell (construct n ell a c e f)
    ∀ {rel}, Marking.stageOne input=some rel → ∀ Y : Finset ℕ, Y⊆rel.marks.toFinset →
    ∀ (x : Bool→Fin d→ℝ),
    (∀ k i, x k i∈Set.Icc ((RootLogs.bracket input k i).left:ℝ) ((RootLogs.bracket input k i).right:ℝ)) →
    ∀ (w shift : ℕ→ℝ) (g : Fin (2*d)→ℝ), (∀ y∈Y,0≤w y) → (∑ y∈Y,w y)≤1 →
    let nominal := fun y : ℕ=>shift y+∑ k,g k*log |(y:ℝ)/input.A-nominalCenter d k|
    let actual := fun y : ℕ=>shift y+∑ k,g k*log |(y:ℝ)/input.A-x (gridPlace k).1 (gridPlace k).2|
    let C := 8*(768*(10000*(d:ℝ))*(2*(d:ℝ)+1))
    ∀ E : ℝ, 0<E → (∑ k,(g k)^2)≤E → E≤C*(∑ y∈Y,w y*(nominal y)^2) →
      0<∑ y∈Y,w y*(actual y)^2 := by
  intro b d input rel stage Y sub x bracket w shift g nn mass nominal actual C E pos arch lower
  let ε := 2*(1/2:ℝ)^(92*Fixed.h b)
  let old := fun (y : Y) (k : Fin (2*d))=>log |(y.val:ℝ)/input.A-nominalCenter d k|
  let new := fun (y : Y) (k : Fin (2*d))=>log |(y.val:ℝ)/input.A-x (gridPlace k).1 (gridPlace k).2|
  have localErr (y : Y) (k : Fin (2*d)) : |new y k-old y k|≤ε := by
    dsimp only [old,new];rw [gridPlace_center]
    exact retained_true_log_error hn big stage y (List.mem_toFinset.mp (sub y.prop)) _ _ _ (bracket _ _)
  have comp := weighted_log_score_error (fun y:Y=>w y) old new g ε (fun y=>nn y y.prop) localErr
  have difference (y : Y) : actual y-nominal y=∑ k,(new y k-old y k)*g k := by
    simp only [actual,nominal,old,new,sub_mul,sum_sub_distrib,mul_comm (g _)]
    ring
  have mp : (∑ y:Y,w y)≤1 := (sum_coe_sort Y w).trans_le mass
  have dr : 1≤d := by change 10004≤d at big;omega
  have dh : d≤Fixed.h b := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have powbd : (2*d+1)^3*2^30 ≤ 2^(92*Fixed.h b) := by
    have l : 2*d+1≤2^(2*d+1) := Nat.lt_two_pow_self.le
    exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left l 3)).trans (by
      rw [←Nat.pow_mul,←Nat.pow_add];apply Nat.pow_le_pow_right (by decide);omega)
  have bound : 4*C*(2*(d:ℝ))*ε^2 ≤ 1 := by
    have sq : (2*(d:ℝ)+1)^3*2^30 ≤ (2:ℝ)^(92*Fixed.h b) := by exact_mod_cast powbd
    have ratio : (1:ℝ)≤(2:ℝ)^(92*Fixed.h b) := one_le_pow₀ (by norm_num)
    dsimp only [C,ε];rw [one_div_pow];field_simp
    nlinarith only [sq,mul_le_mul_of_nonneg_left ratio (show 0≤(2:ℝ)^(92*Fixed.h b) by positivity),
      sq_nonneg (d:ℝ),Nat.cast_nonneg (α:=ℝ) d,mul_nonneg (sq_nonneg (d:ℝ)) (Nat.cast_nonneg d)]
  have Cp : 0<C := by
    have : (0:ℝ)<d := Nat.cast_pos.mpr dr
    dsimp only [C];positivity
  have en := mul_le_mul_of_nonneg_right bound (sum_nonneg (s:=univ) (fun k _=>sq_nonneg (g k)))
  simp only [Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] at comp
  have cr := mul_le_mul_of_nonneg_left (comp.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right mp (by positivity)) (sum_nonneg (fun _ _=>sq_nonneg _)))) (show 0≤4*C by positivity)
  have diff : 4*C*(∑ y:Y,w y*(actual y-nominal y)^2)≤E := by simp_rw [difference];nlinarith only [cr,en,arch]
  have norm : E≤C*∑ y:Y,w y*(nominal y)^2 := by rw [sum_coe_sort Y (fun y=>w y*(nominal y)^2)];exact lower
  have h := positive_true_scores_of_nominal (fun y:Y=>w y) (fun y:Y=>nominal y) (fun y:Y=>actual y)
    C E pos Cp (fun y=>nn y y.prop) norm (by simpa only [show ∀ y, (nominal y-actual y)^2=(actual y-nominal y)^2 by intro y;ring] using diff)
  exact h.2.trans_eq (sum_coe_sort Y (fun y=>w y*(actual y)^2))

end
end Cogentic.Construction

#print axioms Cogentic.Construction.miss_grid_gram_energy
#print axioms Cogentic.Construction.gram_survives_deletion
#print axioms Cogentic.Construction.retained_true_score_positive
