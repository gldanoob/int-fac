import Cogentic.CellCountConcentration
import Cogentic.ModelRank
import Cogentic.TrueLogModel

namespace Cogentic.Construction
open Real Finset

/-- Perturb an affine log grid by at most ε in each entry, with one actual mark per cell. -/
private theorem energy_of_perturbation {ι : Type*} [Fintype ι] (old new : Option ι → ι → ℝ)
    (ε t : ℝ) (v : ι → ℝ)
    (grid : t^2 + ∑ j, (v j)^2 ≤ 3*∑ c, (t+∑ j, old c j*v j)^2)
    (near : ∀ c j, |new c j-old c j| ≤ ε)
    (small : 12*((Fintype.card ι:ℝ)+1)*(Fintype.card ι:ℝ)*ε^2 ≤ 1) :
    t^2 + ∑ j, (v j)^2 ≤ 12*∑ c, (t+∑ j, new c j*v j)^2 := by
  classical
  let err := fun c => ∑ j, (new c j-old c j)*v j
  have dif (c) : err c = (t+∑ j, new c j*v j)-(t+∑ j, old c j*v j) := by
    simp [err,sub_mul,Finset.sum_sub_distrib]
  have p (c) : (t+∑ j, old c j*v j)^2 ≤ 2*(t+∑ j, new c j*v j)^2+2*(err c)^2 := by
    rw [dif]; nlinarith [sq_nonneg ((t+∑ j, new c j*v j)+((t+∑ j, new c j*v j)-(t+∑ j, old c j*v j)))]
  have total := Finset.sum_le_sum (s:=univ) (fun c _=>p c)
  rw [sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum] at total
  have comparison := weighted_log_score_error (fun _ : Option ι => 1) old new v ε (fun _=>zero_le_one) near
  simp only [one_mul,Finset.sum_const,Finset.card_univ,Fintype.card_option,nsmul_eq_mul,
    mul_one,Nat.cast_add,Nat.cast_one] at comparison
  change (∑ c, (err c)^2) ≤ _ at comparison
  have budget := mul_le_mul_of_nonneg_right small (Finset.sum_nonneg (s:=univ) (fun j _=>sq_nonneg (v j)))
  nlinarith only [grid,total,comparison,budget,sq_nonneg t]

private theorem fixed_error_small {b : ℕ} (hd : 1 ≤ Fixed.d b) :
    12*((2*Fixed.d b:ℕ)+1:ℝ)*(2*Fixed.d b:ℕ)*(2*(1/2:ℝ)^(92*Fixed.h b))^2 ≤ 1 := by
  let d := Fixed.d b
  let h := Fixed.h b
  have dh : d≤h := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have big : 16*(2*d+1) ≤ 2^(92*h) := (show 16*(2*d+1)≤92*h by change 1≤d at hd; omega).trans
    (Nat.lt_two_pow_self.le)
  have num : 16*(2*(d:ℝ)+1) ≤ (2:ℝ)^(92*h) := by exact_mod_cast big
  have numpos : 0 < (2:ℝ)^(92*h) := by positivity
  have a : 0≤2*(d:ℝ) := by positivity
  have sq := mul_le_mul num num (by positivity) numpos.le
  push_cast
  change 12*(2*(d:ℝ)+1)*(2*(d:ℝ))*(2*(1/2:ℝ)^(92*h))^2 ≤ 1
  rw [one_div_pow]
  field_simp
  nlinarith [sq, sq_nonneg (d:ℝ)]

/-- On any actual tuple retaining a mark in every cell, the intercept and all
2d *unprojected*, true logarithm rows have positive energy on those marks. -/
theorem retained_arch_energy {n ell u v w z : ℕ} (hn : 2≤n)
    (big : 130000≤Fixed.d (n.log2+1)) :
    let b := n.log2+1
    let s := TryPair.fixedInput n ell (construct n ell u v w z)
    ∀ {rel : Marking.Relations}, Marking.stageOne s=some rel →
    ∀ keep : ℕ → Prop, (∀ cell, ∃ a ∈ constructorCellMarks n ell cell, a ∈ rel.marks ∧ keep a) →
    ∃ mark : Option (Fin (2*Fixed.d b)) → Fin rel.marks.length,
      (∀ c, keep (rel.marks.get (mark c))) ∧ ∀ (x : Bool → Fin s.degree → ℝ),
        (∀ side j, x side j ∈ Set.Icc ((RootLogs.bracket s side j).left:ℝ) ((RootLogs.bracket s side j).right:ℝ)) →
      ∀ (t : ℝ) (v : Fin (2*s.degree) → ℝ),
        t^2+∑ j, (v j)^2 ≤ 12*∑ c, (t+∑ j, log |(rel.marks.get (mark c):ℝ)/s.A-
          x (gridPlace j).1 (gridPlace j).2| * v j)^2 := by
  classical
  intro b s rel marked keep present
  let d := Fixed.d b
  let cell : Option (Fin (2*d)) → Option (Bool × Fin d) := Option.map gridPlace
  have existsIndex (c : Option (Fin (2*d))) :
      ∃ i : Fin rel.marks.length, rel.marks.get i ∈ constructorCellMarks n ell (cell c) ∧ keep (rel.marks.get i) := by
    obtain ⟨a,inCell,inList,allowed⟩ := present (cell c)
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp inList
    exact ⟨i,hi ▸ inCell,hi ▸ allowed⟩
  choose idx idxCell using existsIndex
  refine ⟨idx,fun c=>(idxCell c).2,?_⟩
  intro x roots t coeff
  let point := fun c => (rel.marks.get (idx c):ℝ)/s.A
  let width := (Fixed.invWidth b:ℝ)⁻¹
  have dp : 1≤d := by change 130000≤d at big; omega
  have location (c) := (fixed_grid_interval_bounds dp (cell c) _ (mem_filter.mp (idxCell c).1).1).1
  have actual (c) : (gridCellLeft b (cell c):ℝ) ≤ point c ∧
      point c ≤ (gridCellLeft b (cell c):ℝ)+width := by
    obtain ⟨lower,upper⟩ := location c
    change (gridCellLeft b (cell c):ℝ) ≤ (rel.marks.get (idx c):ℝ)/(Fixed.A b:ℝ) ∧
      (rel.marks.get (idx c):ℝ)/(Fixed.A b:ℝ) ≤ (gridCellLeft b (cell c):ℝ)+(Fixed.invWidth b:ℝ)⁻¹
    have lo := (Rat.cast_le (K:=ℝ)).mpr lower
    have hi := (Rat.cast_le (K:=ℝ)).mpr upper
    push_cast at lo hi
    exact ⟨lo,hi⟩
  have baseline : 3/4≤point none ∧ point none≤1 := by
    have low := (actual none).1
    have atMost := (fixed_grid_interval_bounds dp (cell none) _ (mem_filter.mp (idxCell none).1).1).2.2.1
    have pos : (0:ℝ)<s.A := by change 0<(Fixed.A b:ℝ); dsimp [Fixed.A]; positivity
    exact ⟨by simpa [cell,gridCellLeft] using low, (div_le_one pos).mpr (by exact_mod_cast atMost)⟩
  have inside (j) : nominalCenter d j+width ≤ point (some j) ∧ point (some j) ≤ nominalCenter d j+2*width := by
    have h := actual (some j)
    rw [gridPlace_center]
    rcases p : gridPlace j with ⟨side,i⟩
    simp [cell,gridCellLeft,p] at h
    exact ⟨h.1,by dsimp [width] at *; linarith [h.2]⟩
  let old := fun c j => log |point c - nominalCenter d j|
  let new := fun c j => log |point c - x (gridPlace j).1 (gridPlace j).2|
  let ε := 2*(1/2:ℝ)^(92*Fixed.h b)
  apply energy_of_perturbation old new ε t coeff
  · have energy := fixed_nominal_grid_energy big (β:=fun _=>Unit)
      (fun c _=>point c) (fun _ _=>1) (fun _=>baseline) (fun j _=>inside j)
      (by simp) (by simp) t coeff
    simpa [old,Fintype.sum_option] using energy
  · intro c j
    rw [show old c j = log |point c - (center d (gridPlace j).1 (gridPlace j).2.val:ℝ)| by
      simp only [old,gridPlace_center]]
    exact retained_true_log_error hn (by omega) marked _ (List.get_mem ..) _ _ _ (roots _ _)
  · simpa [d,ε] using fixed_error_small dp

/-- For each surviving input and target, this is energy on the actual retained
marks of one positive search tuple, with the true root of each polynomial. -/
theorem exists_retained_arch_rank (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ ell∈dyadicTargets (Fixed.beta (n.log2+1)), ¬n.Prime →
    presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1
    ∃ (u v w z : ℕ) (rel : Marking.Relations),
      (1≤u ∧ u≤2*b^2*Fixed.U b*Fixed.A b) ∧ (1≤v ∧ v≤2*b^2*Fixed.U b) ∧
      (1≤w ∧ w≤2*b^2*Fixed.U b*Fixed.A b) ∧ (1≤z ∧ z≤2*b^2*Fixed.U b) ∧
      let s := TryPair.fixedInput n ell (construct n ell u v w z)
      Marking.stageOne s = some rel ∧
      7997*Fixed.h b+2 ≤ (rel.matrix.map (Int.castRingHom ℚ)).rank ∧
      2*Fixed.d b ≤ Module.finrank ℚ (LinearMap.ker (rel.matrix.map (Int.castRingHom ℚ)).mulVecLin) ∧
      ∃ (x : Bool → Fin s.degree → ℝ) (mark : Option (Fin (2*s.degree)) → Fin rel.marks.length),
        (∀ side j, x side j ∈ Set.Icc ((RootLogs.bracket s side j).left:ℝ) ((RootLogs.bracket s side j).right:ℝ) ∧
          RootLogs.normalized s.A (s.coeffs side) (x side j)=0) ∧
        ∀ (t : ℝ) (v : Fin (2*s.degree) → ℝ), t^2+∑ j, (v j)^2 ≤
          12*∑ c, (t+∑ j, log |(rel.marks.get (mark c):ℝ)/s.A-x (gridPlace j).1 (gridPlace j).2| * v j)^2 := by
  obtain ⟨n₁,supply⟩ := unrestricted_all_cells_rank line
  obtain ⟨b₀,grow⟩ := Fixed.degree_grows 130000
  refine ⟨max n₁ (max 2 (2^b₀)),?_⟩
  intro n large ell target composite sieved b
  obtain ⟨nlarge,other⟩ := max_le_iff.mp large
  obtain ⟨hn,pow⟩ := max_le_iff.mp other
  have bit := (Nat.le_log2 (show n≠0 by omega)).mpr pow
  have big : 130000≤Fixed.d b := grow _ (by dsimp [b]; omega)
  obtain ⟨u,v,w,z,rel,hu,hv,hw,hz,stage,counts,rnk,nul⟩ := supply n nlarge ell target composite sieved
  have pop (cell) : ∃ a ∈ constructorCellMarks n ell cell, a ∈ rel.marks ∧ True := by
    have positive : 0<(cellMarkCount b:ℝ) := by dsimp [cellMarkCount]; positivity
    have h := counts cell
    by_contra! empty
    have eq : ((constructorCellMarks n ell cell).filter (·∈rel.marks))=∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr (fun a ha=>empty a (mem_filter.mp ha).1 (mem_filter.mp ha).2)
    rw [eq] at h
    simp at h
    linarith
  obtain ⟨mark,_,energy⟩ := retained_arch_energy hn big stage (fun _=>True) pop
  obtain ⟨_,x,_,roots,_,_⟩ := constructed_mark_logs hn (show 10004≤Fixed.d b by omega) target ⟨hu.2,hv.2,hw.2,hz.2⟩ stage
  exact ⟨u,v,w,z,rel,hu,hv,hw,hz,stage,rnk,nul,x,mark,
    fun side j=>⟨(roots side j).2.1,(roots side j).2.2.1⟩,energy x (fun side j=>(roots side j).2.1)⟩

end Cogentic.Construction

#print axioms Cogentic.Construction.exists_retained_arch_rank
