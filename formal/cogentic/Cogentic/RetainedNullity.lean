import Cogentic.ColumnSeparation
import Cogentic.RetainedColumnRank
import Cogentic.ExponentBounds
import Cogentic.MarkIntervals
import Cogentic.RetainedFamilies

namespace Cogentic.Construction
open Finset

/-- The rational nullspace of the actual matrix, including the intercept
row, has at least two directions per degree once the cell count is met. -/
theorem kernel_dim_of_cell_count {n ell u v w z q : ℕ} (qp : 0<q)
    (cap : q≤(Fixed.B (n.log2+1))^4) {rel : Marking.Relations}
    (stage : Marking.stageOne (TryPair.fixedInput n ell (construct n ell u v w z))=some rel) :
    let b := n.log2+1
    (cellMarkCount b:ℝ)/(32*q*(Fixed.B b:ℝ)^2) ≤ rel.marks.length →
    2*Fixed.d b ≤ Module.finrank ℚ (LinearMap.ker (rel.matrix.map (Int.castRingHom ℚ)).mulVecLin) := by
  intro b pop
  let d := Fixed.d b; let B := Fixed.B b; let h := Fixed.h b
  have dp : 0<d := Fixed.degree_pos (Nat.succ_pos _)
  have hp : 0<h := Nat.mul_pos dp (Nat.succ_pos _)
  have hbig : d ≤ h := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have dB : d≤B := (Nat.lt_two_pow_self (n:=d)).le.trans (Nat.pow_le_pow_right (by decide) (by change d≤1000*h; omega))
  have bp : 1≤B := Nat.one_le_two_pow
  have count : (32*q*B^2)*((2*d*B+1)+2*d) ≤ cellMarkCount b := calc
    _ ≤ (32*B^4*B^2)*((2*B*B+1)+2*B) := by gcongr
    _ ≤ 2^8*B^8 := by
      have sq := Nat.mul_le_mul_left B bp
      have one : 1≤B^2 := Nat.one_le_pow _ _ bp
      calc
        _ ≤ (32*B^4*B^2)*(8*B^2) := Nat.mul_le_mul_left _ (by nlinarith only [sq,one])
        _ = _ := by ring
    _ ≤ _ := by
      change 2^8*(2^(1000*h))^8 ≤ 2^(9997*h)
      rw [←pow_mul,←pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)
  have cnt := (le_div_iff₀ (by positivity : (0:ℝ)<32*q*(B:ℝ)^2)).mpr
    (show (((2*d*B+1)+2*d:ℕ):ℝ)*(32*q*(B:ℝ)^2) ≤ cellMarkCount b by
      exact_mod_cast (Nat.mul_comm .. ▸ count : ((2*d*B+1)+2*d)*(32*q*B^2) ≤ cellMarkCount b))
  have cols : (2*d*B+1)+2*d≤rel.marks.length := by exact_mod_cast cnt.trans pop
  have rows : rel.rows.length≤2*d*B := retained_root_row_cap stage
  let L := (rel.matrix.map (Int.castRingHom ℚ)).mulVecLin
  have rank := L.finrank_range_add_finrank_ker
  have upper := (LinearMap.range L).finrank_le
  simp only [Module.finrank_fin_fun] at rank upper
  change 2*d ≤ Module.finrank ℚ (LinearMap.ker L)
  omega

/-- For a positive density of distinct binary columns, the class modulus
costs its binary logarithm in the lower bound on rational incidence rank. -/
theorem incidence_rank_of_cell_count {b q : ℕ} (qp : 0<q) (rel : Marking.Relations)
    (inj : Function.Injective (rel.matrix.map (Int.castRingHom ℚ)).col)
    (many : (cellMarkCount b:ℝ)/(32*q*(Fixed.B b:ℝ)^2)≤rel.marks.length) :
    7997*Fixed.h b ≤ (rel.matrix.map (Int.castRingHom ℚ)).rank + q.log2 + 5 := by
  let r := (rel.matrix.map (Int.castRingHom ℚ)).rank
  let h := Fixed.h b
  have bp : 0<Fixed.B b := Nat.pow_pos (by decide)
  have pop := (div_le_iff₀ (by positivity : 0<32*(q:ℝ)*(Fixed.B b:ℝ)^2)).mp many
  have upper : cellMarkCount b ≤ rel.marks.length*(32*q*(Fixed.B b)^2) := by exact_mod_cast pop
  have bin : rel.marks.length ≤ 2^r := retained_rank_of_column_separation rel inj
  have lo : 2^(9997*h) < 2^(r+5+(q.log2+1)+2000*h) := calc
    _ ≤ 2^r*(32*q*(Fixed.B b)^2) := upper.trans (Nat.mul_le_mul_right _ bin)
    _ < 2^r*(32*2^(q.log2+1)*(Fixed.B b)^2) := by gcongr; exact Nat.lt_log2_self
    _ = _ := by
      change 2^r*(2^5*2^(q.log2+1)*(2^(1000*h))^2)=_
      rw [←pow_mul]; simp only [←pow_add]; congr 1; omega
  have log := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp lo
  change 7997*h≤r+q.log2+5; omega

/-- In every admissible class of any one cell, an actual positive search
tuple retains a large set of distinct marks and its rational matrix has
a nullspace of dimension at least twice the construction degree. -/
theorem cell_retained_kernel (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ ell ∈ dyadicTargets (Fixed.beta (n.log2+1)),
    ¬n.Prime → presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none →
    let b := n.log2+1
    ∀ (cell : Option (Bool × Fin (Fixed.d b))) (q r : ℕ), 0<q → q≤(Fixed.B b)^4 →
    (∀ p∈(markModulus n ell).primeFactors, p∣q → ¬r ≡ Fixed.rootBase n [MOD p]) →
    let lo := firstCellMark b cell; let M := cellMarkCount b
    ∃ (u v w z : ℕ) (rel : Marking.Relations) (Y : Finset ℕ),
      (1≤u ∧ u≤2*b^2*Fixed.U b*Fixed.A b) ∧ (1≤v ∧ v≤2*b^2*Fixed.U b) ∧
      (1≤w ∧ w≤2*b^2*Fixed.U b*Fixed.A b) ∧ (1≤z ∧ z≤2*b^2*Fixed.U b) ∧
      Marking.stageOne (TryPair.fixedInput n ell (construct n ell u v w z))=some rel ∧
      (M:ℝ)/(32*q*(Fixed.B b:ℝ)^2) ≤ Y.card ∧
      (∀ a∈Y, a∈Ico lo (lo+M) ∧ a ≡ r [MOD q] ∧ a∈rel.marks) ∧
      2*Fixed.d b ≤ Module.finrank ℚ (LinearMap.ker (rel.matrix.map (Int.castRingHom ℚ)).mulVecLin) ∧
      7997*Fixed.h b ≤ (rel.matrix.map (Int.castRingHom ℚ)).rank+q.log2+5 := by
  classical
  obtain ⟨n₁,grid⟩ := grid_cells_have_marks line
  obtain ⟨b₁,many⟩ := many_retained_at_marks line
  obtain ⟨b₂,grows⟩ := Fixed.degree_grows 10004
  refine ⟨max n₁ (2^(max b₁ b₂+1)),?_⟩
  intro n hn ell target comp absent b cell q r qp qc eligible lo M
  obtain ⟨first,pw⟩ := max_le_iff.mp hn
  have np := (Nat.pow_pos (by decide : 0<2)).trans_le pw
  have hn2 : 2≤n := (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_add_left 1 (max b₁ b₂))).trans pw
  have logs := (Nat.le_log2 np.ne').mpr pw
  have bits : max b₁ b₂≤b := by dsimp only [b]; omega
  obtain ⟨big,two⟩ := max_le_iff.mp bits
  let X := ((Ico lo (lo+M)).filter (fun a => a ≡ r [MOD q])).filter
    (fun a => a∈(construct n ell 0 0 0 0).marks)
  have cnt := grid n first ell target comp absent q r 0 0 0 0 cell qp qc eligible
  change (M:ℝ)/q/8 ≤ X.card at cnt
  have mp : 0<M := Nat.pow_pos (by decide)
  have pos := (show 0<(M:ℝ)/q/8 by positivity).trans_le cnt
  have non := card_pos.mp (show 0<X.card by exact_mod_cast pos)
  let R : PrescribedRows n ell := ⟨∅,fun _ => 0,empty_subset _,by simp,by simp,by simp⟩
  have forced (a : ℕ) : (R.prefactor a false).Coprime (R.prefactor a true) := by
    exact (R.prefactors_coprime_iff R ((by decide : 3≤10004).trans (grows b two)) target a).mpr (by simp [PrescribedRows.hit,R])
  obtain ⟨u,v,w,z,Y,rel,sub,count,ub,vb,wb,zb,_,_,up,vp,wp,zp,stage,mem⟩ :=
    many R R big hn2 comp target absent X non (fun _ ha => (mem_filter.mp ha).2) (fun a _ => forced a)
  have qty : (M:ℝ)/(32*q*(Fixed.B b:ℝ)^2) ≤ Y.card := by
    apply le_trans _ ((div_le_div_of_nonneg_right cnt (by positivity : 0≤4*(Fixed.B b:ℝ)^2)).trans count)
    rw [div_div,div_div]; apply le_of_eq; congr 1; ring
  have length : Y.card≤rel.marks.length :=
    (card_le_card (show Y⊆rel.marks.toFinset from fun a ha => List.mem_toFinset.mpr (mem a ha))).trans
      (List.toFinset_card_le _)
  refine ⟨u,v,w,z,rel,Y,⟨up,ub⟩,⟨vp,vb⟩,⟨wp,wb⟩,⟨zp,zb⟩,stage,qty,?_,
    kernel_dim_of_cell_count qp qc stage (qty.trans (by exact_mod_cast length)),
    incidence_rank_of_cell_count qp rel (constructed_columns_injective hn2 (grows b two) target ⟨ub,vb⟩ stage)
      (qty.trans (by exact_mod_cast length))⟩
  intro a ha
  have c := mem_filter.mp (mem_filter.mp (sub ha)).1
  exact ⟨c.1,c.2,mem a ha⟩

end Cogentic.Construction
