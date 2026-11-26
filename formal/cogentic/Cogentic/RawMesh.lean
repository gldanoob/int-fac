import Cogentic.ConstructionBrackets

namespace Cogentic.Construction
open Real Finset

def gridCellLeft (b : ℕ) (cell : Option (Bool × Fin (Fixed.d b))) : ℚ :=
  match cell with
  | none => 3/4
  | some (side,j) => center (Fixed.d b) side j.val + (Fixed.invWidth b:ℚ)⁻¹

def firstCellMark (b : ℕ) (cell : Option (Bool × Fin (Fixed.d b))) : ℕ :=
  ⌈(Fixed.A b:ℚ)*gridCellLeft b cell⌉₊

def cellMarkCount (b : ℕ) := 2^(9997*Fixed.h b)

theorem cell_scale (b : ℕ) : cellMarkCount b*Fixed.invWidth b = Fixed.A b := by
  dsimp [cellMarkCount,Fixed.invWidth,Fixed.A]
  rw [←Nat.pow_add]; congr 1; ring

theorem fixed_grid_interval_bounds {b : ℕ} (hd : 1 ≤ Fixed.d b) (cell : Option (Bool × Fin (Fixed.d b))) :
    let lo := firstCellMark b cell
    let M := cellMarkCount b
    ∀ x ∈ Ico lo (lo+M),
      (gridCellLeft b cell ≤ (x:ℚ)/Fixed.A b ∧ (x:ℚ)/Fixed.A b ≤ gridCellLeft b cell+(Fixed.invWidth b:ℚ)⁻¹) ∧
      1 ≤ x ∧ x ≤ Fixed.A b ∧ onGrid (Fixed.d b) (Fixed.A b) (Fixed.invWidth b) x := by
  intro lo M x mem
  let a := (Fixed.A b:ℚ)
  let W := Fixed.invWidth b
  let u := gridCellLeft b cell
  let w := (W:ℚ)⁻¹
  have ap : 0<a := by dsimp [a,Fixed.A]; positivity
  have hp : 1 ≤ Fixed.h b := Nat.mul_pos hd (Nat.succ_pos _)
  have W4 : 4 ≤ W := (by decide : 4 ≤ 2^3).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have q4 : (4:ℚ)≤W := by exact_mod_cast W4
  have wp : 0<w := by dsimp [w]; positivity
  have small : w ≤ 1/4 := by
    simpa only [w,one_div] using one_div_le_one_div_of_le (by norm_num : 0<(4:ℚ)) q4
  have left : 0 < u ∧ u+w ≤ 1 := by
    cases cell with
    | none => change 0 < (3/4:ℚ) ∧ 3/4+w ≤ 1; constructor <;> linarith
    | some c =>
      obtain ⟨side,j⟩ := c
      change 0 < center _ side j.val+w ∧ center _ side j.val+w+w≤1
      have h := center_range j.isLt side
      constructor <;> linarith
  have low := Nat.le_ceil (a*u)
  have ceilL := Nat.ceil_lt_add_one (mul_nonneg ap.le left.1.le)
  change a*u ≤ (lo:ℚ) at low
  change (lo:ℚ) < a*u+1 at ceilL
  obtain ⟨xlo,xhi⟩ := mem_Ico.mp mem
  have xloQ : (lo:ℚ)≤x := by exact_mod_cast xlo
  have xhiQ : (x:ℚ)+1≤lo+M := by exact_mod_cast xhi
  have Mscale : (M:ℚ) = a*w := by
    change (M:ℚ)=a*(W:ℚ)⁻¹
    rw [←div_eq_mul_inv,eq_div_iff (by positivity : (W:ℚ)≠0)]
    change (cellMarkCount b:ℚ)*(Fixed.invWidth b:ℚ) = (Fixed.A b:ℚ)
    exact_mod_cast cell_scale b
  have bot : u ≤ (x:ℚ)/a := (le_div_iff₀ ap).mpr (by linarith only [low,xloQ,mul_comm u a])
  have top : (x:ℚ)/a ≤ u+w := (div_le_iff₀ ap).mpr (by linarith only [xhiQ,Mscale,ceilL,mul_add a u w,mul_comm (u+w) a])
  have xpos : 0 < (x:ℚ) := (mul_pos ap left.1).trans_le (low.trans xloQ)
  have xA : (x:ℚ) ≤ a := by simpa using (div_le_iff₀ ap).mp (top.trans left.2)
  change (x:ℚ) ≤ (Fixed.A b:ℚ) at xA
  refine ⟨⟨bot,top⟩,by exact_mod_cast xpos,by exact_mod_cast xA,?_⟩
  simp only [onGrid,Bool.or_eq_true,decide_eq_true_eq,List.any_eq_true,List.mem_append]
  cases cell with
  | none => exact Or.inl ⟨bot,top⟩
  | some p =>
    obtain ⟨side,j⟩ := p
    refine Or.inr ⟨center _ side j.val,?_,bot,?_⟩
    · cases side
      · exact Or.inl (List.mem_map.mpr ⟨j.val,List.mem_range.mpr j.isLt,rfl⟩)
      · exact Or.inr (List.mem_map.mpr ⟨j.val,List.mem_range.mpr j.isLt,rfl⟩)
    · change (x:ℚ)/a ≤ center _ side j.val+2*w
      change (x:ℚ)/a ≤ center _ side j.val+w+w at top
      linarith

theorem fixed_grid_interval {b : ℕ} (hd : 1 ≤ Fixed.d b) (cell : Option (Bool × Fin (Fixed.d b))) :
    let lo := firstCellMark b cell
    let M := cellMarkCount b
    ∀ x ∈ Ico lo (lo+M), 1 ≤ x ∧ x ≤ Fixed.A b ∧ onGrid (Fixed.d b) (Fixed.A b) (Fixed.invWidth b) x :=
  fun x hx => (fixed_grid_interval_bounds hd cell x hx).2

def meshVariation (L M : ℕ) (f : ℕ → ℝ) : ℝ :=
  |f (L+(M-1))| + ∑ j∈range (M-1), |f (L+(j+1))-f (L+j)|

theorem mesh_product_variation {L M : ℕ} (mp : 0<M) (f g : ℕ→ℝ) (A J : ℝ) (ap : 0≤A)
    (fb : ∀ i<M, |f i|≤A) (gb : ∀ i<M, |g i|≤A)
    (fv : (∑ j∈range (M-1), |f (j+1)-f j|)≤J)
    (gv : (∑ j∈range (M-1), |g (j+1)-g j|)≤J) :
    meshVariation L M (fun a=> f (a-L)*g (a-L)) ≤ A^2+2*A*J := by
  have m : M-1<M := by omega
  have step j (hj : j∈range (M-1)) : |f (j+1)*g (j+1)-f j*g j|≤A*|g (j+1)-g j|+A*|f (j+1)-f j| := by
    obtain hj := mem_range.mp hj
    rw [show f (j+1)*g (j+1)-f j*g j=f (j+1)*(g (j+1)-g j)+(f (j+1)-f j)*g j by ring]
    apply (abs_add_le ..).trans
    rw [abs_mul,abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_right (fb _ (by omega)) (abs_nonneg _)) (by
      rw [mul_comm];exact mul_le_mul_of_nonneg_right (gb j (by omega)) (abs_nonneg _))
  have sum := sum_le_sum step
  rw [sum_add_distrib,←mul_sum,←mul_sum] at sum
  have tail := sum.trans (add_le_add (mul_le_mul_of_nonneg_left gv ap) (mul_le_mul_of_nonneg_left fv ap))
  dsimp only [meshVariation]
  simp only [Nat.add_sub_cancel_left,abs_mul (f (M-1))]
  exact (add_le_add (mul_le_mul (fb _ m) (gb _ m) (abs_nonneg _) ap) tail).trans_eq (by ring)

end Cogentic.Construction
