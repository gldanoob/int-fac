import Cogentic.WeightedGridSieve
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

private theorem cell_scale (b : ℕ) : cellMarkCount b*Fixed.invWidth b = Fixed.A b := by
  dsimp [cellMarkCount,Fixed.invWidth,Fixed.A]
  rw [←Nat.pow_add]; congr 1; ring

theorem fixed_grid_interval {b : ℕ} (hd : 1 ≤ Fixed.d b) (cell : Option (Bool × Fin (Fixed.d b))) :
    let lo := firstCellMark b cell
    let M := cellMarkCount b
    ∀ x ∈ Ico lo (lo+M), 1 ≤ x ∧ x ≤ Fixed.A b ∧ onGrid (Fixed.d b) (Fixed.A b) (Fixed.invWidth b) x := by
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
  refine ⟨by exact_mod_cast xpos,by exact_mod_cast xA,?_⟩
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

/-- Every eligible class of modulus at most B⁴ contains constructor
marks, with a uniform count, in every one of the 2d+1 nominal cells. -/
theorem grid_cells_have_marks (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ ell ∈ dyadicTargets (Fixed.beta (n.log2+1)),
    ¬n.Prime → presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n) = none →
    let b := n.log2+1
    ∀ (q r u₀ u₁ v₀ v₁ : ℕ) (cell : Option (Bool × Fin (Fixed.d b))),
    0 < q → q ≤ (Fixed.B b)^4 →
    (∀ p ∈ (markModulus n ell).primeFactors, p ∣ q → ¬r ≡ Fixed.rootBase n [MOD p]) →
    let lo := firstCellMark b cell
    let M := cellMarkCount b
    let X := (Ico lo (lo+M)).filter (fun x => x ≡ r [MOD q])
    ((M:ℝ)/q)/8 ≤ ((X.filter (fun x => x ∈ (construct n ell u₀ u₁ v₀ v₁).marks)).card:ℝ) := by
  obtain ⟨n₀,marks⟩ := constructed_interval_marks line 20 (by norm_num)
  refine ⟨n₀,?_⟩
  intro n hn ell target comp absent b q r u₀ u₁ v₀ v₁ cell qp qmax elig lo M X
  have hd := Fixed.degree_pos (Nat.succ_pos n.log2)
  have grid := fixed_grid_interval hd cell
  have e := marks n hn ell target comp absent lo (lo+M) q r u₀ u₁ v₀ v₁ (Nat.le_add_right ..) qp elig
    (fun x hx => grid x (mem_filter.mp hx).1)
  simp only [Nat.cast_add,add_sub_cancel_left] at e
  let L := (M:ℝ)/q
  let ρ := ∏ p ∈ (markModulus n ell).primeFactors with ¬p∣q, (1-(p:ℝ)⁻¹)
  let z := (Fixed.z b:ℝ)
  let cnt := ((X.filter (fun x => x ∈ (construct n ell u₀ u₁ v₀ v₁).marks)).card:ℝ)
  change 1/4 ≤ ρ ∧ |cnt-L*ρ| ≤ ((Fixed.B b:ℝ)+2*L*exp 6)*exp (-20*z^2) at e
  have length : (Fixed.B b:ℝ) ≤ L := by
    apply (le_div_iff₀ (by exact_mod_cast qp : (0:ℝ)<q)).mpr
    exact_mod_cast (Nat.mul_le_mul_left (Fixed.B b) qmax).trans (show Fixed.B b*(Fixed.B b)^4 ≤ M by
      dsimp [Fixed.B,Fixed.beta,M,cellMarkCount]
      rw [←Nat.pow_mul,←Nat.pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega))
  have lp : 0 ≤ L := by dsimp [L]; positivity
  have z1 : 1 ≤ z := by
    change (1:ℝ) ≤ (↑(b.log2+1):ℝ)
    exact_mod_cast Nat.le_add_left 1 b.log2
  have e20 : exp (-20*z^2) ≤ exp (-20) := exp_le_exp.mpr (by nlinarith [one_le_pow₀ (n:=2) z1])
  have c6 : 1 ≤ exp 6 := one_le_exp (by norm_num)
  have e14 : 24 ≤ exp 14 := by have t := pow_div_factorial_le_exp 14 (by norm_num) 2; norm_num at t; linarith
  have rate : (1+2*exp 6)*exp (-20*z^2) ≤ 1/8 := by
    refine (mul_le_mul (by linarith only [c6] : 1+2*exp 6 ≤ 3*exp 6) e20 (exp_pos _).le (by positivity)).trans ?_
    rw [mul_assoc,←exp_add,show (6:ℝ)+ -20= -14 by norm_num,exp_neg,←div_eq_mul_inv]
    exact (div_le_iff₀ (exp_pos _)).mpr (by linarith)
  have bound := (mul_le_mul_of_nonneg_right (add_le_add length (le_refl (2*L*exp 6))) (exp_pos (-20*z^2)).le)
  have norm : ((Fixed.B b:ℝ)+2*L*exp 6)*exp (-20*z^2) ≤ L/8 := by
    apply bound.trans
    calc _ = L*((1+2*exp 6)*exp (-20*z^2)) := by ring
         _ ≤ _ := (mul_le_mul_of_nonneg_left rate lp).trans_eq (by ring)
  have lower := (abs_le.mp (e.2.trans norm)).1
  change L/8 ≤ cnt
  linarith only [lower,mul_le_mul_of_nonneg_left e.1 lp]

end Cogentic.Construction
