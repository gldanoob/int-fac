import Cogentic.WeightedGridSieve
import Cogentic.RawMesh

namespace Cogentic.Construction
open Real Finset

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
