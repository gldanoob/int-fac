import Cogentic.Marking
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace Cogentic.Construction
open Finset Real
open scoped Classical
noncomputable section

/-- A residue class with retained mass still contains a column after rows in
`D` are peeled. The interaction cost and mass charge are both on this draw. -/
theorem target_survives_ordinary_deletion {ι : Type*} (Y : Finset ℕ) (D : Finset ι)
    (weight : ℕ → ℝ) (hit : ι → ℕ → Prop) [∀ i, DecidablePred (hit i)]
    (mass err : ι → ℝ) (ell A base cap energy : ℝ)
    (wn : ∀ a∈Y, 0≤ weight a) (mn : ∀ i∈D, 0≤ mass i)
    (en : 0≤ ell) (an : 0≤ A) (bn : 0≤ base)
    (limited : (∑ i∈D,mass i)≤ cap) (small : (∑ i∈D,mass i*(err i)^2)≤ energy)
    (overlap : ∀ i∈D, ell*(∑ a∈Y with hit i a,weight a) ≤ A*(mass i*(|err i|+base)))
    (margin : A*(sqrt (cap*energy)+cap*base) < ell*∑ a∈Y,weight a) :
    ∃ a∈Y, ∀ i∈D, ¬hit i a := by
  classical
  by_contra! covered
  have m0 := sum_nonneg mn
  have e0 := sum_nonneg (s:=D) (fun i hi=>mul_nonneg (mn i hi) (sq_nonneg (err i)))
  have cs := sum_mul_sq_le_sq_mul_sq D (fun i=>sqrt (mass i)) (fun i=>sqrt (mass i)*|err i|)
  have lin : (∑ i∈D,mass i*|err i|)≤ sqrt (cap*energy) := by
    have first : (∑ i∈D,sqrt (mass i)*(sqrt (mass i)*|err i|))=(∑ i∈D,mass i*|err i|) := by
      apply sum_congr rfl; intro i hi; rw [←mul_assoc,←sq,sq_sqrt (mn i hi)]
    have second : (∑ i∈D,(sqrt (mass i))^2)=∑ i∈D,mass i :=
      sum_congr rfl (fun i hi=>sq_sqrt (mn i hi))
    have third : (∑ i∈D,(sqrt (mass i)*|err i|)^2)=∑ i∈D,mass i*(err i)^2 := by
      apply sum_congr rfl; intro i hi; rw [mul_pow,sq_abs,sq_sqrt (mn i hi)]
    rw [first,second,third] at cs
    exact (Real.le_sqrt_of_sq_le (cs.trans (mul_le_mul limited small e0 (m0.trans limited))))
  have total : (∑ a∈Y,weight a)≤∑ i∈D,∑ a∈Y with hit i a,weight a := by
    simp only [sum_filter]
    rw [sum_comm]
    apply sum_le_sum
    intro a ha
    obtain ⟨i,hi,yes⟩ := covered a ha
    exact (if_pos yes).symm.le.trans (single_le_sum (s:=D) (f:=fun j=>if hit j a then weight a else 0)
      (fun j _=>by split <;> first | exact wn a ha | rfl) hi)
  have charged := sum_le_sum overlap
  rw [←mul_sum,←mul_sum] at charged
  simp only [mul_add,sum_add_distrib,←sum_mul] at charged
  have sum := (mul_le_mul_of_nonneg_left total en).trans charged
  have bound : ell * ∑ a ∈ Y, weight a ≤ A * (sqrt (cap * energy) + cap * base) := by
    calc
      ell * ∑ a ∈ Y, weight a ≤ A * (∑ i ∈ D, mass i * |err i| + (∑ i ∈ D, mass i) * base) := by
        simpa only [mul_add, ←sum_mul] using sum
      _ ≤ A * (sqrt (cap * energy) + cap * base) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add lin (mul_le_mul_of_nonneg_right limited bn)) an
  apply margin.not_ge
  exact bound

end
end Cogentic.Construction

#print axioms Cogentic.Construction.target_survives_ordinary_deletion
