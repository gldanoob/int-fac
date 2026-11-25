import Cogentic.CoefficientTail
import Cogentic.RowAdmission

namespace Cogentic.Construction
open Real Cogentic.Window

/-- An event on the prescribed CRT lattice whose probability exceeds the
explicit Gaussian tail has a witness in the executable coefficient box. -/
theorem PrescribedRows.box_witness {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (side : Bool)
    (E : ℤ×ℤ → Prop) [DecidablePred E] :
    let b := n.log2+1
    1216*(Fixed.B b:ℝ)^2*exp (-π*((b:ℝ)^2)^2/2) < prescribedProbability R side E →
    ∃ k : ℤ×ℤ, R.compatible side k.1 k.2 ∧ inCoefficientBox n k ∧ E k := by
  classical
  intro b lower
  by_contra! no
  let C := {k : ℤ×ℤ // R.compatible side k.1 k.2}
  let Z := ∑' k : C, coefficientWeight n k.val
  let W := (Fixed.U b:ℝ)*Fixed.A b*Fixed.U b
  let e := exp (-π*((b:ℝ)^2)^2/2)
  let Q : ℝ := prodPrimes R.primes
  let bad := fun k : ℤ×ℤ => if ¬inCoefficientBox n k then coefficientWeight n k else 0
  let g := fun k : C => if E k.val then coefficientWeight n k.val else 0
  have ⟨sBad,tail⟩ := coefficient_outside_weight n
  change Summable bad at sBad
  change (∑' k, bad k) ≤ 64*W*e at tail
  have bw (k : ℤ×ℤ) : 0≤coefficientWeight n k := mul_nonneg (exp_pos _).le (exp_pos _).le
  have bn (k : ℤ×ℤ) : 0≤bad k := by dsimp only [bad]; split <;> first | exact bw k | rfl
  have gn (k : C) : 0≤g k := by dsimp only [g]; split <;> first | exact bw _ | rfl
  have le (k : C) : g k ≤ bad k.val := by
    by_cases ev : E k.val
    · have outside : ¬inCoefficientBox n k.val := fun box => no k.val k.property box ev
      simp only [g,bad,if_pos ev,if_pos outside,le_refl]
    · simpa only [g,if_neg ev] using bn k.val
  have sb := sBad.subtype (fun k : ℤ×ℤ => R.compatible side k.1 k.2)
  have sg := Summable.of_nonneg_of_le gn le sb
  have num : (∑' k, g k)≤64*W*e := (sg.tsum_le_tsum le sb).trans
    ((sBad.tsum_subtype_le bad _ bn).trans tail)
  obtain ⟨zp,normal⟩ := R.weight_normalizer target side
  change 0<Z at zp
  change |W/(Q*Z)-1| ≤ 18*exp (-(Fixed.U b:ℝ)) at normal
  have hp := R.subprod_bounds (s := R.primes) Finset.Subset.rfl
  have qp : 0<Q := by dsimp only [Q]; exact_mod_cast hp.1
  have cap : Q ≤ (Fixed.B b:ℝ)^2 := by dsimp only [Q]; exact_mod_cast hp.2
  have rate := exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg (α:=ℝ) (Fixed.U b)))
  have bound : W/(Q*Z) ≤ 19 := by linarith only [(abs_le.mp normal).2,rate]
  rw [div_le_iff₀ (mul_pos qp zp)] at bound
  have total := bound.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right cap zp.le) (by norm_num : (0:ℝ)≤19))
  change 1216*(Fixed.B b:ℝ)^2*e < (∑' k, g k)/Z at lower
  have en : 0≤e := (exp_pos _).le
  rw [lt_div_iff₀ zp] at lower
  linarith only [lower,num,mul_le_mul_of_nonneg_right total en]

end Cogentic.Construction
