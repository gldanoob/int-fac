import Cogentic.TrueLogModel
import Cogentic.GramPeeling

/-! Scalar perturbation margins for the centered two-field model Gram. -/

open scoped Matrix BigOperators
namespace Cogentic

/-- The finite variance lower bound absorbs the covariance direction and
the block-supported remainder. An arbitrary error measured in the full
coefficient energy is allowed only at the smaller archimedean scale. -/
theorem centered_model_margin {α : Type*} [Fintype α]
    (p g m : α → ℝ) (u cells F arch diag projection remainder actual ε : ℝ)
    (nonneg : ∀ a, 0 ≤ p a) (up : 1 ≤ u) (cp : 1 ≤ cells) (fp : 0 ≤ F)
    (grid : arch ≤ 3*cells*(∑ a, p a*(g a)^2))
    (mean : ∑ a, p a*(m a)^2 ≤ 12*u*F)
    (diagonal : 15*F ≤ 16*diag) (removed : 16*projection ≤ F) (finiteError : 16*remainder ≤ F)
    (observed : (∑ a, p a*(g a+m a)^2)+diag-projection-remainder ≤ actual+ε)
    (error : 768*u*cells*ε ≤ F+arch) :
    F+arch ≤ 768*u*cells*actual := by
  let Q := (∑ a, p a*(g a+m a)^2)+diag-projection-remainder
  have finitePart : 4*(∑ a, p a*(g a+m a)^2)+3*F ≤ 4*Q := by dsimp [Q]; linarith
  have energy := covariance_energy p g m F u Q nonneg fp up mean finitePart
  have sc : 0 ≤ 3*cells := by linarith
  have fe : F ≤ 3*cells*(64*u*F) := by
    have a := mul_le_mul_of_nonneg_right up fp
    have b := mul_le_mul_of_nonneg_right cp (by positivity : 0 ≤ 64*u*F)
    linarith
  have raw : F+arch ≤ 384*u*cells*Q := by
    nlinarith [mul_le_mul_of_nonneg_left energy sc]
  have obs : Q ≤ actual+ε := observed
  nlinarith [mul_le_mul_of_nonneg_left obs (by positivity : 0 ≤ 768*u*cells)]

/-- Conditional centered model comparison for the actual root grid. Its
conclusion is a quantitative lower bound for the measured Gram energy. -/
theorem fixed_centered_model_margin {b : ℕ} (big : 130000 ≤ Fixed.d b) :
    let d := Fixed.d b
    let w := (Fixed.invWidth b:ℝ)⁻¹
    ∀ {β : Option (Fin (2*d)) → Type*} [∀ k, Fintype (β k)]
      (point mass : (k : Option (Fin (2*d))) → β k → ℝ),
      (∀ a, 3/4 ≤ point none a ∧ point none a ≤ 1) →
      (∀ i a, nominalCenter d i+w ≤ point (some i) a ∧ point (some i) a ≤ nominalCenter d i+2*w) →
      (∀ k a, 0 ≤ mass k a) → (∀ k, ∑ a, mass k a = 1) →
    ∀ (v₀ : ℝ) (v : Fin (2*d) → ℝ) (m : (k : Option (Fin (2*d))) × β k → ℝ),
      let cells := (2*d+1:ℝ)
      let p := fun a : (k : Option (Fin (2*d))) × β k => mass a.1 a.2/cells
      let g := fun a : (k : Option (Fin (2*d))) × β k =>
        v₀+∑ j, Real.log |point a.1 a.2-nominalCenter d j| * v j
      let arch := v₀^2+∑ j, (v j)^2
      ∀ u F diag projection remainder actual ε : ℝ, 1 ≤ u → 0 ≤ F →
      (∑ a, p a*(m a)^2 ≤ 12*u*F) → 15*F ≤ 16*diag → 16*projection ≤ F → 16*remainder ≤ F →
      (∑ a, p a*(g a+m a)^2)+diag-projection-remainder ≤ actual+ε →
      768*u*cells*ε ≤ F+arch → F+arch ≤ 768*u*cells*actual := by
  intro d w β _ point mass base loc pos norm v₀ v m cells p g arch u F diag proj remn actual ε
    up fp means var loss block observed err
  have cp : 1 ≤ cells := by dsimp [cells]; linarith [Nat.cast_nonneg (α:=ℝ) d]
  have cpos : cells ≠ 0 := by linarith
  have grid := fixed_nominal_grid_energy big point mass base loc pos norm v₀ v
  have normalized : cells*(∑ a, p a*(g a)^2) =
      (∑ a, mass none a*(g ⟨none,a⟩)^2) +
       ∑ i, ∑ a, mass (some i) a*(g ⟨some i,a⟩)^2 := by
    rw [Finset.mul_sum]
    simp only [p,show ∀ t q : ℝ, cells*(t/cells*q)=t*q by intro t q; field_simp]
    rw [Fintype.sum_sigma, Fintype.sum_option]
  apply centered_model_margin p g m u cells F arch diag proj remn actual ε
    (fun a => div_nonneg (pos a.1 a.2) (by linarith)) up cp fp _ means var loss block observed err
  rw [mul_assoc,normalized]
  exact grid

/-- Positive scores give positive definiteness of the weighted Gram of the
actual columns. This form also admits zero weights on discarded columns. -/
theorem diagonal_gram_positive {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (V : Matrix ι κ ℝ) (weight : κ → ℝ)
    (scores : ∀ v : ι → ℝ, v ≠ 0 → 0 < ∑ a, weight a*((V.transpose *ᵥ v) a)^2) :
    (V * Matrix.diagonal weight * V.transpose).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · change (V * Matrix.diagonal weight * V.transpose).conjTranspose = _
    simp [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_mul,Matrix.mul_assoc]
  · intro v ne
    rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    simp only [star_trivial,dotProduct,Matrix.mulVec_diagonal]
    simpa only [sq,mul_left_comm,mul_assoc] using scores v ne

end Cogentic

#print axioms Cogentic.fixed_centered_model_margin
