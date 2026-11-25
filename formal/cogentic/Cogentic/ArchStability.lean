import Cogentic.UnitGap

/-! A priori conditioning of the rounded real matrix used to reconstruct the
unit relation, starting from exact determinant and entry bounds. -/

open scoped BigOperators Matrix
namespace Cogentic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The true inverse has an explicit absolute row-sum bound by the adjugate
formula, including every minor obtained by replacing a row with a unit vector. -/
theorem inverse_rows_from_det (B : Matrix ι ι ℝ) (T g : ℝ) (hT : 1 ≤ T) (hg : 0 < g)
    (entries : ∀ i j, |B i j| ≤ T) (margin : g ≤ |B.det|) :
    ∀ i, ∑ j, |B⁻¹ i j| ≤ Fintype.card ι * ((Fintype.card ι).factorial * T^(Fintype.card ι) / g) := by
  classical
  have positive : 0 < |B.det| := hg.trans_le margin
  have top : 0 ≤ (Fintype.card ι).factorial * T^Fintype.card ι := by
    have := zero_le_one.trans hT
    positivity
  intro i
  calc
    _ ≤ ∑ _j : ι, (Fintype.card ι).factorial * T^(Fintype.card ι)/g := by
      apply Finset.sum_le_sum
      intro j _
      have adj : |B.adjugate i j| ≤ (Fintype.card ι).factorial * T^Fintype.card ι := by
        rw [Matrix.adjugate_apply]
        apply real_det_entry_bound
        intro k l
        by_cases h : k=j
        · subst k
          rw [Matrix.updateRow_self]
          by_cases e : l=i
          · subst l; simpa using hT
          · simpa [Pi.single_eq_of_ne e] using zero_le_one.trans hT
        · simpa [Matrix.updateRow_ne h] using entries k l
      rw [Matrix.inv_def,Matrix.smul_apply,Ring.inverse_eq_inv,smul_eq_mul, abs_mul,abs_inv,
        ← div_eq_inv_mul]
      exact (div_le_div_of_nonneg_right adj positive.le).trans (div_le_div_of_nonneg_left top hg margin)
    _ = _ := by simp

omit [DecidableEq ι] in
private theorem mulVec_row_bound (B : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) (M X : ℝ)
    (xp : 0 ≤ X) (row : ∑ j, |B i j| ≤ M) (bnd : ∀ j, |x j| ≤ X) :
    |(B *ᵥ x) i| ≤ M * X := by
  calc
    _ ≤ ∑ j, |B i j*x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |B i j| * X := Finset.sum_le_sum fun j _ => by rw [abs_mul]; gcongr; exact bnd j
    _ = (∑ j, |B i j|)*X := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right row xp

/-- Any solution of the rounded system is bounded using only the true
inverse, the perturbation and a bound for the rounded right-hand side. -/
theorem perturbed_preimage_bound (B C R : Matrix ι ι ℝ) (x : ι → ℝ) (ε M S : ℝ) (he : 0 ≤ ε)
    (_hp : 0 ≤ M) (hs : 0 ≤ S) (inverse : R*B = 1) (rows : ∀ i, ∑ j, |R i j| ≤ M)
    (close : ∀ i j, |C i j-B i j| ≤ ε) (rhs : ∀ i, |(C *ᵥ x) i| ≤ S)
    (small : M*Fintype.card ι*ε ≤ 1/2) : ∀ i, |x i| ≤ 2*M*S := by
  classical
  intro i
  obtain ⟨k,_,maximal⟩ := Finset.exists_max_image Finset.univ (fun j => |x j|) ⟨i,Finset.mem_univ i⟩
  let X := |x k|
  have xp : 0 ≤ X := abs_nonneg _
  have xm (j) : |x j| ≤ X := maximal j (Finset.mem_univ j)
  have pert (j) : |((C-B) *ᵥ x) j| ≤ (Fintype.card ι*ε)*X := by
    apply mulVec_row_bound _ _ _ _ _ xp _ xm
    calc
      _ ≤ ∑ _l : ι, ε := Finset.sum_le_sum (fun l _ => close j l)
      _ = _ := by simp
  have raw (j) : |(B *ᵥ x) j| ≤ S+(Fintype.card ι*ε)*X := by
    have id : B *ᵥ x = C *ᵥ x - (C-B) *ᵥ x := by rw [Matrix.sub_mulVec]; abel
    rw [id]
    exact (abs_sub _ _).trans (add_le_add (rhs j) (pert j))
  have combined := mulVec_row_bound R (B *ᵥ x) k M _ (by positivity) (rows k) raw
  rw [Matrix.mulVec_mulVec,inverse,Matrix.one_mulVec] at combined
  change X ≤ _ at combined
  have contraction := mul_le_mul_of_nonneg_right small xp
  exact (xm i).trans (by nlinarith only [combined,contraction])

/-- Nonsingularity survives rounding at the stated entry precision. -/
theorem rounded_matrix_det_ne_zero (B C R : Matrix ι ι ℝ) (ε M : ℝ) (he : 0 ≤ ε)
    (hp : 0 ≤ M) (inverse : R*B = 1) (rows : ∀ i, ∑ j, |R i j| ≤ M)
    (close : ∀ i j, |C i j-B i j| ≤ ε) (small : M*Fintype.card ι*ε ≤ 1/2) : C.det ≠ 0 := by
  intro singular
  obtain ⟨x,nz,zero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr singular
  apply nz
  funext i
  have hi := perturbed_preimage_bound B C R x ε M 0 he hp le_rfl inverse rows close
    (by intro j; simp [zero]) small i
  simpa using hi


/-- The true unit-minor margin and entry envelope alone supply nonsingularity
of the rounded matrix and continued-fraction correctness for its rational
solution. Every numerical side condition is a scalar precision inequality. -/
theorem apriori_archimedean_reconstruction {L : Type*} [AddCommGroup L] [Module ℤ L]
    (base : Module.Basis ι ℤ L) (v : ι → L) (t : L) (obs : L →ₗ[ℤ] (ι → ℝ))
    (nz : (base.toMatrix v).det ≠ 0) (Q : ℕ) (cap : (base.toMatrix v).det.natAbs ≤ Q)
    (C : Matrix ι ι ℝ) (s : ι → ℝ) (T g ε S : ℝ) (one : 1 ≤ T) (gp : 0 < g) (ep : 0 ≤ ε) (sp : 0 ≤ S) :
    let B : Matrix ι ι ℝ := fun i j => obs (v j) i
    let n := Fintype.card ι
    let M := (n : ℝ) * (n.factorial*T^n/g)
    (∀ i j, |B i j| ≤ T) → g ≤ |B.det| → (∀ i j, |C i j-B i j| ≤ ε) →
    (∀ i, |s i+obs t i| ≤ ε) → (∀ i, |s i| ≤ S) → M*n*ε ≤ 1/2 →
    M*(ε+n*(ε*(2*M*S))) < 1/(2*(Q:ℝ)^2) →
    C.det ≠ 0 ∧ ∀ y : ι → ℚ, C *ᵥ (fun j => (y j : ℝ)) = s →
      ∃ x : ι → ℚ, (∀ j, (base.repr t j : ℚ) + ∑ i, (base.repr (v i) j : ℚ)*x i = 0) ∧
        (∀ i, (x i).den ≤ Q) ∧ (∀ i, |y i-x i| < 1/(2*(Q:ℚ)^2)) ∧
        Reconstruction.multiplier y Q = some (Finset.univ.lcm (fun i => (x i).den)) ∧
        Finset.univ.lcm (fun i => (x i).den) ≤ Q := by
  classical
  intro B n M entries margin close rhs rhsSize small precision
  have tp := zero_le_one.trans one
  have mp : 0 ≤ M := by dsimp [M]; positivity
  have bn : B.det ≠ 0 := abs_pos.mp (gp.trans_le margin)
  have inv := B.nonsing_inv_mul (isUnit_iff_ne_zero.mpr bn)
  have rows := inverse_rows_from_det B T g one gp entries margin
  have cn := rounded_matrix_det_ne_zero B C B⁻¹ ε M ep mp inv rows close small
  refine ⟨cn,?_⟩
  intro y solve
  obtain ⟨x,lattice,real,den⟩ := exact_archimedean_coordinates base v t obs nz
  have lcmCap := (Nat.le_of_dvd (Int.natAbs_pos.mpr nz) den).trans cap
  have lcmPos : 0 < Finset.univ.lcm (fun i => (x i).den) := by
    apply Nat.pos_of_ne_zero; simp [Finset.lcm_eq_zero_iff]
  have widths (i) : (x i).den ≤ Q := (Nat.le_of_dvd lcmPos (Finset.dvd_lcm (Finset.mem_univ i))).trans lcmCap
  have trueSolve : B *ᵥ (fun j => (x j : ℝ)) = -obs t := by
    funext i; exact eq_neg_of_add_eq_zero_right (real i)
  have ysize := perturbed_preimage_bound B C B⁻¹ (fun j => (y j : ℝ)) ε M S ep mp sp
    inv rows close (by simpa only [solve] using rhsSize) small
  have err := arch_solve_error C B B⁻¹ s (-obs t) (fun j => (y j : ℝ)) (fun j => (x j : ℝ))
    ε (2*M*S) M ep (by positivity) solve trueSolve inv (fun i j => by rw [abs_sub_comm]; exact close i j)
    (fun i => by rw [Pi.neg_apply,sub_eq_add_neg,← neg_add,abs_neg,add_comm]; exact rhs i) ysize rows
  have near (i) : |y i-x i| < 1/(2*(Q:ℚ)^2) := by
    apply (Rat.cast_lt (K := ℝ)).mp
    push_cast
    rw [abs_sub_comm]
    exact (err i).trans_lt precision
  exact ⟨x,lattice,widths,near,Reconstruction.multiplier_exact y x Q widths near,lcmCap⟩

end Cogentic
