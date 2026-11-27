import Cogentic.RandomizedFormReduction

namespace Cogentic.RandomizedFormReductionSize

open RandomizedReducedFormRoot (formValue norm_identity)

/-- Completing the square in both directions bounds the coordinates of a
vector from its form value. -/
theorem column_square_bounds (a b c x y : ℤ) :
    (a * c - b ^ 2) * x ^ 2 ≤ c * formValue a b c x y ∧
    (a * c - b ^ 2) * y ^ 2 ≤ a * formValue a b c x y := by
  have hx := norm_identity (a := c) (b := b) (c := a) (N := a * c - b ^ 2)
    (x := y) (y := x) (by ring)
  have hy := norm_identity (a := a) (b := b) (c := c) (N := a * c - b ^ 2)
    (x := x) (y := y) (by ring)
  rw [show formValue c b a y x = formValue a b c x y by unfold formValue; ring] at hx
  exact ⟨by linarith only [hx, sq_nonneg (c * y + b * x)],
    by linarith only [hy, sq_nonneg (a * x + b * y)]⟩

private theorem abs_le_square (x : ℤ) : |x| ≤ x ^ 2 := by
  by_cases hx : x = 0
  · simp [hx]
  have hpos : 0 < |x| := abs_pos.mpr hx
  have hprod := mul_le_mul_of_nonneg_right (show 1 ≤ |x| by omega) (abs_nonneg x)
  simpa only [one_mul, ← pow_two, sq_abs] using hprod

/-- Each basis column is bounded in terms of its own represented value. -/
theorem basis_entry_bounds {a b c A C x y u v : ℤ} (hdisc : 0 < a * c - b ^ 2)
    (hfirst : formValue a b c x y = A) (hsecond : formValue a b c u v = C) :
    |x| ≤ c * A ∧ |y| ≤ a * A ∧ |u| ≤ c * C ∧ |v| ≤ a * C := by
  have hbound (r s : ℤ) :
      |r| ≤ c * formValue a b c r s ∧ |s| ≤ a * formValue a b c r s := by
    obtain ⟨hr, hs⟩ := column_square_bounds a b c r s
    have hD : 1 ≤ a * c - b ^ 2 := by omega
    have hscale (t : ℤ) : t ^ 2 ≤ (a * c - b ^ 2) * t ^ 2 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hD (sq_nonneg t)
    exact ⟨(abs_le_square r).trans ((hscale r).trans hr),
      (abs_le_square s).trans ((hscale s).trans hs)⟩
  obtain ⟨hx, hy⟩ := hbound x y
  obtain ⟨hu, hv⟩ := hbound u v
  rw [hfirst] at hx hy
  rw [hsecond] at hu hv
  exact ⟨hx, hy, hu, hv⟩

/-- A centered stage has a bounded trailing coefficient even before testing
whether to swap. -/
theorem centered_coefficient_bounds {A B C D : ℤ} (hA : 0 < A) (hD : 0 < D)
    (hcenter : |2 * B| ≤ A) (hdisc : A * C - B ^ 2 = D) :
    0 < C ∧ 2 * |B| ≤ A ∧ 4 * C ≤ 4 * D + A := by
  have hC : 0 < C := by
    by_contra! hn
    have hp := mul_nonpos_of_nonneg_of_nonpos hA.le hn
    have hs := sq_nonneg B
    omega
  have hmid : 2 * |B| ≤ A := by
    simpa only [abs_mul, abs_of_nonneg (show (0 : ℤ) ≤ 2 by decide)] using hcenter
  refine ⟨hC, hmid, le_of_mul_le_mul_left ?_ hA⟩
  have hBprod := mul_nonneg (sub_nonneg.mpr hmid) (add_nonneg hA.le
    (mul_nonneg (show (0 : ℤ) ≤ 2 by decide) (abs_nonneg B)))
  have hBsq : 4 * B ^ 2 ≤ A ^ 2 := by nlinarith only [hBprod, sq_abs B]
  have hDprod := mul_nonneg (show 0 ≤ A - 1 by omega) hD.le
  nlinarith only [hdisc, hBsq, hDprod]

/-- The centering quotient has size controlled by the incoming middle and
leading coefficients. -/
theorem centered_shear_index_bound {A b k : ℤ} (hA : 0 < A)
    (hcenter : |2 * (b + A * k)| ≤ A) : |k| ≤ A + |b| := by
  have hmid : 2 * |b + A * k| ≤ A := by
    simpa only [abs_mul, abs_of_nonneg (show (0 : ℤ) ≤ 2 by decide)] using hcenter
  calc
    |k| ≤ A * |k| := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (show 1 ≤ A by omega) (abs_nonneg k)
    _ = |A * k| := by rw [abs_mul, abs_of_pos hA]
    _ = |(b + A * k) - b| := by rw [add_sub_cancel_left]
    _ ≤ |b + A * k| + |b| := abs_sub _ _
    _ ≤ A + |b| := by omega

/-- A centered equivalent stage whose lead has decreased from the input lead
has polynomial-size coefficients and cumulative basis entries. -/
theorem centered_stage_bounds {a b c A B C x y u v : ℤ}
    (ha : 0 < a) (hdisc : 0 < a * c - b ^ 2)
    (hA : 0 < A) (hlead : A ≤ a) (hcenter : |2 * B| ≤ A)
    (hstage : A * C - B ^ 2 = a * c - b ^ 2)
    (hfirst : formValue a b c x y = A) (hsecond : formValue a b c u v = C) :
    let H := a * c - b ^ 2 + a
    |B| ≤ a ∧ |C| ≤ H ∧
      |x| ≤ c * H ∧ |y| ≤ a * H ∧ |u| ≤ c * H ∧ |v| ≤ a * H := by
  dsimp only
  have hc : 0 < c := by
    by_contra! hn
    have hp := mul_nonpos_of_nonneg_of_nonpos ha.le hn
    have hs := sq_nonneg b
    omega
  obtain ⟨hCpos, hmid, htrail⟩ := centered_coefficient_bounds hA hdisc hcenter hstage
  have hC : C ≤ a * c - b ^ 2 + a := by omega
  have hAH : A ≤ a * c - b ^ 2 + a := by omega
  obtain ⟨hx, hy, hu, hv⟩ := basis_entry_bounds hdisc hfirst hsecond
  exact ⟨by omega, by rwa [abs_of_pos hCpos], hx.trans (mul_le_mul_of_nonneg_left hAH hc.le),
    hy.trans (mul_le_mul_of_nonneg_left hAH ha.le),
    hu.trans (mul_le_mul_of_nonneg_left hC hc.le), hv.trans (mul_le_mul_of_nonneg_left hC ha.le)⟩

/-- A rotation swaps the two columns and negates the old first column.
Its new lead stays positive and no larger than the input lead. -/
theorem rotated_stage_bounds {a b c A B C x y u v : ℤ}
    (ha : 0 < a) (hdisc : 0 < a * c - b ^ 2)
    (hA : 0 < A) (hlead : A ≤ a) (hrotate : C ≤ A) (hcenter : |2 * B| ≤ A)
    (hstage : A * C - B ^ 2 = a * c - b ^ 2)
    (hfirst : formValue a b c x y = A) (hsecond : formValue a b c u v = C) :
    let H := a * c - b ^ 2 + a
    0 < C ∧ C ≤ a ∧ |-B| ≤ a ∧ |A| ≤ a ∧
      |u| ≤ c * H ∧ |v| ≤ a * H ∧ |-x| ≤ c * H ∧ |-y| ≤ a * H := by
  obtain ⟨hmid, _, hx, hy, hu, hv⟩ :=
    centered_stage_bounds ha hdisc hA hlead hcenter hstage hfirst hsecond
  have hC := (centered_coefficient_bounds hA hdisc hcenter hstage).1
  simpa only [abs_neg, abs_of_pos hA] using
    And.intro hC ⟨hrotate.trans hlead, hmid, hlead, hu, hv, hx, hy⟩

private theorem reduced_minimum {A B C x y : ℤ} (hA : 0 < A) (hAC : A ≤ C)
    (hcenter : |2 * B| ≤ A) (hnonzero : x ≠ 0 ∨ y ≠ 0) :
    A ≤ formValue A B C x y := by
  have hprod : |2 * B * x * y| ≤ A * |x| * |y| := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcenter (abs_nonneg x)) (abs_nonneg y)
  have hcross : -(A * |x| * |y|) ≤ 2 * B * x * y :=
    (neg_le_neg hprod).trans (neg_abs_le _)
  have hsum : 1 ≤ x ^ 2 + y ^ 2 := by
    rcases hnonzero with hx | hy
    · have hpos := sq_pos_of_ne_zero hx
      have hn := sq_nonneg y
      omega
    · have hpos := sq_pos_of_ne_zero hy
      have hn := sq_nonneg x
      omega
  have hq2 : 1 ≤ 2 * (x ^ 2 - |x| * |y| + y ^ 2) := by
    nlinarith only [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y, hsum]
  have hq : 1 ≤ x ^ 2 - |x| * |y| + y ^ 2 := by omega
  have hlead := mul_le_mul_of_nonneg_left hq hA.le
  have htail := mul_le_mul_of_nonneg_right hAC (sq_nonneg y)
  unfold formValue
  nlinarith only [hlead, hcross, htail]

/-- The integral reduced lead is at most the input lead, using the first
column of the inverse transformation. -/
theorem result_lead_le_input {a b c : ℤ} (r : RandomizedFormReduction.Result a b c) :
    r.A ≤ a := by
  have hcenter : |2 * r.B| ≤ r.A := abs_le.mpr ⟨r.reduced.2.1.le, r.reduced.2.2.1⟩
  have hnonzero : r.v ≠ 0 ∨ -r.y ≠ 0 := by
    by_contra! h
    obtain ⟨hv, hy⟩ := h
    have hy' : r.y = 0 := by omega
    have hdet := r.det
    rw [hv, hy'] at hdet
    simp at hdet
  have hval := r.transform r.v (-r.y)
  rw [show r.x * r.v + r.u * (-r.y) = 1 by rw [← r.det]; ring,
    show r.y * r.v + r.v * (-r.y) = 0 by ring] at hval
  rw [show formValue a b c 1 0 = a by simp [formValue]] at hval
  exact (reduced_minimum r.reduced.1 r.reduced.2.2.2.1 hcenter hnonzero).trans hval.le

/-- The certified reducer's four returned basis entries and its centered
coefficients satisfy the polynomial bounds. -/
theorem reduce_size_bounds (a b c : ℤ) (ha : 0 < a) (hdisc : 0 < a * c - b ^ 2) :
    let r := RandomizedFormReduction.reduce a b c ha hdisc
    let H := a * c - b ^ 2 + a
    r.A ≤ a ∧ |r.B| ≤ a ∧ |r.C| ≤ H ∧
      |r.x| ≤ c * H ∧ |r.y| ≤ a * H ∧ |r.u| ≤ c * H ∧ |r.v| ≤ a * H := by
  intro r H
  have hlead := result_lead_le_input r
  have hcenter : |2 * r.B| ≤ r.A := abs_le.mpr ⟨r.reduced.2.1.le, r.reduced.2.2.1⟩
  have hstage : r.A * r.C - r.B ^ 2 = a * c - b ^ 2 := by
    have hd := r.discriminant
    omega
  have hfirst := r.first_column.symm
  have hsecond : formValue a b c r.u r.v = r.C := by
    simpa [formValue] using (r.transform 0 1).symm
  exact ⟨hlead, centered_stage_bounds ha hdisc r.reduced.1 hlead hcenter hstage hfirst hsecond⟩

theorem centered_height_le_input_polynomial (a b c : ℤ) :
    a * c - b ^ 2 + a ≤ a * (c + 1) := by
  nlinarith only [sq_nonneg b]

#print axioms column_square_bounds
#print axioms centered_coefficient_bounds
#print axioms centered_stage_bounds
#print axioms rotated_stage_bounds
#print axioms centered_shear_index_bound
#print axioms reduce_size_bounds

end Cogentic.RandomizedFormReductionSize
