import Cogentic.MarkSeparation

namespace Cogentic.Construction

/-- The amplitude of the unperturbed real target. -/
def amplitude (n : ℕ) : ℕ :=
  let b := n.log2+1
  leadingCoefficient n*(Fixed.A b)^Fixed.d b

/-- Reference scale common to the one- and two-point widths. -/
def referenceWidth (n : ℕ) : ℕ :=
  let b := n.log2+1
  primorial (Fixed.d b)*Fixed.B b*Fixed.rootBase n*Fixed.U b*Fixed.A b

/-- The power-of-three rounding of the leading coefficient costs at most
    a factor nine compared with its defining lower threshold. -/
theorem amplitude_compare {n : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1)) :
    let b := n.log2+1; let w := referenceWidth n
    6*Fixed.K₁ b*b^2*w ≤ amplitude n ∧ amplitude n ≤ 54*Fixed.K₁ b*b^2*w := by
  let b := n.log2+1
  let d := Fixed.d b
  let P := primorial d
  let A := Fixed.A b
  let T := 6*Fixed.K₁ b*Fixed.B b*P*Fixed.rootBase n*(b^2*Fixed.U b*A)
  let base := (P/2)*A^d
  let q := (T-1)/base+1
  have dp : 2 ≤ d := by change 10004 ≤ d at big; omega
  have bp : 0 < b := Nat.succ_pos _
  have mp : 0 < Fixed.rootBase n := by simp [Fixed.rootBase]
  have pp := primorial_pos d
  have ap : 0 < A := Nat.pow_pos (by decide)
  have kp : 0 < Fixed.K₁ b := Nat.pow_pos (by decide)
  have Bp : 0 < Fixed.B b := Nat.pow_pos (by decide)
  have up : 0 < Fixed.U b := Nat.pow_pos (by decide)
  have fit := (Fixed.stage_guards hn big).gaussian.2
  have aFits : A^d ≤ Fixed.U b := (Nat.le_mul_of_pos_left _ (by omega : 0 < d)).trans fit
  have baseFit : base ≤ T := by
    change (P/2)*A^d ≤ _
    calc _ ≤ P*Fixed.U b := Nat.mul_le_mul (Nat.div_le_self _ _) aFits
         _ ≤ (6*Fixed.K₁ b*Fixed.B b*Fixed.rootBase n*b^2*A)*(P*Fixed.U b) :=
           Nat.le_mul_of_pos_left _ (by positivity)
         _ = T := by dsimp [T]; ring
  have basepos : 0 < base := Nat.mul_pos
    (Nat.div_pos (Nat.le_of_dvd pp (Nat.prime_two.dvd_primorial_iff.mpr dp)) (by decide)) (Nat.pow_pos ap)
  have rq : base*((T-1)/base) ≤ T-1 := Nat.mul_div_le ..
  have upper : amplitude n ≤ 9*T := by
    calc amplitude n = base*3^(max 1 (Nat.clog 3 q)) := by
           change (P/2*3^(max 1 (Nat.clog 3 q)))*A^d = _; dsimp only [base]; ring
         _ ≤ base*(3*(q+1)) := Nat.mul_le_mul_left _ (clog_three_upper q)
         _ = 3*(base*((T-1)/base)+base+base) := by dsimp [q]; ring
         _ ≤ _ := by omega
  have lower := leading_amplitude (n := n) dp
  have eq : T = 6*Fixed.K₁ b*b^2*referenceWidth n := by dsimp [T,referenceWidth,b,P,d,A]; ring
  change T ≤ amplitude n at lower
  rw [eq] at lower upper
  exact ⟨lower,upper.trans_eq (by ring)⟩

/-- All marks in the fixed grid stay away from the ideal polynomial zeroes.
    At most one factor can be closer than one quarter of the mesh. -/
theorem grid_ideal_value {n a : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1))
    (cap : a ≤ Fixed.A (n.log2+1))
    (grid : onGrid (Fixed.d (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.invWidth (n.log2+1)) a)
    (side : Bool) :
    let b := n.log2+1; let h := Fixed.h b
    let t := (a:ℚ)/Fixed.A b
    (1/2:ℚ)^(4*h) ≤ |idealValue (Fixed.d b) side t| ∧ |idealValue (Fixed.d b) side t| ≤ 1 := by
  let b := n.log2+1
  let d := Fixed.d b
  let W := Fixed.invWidth b
  let h := Fixed.h b
  let t := (a:ℚ)/Fixed.A b
  have dp : 0 < d := by change 10004 ≤ d at big; omega
  have bp : 0 < b := Nat.succ_pos _
  have zp : 0 < Fixed.z b := Nat.succ_pos _
  have ap : 0 < Fixed.A b := Nat.pow_pos (by decide)
  have hp : 0 < h := Nat.mul_pos dp zp
  have one : |t| ≤ 1 := by
    rw [abs_of_nonneg (by dsimp [t]; positivity)]
    exact (div_le_one (by exact_mod_cast ap)).mpr (by exact_mod_cast cap)
  let s := Finset.range d
  have ne : s.Nonempty := ⟨0,Finset.mem_range.mpr dp⟩
  obtain ⟨j,hj,minimal⟩ := s.exists_min_image (fun i => |t-center d side i|) ne
  let r := (1:ℚ)/(4*d)
  have rp : 0 < r := by dsimp [r]; positivity
  have far (i : ℕ) (hi : i ∈ s.erase j) : r ≤ |t-center d side i| := by
    have mem := Finset.mem_erase.mp hi
    have dist : 2*r ≤ |center d side i-center d side j| := by
      rcases lt_or_gt_of_ne mem.1 with lt | gt
      · rw [abs_sub_comm]; exact (show 2*r = 2/(4*(d:ℚ)) by dsimp [r]; ring) ▸
          (center_gap dp lt side).trans (le_abs_self _)
      · exact (show 2*r = 2/(4*(d:ℚ)) by dsimp [r]; ring) ▸
          (center_gap dp gt side).trans (le_abs_self _)
    have tri := abs_sub_le (center d side i) t (center d side j)
    rw [abs_sub_comm (center d side i) t] at tri
    linarith [minimal _ mem.2]
  have closest := grid_separation (Fixed.stage_guards hn big).roots.1 grid side ⟨j,Finset.mem_range.mp hj⟩
  have others : r^(d-1) ≤ ∏ i ∈ s.erase j, |t-center d side i| := by
    simpa [s,Finset.card_erase_of_mem hj] using Finset.prod_le_prod (fun _ _ => rp.le) far
  have gridProd : (W:ℚ)⁻¹*r^(d-1) ≤ |idealValue d side t| := by
    rw [idealValue,Finset.abs_prod,←Finset.prod_erase_mul _ _ hj,mul_comm]
    exact mul_le_mul others closest (by positivity) (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
  have degree : d^3 ≤ b := (Nat.le_mul_of_pos_right _ zp).trans (Fixed.degree_floor b).1
  have trivial : 4*d ≤ d^3 := by have hh : 2≤d := by change 10004≤d at big; omega
                                 nlinarith [Nat.mul_le_mul_left d (Nat.pow_le_pow_left hh 2)]
  have strength : (4*d)^(d-1) ≤ 2^h := by
    apply (Nat.pow_le_pow_left (trivial.trans (degree.trans Nat.lt_log2_self.le)) (d-1)).trans
    rw [←Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) ((Nat.mul_le_mul_left _ (Nat.sub_le d 1)).trans_eq (Nat.mul_comm ..))
  have total : W*(4*d)^(d-1) ≤ 2^(4*h) := by
    calc _ ≤ 2^(3*h)*2^h := Nat.mul_le_mul_left W strength
         _ = _ := by rw [←Nat.pow_add]; congr 1; omega
  have low : (1/2:ℚ)^(4*h) ≤ (W:ℚ)⁻¹*r^(d-1) := by
    simp only [r,one_div,inv_pow,←mul_inv]
    apply inv_anti₀ (show (0:ℚ) < (W:ℚ)*((4:ℚ)*d)^(d-1) by dsimp [W,Fixed.invWidth]; positivity)
    exact_mod_cast total
  have oneProd : |idealValue d side t| ≤ 1 := by
    rw [idealValue,Finset.abs_prod]
    apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
    intro i hi
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have t1 := (abs_le.mp one).2
    obtain ⟨left,right⟩ := center_range (Finset.mem_range.mp hi) side
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  exact ⟨low.trans gridProd,oneProd⟩

end Cogentic.Construction
