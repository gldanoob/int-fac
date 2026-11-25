import Cogentic.ConstructionGeometry

namespace Cogentic.Construction

private theorem center_scale {d : ℕ} (dp : 0 < d) (side : Bool) (j : ℕ) :
    center d side j*(4*d) = (2*j + if side then 2 else 1 : ℕ) := by
  exact div_mul_cancel₀ _ (by positivity)

private theorem center_gap {d i j : ℕ} (dp : 0 < d) (ij : i < j) (side : Bool) :
    2/(4*d : ℚ) ≤ center d side j-center d side i := by
  apply (div_le_iff₀ (by positivity)).mpr
  rw [sub_mul,center_scale dp,center_scale dp]
  have diff : (2*i + (if side then 2 else 1 : ℕ)) + 2 ≤ 2*j+(if side then 2 else 1) := by omega
  have q : ((2*i + if side then 2 else 1 : ℕ):ℚ) + 2 ≤ ((2*j + if side then 2 else 1 : ℕ):ℚ) := by exact_mod_cast diff
  linarith

private theorem bracket_product {d j : ℕ} (side : Bool) (hj : j < d) {δ : ℚ} (pos : 0 < δ)
    (width : δ ≤ 1/(4*d : ℚ)) :
    let left := center d side j-δ
    let right := center d side j+δ
    idealValue d side left * idealValue d side right < 0 ∧
    δ*(1/(4*d:ℚ))^(d-1) ≤ |idealValue d side left| ∧
    δ*(1/(4*d:ℚ))^(d-1) ≤ |idealValue d side right| := by
  let s := (Finset.range d).erase j
  let c := center d side j
  let L := fun i => c-δ-center d side i
  let R := fun i => c+δ-center d side i
  let v := 1/(4*d:ℚ)
  have dp : 0 < d := by omega
  have good : (0:ℚ) < v := by dsimp [v]; positivity
  have two : (2:ℚ)/(4*d) = 2*v := by dsimp [v]; ring
  have each (i : ℕ) (hi : i ∈ s) : 0 < L i*R i ∧ v ≤ |L i| ∧ v ≤ |R i| := by
    have ne := (Finset.mem_erase.mp hi).1
    change δ ≤ v at width
    rcases lt_or_gt_of_ne ne with low | high
    · have sep := center_gap dp low side
      rw [two] at sep
      have l : v ≤ L i := by dsimp [L,c]; linarith
      have r : v ≤ R i := by dsimp [R,c]; linarith
      exact ⟨mul_pos (good.trans_le l) (good.trans_le r),l.trans (le_abs_self _),r.trans (le_abs_self _)⟩
    · have sep := center_gap dp high side
      rw [two] at sep
      have l : v ≤ -L i := by dsimp [L,c]; linarith
      have r : v ≤ -R i := by dsimp [R,c]; linarith
      exact ⟨mul_pos_of_neg_of_neg (by linarith) (by linarith),
        l.trans (neg_le_abs _),r.trans (neg_le_abs _)⟩
  have member := Finset.mem_range.mpr hj
  have left : idealValue d side (c-δ) = (∏ i ∈ s, L i)*(-δ) := by
    change (∏ i ∈ Finset.range d, L i) = _
    rw [←Finset.prod_erase_mul _ _ member]
    simp [s,L,c]
  have right : idealValue d side (c+δ) = (∏ i ∈ s, R i)*δ := by
    change (∏ i ∈ Finset.range d, R i) = _
    rw [←Finset.prod_erase_mul _ _ member]
    simp [s,R,c]
  have prod : 0 < (∏ i ∈ s, L i)*(∏ i ∈ s, R i) := by
    rw [←Finset.prod_mul_distrib]; exact Finset.prod_pos (fun i hi => (each i hi).1)
  have card : s.card = d-1 := by simp [s,member,Finset.card_erase_of_mem]
  have mag (f : ℕ → ℚ) (lower : ∀ i ∈ s, v ≤ |f i|) : v^(d-1) ≤ |∏ i ∈ s, f i| := by
    rw [Finset.abs_prod]
    simpa [card] using Finset.prod_le_prod (fun _ _ => good.le) lower
  change idealValue d side (c-δ)*idealValue d side (c+δ) < 0 ∧ _
  rw [left,right]
  constructor
  · calc _ = ((∏ i ∈ s, L i)*(∏ i ∈ s, R i))*(-(δ^2)) := by ring
         _ < 0 := mul_neg_of_pos_of_neg prod (neg_neg_of_pos (pow_pos pos 2))
  · simp only [abs_mul,abs_neg,abs_of_pos pos]
    constructor
    · simpa [v,mul_comm] using (mul_le_mul_of_nonneg_left (mag L (fun i hi => (each i hi).2.1)) pos.le)
    · simpa [v,mul_comm] using (mul_le_mul_of_nonneg_left (mag R (fun i hi => (each i hi).2.2)) pos.le)

private def radius (b : ℕ) : ℚ := (1/2:ℚ)^(95*Fixed.h b)

private theorem bracket_scale {n : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1)) :
    let b := n.log2+1
    let d := Fixed.d b
    0 < radius b ∧ radius b ≤ 1/(4*d : ℚ) ∧
      (1:ℚ)/(Fixed.K₁ b) < radius b*(1/(4*d:ℚ))^(d-1) := by
  let b := n.log2+1
  let d := Fixed.d b
  let h := Fixed.h b
  have bp : 0 < b := by simp [b]
  have dp : 0 < d := Fixed.degree_pos bp
  have zp : 0 < Fixed.z b := by simp [Fixed.z]
  have hp : 0 < h := Nat.mul_pos dp zp
  have k8 := (Fixed.stage_guards hn big).roots.2.1
  have br : Fixed.bracketExponent b = 95*h := by unfold Fixed.bracketExponent; dsimp [h]; omega
  change 8*d < 2^Fixed.bracketExponent b at k8
  rw [br] at k8
  have fit : 4*d ≤ 2^(95*h) := by omega
  have small : (4*d)^(d-1) ≤ 2^(3*h) := by
    have db : d ≤ 2^Fixed.z b := (Fixed.degree_le_bits b).trans Nat.lt_log2_self.le
    have base : 4*d ≤ 2^(2+Fixed.z b) := (Nat.mul_le_mul_left 4 db).trans_eq (Nat.pow_add 2 2 _).symm
    apply (Nat.pow_le_pow_left base _).trans
    rw [←Nat.pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    calc (2+Fixed.z b)*(d-1) ≤ (3*Fixed.z b)*d := Nat.mul_le_mul (by omega) (Nat.sub_le ..)
         _ = _ := by change _ = 3*(d*Fixed.z b); ring
  have separation : 2^(95*h)*(4*d)^(d-1) < 2^(100*h) := by
    calc _ ≤ 2^(95*h)*2^(3*h) := Nat.mul_le_mul_left _ small
         _ = 2^(95*h+3*h) := (Nat.pow_add ..).symm
         _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)
  have fQ : (4:ℚ)*d ≤ 2^(95*h) := by exact_mod_cast fit
  have sQ : (2:ℚ)^(95*h)*(4*d)^(d-1) < 2^(100*h) := by exact_mod_cast separation
  change 0 < (1/2:ℚ)^(95*h) ∧ (1/2:ℚ)^(95*h) ≤ 1/(4*d) ∧
    (1:ℚ)/((2:ℕ)^(100*h):ℕ) < (1/2:ℚ)^(95*h)*(1/(4*d))^(d-1)
  push_cast
  rw [one_div_pow,one_div_pow,one_div_mul_one_div]
  exact ⟨by positivity,one_div_le_one_div_of_le (by positivity) fQ,
    one_div_lt_one_div_of_lt (by positivity) sQ⟩

private theorem center_range {j d : ℕ} (hj : j < d) (side : Bool) :
    0 ≤ center d side j ∧ center d side j ≤ 1/2 := by
  have dp : 0 < d := by omega
  have amount : 2*j+(if side then 2 else 1 : ℕ) ≤ 2*d := by cases side <;> simp <;> omega
  refine ⟨by unfold center; positivity,?_⟩
  apply (div_le_iff₀ (by positivity : (0:ℚ) < 4*d)).mpr
  calc ((2*j + if side then 2 else 1 : ℕ):ℚ) ≤ 2*(d:ℚ) := by exact_mod_cast amount
       _ = _ := by ring

/-- All initial bracket sign tests used by `RootLogs.isolate` succeed on both
    coefficient lists, uniformly in the perturbation box. -/
theorem constructed_bracket_sign {n ell u₀ u₁ v₀ v₁ : ℕ} (hn : 2 ≤ n)
    (big : 10004 ≤ Fixed.d (n.log2+1)) (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (box : let b := n.log2+1
      u₀ ≤ 2*b^2*Fixed.U b*Fixed.A b ∧ u₁ ≤ 2*b^2*Fixed.U b ∧
      v₀ ≤ 2*b^2*Fixed.U b*Fixed.A b ∧ v₁ ≤ 2*b^2*Fixed.U b) :
    let s := TryPair.fixedInput n ell (construct n ell u₀ u₁ v₀ v₁)
    ∀ side (j : Fin s.degree), let c := RootLogs.bracket s side j
      RootLogs.normalized s.A (s.coeffs side) c.left * RootLogs.normalized s.A (s.coeffs side) c.right < 0 := by
  let b := n.log2+1
  let d := Fixed.d b
  let A := Fixed.A b
  let c := leadingCoefficient n
  let s := TryPair.fixedInput n ell (construct n ell u₀ u₁ v₀ v₁)
  let S : ℚ := c*(A:ℚ)^d
  let K : ℚ := Fixed.K₁ b
  have dpos : 0 < d := by change 10004 ≤ d at big; omega
  have amp := leading_amplitude (n := n) (by omega : 2 ≤ Fixed.d (n.log2+1))
  have cpos : 0 < c := by
    have ppos := primorial_pos (Fixed.d b)
    have mp : 0 < Fixed.rootBase n := by simp [Fixed.rootBase]
    have bp : 0 < b := by simp [b]
    have apos : 0 < Fixed.A b := Nat.pow_pos (by decide)
    have upos : 0 < Fixed.U b := Nat.pow_pos (by decide)
    have kpos : 0 < Fixed.K₁ b := Nat.pow_pos (by decide)
    have bpos : 0 < Fixed.B b := Nat.pow_pos (by decide)
    have t : 0 < 6*Fixed.K₁ b*Fixed.B b*primorial (Fixed.d b)*Fixed.rootBase n*(b^2*Fixed.U b*Fixed.A b) := by positivity
    exact Nat.pos_of_mul_pos_right (t.trans_le amp)
  have ap : 0 < A := Nat.pow_pos (by decide)
  have sPos : 0 < S := by dsimp [S]; positivity
  obtain ⟨rPos,rWidth,rCap⟩ := bracket_scale hn big
  change 0 < radius b at rPos
  change radius b ≤ 1/(4*d:ℚ) at rWidth
  change 1/K < radius b*(1/(4*d:ℚ))^(d-1) at rCap
  change ∀ side (j : Fin s.degree), _
  intro side j
  have low := bracket_product side (show j.val < d from j.isLt) rPos rWidth
  let x := center d side j.val-radius b
  let y := center d side j.val+radius b
  change idealValue d side x*idealValue d side y < 0 ∧ _ at low
  have ctr := center_range (show j.val < d from j.isLt) side
  have narrow : radius b ≤ 1/2 := rWidth.trans (one_div_le_one_div_of_le (by norm_num) (by
    have q : (1:ℚ) ≤ d := by exact_mod_cast dpos
    linarith))
  have xOK : |x| ≤ 1 := abs_le.mpr ⟨by dsimp [x]; linarith [ctr.1],by dsimp [x]; linarith [ctr.2]⟩
  have yOK : |y| ≤ 1 := abs_le.mpr ⟨by dsimp [y]; linarith [ctr.1],by dsimp [y]; linarith [ctr.2]⟩
  have approx (t : ℚ) (ht : |t| ≤ 1) :
      |RootLogs.normalized A (s.coeffs side) t - S*idealValue d side t| ≤ S/K := by
    cases side with
    | false => exact normalized_error hn big target false ⟨box.1,box.2.1⟩ t ht
    | true => exact normalized_error hn big target true ⟨box.2.2.1,box.2.2.2⟩ t ht
  have sign (t : ℚ) (inRange : |t| ≤ 1) (lower : 1/K < |idealValue d side t|) :
      (0 < idealValue d side t → 0 < RootLogs.normalized A (s.coeffs side) t) ∧
      (idealValue d side t < 0 → RootLogs.normalized A (s.coeffs side) t < 0) := by
    have L : S/K < S*|idealValue d side t| := by simpa [div_eq_mul_inv] using mul_lt_mul_of_pos_left lower sPos
    have error := abs_le.mp (approx t inRange)
    constructor
    · intro pos; rw [abs_of_pos pos] at L; linarith
    · intro neg; rw [abs_of_neg neg,mul_neg] at L; linarith
  have sx := sign x xOK (rCap.trans_le low.2.1)
  have sy := sign y yOK (rCap.trans_le low.2.2)
  have actual : RootLogs.normalized A (s.coeffs side) x * RootLogs.normalized A (s.coeffs side) y < 0 := by
    rcases mul_neg_iff.mp low.1 with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact mul_neg_of_pos_of_neg (sx.1 hx) (sy.2 hy)
    · exact mul_neg_of_neg_of_pos (sx.2 hx) (sy.1 hy)
  have br : (19*(Fixed.K₁ b).log2+19)/20 = 95*Fixed.h b := by rw [Fixed.K₁,Nat.log2_two_pow]; omega
  change RootLogs.normalized A (s.coeffs side) (center d side j.val-(1/2:ℚ)^((19*(Fixed.K₁ b).log2+19)/20)) *
    RootLogs.normalized A (s.coeffs side) (center d side j.val+(1/2:ℚ)^((19*(Fixed.K₁ b).log2+19)/20)) < 0
  rw [br]; exact actual

theorem constructed_isolate {n ell u₀ u₁ v₀ v₁ : ℕ} (hn : 2 ≤ n)
    (big : 10004 ≤ Fixed.d (n.log2+1)) (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (box : let b := n.log2+1
      u₀ ≤ 2*b^2*Fixed.U b*Fixed.A b ∧ u₁ ≤ 2*b^2*Fixed.U b ∧
      v₀ ≤ 2*b^2*Fixed.U b*Fixed.A b ∧ v₁ ≤ 2*b^2*Fixed.U b) :
    let s := TryPair.fixedInput n ell (construct n ell u₀ u₁ v₀ v₁)
    ∀ side (j : Fin s.degree) bits, ∃ t, RootLogs.isolate s side j bits = some t ∧
      ∃ x ∈ Set.Icc ((RootLogs.bracket s side j).left:ℝ) ((RootLogs.bracket s side j).right:ℝ),
        RootLogs.normalized s.A (s.coeffs side) x = 0 ∧ |(t:ℝ)-x| ≤ (1/2:ℝ)^bits := by
  dsimp only
  intro side j bits
  have sign := constructed_bracket_sign hn big target box side j
  let s := TryPair.fixedInput n ell (construct n ell u₀ u₁ v₀ v₁)
  have hit : ∃ t, RootLogs.isolate s side j bits = some t := by
    unfold RootLogs.isolate
    rw [if_pos sign]; exact ⟨_,rfl⟩
  obtain ⟨t,eq⟩ := hit
  exact ⟨t,eq,RootLogs.isolate_correct eq⟩

theorem brackets_ordered {n : ℕ} (hn : 2 ≤ n) (big : 10004 ≤ Fixed.d (n.log2+1))
    (ell : ℕ) (data : TryPair.PairData) :
    let s := TryPair.fixedInput n ell data
    ∀ side (i j : Fin s.degree), i < j →
      (RootLogs.bracket s side i).right < (RootLogs.bracket s side j).left := by
  let b := n.log2+1
  let d := Fixed.d b
  dsimp only
  intro side i j h
  have dpos : 0 < d := by change 10004 ≤ d at big; omega
  have separation := center_gap dpos (show i.val < j.val from h) side
  have k8 := (Fixed.stage_guards hn big).roots.2.1
  change 8*d < 2^Fixed.bracketExponent b at k8
  have br : Fixed.bracketExponent b = 95*Fixed.h b := by unfold Fixed.bracketExponent; omega
  rw [br] at k8
  have half : (1/2:ℚ)^(95*Fixed.h b) < 1/(4*d) := by
    rw [one_div_pow]
    apply one_div_lt_one_div_of_lt (by positivity)
    exact_mod_cast (by omega : 4*d < 2^(95*Fixed.h b))
  have br' : (19*(Fixed.K₁ b).log2+19)/20 = 95*Fixed.h b := by rw [Fixed.K₁,Nat.log2_two_pow]; omega
  change center d side i.val+(1/2:ℚ)^((19*(Fixed.K₁ b).log2+19)/20) <
    center d side j.val-(1/2:ℚ)^((19*(Fixed.K₁ b).log2+19)/20)
  rw [br']
  have two : (2:ℚ)/(4*d) = 2*(1/(4*d:ℚ)) := by ring
  rw [two] at separation
  linarith

end Cogentic.Construction

#print axioms Cogentic.Construction.constructed_isolate
