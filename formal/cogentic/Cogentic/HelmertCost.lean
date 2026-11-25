import Cogentic.PowerScanCost
import Cogentic.Concrete
import Cogentic.ExponentBounds

namespace Cogentic.BinaryHelmert
open BinaryDivision BinaryPivot BinaryPowerScan

/-- The fixed-point numerator of the factor in `Concrete.projection`.
The denominator of the output is implicit in the requested precision. -/
def coefficient (j : List Bool) (bits : ℕ) : List Bool × ℕ :=
  let jp := addDigits j.length j [] true
  let denom := multiply jp.1 j
  let unit := List.replicate (2*bits) false ++ [true]
  let q := divide denom.1 unit
  let r := root q.quotient 2 unit.length []
  (r.1,jp.2+denom.2+unit.length+q.gates+r.2)

private theorem unit_value (k : ℕ) : value (List.replicate k false ++ [true])=2^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ,value,ih,pow_succ,Nat.mul_comm]

theorem coefficient_spec (j : List Bool) (positive : 0<value j) (bits : ℕ) :
    let r := coefficient j bits
    (value r.1:ℚ)/2^bits = ArchNumerics.approxSqrt 1 (value j*(value j+1)) bits ∧
    r.1.length=2*bits+1 ∧ r.2≤1000*(j.length+bits+1)^3 := by
  let jp := addDigits j.length j [] true
  let den := multiply jp.1 j
  let unit := List.replicate (2*bits) false ++ [true]
  let q := divide den.1 unit
  let r := root q.quotient 2 unit.length []
  have ⟨jw,jc,jv⟩ := addDigits_spec j.length j [] true le_rfl (by simp)
  change jp.1.length=_ at jw
  change jp.2=_ at jc
  have jval : value jp.1=value j+1 := by simpa [jp,value] using jv
  have ⟨dv,dw,dc⟩ := multiply_spec jp.1 j
  change value den.1=_ at dv
  change den.1.length≤_ at dw
  change den.2≤_ at dc
  rw [jval] at dv
  rw [jw] at dw dc
  have ul : unit.length=2*bits+1 := by simp [unit]
  have uv : value unit=(2^bits)^2 := (unit_value _).trans (by rw [←pow_mul,Nat.mul_comm])
  have dp : 0<value den.1 := dv ▸ Nat.mul_pos positive (Nat.succ_pos _)
  obtain ⟨_,_,decomp,remSmall,qc⟩ := divide_spec den.1 unit dp
  change value unit=value q.quotient*value den.1+value q.remainder at decomp
  change value q.remainder<value den.1 at remSmall
  change q.gates≤_ at qc
  have qv : value q.quotient=value unit/value den.1 := by
    conv_rhs => rw [decomp,Nat.mul_comm (value q.quotient),Nat.mul_add_div dp,Nat.div_eq_of_lt remSmall,Nat.add_zero]
  have ql : q.quotient.length=unit.length := BinaryIndexCap.quotient_length ..
  obtain ⟨rv,rl,rc⟩ := root_spec q.quotient 2 unit.length unit.length [] ql.le (by simp)
  change value r.1=_ at rv
  change r.1.length=_ at rl
  change r.2≤_ at rc
  simp only [value,Nat.mul_zero,List.length_nil,Nat.zero_add] at rv rl
  have small : value q.quotient<2^unit.length := ql ▸ value_lt q.quotient
  have top : value q.quotient<(0+2^unit.length)^2 := by
    simpa only [Nat.zero_add] using small.trans_le (Nat.le_self_pow (by decide : 2≠0) _)
  obtain ⟨low,high,_⟩ := Fixed.digits_floor (by simp : 0^2≤value q.quotient) top
  rw [←rv] at low high
  have sqrt : value r.1=(value q.quotient).sqrt :=
    Nat.le_antisymm (Nat.le_sqrt'.mpr low) (Nat.le_of_lt_succ (Nat.sqrt_lt'.mpr high))
  refine ⟨?_,rl.trans ul,?_⟩
  · change (value r.1:ℚ)/2^bits=_
    rw [sqrt,qv,uv,dv]
    simp [ArchNumerics.approxSqrt]
  · change jp.2+den.2+unit.length+q.gates+r.2≤_
    have bound := Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add_left dc jp.2) unit.length)
      (Nat.add_le_add (qc.trans (Nat.mul_le_mul_left _ (by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right dw _)) _))) rc)
    rw [jc,ul] at bound
    rw [jc,ul]
    unfold rootStep at bound
    apply (le_of_eq (by omega)).trans bound |>.trans
    ring_nf
    omega

/-- One charge for each mark and projected row, including repeated evaluations
of the same coefficient. Earlier rejection only shortens this sum. -/
def columnsWork (s : Marking.Input) (rel : Marking.Relations) : ℕ :=
  let bits := 2*TryPair.localBits s rel+16
  rel.marks.length * ∑ row : Fin (2*s.degree-2),
    (coefficient (row.val%(s.degree-1)+1).bits bits).2

theorem fixed_local_bits {n g : ℕ} {pair : TryPair.PairData} {rel : Marking.Relations}
    (marked : Marking.stageOne (TryPair.fixedInput n g pair)=some rel) :
    TryPair.localBits (TryPair.fixedInput n g pair) rel≤2^(1013*TwoThirdsCost.scale (n.log2+1)) := by
  let b := n.log2+1
  let S := TwoThirdsCost.scale b
  have hb : 0<b := Nat.succ_pos _
  have hs : Fixed.h b≤S := (Nat.le_mul_of_pos_left _ (Fixed.degree_pos hb)).trans (Fixed.scale_bounds hb).1
  have zs : Fixed.z b≤S := (Nat.le_mul_of_pos_left _ (Fixed.degree_pos hb)).trans hs
  have sp : 0<S := (Nat.succ_pos b.log2).trans_le zs
  have pp : TryPair.localBits (TryPair.fixedInput n g pair) rel≤Fixed.precision b := by
    change 64*(Fixed.d b)^3*(rel.rows.length+1)*b≤64*(Fixed.d b)^3*(2*Fixed.d b*Fixed.B b+1)*b
    gcongr; exact retained_root_row_cap marked
  change _≤2^(1013*S)
  exact pp.trans ((Fixed.precision_bound b).trans
    (Nat.pow_le_pow_right Nat.zero_lt_two (by unfold Fixed.beta; omega)))

theorem fixed_columns_gates {n g : ℕ} {pair : TryPair.PairData} {rel : Marking.Relations}
    (marked : Marking.stageOne (TryPair.fixedInput n g pair)=some rel)
    (big : 2≤Fixed.d (n.log2+1)) :
    columnsWork (TryPair.fixedInput n g pair) rel ≤ 2^(14000*TwoThirdsCost.scale (n.log2+1)) := by
  let b := n.log2+1
  let d := Fixed.d b
  let S := TwoThirdsCost.scale b
  let s := TryPair.fixedInput n g pair
  let P := TryPair.localBits s rel
  have hb : 0<b := Nat.succ_pos _
  have hs : Fixed.h b≤S := (Nat.le_mul_of_pos_left _ (Fixed.degree_pos hb)).trans (Fixed.scale_bounds hb).1
  have zs : Fixed.z b≤S := (Nat.le_mul_of_pos_left _ (Fixed.degree_pos hb)).trans hs
  have sp : 0<S := (Nat.succ_pos b.log2).trans_le zs
  have dz : d≤2^S := (Fixed.degree_le_bits b).trans
    (Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right Nat.zero_lt_two zs))
  have pw : P≤2^(1013*S) := fixed_local_bits marked
  have marks : rel.marks.length≤2^(10000*S) := (Concrete.retained_size marked).trans
    (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_left _ hs))
  have dg : 2≤d := big
  let W := 2^(1013*S)
  have sw : 2^S≤W := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  have one : 1≤W := Nat.two_pow_pos _
  have cell (i : Fin (2*d-2)) :
      (coefficient (i.val%(d-1)+1).bits (2*P+16)).2≤1000*(32*W)^3 := by
    let j := i.val%(d-1)+1
    have jbound : j≤d := by have := Nat.mod_lt i.val (by omega : 0<d-1); dsimp [j]; omega
    have jw : j.bits.length≤W := (Nat.size_eq_bits_len j).le.trans
      ((Nat.size_le.mpr Nat.lt_two_pow_self).trans (jbound.trans (dz.trans sw)))
    have jc := (coefficient_spec j.bits (by simp [j]) (2*P+16)).2.2
    apply jc.trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    change P≤W at pw
    omega
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>cell i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at sum
  have dim : 2*d-2 ≤ 2*2^S := (Nat.sub_le ..).trans (Nat.mul_le_mul_left _ dz)
  change rel.marks.length*_ ≤ 2^(14000*S)
  calc
    _ ≤ 2^(10000*S)*((2*2^S)*(1000*(32*W)^3)) :=
      Nat.mul_le_mul marks (sum.trans (Nat.mul_le_mul_right _ dim))
    _ ≤ 2^(10000*S)*((2^1*2^S)*(2^10*(2^5*W)^3)) := by gcongr <;> decide
    _ = 2^(10000*S+(1+S+(10+(5+1013*S)*3))) := by
      dsimp only [W]; simp only [←pow_add,←pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)

end Cogentic.BinaryHelmert
