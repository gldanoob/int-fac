import Cogentic.BinaryBisectionCost
import Cogentic.RootLogCost
import Cogentic.MarkDistanceCost

namespace Cogentic.BinaryRootColumns
open BinaryDivision BinaryPivot
abbrev Point := SignedWord × List Bool

/-- Use the binary bisection output directly. The distance routine charges
the comparison, gcd and reduction before evaluating the logarithm. -/
def logFromRoot (s : Marking.Input) (a P : ℕ) : Option Point → Option ℤ × ℕ
  | none => (none,0)
  | some t => BinaryMarkDistance.markLog a.bits s.A.bits t.1 t.2 s.L₀ (2*P+16)

/-- Compute each root once for all marks. A failed root contributes its
full isolation cost and no per-mark logarithm work. -/
def work (s : Marking.Input) (rel : Marking.Relations) : ℕ :=
  let P := TryPair.localBits s rel
  ∑ side : Bool, ∑ j : Fin s.degree,
    let root := BinaryBisection.isolate s side j (2*P)
    root.2+∑ i : Fin rel.marks.length,(logFromRoot s (rel.marks.get i) P root.1).2

theorem emitted_den_positive (s : Marking.Input) (side : Bool) (j : Fin s.degree) (bits : ℕ)
    (t : Point) (found : (BinaryBisection.isolate s side j bits).1=some t) : 0<value t.2 := by
  let k := (19*s.K₁.log2+19)/20
  let g := (BinaryBisection.initial s.degree.bits j.val.bits side k).1
  have pos := (BinaryBisection.initial_value s side j).2
  have rp := (BinaryBisection.refine_value s.A.bits (s.coeffs side) bits g pos).2
  change (BinaryBisection.isolateGrid s.A.bits ((s.coeffs side).map encode) bits g).1=some t at found
  dsimp only [BinaryBisection.isolateGrid] at found
  split at found
  · cases Option.some.inj found
    simpa [value] using rp
  · cases found

/-- Each decoded fixed-point word equals the original guarded rational
calculation, for positive A and for both bisection and distance failures. -/
theorem entry_value (s : Marking.Input) (Ap : 0<s.A) (a P : ℕ) (side : Bool) (j : Fin s.degree) :
    let bits := 2*P+16
    (logFromRoot s a P (BinaryBisection.isolate s side j (2*P)).1).1.map (fun (z:ℤ)=>(z:ℚ)/2^bits) =
      (RootLogs.isolate s side j (2*P)).bind (fun x=>RootLogs.markLog s.A a x s.L₀ bits) := by
  intro bits
  rw [←BinaryBisection.isolate_value]
  cases out : (BinaryBisection.isolate s side j (2*P)).1 with
  | none => rfl
  | some t =>
    have den := emitted_den_positive s side j _ t out
    let W := a.bits.length+s.A.bits.length+t.1.digits.length+t.2.length+s.L₀
    have v := (BinaryMarkDistance.markLog_spec a.bits s.A.bits t.1 t.2 s.L₀ bits W
      (by simpa using Ap) den (by dsimp [W];omega) (by dsimp [W];omega) (by dsimp [W];omega)
      (by dsimp [W];omega) (by dsimp [W];omega)).1
    simp only [value_bits] at v
    exact v

/-- All root and mark-log Boolean arithmetic after stage one, including
attempts rejected by either guard, on a fixed-schedule candidate. -/
theorem fixed_work {n g : ℕ} {pair : TryPair.PairData} {rel : Marking.Relations}
    (marked : Marking.stageOne (TryPair.fixedInput n g pair)=some rel) :
    work (TryPair.fixedInput n g pair) rel ≤ 2^(20000*TwoThirdsCost.scale (n.log2+1)) := by
  let b := n.log2+1; let S := TwoThirdsCost.scale b; let s := TryPair.fixedInput n g pair
  let P := TryPair.localBits s rel; let W := 2^(1013*S);let C := 2^25*(65536*W)^6
  have hb : 0<b := Nat.succ_pos _
  have hs : Fixed.h b≤S := (Nat.le_mul_of_pos_left _ (Fixed.degree_pos hb)).trans (Fixed.scale_bounds hb).1
  have zs : Fixed.z b≤S := (Nat.le_mul_of_pos_left _ (Fixed.degree_pos hb)).trans hs
  have sp : 0<S := (Nat.succ_pos b.log2).trans_le zs
  have dz : s.degree≤2^S := (Fixed.degree_le_bits b).trans
    (Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right Nat.zero_lt_two zs))
  have sw : 2^S≤W := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  have ss : S≤W := (Nat.lt_two_pow_self (n:=S)).le.trans sw
  have dw : s.degree.size≤W := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (dz.trans sw)
  have pw : P≤W := BinaryHelmert.fixed_local_bits marked
  have wp : 0<W := Nat.two_pow_pos _
  have area : s.A.size=10000*Fixed.h b+1 := by change (2^(10000*Fixed.h b)).size=_; rw [Nat.size_pow]
  have band : (19*s.K₁.log2+19)/20=95*Fixed.h b := by
    change (19*(2^(100*Fixed.h b)).log2+19)/20=_;rw [Nat.log2_two_pow];omega
  have bW : s.L₀≤W := (Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right Nat.zero_lt_two zs)).trans sw
  let width := s.L₀+s.degree.size+1+95*Fixed.h b+5
  have widthBound : width+2*P+1≤128*W := by dsimp only [width];omega
  have co : s.degree+1+1≤3*W := by have := dz.trans sw;omega
  have round : BinaryBisection.roundCap (s.degree+1) (width+2*P) ≤ 1200*(3*W)*(8192*W^2)^2 := by
    unfold BinaryBisection.roundCap
    gcongr
    calc
      2+(s.degree+1+1)*(12*(width+2*P+1)+1)
          ≤ 2+(3*W)*(12*(128*W)+1) := by gcongr
      _ ≤ 8192*W^2 := by nlinarith only [wp,Nat.le_mul_self W]
  have w6 : W ≤ W^6 := Nat.le_self_pow (by decide) _
  have rootBound (side : Bool) (j : Fin s.degree) : (BinaryBisection.isolate s side j (2*P)).2≤C := by
    have root := (BinaryBisection.isolate_stage_gates marked side j (2*P)).1
    rw [band] at root
    apply root.trans
    calc
      60*width+(2*P+2)*BinaryBisection.roundCap (s.degree+1) (width+2*P) ≤
          60*(128*W)+(4*W)*(1200*(3*W)*(8192*W^2)^2) := by gcongr <;> omega
      _ ≤ C := by dsimp only [C];nlinarith only [w6]
  have each (side : Bool) (j : Fin s.degree) (i : Fin rel.marks.length) :
      (logFromRoot s (rel.marks.get i) P (BinaryBisection.isolate s side j (2*P)).1).2≤C := by
    cases out : (BinaryBisection.isolate s side j (2*P)).1 with
    | none => exact Nat.zero_le _
    | some t =>
      let a := rel.marks.get i; let x := BinaryBisection.decodePoint t
      let dist := |(a:ℚ)/s.A-x|
      have decoded : RootLogs.isolate s side j (2*P)=some x := by rw [←BinaryBisection.isolate_value,out];rfl
      have ep := ((Marking.retained_iff marked a).mp (rel.marks.get_mem i)).1
      simp only [Marking.Input.eligibleMarks,Finset.mem_sort,Finset.mem_filter] at ep
      have fit : a ≤ s.A := ep.2.2.1
      have Ap : 0<s.A := ep.2.1.trans fit
      have bounds := RootLogs.isolate_distance_width marked (rel.marks.get_mem i) decoded
      change dist.num.natAbs.size≤_ ∧ dist.den.size≤_ at bounds
      rw [area,band] at bounds
      let cap := 10000*Fixed.h b+1+s.degree.size+95*Fixed.h b+2*P+5
      change dist.num.natAbs.size≤cap ∧ dist.den.size≤cap at bounds
      dsimp only [cap] at bounds
      have hW : 2*P+16+dist.num.natAbs.size+dist.den.size+8≤32768*W := by omega
      have argA : s.A.bits.length≤16384*W := by rw [Nat.size_eq_bits_len,area];omega
      have arga : a.bits.length≤16384*W := (Nat.size_eq_bits_len _).le.trans
        ((Nat.size_le_size fit).trans ((Nat.size_eq_bits_len _).symm.le.trans argA))
      have ww := (BinaryBisection.isolate_stage_gates marked side j (2*P)).2 t (by rw [out];simp)
      rw [band] at ww
      have den := emitted_den_positive s side j (2*P) t out
      have bound := (BinaryMarkDistance.markLog_spec a.bits s.A.bits t.1 t.2 s.L₀ (2*P+16) (16384*W)
        (by simpa using Ap) den arga argA (ww.1.trans (widthBound.trans (by omega))) (ww.2.trans (widthBound.trans (by omega)))
        (by omega)).2
      simp only [value_bits] at bound
      change _≤10000*(16384*W+1)^3+16777216*(2*P+16+dist.num.natAbs.size+dist.den.size+8)^5 at bound
      have common : (16384*W+1)^3≤(65536*W)^6 :=
        (Nat.pow_le_pow_left (by omega) 3).trans (Nat.pow_le_pow_right (by positivity) (by decide : 3≤6))
      have other : (2*P+16+dist.num.natAbs.size+dist.den.size+8)^5≤(65536*W)^6 :=
        (Nat.pow_le_pow_left (hW.trans (by omega : 32768*W≤65536*W)) 5).trans
          (Nat.pow_le_pow_right (by positivity) (by decide : 5≤6))
      apply bound.trans
      dsimp only [C];omega
  have marks : rel.marks.length≤2^(10000*S) := (Concrete.retained_size marked).trans
    (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_left _ hs))
  have one (side : Bool) (j : Fin s.degree) :
      (BinaryBisection.isolate s side j (2*P)).2 + (∑ i : Fin rel.marks.length,(logFromRoot s (rel.marks.get i) P
        (BinaryBisection.isolate s side j (2*P)).1).2) ≤ C+rel.marks.length*C := by
    have h := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>each side j i)
    apply Nat.add_le_add (rootBound side j)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using h
  have count := Finset.sum_le_sum (s:=Finset.univ) (fun side _=>Finset.sum_le_sum (s:=Finset.univ) (fun j _=>one side j))
  have num : rel.marks.length+1≤2^(1+10000*S) := by rw [pow_add,pow_one];have := Nat.two_pow_pos (10000*S);omega
  change work s rel≤2^(20000*S)
  calc
    _ ≤ 2*(s.degree*(C+rel.marks.length*C)) := by
      simpa only [work,Finset.sum_const,Finset.card_univ,Fintype.card_fin,Fintype.card_bool,smul_eq_mul] using count
    _ = 2*(s.degree*((rel.marks.length+1)*C)) := by ring
    _ ≤ 2^1*(2^S*(2^(1+10000*S)*(2^25*(2^16*W)^6))) := by dsimp only [C];gcongr <;> decide
    _ = 2^(1+(S+(1+10000*S+(25+(16+1013*S)*6)))) := by dsimp only [W];simp only [←pow_add,←pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)

end Cogentic.BinaryRootColumns

#print axioms Cogentic.BinaryRootColumns.entry_value
#print axioms Cogentic.BinaryRootColumns.fixed_work
