import Cogentic.PowerScanCost

namespace Cogentic.BinarySchedule
open BinaryDivision BinarySaturation BinaryIndexCap

/-- Canonical binary length of a list, counting the dispatch for the list map. -/
def lengthWord {α : Type*} (xs : List α) : List Bool × ℕ :=
  let c := count (xs.map fun _ => false)
  let w := canonical c.1
  (w.1, xs.length + c.2 + w.2)

theorem lengthWord_spec {α : Type*} (xs : List α) :
    (lengthWord xs).1 = xs.length.bits ∧ (lengthWord xs).2 ≤ 8*(xs.length+1)^2 := by
  let bs := xs.map fun _ => false
  obtain ⟨v,l,g⟩ := count_spec bs
  obtain ⟨w,c⟩ := canonical_spec (count bs).1
  rw [v] at w
  rw [l] at c
  simp only [bs,List.length_map] at w c g
  exact ⟨w,by change xs.length + (count bs).2 + (canonical _).2 ≤ _; nlinarith only [c,g]⟩

/-- Unary exponents are copied by list traversal. -/
def copies {α β : Type*} (ys : List β) : List α → List β × ℕ
  | [] => ([],1)
  | _ :: xs =>
    let t := copies ys xs
    (ys ++ t.1, ys.length+1+t.2)

theorem copies_spec {α β : Type*} (ys : List β) (xs : List α) :
    (copies ys xs).1.length = xs.length*ys.length ∧ (copies ys xs).2 = xs.length*(ys.length+1)+1 := by
  induction xs with
  | nil => simp [copies]
  | cons a xs ih => simp only [copies,List.length_append,List.length_cons,ih.1,ih.2,Nat.succ_mul]; omega

/-- Emit a power of two by prefixing zeros to its single set bit. -/
def shiftOne {α : Type*} : List α → List Bool × ℕ
  | [] => ([true],1)
  | _ :: xs =>
    let r := shiftOne xs
    (false :: r.1, r.2+1)

theorem shiftOne_spec {α : Type*} (xs : List α) :
    (shiftOne xs).1=(2^xs.length : ℕ).bits ∧ (shiftOne xs).2=xs.length+1 := by
  induction xs with
  | nil => simp [shiftOne]
  | cons a xs ih =>
    simp only [shiftOne,List.length_cons,ih.1,ih.2,pow_succ]
    rw [Nat.mul_comm _ 2,Nat.bit0_bits _ (Nat.two_pow_pos _).ne']; simp

private def scaledPower (c : ℕ) (xs : List Unit) : List Bool × ℕ :=
  let exp := copies xs (List.replicate c ())
  let out := shiftOne exp.1
  (out.1, c+exp.2+out.2)

private theorem scaledPower_spec (c : ℕ) (xs : List Unit) :
    (scaledPower c xs).1=(2^(c*xs.length):ℕ).bits ∧ (scaledPower c xs).2≤4*(c+1)*(xs.length+1) := by
  obtain ⟨l,w⟩ := copies_spec xs (List.replicate c ())
  simp only [List.length_replicate] at l w
  obtain ⟨v,cost⟩ := shiftOne_spec (copies xs (List.replicate c ())).1
  rw [l] at v cost
  exact ⟨v,by dsimp only [scaledPower]; rw [cost,w]; nlinarith⟩

structure Words where
  bits : List Bool
  degree : List Bool
  beta : List Bool
  B : List Bool
  A : List Bool
  K₁ : List Bool
  invWidth : List Bool
  U : List Bool

/-- Compute the shared schedule from the input bits themselves. -/
def run (n : List Bool) : Words × ℕ :=
  let b := lengthWord n
  let d := BinaryPowerScan.degreeFuel n
  let dw := lengthWord d.1
  let h := copies (b.1.map fun _ => ()) d.1
  let v := copies h.1 d.1
  let beta := copies h.1 (List.replicate 1000 ())
  let bw := lengthWord beta.1
  let B := shiftOne beta.1
  let A := scaledPower 10000 h.1
  let K := scaledPower 100 h.1
  let I := scaledPower 3 h.1
  let U := scaledPower 100000 v.1
  (⟨b.1,dw.1,bw.1,B.1,A.1,K.1,I.1,U.1⟩,
    b.2+d.2+dw.2+b.1.length+h.2+v.2+1000+beta.2+bw.2+B.2+A.2+K.2+I.2+U.2+13)

private theorem word_cost_cap {b d h z v X : ℕ} (bx : b+1≤X) (dx : d≤X)
    (hx : h≤X) (zx : z≤X) (vx : v≤X) :
    8*(b+1)^2+256*(b+1)^4+8*(d+1)^2+z+
            (d*(z+1)+1)+(d*(h+1)+1)+1000+
            (1000*(h+1)+1)+8*(1000*h+1)^2+(1000*h+1)+
            4*(10000+1)*(h+1)+4*(100+1)*(h+1)+4*(3+1)*(h+1)+
            4*(100000+1)*(v+1)+13 ≤ 2^25*(X+1)^4 := by
  calc
    _ ≤ 8*X^2+256*X^4+8*(X+1)^2+X+(X*(X+1)+1)+(X*(X+1)+1)+1000+
        (1000*(X+1)+1)+8*(1000*X+1)^2+(1000*X+1)+4*(10000+1)*(X+1)+
        4*(100+1)*(X+1)+4*(3+1)*(X+1)+4*(100000+1)*(X+1)+13 := by gcongr
    _ ≤ _ := by ring_nf; omega

theorem fixed_words (n : List Bool) (pos : 0<n.length) :
    let b := n.length
    let out := run n
    out.1=⟨b.bits,(Fixed.d b).bits,(Fixed.beta b).bits,(Fixed.B b).bits,
      (Fixed.A b).bits,(Fixed.K₁ b).bits,(Fixed.invWidth b).bits,(Fixed.U b).bits⟩ ∧
    out.2 ≤ 2^(34*TwoThirdsCost.scale b) := by
  intro b out
  let d := (BinaryPowerScan.degreeFuel n).1
  let bw := (lengthWord n).1
  let h := (copies (bw.map fun _ => ()) d).1
  let v := (copies h d).1
  let beta := (copies h (List.replicate 1000 ())).1
  obtain ⟨bl,bc⟩ := lengthWord_spec n
  have bz : bw.length = Fixed.z b := by
    change (lengthWord n).1.length = _
    rw [bl,Nat.size_eq_bits_len]
    exact Nat.le_antisymm (Nat.size_le.mpr Nat.lt_log2_self) (Nat.lt_size.mpr (Nat.log2_self_le pos.ne'))
  obtain ⟨dl,dc⟩ := BinaryPowerScan.degreeFuel_spec n pos
  change d.length=Fixed.d b at dl
  obtain ⟨dw,dwc⟩ := lengthWord_spec d
  rw [dl] at dw dwc
  obtain ⟨hl,hc⟩ := copies_spec (bw.map fun _ => ()) d
  simp only [List.length_map,bz,dl] at hl hc
  change h.length=Fixed.h b at hl
  obtain ⟨vl,vc⟩ := copies_spec h d
  rw [hl,dl] at vl vc
  change v.length=Fixed.v b at vl
  obtain ⟨el,ec⟩ := copies_spec h (List.replicate 1000 ())
  simp only [List.length_replicate,hl] at el ec
  change beta.length=Fixed.beta b at el
  obtain ⟨ew,ewc⟩ := lengthWord_spec beta
  rw [el] at ew ewc
  obtain ⟨B,Bc⟩ := shiftOne_spec beta
  rw [el] at B Bc
  obtain ⟨A,Ac⟩ := scaledPower_spec 10000 h
  obtain ⟨K,Kc⟩ := scaledPower_spec 100 h
  obtain ⟨I,Ic⟩ := scaledPower_spec 3 h
  obtain ⟨U,Uc⟩ := scaledPower_spec 100000 v
  rw [hl] at A Ac K Kc I Ic
  rw [vl] at U Uc
  constructor
  · change Words.mk bw (lengthWord d).1 (lengthWord beta).1 (shiftOne beta).1
        (scaledPower 10000 h).1 (scaledPower 100 h).1 (scaledPower 3 h).1 (scaledPower 100000 v).1 = _
    rw [dw,ew,B,A,K,I,U]
    exact congrArg (fun x => Words.mk x _ _ _ _ _ _ _) bl
  · let S := TwoThirdsCost.scale b
    have dp := Fixed.degree_pos pos
    have vs : Fixed.v b≤S := (Fixed.scale_bounds pos).1
    have hs : Fixed.h b≤S := (Nat.le_mul_of_pos_left _ dp).trans vs
    have zs : Fixed.z b≤S := (Nat.le_mul_of_pos_left _ dp).trans hs
    have ds : Fixed.d b≤S := (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans hs
    have sp : 0<S := (Nat.succ_pos _).trans_le zs
    let X := 2^S
    have sx : S ≤ X := Nat.lt_two_pow_self.le
    have bx : b+1 ≤ X := Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two zs)
    have hx := hs.trans sx
    have vx := vs.trans sx
    have zx := zs.trans sx
    have dx := ds.trans sx
    change _ + _ + _ + bw.length + _ + _ + 1000 + _ + _ + _ + _ + _ + _ + _ + 13 ≤ _
    rw [bz]
    apply le_trans (b := 2^25*(X+1)^4)
    ·
      change (lengthWord n).2+(BinaryPowerScan.degreeFuel n).2+(lengthWord d).2+Fixed.z b+
        (copies (bw.map fun _=>()) d).2+(copies h d).2+1000+(copies h (List.replicate 1000 ())).2+
        (lengthWord beta).2+(shiftOne beta).2+(scaledPower 10000 h).2+
        (scaledPower 100 h).2+(scaledPower 3 h).2+(scaledPower 100000 v).2+13 ≤ _
      rw [hc,vc,ec,Bc]
      change b+1 ≤ X at bx
      change (lengthWord n).2 ≤ 8*(b+1)^2 at bc
      change (BinaryPowerScan.degreeFuel n).2 ≤ 256*(b+1)^4 at dc
      dsimp only [Fixed.beta] at ewc ⊢
      calc
        _ ≤ 8*(b+1)^2+256*(b+1)^4+8*(Fixed.d b+1)^2+Fixed.z b+
            (Fixed.d b*(Fixed.z b+1)+1)+(Fixed.d b*(Fixed.h b+1)+1)+1000+
            (1000*(Fixed.h b+1)+1)+8*(1000*Fixed.h b+1)^2+(1000*Fixed.h b+1)+
            4*(10000+1)*(Fixed.h b+1)+4*(100+1)*(Fixed.h b+1)+4*(3+1)*(Fixed.h b+1)+
            4*(100000+1)*(Fixed.v b+1)+13 := by omega
        _ ≤ _ := word_cost_cap bx dx hx zx vx
    have xp : X+1≤2^(S+1) := by rw [pow_succ]; have : 0<X := Nat.two_pow_pos _; omega
    apply (Nat.mul_le_mul_left (2^25) (Nat.pow_le_pow_left xp 4)).trans
    rw [←pow_mul,←pow_add]
    exact Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
end Cogentic.BinarySchedule
