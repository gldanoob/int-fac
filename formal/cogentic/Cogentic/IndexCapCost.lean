import Cogentic.CandidateSieveCost

namespace Cogentic.BinaryIndexCap
open BinaryDivision BinaryPivot BinarySaturation

/-- Count the canonical digits in binary, charging the increment and dispatch. -/
def count : List Bool → List Bool × ℕ
  | [] => ([],0)
  | _::xs =>
    let prev := count xs
    let next := addDigits prev.1.length prev.1 [] true
    (next.1,prev.2+next.2+1)

private theorem count_spec (xs : List Bool) : value (count xs).1=xs.length ∧
    (count xs).1.length=xs.length ∧ (count xs).2≤(3*xs.length+1)*xs.length := by
  induction xs with
  | nil => simp [count,value]
  | cons b xs ih =>
    have ⟨len,cost,val⟩ := addDigits_spec (count xs).1.length (count xs).1 [] true le_rfl (by simp)
    simp only [count,List.length_cons,ih.2.1] at *
    simp only [value,Bool.toNat_true,Nat.add_zero] at val
    simp only [ih.1] at val
    exact ⟨val,len,by nlinarith only [ih.2.2,cost]⟩

private theorem clog_bits (x : ℕ) (pos : 0<x) : Nat.clog 2 x=(x-1).size := by
  apply le_antisymm
  · apply (Nat.clog_le_iff_le_pow (by decide)).mpr
    have h : x-1 < 2^(x-1).size := Nat.size_le.mp le_rfl
    omega
  · apply Nat.size_le.mpr
    have h := (Nat.clog_le_iff_le_pow (b:=2) (by decide)).mp (le_refl (Nat.clog 2 x))
    omega

private def powerWord (fuel : List Unit) := fuel.foldr (fun _ t=>false::t) [true]

private theorem power_spec (fuel : List Unit) :
    value (powerWord fuel)=2^fuel.length ∧ (powerWord fuel).length=fuel.length+1 := by
  induction fuel with
  | nil => decide
  | cons u us ih => simp [powerWord] at ih ⊢; simp [value,ih,pow_succ,Nat.mul_comm]

/-- Construct 2^(β+⌊b·ceil(log₂(6b))/β⌋) directly in binary. -/
def build (b β : List Bool) : List Bool × ℕ :=
  let six := multiply [false,true,true] b
  let prev := subtract six.1.length six.1 [] true
  let can := canonical prev.digits
  let l := count can.1
  let top := multiply b l.1
  let q := divide β top.1
  let e := addDigits (max β.length q.quotient.length) β q.quotient false
  let fuel := tokens e.1
  let result := canonical (powerWord fuel.1)
  (result.1,six.2+prev.gates+can.2+l.2+top.2+q.gates+e.2+fuel.2+2*(fuel.1.length+1)+result.2)

private theorem qlen (d x : List Bool) : (divide d x).quotient.length=x.length := by
  induction x with | nil => rfl | cons b xs ih => simp [divide,ih]

theorem build_spec (b β : List Bool) (hb : 0<value b) (hp : 0<value β) :
    let s := 4+b.length+β.length
    let k := value β + value b*Nat.clog 2 (6*value b)/value β
    (build b β).1=(indexCap (value b) (value β)).bits ∧ (build b β).2≤3000*s^2+6*k := by
  intro s k
  let six := multiply [false,true,true] b
  let prev := subtract six.1.length six.1 [] true
  let can := canonical prev.digits
  let l := count can.1
  let top := multiply b l.1
  let q := divide β top.1
  let w := max β.length q.quotient.length
  let e := addDigits w β q.quotient false
  let fuel := tokens e.1
  let result := canonical (powerWord fuel.1)
  obtain ⟨sv,sl,sc⟩ := multiply_spec [false,true,true] b
  change value six.1=value b*6 at sv
  change six.1.length≤3+2*b.length at sl
  change six.2≤b.length*(3+5*(3+2*b.length)) at sc
  obtain ⟨pl,pc,pv⟩ := subtract_spec six.1.length six.1 [] true le_rfl (by simp)
  change prev.digits.length=_ at pl; change prev.gates=7*six.1.length at pc
  change value prev.digits+0+1=value six.1+2^six.1.length*prev.borrow.toNat at pv
  have small := value_lt prev.digits; rw [pl] at small
  have old : value prev.digits=6*value b-1 := by
    cases h : prev.borrow <;> simp [h,sv] at pv <;> omega
  obtain ⟨cv,cc⟩ := canonical_spec prev.digits
  change can.1=_ at cv; change can.2=3*prev.digits.length at cc
  have clen : can.1.length=Nat.clog 2 (6*value b) := by rw [cv,Nat.size_eq_bits_len,old,clog_bits _ (by omega)]
  have clen' : can.1.length≤ six.1.length := by
    rw [cv,Nat.size_eq_bits_len]; exact Nat.size_le.mpr small
  obtain ⟨lv,ll,lc⟩ := count_spec can.1
  change value l.1=_ at lv; change l.1.length=_ at ll; change l.2≤_ at lc
  obtain ⟨tv,tl,tc⟩ := multiply_spec b l.1
  change value top.1=_ at tv; change top.1.length≤_ at tl; change top.2≤_ at tc
  have ⟨_,_,eq,rem,qc⟩ := divide_spec β top.1 hp
  change value top.1=value q.quotient*value β + value q.remainder at eq
  change value q.remainder<value β at rem; change q.gates≤_ at qc
  have qv : value q.quotient=value b*Nat.clog 2 (6*value b)/value β := by
    rw [lv,clen,Nat.mul_comm] at tv
    rw [←tv,eq,Nat.mul_comm _ (value β),Nat.mul_add_div hp,Nat.div_eq_of_lt rem,Nat.add_zero]
  obtain ⟨el,ec,ev⟩ := addDigits_spec w β q.quotient false (le_max_left ..) (le_max_right ..)
  change e.1.length=w+1 at el; change e.2=5*w at ec
  change value e.1=value β+value q.quotient+0 at ev
  rw [Nat.add_zero,qv] at ev
  have ⟨fl,fc⟩ := token_spec e.1
  change fuel.1.length=_ at fl; change fuel.2≤_ at fc; rw [ev] at fl fc
  have ⟨rv,rc⟩ := canonical_spec (powerWord fuel.1)
  change result.1=_ at rv; change result.2=_ at rc
  rw [(power_spec _).1,fl] at rv
  rw [(power_spec _).2,fl] at rc
  change result.1=_ ∧ six.2+prev.gates+can.2+l.2+top.2+q.gates+e.2+fuel.2+2*(fuel.1.length+1)+result.2≤_
  refine ⟨rv.trans (by rw [indexCap,←pow_add]),?_⟩
  have bl : b.length≤ s := by unfold s; omega
  have βl : β.length≤ s := by unfold s; omega
  have large : 4≤ s := by unfold s; omega
  have sixW : six.1.length≤2*s := by unfold s; omega
  have lW : l.1.length≤2*s := ll ▸ clen'.trans sixW
  have tW : top.1.length≤5*s := tl.trans (by omega)
  have wW : w≤5*s := by dsimp only [w]; rw [show q.quotient.length=top.1.length from qlen ..]; exact max_le (by omega) tW
  have c₁ : six.2≤16*s^2 := sc.trans (calc
      _ ≤ s*(s+5*(s+2*s)) := by gcongr <;> omega
      _ = _ := by ring)
  have c₂ : l.2≤14*s^2 := lc.trans (calc
      _ ≤ (3*(2*s)+s)*(2*s) := by gcongr <;> omega
      _ = _ := by ring)
  have c₃ : top.2≤52*s^2 := tc.trans (calc
      _ ≤ (2*s)*(s+5*(s+2*(2*s))) := by gcongr
      _ = _ := by ring)
  have c₄ : q.gates≤305*s^2 := qc.trans (calc
      _ ≤ (5*s)*(10*(s+5*s)+s) := by gcongr; omega
      _ = _ := by ring)
  change fuel.1.length=k at fl; change result.2=3*(k+1) at rc; change fuel.2≤k+2*e.1.length at fc
  rw [el] at fc; rw [pl] at cc
  have sqS : s≤ s^2 := Nat.le_self_pow (by decide) s
  omega

/-- The presieve obtains its own trial cap from the bit length and band
parameter. Its other binary inputs are the modulus, root base and mark limit. -/
def presieveBits (n b β A m : List Bool) : Option (List Bool) × ℕ :=
  let cap := build b β
  let test := BinaryPresieve.run n cap.1 A m
  (test.1,cap.2+test.2)

theorem fixed_presieve_with_cap {n : ℕ} (hn : 2≤n) :
    let b := n.log2+1; let β := Fixed.beta b
    let out := presieveBits n.bits b.bits β.bits (Fixed.A b).bits (Fixed.rootBase n).bits
    out.1.map value=(Cogentic.presieve n b β (Fixed.A b) (Fixed.rootBase n)).map Subtype.val ∧
      out.2≤2^(40021*TwoThirdsCost.scale b) := by
  intro b β out
  have hb : 0<b := Nat.succ_pos _
  have d := Fixed.degree_pos hb
  let s := TwoThirdsCost.scale b
  have vs : Fixed.v b≤ s := (Fixed.scale_bounds hb).1
  have hs : Fixed.h b≤ s := (Nat.le_mul_of_pos_left _ d).trans vs
  have zs : Fixed.z b≤ s := (Nat.le_mul_of_pos_left _ d).trans hs
  have sp : 0< s := (Nat.succ_pos b.log2).trans_le zs
  have bet : 0<β := Nat.mul_pos (by decide : 0<1000) (Nat.mul_pos d (Nat.succ_pos _))
  obtain ⟨eq,cost⟩ := build_spec b.bits β.bits (by simpa using hb) (by simpa using bet)
  simp only [value_bits,Nat.size_eq_bits_len] at eq cost
  let ex := β+b*Nat.clog 2 (6*b)/β
  let W := 2^(1001*s)
  have wp : 1≤W := Nat.one_le_two_pow
  have exBound : ex≤1001*s := by
    have bound := Fixed.index_bound hb
    rw [indexCap,←pow_add] at bound
    have l := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp bound
    change ex≤1000*Fixed.h b+Fixed.v b at l
    omega
  have eW : ex≤W := exBound.trans Nat.lt_two_pow_self.le
  have bW : b≤W := (Nat.lt_log2_self (n:=b)).le.trans (Nat.pow_le_pow_right (by decide) (by change b.log2+1≤ s at zs; omega))
  have βW : β≤W := (show β≤1001*s by unfold β Fixed.beta; omega).trans Nat.lt_two_pow_self.le
  have bw := (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=b))).trans bW
  have βw := (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=β))).trans βW
  have len : 4+b.size+β.size≤6*W := by omega
  have setup : (build b.bits β.bits).2≤2^(40020*s) := calc
    _ ≤ 3000*(4+b.size+β.size)^2+6*ex := cost
    _ ≤ 3000*(6*W)^2+6*W := by gcongr
    _ ≤ 2^17*W^2 := by nlinarith only [Nat.le_self_pow (n:=2) (by decide) W]
    _ ≤ _ := by change 2^17*(2^(1001*s))^2≤_; rw [←pow_mul,←pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have previous := BinaryPresieve.fixed_presieve hn
  simp only [out,presieveBits,eq]
  refine ⟨previous.1,(Nat.add_le_add setup previous.2).trans ?_⟩
  calc 2^(40020*s)+2^(40020*s)=2^(40020*s+1) := by rw [pow_succ]; omega
       _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

end Cogentic.BinaryIndexCap

#print axioms Cogentic.BinaryIndexCap.build_spec

#print axioms Cogentic.BinaryIndexCap.fixed_presieve_with_cap
