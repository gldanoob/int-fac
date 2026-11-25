import Cogentic.IndexCapCost

namespace Cogentic.BinaryPowerScan
open BinaryDivision BinaryPivot TwoThirdsSearch

/-- Each product uses the fixed base as its multiplier. The output length
therefore grows by at most twice the base width at each exponent step. -/
def exactPower (a : List Bool) : ℕ → List Bool × ℕ
  | 0 => ([true],0)
  | k+1 =>
    let prev := exactPower a k
    let next := multiply prev.1 a
    (next.1,prev.2+next.2)

theorem exactPower_spec (a : List Bool) (k w : ℕ) (aw : a.length ≤ w) :
    let out := exactPower a k
    value out.1=value a^k ∧ out.1.length ≤ 1+2*w*k ∧
      out.2 ≤ k*(w*(6*(1+2*w*k)+10*w)) := by
  induction k with
  | zero => simp [exactPower,value]
  | succ k ih =>
    let prev := exactPower a k
    obtain ⟨pv,pl,pc⟩ := ih
    obtain ⟨v,l,c⟩ := multiply_spec prev.1 a
    change value prev.1 = _ at pv
    change prev.1.length ≤ _ at pl
    change prev.2 ≤ _ at pc
    have cost : (multiply prev.1 a).2 ≤ w*(6*(1+2*w*k)+10*w) :=
      c.trans (Nat.mul_le_mul aw (by omega))
    change value (multiply prev.1 a).1 = _ ∧ (multiply prev.1 a).1.length ≤ _ ∧ prev.2+(multiply prev.1 a).2 ≤ _
    refine ⟨by rw [v,pv,pow_succ,mul_comm],l.trans (by nlinarith),?_⟩
    exact (Nat.add_le_add pc cost).trans (by nlinarith)

def leBits (x y : List Bool) : Bool × ℕ :=
  let sub := subtract (max x.length y.length) y x false
  (!sub.borrow,sub.gates+1)

theorem leBits_spec (x y : List Bool) :
    ((leBits x y).1=true ↔ value x ≤ value y) ∧ (leBits x y).2=7*max x.length y.length+1 := by
  let w := max x.length y.length
  let sub := subtract w y x false
  have ⟨l,g,e⟩ := subtract_spec w y x false (le_max_right ..) (le_max_left ..)
  have small := value_lt sub.digits
  rw [show sub.digits.length=w from l] at small
  change value sub.digits+value x+0=value y+2^w*sub.borrow.toNat at e
  change ((!sub.borrow)=true ↔ _) ∧ sub.gates+1=7*w+1
  refine ⟨?_,congrArg (·+1) g⟩
  cases h : sub.borrow <;> simp [h] at e ⊢ <;> omega

theorem value_low_zeros (i : ℕ) (bs : List Bool) :
    value (List.replicate i false ++ bs)=2^i*value bs := by
  induction i with
  | zero => simp
  | succ i ih => simp [List.replicate_succ,value,ih,pow_succ]; ring

/-- The prefix contains the high digits already settled. Trial low zero bits
are fixed wires, and each next bit comes directly from the power comparison. -/
def root (n : List Bool) (k : ℕ) : ℕ → List Bool → List Bool × ℕ
  | 0,hi => (hi,0)
  | i+1,hi =>
    let trial := List.replicate i false ++ true::hi
    let p := exactPower trial k
    let test := leBits p.1 n
    let rest := root n k i (test.1::hi)
    (rest.1,p.2+test.2+rest.2)

def rootStep (w k : ℕ) := k*(w*(6*(1+2*w*k)+10*w))+7*(1+2*w*k+w)+1

theorem root_spec (n : List Bool) (k w i : ℕ) (hi : List Bool)
    (nw : n.length ≤ w) (width : hi.length+i ≤ w) :
    let out := root n k i hi
    value out.1 = rootDigits (value n) k i (2^i*value hi) ∧ out.1.length = hi.length+i ∧
      out.2 ≤ i*rootStep w k := by
  induction i generalizing hi with
  | zero => simp [root,rootDigits]
  | succ i ih =>
    let trial := List.replicate i false ++ true::hi
    let p := exactPower trial k
    let test := leBits p.1 n
    let mid := 2^(i+1)*value hi+2^i
    have tw : trial.length ≤ w := by simp [trial]; omega
    have tv : value trial=mid := by
      rw [show trial=List.replicate i false ++ true::hi from rfl,value_low_zeros]
      simp [mid,value,pow_succ]; ring
    obtain ⟨pv,pl,pc⟩ := exactPower_spec trial k w tw
    have ⟨eq,cost⟩ := leBits_spec p.1 n
    change value p.1=value trial^k at pv
    change p.1.length ≤ _ at pl
    change p.2 ≤ _ at pc
    change (test.1=true ↔ value p.1 ≤ value n) at eq
    change test.2=7*max p.1.length n.length+1 at cost
    rw [pv,tv] at eq
    let step := test.1::hi
    have ⟨rv,rl,rc⟩ := ih step (by simp [step]; omega)
    have fit : max p.1.length n.length ≤ 1+2*w*k+w := max_le (by omega) (by omega)
    have gate : p.2+test.2 ≤ rootStep w k := by unfold rootStep; omega
    change value (root n k i step).1 = _ ∧ (root n k i step).1.length=hi.length+(i+1) ∧ p.2+test.2+(root n k i step).2 ≤ _
    refine ⟨?_,by simpa [step,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using rl,?_⟩
    · rw [rv,rootDigits]; congr 1
      change 2^i*value (test.1::hi) = if mid^k ≤ value n then mid else 2^(i+1)*value hi
      by_cases h : mid^k ≤ value n
      · rw [if_pos h,eq.mpr h]
        simp [value,mid,pow_succ]; ring
      · have no : test.1=false := Bool.eq_false_iff.mpr (fun v => h (eq.mp v))
        simp [if_neg h,no,value,pow_succ]; ring
    · simpa [Nat.succ_mul,Nat.add_comm] using Nat.add_le_add gate rc

/-- The driver's power candidate accepts any proper divisor found by the
root scan. Its divisibility test uses the complete binary remainder. -/
def candidate (n : List Bool) (k : ℕ) : Option (List Bool) × ℕ :=
  let d := root n k n.length []
  let test := BinarySplitter.proper n d.1
  if test.1 then
    let div := divide d.1 n
    let zero := leBits div.remainder []
    (if zero.1 then some d.1 else none,d.2+test.2+div.gates+zero.2+2)
  else (none,d.2+test.2+1)

private def candidateValue (n b k : ℕ) : Option ℕ :=
  let d := rootDigits n k b 0
  if 1<d ∧ d<n ∧ d∣n then some d else none

def candidateBudget (b : ℕ) :=
  b*rootStep b b+(14*b+1) + b*(20*b+1) + (14*b+1) + 2

private theorem candidate_spec (n : List Bool) (k : ℕ) (pos : 0<value n) (kb : k ≤ n.length) :
    (candidate n k).1.map value=candidateValue (value n) n.length k ∧
      (candidate n k).2 ≤ candidateBudget n.length := by
  let b := n.length
  let d := root n k b []
  obtain ⟨rv,rl,rc⟩ := root_spec n k b b [] le_rfl (by simp)
  change value d.1=_ at rv; change d.1.length=_ at rl; change d.2 ≤ _ at rc
  simp only [value,Nat.mul_zero,List.length_nil,Nat.zero_add] at rv rl
  have ⟨proper,work⟩ := BinarySplitter.proper_spec n d.1 pos rl.le
  let test := BinarySplitter.proper n d.1
  change (test.1=true ↔ _) at proper
  change test.2=14*b+1 at work
  have maxWork : d.2 ≤ b*rootStep b b := rc.trans (by unfold rootStep; gcongr)
  by_cases ok : test.1=true
  · obtain ⟨one,less⟩ := proper.mp ok
    let div := divide d.1 n
    let zero := leBits div.remainder []
    obtain ⟨width,len,decomp,small,cost⟩ := divide_spec d.1 n (one.trans' Nat.zero_lt_one)
    change div.width=d.1.length+b at width
    change div.remainder.length ≤ div.width at len
    change value n=value div.quotient*value d.1+value div.remainder at decomp
    change value div.remainder<value d.1 at small
    change div.gates ≤ b*(10*(d.1.length+b)+1) at cost
    have rem : value div.remainder=value n%value d.1 := by
      conv_rhs => rw [decomp,Nat.mul_comm (value div.quotient),Nat.mul_add_mod,Nat.mod_eq_of_lt small]
    obtain ⟨eq,w⟩ := leBits_spec div.remainder []
    have check : zero.1=true ↔ value d.1∣value n := by simpa [zero,value,rem,Nat.dvd_iff_mod_eq_zero] using eq
    change zero.2=7*max div.remainder.length 0+1 at w
    have zCost : zero.2 ≤ 14*b+1 := by simp only [max_zero] at w; omega
    have divCost : div.gates ≤ b*(20*b+1) := cost.trans (by rw [rl]; exact Nat.mul_le_mul_left _ (by omega))
    change ((if test.1 then _ else _):Option (List Bool) × ℕ).1.map value = _ ∧ _ ≤ _
    simp only [ok,if_true,candidate,show (BinarySplitter.proper n (root n k n.length []).1).1=true from ok]
    change (if zero.1 then some d.1 else none).map value=candidateValue (value n) b k ∧
      d.2+test.2+div.gates+zero.2+2 ≤ candidateBudget b
    refine ⟨?_,by unfold candidateBudget; omega⟩
    unfold candidateValue
    rw [←rv]
    simp only [one,less,true_and,←check]
    split <;> rfl
  · have rejected : ¬(1<value d.1 ∧ value d.1<value n) := fun h => ok (proper.mpr h)
    have no : ¬(1<value d.1 ∧ value d.1<value n ∧ value d.1∣value n) :=
      fun h => rejected ⟨h.1,h.2.1⟩
    change ((if test.1 then _ else _):Option (List Bool) × ℕ).1.map value = _ ∧ _
    simp only [ok,candidate,show ¬(BinarySplitter.proper n (root n k n.length []).1).1=true from ok]
    change none=candidateValue (value n) b k ∧ d.2+test.2+1 ≤ candidateBudget b
    exact ⟨by simp [candidateValue,←rv,no],by unfold candidateBudget; omega⟩

/-- Exponents occur in the same ascending order as the driver. The exponent
and bit positions are fixed by the input width before evaluating the circuit. -/
def scan (n : List Bool) (k : ℕ) : ℕ → Option (List Bool) × ℕ
  | 0 => (none,0)
  | r+1 =>
    let test := candidate n k
    match test.1 with
    | some d => (some d,test.2+1)
    | none =>
      let rest := scan n (k+1) r
      (rest.1,test.2+1+rest.2)

private theorem scan_spec (n : List Bool) (k r : ℕ) (pos : 0<value n) (cap : k+r ≤ n.length+1) :
    (scan n k r).1.map value=(List.range' k r).findSome? (candidateValue (value n) n.length) ∧
      (scan n k r).2 ≤ r*(candidateBudget n.length+1) := by
  induction r generalizing k with
  | zero => simp [scan]
  | succ r ih =>
    have ⟨same,work⟩ := candidate_spec n k pos (by omega)
    rw [scan,List.range'_succ,List.findSome?_cons]
    cases h : (candidate n k).1 with
    | none =>
      have ⟨eq,cost⟩ := ih (k+1) (by omega)
      rw [h] at same
      simp only [←same,Option.map_none]
      exact ⟨eq,by nlinarith⟩
    | some d =>
      rw [h] at same
      simp only [←same,Option.map_some]
      refine ⟨trivial,?_⟩
      nlinarith

def run (n : List Bool) := scan n 2 (n.length-1)

theorem driver_power_scan {n : ℕ} (pos : 0<n) :
    let b := n.log2+1
    let out := run n.bits
    out.1.map value=(powerDivisor n b).map Subtype.val ∧ out.2 ≤ 128*(b+1)^6 := by
  intro b out
  have bits : n.bits.length=b := by
    rw [Nat.size_eq_bits_len]
    exact Nat.le_antisymm (Nat.size_le.mpr Nat.lt_log2_self) (Nat.lt_size.mpr (Nat.log2_self_le pos.ne'))
  have ⟨eq,work⟩ := scan_spec n.bits 2 (n.bits.length-1) (by simpa using pos)
    (by rw [bits]; dsimp [b]; omega)
  change out.1.map value=_ at eq
  change out.2 ≤ _ at work
  simp only [bits,value_bits] at eq work
  let c (k : ℕ) : Option {d // ProperDivisor n d} :=
    let d := rootDigits n k b 0
    if h : 1<d ∧ d<n ∧ d∣n then some ⟨d,h⟩ else none
  have cv (k : ℕ) : (c k).map Subtype.val=candidateValue n b k := by
    dsimp only [c,candidateValue]; split <;> simp_all
  refine ⟨eq.trans ?_,?_⟩
  · change _=((List.range' 2 (b-1)).findSome? c).map Subtype.val
    simp only [List.map_findSome?,Function.comp_def,cv]
  · refine work.trans ((Nat.mul_le_mul_right _ (Nat.sub_le b 1)).trans ?_)
    unfold candidateBudget rootStep
    ring_nf; omega

/-- The root construction used in the presieve. The degree is a fixed
parameter of the input-width circuit. Both the decrement and the final
increment are binary ripple operations. -/
def baseAtDegree (n : List Bool) (degree : ℕ) : List Bool × ℕ :=
  let b := n.length
  let pred := subtract b n [true] false
  let r := root pred.digits degree b []
  let next := addDigits b r.1 [] true
  (next.1,pred.gates+r.2+next.2)

def rootBase (n : List Bool) := baseAtDegree n (Fixed.d n.length)

theorem fixed_root_base {n : ℕ} (pos : 0<n) :
    let b := n.log2+1
    let out := rootBase n.bits
    value out.1=Fixed.rootBase n ∧ out.1.length=b+1 ∧ out.2 ≤ 128*(b+1)^5 := by
  intro b out
  have bits : n.bits.length=b := by
    rw [Nat.size_eq_bits_len]
    exact Nat.le_antisymm (Nat.size_le.mpr Nat.lt_log2_self) (Nat.lt_size.mpr (Nat.log2_self_le pos.ne'))
  let pred := subtract b n.bits [true] false
  have ⟨width,cost,pre⟩ := subtract_spec b n.bits [true] false bits.le (by dsimp [b]; simp)
  change pred.digits.length=b at width
  change pred.gates=7*b at cost
  change value pred.digits+value [true]+false.toNat = value n.bits+2^b*pred.borrow.toNat at pre
  have small := value_lt pred.digits
  rw [width] at small
  have v : value pred.digits=n-1 := by
    cases h : pred.borrow <;> simp [h,value] at pre <;> omega
  let r := root pred.digits (Fixed.d b) b []
  obtain ⟨val,len,work⟩ := root_spec pred.digits (Fixed.d b) b b [] width.le (by simp)
  change value r.1=_ at val; change r.1.length=_ at len; change r.2 ≤ _ at work
  simp only [value,Nat.mul_zero,List.length_nil,Nat.zero_add,v] at val len
  let next := addDigits b r.1 [] true
  obtain ⟨ow,oc,ov⟩ := addDigits_spec b r.1 [] true len.le (by simp)
  have eq : out=(next.1,pred.gates+r.2+next.2) := by simp [out,rootBase,baseAtDegree,bits,next,r,pred]
  rw [eq]
  refine ⟨?_,ow,?_⟩
  · change value next.1=Fixed.rootBase n
    simpa [next,value,Fixed.rootBase,b,val] using ov
  · have db := Fixed.degree_le_bits b
    have work' : r.2 ≤ b*rootStep b b := work.trans (by unfold rootStep; gcongr)
    change next.2=5*b at oc
    change pred.gates+r.2+next.2 ≤ _
    rw [cost,oc]
    apply (Nat.add_le_add_right (Nat.add_le_add_left work' _) _).trans
    unfold rootStep; ring_nf; omega

/-- The two root computations before the search together fit the dyadic
two-thirds scale at all positive input widths. -/
theorem driver_root_gates_scale {n : ℕ} (pos : 0<n) :
    let b := n.log2+1
    (run n.bits).2+(rootBase n.bits).2 ≤ 2^(14*TwoThirdsCost.scale b) := by
  intro b
  have h₁ := (driver_power_scan pos).2
  have h₂ := (fixed_root_base pos).2.2
  let s := TwoThirdsCost.scale b
  have hb : 0<b := Nat.succ_pos _
  have dp := Fixed.degree_pos hb
  have zs : Fixed.z b ≤ s := (Nat.le_mul_of_pos_left _ dp).trans
    ((Nat.le_mul_of_pos_left _ dp).trans (Fixed.scale_bounds hb).1)
  have sp := (show 0<Fixed.z b from Nat.succ_pos _).trans_le zs
  have bits : b+1 ≤ 2^s := (Nat.lt_log2_self (n:=b)).trans_le (Nat.pow_le_pow_right (by decide) zs)
  have small := Nat.pow_le_pow_left bits 6
  have h := Nat.pow_le_pow_right (show 0<b+1 by omega) (by decide : 5 ≤ 6)
  calc
    _ ≤ 128*(b+1)^6+128*(b+1)^5 := Nat.add_le_add h₁ h₂
    _ ≤ 256*(b+1)^6 := by omega
    _ ≤ 2^8*(2^s)^6 := Nat.mul_le_mul_left 256 small
    _ ≤ _ := by rw [←pow_mul,←pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)

/-- Generate the root exponent from the input itself. Count its bits in
binary, count the canonical digits of that count, divide, and take the
integer cube root. The result is unary loop fuel. -/
def degreeFuel (n : List Bool) : List Unit × ℕ :=
  let len := BinaryIndexCap.count n
  let bits := BinarySaturation.canonical len.1
  let log := BinaryIndexCap.count bits.1
  let q := divide log.1 bits.1
  let cube := root q.quotient 3 bits.1.length []
  let fuel := BinarySaturation.tokens cube.1
  (fuel.1,len.2+bits.2+log.2+q.gates+cube.2+fuel.2)

theorem degreeFuel_spec (n : List Bool) (pos : 0<n.length) :
    (degreeFuel n).1.length=Fixed.d n.length ∧ (degreeFuel n).2 ≤ 256*(n.length+1)^4 := by
  let b := n.length
  let z := Fixed.z b
  let len := BinaryIndexCap.count n
  let bits := BinarySaturation.canonical len.1
  let log := BinaryIndexCap.count bits.1
  let q := divide log.1 bits.1
  let cube := root q.quotient 3 bits.1.length []
  let fuel := BinarySaturation.tokens cube.1
  obtain ⟨lv,ll,lc⟩ := BinaryIndexCap.count_spec n
  change value len.1=b at lv; change len.1.length=b at ll; change len.2 ≤ _ at lc
  obtain ⟨cv,cc⟩ := BinarySaturation.canonical_spec len.1
  change bits.1=(value len.1).bits at cv; rw [lv] at cv
  change bits.2=3*len.1.length at cc; rw [ll] at cc
  have bz : bits.1.length=z := by
    rw [cv,Nat.size_eq_bits_len]
    exact Nat.le_antisymm (Nat.size_le.mpr Nat.lt_log2_self) (Nat.lt_size.mpr (Nat.log2_self_le pos.ne'))
  have zb : z ≤ b := by
    change b.log2+1 ≤ b
    exact (Nat.log2_lt pos.ne').mpr Nat.lt_two_pow_self
  obtain ⟨zv,zl,zc⟩ := BinaryIndexCap.count_spec bits.1
  change value log.1=bits.1.length at zv; rw [bz] at zv
  change log.1.length=bits.1.length at zl; rw [bz] at zl
  change log.2 ≤ _ at zc; rw [bz] at zc
  have zp : 0<z := Nat.succ_pos _
  have bv : value bits.1=b := cv ▸ value_bits b
  have ⟨_,_,dec,rem,qc⟩ := divide_spec log.1 bits.1 (zv.trans_gt zp)
  change value bits.1=value q.quotient*value log.1+value q.remainder at dec
  change value q.remainder<value log.1 at rem
  rw [bv,zv] at dec; rw [zv] at rem
  have qv : value q.quotient=b/z := by
    conv_rhs => rw [dec,Nat.mul_comm _ z,Nat.mul_add_div zp,Nat.div_eq_of_lt rem,Nat.add_zero]
  have ql : q.quotient.length=bits.1.length := BinaryIndexCap.quotient_length ..
  obtain ⟨rv,rl,rc⟩ := root_spec q.quotient 3 bits.1.length bits.1.length [] ql.le (by simp)
  change value cube.1=_ at rv; change cube.1.length=_ at rl; change cube.2 ≤ _ at rc
  simp only [value,Nat.mul_zero,List.length_nil,Nat.zero_add,qv,bz] at rv rl rc
  have upper : b/z < (0+2^z)^3 := ((Nat.div_le_self ..).trans_lt Nat.lt_log2_self).trans_le
    (by simp only [Nat.zero_add]; exact Nat.le_self_pow (by decide) _)
  have floor := Fixed.digits_floor (n:=b/z) (k:=3) (lo:=0) (bits:=z) (by simp) upper
  have dv : value cube.1=Fixed.d b := by
    rw [rv]; apply Nat.le_antisymm
    · exact (Nat.le_nthRoot_iff (by decide)).mpr floor.1
    · change Nat.nthRoot 3 (b/z) ≤ _
      by_contra! bad
      have h := (Nat.le_nthRoot_iff (by decide : 3≠0)).mp (show rootDigits (b/z) 3 z 0+1 ≤ Nat.nthRoot 3 (b/z) from bad)
      exact floor.2.1.not_ge h
  obtain ⟨fl,fc⟩ := BinarySaturation.token_spec cube.1
  change fuel.1.length=value cube.1 at fl
  change fuel.2 ≤ value cube.1+2*cube.1.length at fc
  rw [dv,rl] at fc
  change q.gates ≤ _ at qc; rw [bz,zl] at qc
  change _ ≤ (3*b+1)*b at lc
  have upperPoly : (3*z+1)*z+z*(10*(z+z)+1)+z*rootStep z 3 ≤
      (3*b+1)*b+b*(10*(b+b)+1)+b*rootStep b 3 := by unfold rootStep; gcongr
  have dd := Fixed.degree_le_bits b
  refine ⟨fl.trans dv,?_⟩
  change len.2+bits.2+log.2+q.gates+cube.2+fuel.2 ≤ 256*(b+1)^4
  have total : len.2+bits.2+log.2+q.gates+cube.2+fuel.2 ≤
      (3*b+1)*b+3*b+((3*b+1)*b+b*(10*(b+b)+1)+b*rootStep b 3)+3*b := by omega
  exact total.trans (by unfold rootStep; ring_nf; omega)

def computedBase (n : List Bool) : List Bool × ℕ :=
  let fuel := degreeFuel n
  let out := baseAtDegree n fuel.1.length
  (out.1,fuel.2+out.2)

theorem driver_root_setup {n : ℕ} (pos : 0<n) :
    let b := n.log2+1
    value (computedBase n.bits).1=Fixed.rootBase n ∧
      (run n.bits).2+(computedBase n.bits).2 ≤ 512*(b+1)^6 ∧
      (run n.bits).2+(computedBase n.bits).2 ≤ 2^(15*TwoThirdsCost.scale b) := by
  intro b
  have bits : n.bits.length=b := by
    rw [Nat.size_eq_bits_len]
    exact Nat.le_antisymm (Nat.size_le.mpr Nat.lt_log2_self) (Nat.lt_size.mpr (Nat.log2_self_le pos.ne'))
  have hb : 0<b := Nat.succ_pos _
  have ⟨degree,work⟩ := degreeFuel_spec n.bits (bits ▸ hb)
  have eq : computedBase n.bits=((rootBase n.bits).1,(degreeFuel n.bits).2+(rootBase n.bits).2) := by
    simp only [computedBase,rootBase,degree]
  rw [eq]
  rw [bits] at work
  have ⟨base,_,bc⟩ := fixed_root_base pos
  have pc := (driver_power_scan pos).2
  change _=Fixed.rootBase n ∧ (run n.bits).2+((degreeFuel n.bits).2+(rootBase n.bits).2) ≤ _ ∧ _
  let s := TwoThirdsCost.scale b
  have dp := Fixed.degree_pos hb
  have zs : Fixed.z b ≤ s := (Nat.le_mul_of_pos_left _ dp).trans
    ((Nat.le_mul_of_pos_left _ dp).trans (Fixed.scale_bounds hb).1)
  have sp := (show 0<Fixed.z b from Nat.succ_pos _).trans_le zs
  have pow : b+1 ≤ 2^s := (Nat.lt_log2_self (n:=b)).trans_le (Nat.pow_le_pow_right (by decide) zs)
  have four := Nat.pow_le_pow_right (show 0<b+1 by omega) (by decide : 4 ≤ 6)
  have five := Nat.pow_le_pow_right (show 0<b+1 by omega) (by decide : 5 ≤ 6)
  have total : (run n.bits).2+((degreeFuel n.bits).2+(rootBase n.bits).2) ≤ 512*(b+1)^6 := by
    change _ ≤ 128*(b+1)^5 at bc
    change _ ≤ 128*(b+1)^6 at pc
    omega
  refine ⟨base,total,total.trans ?_⟩
  calc
    _ ≤ 2^9*(2^s)^6 := Nat.mul_le_mul_left 512 (Nat.pow_le_pow_left pow 6)
    _ ≤ _ := by rw [←pow_mul,←pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)

end Cogentic.BinaryPowerScan

#print axioms Cogentic.BinaryPowerScan.root_spec
#print axioms Cogentic.BinaryPowerScan.driver_power_scan

#print axioms Cogentic.BinaryPowerScan.fixed_root_base
#print axioms Cogentic.BinaryPowerScan.driver_root_gates_scale

#print axioms Cogentic.BinaryPowerScan.driver_root_setup
