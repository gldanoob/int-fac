import Cogentic.BinaryPivotCost
import TwoThirdsSearch

namespace Cogentic.BinaryModularPower
open BinaryDivision BinaryPivot

private theorem value_take_of_lt (w : ℕ) (xs : List Bool) (small : value xs < 2^w) :
    value (xs.take w) = value xs := by
  induction w generalizing xs with
  | zero => simp at small; simp [value,small]
  | succ w ih =>
    cases xs with
    | nil => simp
    | cons bit xs =>
      simp only [value, pow_succ] at small
      have bound : value xs < 2^w := by omega
      simp [value,ih xs bound]

/-- The low modulus-width wires hold the complete remainder. -/
def reduce (d xs : List Bool) : List Bool × ℕ :=
  let out := divide d xs
  (out.remainder.take d.length, out.gates)

private theorem reduce_spec (d xs : List Bool) (pos : 0 < value d) :
    let out := reduce d xs
    value out.1 = value xs % value d ∧ out.1.length ≤ d.length ∧
    out.2 ≤ xs.length*(10*(d.length+xs.length)+1) := by
  have ⟨_,_,eq,lt,cost⟩ := divide_spec d xs pos
  have same := value_take_of_lt d.length _ (lt.trans (value_lt d))
  change value ((divide d xs).remainder.take d.length) = _ ∧ _ ∧ _
  rw [same]
  refine ⟨?_,by simp [reduce],cost⟩
  conv_rhs => rw [eq,Nat.mul_comm (value (divide d xs).quotient) (value d),
    Nat.mul_add_mod,Nat.mod_eq_of_lt lt]

def mulMod (d x y : List Bool) : List Bool × ℕ :=
  let product := multiply y x
  let rem := reduce d product.1
  (rem.1, product.2+rem.2)

private theorem mulMod_spec (d x y : List Bool) (pos : 0 < value d)
    (hx : x.length≤d.length) (hy : y.length≤d.length) :
    let out := mulMod d x y
    value out.1 = (value x*value y)%value d ∧ out.1.length ≤ d.length ∧
      out.2 ≤ 136*d.length^2+3*d.length := by
  have ⟨val, len, work⟩ := multiply_spec y x
  have ⟨rem, width, cost⟩ := reduce_spec d (multiply y x).1 pos
  refine ⟨rem.trans (congrArg (· % value d) val),width,?_⟩
  have size : (multiply y x).1.length ≤ 3*d.length := by omega
  have m : (multiply y x).2 ≤ d.length*(d.length+5*(d.length+2*d.length)) := work.trans (by gcongr)
  have r : (reduce d (multiply y x).1).2 ≤ 3*d.length*(10*(d.length+3*d.length)+1) :=
    cost.trans (by gcongr)
  exact (Nat.add_le_add m r).trans_eq (by ring)

/-- Each bit squares the high-part result, multiplies by the fixed base,
and selects the new residue with a full-width multiplexer. -/
def powerBits (d base one : List Bool) : List Bool → List Bool × ℕ
  | [] => (one,0)
  | bit :: hi =>
    let prev := powerBits d base one hi
    let sq := mulMod d prev.1 prev.1
    let prod := mulMod d sq.1 base
    let choice := selectDigits d.length bit (!bit) prod.1 sq.1
    (choice.1, prev.2+sq.2+prod.2+choice.2+1)

private theorem powerBits_spec (d base one xs : List Bool) (a : ℕ)
    (pos : 0 < value d) (baseVal : value base = a%value d)
    (oneVal : value one = 1%value d) (bw : base.length ≤ d.length) (ow : one.length≤d.length) :
    let out := powerBits d base one xs
    value out.1 = a^(value xs)%value d ∧ out.1.length ≤ d.length ∧
    out.2 ≤ xs.length*(272*d.length^2+9*d.length+1) := by
  induction xs with
  | nil => simp [powerBits,value,oneVal,ow]
  | cons bit xs ih =>
    let prev := powerBits d base one xs
    let sq := mulMod d prev.1 prev.1
    let prod := mulMod d sq.1 base
    let chosen := selectDigits d.length bit (!bit) prod.1 sq.1
    obtain ⟨v,l,c⟩ := ih
    have ⟨sv,sl,sc⟩ := mulMod_spec d prev.1 prev.1 pos l l
    have ⟨pv,pl,pc⟩ := mulMod_spec d sq.1 base pos sl bw
    have ⟨cl,cc,cv⟩ := select_spec d.length bit prod.1 sq.1 pl sl
    change value chosen.1 = a^(value (bit::xs))%value d ∧ chosen.1.length≤d.length ∧
      prev.2+sq.2+prod.2+chosen.2+1≤(xs.length+1)*_
    refine ⟨?_,cl.le,?_⟩
    · change value chosen.1 = _ at cv
      change value prev.1 = _ at v
      change value sq.1 = _ at sv
      change value prod.1 = _ at pv
      rw [cv,pv,sv,v,baseVal]
      simp only [Nat.mod_mul_mod,Nat.mul_mod_mod,value,pow_add,pow_mul,pow_two]
      cases bit <;> simp [mul_pow,Nat.mul_comm]
    · change prev.2 ≤ _ at c
      change sq.2 ≤ _ at sc
      change prod.2 ≤ _ at pc
      change chosen.2 = _ at cc
      nlinarith

/-- At modulus zero Lean's natural remainder returns the numerator, so the
bit evaluator performs exact powering and keeps all product bits. -/
def rawPower (a : List Bool) : List Bool → List Bool × ℕ
  | [] => ([true],0)
  | bit :: hi =>
    let prev := rawPower a hi
    let sq := multiply prev.1 prev.1
    if bit then
      let prod := multiply a sq.1
      (prod.1,prev.2+sq.2+prod.2)
    else (sq.1,prev.2+sq.2)

private theorem rawPower_value (a xs : List Bool) : value (rawPower a xs).1 = value a ^ value xs := by
  induction xs with
  | nil => simp [rawPower,value]
  | cons bit xs ih =>
    cases bit <;> simp [rawPower,value,(multiply_spec ..).1,ih,pow_add,pow_mul,pow_two,mul_pow,Nat.mul_comm]

def power (a e n : ℕ) : List Bool × ℕ :=
  if n=0 then rawPower a.bits e.bits else
    let base := reduce n.bits a.bits
    let one := reduce n.bits [true]
    let result := powerBits n.bits base.1 one.1 e.bits
    (result.1,base.2+one.2+result.2)

/-- The circuit returns exactly the program's modular power at every input. -/
theorem power_value (a e n : ℕ) : value (power a e n).1 = ModularPower.powMod a e n := by
  by_cases z : n=0
  · simp [power,z,rawPower_value,ModularPower.powMod_def]
  have pos : 0 < value n.bits := by simpa using Nat.pos_of_ne_zero z
  have base := reduce_spec n.bits a.bits pos
  have one := reduce_spec n.bits [true] pos
  have result := powerBits_spec n.bits _ _ e.bits a pos (by simpa using base.1)
    (by simpa [value] using one.1) base.2.1 one.2.1
  simpa [power,z,ModularPower.powMod_def] using result.1

def powerBudget (A E W : ℕ) :=
  A*(10*(W+A)+1)+(10*(W+1)+1)+E*(272*W^2+9*W+1)

/-- On a positive modulus of W bits, the Boolean gate count grows linearly
with the exponent's bit length. The base need not already be reduced. -/
theorem power_gates (a e n : ℕ) (positive : 0<n) :
    let W := n.size
    (power a e n).1.length≤W ∧ (power a e n).2 ≤ powerBudget a.size e.size W := by
  have pos : 0 < value n.bits := by simpa using positive
  have base := reduce_spec n.bits a.bits pos
  have one := reduce_spec n.bits [true] pos
  have result := powerBits_spec n.bits _ _ e.bits a pos (by simpa using base.1)
    (by simpa [value] using one.1) base.2.1 one.2.1
  have total := Nat.add_le_add (Nat.add_le_add base.2.2 one.2.2) result.2.2
  simpa [power,powerBudget,positive.ne',←Nat.size_eq_bits_len] using And.intro result.2.1 total

private def nonzero : List Bool → Bool × ℕ
  | [] => (false,0)
  | b::hi =>
    let upper := nonzero hi
    (b || upper.1,upper.2+1)

private theorem nonzero_spec (bs : List Bool) :
    ((nonzero bs).1=true ↔ 0<value bs) ∧ (nonzero bs).2=bs.length := by
  induction bs with
  | nil => simp [nonzero,value]
  | cons b bs ih =>
    cases b <;> simp [nonzero,value,ih.1,ih.2]

private def isOne (bs : List Bool) : Bool × ℕ :=
  let high := nonzero bs.tail
  (bs.headD false && !high.1,high.2+2)

private theorem isOne_spec (bs : List Bool) :
    ((isOne bs).1=true ↔ value bs=1) ∧ (isOne bs).2≤bs.length+2 := by
  obtain ⟨h,c⟩ := nonzero_spec bs.tail
  have v := value_head bs
  change ((bs.headD false && !(nonzero bs.tail).1)=true ↔ value bs=1) ∧ _
  refine ⟨?_, by simp [isOne,c]⟩
  cases hb : bs.headD false <;> cases hh : (nonzero bs.tail).1 <;>
    simp only [hh,hb,Bool.toNat_true,Bool.toNat_false,Bool.not_true,Bool.not_false,Bool.and_true,Bool.and_false,Bool.false_eq_true,true_iff,false_iff] at h v ⊢ <;> omega

def checkOne (a e n : ℕ) : Bool × ℕ :=
  let out := power a e n
  let same := isOne out.1
  (same.1,out.2+same.2)

theorem checkOne_spec (a e n : ℕ) :
    ((checkOne a e n).1 = true ↔ ModularPower.powMod a e n=1) ∧
    (0<n → (checkOne a e n).2 ≤ powerBudget a.size e.size n.size+n.size+2) := by
  have ⟨ok,cost⟩ := isOne_spec (power a e n).1
  refine ⟨ok.trans (by rw [power_value]),?_⟩
  intro hn
  have ⟨width,work⟩ := power_gates a e n hn
  change (power a e n).2+(isOne (power a e n).1).2≤_
  omega

/-- The three Boolean conditions checked in the exponent-proposal branch
of TwoThirdsSearch.verify. All bits above the parity bit are ORed together. -/
def checkExponent (n a e : ℕ) : Bool × ℕ :=
  let high := nonzero e.bits.tail
  let ok := checkOne a e n
  (high.1 && !e.bits.headD false && ok.1,high.2+ok.2+3)

theorem checkExponent_spec (n a e : ℕ) :
    ((checkExponent n a e).1 = true ↔ TwoThirdsSearch.ValidExponent n a e) ∧
    (0<n → (checkExponent n a e).2 ≤ powerBudget a.size e.size n.size+n.size+e.size+5) := by
  obtain ⟨h,c⟩ := nonzero_spec e.bits.tail
  obtain ⟨ok,work⟩ := checkOne_spec a e n
  have v := value_head e.bits
  rw [value_bits] at v
  constructor
  · change ((_ && _ && _)=true) ↔ 2≤e ∧ 2∣e ∧ ModularPower.powMod a e n=1
    simp only [Bool.and_eq_true,Bool.not_eq_true',h,ok]
    have arithmetic (b : Bool) (y : ℕ) :
        (0<y ∧ b=false) ↔ 2≤b.toNat+2*y ∧ 2∣b.toNat+2*y := by
      cases b with
      | false =>
        simp only [Bool.toNat_false,zero_add,and_true,dvd_mul_right,and_true]
        omega
      | true =>
        simp only [Bool.toNat_true,Bool.true_eq_false,and_false,false_iff]
        rintro ⟨_,k,hk⟩
        omega
    rw [arithmetic,←v,and_assoc]
  · intro hn
    have len : e.bits.tail.length≤e.bits.length := by simp
    rw [Nat.size_eq_bits_len] at len
    change (nonzero e.bits.tail).2+(checkOne a e n).2+3≤_
    have := work hn
    omega

theorem verify_exponent_iff (n a e : ℕ) :
    (checkExponent n a e).1=true ↔ (TwoThirdsSearch.verify n a (some (.exponent e))).isSome := by
  rw [(checkExponent_spec n a e).1]
  simp only [TwoThirdsSearch.verify,TwoThirdsSearch.ValidExponent]
  split <;> simp_all

/-- Euclid on bit-list inputs; every termination test uses the counted OR circuit. -/
def gcdBits (x y : List Bool) : List Bool × ℕ :=
  let test := nonzero x
  if h : test.1=true then
    let rem := reduce x y
    let tail := gcdBits rem.1 x
    (tail.1,test.2+rem.2+tail.2+1)
  else (y,test.2+1)
termination_by value x
decreasing_by
  have pos := (nonzero_spec x).1.mp h
  exact (reduce_spec x y pos).1.trans_lt (Nat.mod_lt _ pos)

private theorem gcdBits_spec (x y : List Bool) (W : ℕ) (hx : x.length≤W) (hy : y.length≤W) :
    value (gcdBits x y).1=(value x).gcd (value y) ∧ (gcdBits x y).1.length≤W ∧
    (gcdBits x y).2 ≤ (Elimination.gcdWithCount (value x) (value y)).2*
      (W*(20*W+1)+W+1)+(W+1) := by
  induction x, y using gcdBits.induct with
  | case1 x y test h rem ih =>
    obtain ⟨nz,scan⟩ := nonzero_spec x
    change (nonzero x).1=true at h
    have pos := nz.mp h
    obtain ⟨rv,rl,rc⟩ := reduce_spec x y pos
    obtain ⟨good,width,cost⟩ := ih (rl.trans hx) hx
    dsimp only [rem] at good width cost
    rw [rv] at good cost
    rw [gcdBits,Elimination.gcdWithCount]
    simp only [h,↓reduceDIte,Nat.ne_of_gt pos]
    have remBudget := rc.trans (show y.length*(10*(x.length+y.length)+1)≤W*(20*W+1) by
      apply Nat.mul_le_mul hy; omega)
    exact ⟨good.trans (Nat.gcd_rec ..).symm,width,by rw [Nat.succ_mul]; omega⟩
  | case2 x y test h =>
    obtain ⟨nz,scan⟩ := nonzero_spec x
    change ¬(nonzero x).1=true at h
    have z : value x=0 := Nat.eq_zero_of_not_pos (fun pos => h (nz.mpr pos))
    rw [gcdBits,Elimination.gcdWithCount]
    simp [h,z,scan,hy,hx]

def gcdBudget (W : ℕ) := 2*W*(W*(20*W+1)+W+1)+(W+1)

theorem gcd_gates (a n W : ℕ) (ha : a.size≤W) (hn : n.size≤W) :
    value (gcdBits a.bits n.bits).1=a.gcd n ∧ (gcdBits a.bits n.bits).1.length≤W ∧
      (gcdBits a.bits n.bits).2≤gcdBudget W := by
  obtain ⟨v,l,w⟩ := gcdBits_spec a.bits n.bits W (by simpa only [Nat.size_eq_bits_len] using ha)
    (by simpa only [Nat.size_eq_bits_len] using hn)
  simp only [value_bits] at v w
  have cnt := (Elimination.gcdWithCount_le a n).trans (Nat.mul_le_mul_left 2 ha)
  exact ⟨v,l,w.trans (by unfold gcdBudget; gcongr)⟩

/-- Each Fermat guard in primeCheck counts the coprimality condition as well
as the modular power and the tests against one. -/
def fermatGuard (g n : ℕ) : Bool × ℕ :=
  let gcd := gcdBits g.bits n.bits
  let cop := isOne gcd.1
  let ok := checkOne g (n-1) n
  (!cop.1 || ok.1,gcd.2+cop.2+ok.2+2)

theorem fermatGuard_spec (g n W : ℕ) (hp : 0<n) (hg : g.size≤W) (hn : n.size≤W) :
    (fermatGuard g n).1=decide (g.Coprime n → ModularPower.powMod g (n-1) n=1) ∧
    (fermatGuard g n).2 ≤ gcdBudget W+powerBudget W W W+2*W+6 := by
  obtain ⟨gv,gl,gc⟩ := gcd_gates g n W hg hn
  obtain ⟨cv,cc⟩ := isOne_spec (gcdBits g.bits n.bits).1
  rw [gv] at cv
  obtain ⟨pv,pc⟩ := checkOne_spec g (n-1) n
  have ee := (Nat.size_le_size (Nat.sub_le n 1)).trans hn
  have bounded : powerBudget g.size (n-1).size n.size ≤ powerBudget W W W := by unfold powerBudget; gcongr
  constructor
  · apply Bool.eq_iff_iff.mpr
    change ((!_ || _)=true) ↔ decide (_ → _)=true
    simp only [Bool.or_eq_true,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,cv,pv,decide_eq_true_eq]
    change (¬g.gcd n=1 ∨ _) ↔ (g.gcd n=1 → _)
    tauto
  · change (gcdBits g.bits n.bits).2+(isOne (gcdBits g.bits n.bits).1).2+(checkOne g (n-1) n).2+2 ≤ _
    have work := pc hp
    omega

def fermatGuards (n : ℕ) : List ℕ → Bool × ℕ
  | [] => (true,0)
  | g::gs =>
    let test := fermatGuard g n
    let tail := fermatGuards n gs
    (test.1 && tail.1,test.2+tail.2+1)

theorem fermatGuards_spec (n W : ℕ) (gs : List ℕ) (hp : 0<n) (hn : n.size≤W)
    (bases : ∀ g∈gs, g.size≤W) :
    (fermatGuards n gs).1=gs.all (fun g => decide (g.Coprime n → ModularPower.powMod g (n-1) n=1)) ∧
    (fermatGuards n gs).2 ≤ gs.length*(gcdBudget W+powerBudget W W W+2*W+7) := by
  induction gs with
  | nil => simp [fermatGuards]
  | cons g gs ih =>
    obtain ⟨v,w⟩ := fermatGuard_spec g n W hp (bases _ (by simp)) hn
    obtain ⟨tv,tw⟩ := ih (fun h hh => bases h (List.mem_cons_of_mem _ hh))
    simp only [fermatGuards,List.all_cons,v,tv,List.length_cons,true_and]
    rw [Nat.succ_mul]; omega

end Cogentic.BinaryModularPower

#print axioms Cogentic.BinaryModularPower.power_value
#print axioms Cogentic.BinaryModularPower.power_gates

#print axioms Cogentic.BinaryModularPower.checkExponent_spec
#print axioms Cogentic.BinaryModularPower.verify_exponent_iff

#print axioms Cogentic.BinaryModularPower.fermatGuards_spec
