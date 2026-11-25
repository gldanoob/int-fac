import Cogentic.SaturationCost
import Cogentic.BadRowGcd

namespace Cogentic.CandidateRuntime
open BinaryDivision BinaryPivot
open Marking (divided)

/-- Compare two binary words of possibly unequal length using a subtractor. -/
def leq (x y : List Bool) : Bool × ℕ :=
  let t := subtract (max x.length y.length) y x false
  (!t.borrow, t.gates+1)

theorem leq_spec (x y : List Bool) :
    ((leq x y).1 = true ↔ value x ≤ value y) ∧
    (leq x y).2 = 7*max x.length y.length+1 := by
  let w := max x.length y.length
  let t := subtract w y x false
  obtain ⟨l,c,e⟩ := subtract_spec w y x false (le_max_right ..) (le_max_left ..)
  change t.digits.length = w at l
  change t.gates = _ at c
  change value t.digits + value x + 0 = value y + 2^w*t.borrow.toNat at e
  have bound := value_lt t.digits
  rw [l] at bound
  have yb := (value_lt y).trans_le (Nat.pow_le_pow_right (by decide : 0<2) (le_max_right x.length y.length))
  change ((!t.borrow) = true ↔ _) ∧ t.gates+1 = _
  refine ⟨?_, by rw [c]⟩
  cases h : t.borrow <;> simp [h] at e ⊢ <;> omega

def equalWords (x y : List Bool) : Bool × ℕ :=
  let a := leq x y
  let b := leq y x
  (a.1 && b.1, a.2+b.2+1)

theorem equalWords_spec (x y : List Bool) :
    ((equalWords x y).1 = true ↔ value x = value y) ∧
    (equalWords x y).2 = 14*max x.length y.length+3 := by
  obtain ⟨a,ac⟩ := leq_spec x y
  obtain ⟨b,bc⟩ := leq_spec y x
  constructor
  · change (((leq x y).1 && (leq y x).1) = true ↔ _)
    rw [Bool.and_eq_true,a,b,le_antisymm_iff]
  · change (leq x y).2+(leq y x).2+1 = _
    rw [ac,bc,max_comm y.length x.length]; omega

/-- Test a congruence by restoring division and a bit comparison. -/
def residueEq (x q r : List Bool) : Bool × ℕ :=
  let d := divide q x
  let e := equalWords d.remainder r
  (e.1,d.gates+e.2+1)

theorem residue_spec (x q r : List Bool) (hq : 0<value q) (w : ℕ)
    (hx : x.length≤w) (hwq : q.length≤w) (hr : r.length≤w) :
    ((residueEq x q r).1 = true ↔ value x % value q = value r) ∧
    (residueEq x q r).2 ≤ w*(20*w+1)+28*w+4 := by
  obtain ⟨width,len,eq,small,work⟩ := divide_spec q x hq
  obtain ⟨e,ec⟩ := equalWords_spec (divide q x).remainder r
  have rem : value (divide q x).remainder = value x % value q := by
    conv_rhs => rw [eq,Nat.mul_comm (value (divide q x).quotient) (value q),Nat.mul_add_mod,Nat.mod_eq_of_lt small]
  have hmax : max (divide q x).remainder.length r.length ≤ 2*w := by rw [width] at len; omega
  have wc : (divide q x).gates ≤ w*(20*w+1) := work.trans (Nat.mul_le_mul hx (by omega))
  refine ⟨by simpa [residueEq,rem] using e,?_⟩
  change (divide q x).gates+(equalWords (divide q x).remainder r).2+1≤_
  rw [ec]; omega

structure ProductCount where
  product : List Bool
  count : List Bool
  gates : ℕ

/-- Collect the product and number of all eligible primes dividing the original
mark value. Each failed divisibility test also incurs a charge. -/
def scan (x : List Bool) : List (List Bool) → ProductCount
  | [] => ⟨[true],[],1⟩
  | q::qs =>
    let prev := scan x qs
    let test := residueEq x q []
    if test.1 then
      let p := multiply prev.product q
      let c := addDigits prev.count.length prev.count [] true
      ⟨p.1,c.1,prev.gates+test.2+p.2+c.2+1⟩
    else ⟨prev.product,prev.count,prev.gates+test.2+1⟩

def stepBudget (w : ℕ) := w*(20*w+1)+28*w+4+w*(w+5*(w+2*w))+5*w+1

private theorem scan_spec (x : List Bool) (base : List (List Bool)) (qbits w : ℕ)
    (pos : ∀ q ∈ base, 0<value q) (sizes : ∀ q ∈ base, q.length≤qbits)
    (hx : x.length≤w) (qw : qbits≤w) (room : 1+2*base.length*qbits≤w)
    (countRoom : base.length≤w) :
    let out := scan x base
    let hits := divided (base.map value) (value x)
    value out.product = hits.prod ∧ value out.count = hits.length ∧
    out.product.length≤1+2*base.length*qbits ∧ out.count.length≤base.length ∧
    out.gates≤1+base.length*stepBudget w := by
  induction base with
  | nil => simp [scan,divided,value]
  | cons q qs ih =>
    have tailRoom : 1+2*qs.length*qbits≤w := by
      simp only [List.length_cons, Nat.mul_add, Nat.add_mul] at room; omega
    have tailCount : qs.length≤w := by simpa using (Nat.le_succ _).trans countRoom
    obtain ⟨pv,cv,pl,cl,pw⟩ := ih (fun t ht => pos t (by simp [ht]))
      (fun t ht => sizes t (by simp [ht])) tailRoom tailCount
    have ql := sizes q (by simp)
    have ⟨res,rw'⟩ := residue_spec x q [] (pos q (by simp)) w hx (ql.trans qw) (by simp)
    have pid : (residueEq x q []).1 = true ↔ value q ∣ value x := by
      simpa [value,Nat.dvd_iff_mod_eq_zero] using res
    let prev := scan x qs
    have hp : prev.product.length≤w := pl.trans tailRoom
    have hc : prev.count.length≤w := cl.trans tailCount
    obtain ⟨v,l,c⟩ := multiply_spec prev.product q
    obtain ⟨al,ac,av⟩ := addDigits_spec prev.count.length prev.count [] true le_rfl (by simp)
    have ch : (multiply prev.product q).2 ≤ w*(w+5*(w+2*w)) :=
      c.trans (by gcongr <;> exact ql.trans qw)
    change value prev.product=_ at pv
    change value prev.count=_ at cv
    change prev.gates≤_ at pw
    change prev.product.length≤_ at pl
    change prev.count.length≤_ at cl
    change value _=_ ∧ value _=_ ∧ _≤_ ∧ _≤_ ∧ _≤_
    cases h : (residueEq x q []).1 with
    | false =>
      have fail : ¬ value q ∣ value x := by simp [←pid,h]
      simp only [scan,h,Bool.false_eq_true,if_false,List.map_cons,divided,List.filter_cons,
        decide_eq_false fail,List.length_cons]
      refine ⟨pv,cv,?_,?_,?_⟩
      · simp only [Nat.mul_add,Nat.add_mul]; dsimp only [prev] at *; omega
      · exact cl.trans (Nat.le_succ _)
      · change prev.gates+_+1≤_; unfold stepBudget at *; rw [Nat.succ_mul]; omega
    | true =>
      have hit := pid.mp h
      simp only [scan,h,if_true,List.map_cons,divided,List.filter_cons,decide_eq_true hit,
        List.prod_cons,List.length_cons]
      refine ⟨v.trans (by rw [pv]; rfl),?_,?_,?_,?_⟩
      · simp only [value,Bool.toNat_true,Nat.add_zero] at av
        rw [av,cv]; rfl
      · simp only [Nat.mul_add,Nat.add_mul]; dsimp only [prev] at *; omega
      · rw [al]; omega
      · change prev.gates+_+_+_+1≤_
        rw [ac,Nat.succ_mul qs.length (stepBudget w)]; unfold stepBudget at *; dsimp only [prev] at *; omega


/-- Both field norms must be squarefree and supported on the factor base.
The binary counter includes the intercept in the relation-height guard. -/
def smooth (x y cap : List Bool) (base : List (List Bool)) : Bool × ℕ :=
  let left := scan x base
  let right := scan y base
  let lx := equalWords left.product x
  let ry := equalWords right.product y
  let k := addDigits (max left.count.length right.count.length) left.count right.count true
  let small := leq k.1 cap
  (lx.1 && ry.1 && small.1, left.gates+right.gates+lx.2+ry.2+k.2+small.2+2)

theorem smooth_spec (x y cap : List Bool) (base : List (List Bool)) (qbits w : ℕ)
    (pos : ∀ q ∈ base, 0<value q) (sizes : ∀ q ∈ base, q.length≤qbits)
    (hx : x.length≤w) (hy : y.length≤w) (hc : cap.length≤w)
    (qw : qbits≤w) (room : 1+2*base.length*qbits≤w) (countRoom : base.length≤w) :
    let out := smooth x y cap base
    let l := divided (base.map value) (value x)
    let r := divided (base.map value) (value y)
    (out.1 = true ↔ l.prod = value x ∧ r.prod = value y ∧ 1+l.length+r.length ≤ value cap) ∧
    out.2 ≤ 2*base.length*stepBudget w+40*w+18 := by
  obtain ⟨lv,lk,ll,lklen,lc⟩ := scan_spec x base qbits w pos sizes hx qw room countRoom
  obtain ⟨rv,rk,rl,rklen,rc⟩ := scan_spec y base qbits w pos sizes hy qw room countRoom
  obtain ⟨leqv,lec⟩ := equalWords_spec (scan x base).product x
  obtain ⟨reqv,rec⟩ := equalWords_spec (scan y base).product y
  let width := max (scan x base).count.length (scan y base).count.length
  let k := addDigits width (scan x base).count (scan y base).count true
  obtain ⟨kl,kc,kv⟩ := addDigits_spec width (scan x base).count (scan y base).count true
    (le_max_left ..) (le_max_right ..)
  change value k.1 = _ at kv
  change k.2 = _ at kc
  change k.1.length = _ at kl
  have ⟨guard,gates⟩ := leq_spec k.1 cap
  have size : width ≤ w := max_le (lklen.trans countRoom) (rklen.trans countRoom)
  constructor
  · change (((equalWords (scan x base).product x).1 && (equalWords (scan y base).product y).1 && (leq k.1 cap).1) = true ↔ _)
    rw [Bool.and_eq_true,Bool.and_eq_true,leqv,reqv,guard,lv,rv,kv,lk,rk]
    simp [Nat.add_comm,Nat.add_assoc,and_assoc]
  · change (scan x base).gates+(scan y base).gates+_+_+k.2+(leq k.1 cap).2+2≤_
    rw [lec,rec,kc,gates,kl]
    have l := max_le (ll.trans room) hx
    have r := max_le (rl.trans room) hy
    have ww := max_le (a:=width+1) (b:=cap.length) (c:=w+1) (by omega) (by omega)
    rw [Nat.mul_assoc]; omega

/-- A bad row rejects precisely the marks in its residue class. -/
def avoids (a : List Bool) : List (List Bool × List Bool) → Bool × ℕ
  | [] => (true,1)
  | (q,r)::rows =>
    let test := residueEq a q r
    if test.1 then (false,test.2+1) else
      let tail := avoids a rows
      (tail.1,test.2+tail.2+1)

private theorem avoids_spec (a : List Bool) (rows : List (List Bool × List Bool)) (w : ℕ)
    (aw : a.length≤w) (sizes : ∀ p ∈ rows, 0<value p.1 ∧ p.1.length≤w ∧ p.2.length≤w) :
    ((avoids a rows).1=true ↔ ∀ p ∈ rows, value a % value p.1 ≠ value p.2) ∧
    (avoids a rows).2≤1+rows.length*(w*(20*w+1)+28*w+5) := by
  induction rows with
  | nil => simp [avoids]
  | cons p rows ih =>
    obtain ⟨q,r⟩ := p
    have ⟨pos,qw,rw'⟩ := sizes (q,r) (by simp)
    obtain ⟨e,c⟩ := residue_spec a q r pos w aw qw rw'
    obtain ⟨t,tc⟩ := ih (fun p hp => sizes p (by simp [hp]))
    cases h : (residueEq a q r).1 with
    | true =>
      have hit := e.mp h
      simp only [avoids,h,if_true,List.forall_mem_cons,List.length_cons]
      exact ⟨by simp [hit], by rw [Nat.succ_mul rows.length]; omega⟩
    | false =>
      have miss : value a % value q ≠ value r := by simp [←e,h]
      simp only [avoids,h,Bool.false_eq_true,if_false,List.forall_mem_cons,List.length_cons]
      exact ⟨by simpa [miss] using t, by rw [Nat.succ_mul rows.length]; omega⟩

private theorem base_length (s : Marking.Input) : s.base.length ≤ s.B+1 := by
  have h : s.base.toFinset ⊆ Finset.range (s.B+1) := by
    intro q hq
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Marking.mem_base.mp (List.mem_toFinset.mp hq)).2.2.1)
  have nodup : s.base.Nodup := List.nodup_dedup _
  simpa only [List.toFinset_card_of_nodup nodup,Finset.card_range] using Finset.card_le_card h

private theorem flat_length {α β : Type*} (f : α→List β) (xs : List α) (k : ℕ)
    (bound : ∀ x ∈ xs, (f x).length ≤ k) : (xs.flatMap f).length ≤ xs.length*k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := bound x (by simp)
    have tail := ih (fun a ha => bound a (by simp [ha]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul]
    omega

private theorem bad_length (s : Marking.Input) : s.badRows.length ≤ (s.B+1)*(2*s.B) := by
  refine (List.length_filter_le ..).trans ((List.dedup_sublist _).length_le.trans
    ((List.length_filter_le ..).trans ?_))
  refine (flat_length _ s.base (2*s.B) ?_).trans (Nat.mul_le_mul_right _ (base_length s))
  intro q hq
  have under := (Marking.mem_base.mp hq).2.2.1
  refine (flat_length _ (List.range q) 2 (fun _ _ => le_rfl)).trans ?_
  simp only [List.length_range]; omega

/-- The binary inputs are the two evaluated norms, the relation-height cap,
the prepared factor base and the residue classes of the excluded rows. -/
def testMark (x y cap a : List Bool) (base : List (List Bool))
    (bad : List (List Bool × List Bool)) : Bool × ℕ :=
  let t := smooth x y cap base
  if t.1 then
    let c := avoids a bad
    (c.1,t.2+c.2+1)
  else (false,t.2+1)

def preparedTest (s : Marking.Input) (a : ℕ) : Bool × ℕ :=
  testMark (Marking.value s.first a).bits (Marking.value s.second a).bits s.L₀.bits a.bits
    (s.base.map Nat.bits) (s.badRows.map (fun r => (r.q.bits,r.r.bits)))

def markWidth (s : Marking.Input) (a : ℕ) :=
  4+2*(s.B+1)*(s.B+1)+(s.degree+3)*s.L₀+a.size+s.L₀.size

def markBudget (B w : ℕ) :=
  2*(B+1)*stepBudget w + 40*w+20 + (B+1)*(2*B)*(w*(20*w+1)+28*w+5)

/-- The comparison agrees with the first-stage retention predicate, including
zero norms, primes repeated in a norm, and bad rows on either side. -/
theorem preparedTest_spec (s : Marking.Input) (a : ℕ)
    (first : s.polynomialGuard s.first) (second : s.polynomialGuard s.second)
    (pos : 1≤a) (within : a≤2^s.L₀) (degreeBits : s.degree+1≤2^s.L₀) :
    (preparedTest s a).1 = Marking.survives s s.badRows a ∧
    (preparedTest s a).2 ≤ markBudget s.B (markWidth s a) := by
  let w := markWidth s a
  let base := s.base.map Nat.bits
  let bad := s.badRows.map (fun r => (r.q.bits,r.r.bits))
  let x := Marking.value s.first a
  let y := Marking.value s.second a
  have widthNorm {cs : List ℤ} (h : s.polynomialGuard cs) :
      (Marking.value cs a).bits.length ≤ w := by
    rw [Nat.size_eq_bits_len]
    have u := (Marking.value_size h pos within degreeBits).trans_lt
      (Nat.pow_lt_pow_right (by decide : 1<2) (Nat.lt_succ_self _))
    exact (Nat.size_le.mpr u).trans (by dsimp [w,markWidth]; omega)
  have qb : s.B+1≤w := by
    have := Nat.le_mul_of_pos_left (s.B+1) (show 0<2*(s.B+1) by positivity)
    dsimp [w,markWidth]; omega
  have bs : base.length ≤ s.B+1 := by simpa [base] using base_length s
  have ss : ∀ q ∈ base, q.length ≤ s.B+1 := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    have limit := (Marking.mem_base.mp hp).2.2.1
    rw [Nat.size_eq_bits_len]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=p))).trans (by omega)
  have bp : ∀ q ∈ base, 0<value q := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    simpa using (Marking.mem_base.mp hp).2.1.pos
  have room : 1+2*base.length*(s.B+1)≤w := by
    have mul := Nat.mul_le_mul_right (s.B+1) (Nat.mul_le_mul_left 2 bs)
    dsimp [w,markWidth]; omega
  have ⟨v,c⟩ := smooth_spec x.bits y.bits s.L₀.bits base (s.B+1) w bp ss
    (widthNorm first) (widthNorm second) (by rw [Nat.size_eq_bits_len]; dsimp [w,markWidth]; omega)
    qb room (bs.trans qb)
  have ⟨bv,bc⟩ := avoids_spec a.bits bad w (by rw [Nat.size_eq_bits_len]; dsimp [w,markWidth]; omega)
    (fun p h => by
      obtain ⟨row,hr,rfl⟩ := List.mem_map.mp h
      obtain ⟨mem,lt,_⟩ := Marking.mem_rows.mp (List.mem_filter.mp hr).1
      have q := Marking.mem_base.mp mem
      have qs := Nat.size_le.mpr (Nat.lt_two_pow_self (n:=row.q))
      have rs := Nat.size_le.mpr (Nat.lt_two_pow_self (n:=row.r))
      simp only [value_bits,Nat.size_eq_bits_len]
      refine ⟨q.2.1.pos,qs.trans ?_,rs.trans ?_⟩ <;> omega)
  have vl : base.map value=s.base := by simp [base,List.map_map,Function.comp_def]
  have bl : bad.length ≤ (s.B+1)*(2*s.B) := by simpa [bad] using bad_length s
  have c' := c.trans (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.mul_le_mul_right (stepBudget w) (Nat.mul_le_mul_left 2 bs)) _) _)
  have bc' := bc.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ bl) 1)
  simp only [value_bits,vl] at v
  simp only [bad,List.forall_mem_map,value_bits] at bv
  change (testMark x.bits y.bits s.L₀.bits a.bits base bad).1 = _ ∧
    (testMark x.bits y.bits s.L₀.bits a.bits base bad).2 ≤ _
  constructor
  · apply Bool.eq_iff_iff.mpr
    unfold testMark Marking.survives
    simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
    cases h : (smooth x.bits y.bits s.L₀.bits base).1 <;> simp [h] at v ⊢
    · exact fun h₁ h₂ small => (Nat.not_le_of_gt (v h₁ h₂) small).elim
    · simpa [x,y,v] using bv
  · dsimp only [w] at c' bc'
    cases h : (smooth x.bits y.bits s.L₀.bits base).1 <;> simp [testMark,h,markBudget] <;> omega

private theorem select_length (k : ℕ) (a b : Bool) (xs ys : List Bool) :
    (selectDigits k a b xs ys).1.length = k := by
  induction k generalizing xs ys with
  | zero => rfl
  | succ k ih => simp [selectDigits,ih]

theorem difference_length (x y : SignedWord) :
    (signedDifference x y).1.digits.length = max x.digits.length y.digits.length+1 := by
  unfold signedDifference; exact select_length ..

private theorem signed_abs (x : SignedWord) : x.decode.natAbs = value x.digits := by
  obtain ⟨neg,d⟩ := x
  cases neg <;> simp [SignedWord.decode,signed]

def evalStep (w : ℕ) := w*(w+5*(w+2*w))+76*w+10

def mulAdd (a : List Bool) (c tail : SignedWord) : SignedWord × ℕ :=
  let p := multiply tail.digits a
  let neg : SignedWord := ⟨!tail.negative,p.1⟩
  let sum := signedDifference c neg
  (sum.1,p.2+sum.2+c.digits.length+2)

private theorem mulAdd_spec (a : List Bool) (c tail : SignedWord) (w : ℕ)
    (aw : a.length≤w) (cw : c.digits.length≤w) (tw : tail.digits.length≤w) :
    let v := mulAdd a c tail
    v.1.decode = c.decode+(value a : ℤ)*tail.decode ∧
    v.1.digits.length ≤ max c.digits.length (tail.digits.length+2*a.length)+1 ∧
    v.2≤evalStep w := by
  let p := multiply tail.digits a
  let neg : SignedWord := ⟨!tail.negative,p.1⟩
  obtain ⟨pv,pl,pc⟩ := multiply_spec tail.digits a
  change value p.1=value a*value tail.digits at pv
  change p.1.length≤tail.digits.length+2*a.length at pl
  change p.2≤_ at pc
  have n : neg.decode = -(value a : ℤ)*tail.decode := by
    unfold SignedWord.decode
    cases hs : tail.negative <;> simp [neg,hs,signed,pv]
  obtain ⟨sumval,sumcost⟩ := signedDifference_spec c neg
  have sumlen := difference_length c neg
  have len : max c.digits.length p.1.length≤3*w := by omega
  have work : p.2 ≤ w*(w+5*(w+2*w)) := pc.trans (Nat.mul_le_mul aw (by omega))
  change (signedDifference c neg).2=25*max c.digits.length p.1.length+8 at sumcost
  change (signedDifference c neg).1.decode=_ ∧ (signedDifference c neg).1.digits.length≤_ ∧
    p.2+(signedDifference c neg).2+c.digits.length+2≤_
  refine ⟨?_,?_,?_⟩
  · rw [sumval,n]; ring
  · rw [sumlen]; change max c.digits.length p.1.length+1≤_; omega
  · rw [sumcost]; unfold evalStep; omega

/-- Signed Horner evaluation. Multiplying with the mark as the fixed-width
multiplier keeps padding growth linear in the number of coefficients. -/
def horner (a : List Bool) : List SignedWord → SignedWord × ℕ
  | [] => (⟨false,[]⟩,1)
  | c::cs =>
    let tail := horner a cs
    let next := mulAdd a c tail.1
    (next.1,tail.2+next.2)

theorem horner_spec (a : List Bool) (cs : List ℤ) (h w : ℕ)
    (bounds : ∀ c ∈ cs, c.natAbs.size ≤ h) (aw : a.length≤w)
    (room : h+cs.length*(2*a.length+1)≤w) :
    let out := horner a (cs.map encode)
    out.1.decode = (Marking.horner (value a : ℤ) cs).1 ∧
    out.1.digits.length ≤ h+cs.length*(2*a.length+1) ∧
    out.2 ≤ 1+cs.length*evalStep w := by
  induction cs with
  | nil => simp [horner,Marking.horner,SignedWord.decode,signed,value]
  | cons c cs ih =>
    have csmall := bounds c (by simp)
    rw [List.length_cons,Nat.succ_mul cs.length] at room
    have room' : h+cs.length*(2*a.length+1)≤w := by omega
    obtain ⟨v,l,cost⟩ := ih (fun t ht => bounds t (by simp [ht])) room'
    have clen : (encode c).digits.length≤h := by simpa [encode,Nat.size_eq_bits_len] using csmall
    obtain ⟨nv,nl,nc⟩ := mulAdd_spec a (encode c) (horner a (cs.map encode)).1 w
      aw (clen.trans (by omega)) (l.trans room')
    simp only [List.map_cons,horner,List.length_cons,Nat.succ_mul cs.length]
    refine ⟨?_,by omega,by omega⟩
    rw [nv,decode_encode,v]; rfl

structure Evaluation where
  atPoint : SignedWord
  slope : SignedWord
  gates : ℕ

/-- Evaluate the polynomial and its derivative together over the signed words. -/
def evaluateBoth (a : List Bool) : List SignedWord → Evaluation
  | [] => ⟨⟨false,[]⟩,⟨false,[]⟩,1⟩
  | c::cs =>
    let tail := evaluateBoth a cs
    let v := mulAdd a c tail.atPoint
    let d := mulAdd a tail.atPoint tail.slope
    ⟨v.1,d.1,tail.gates+v.2+d.2+1⟩

private theorem evaluateBoth_spec (a : List Bool) (cs : List ℤ) (h w : ℕ)
    (bounds : ∀ c ∈ cs, c.natAbs.size ≤ h) (aw : a.length≤w)
    (room : h+cs.length*(2*a.length+1)≤w) :
    let out := evaluateBoth a (cs.map encode)
    let z := Marking.horner (value a : ℤ) cs
    out.atPoint.decode=z.1 ∧ out.slope.decode=z.2 ∧
    out.atPoint.digits.length ≤ h+cs.length*(2*a.length+1) ∧
    out.slope.digits.length ≤ h+cs.length*(2*a.length+1) ∧
    out.gates≤1+cs.length*(2*evalStep w+1) := by
  induction cs with
  | nil => simp [evaluateBoth,Marking.horner,SignedWord.decode,signed,value]
  | cons c cs ih =>
    have csmall := bounds c (by simp)
    rw [List.length_cons,Nat.succ_mul cs.length] at room
    have room' : h+cs.length*(2*a.length+1)≤w := by omega
    obtain ⟨v,d,vl,dl,wc⟩ := ih (fun t ht => bounds t (by simp [ht])) room'
    let tail := evaluateBoth a (cs.map encode)
    have clen : (encode c).digits.length≤h := by simpa [encode,Nat.size_eq_bits_len] using csmall
    obtain ⟨nv,nl,nc⟩ := mulAdd_spec a (encode c) tail.atPoint w
      aw (clen.trans (by omega)) (vl.trans room')
    obtain ⟨nd,ndl,ndc⟩ := mulAdd_spec a tail.atPoint tail.slope w aw (vl.trans room') (dl.trans room')
    dsimp only [tail] at nv nl nc nd ndl ndc
    simp only [List.map_cons,evaluateBoth,List.length_cons,Nat.succ_mul cs.length]
    refine ⟨?_,?_,by omega,by omega,by omega⟩
    · rw [nv,decode_encode,v]; rfl
    · rw [nd,v,d]; rfl

/-- Trim the magnitude before it enters the divisibility checker. -/
def norm (a : List Bool) (cs : List SignedWord) : List Bool × ℕ :=
  let out := horner a cs
  let mag := BinarySaturation.canonical out.1.digits
  (mag.1,out.2+mag.2)

theorem norm_spec (a : ℕ) (cs : List ℤ) (h w : ℕ)
    (bounds : ∀ c ∈ cs, c.natAbs.size ≤ h) (aw : a.size≤w)
    (room : h+cs.length*(2*a.size+1)≤w) :
    (norm a.bits (cs.map encode)).1 = (Marking.value cs a).bits ∧
    (norm a.bits (cs.map encode)).2 ≤ 1+cs.length*evalStep w+3*w := by
  obtain ⟨v,l,c⟩ := horner_spec a.bits cs h w bounds (by simpa [Nat.size_eq_bits_len] using aw)
    (by simpa [Nat.size_eq_bits_len] using room)
  have ⟨e,g⟩ := BinarySaturation.canonical_spec (horner a.bits (cs.map encode)).1.digits
  rw [value_bits] at v
  simp only [Nat.size_eq_bits_len] at l
  have val : value (horner a.bits (cs.map encode)).1.digits = Marking.value cs a := by
    rw [←signed_abs,v]; rfl
  refine ⟨by simpa [norm,val] using e,?_⟩
  change (horner a.bits (cs.map encode)).2+_≤_
  rw [g]; omega

theorem norm_length (a : ℕ) (cs : List ℤ) (h w : ℕ)
    (bounds : ∀ c ∈ cs, c.natAbs.size ≤ h) (aw : a.size≤w)
    (room : h+cs.length*(2*a.size+1)≤w) : (norm a.bits (cs.map encode)).1.length≤w := by
  obtain ⟨_,l,_⟩ := horner_spec a.bits cs h w bounds (by simpa [Nat.size_eq_bits_len] using aw)
    (by simpa [Nat.size_eq_bits_len] using room)
  simp only [Nat.size_eq_bits_len] at l
  let x := (horner a.bits (cs.map encode)).1.digits
  change (BinarySaturation.canonical x).1.length≤w
  rw [(BinarySaturation.canonical_spec x).1,Nat.size_eq_bits_len]
  exact (Nat.size_le.mpr (value_lt x)).trans (l.trans room)

def markWord (first second : List SignedWord) (cap : List Bool) (base : List (List Bool))
    (bad : List (List Bool × List Bool)) (a : List Bool) : Bool × ℕ :=
  let x := norm a first
  let y := norm a second
  let chk := testMark x.1 y.1 cap a base bad
  (chk.1,x.2+y.2+chk.2)

def markKernel (first second : List SignedWord) (cap : List Bool) (base : List (List Bool))
    (bad : List (List Bool × List Bool)) (a : ℕ) :=
  markWord first second cap base bad a.bits

/-- Materialize the common inputs for the entire pass. -/
def markTest (s : Marking.Input) : ℕ → Bool × ℕ :=
  markKernel (s.first.map encode) (s.second.map encode) s.L₀.bits (s.base.map Nat.bits)
    (s.badRows.map (fun r => (r.q.bits,r.r.bits)))

/-- Every Horner stage and its partial product fit in this many bits, including
the padding left by schoolbook multiplication. -/
def evalWidth (s : Marking.Input) (a : ℕ) :=
  s.L₀+1+(s.degree+1)*(2*a.size+1)+a.size

theorem markTest_spec (s : Marking.Input) (a : ℕ)
    (first : s.polynomialGuard s.first) (second : s.polynomialGuard s.second)
    (pos : 1≤a) (within : a≤2^s.L₀) (degreeBits : s.degree+1≤2^s.L₀) :
    (markTest s a).1 = Marking.survives s s.badRows a ∧
    (markTest s a).2 ≤ markBudget s.B (markWidth s a) +
      2*(1+(s.degree+1)*evalStep (evalWidth s a)+3*evalWidth s a) := by
  obtain ⟨pv,pc⟩ := preparedTest_spec s a first second pos within degreeBits
  have norms {cs : List ℤ} (guard : s.polynomialGuard cs) :=
    norm_spec a cs (s.L₀+1) (evalWidth s a) (fun c hc =>
      Nat.size_le.mpr ((guard.2.2.1 c hc).trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))))
      (by unfold evalWidth; omega) (by rw [guard.1]; unfold evalWidth; omega)
  obtain ⟨v,c⟩ := norms first
  obtain ⟨v',c'⟩ := norms second
  rw [first.1] at c
  rw [second.1] at c'
  simp only [markTest, markKernel, markWord, v, v']
  change (preparedTest s a).1 = _ ∧ _+_+(preparedTest s a).2 ≤ _
  exact ⟨pv,by omega⟩

private theorem budget_mono {b B w W : ℕ} (h : b≤B) (h' : w≤W) :
    markBudget b w ≤ markBudget B W := by unfold markBudget stepBudget; gcongr

private theorem fixed_mark {n g a : ℕ} {pair : TryPair.PairData}
    (guard : (TryPair.fixedInput n g pair).guard) (lo : 1≤a) (hi : a≤Fixed.A (n.log2+1)) :
    let s := TryPair.fixedInput n g pair
    (markTest s a).1 = Marking.survives s s.badRows a ∧
    (markTest s a).2 ≤ 2^(80020*TwoThirdsCost.scale (n.log2+1)) := by
  let b := n.log2+1
  let t := TwoThirdsCost.scale b
  let X := 2^(10000*t)
  let H := X^2
  let s := TryPair.fixedInput n g pair
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,alim,_,_,first,second⟩ := guard
  have deg := Fixed.degree_le_bits b
  have ds : s.degree = Fixed.d b := rfl
  have l0 : s.L₀ = b := rfl
  have b0 : 0<b := Nat.succ_pos _
  have h := (Fixed.scale_bounds b0).1
  have d0 := Fixed.degree_pos b0
  have ht : Fixed.h b≤t := (Nat.le_mul_of_pos_left _ d0).trans h
  have zt : Fixed.z b≤t := (Nat.le_mul_of_pos_left _ d0).trans ht
  have t0 : 0<t := (Nat.succ_pos b.log2).trans_le zt
  have z : b.log2+1≤t := zt
  have BX : s.B≤X := by
    change 2^(1000*Fixed.h b)≤2^(10000*t)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have AX : Fixed.A b≤X := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 10000 ht)
  have bX : b≤X := (Nat.lt_log2_self (n:=b)).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have aX := (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=a))).trans (hi.trans AX)
  have bsX := (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=b))).trans bX
  have pX : 0<X := Nat.two_pow_pos _
  have xh : X≤H := Nat.le_self_pow (by decide : 2≠0) X
  have hH : 0<H := Nat.pow_pos pX
  have wH : markWidth s a≤32*H := by
    have hb : s.B+1≤2*X := by omega
    have sides := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hb) hb
    have product := Nat.mul_le_mul (show Fixed.d b+3 ≤ 4*X by omega) bX
    unfold markWidth; rw [ds,l0]
    dsimp [H] at xh ⊢
    nlinarith only [sides,product,aX,bsX,xh,pX]
  obtain ⟨e,c⟩ := markTest_spec s a first second lo (hi.trans alim)
    (by rw [ds,l0]; exact Nat.succ_le_of_lt (deg.trans_lt Nat.lt_two_pow_self))
  have vH : evalWidth s a ≤ 32*H := by
    have v := Nat.mul_le_mul (show Fixed.d b+1 ≤ 2*X by omega) (show 2*a.size+1≤3*X by omega)
    unfold evalWidth; rw [ds,l0]; dsimp [H] at xh ⊢
    nlinarith only [v,bX,aX,xh,pX]
  have ev : evalStep (evalWidth s a) ≤ evalStep (32*H) := by unfold evalStep; gcongr
  have degH : s.degree+1≤2*H := by rw [ds]; omega
  refine ⟨e,c.trans ((Nat.add_le_add (budget_mono (BX.trans xh) wH)
    (Nat.mul_le_mul_left 2 (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul degH ev) 1) (Nat.mul_le_mul_left 3 vH)))).trans ?_)⟩
  calc markBudget H (32*H) + 2*(1+(2*H)*evalStep (32*H)+3*(32*H)) ≤ 1048576*H^4 := by
          unfold markBudget stepBudget evalStep
          have h1 := Nat.le_self_pow (by decide : 4≠0) H
          have h2 := Nat.pow_le_pow_right hH (by decide : 2≤4)
          have h3 := Nat.pow_le_pow_right hH (by decide : 3≤4)
          have h0 := Nat.one_le_pow 4 H hH
          nlinarith only [h0,h1,h2,h3]
       _ ≤ 2^(80020*t) := by
          change 2^20*((2^(10000*t))^2)^4≤_
          rw [←pow_mul,←pow_mul,←pow_add]
          exact Nat.pow_le_pow_right (by decide) (by omega)

/-- Record the tested marks and the work, including every rejected mark. -/
def screenWith {α : Type*} (test : α → Bool × ℕ) : List α → List α × ℕ
  | [] => ([],1)
  | a::as =>
    let hit := test a
    let tail := screenWith test as
    (if hit.1 then a::tail.1 else tail.1, hit.2+tail.2+1)

def screen (s : Marking.Input) := screenWith (markTest s)

private theorem screen_spec (s : Marking.Input) (as : List ℕ) (k : ℕ)
    (tests : ∀ a ∈ as, (markTest s a).1 = Marking.survives s s.badRows a ∧ (markTest s a).2≤k) :
    (screen s as).1 = as.filter (Marking.survives s s.badRows) ∧
    (screen s as).2 ≤ 1+as.length*(k+1) := by
  induction as with
  | nil => exact ⟨rfl, by simp [screen,screenWith]⟩
  | cons a as ih =>
    obtain ⟨eq,cost⟩ := tests a (by simp)
    obtain ⟨tail,work⟩ := ih (fun b hb => tests b (by simp [hb]))
    refine ⟨?_,?_⟩
    · change (if (markTest s a).1 then a::(screen s as).1 else (screen s as).1) = _
      simp [List.filter_cons,eq,tail]
    · change (markTest s a).2+(screen s as).2+1≤1+(as.length+1)*(k+1)
      rw [Nat.succ_mul as.length]; omega

/-- All smoothness and excluded-residue tests in the concrete first-stage mark
filter, including signed polynomial evaluation at every scanned mark. The
factor base, excluded-row list, and eligible-mark list are supplied to the pass. -/
theorem fixed_mark_screen {n g : ℕ} {pair : TryPair.PairData} {rel : Marking.Relations}
    (ok : Marking.stageOne (TryPair.fixedInput n g pair) = some rel) :
    let s := TryPair.fixedInput n g pair
    (screen s s.eligibleMarks).1 = rel.marks ∧
    (screen s s.eligibleMarks).2 ≤ 2^(90022*TwoThirdsCost.scale (n.log2+1)) := by
  let b := n.log2+1
  let t := TwoThirdsCost.scale b
  let s := TryPair.fixedInput n g pair
  change Marking.stageOne s=some rel at ok
  simp only [Marking.stageOne] at ok
  split at ok
  next h =>
    cases ok
    have guards := h.1
    have mem (a : ℕ) (h : a ∈ s.eligibleMarks) : 1≤a ∧ a ≤ s.A := by
      have a' := List.mem_toFinset.mpr h
      change a ∈ (Finset.sort _ _).toFinset at a'
      rw [Finset.sort_toFinset] at a'
      exact ⟨(Finset.mem_filter.mp a').2.1,(Finset.mem_filter.mp a').2.2.1⟩
    obtain ⟨eq,c⟩ := screen_spec s s.eligibleMarks (2^(80020*t)) (fun a ha =>
      fixed_mark guards (mem a ha).1 (mem a ha).2)
    have size : s.eligibleMarks.length ≤ s.A := by
      unfold Marking.Input.eligibleMarks
      rw [Finset.length_sort]
      let set := s.marks.toFinset.filter (fun a => 1≤a ∧ a ≤ s.A ∧ (((a:ℤ)-s.m).natAbs).Coprime s.n)
      have sub : set ⊆ Finset.Icc 1 s.A := by
        intro a ha; exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp ha).2.1,(Finset.mem_filter.mp ha).2.2.1⟩
      simpa [set] using Finset.card_le_card sub
    have hp := Fixed.degree_pos (Nat.succ_pos n.log2)
    have ht : Fixed.h b≤t := (Nat.le_mul_of_pos_left _ hp).trans (Fixed.scale_bounds (Nat.succ_pos n.log2)).1
    have t0 : 0<t := (Nat.mul_pos hp (Nat.succ_pos _)).trans_le ht
    have size' : s.eligibleMarks.length≤2^(10000*t) :=
      size.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ ht))
    have p : 0<2^(80020*t) := Nat.two_pow_pos _
    have q : 0<2^(10000*t+80020*t) := Nat.two_pow_pos _
    refine ⟨eq,c.trans ?_⟩
    calc 1+s.eligibleMarks.length*(2^(80020*t)+1)
          ≤ 1+2^(10000*t)*(2^(80020*t)*2) := Nat.add_le_add_left (Nat.mul_le_mul size' (by omega)) _
        _ ≤ 2^(90022*t) := by
          rw [←Nat.mul_assoc,←pow_add]
          calc _ ≤ 2^(10000*t+80020*t+2) := by rw [pow_add _ _ 2]; norm_num; omega
               _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  next h => contradiction

/-- The two Boolean components report whether the polynomial and its derivative
vanish at the residue. Their common signed Horner pass runs once. -/
def zeros (coeffs : List SignedWord) (q r : List Bool) : (Bool × Bool) × ℕ :=
  let h := evaluateBoth r coeffs
  let t := residueEq h.atPoint.digits q []
  let d := residueEq h.slope.digits q []
  ((t.1,d.1),h.gates+t.2+d.2+1)

def zeroBudget (len w : ℕ) :=
  1+len*(2*evalStep w+1)+2*(w*(20*w+1)+28*w+4)+1

private theorem zeros_spec (cs : List ℤ) (q r h w : ℕ) (less : r<q)
    (bounds : ∀ c ∈ cs, c.natAbs.size≤h)
    (qw : q.size≤w) (room : h+cs.length*(2*r.size+1)≤w) :
    let out := zeros (cs.map encode) q.bits r.bits
    let z := Marking.horner (r:ZMod q) cs
    (out.1.1 = true ↔ z.1=0) ∧ (out.1.2 = true ↔ z.2=0) ∧ out.2 ≤ zeroBudget cs.length w := by
  have rsize := Nat.size_le_size less.le
  obtain ⟨v,d,vl,dl,wc⟩ := evaluateBoth_spec r.bits cs h w bounds
    (by simpa [Nat.size_eq_bits_len] using rsize.trans qw)
    (by simpa [Nat.size_eq_bits_len] using room)
  let b := evaluateBoth r.bits (cs.map encode)
  change b.atPoint.decode = _ at v
  change b.slope.decode = _ at d
  change b.gates ≤ _ at wc
  change b.atPoint.digits.length ≤ _ at vl
  change b.slope.digits.length ≤ _ at dl
  rw [value_bits] at v d
  simp only [Nat.size_eq_bits_len] at vl dl
  have vp : value b.atPoint.digits = Marking.value cs r := by rw [←signed_abs,v]; rfl
  have dp : value b.slope.digits = (Marking.horner (r:ℤ) cs).2.natAbs := by rw [←signed_abs,d]
  have qp : 0<value q.bits := by rw [value_bits]; omega
  have ⟨tv,tc⟩ := residue_spec b.atPoint.digits q.bits [] qp w (vl.trans room)
    (by simpa [Nat.size_eq_bits_len] using qw) (by simp)
  have ⟨dv,dc⟩ := residue_spec b.slope.digits q.bits [] qp w (dl.trans room)
    (by simpa [Nat.size_eq_bits_len] using qw) (by simp)
  have ⟨zv,zd⟩ := Marking.zero_at_mark cs r q
  rw [Nat.mod_eq_of_lt less] at zv zd
  simp only [value_bits,vp,dp,value,←Nat.dvd_iff_mod_eq_zero] at tv dv
  change (_ ↔ _) ∧ (_ ↔ _) ∧ b.gates+_+_+1≤_
  refine ⟨tv.trans zv.symm,dv.trans zd.symm,?_⟩
  unfold zeroBudget; dsimp only [b] at *; omega

structure RowFlags where
  isRoot : Bool
  bad : Bool
  gates : ℕ

def classify (selected other : List SignedWord) (row : Marking.Row) : RowFlags :=
  let s := zeros selected row.q.bits row.r.bits
  let t := zeros other row.q.bits row.r.bits
  ⟨s.1.1, s.1.2 || t.1.1, s.2+t.2+1⟩

def rowWidth (s : Marking.Input) := s.L₀+1+(s.degree+1)*(2*s.B.size+1)+s.B.size

private theorem classify_spec (s : Marking.Input) (row : Marking.Row)
    (guard : ∀ b : Bool, s.polynomialGuard (s.coeffs b)) (less : row.r<row.q)
    (cap : row.q ≤ s.B) :
    let f := classify ((s.coeffs row.second).map encode) ((s.coeffs (!row.second)).map encode) row
    f.isRoot = row.isRoot (s.coeffs row.second) ∧ f.bad = row.bad s ∧
    f.gates ≤ 2*zeroBudget (s.degree+1) (rowWidth s)+1 := by
  have qs := Nat.size_le_size cap
  have rs := (Nat.size_le_size less.le).trans qs
  have run (b : Bool) := zeros_spec (s.coeffs b) row.q row.r (s.L₀+1) (rowWidth s) less
    (fun c hc => Nat.size_le.mpr (((guard b).2.2.1 c hc).trans_lt
      (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))))
    (by unfold rowWidth; omega)
    (by rw [(guard b).1]; unfold rowWidth
        have := Nat.mul_le_mul_left (s.degree+1) (show 2*row.r.size+1≤2*s.B.size+1 by omega)
        omega)
  obtain ⟨sv,sd,sc⟩ := run row.second
  obtain ⟨tv,_,tc⟩ := run (!row.second)
  rw [(guard row.second).1] at sc
  rw [(guard (!row.second)).1] at tc
  refine ⟨Bool.eq_iff_iff.mpr (by simpa [classify,Marking.Row.isRoot] using sv),?_,?_⟩
  · apply Bool.eq_iff_iff.mpr
    simp only [classify,Marking.Row.bad,Marking.Row.isRoot,Bool.or_eq_true,decide_eq_true_eq,sd,tv]
  · change _+_+1≤_; omega

private def rawRows (s : Marking.Input) := s.base.flatMap (fun q =>
  (List.range q).flatMap (fun r => [Marking.Row.mk false q r, Marking.Row.mk true q r]))

private theorem raw_nodup (s : Marking.Input) : (rawRows s).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro q _
    apply List.nodup_flatMap.mpr
    refine ⟨fun r _ => by simp, (List.nodup_range (n:=q)).imp ?_⟩
    intro x y ne
    change List.Disjoint [Marking.Row.mk false q x, Marking.Row.mk true q x]
      [Marking.Row.mk false q y, Marking.Row.mk true q y]
    simp [List.disjoint_left,Marking.Row.mk.injEq,ne]
  · have nodup : s.base.Nodup := List.nodup_dedup _
    apply nodup.imp
    intro q q' ne
    apply List.disjoint_left.mpr
    intro row h k
    simp only [List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at h k
    obtain ⟨r,_,h⟩ := h
    obtain ⟨r',_,k⟩ := k
    rcases h with h|h <;> rcases k with k|k <;> subst row <;> simp_all

structure ClassifiedRows where
  clean : List Marking.Row
  bad : List Marking.Row
  gates : ℕ

def partitionRows (test : Marking.Row → RowFlags) : List Marking.Row → ClassifiedRows
  | [] => ⟨[],[],1⟩
  | row::rows =>
    let tail := partitionRows test rows
    let f := test row
    if f.isRoot then
      if f.bad then ⟨tail.clean,row::tail.bad,f.gates+tail.gates+3⟩
      else ⟨row::tail.clean,tail.bad,f.gates+tail.gates+3⟩
    else ⟨tail.clean,tail.bad,f.gates+tail.gates+2⟩

private theorem partition_spec (s : Marking.Input) (rows : List Marking.Row) (test : Marking.Row→RowFlags)
    (k : ℕ) (tests : ∀ r ∈ rows, (test r).isRoot=r.isRoot (s.coeffs r.second) ∧
      (test r).bad=r.bad s ∧ (test r).gates≤k) :
    let out := partitionRows test rows
    let kept := rows.filter (fun r => r.isRoot (s.coeffs r.second))
    out.clean=kept.filter (fun r => !(r.bad s)) ∧ out.bad=kept.filter (fun r => r.bad s) ∧
    out.gates≤1+rows.length*(k+3) := by
  induction rows with
  | nil => simp [partitionRows]
  | cons r rows ih =>
    obtain ⟨rv,bv,w⟩ := tests r (by simp)
    obtain ⟨cl,bl,c⟩ := ih (fun j hj => tests j (by simp [hj]))
    cases root : r.isRoot (s.coeffs r.second) <;> cases bad : r.bad s <;>
      simp only [partitionRows,rv,bv,root,bad,List.filter_cons,Bool.not_false,Bool.not_true,
        Bool.false_eq_true,if_false,if_true,List.length_cons,Nat.succ_mul rows.length,cl,bl,true_and] <;> omega

/-- Prepare the clean and excluded rows from all residues at primes in the
base. Each residue/field candidate is classified, including every nonroot. -/
def prepareRows (s : Marking.Input) : ClassifiedRows :=
  let first := s.first.map encode
  let second := s.second.map encode
  partitionRows (fun r => if r.second then classify second first r else classify first second r) (rawRows s)

theorem prepareRows_spec (s : Marking.Input) (guard : ∀ b : Bool, s.polynomialGuard (s.coeffs b)) :
    (prepareRows s).clean = s.clean ∧ (prepareRows s).bad = s.badRows ∧
    (prepareRows s).gates ≤ 1+(s.B+1)*(2*s.B)*(2*zeroBudget (s.degree+1) (rowWidth s)+4) := by
  let test (r : Marking.Row) := if r.second then classify (s.second.map encode) (s.first.map encode) r
    else classify (s.first.map encode) (s.second.map encode) r
  have checks (r : Marking.Row) (hr : r ∈ rawRows s) :=
    (show (test r).isRoot=r.isRoot (s.coeffs r.second) ∧ (test r).bad=r.bad s ∧
      (test r).gates≤2*zeroBudget (s.degree+1) (rowWidth s)+1 from by
      simp only [rawRows,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hr
      obtain ⟨q,qm,j,jm,h|h⟩ := hr <;> subst r <;>
        exact classify_spec s _ guard (List.mem_range.mp jm) (Marking.mem_base.mp qm).2.2.1)
  obtain ⟨cl,ba,c⟩ := partition_spec s (rawRows s) test _ checks
  have nodup := (raw_nodup s).filter (fun r => r.isRoot (s.coeffs r.second))
  have eq : s.rows = (rawRows s).filter (fun r => r.isRoot (s.coeffs r.second)) := List.dedup_eq_self.mpr nodup
  have len : (rawRows s).length ≤ (s.B+1)*(2*s.B) := by
    refine (flat_length _ s.base (2*s.B) ?_).trans (Nat.mul_le_mul_right _ (base_length s))
    intro q hq
    have under := (Marking.mem_base.mp hq).2.2.1
    refine (flat_length _ (List.range q) 2 (fun _ _ => le_rfl)).trans ?_
    simp only [List.length_range]; omega
  refine ⟨by simpa only [prepareRows,test,Marking.Input.clean,eq] using cl,by simpa only [prepareRows,test,Marking.Input.badRows,eq] using ba,?_⟩
  exact c.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ len) _)

/-- Build the field-root and derivative classifications and use the same
excluded rows to filter every eligible mark. -/
def rowsAndMarks (s : Marking.Input) : Marking.Relations × ℕ :=
  let rows := prepareRows s
  let kernel := markKernel (s.first.map encode) (s.second.map encode) s.L₀.bits (s.base.map Nat.bits)
    (rows.bad.map (fun r => (r.q.bits,r.r.bits)))
  let pass := screenWith kernel s.eligibleMarks
  (⟨rows.clean,pass.1,s.target⟩,rows.gates+pass.2+1)

private theorem row_bound (n g : ℕ) (pair : TryPair.PairData) :
    let s := TryPair.fixedInput n g pair
    1+(s.B+1)*(2*s.B)*(2*zeroBudget (s.degree+1) (rowWidth s)+4) ≤
      2^(80021*TwoThirdsCost.scale (n.log2+1)) := by
  let s := TryPair.fixedInput n g pair
  let b := n.log2+1
  let t := TwoThirdsCost.scale b
  let X := 2^(10000*t)
  let H := X^2
  have b0 : 0<b := Nat.succ_pos _
  have d := Fixed.degree_pos b0
  have h : Fixed.h b≤t := (Nat.le_mul_of_pos_left _ d).trans (Fixed.scale_bounds b0).1
  have z : b.log2+1≤t := (Nat.le_mul_of_pos_left _ d).trans h
  have t0 : 0<t := by omega
  have bx : b≤X := (Nat.lt_log2_self (n:=b)).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have dx : s.degree≤X := (Fixed.degree_le_bits b).trans bx
  have Bx : s.B≤X := Nat.pow_le_pow_right (by decide) (show 1000*Fixed.h b≤10000*t by omega)
  have bs := (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=s.B))).trans Bx
  have xp : 0<X := Nat.two_pow_pos _
  have hp : 0<H := Nat.pow_pos xp
  have xh : X≤H := Nat.le_self_pow (by decide : 2≠0) X
  have wx : rowWidth s≤16*H := by
    have bound := Nat.mul_le_mul (show s.degree+1≤2*X by omega) (show 2*s.B.size+1≤3*X by omega)
    change b+1+(s.degree+1)*(2*s.B.size+1)+s.B.size≤16*X^2
    dsimp [H] at xh
    nlinarith only [bound,bx,bs,xh,xp]
  have dd : s.degree+1≤2*H := by omega
  have y1 : s.B+1≤2*X := by omega
  have y2 := Nat.mul_le_mul_left 2 Bx
  have factor : (s.B+1)*(2*s.B) ≤ 4*H := by
    have factor := Nat.mul_le_mul y1 y2
    dsimp [H]; nlinarith only [factor]
  have work : zeroBudget (s.degree+1) (rowWidth s)≤zeroBudget (2*H) (16*H) := by
    unfold zeroBudget evalStep; gcongr
  calc 1+(s.B+1)*(2*s.B)*(2*zeroBudget (s.degree+1) (rowWidth s)+4)
        ≤ 1+(4*H)*(2*zeroBudget (2*H) (16*H)+4) := by gcongr
      _ ≤ 2097152*H^4 := by
        unfold zeroBudget evalStep
        have h0 := Nat.one_le_pow 4 H hp
        have h1 := Nat.le_self_pow (by decide : 4≠0) H
        have h2 := Nat.pow_le_pow_right hp (by decide : 2≤4)
        have h3 := Nat.pow_le_pow_right hp (by decide : 3≤4)
        nlinarith only [h0,h1,h2,h3]
      _ ≤ 2^(80021*t) := by
        change 2^21*((2^(10000*t))^2)^4≤_
        rw [←pow_mul,←pow_mul,←pow_add]
        exact Nat.pow_le_pow_right (by decide) (by omega)

/-- Refine the full returned relation data after the first-stage guard. The
bound charges root classification on every candidate and signed-norm screening
on every eligible mark. It takes the range enumeration, base and eligible-mark
lists as inputs. -/
theorem fixed_rows_and_marks {n g : ℕ} {pair : TryPair.PairData} {rel : Marking.Relations}
    (ok : Marking.stageOne (TryPair.fixedInput n g pair) = some rel) :
    let s := TryPair.fixedInput n g pair
    (rowsAndMarks s).1 = rel ∧
    (rowsAndMarks s).2 ≤ 2^(90024*TwoThirdsCost.scale (n.log2+1)) := by
  let s := TryPair.fixedInput n g pair
  let t := TwoThirdsCost.scale (n.log2+1)
  have ⟨sm,sg⟩ := fixed_mark_screen ok
  change (screen s s.eligibleMarks).1=_ at sm
  change (screen s s.eligibleMarks).2 ≤ 2^(90022*t) at sg
  change Marking.stageOne s=some rel at ok
  simp only [Marking.stageOne] at ok
  split at ok
  next h =>
    have guards := h.1
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,first,second⟩ := guards
    have polys : ∀ side : Bool, s.polynomialGuard (s.coeffs side) := by
      rintro (_|_) <;> assumption
    have ⟨cl,ba,c⟩ := prepareRows_spec s polys
    have rc := c.trans (row_bound n g pair)
    change (prepareRows s).gates≤2^(80021*t) at rc
    have d := Fixed.degree_pos (Nat.succ_pos n.log2)
    have t0 : 0<t := (Nat.mul_pos d (Nat.succ_pos _)).trans_le
      ((Nat.le_mul_of_pos_left _ d).trans (Fixed.scale_bounds (Nat.succ_pos n.log2)).1)
    have rc' := rc.trans (Nat.pow_le_pow_right (by decide : 0<2) (show 80021*t ≤ 90022*t by omega))
    have p : 0<2^(90022*t) := Nat.two_pow_pos _
    change (rowsAndMarks s).1 = _ ∧ (rowsAndMarks s).2 ≤ _
    simp only [rowsAndMarks,cl,ba]
    change Marking.Relations.mk s.clean (screen s s.eligibleMarks).1 s.target = rel ∧
      (prepareRows s).gates+(screen s s.eligibleMarks).2+1≤2^(90024*t)
    refine ⟨?_,?_⟩
    · rw [sm]; cases ok; rfl
    · calc _ ≤ 2^(90022*t+2) := by rw [pow_add _ _ 2]; norm_num; omega
             _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  next => contradiction

end Cogentic.CandidateRuntime

#print axioms Cogentic.CandidateRuntime.markTest_spec
#print axioms Cogentic.CandidateRuntime.fixed_mark_screen
#print axioms Cogentic.CandidateRuntime.prepareRows_spec
#print axioms Cogentic.CandidateRuntime.fixed_rows_and_marks
