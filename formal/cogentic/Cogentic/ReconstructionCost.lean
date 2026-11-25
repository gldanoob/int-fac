import Cogentic.ReconstructedOrder
import Cogentic.SaturationCost
import Cogentic.CollectorCost

namespace Cogentic.BinaryReconstruction
open Reconstruction BinaryDivision BinaryPivot BinarySaturation

/-- Positive tails already have coprime coordinates, so a reciprocal followed
by integer translation requires one multiply-add and no rational reduction. -/
theorem next_coordinates (a : ℤ) (x : ℚ) (pos : 0<x.num) :
    ((a:ℚ)+x⁻¹).num=a*x.num+x.den ∧ ((a:ℚ)+x⁻¹).den=x.num.natAbs := by
  have den : ((a:ℚ)+x⁻¹).den=x.num.natAbs := by
    rw [Rat.intCast_add_den,Rat.den_inv,if_neg pos.ne']
  refine ⟨?_, den⟩
  have abs := Int.natAbs_of_nonneg pos.le
  have hi := Rat.mul_den_eq_num (x⁻¹)
  rw [Rat.den_inv,if_neg pos.ne',Rat.num_inv,Int.sign_eq_one_of_pos pos,one_mul] at hi
  have eq := Rat.mul_den_eq_num ((a:ℚ)+x⁻¹)
  rw [den,add_mul,hi] at eq
  exact_mod_cast (show ((((a:ℤ)*x.num+x.den:ℤ):ℚ))=(((a:ℚ)+x⁻¹).num:ℚ) by
    push_cast; rw [←eq]; congr 2; rw [←Int.cast_natCast (R:=ℚ) x.num.natAbs,abs]).symm

private theorem positive_bounds (u v : ℕ) (vp : 0<v) (uv : v≤u) (x : ℚ)
    (mem : x∈convergents (u:ℤ) v) : 0<x.num ∧ x.num.natAbs≤u ∧ x.den≤v := by
  induction v using Nat.strong_induction_on generalizing u x with
  | h v ih =>
    let a := u/v
    let r := u%v
    have rv : r<v := Nat.mod_lt u vp
    have au : a≤u := Nat.div_le_self _ _
    have ap : 0<a := Nat.div_pos uv vp
    have add : a*v+r=u := by simpa [a,r,Nat.add_comm,Nat.mul_comm] using Nat.mod_add_div u v
    have head : 0<((a:ℚ).num) ∧ (a:ℚ).num.natAbs≤u ∧ (a:ℚ).den≤v := by simpa using ⟨ap,au,vp⟩
    rw [convergents,dif_neg vp.ne'] at mem
    simp only [←Int.natCast_ediv,←Int.natCast_mod,Int.toNat_natCast,Int.cast_natCast] at mem
    change x∈(if r=0 then [(a:ℚ)] else (a:ℚ)::(convergents (v:ℤ) r).map _) at mem
    by_cases rz : r=0
    · simp [rz] at mem; simpa [mem] using head
    · rw [if_neg rz,List.mem_cons,List.mem_map] at mem
      rcases mem with eq | ⟨y,ym,rfl⟩
      · simpa [eq] using head
      · obtain ⟨yp,yn,yd⟩ := ih r rv v (Nat.pos_of_ne_zero rz) rv.le y ym
        have ⟨num,den⟩ := next_coordinates (a:ℤ) y yp
        have ny := Int.natAbs_of_nonneg yp.le
        rw [Int.cast_natCast] at num den
        rw [num,den,←ny]
        rw [←Int.natCast_mul,←Int.natCast_add,Int.natAbs_natCast]
        exact ⟨by positivity,(Nat.add_le_add (Nat.mul_le_mul_left a yn) yd).trans_eq add,yn⟩

/-- Every reduced numerator and denominator in the actual list, including
the signed first quotient. -/
theorem convergent_height (u : ℤ) (v : ℕ) (vp : 0<v) (x : ℚ) (mem : x∈convergents u v) :
    x.num.natAbs≤u.natAbs+2*v ∧ x.den≤v := by
  let a := u/(v:ℤ)
  let r := (u%(v:ℤ)).toNat
  have vi : (0:ℤ)<v := by exact_mod_cast vp
  have rv : r<v := by have := Int.emod_lt_of_pos u vi; dsimp [r]; omega
  have ri : (r:ℤ)=u%(v:ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ vi.ne')
  have div : a*(v:ℤ)=u-r := by have := Int.emod_add_ediv_mul u (v:ℤ); dsimp [a]; omega
  have av : a.natAbs*v≤u.natAbs+r := by
    have h := Int.natAbs_sub_le u (r:ℤ)
    rw [←div,Int.natAbs_mul,Int.natAbs_natCast,Int.natAbs_natCast] at h
    exact h
  have head : (a:ℚ).num.natAbs≤u.natAbs+2*v ∧ (a:ℚ).den≤v := by
    have small := Nat.le_mul_of_pos_right a.natAbs vp
    simp; omega
  rw [convergents,dif_neg vp.ne'] at mem
  change x∈(if r=0 then [(a:ℚ)] else (a:ℚ)::(convergents (v:ℤ) r).map _) at mem
  by_cases rz : r=0
  · simp [rz] at mem; simpa [mem] using head
  · rw [if_neg rz,List.mem_cons,List.mem_map] at mem
    rcases mem with eq | ⟨y,ym,rfl⟩
    · simpa [eq] using head
    · have ⟨yp,yn,yd⟩ := positive_bounds v r (Nat.pos_of_ne_zero rz) rv.le y ym
      have ⟨num,den⟩ := next_coordinates a y yp
      rw [num,den]
      have bound := (Int.natAbs_add_le (a*y.num) (y.den:ℤ))
      rw [Int.natAbs_mul,Int.natAbs_natCast] at bound
      have prod := Nat.mul_le_mul_left a.natAbs yn
      exact ⟨by omega,yn⟩

private theorem select_length (w : ℕ) (b c : Bool) (x y : List Bool) :
    (selectDigits w b c x y).1.length=w := by
  induction w generalizing x y with
  | zero => rfl
  | succ w ih => simp [selectDigits,ih]

private theorem cross_length (a b c d : SignedWord) {w : ℕ}
    (ha : a.digits.length≤w) (hb : b.digits.length≤w)
    (hc : c.digits.length≤w) (hd : d.digits.length≤w) :
    (cross a b c d).1.digits.length≤3*w+1 := by
  have p := (multiply_spec b.digits a.digits).2.1
  have q := (multiply_spec d.digits c.digits).2.1
  simp only [cross,signedDifference,select_length]
  omega

private theorem abs_decode (x : SignedWord) : value x.digits=x.decode.natAbs := by
  cases x with | mk s ds => cases s <;> simp [SignedWord.decode,signed]

/-- The final borrow of x-y is the strict unsigned comparison x<y. -/
def below (x y : List Bool) : Bool × ℕ :=
  let sub := subtract (max x.length y.length) x y false
  (sub.borrow,sub.gates)

theorem below_spec (x y : List Bool) :
    ((below x y).1=true ↔ value x<value y) ∧ (below x y).2=7*max x.length y.length := by
  let w := max x.length y.length
  let sub := subtract w x y false
  obtain ⟨len,cost,v⟩ := subtract_spec w x y false (le_max_left ..) (le_max_right ..)
  have small := value_lt sub.digits
  rw [show sub.digits.length=w from len] at small
  change value sub.digits+value y+0=value x+2^w*sub.borrow.toNat at v
  refine ⟨?_,cost⟩
  change sub.borrow=true ↔ _
  cases h : sub.borrow <;> simp [h] at v ⊢ <;> omega

private theorem accept_iff (u : ℤ) (v Q : ℕ) (y : ℚ) (vp : 0<v) :
    (y.den≤Q ∧ |(u:ℚ)/v-y|<1/(2*(Q:ℚ)^2)) ↔
      y.den≤Q ∧ 2*(Q^2*(u*y.den-y.num*v).natAbs)<v*y.den := by
  have vi : (0:ℚ)<v := by exact_mod_cast vp
  have yd : (0:ℚ)<y.den := by exact_mod_cast y.pos
  have eq : (u:ℚ)/v-y=(((u*y.den-y.num*v:ℤ):ℚ))/((v:ℚ)*y.den) := by
    push_cast
    field_simp
    linear_combination v * (Rat.mul_den_eq_num y).symm
  have diff : |(u:ℚ)/v-y|=(((u*y.den-y.num*v).natAbs:ℕ):ℚ)/((v:ℚ)*y.den) := by
    rw [eq,abs_div,abs_of_pos (mul_pos vi yd),Nat.cast_natAbs,Int.cast_abs]
  constructor <;> rintro ⟨sm,h⟩ <;> refine ⟨sm,?_⟩
  · have qp : (0:ℚ)<Q := by exact_mod_cast y.pos.trans_le sm
    rw [diff,div_lt_div_iff₀ (mul_pos vi yd) (by positivity)] at h
    exact_mod_cast (show (2:ℚ)*((Q:ℚ)^2*↑(u*y.den-y.num*v).natAbs)<v*(y.den:ℚ) by linarith)
  · have qp : (0:ℚ)<Q := by exact_mod_cast y.pos.trans_le sm
    rw [diff,div_lt_div_iff₀ (mul_pos vi yd) (by positivity)]
    have : (2:ℚ)*((Q:ℚ)^2*↑(u*y.den-y.num*v).natAbs)<v*(y.den:ℚ) := by exact_mod_cast h
    linarith

/-- The numerator and positive denominator are already coprime at every
stage. Keep their signed and unsigned binary encodings as separate fields. -/
abbrev Fraction := ℤ × ℕ

def coords (y : ℚ) : Fraction := (y.num,y.den)

/-- Compare the cross products in the strict rational test, including the
denominator cap. No divisions or rational normalizations are needed. -/
def acceptPair (u : ℤ) (v Q : ℕ) (y : Fraction) : Bool × ℕ :=
  let delta := cross (encode u) (encode y.2) (encode y.1) (encode v)
  let sq := multiply Q.bits Q.bits
  let lhs := multiply delta.1.digits sq.1
  let rhs := multiply y.2.bits v.bits
  let test := below (false::lhs.1) rhs.1
  let cap := below Q.bits y.2.bits
  (!cap.1 && test.1,delta.2+sq.2+lhs.2+rhs.2+test.2+cap.2+2)

def accept (u : ℤ) (v Q : ℕ) (y : ℚ) := acceptPair u v Q (coords y)

theorem accept_spec (u : ℤ) (v Q : ℕ) (y : ℚ) {w : ℕ} (wp : 1≤w) (vp : 0<v)
    (uw : u.natAbs.size≤w) (vw : v.size≤w) (qw : Q.size≤w)
    (nw : y.num.natAbs.size≤w) (dw : y.den.size≤w) :
    ((accept u v Q y).1=true ↔ (y.den≤Q ∧ |(u:ℚ)/v-y|<1/(2*(Q:ℚ)^2))) ∧
      (accept u v Q y).2≤500*w^2 := by
  let delta := cross (encode u) (encode y.den) (encode y.num) (encode v)
  let sq := multiply Q.bits Q.bits
  let lhs := multiply delta.1.digits sq.1
  let rhs := multiply y.den.bits v.bits
  let test := below (false::lhs.1) rhs.1
  let cap := below Q.bits y.den.bits
  obtain ⟨de,dc⟩ := cross_spec (encode u) (encode y.den) (encode y.num) (encode v) w
    (by simpa [encode,Nat.size_eq_bits_len] using uw) (by simpa [encode,Nat.size_eq_bits_len] using dw)
    (by simpa [encode,Nat.size_eq_bits_len] using nw) (by simpa [encode,Nat.size_eq_bits_len] using vw)
  have dl : delta.1.digits.length≤3*w+1 := cross_length _ _ _ _
    (by simpa [encode,Nat.size_eq_bits_len] using uw) (by simpa [encode,Nat.size_eq_bits_len] using dw)
    (by simpa [encode,Nat.size_eq_bits_len] using nw) (by simpa [encode,Nat.size_eq_bits_len] using vw)
  change delta.1.decode=_ at de
  change delta.2≤_ at dc
  simp only [decode_encode] at de
  have abs := (abs_decode delta.1).trans (congrArg Int.natAbs de)
  obtain ⟨sv,sl,sc⟩ := multiply_spec Q.bits Q.bits
  obtain ⟨lv,ll,lc⟩ := multiply_spec delta.1.digits sq.1
  obtain ⟨rv,rl,rc⟩ := multiply_spec y.den.bits v.bits
  change value sq.1=_ at sv; change sq.1.length≤_ at sl; change sq.2≤_ at sc
  change value lhs.1=_ at lv; change lhs.1.length≤_ at ll; change lhs.2≤_ at lc
  change value rhs.1=_ at rv; change rhs.1.length≤_ at rl; change rhs.2≤_ at rc
  simp only [value_bits,Nat.size_eq_bits_len] at sv sl sc rv rl rc
  obtain ⟨tv,tc⟩ := below_spec (false::lhs.1) rhs.1
  obtain ⟨cv,cc⟩ := below_spec Q.bits y.den.bits
  change (test.1=true ↔ _) at tv
  change (cap.1=true ↔ _) at cv
  simp only [value_bits] at cv
  simp only [value,Bool.toNat_false,Nat.zero_add,lv,sv,abs,rv] at tv
  change ((!cap.1 && test.1)=true ↔ _) ∧ delta.2+sq.2+lhs.2+rhs.2+test.2+cap.2+2≤_
  constructor
  · rw [accept_iff u v Q y vp]
    simp only [Bool.and_eq_true,Bool.not_eq_true']
    have cp : cap.1=false ↔ y.den≤Q := by cases e : cap.1 <;> simp [e] at cv ⊢ <;> omega
    rw [cp,tv,pow_two]
  · change test.2=7*max (lhs.1.length+1) rhs.1.length at tc
    change cap.2=7*max _ _ at cc
    rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len] at cc
    have sw : sq.1.length≤3*w := by omega
    have scw : sq.2≤16*w^2 := sc.trans (calc _ ≤ w*(w+5*(w+2*w)) := by gcongr
                                            _ = _ := by ring)
    have rcw : rhs.2≤16*w^2 := rc.trans (calc _ ≤ w*(w+5*(w+2*w)) := by gcongr
                                              _ = _ := by ring)
    have dcw : delta.1.digits.length≤4*w := by omega
    have lcw : lhs.2≤162*w^2 := lc.trans (calc
      _ ≤ (3*w)*(4*w+5*(4*w+2*(3*w))) := by gcongr
      _ = _ := by ring)
    have sqw := Nat.le_self_pow (n:=2) (by decide) w
    omega

def scan (u : ℤ) (v Q : ℕ) : List ℚ → Option ℚ × ℕ
  | [] => (none,0)
  | y::ys =>
    let gate := accept u v Q y
    if gate.1 then (some y,gate.2+1) else
      let tail := scan u v Q ys
      (tail.1,gate.2+1+tail.2)

private theorem scan_spec (u : ℤ) (v Q w : ℕ) (vp : 0<v) (wp : 1≤w)
    (uw : u.natAbs.size≤w) (vw : v.size≤w) (qw : Q.size≤w) (ys : List ℚ)
    (coords : ∀ y∈ys, y.num.natAbs.size≤w ∧ y.den.size≤w) :
    (scan u v Q ys).1=ys.find? (fun y => decide (y.den≤Q ∧ |(u:ℚ)/v-y|<1/(2*(Q:ℚ)^2))) ∧
      (scan u v Q ys).2≤ys.length*(500*w^2+1) := by
  induction ys with
  | nil => exact ⟨rfl,by simp [scan]⟩
  | cons y ys ih =>
    obtain ⟨cw,dw⟩ := coords y (by simp)
    obtain ⟨eq,paid⟩ := accept_spec u v Q y wp vp uw vw qw cw dw
    have ⟨tail,work⟩ := ih (fun z hz => coords z (by simp [hz]))
    have step : (accept u v Q y).2+1+(scan u v Q ys).2≤(y::ys).length*(500*w^2+1) := by
      rw [List.length_cons,Nat.succ_mul]; omega
    cases h : (accept u v Q y).1 with
    | true =>
      have ok := eq.mp h
      refine ⟨by simp only [scan,h,↓reduceIte,List.find?_cons,decide_eq_true ok],?_⟩
      simp only [scan,h,↓reduceIte]; omega
    | false =>
      have no := mt eq.mpr (by simp [h])
      refine ⟨?_,?_⟩
      · simp only [scan,h,Bool.false_eq_true,↓reduceIte,List.find?_cons,decide_eq_false no,tail]
      · simpa only [scan,h,Bool.false_eq_true,↓reduceIte] using step

/-- Scan the precise ordered list, stopping at the same first successful
candidate as reconstruct. The bound includes each candidate's signed arithmetic. -/
theorem reconstruct_scan {u : ℤ} {v Q : ℕ} (vp : 0<v) :
    let w := u.natAbs.size+v.size+Q.size+3
    (scan u v Q (convergents u v)).1=reconstruct u v Q ∧
      (scan u v Q (convergents u v)).2≤(2*v.log2+1)*(500*w^2+1) := by
  intro w
  have uw : u.natAbs.size≤w := by dsimp [w]; omega
  have vw : v.size≤w := by dsimp [w]; omega
  have qw : Q.size≤w := by dsimp [w]; omega
  let t := u.natAbs.size+v.size+Q.size
  have un : u.natAbs<2^t := (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide)
    (show u.natAbs.size≤t by dsimp [t]; omega))
  have vn : v<2^t := (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide)
    (show v.size≤t by dsimp [t]; omega))
  have height : u.natAbs+2*v<2^w := by
    change u.natAbs+2*v<2^(t+3)
    rw [pow_add]; norm_num; omega
  obtain ⟨exactAnswer,cost⟩ := scan_spec u v Q w vp (by dsimp [w]; omega) uw vw qw (convergents u v)
    (fun y hy => by
      have ⟨num,den⟩ := convergent_height u v vp y hy
      exact ⟨Nat.size_le.mpr (num.trans_lt height),Nat.size_le.mpr (den.trans_lt
        ((Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) vw)))⟩)
  exact ⟨exactAnswer,cost.trans (Nat.mul_le_mul_right _ (convergents_length u v vp))⟩

private theorem pow_word (k : ℕ) : value (List.replicate k false++[true])=2^k := by
  induction k with
  | zero => decide
  | succ k ih => simp [List.replicate_succ,value,ih,pow_succ,Nat.mul_comm]

/-- Integer portion of reconstructedProposal after its optional multiplier:
schoolbook multiplication, a low zero bit and comparison against the exact cap. -/
def finish (e bits : ℕ) : Option ℕ → Option (List Bool) × ℕ
  | none => (none,1)
  | some m =>
    let p := multiply e.bits m.bits
    let doubled := false::p.1
    let test := below (List.replicate bits false++[true]) doubled
    (if test.1 then none else some doubled,p.2+test.2+bits+3)

theorem finish_spec (e bits m : ℕ) {w : ℕ} (ew : e.size≤w) (mw : m.size≤w) :
    ((finish e bits (some m)).1.map value)=
      (if 2*(e*m)≤2^bits then some (2*(e*m)) else none) ∧
    (finish e bits (some m)).2≤16*w^2+7*(bits+3*w+2)+bits+3 := by
  let p := multiply e.bits m.bits
  let test := below (List.replicate bits false++[true]) (false::p.1)
  obtain ⟨pv,pl,pc⟩ := multiply_spec e.bits m.bits
  change value p.1=_ at pv; change p.1.length≤_ at pl; change p.2≤_ at pc
  simp only [value_bits,Nat.size_eq_bits_len] at pv pl pc
  obtain ⟨tv,tc⟩ := below_spec (List.replicate bits false++[true]) (false::p.1)
  change (test.1=true ↔ _) at tv; change test.2=_ at tc
  simp only [pow_word,value,Bool.toNat_false,Nat.zero_add,pv,Nat.mul_comm m e] at tv
  change (if test.1 then none else some (false::p.1)).map value=_ ∧ p.2+test.2+bits+3≤_
  constructor
  · by_cases h : 2*(e*m)≤2^bits
    · have no : test.1=false := Bool.eq_false_iff.mpr (fun ok => (Nat.not_lt_of_ge h) (tv.mp ok))
      rw [if_pos h]; simp only [no,Bool.false_eq_true,↓reduceIte,Option.map_some,value,Bool.toNat_false,Nat.zero_add,pv,Nat.mul_comm m e]
    · simp [h,tv.mpr (by omega)]
  · have prod : p.2≤16*w^2 := pc.trans (calc
      _ ≤ w*(w+5*(w+2*w)) := by gcongr
      _ = _ := by ring)
    simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil] at tc
    omega

theorem reconstructed_proposal_guard {ι : Type*} [Fintype ι] (approx : ι → ℚ) (Q e bits : ℕ)
    {w : ℕ} (ew : e.size≤w)
    (width : ∀ m, multiplier approx Q=some m → m.size≤w) :
    let out := finish e bits (multiplier approx Q)
    out.1.map (fun ds => TwoThirdsSearch.Proposal.exponent (value ds))=reconstructedProposal approx Q e bits ∧
      out.2≤16*w^2+7*(bits+3*w+2)+bits+3 := by
  cases h : multiplier approx Q with
  | none => simp [finish,reconstructedProposal,h]
  | some m =>
    have ⟨result,cost⟩ := finish_spec e bits m ew (width _ h)
    refine ⟨?_,cost⟩
    have eq := congrArg (Option.map TwoThirdsSearch.Proposal.exponent) result
    rw [Option.map_map] at eq
    simp only [reconstructedProposal,h]
    by_cases fit : 2*(e*m)≤2^bits <;> simpa [fit] using eq

private theorem quotient_width (v x : List Bool) : (divide v x).quotient.length=x.length := by
  induction x with | nil => rfl | cons b x ih => simp [divide,ih]

structure Step where
  quotient : ℤ
  remainder : ℕ
  gates : ℕ

/-- Unsigned long division followed by the floor correction for a negative
dividend. Normalize both output words before feeding them into the next step. -/
def divmod (u : ℤ) (v : ℕ) : Step :=
  let d := divide v.bits u.natAbs.bits
  let nz := below [] d.remainder
  let fix := decide (u<0) && nz.1
  let q := addDigits d.quotient.length d.quotient [] fix
  let w := max v.bits.length d.remainder.length
  let complement := subtract w v.bits d.remainder false
  let rem := if fix then complement.digits else d.remainder
  let qc := canonical q.1
  let rc := canonical rem
  ⟨signed (decide (u<0)) (value qc.1),value rc.1,
    d.gates+nz.2+q.2+complement.gates+qc.2+rc.2+3⟩

set_option maxHeartbeats 800000 in
theorem divmod_spec (u : ℤ) (v w : ℕ) (vp : 0<v) (uw : u.natAbs.size≤w) (vw : v.size≤w) :
    (divmod u v).quotient=u/(v:ℤ) ∧ (divmod u v).remainder=(u%(v:ℤ)).toNat ∧
      (divmod u v).gates≤100*(w+1)^2 := by
  let d := divide v.bits u.natAbs.bits
  let nz := below [] d.remainder
  let fix := decide (u<0) && nz.1
  let q := addDigits d.quotient.length d.quotient [] fix
  let k := max v.bits.length d.remainder.length
  let c := subtract k v.bits d.remainder false
  let r := if fix then c.digits else d.remainder
  obtain ⟨width,dr,de,small,dc⟩ := divide_spec v.bits u.natAbs.bits (by simpa)
  change d.width=_ at width; change d.remainder.length≤d.width at dr
  change value u.natAbs.bits=value d.quotient*value v.bits+value d.remainder at de
  change value d.remainder<value v.bits at small; change d.gates≤_ at dc
  simp only [value_bits,Nat.size_eq_bits_len] at width de small dc
  obtain ⟨neq,ncost⟩ := below_spec [] d.remainder
  change (nz.1=true ↔ 0<value d.remainder) at neq
  change nz.2=7*max 0 d.remainder.length at ncost
  have ql : d.quotient.length=u.natAbs.size := (quotient_width ..).trans (Nat.size_eq_bits_len _)
  obtain ⟨al,ac,av⟩ := addDigits_spec d.quotient.length d.quotient [] fix le_rfl (by simp)
  change q.1.length=_ at al; change q.2=_ at ac
  change value q.1=value d.quotient+0+fix.toNat at av
  obtain ⟨cl,cc,cv⟩ := subtract_spec k v.bits d.remainder false (le_max_left ..) (le_max_right ..)
  change c.digits.length=_ at cl; change c.gates=_ at cc
  change value c.digits+value d.remainder+0=value v.bits+2^k*c.borrow.toNat at cv
  rw [value_bits] at cv
  have lt := value_lt c.digits
  rw [cl] at lt
  have complement : value c.digits+value d.remainder=v := by
    cases h : c.borrow <;> simp [h] at cv <;> omega
  obtain ⟨qc,qcost⟩ := canonical_spec q.1
  obtain ⟨rc,rcost⟩ := canonical_spec r
  have ar : value (canonical r).1=value r := by rw [rc,value_bits]
  have aq : value (canonical q.1).1=value q.1 := by rw [qc,value_bits]
  have vi : (0:ℤ)<v := by exact_mod_cast vp
  let a := signed (decide (u<0)) (value (canonical q.1).1)
  let b := value (canonical r).1
  have divEq : u/(v:ℤ)=a ∧ u%(v:ℤ)=(b:ℤ) := by
    apply (Int.ediv_emod_unique vi).mpr
    obtain ⟨de',cv'⟩ : ((u.natAbs:ℕ):ℤ)=((value d.quotient:ℕ):ℤ)*v+value d.remainder ∧
        ((value c.digits:ℕ):ℤ)+value d.remainder=v := by exact_mod_cast And.intro de complement
    change ↑(value (canonical r).1)+(v:ℤ)*signed (decide (u<0)) (value (canonical q.1).1)=u ∧
      0≤(↑(value (canonical r).1):ℤ) ∧ (↑(value (canonical r).1):ℤ)<v
    rw [ar,aq,av,Nat.add_zero]
    by_cases neg : u<0
    · have mag := Int.ofNat_natAbs_of_nonpos neg.le
      cases nonzero : nz.1 with
      | false =>
        have rz : value d.remainder=0 := by rw [nonzero] at neq; simp at neq; omega
        simp only [r,fix,neg,decide_true,nonzero,Bool.and_false,Bool.false_eq_true,↓reduceIte,
          signed,Bool.toNat_false,Nat.add_zero,rz,Int.natCast_zero,zero_add]
        refine ⟨?_,by decide,vi⟩
        rw [rz,Int.natCast_zero,add_zero] at de'
        nlinarith only [de',mag]
      | true =>
        have rp := neq.mp nonzero
        simp only [r,fix,neg,decide_true,nonzero,Bool.and_self,↓reduceIte,signed,Bool.toNat_true]
        push_cast
        exact ⟨by nlinarith only [de',mag,cv'],by positivity,by omega⟩
    · have mag := Int.natAbs_of_nonneg (le_of_not_gt neg)
      simp only [r,fix,neg,decide_false,Bool.false_and,Bool.false_eq_true,↓reduceIte,signed,
        Bool.toNat_false,Nat.add_zero]
      exact ⟨by nlinarith only [de',mag],by positivity,by exact_mod_cast small⟩
  change a=u/(v:ℤ) ∧ b=(u%(v:ℤ)).toNat ∧
    d.gates+nz.2+q.2+c.gates+(canonical q.1).2+(canonical r).2+3≤_
  refine ⟨divEq.1.symm,by rw [divEq.2,Int.toNat_natCast],?_⟩
  have kw : k≤2*w := by dsimp [k]; rw [Nat.size_eq_bits_len]; omega
  have rl : r.length≤2*w := by dsimp only [r]; split <;> omega
  have bound : d.gates≤w*(20*w+1) := dc.trans (Nat.mul_le_mul uw (by omega))
  nlinarith only [bound,ncost,ac,cc,qcost,rcost,kw,rl,al,ql,vw,uw,dr,width,
    show max 0 d.remainder.length=d.remainder.length from Nat.zero_max _]

def lift (a : ℤ) (y : Fraction) : Fraction × ℕ :=
  let s := cross (encode a) (encode y.1) (encode (-(y.2:ℤ))) (encode 1)
  let c := canonical s.1.digits
  ((signed s.1.negative (value c.1),y.1.natAbs),s.2+c.2+1)

private theorem lift_spec (a : ℤ) (y : ℚ) (w : ℕ) (pos : 0<y.num) (wp : 1≤w)
    (aw : a.natAbs.size≤w) (nw : y.num.natAbs.size≤w) (dw : y.den.size≤w) :
    (lift a (coords y)).1=coords ((a:ℚ)+y⁻¹) ∧ (lift a (coords y)).2≤150*w^2 := by
  let s := cross (encode a) (encode y.num) (encode (-(y.den:ℤ))) (encode 1)
  have aW : (encode a).digits.length≤w := by simpa [encode,Nat.size_eq_bits_len] using aw
  have nW : (encode y.num).digits.length≤w := by simpa [encode,Nat.size_eq_bits_len] using nw
  have dW : (encode (-(y.den:ℤ))).digits.length≤w := by simpa [encode,Nat.size_eq_bits_len] using dw
  have one : (encode 1).digits.length≤w := wp
  have ⟨decoded,paid⟩ := cross_spec _ _ _ _ w aW nW dW one
  have sl : s.1.digits.length≤3*w+1 := cross_length _ _ _ _ aW nW dW one
  change s.1.decode=_ at decoded
  change s.2≤_ at paid
  simp only [decode_encode,mul_one,sub_neg_eq_add] at decoded
  obtain ⟨can,cost⟩ := canonical_spec s.1.digits
  have ⟨num,den⟩ := next_coordinates a y pos
  change (signed s.1.negative (value (canonical s.1.digits).1),y.num.natAbs)=_ ∧ s.2+(canonical s.1.digits).2+1≤_
  rw [can,value_bits]
  change (s.1.decode,y.num.natAbs)=_ ∧ _
  rw [decoded,coords,num,den]
  have sq := Nat.le_self_pow (n:=2) (by decide) w
  exact ⟨rfl,by omega⟩

def lifts (a : ℤ) : List Fraction → List Fraction × ℕ
  | [] => ([],0)
  | y::ys =>
    let q := lift a y
    let tail := lifts a ys
    (q.1::tail.1,q.2+1+tail.2)

private theorem lifts_spec (a : ℤ) (ys : List ℚ) (w : ℕ) (wp : 1≤w) (aw : a.natAbs.size≤w)
    (bounded : ∀ y∈ys, 0<y.num ∧ y.num.natAbs.size≤w ∧ y.den.size≤w) :
    (lifts a (ys.map coords)).1=(ys.map (fun y => (a:ℚ)+y⁻¹)).map coords ∧
    (lifts a (ys.map coords)).2≤ys.length*(150*w^2+1) := by
  induction ys with
  | nil => exact ⟨rfl,by simp [lifts]⟩
  | cons y ys ih =>
    have ⟨pos,nw,dw⟩ := bounded y (by simp)
    have ⟨eq,cost⟩ := lift_spec a y w pos wp aw nw dw
    have ⟨rest,paid⟩ := ih (fun z hz => bounded z (by simp [hz]))
    simp only [List.map_cons,lifts]
    refine ⟨by rw [eq,rest],?_⟩
    rw [List.length_cons,Nat.succ_mul]; omega

private theorem remainder_lt (u : ℤ) (v : ℕ) (vp : 0<v) : (divmod u v).remainder<v := by
  have eq := (divmod_spec u v (max u.natAbs.size v.size) vp (le_max_left ..) (le_max_right ..)).2.1
  have vi : (0:ℤ)<v := by exact_mod_cast vp
  have := Int.emod_lt_of_pos u vi
  rw [eq]; omega

/-- Construct the entire ordered list from signed Euclidean steps, applying
the exact integer-coordinate recurrence while unwinding the same recursion. -/
def generate (u : ℤ) (v : ℕ) : List Fraction × ℕ :=
  if vp : v=0 then ([(0,1)],1) else
    let d := divmod u v
    if d.remainder=0 then ([(d.quotient,1)],d.gates+2) else
      let tail := generate (v:ℤ) d.remainder
      let lifted := lifts d.quotient tail.1
      ((d.quotient,1)::lifted.1,d.gates+tail.2+lifted.2+2)
termination_by v
decreasing_by exact remainder_lt _ _ (Nat.pos_of_ne_zero vp)

theorem generate_spec (u : ℤ) (v w : ℕ) (vp : 0<v) (uw : u.natAbs.size≤w) (vw : v.size≤w) :
    let L := (convergents u v).length
    (generate u v).1=(convergents u v).map coords ∧
      (generate u v).2≤L^2*(400*(w+3)^2) := by
  induction v using Nat.strong_induction_on generalizing u with
  | h v ih =>
    let d := divmod u v
    let a := u/(v:ℤ)
    let r := (u%(v:ℤ)).toNat
    have ⟨dq,dr,dc⟩ := divmod_spec u v w vp uw vw
    change d.quotient=a at dq; change d.remainder=r at dr; change d.gates≤_ at dc
    have rv : r<v := dr ▸ remainder_lt u v vp
    have head : (a:ℚ)∈convergents u v := by
      rw [convergents,dif_neg vp.ne']; dsimp only; split <;> simp [a]
    have num := (convergent_height u v vp _ head).1
    simp only [Rat.num_intCast] at num
    have aw : a.natAbs.size≤w+3 := by
      apply Nat.size_le.mpr
      have nu := (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) uw)
      have nv := (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) vw)
      rw [pow_add]; norm_num; omega
    rw [generate,dif_neg vp.ne',convergents,dif_neg vp.ne']
    dsimp only
    simp only [show (divmod u v).remainder=r from dr,show (divmod u v).quotient=a from dq]
    have smallCost : d.gates+2≤400*(w+3)^2 := by
      have hi := Nat.pow_le_pow_left (show w+1≤w+3 by omega) 2
      have lo : 0<(w+3)^2 := by positivity
      omega
    by_cases rz : r=0
    · have rz' : (u%(v:ℤ)).toNat=0 := rz
      simp only [rz,rz',↓reduceIte,List.map_cons,List.map_nil,List.length_cons,List.length_nil,
        coords,Rat.num_intCast,Rat.den_intCast]
      exact ⟨rfl,by simpa using smallCost⟩
    · have rp : 0<r := Nat.pos_of_ne_zero rz
      have rw' : r.size≤w := Nat.size_le.mpr (rv.trans ((Nat.lt_size_self _).trans_le
        (Nat.pow_le_pow_right (by decide) vw)))
      have ⟨tail,paid⟩ := ih r rv (v:ℤ) rp (by simpa using vw) rw'
      let ys := convergents (v:ℤ) r
      have ⟨lifted,lc⟩ := lifts_spec a ys (w+3) (by omega) aw (fun y h => by
        have ⟨pos,yn,yd⟩ := positive_bounds v r rp rv.le y h
        have hi := (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) vw)
        have dn := (Nat.size_le.mpr (yd.trans_lt (rv.trans hi)))
        have pn := (Nat.size_le.mpr (yn.trans_lt hi))
        exact ⟨pos,by omega,by omega⟩)
      have rz' : (u%(v:ℤ)).toNat≠0 := rz
      simp only [if_neg rz,if_neg rz',tail,List.map_cons,coords,Rat.num_intCast,Rat.den_intCast,
        List.length_cons,List.length_map]
      change (a,1)::(lifts a (ys.map coords)).1=(a,1)::(ys.map _).map coords ∧
        d.gates+(generate (v:ℤ) r).2+(lifts a (ys.map coords)).2+2≤(ys.length+1)^2*(400*(w+3)^2)
      refine ⟨congrArg ((a,1)::·) lifted,?_⟩
      change (generate (v:ℤ) r).2≤ys.length^2*(400*(w+3)^2) at paid
      have upper : 150*(w+3)^2+1≤400*(w+3)^2 := by nlinarith
      have cost := lc.trans (Nat.mul_le_mul_left ys.length upper)
      let M := 400*(w+3)^2
      change d.gates+2≤M at smallCost
      change (generate (v:ℤ) r).2≤ys.length^2*M at paid
      change (lifts a (ys.map coords)).2≤ys.length*M at cost
      change _≤(ys.length+1)^2*M
      have hle : ys.length^2*M+ys.length*M+M≤(ys.length+1)^2*M := by nlinarith only [Nat.zero_le (ys.length*M)]
      omega

open Reconstruction

def scanPairs (u : ℤ) (v Q : ℕ) : List Fraction → Option Fraction × ℕ
  | [] => (none,0)
  | y::ys =>
    let gate := acceptPair u v Q y
    if gate.1 then (some y,gate.2+1) else
      let tail := scanPairs u v Q ys
      (tail.1,gate.2+1+tail.2)

private theorem scanPairs_spec (u : ℤ) (v Q : ℕ) (ys : List ℚ) :
    scanPairs u v Q (ys.map coords)=((scan u v Q ys).1.map coords,(scan u v Q ys).2) := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    cases gate : (acceptPair u v Q (coords y)).1
    · simp only [List.map_cons,scanPairs,scan,accept,gate,Bool.false_eq_true,↓reduceIte,ih]
    · simp only [List.map_cons,scanPairs,scan,accept,gate,↓reduceIte,Option.map_some]

def reconstructBits (u : ℤ) (v Q : ℕ) : Option Fraction × ℕ :=
  let output := generate u v
  let checked := scanPairs u v Q output.1
  (checked.1,output.2+checked.2)

/-- Complete signed rational reconstruction. Cost covers producing all
convergents, including Euclidean division and normalized binary coordinates,
and the same ordered stopping test as the driver's reconstruct. -/
theorem reconstruct_bits (u : ℤ) (v Q : ℕ) (vp : 0<v) :
    let w := u.natAbs.size+v.size+Q.size+3
    let L := 2*v.log2+1
    (reconstructBits u v Q).1=(reconstruct u v Q).map coords ∧
      (reconstructBits u v Q).2≤L^2*(400*(w+3)^2)+L*(500*w^2+1) := by
  intro w L
  obtain ⟨list,work⟩ := generate_spec u v w vp (by dsimp [w]; omega) (by dsimp [w]; omega)
  obtain ⟨answer,scanCost⟩ := reconstruct_scan (u:=u) (Q:=Q) vp
  have eq := scanPairs_spec u v Q (convergents u v)
  have len : (convergents u v).length≤L := convergents_length _ _ vp
  simp only [reconstructBits,list,eq,answer]
  refine ⟨trivial,Nat.add_le_add ?_ scanCost⟩
  exact work.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left len 2))

open Reconstruction BinaryDivision

private def get {ι : Type*} (x : ι → ℚ) (Q : ℕ) (i : ι) := reconstruct (x i).num (x i).den Q

private theorem get_den_le {ι : Type*} (x : ι → ℚ) (Q : ℕ) {i : ι} {y : ℚ}
    (hit : get x Q i=some y) : y.den≤Q := by
  have p := List.find?_some (show (convergents (x i).num (x i).den).find? _=some y from hit)
  exact (decide_eq_true_eq.mp p).1

/-- Use each reconstructed denominator once and merge the successful suffix
by binary LCM. Encountering a failed coordinate returns immediately. -/
def vector {ι : Type*} (x : ι → ℚ) (Q : ℕ) : List ι → Option ℕ × ℕ
  | [] => (some 1,1)
  | i::rest =>
    let y := reconstructBits (x i).num (x i).den Q
    match y.1 with
    | none => (none,y.2+1)
    | some z =>
      let tail := vector x Q rest
      match tail.1 with
      | none => (none,y.2+tail.2+2)
      | some m =>
        let next := BinaryCollector.lcmBits z.2.bits m.bits
        (some (value next.1),y.2+tail.2+next.2+3)

def coordinateBudget (h : ℕ) :=
  let w := 3*h+3
  let L := 2*h+1
  L^2*(400*(w+3)^2)+L*(500*w^2+1)

private theorem vector_spec {ι : Type*} [DecidableEq ι] (x : ι → ℚ) (Q h K : ℕ)
    (qw : Q.size≤h) (xs : List ι) (lengthBound : xs.length≤K)
    (width : ∀ i∈xs, (x i).num.natAbs.size≤h ∧ (x i).den.size≤h) :
    let D := fun i => ((get x Q i).getD 0).den
    let w := 1+Q.size*(K+1)
    (vector x Q xs).1=(if xs.all (fun i => (get x Q i).isSome) then some (xs.toFinset.lcm D) else none) ∧
      (∀ m, (vector x Q xs).1=some m → 0 < m ∧ m≤(2^Q.size)^xs.length) ∧
      (vector x Q xs).2≤1+xs.length*(coordinateBudget h+BinaryCollector.lcmBudget w+3) := by
  let w := 1+Q.size*(K+1)
  let p := coordinateBudget h+BinaryCollector.lcmBudget w+3
  let D := fun i => ((get x Q i).getD 0).den
  change _= (if _ then some (xs.toFinset.lcm D) else none) ∧ _ ∧ (vector x Q xs).2≤1+xs.length*p
  induction xs with
  | nil =>
    simp [vector]
  | cons i xs ih =>
    have len : xs.length≤K := (Nat.le_succ _).trans lengthBound
    have ⟨tail,size,paid⟩ := ih len (fun j hj => width j (by simp [hj]))
    have ⟨nw,dw⟩ := width i (by simp)
    let y := reconstructBits (x i).num (x i).den Q
    have ⟨eq,cr⟩ := reconstruct_bits (x i).num (x i).den Q (x i).pos
    change y.1=(get x Q i).map coords at eq
    have yl : (x i).den.log2≤h := (Nat.lt_size.mpr (Nat.log2_self_le (x i).pos.ne')).le.trans dw
    have yw : (x i).num.natAbs.size+(x i).den.size+Q.size+3≤3*h+3 := by omega
    have lB : 2*(x i).den.log2+1≤2*h+1 := by omega
    have recCost : y.2≤coordinateBudget h := cr.trans (Nat.add_le_add
      (Nat.mul_le_mul (Nat.pow_le_pow_left lB 2) (Nat.mul_le_mul_left 400
        (Nat.pow_le_pow_left (Nat.add_le_add_right yw 3) 2)))
      (Nat.mul_le_mul lB (Nat.add_le_add_right (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left yw 2)) 1)))
    have charged : 1+xs.length*p+p=1+(i::xs).length*p := by rw [List.length_cons,Nat.succ_mul]; omega
    cases hi : get x Q i with
    | none =>
      have ans : y.1=none := by simpa [hi] using eq
      change (reconstructBits (x i).num (x i).den Q).1=none at ans
      simp only [vector,ans,hi,List.all_cons,Option.isSome_none,Bool.false_and,Bool.false_eq_true,↓reduceIte]
      refine ⟨trivial,by simp,?_⟩
      change y.2+1≤_
      dsimp only [p] at charged; dsimp only [p]; omega
    | some z =>
      have ans : (reconstructBits (x i).num (x i).den Q).1=some (coords z) := by simpa [hi] using eq
      have den : z.den≤Q := get_den_le x Q hi
      have dz : D i=z.den := by simp [D,hi]
      simp only [vector,ans,List.all_cons,hi,Option.isSome_some,Bool.true_and,List.toFinset_cons,Finset.lcm_insert,dz]
      cases ht : (vector x Q xs).1 with
      | none =>
        rw [ht] at tail
        have failed : xs.all (fun j => (get x Q j).isSome)=false := by
          cases h : xs.all (fun j => (get x Q j).isSome) <;> simp [h] at tail ⊢
        simp only [failed,Bool.false_eq_true,↓reduceIte]
        refine ⟨trivial,by simp,?_⟩
        change y.2+(vector x Q xs).2+2≤_
        have step : y.2+2≤p := by dsimp [p]; omega
        omega
      | some m =>
        have ⟨mp,mb⟩ := size _ ht
        have mw : m.size≤w := by
          apply Nat.size_le.mpr
          rw [←pow_mul] at mb
          have cap : Q.size*xs.length+1≤w := by
            have := Nat.mul_le_mul_left Q.size len; dsimp [w]; rw [Nat.mul_succ]; omega
          exact (mb.trans_lt (Nat.pow_lt_pow_right (by decide : 1<2) (Nat.lt_succ_self _))).trans_le
            (Nat.pow_le_pow_right (by decide) cap)
        have zw : z.den.size≤w := by
          apply Nat.size_le.mpr
          have one : Q.size≤w := by dsimp [w]; rw [Nat.mul_succ]; omega
          exact (den.trans_lt (Nat.lt_size_self Q)).trans_le (Nat.pow_le_pow_right (by decide) one)
        have ⟨lcm,cost⟩ := BinaryCollector.lcm_spec z.den m w z.pos zw mw
        rw [ht] at tail
        have passed : xs.all (fun j => (get x Q j).isSome)=true := by
          cases h : xs.all (fun j => (get x Q j).isSome) <;> simp [h] at tail ⊢
        simp only [passed,↓reduceIte] at tail ⊢
        have mval := Option.some.inj tail
        change some (value (BinaryCollector.lcmBits z.den.bits m.bits).1)=some _ ∧
          (∀ j, some (value (BinaryCollector.lcmBits z.den.bits m.bits).1)=some j → _) ∧
          y.2+(vector x Q xs).2+(BinaryCollector.lcmBits z.den.bits m.bits).2+3≤_
        rw [lcm,value_bits]
        refine ⟨by rw [mval]; rfl,?_,?_⟩
        · intro j hj
          cases hj
          refine ⟨Nat.lcm_pos z.pos mp,?_⟩
          rw [List.length_cons,pow_succ,Nat.mul_comm _ (2^Q.size)]
          exact (Nat.lcm_le_mul z.pos mp).trans (Nat.mul_le_mul (den.trans (Nat.lt_size_self Q).le) mb)
        · have step : y.2+(BinaryCollector.lcmBits z.den.bits m.bits).2+3≤p := by dsimp [p]; omega
          omega

/-- Complete archimedean reconstruction after the linear solve on k
coordinates, including the coordinate-denominator LCM and the integer guard. -/
def proposal {k : ℕ} (x : Fin k → ℚ) (Q e bits : ℕ) : Option (List Bool) × ℕ :=
  let m := vector x Q (List.finRange k)
  let out := finish e bits m.1
  (out.1,m.2+out.2)

theorem proposal_spec {k : ℕ} (x : Fin k → ℚ) (Q e bits h : ℕ)
    (qw : Q.size≤h) (width : ∀ i, (x i).num.natAbs.size≤h ∧ (x i).den.size≤h) :
    let w := 1+Q.size*(k+1)
    let S := max e.size w
    (proposal x Q e bits).1.map (fun b => TwoThirdsSearch.Proposal.exponent (value b))=
        reconstructedProposal x Q e bits ∧
      (proposal x Q e bits).2≤1+k*(coordinateBudget h+BinaryCollector.lcmBudget w+3)+
        (16*S^2+7*(bits+3*S+2)+bits+3) := by
  intro w S
  let xs := List.finRange k
  obtain ⟨eq,size,work⟩ := vector_spec x Q h k qw xs (by simp [xs]) (fun i _ => width i)
  have bound : (vector x Q xs).1=multiplier x Q := by
    rw [eq,multiplier]
    simp [xs,List.all_eq_true,get]
  have paid (m : ℕ) (hm : multiplier x Q=some m) : m.size≤S := by
    have b := (size m (bound.trans hm)).2
    simp only [xs,List.length_finRange,←pow_mul] at b
    apply (Nat.size_le.mpr ?_).trans (le_max_right e.size w)
    exact (b.trans_lt (Nat.pow_lt_pow_right (by decide : 1<2) (Nat.lt_succ_self _))).trans_le
      (Nat.pow_le_pow_right (by decide) (by dsimp [w]; rw [Nat.mul_succ]; omega))
  have ⟨result,finishCost⟩ := reconstructed_proposal_guard x Q e bits (le_max_left e.size w) paid
  change (finish e bits (vector x Q xs).1).1.map _=_ ∧ (vector x Q xs).2+(finish e bits (vector x Q xs).1).2≤_
  rw [bound]
  simp only [xs,List.length_finRange] at work
  exact ⟨result,Nat.add_le_add work finishCost⟩

open Reconstruction BinaryDivision BinaryPivot BinaryModularPower BinarySaturation TwoThirdsSearch

private theorem finish_width {e bits S : ℕ} {m : Option ℕ} {ds : List Bool} (ew : e.size≤S)
    (mw : ∀ j, m=some j → j.size≤S) (out : (finish e bits m).1=some ds) :
    ds.length≤3*S+1 ∧ value ds≤2^bits := by
  cases m with
  | none => simp [finish] at out
  | some j =>
    have jw := mw _ rfl
    have eq := (finish_spec e bits j ew jw).1
    rw [out,Option.map_some] at eq
    have le : value ds≤2^bits := by
      split at eq <;> simp_all
    refine ⟨?_,le⟩
    let p := multiply e.bits j.bits
    have len := (multiply_spec e.bits j.bits).2.1
    change p.1.length≤_ at len
    rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len] at len
    change (if _ then none else some (false::p.1))=some ds at out
    split at out <;> cases out
    simp only [List.length_cons]; omega

def verified {k : ℕ} (n g : ℕ) (x : Fin k → ℚ) (Q e bits : ℕ) : Option ℕ × ℕ :=
  let p := proposal x Q e bits
  match p.1 with
  | none => (none,p.2+1)
  | some ds =>
    let word := canonical ds
    let check := checkExponent n g (value word.1)
    (if check.1 then some (value word.1) else none,p.2+word.2+check.2+2)

def hitValue {n g : ℕ} : Hit n g → ℕ
  | .divisor d _ => d
  | .exponent a _ => a

/-- The whole reconstruction and exponent-verification suffix of a successful
archimedean solve. The bound includes producing the canonical word consumed
by the modular powering circuit, also on a failed modular check. -/
theorem verified_proposal_spec {k : ℕ} (n g : ℕ) (pos : 0<n) (x : Fin k → ℚ) (Q e bits h : ℕ)
    (qw : Q.size≤h) (width : ∀ i, (x i).num.natAbs.size≤h ∧ (x i).den.size≤h) :
    let w := 1+Q.size*(k+1)
    let S := max e.size w
    let P := 1+k*(coordinateBudget h+BinaryCollector.lcmBudget w+3)+(16*S^2+7*(bits+3*S+2)+bits+3)
    (verified n g x Q e bits).1=(verify n g (reconstructedProposal x Q e bits)).map hitValue ∧
      (verified n g x Q e bits).2≤P+3*(3*S+1)+powerBudget g.size (bits+1) n.size+n.size+(bits+1)+7 := by
  intro w S P
  have ⟨eq,work⟩ := proposal_spec x Q e bits h qw width
  change (proposal x Q e bits).2≤P at work
  obtain ⟨_,size,_⟩ := vector_spec x Q h k qw (List.finRange k) (by simp) (fun i _ => width i)
  have mw (j : ℕ) (hit : (vector x Q (List.finRange k)).1=some j) : j.size≤S := by
    have b := (size j hit).2
    simp only [List.length_finRange,←pow_mul] at b
    apply (Nat.size_le.mpr ?_).trans (le_max_right e.size w)
    exact (b.trans_lt (Nat.pow_lt_pow_right (by decide : 1<2) (Nat.lt_succ_self _))).trans_le
      (Nat.pow_le_pow_right (by decide) (by dsimp [w]; rw [Nat.mul_succ]; omega))
  rw [←eq]
  cases hp : (proposal x Q e bits).1 with
  | none => simp only [verified,hp,Option.map_none,verify]; exact ⟨trivial,by omega⟩
  | some ds =>
    have ⟨dl,cap⟩ := finish_width (le_max_left e.size w) mw hp
    have vS : (value ds).size≤bits+1 := Nat.size_le.mpr
      (cap.trans_lt (Nat.pow_lt_pow_right (by decide : 1<2) (Nat.lt_succ_self bits)))
    have ⟨wc,cost⟩ := canonical_spec ds
    have val : value (canonical ds).1=value ds := by rw [wc,value_bits]
    have ⟨ok,check⟩ := checkExponent_spec n g (value ds)
    have checkCost := check pos
    have upper := show powerBudget g.size (value ds).size n.size≤powerBudget g.size (bits+1) n.size by
      unfold powerBudget; gcongr
    simp only [verified,hp,Option.map_some,val]
    constructor
    · by_cases h : ValidExponent n g (value ds)
      · have good := ok.mpr h
        simp only [good,↓reduceIte,verify,show 2≤value ds ∧ 2∣value ds ∧ ModularPower.powMod g (value ds) n=1 from h,
          and_self,↓reduceDIte,Option.map_some,hitValue]
      · have bad := Bool.eq_false_iff.mpr (fun v => h (ok.mp v))
        simp only [bad,Bool.false_eq_true,↓reduceIte,verify,
          show ¬(2≤value ds ∧ 2∣value ds ∧ ModularPower.powMod g (value ds) n=1) from h,↓reduceDIte,Option.map_none]
    · change ds.length≤3*S+1 at dl
      omega

end Cogentic.BinaryReconstruction

#print axioms Cogentic.BinaryReconstruction.reconstruct_scan
#print axioms Cogentic.BinaryReconstruction.reconstructed_proposal_guard
#print axioms Cogentic.BinaryReconstruction.generate_spec
#print axioms Cogentic.BinaryReconstruction.reconstruct_bits
#print axioms Cogentic.BinaryReconstruction.proposal_spec
#print axioms Cogentic.BinaryReconstruction.verified_proposal_spec
