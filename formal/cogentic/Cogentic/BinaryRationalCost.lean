import Cogentic.MarkDistanceCost
import Cogentic.PerturbationCost

namespace Cogentic.BinaryRational
open BinaryDivision BinaryPivot BinaryPerturbation BinaryMarkDistance

abbrev Word := SignedWord × List Bool

def pack (x : ℚ) : Word := (encode x.num,x.den.bits)
def unpack (x : Word) : ℚ := (x.1.decode:ℚ)/value x.2
def width (x : ℚ) := max x.num.natAbs.size x.den.size
def budget (W : ℕ) := 2^20*(W+1)^3

@[simp] theorem unpack_pack (x : ℚ) : unpack (pack x)=x := by simp [unpack,pack,Rat.num_div_den]

private theorem widths (x : ℚ) {W : ℕ} (h : width x≤W) :
    (pack x).1.digits.length≤W ∧ (pack x).2.length≤W := by
  simpa only [width,pack,encode,Nat.size_eq_bits_len] using max_le_iff.mp h

private theorem denPositive (x : ℚ) : 0<value (pack x).2 := by simpa [pack] using x.den_pos

private def negateWord (x : SignedWord) : SignedWord := ⟨!x.negative,x.digits⟩
private theorem negate_value (x : SignedWord) : (negateWord x).decode= -x.decode := by
  cases x with | mk b ls => cases b <;> simp [negateWord,SignedWord.decode,signed]

private def product (x y : SignedWord) : SignedWord×ℕ :=
  let m := multiply y.digits x.digits
  (⟨xor x.negative y.negative,m.1⟩,m.2+1)

private theorem product_spec (x y : SignedWord) (W : ℕ) (hx : x.digits.length≤W) (hy : y.digits.length≤W) :
    (product x y).1.decode=x.decode*y.decode ∧ (product x y).1.digits.length≤3*W ∧
    (product x y).2≤16*W^2+1 := by
  obtain ⟨v,l,c⟩ := multiply_spec y.digits x.digits
  have cap := c.trans (Nat.mul_le_mul hx (show y.digits.length+5*(y.digits.length+2*x.digits.length)≤W+5*(W+2*W) by omega))
  refine ⟨?_,by dsimp [product];omega,by dsimp [product];nlinarith only [cap]⟩
  simp only [product,SignedWord.decode,v]
  cases x.negative <;> cases y.negative <;> simp [signed]

/-- Reduce the unsigned numerator and denominator by their binary gcd, then
restore the numerator's sign and normalize zero. -/
def normalize (x : SignedWord) (den : List Bool) : Word×ℕ :=
  let r := reduced x.digits den
  let n := adjust (encode 0) r.1.1 (!x.negative)
  ((n.1,r.1.2),r.2+n.2+2)

private theorem normalize_spec (x : SignedWord) (den : List Bool) (pos : 0<value den)
    (W : ℕ) (hx : x.digits.length≤W) (hd : den.length≤W) :
    (normalize x den).1=pack ((x.decode:ℚ)/value den) ∧ (normalize x den).2≤150*(W+1)^3 := by
  let f := (value x.digits:ℚ)/value den
  obtain ⟨v,c⟩ := reduced_spec x.digits den pos W hx hd
  change (reduced x.digits den).1=(f.num.natAbs.bits,f.den.bits) at v
  have fp : 0≤f := by dsimp [f];positivity
  have nn := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr fp)
  have mag : f.num.natAbs≤value x.digits := by
    have fe : f=mkRat (value x.digits) (value den) := by dsimp [f];rw [Rat.mkRat_eq_div];rfl
    rw [fe,Rat.num_mkRat,if_neg pos.ne']
    simp only [Int.natAbs_natCast]
    rw [←Int.natCast_ediv,Int.natAbs_natCast]
    exact Nat.div_le_self ..
  have fl := (Nat.size_le_size mag).trans ((Nat.size_le.mpr (value_lt x.digits)).trans hx)
  obtain ⟨out,_,pay⟩ := adjust_spec (encode 0) f.num.natAbs.bits (!x.negative)
  simp only [decode_encode,value_bits,show (encode 0).digits.length=0 from rfl,Nat.zero_max,Nat.size_eq_bits_len] at out pay
  simp only [normalize,v,out,pay]
  refine ⟨?_,?_⟩
  · cases h : x.negative
    · have same : (x.decode:ℚ)/value den=f := by simp [SignedWord.decode,h,signed,f]
      rw [same];simp [pack,signed,nn]
    · have same : (x.decode:ℚ)/value den= -f := by simp [SignedWord.decode,h,signed,f,neg_div]
      rw [same];simp [pack,signed,nn]
  · nlinarith only [c,fl,Nat.zero_le W,Nat.zero_le (W^2),Nat.zero_le (W^3)]

private def plusMinus (subtract : Bool) (x y : Word) : Word×ℕ :=
  let a := product x.1 ⟨false,y.2⟩
  let b := product y.1 ⟨false,x.2⟩
  let c := adjust a.1 b.1.digits (if subtract then b.1.negative else !b.1.negative)
  let d := multiply x.2 y.2
  let r := normalize c.1 d.1
  (r.1,a.2+b.2+c.2+d.2+r.2+4)

private theorem plusMinus_spec (sub : Bool) (x y : ℚ) (W : ℕ) (hx : width x≤W) (hy : width y≤W) :
    (plusMinus sub (pack x) (pack y)).1=pack (if sub then x-y else x+y) ∧
    (plusMinus sub (pack x) (pack y)).2≤budget W := by
  let X := pack x
  let Y := pack y
  let a := product X.1 ⟨false,Y.2⟩
  let b := product Y.1 ⟨false,X.2⟩
  let c := adjust a.1 b.1.digits (if sub then b.1.negative else !b.1.negative)
  let d := multiply X.2 Y.2
  obtain ⟨xn,xd⟩ := widths x hx
  obtain ⟨yn,yd⟩ := widths y hy
  obtain ⟨av,al,ac⟩ := product_spec X.1 ⟨false,Y.2⟩ W xn yd
  obtain ⟨bv,bl,bc⟩ := product_spec Y.1 ⟨false,X.2⟩ W yn xd
  change a.1.decode=_ at av;change a.1.digits.length≤_ at al;change a.2≤_ at ac
  change b.1.decode=_ at bv;change b.1.digits.length≤_ at bl;change b.2≤_ at bc
  have dn (z : ℚ) : (SignedWord.mk false (pack z).2).decode=(z.den:ℤ) := by simp [SignedWord.decode,pack,signed]
  change a.1.decode=(encode x.num).decode*(SignedWord.mk false (pack y).2).decode at av
  change b.1.decode=(encode y.num).decode*(SignedWord.mk false (pack x).2).decode at bv
  rw [decode_encode,dn] at av bv
  obtain ⟨cv,cl,cc⟩ := adjust_spec a.1 b.1.digits (if sub then b.1.negative else !b.1.negative)
  change c.1=_ at cv;change c.1.digits.length≤_ at cl;change c.2=_ at cc
  obtain ⟨dv,dl,dc⟩ := multiply_spec X.2 Y.2
  change value d.1=_ at dv;change d.1.length≤_ at dl;change d.2≤_ at dc
  simp only [X,Y,pack,value_bits] at dv
  have dp : 0<value d.1 := dv ▸ Nat.mul_pos y.den_pos x.den_pos
  have dw : d.1.length≤3*W := dl.trans (show X.2.length+2*Y.2.length≤3*W by change (pack x).2.length+2*(pack y).2.length≤3*W;omega)
  have gd := dc.trans (Nat.mul_le_mul yd (show X.2.length+5*(X.2.length+2*Y.2.length)≤W+5*(W+2*W) by
    change (pack x).2.length+5*((pack x).2.length+2*(pack y).2.length)≤_;omega))
  obtain ⟨r,rc⟩ := normalize_spec c.1 d.1 dp (3*W+1) (by omega) (by omega)
  change (normalize c.1 d.1).1=_ ∧ a.2+b.2+c.2+d.2+(normalize c.1 d.1).2+4≤_
  refine ⟨r.trans (congrArg pack ?_),?_⟩
  · have eqn : signed (!b.1.negative) (value b.1.digits)= -b.1.decode := negate_value b.1
    have eqp : signed b.1.negative (value b.1.digits)=b.1.decode := rfl
    have nx : (x.den:ℚ)≠0 := by exact_mod_cast x.den_ne_zero
    have ny : (y.den:ℚ)≠0 := by exact_mod_cast y.den_ne_zero
    rw [cv,decode_encode,dv]
    cases sub <;> simp only [Bool.false_eq_true,if_false,if_true,eqn,eqp,av,bv,sub_neg_eq_add]
    · calc _ = (x.num:ℚ)/x.den+(y.num:ℚ)/y.den := by push_cast; field_simp
           _ = _ := by rw [Rat.num_div_den,Rat.num_div_den]
    · calc _ = (x.num:ℚ)/x.den-(y.num:ℚ)/y.den := by push_cast; field_simp
           _ = _ := by rw [Rat.num_div_den,Rat.num_div_den]
  · rw [cc];unfold budget
    have m := max_le al bl
    nlinarith only [ac,bc,m,gd,rc,Nat.zero_le W,Nat.zero_le (W^2),Nat.zero_le (W^3)]



def wordMul (x y : Word) : Word×ℕ :=
  let a := product x.1 y.1
  let d := multiply x.2 y.2
  let r := normalize a.1 d.1
  (r.1,a.2+d.2+r.2+2)

private theorem mul_core (x y : ℚ) (W : ℕ) (hx : width x≤W) (hy : width y≤W) :
    (wordMul (pack x) (pack y)).1=pack (x*y) ∧ (wordMul (pack x) (pack y)).2+2≤budget W := by
  let a := product (pack x).1 (pack y).1
  let d := multiply (pack x).2 (pack y).2
  obtain ⟨xn,xd⟩ := widths x hx
  obtain ⟨yn,yd⟩ := widths y hy
  obtain ⟨av,al,ac⟩ := product_spec (pack x).1 (pack y).1 W xn yn
  change a.1.decode=(encode x.num).decode*(encode y.num).decode at av
  rw [decode_encode,decode_encode] at av
  change a.1.digits.length≤_ at al;change a.2≤_ at ac
  obtain ⟨dv,dl,dc⟩ := multiply_spec (pack x).2 (pack y).2
  change value d.1=_ at dv;change d.1.length≤_ at dl;change d.2≤_ at dc
  simp only [pack,value_bits] at dv
  obtain ⟨r,rc⟩ := normalize_spec a.1 d.1 (dv ▸ Nat.mul_pos y.den_pos x.den_pos) (3*W) al (by omega)
  have gd := dc.trans (Nat.mul_le_mul yd (show (pack x).2.length+5*((pack x).2.length+2*(pack y).2.length)≤W+5*(W+2*W) by omega))
  change (normalize a.1 d.1).1=_ ∧ a.2+d.2+(normalize a.1 d.1).2+2+2≤_
  refine ⟨r.trans (congrArg pack ?_),?_⟩
  · rw [av,dv]
    calc _ = ((x.num:ℚ)/x.den)*((y.num:ℚ)/y.den) := by push_cast;ring
         _ = _ := by rw [Rat.num_div_den,Rat.num_div_den]
  · unfold budget;nlinarith only [ac,gd,rc,Nat.zero_le W,Nat.zero_le (W^2),Nat.zero_le (W^3)]

/-- Canonical reciprocal, including the zero convention of rational division. -/
def inverse (x : Word) : Word :=
  if x.1.digits.isEmpty then pack 0 else (⟨x.1.negative,x.2⟩,x.1.digits)

private theorem inverse_pack (x : ℚ) : inverse (pack x)=pack x⁻¹ ∧ width x⁻¹≤width x := by
  by_cases xz : x=0
  · subst x; exact ⟨by rw [inv_zero]; rfl,by simp⟩
  have nz := Rat.num_eq_zero.not.mpr xz
  have ne : x.num.natAbs.bits.isEmpty=false := List.isEmpty_eq_false_iff.mpr (by
    intro h; have := congrArg value h
    simp only [value_bits,value,Int.natAbs_eq_zero] at this;contradiction)
  have den := Rat.den_inv_of_ne_zero xz
  have dp : 0<(x.den:ℤ) := by exact_mod_cast x.den_pos
  rcases lt_or_gt_of_ne nz with neg|pos
  · simp [inverse,pack,encode,ne,Rat.num_inv,Int.sign_eq_neg_one_of_neg neg,den,neg,x.den_pos,width,max_comm]
  · simp [inverse,pack,encode,ne,Rat.num_inv,Int.sign_eq_one_of_pos pos,den,pos.not_gt,dp.not_gt,width,max_comm]

def wordAdd := plusMinus false
def wordSub := plusMinus true
def wordDiv (x y : Word) : Word×ℕ :=
  let r := wordMul x (inverse y)
  (r.1,r.2+2)

theorem wordAdd_spec (x y : ℚ) (W : ℕ) (hx : width x≤W) (hy : width y≤W) :
    (wordAdd (pack x) (pack y)).1=pack (x+y) ∧ (wordAdd (pack x) (pack y)).2≤budget W :=
  plusMinus_spec false x y W hx hy

theorem wordSub_spec (x y : ℚ) (W : ℕ) (hx : width x≤W) (hy : width y≤W) :
    (wordSub (pack x) (pack y)).1=pack (x-y) ∧ (wordSub (pack x) (pack y)).2≤budget W :=
  plusMinus_spec true x y W hx hy

theorem wordMul_spec (x y : ℚ) (W : ℕ) (hx : width x≤W) (hy : width y≤W) :
    (wordMul (pack x) (pack y)).1=pack (x*y) ∧ (wordMul (pack x) (pack y)).2≤budget W :=
  (mul_core x y W hx hy).imp_right (fun h=>by omega)

theorem wordDiv_spec (x y : ℚ) (W : ℕ) (hx : width x≤W) (hy : width y≤W) :
    (wordDiv (pack x) (pack y)).1=pack (x/y) ∧ (wordDiv (pack x) (pack y)).2≤budget W := by
  obtain ⟨v,w⟩ := inverse_pack y
  simpa only [wordDiv,v,div_eq_mul_inv] using mul_core x y⁻¹ W hx (w.trans hy)

private def observe (op : Word→Word→Word×ℕ) (x y : ℚ) : ℚ×ℕ :=
  let r := op (pack x) (pack y)
  (unpack r.1,r.2)

def binaryAdd := observe wordAdd
def binarySub := observe wordSub
def binaryMul := observe wordMul
def binaryDiv := observe wordDiv

theorem binaryAdd_spec (x y : ℚ) (W : ℕ) (hx : width x≤W) (hy : width y≤W) :
    (binaryAdd x y).1=x+y ∧ (binaryAdd x y).2≤budget W := by
  obtain ⟨v,c⟩ := wordAdd_spec x y W hx hy
  exact ⟨by simp [binaryAdd,observe,v],c⟩

theorem binarySub_spec (x y : ℚ) (W : ℕ) (hx : width x≤W) (hy : width y≤W) :
    (binarySub x y).1=x-y ∧ (binarySub x y).2≤budget W := by
  obtain ⟨v,c⟩ := wordSub_spec x y W hx hy
  exact ⟨by simp [binarySub,observe,v],c⟩

theorem binaryMul_spec (x y : ℚ) (W : ℕ) (hx : width x≤W) (hy : width y≤W) :
    (binaryMul x y).1=x*y ∧ (binaryMul x y).2≤budget W := by
  obtain ⟨v,c⟩ := wordMul_spec x y W hx hy
  exact ⟨by simp [binaryMul,observe,v],c⟩

theorem binaryDiv_spec (x y : ℚ) (W : ℕ) (hx : width x≤W) (hy : width y≤W) :
    (binaryDiv x y).1=x/y ∧ (binaryDiv x y).2≤budget W := by
  obtain ⟨v,c⟩ := wordDiv_spec x y W hx hy
  exact ⟨by simp [binaryDiv,observe,v],c⟩

end Cogentic.BinaryRational

#print axioms Cogentic.BinaryRational.binaryAdd_spec
#print axioms Cogentic.BinaryRational.binarySub_spec
#print axioms Cogentic.BinaryRational.binaryMul_spec
#print axioms Cogentic.BinaryRational.binaryDiv_spec
