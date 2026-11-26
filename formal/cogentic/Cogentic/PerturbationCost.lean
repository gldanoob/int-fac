import Cogentic.CandidateRuntime
import Cogentic.ConstructionHeight

namespace Cogentic.BinaryPerturbation
open BinaryDivision BinaryPivot BinarySaturation Construction

private theorem select_length (w : ℕ) (a b : Bool) (x y : List Bool) :
    (selectDigits w a b x y).1.length=w := by
  induction w generalizing x y with
  | zero => rfl
  | succ k ih => simp [selectDigits,ih]

private theorem difference_length (x y : SignedWord) :
    (signedDifference x y).1.digits.length=max x.digits.length y.digits.length+1 := by
  unfold signedDifference; exact select_length ..

/-- Canonical sign/magnitude encoding also clears the sign of zero. -/
def normal (x : SignedWord) : SignedWord × ℕ :=
  let y := canonical x.digits
  (⟨x.negative && !y.1.isEmpty,y.1⟩,y.2+2)

theorem normal_spec (x : SignedWord) :
    (normal x).1=encode x.decode ∧ (normal x).1.digits.length≤x.digits.length ∧
    (normal x).2=3*x.digits.length+2 := by
  obtain ⟨sign,ds⟩ := x
  obtain ⟨v,c⟩ := canonical_spec ds
  have len := Nat.size_le.mpr (value_lt ds)
  change (normal ⟨sign,ds⟩).1=_ ∧ (normal ⟨sign,ds⟩).1.digits.length≤ds.length ∧ _=_
  refine ⟨?_,by simpa [normal,v,Nat.size_eq_bits_len] using len,by simp [normal,c]⟩
  cases sign with
  | false => simp [normal,v,encode,SignedWord.decode,signed]
  | true =>
    by_cases z : value ds=0
    · simp [normal,v,z,encode,SignedWord.decode,signed]
    · have nz : (value ds).bits.isEmpty=false := by
        apply List.isEmpty_eq_false_iff.mpr
        intro h; exact z (by simpa [value] using congrArg value h)
      have p := Nat.pos_of_ne_zero z
      simp [normal,v,nz,encode,SignedWord.decode,signed,p]

def adjust (c : SignedWord) (x : List Bool) (neg : Bool) : SignedWord × ℕ :=
  let z := signedDifference c ⟨neg,x⟩
  let out := normal z.1
  (out.1,z.2+out.2+1)

theorem adjust_spec (c : SignedWord) (x : List Bool) (neg : Bool) :
    let k := max c.digits.length x.length
    (adjust c x neg).1=encode (c.decode-signed neg (value x)) ∧
    (adjust c x neg).1.digits.length≤k+1 ∧ (adjust c x neg).2=28*k+14 := by
  let z := signedDifference c ⟨neg,x⟩
  obtain ⟨ev,ec⟩ := signedDifference_spec c ⟨neg,x⟩
  have len := difference_length c ⟨neg,x⟩
  change z.1.decode=c.decode-signed neg (value x) at ev
  change z.1.digits.length=_ at len
  change z.2=_ at ec
  obtain ⟨nv,nl,nc⟩ := normal_spec z.1
  change (normal z.1).1=_ ∧ (normal z.1).1.digits.length≤_ ∧ z.2+(normal z.1).2+1=_
  refine ⟨nv.trans (congrArg encode ev),nl.trans_eq len,?_⟩
  rw [ec,nc,len]; dsimp only; omega

/-- The update only constructs the first three coefficient cells, sharing the
already canonical suffix of the corrected polynomial. -/
def field (step m u v : List Bool) : List SignedWord → List SignedWord × ℕ
  | a::b::c::cs =>
    let su := multiply step u
    let sv := multiply step v
    let mu := multiply su.1 m
    let mv := multiply sv.1 m
    let A := adjust a mu.1 false
    let B₀ := adjust b su.1 true
    let B := adjust B₀.1 mv.1 false
    let C := adjust c sv.1 true
    (A.1::B.1::C.1::cs,su.2+sv.2+mu.2+mv.2+A.2+B₀.2+B.2+C.2+8)
  | other => (other,4)

def fieldBudget (w : ℕ) := 128*w^2+560*w+64

theorem field_spec (step m u v : List Bool) (cs : List ℤ) (w : ℕ) (pos : 0<w)
    (sw : step.length≤w) (mw : m.length≤w) (uw : u.length≤w) (vw : v.length≤w)
    (width : ∀ c∈cs,c.natAbs.size≤w) :
    (field step m u v (cs.map encode)).1 =
      (perturb (value step) (value m) (value u) (value v) cs).map encode ∧
    (field step m u v (cs.map encode)).2 ≤ fieldBudget w := by
  cases cs with
  | nil => exact ⟨rfl,by simp [field,fieldBudget]⟩
  | cons a cs =>
    cases cs with
    | nil => exact ⟨rfl,by simp [field,fieldBudget]⟩
    | cons b cs =>
      cases cs with
      | nil => exact ⟨rfl,by simp [field,fieldBudget]⟩
      | cons c cs =>
        obtain ⟨xv,xl,xc⟩ := multiply_spec step u
        obtain ⟨yv,yl,yc⟩ := multiply_spec step v
        let su := multiply step u
        let sv := multiply step v
        change value su.1=_ at xv
        change su.1.length≤_ at xl
        change su.2≤_ at xc
        change value sv.1=_ at yv
        change sv.1.length≤_ at yl
        change sv.2≤_ at yc
        let mu := multiply su.1 m
        let mv := multiply sv.1 m
        obtain ⟨xv',xl',xc'⟩ := multiply_spec su.1 m
        obtain ⟨yv',yl',yc'⟩ := multiply_spec sv.1 m
        change value mu.1=_ at xv'
        change mu.1.length≤_ at xl'
        change mu.2≤_ at xc'
        change value mv.1=_ at yv'
        change mv.1.length≤_ at yl'
        change mv.2≤_ at yc'
        let A := adjust (encode a) mu.1 false
        let B₀ := adjust (encode b) su.1 true
        let B := adjust B₀.1 mv.1 false
        let C := adjust (encode c) sv.1 true
        obtain ⟨av,_,ac⟩ := adjust_spec (encode a) mu.1 false
        obtain ⟨bv0,bl0,bc0⟩ := adjust_spec (encode b) su.1 true
        obtain ⟨bv,_,bc⟩ := adjust_spec B₀.1 mv.1 false
        obtain ⟨cv,_,cc⟩ := adjust_spec (encode c) sv.1 true
        change A.1=_ at av
        change B₀.1=_ at bv0
        change B.1=_ at bv
        change C.1=_ at cv
        change A.2=_ at ac
        change B₀.2=_ at bc0
        change B.2=_ at bc
        change C.2=_ at cc
        change B₀.1.digits.length≤_ at bl0
        change A.1::B.1::C.1::cs.map encode=_ ∧ su.2+sv.2+mu.2+mv.2+A.2+B₀.2+B.2+C.2+8≤_
        constructor
        · rw [av,bv,cv,bv0,xv',yv',xv,yv]
          simp only [perturb,List.map_cons,decode_encode,signed,Bool.false_eq_true,if_false,if_true,Nat.cast_mul]
          have ea : a-(value m:ℤ)*(value u*value step)=a-(value step:ℤ)*value m*value u := by ring
          have eb : b- -(value u:ℤ)*value step-(value m:ℤ)*(value v*value step) =
              b+(value step:ℤ)*(value u-value m*value v) := by ring
          have ec : c- -((value v:ℤ)*value step)=c+(value step:ℤ)*value v := by ring
          simp only [ea,neg_mul] at eb ⊢
          rw [eb,ec]
        · have wa : (encode a).digits.length≤w := by simpa [encode,Nat.size_eq_bits_len] using width a (by simp)
          have wb : (encode b).digits.length≤w := by simpa [encode,Nat.size_eq_bits_len] using width b (by simp)
          have wc : (encode c).digits.length≤w := by simpa [encode,Nat.size_eq_bits_len] using width c (by simp)
          have su3 : su.1.length≤3*w := by omega
          have sv3 : sv.1.length≤3*w := by omega
          have mu5 : mu.1.length≤5*w := by omega
          have mv5 : mv.1.length≤5*w := by omega
          have B₀4 : B₀.1.digits.length≤4*w := by omega
          have c1 := xc.trans (Nat.mul_le_mul uw (show _≤w+5*(w+2*w) by omega))
          have c2 := yc.trans (Nat.mul_le_mul vw (show _≤w+5*(w+2*w) by omega))
          have c3 := xc'.trans (Nat.mul_le_mul mw (show _≤3*w+5*(3*w+2*w) by omega))
          have c4 := yc'.trans (Nat.mul_le_mul mw (show _≤3*w+5*(3*w+2*w) by omega))
          have la : max (encode a).digits.length mu.1.length≤5*w := by omega
          have lb₁ : max (encode b).digits.length su.1.length≤3*w := by omega
          have lb₂ : max B₀.1.digits.length mv.1.length≤5*w := by omega
          have lc : max (encode c).digits.length sv.1.length≤3*w := by omega
          rw [ac,bc0,bc,cc]; unfold fieldBudget
          nlinarith only [la,lb₁,lb₂,lc,c1,c2,c3,c4]

/-- Multiply the primorial by the target once for both fields. -/
def run (P ell m u₀ u₁ v₀ v₁ : List Bool) (left right : List SignedWord) :
    (List SignedWord × List SignedWord) × ℕ :=
  let p := multiply P ell
  let step := canonical p.1
  let l := field step.1 m u₀ u₁ left
  let r := field step.1 m v₀ v₁ right
  ((l.1,r.1),p.2+step.2+l.2+r.2+1)

private theorem perturb_zero (s m : ℕ) (cs : List ℤ) : perturb s m 0 0 cs=cs := by
  cases cs with
  | nil => rfl
  | cons a cs => cases cs with
    | nil => rfl
    | cons b cs => cases cs <;> simp [perturb]

/-- The corrected polynomial shared by every pair of coordinates for one
field and target. Its coefficients can be computed once per target. -/
def correctedBase (n ell : ℕ) (side : Bool) : List ℤ :=
  let b := n.log2+1
  let d := Fixed.d b
  let m := Fixed.rootBase n
  let P := primorial d
  let c := leadingCoefficient n
  corrected n m (P*ell) c (preliminary d (Fixed.A b) m P ell c side)

theorem fixed_pair {n ell u₀ u₁ v₀ v₁ : ℕ} (hn : 2≤n) (big : 130000≤Fixed.d (n.log2+1))
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (box : let b := n.log2+1
      u₀≤2*b^2*Fixed.U b*Fixed.A b ∧ u₁≤2*b^2*Fixed.U b ∧
      v₀≤2*b^2*Fixed.U b*Fixed.A b ∧ v₁≤2*b^2*Fixed.U b) :
    let b := n.log2+1
    let pair := construct n ell u₀ u₁ v₀ v₁
    let r := run (primorial (Fixed.d b)).bits ell.bits (Fixed.rootBase n).bits u₀.bits u₁.bits v₀.bits v₁.bits
      ((correctedBase n ell false).map encode) ((correctedBase n ell true).map encode)
    r.1=(pair.first.map encode,pair.second.map encode) ∧ r.2≤2^45*(b+1)^2 ∧ r.2≤2^(47*TwoThirdsCost.scale b) := by
  intro b pair r
  let w := 200000*(b+1)
  let m := Fixed.rootBase n
  let d := Fixed.d b
  let P := primorial d
  have bp : 0<b := Nat.succ_pos _
  have dp := Fixed.degree_pos bp
  have db := Fixed.degree_le_bits b
  have hb : Fixed.h b≤Fixed.v b := Nat.le_mul_of_pos_left _ dp
  have vb : Fixed.v b≤b := by
    refine (Nat.le_mul_of_pos_left _ dp).trans ?_
    simpa only [show Fixed.d b*Fixed.v b=(Fixed.d b)^3*Fixed.z b by unfold Fixed.v Fixed.h; ring] using
      (Fixed.degree_floor b).1
  have cap (x e : ℕ) (h : x≤2^e) : x.size≤e+1 := by simpa [Nat.size_pow] using Nat.size_le_size h
  have Ppow : P≤2^(2*d) := by simpa only [show 4=2^2 by decide,←pow_mul] using primorial_le_four_pow d
  have ep : ell≤2^(1000*Fixed.h b) := (mem_dyadicTargets.mp target).2.2
  have step := Nat.mul_le_mul Ppow ep
  rw [←pow_add] at step
  have Pc := cap P _ Ppow
  have ec := cap ell _ ep
  have sc := cap (P*ell) _ step
  have mc : m.size≤b+1 := Nat.size_le.mpr ((Fixed.rootBase_spec hn).2.2.trans_lt
    (Nat.pow_lt_pow_right (by decide : 1<2) (Nat.lt_succ_self b)))
  have pB : b≤2^b := Nat.lt_two_pow_self.le
  have boxCap : 2*b^2*Fixed.U b*Fixed.A b ≤ 2^(1+2*b+100000*Fixed.v b+10000*Fixed.h b) := by
    have hp := Nat.pow_le_pow_left pB 2
    change 2*b^2*2^(100000*Fixed.v b)*2^(10000*Fixed.h b)≤_
    have e : (2:ℕ)^(2*b)=(2^b)^2 := by rw [Nat.mul_comm 2 b,pow_mul]
    rw [pow_add,pow_add,pow_add,pow_one,e]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hp))
  have bounds {a z : ℕ} (x : a≤2*b^2*Fixed.U b*Fixed.A b) (y : z≤2*b^2*Fixed.U b) :
      a.bits.length≤w ∧ z.bits.length≤w := by
    have z' := y.trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos (10000*Fixed.h b)))
    have ac := cap _ _ (x.trans boxCap)
    have zc := cap _ _ (z'.trans boxCap)
    simp only [Nat.size_eq_bits_len]; unfold w; omega
  have ⟨ul,ur⟩ := bounds box.1 box.2.1
  have ⟨vl,vr⟩ := bounds box.2.2.1 box.2.2.2
  have zeroBox : let b := n.log2+1
      0≤2*b^2*Fixed.U b*Fixed.A b ∧ 0≤2*b^2*Fixed.U b ∧
      0≤2*b^2*Fixed.U b*Fixed.A b ∧ 0≤2*b^2*Fixed.U b := by simp
  have ⟨hl,hr⟩ := box_height hn big target zeroBox
  simp only [construct,perturb_zero] at hl hr
  have left : ∀ c∈correctedBase n ell false,c.natAbs.size≤w := fun c hc =>
    (cap _ b (hl c hc)).trans (by unfold w; omega)
  have right : ∀ c∈correctedBase n ell true,c.natAbs.size≤w := fun c hc =>
    (cap _ b (hr c hc)).trans (by unfold w; omega)
  have pwidth : P.bits.length≤w := by rw [Nat.size_eq_bits_len]; change Fixed.d b≤b at db; dsimp [w,d] at *; omega
  have ewidth : ell.bits.length≤w := by rw [Nat.size_eq_bits_len]; unfold w; omega
  let mul := multiply P.bits ell.bits
  let stepWord := canonical mul.1
  obtain ⟨pv,pl,pc⟩ := multiply_spec P.bits ell.bits
  change value mul.1=_ at pv
  change mul.1.length≤_ at pl
  change mul.2≤_ at pc
  have ⟨sv,sw⟩ := canonical_spec mul.1
  change stepWord.1=_ at sv
  change stepWord.2=_ at sw
  rw [pv,value_bits,value_bits,Nat.mul_comm ell P] at sv
  have sl : stepWord.1.length≤w := by rw [sv,Nat.size_eq_bits_len]; dsimp [d] at sc; dsimp [P,d,w] at *; omega
  have ml : m.bits.length≤w := by rw [Nat.size_eq_bits_len]; unfold w; omega
  have wp : 0<w := by unfold w; omega
  obtain ⟨le,lc⟩ := field_spec stepWord.1 m.bits u₀.bits u₁.bits _ w wp sl ml ul ur left
  obtain ⟨re,rc⟩ := field_spec stepWord.1 m.bits v₀.bits v₁.bits _ w wp sl ml vl vr right
  have stepValue : value stepWord.1=P*ell := by rw [sv,value_bits]
  simp only [stepValue,value_bits] at le re
  have e : r.1=(pair.first.map encode,pair.second.map encode) := by
    change ((field stepWord.1 m.bits u₀.bits u₁.bits _).1,(field stepWord.1 m.bits v₀.bits v₁.bits _).1)=_
    rw [le,re]; rfl
  have mult := pc.trans (Nat.mul_le_mul ewidth (show _≤w+5*(w+2*w) by omega))
  have poly : r.2≤2^45*(b+1)^2 := by
    change mul.2+stepWord.2+(field stepWord.1 m.bits u₀.bits u₁.bits _).2+
      (field stepWord.1 m.bits v₀.bits v₁.bits _).2+1≤_
    rw [sw]
    have ul' := lc
    have ur' := rc
    unfold fieldBudget at ul' ur'
    dsimp only [w] at ul' ur' mult pwidth ewidth
    dsimp only [w] at *
    nlinarith only [ul',ur',mult,pl,pwidth,ewidth,bp]
  refine ⟨e,poly,poly.trans ?_⟩
  let t := TwoThirdsCost.scale b
  have ht : Fixed.h b≤t := hb.trans (Fixed.scale_bounds bp).1
  have zs : b.log2+1≤t := (Nat.le_mul_of_pos_left _ dp).trans ht
  have tp : 0<t := by omega
  have bx : b+1≤2^t := Nat.succ_le_of_lt (Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by decide) zs))
  calc 2^45*(b+1)^2 ≤ 2^45*(2^t)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left bx 2)
       _ ≤ 2^(47*t) := by rw [←pow_mul,←pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)

end Cogentic.BinaryPerturbation

#print axioms Cogentic.BinaryPerturbation.field_spec
#print axioms Cogentic.BinaryPerturbation.fixed_pair
