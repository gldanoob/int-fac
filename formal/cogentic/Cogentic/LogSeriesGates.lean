import Cogentic.BinaryPivotCost
import Cogentic.ArchNumerics

namespace Cogentic.BinaryLogSeries
open BinaryDivision BinaryPivot Finset

structure Fraction where
  num : List Bool
  den : List Bool
  gates : ℕ

/-- Backwards Horner summation of y/j + y²/(j+1) + …, with y = a/q.
Positive unreduced denominators avoid rational normalization inside the loop. -/
def series (a q : List Bool) : List Bool → ℕ → Fraction
  | _, 0 => ⟨[],[true],0⟩
  | j, t+1 =>
    let next := addDigits j.length j [] true
    let tail := series a q next.1 t
    let scaled := multiply tail.num j
    let sum := addDigits (max tail.den.length scaled.1.length) tail.den scaled.1 false
    let num := multiply sum.1 a
    let base := multiply tail.den j
    let den := multiply base.1 q
    ⟨num.1,den.1,next.2+tail.gates+scaled.2+sum.2+num.2+base.2+den.2⟩

private def shifted (y : ℚ) (j t : ℕ) :=
  ∑ i ∈ range t, y^(i+1)/((j:ℚ)+i)

private theorem shifted_succ (y : ℚ) (j t : ℕ) :
    shifted y j (t+1)=y*(1/j+shifted y (j+1) t) := by
  unfold shifted
  rw [sum_range_succ',mul_add,mul_sum]
  simp only [Nat.cast_zero,add_zero,zero_add,pow_one,Nat.cast_add,Nat.cast_one]
  rw [add_comm]
  congr 1
  · ring
  · apply sum_congr rfl
    intro i _
    rw [pow_succ]
    ring

theorem series_value (a q j : List Bool) (qp : 0<value q) (jp : 0<value j) (t : ℕ) :
    let r := series a q j t
    0<value r.den ∧ (value r.num:ℚ)/value r.den=shifted ((value a:ℚ)/value q) (value j) t := by
  induction t generalizing j with
  | zero => simp [series,value,shifted]
  | succ t ih =>
    let next := addDigits j.length j [] true
    obtain ⟨_,_,nv⟩ := addDigits_spec j.length j [] true le_rfl (by simp)
    have step : value next.1=value j+1 := by simpa [next,value] using nv
    let f := series a q next.1 t
    obtain ⟨fp,fv⟩ := ih next.1 (by rw [step]; omega)
    change 0<value f.den at fp
    change (value f.num:ℚ)/value f.den=_ at fv
    let prod := multiply f.num j
    let sum := addDigits (max f.den.length prod.1.length) f.den prod.1 false
    obtain ⟨_,_,sv⟩ := addDigits_spec _ f.den prod.1 false (le_max_left ..) (le_max_right ..)
    change value sum.1=_ at sv
    have prodv := (multiply_spec f.num j).1
    change value prod.1=_ at prodv
    have nv' := (multiply_spec sum.1 a).1
    have bv := (multiply_spec f.den j).1
    have dv := (multiply_spec (multiply f.den j).1 q).1
    change 0<value (multiply (multiply f.den j).1 q).1 ∧
      (value (multiply sum.1 a).1:ℚ)/value (multiply (multiply f.den j).1 q).1=_
    rw [nv',dv,bv,sv,prodv]
    simp only [Bool.toNat_false,Nat.add_zero]
    rw [shifted_succ,←step,←fv]
    constructor
    · positivity
    · push_cast
      field_simp

/-- The width includes all counter increments. The budget also charges every
addition and multiplication, including the work on unreduced intermediates. -/
theorem series_cost (a q j : List Bool) (t T W : ℕ) (steps : t≤T)
    (aw : a.length≤W) (qw : q.length≤W) (jw : j.length+t≤W) :
    let f := series a q j t
    let D := 1+T*(4*W+1)
    f.num.length≤1+t*(4*W+1) ∧ f.den.length≤1+t*(4*W+1) ∧ f.gates≤t*(100*(D+W+1)^2) := by
  induction t generalizing j with
  | zero => simp [series]
  | succ t ih =>
    let next := addDigits j.length j [] true
    obtain ⟨nw,nc,_⟩ := addDigits_spec j.length j [] true le_rfl (by simp)
    change next.1.length=j.length+1 at nw
    change next.2=5*j.length at nc
    let f := series a q next.1 t
    obtain ⟨fn,fd,fc⟩ := ih next.1 (by omega) (by rw [nw]; omega)
    change f.num.length≤_ at fn
    change f.den.length≤_ at fd
    change f.gates≤_ at fc
    let prod := multiply f.num j
    obtain ⟨_,pl,pc⟩ := multiply_spec f.num j
    change prod.1.length≤_ at pl; change prod.2≤_ at pc
    let m := max f.den.length prod.1.length
    let sum := addDigits m f.den prod.1 false
    obtain ⟨sl,sc,_⟩ := addDigits_spec m f.den prod.1 false (le_max_left ..) (le_max_right ..)
    change sum.1.length=m+1 at sl; change sum.2=5*m at sc
    let num := multiply sum.1 a
    let base := multiply f.den j
    let den := multiply base.1 q
    obtain ⟨_,nl,ng⟩ := multiply_spec sum.1 a
    obtain ⟨_,bl,bg⟩ := multiply_spec f.den j
    obtain ⟨_,dl,dg⟩ := multiply_spec base.1 q
    change base.1.length≤_ at bl
    change num.1.length≤_ at nl; change den.1.length≤_ at dl
    change num.2≤_ at ng; change base.2≤_ at bg; change den.2≤_ at dg
    let D := 1+T*(4*W+1)
    let E := 1+t*(4*W+1)
    have ml : m≤E+2*W := max_le (by dsimp [E]; omega) (by dsimp [E]; omega)
    have ed : E≤D := Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : t≤T)) 1
    have jlen : j.length≤W := by omega
    have multBound (x y : ℕ) (xw : x≤D+2*W+1) (yw : y≤W) :
        y*(x+5*(x+2*y)) ≤ W*((D+2*W+1)+5*((D+2*W+1)+2*W)) := by gcongr
    have pc' := pc.trans (multBound _ _ (by change f.num.length≤E at fn; omega) jlen)
    have ng' := ng.trans (multBound _ _ (by omega) aw)
    have bg' := bg.trans (multBound _ _ (by change f.den.length≤E at fd; omega) jlen)
    have dg' := dg.trans (multBound _ _ (by change f.den.length≤E at fd; omega) qw)
    have addG : next.2+sum.2≤5*W+5*(D+2*W) := by rw [nc,sc]; omega
    change num.1.length≤_ ∧ den.1.length≤_ ∧ next.2+f.gates+prod.2+sum.2+num.2+base.2+den.2≤_
    simp only [Nat.succ_mul (n := t)]
    refine ⟨by dsimp [E] at ml; omega,by omega,?_⟩
    have gateStep : next.2+sum.2+prod.2+num.2+base.2+den.2≤100*(D+W+1)^2 := by
      apply (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add addG pc') ng') bg') dg').trans
      ring_nf; omega
    change f.gates≤t*(100*(D+W+1)^2) at fc
    change _ ≤ t*(100*(D+W+1)^2)+100*(D+W+1)^2
    omega

/-- The exact partial sum consumed by reducedLog at an integral fraction
with 1−1/x = a/q, at polynomial Boolean cost in the widths and term count. -/
theorem reducedLog_gates (x : ℚ) (a q : List Bool) (qp : 0<value q)
    (arg : 1-x⁻¹=(value a:ℚ)/value q) (t : ℕ) :
    let W := max (max a.length q.length) (1+t)
    let f := series a q [true] t
    (value f.num:ℚ)/value f.den=ArchNumerics.reducedLog x t ∧
      f.gates≤t*(100*((1+t*(4*W+1))+W+1)^2) := by
  intro W f
  have v := (series_value a q [true] qp (by decide) t).2
  refine ⟨v.trans ?_,(series_cost a q [true] t t W le_rfl
    ((le_max_left ..).trans (le_max_left ..)) ((le_max_right ..).trans (le_max_left ..)) (le_max_right ..)).2.2⟩
  simp [shifted,ArchNumerics.reducedLog,arg,value,add_comm]

end Cogentic.BinaryLogSeries

namespace Cogentic.BinaryLogSeries
open BinaryDivision BinaryPivot

private def offset (k : ℕ) := List.replicate k false ++ [true]

private theorem offset_value (k : ℕ) : value (offset k)=2^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [offset,List.replicate_succ,value] at ih ⊢; omega

private def readFraction (f : Fraction) : ℚ := (value f.num:ℚ)/value f.den

def logTwoSeries (t : ℕ) := series [true] [false,true] [true] t

def mantSeries (n : List Bool) (t : ℕ) :=
  let a := subtract n.length n (offset (n.length-1)) false
  series a.digits n [true] t

theorem series_widths (n : List Bool) (t W : ℕ) (nw : n.length≤W) (tw : 1+t≤W) (two : 2≤W) :
    let D := 1+t*(4*W+1)
    (logTwoSeries t).num.length≤D ∧ (logTwoSeries t).den.length≤D ∧
      (mantSeries n t).num.length≤D ∧ (mantSeries n t).den.length≤D := by
  let a := subtract n.length n (offset (n.length-1)) false
  have len (k : ℕ) (u v : List Bool) (b : Bool) : (subtract k u v b).digits.length=k := by
    induction k generalizing u v b with
    | zero => rfl
    | succ k ih => simp [subtract,ih]
  have aw : a.digits.length=n.length := len ..
  have x := series_cost [true] [false,true] [true] t t W le_rfl (by simp; omega) (by simpa using two) (by simpa using tw)
  have y := series_cost a.digits n [true] t t W le_rfl (aw.le.trans nw) nw (by simpa using tw)
  exact ⟨x.1,x.2.1,y.1,y.2.1⟩

theorem series_den_pos {n : ℕ} (np : 0<n) (t : ℕ) :
    0<value (logTwoSeries t).den ∧ 0<value (mantSeries n.bits t).den :=
  ⟨(series_value _ _ _ (by decide) (by decide) t).1,(series_value _ _ _ (by simpa) (by decide) t).1⟩

/-- The binary words and total preparation cost for both range-reduced series. -/
def prepare (n : List Bool) (t : ℕ) : Fraction × Fraction × ℕ :=
  let p := offset (n.length-1)
  let a := subtract n.length n p false
  let base := logTwoSeries t
  let mant := series a.digits n [true] t
  (base,mant,p.length+a.gates+base.gates+mant.gates)

/-- Read the two series in the range reduction for log n. -/
def natParts (n : List Bool) (terms : ℕ) : ℚ × ℕ :=
  let parts := prepare n terms
  ((n.length-1:ℕ)*readFraction parts.1+readFraction parts.2.1,parts.2.2)

theorem natParts_spec {n : ℕ} (np : 0<n) (t : ℕ) :
    (natParts n.bits t).1=ArchNumerics.natLog n t ∧
    (natParts n.bits t).2≤8*n.size+2*(t*(100*((1+t*(4*(n.size+t+2)+1))+(n.size+t+2)+1)^2)) := by
  have len : n.bits.length=n.log2+1 := by
    rw [Nat.size_eq_bits_len]
    exact Nat.le_antisymm (Nat.size_le.mpr Nat.lt_log2_self) (Nat.lt_size.mpr (Nat.log2_self_le np.ne'))
  let p := offset (n.bits.length-1)
  have pl : p.length=n.bits.length := by simp [p,offset,len]
  have pv : value p=2^n.log2 := by simp [p,offset_value,len]
  let a := subtract n.bits.length n.bits p false
  obtain ⟨aw,ac,av⟩ := subtract_spec n.bits.length n.bits p false le_rfl pl.le
  change a.digits.length=_ at aw
  change a.gates=_ at ac
  change value a.digits+value p+false.toNat=value n.bits+2^n.bits.length*a.borrow.toNat at av
  rw [pv,value_bits] at av
  have small := value_lt a.digits
  rw [aw] at small
  have lower := Nat.log2_self_le np.ne'
  have diff : value a.digits=n-2^n.log2 := by cases h : a.borrow <;> simp [h] at av <;> omega
  have arg : 1-(ArchNumerics.mantissa n)⁻¹=(value a.digits:ℚ)/value n.bits := by
    rw [diff,value_bits,Nat.cast_sub lower]
    push_cast
    unfold ArchNumerics.mantissa
    rw [inv_div,sub_div,div_self (by exact_mod_cast np.ne')]
  obtain ⟨base,bwork⟩ := reducedLog_gates 2 [true] [false,true] (by decide) (by norm_num [value]) t
  obtain ⟨mant,mwork⟩ := reducedLog_gates (ArchNumerics.mantissa n) a.digits n.bits (by simpa) arg t
  constructor
  · change (n.bits.length-1:ℕ)*readFraction _+readFraction _=_
    change (n.bits.length-1:ℕ)*readFraction (logTwoSeries t)+readFraction (mantSeries n.bits t)=_
    unfold readFraction logTwoSeries mantSeries
    rw [base,mant,len]
    simp [ArchNumerics.natLog]
  · let W := n.size+t+2
    have cap (h : ℕ) (hw : h≤W) : t*(100*(1+t*(4*h+1)+h+1)^2)≤t*(100*(1+t*(4*W+1)+W+1)^2) := by gcongr
    have bw := bwork.trans (cap _ (by simp [W]; omega))
    have mw := mwork.trans (cap _ (by simp [aw,W,Nat.size_eq_bits_len]; omega))
    change p.length+a.gates+(series [true] [false,true] [true] t).gates+(series a.digits n.bits [true] t).gates≤_
    have front : p.length+a.gates=8*n.size := by rw [pl,ac,Nat.size_eq_bits_len]; omega
    rw [front]
    change _≤8*n.size+2*(t*(100*(1+t*(4*W+1)+W+1)^2))
    omega

/-- Exact `approxLog` answer, together with the counted part of its work.
Combining the four fractions and rounding are outside this counter. -/
def logParts (u v bits : ℕ) : ℚ × ℕ :=
  let t := bits+u.log2+v.log2+4
  let x := natParts u.bits t
  let y := natParts v.bits t
  (ArchNumerics.roundDyadic (x.1-y.1) bits,x.2+y.2)

theorem approxLog_series_gates {u v : ℕ} (up : 0<u) (vp : 0<v) (bits : ℕ) :
    let H := bits+u.size+v.size+8
    (logParts u v bits).1=ArchNumerics.approxLog u v bits ∧
      (logParts u v bits).2≤100000*H^5 := by
  intro H
  let t := bits+u.log2+v.log2+4
  obtain ⟨x,cx⟩ := natParts_spec up t
  obtain ⟨y,cy⟩ := natParts_spec vp t
  refine ⟨by change ArchNumerics.roundDyadic (_-_) bits=_; rw [x,y]; rfl,?_⟩
  have sizeU : u.log2<u.size := Nat.lt_size.mpr (Nat.log2_self_le up.ne')
  have sizeV : v.log2<v.size := Nat.lt_size.mpr (Nat.log2_self_le vp.ne')
  have tt : t≤H := by dsimp [t,H]; omega
  have hh : 1≤H := by dsimp [H]; omega
  have us : u.size≤H := by dsimp [H]; omega
  have vs : v.size≤H := by dsimp [H]; omega
  have bound (s : ℕ) (le : s≤H) :
      8*s+2*(t*(100*(1+t*(4*(s+t+2)+1)+(s+t+2)+1)^2))≤50000*H^5 := by
    have sw : s+t+2≤2*H := by dsimp [t,H] at *; omega
    have scale : 1+t*(4*(s+t+2)+1)+(s+t+2)+1≤13*H^2 := calc
      _ ≤ 1+H*(4*(2*H)+1)+2*H+1 := by gcongr
      _ ≤ _ := by nlinarith only [Nat.le_self_pow (by decide : 2≠0) H,hh]
    calc
      _ ≤ 8*H+2*(H*(100*(13*H^2)^2)) := by gcongr
      _ ≤ _ := by ring_nf; nlinarith only [Nat.le_self_pow (by decide : 5≠0) H]
  change (natParts u.bits t).2+(natParts v.bits t).2≤_
  linarith only [cx.trans (bound _ us),cy.trans (bound _ vs)]

end Cogentic.BinaryLogSeries
