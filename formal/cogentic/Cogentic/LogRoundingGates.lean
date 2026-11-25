import Cogentic.LogSeriesGates
import Cogentic.ReconstructionCost
import Cogentic.IndexCapCost

namespace Cogentic.BinaryLogSeries
open BinaryDivision BinaryPivot BinarySaturation BinaryReconstruction

/-- Put k times the first series and the mantissa series over a common
denominator. The input counters are paid by the series evaluator. -/
def weighted (k : List Bool) (x y : Fraction) : Fraction :=
  let kx := multiply x.num k
  let left := multiply kx.1 y.den
  let right := multiply y.num x.den
  let num := addDigits (max left.1.length right.1.length) left.1 right.1 false
  let den := multiply x.den y.den
  ⟨num.1,den.1,kx.2+left.2+right.2+num.2+den.2⟩

theorem weighted_spec (k : List Bool) (x y : Fraction) (W : ℕ)
    (xp : 0<value x.den) (yp : 0<value y.den)
    (kw : k.length≤W) (xn : x.num.length≤W) (xd : x.den.length≤W)
    (yn : y.num.length≤W) (yd : y.den.length≤W) :
    let f := weighted k x y
    0<value f.den ∧ (value f.num:ℚ)/value f.den=
      value k*((value x.num:ℚ)/value x.den)+(value y.num:ℚ)/value y.den ∧
      f.num.length≤5*W+1 ∧ f.den.length≤5*W+1 ∧ f.gates≤200*(W+1)^2 := by
  let kx := multiply x.num k
  let l := multiply kx.1 y.den
  let r := multiply y.num x.den
  let a := addDigits (max l.1.length r.1.length) l.1 r.1 false
  let d := multiply x.den y.den
  obtain ⟨kv,kl,kc⟩ := multiply_spec x.num k
  obtain ⟨lv,ll,lc⟩ := multiply_spec kx.1 y.den
  obtain ⟨rv,rl,rc⟩ := multiply_spec y.num x.den
  obtain ⟨al,ac,av⟩ := addDigits_spec _ l.1 r.1 false (le_max_left ..) (le_max_right ..)
  obtain ⟨dv,dl,dc⟩ := multiply_spec x.den y.den
  change value kx.1=_ at kv; change kx.1.length≤_ at kl; change kx.2≤_ at kc
  change value l.1=_ at lv; change l.1.length≤_ at ll; change l.2≤_ at lc
  change value r.1=_ at rv; change r.1.length≤_ at rl; change r.2≤_ at rc
  change value a.1=_ at av; change a.1.length=_ at al; change a.2=_ at ac
  change value d.1=_ at dv; change d.1.length≤_ at dl; change d.2≤_ at dc
  have ml : max l.1.length r.1.length≤5*W := max_le (by omega) (by omega)
  change 0<value d.1 ∧ (value a.1:ℚ)/value d.1=_ ∧ a.1.length≤_ ∧ d.1.length≤_ ∧
    kx.2+l.2+r.2+a.2+d.2≤_
  refine ⟨dv ▸ Nat.mul_pos yp xp,?_,by omega,by omega,?_⟩
  · rw [av,lv,rv,kv,dv]
    simp only [Bool.toNat_false,Nat.add_zero]
    push_cast; field_simp
  · have mulBound (u v : ℕ) (hu : u≤3*W) (hv : v≤W) :
        v*(u+5*(u+2*v))≤28*W^2 := by
      calc _ ≤ W*(3*W+5*(3*W+2*W)) := by gcongr
           _ = _ := by ring
    have kcost := kc.trans (mulBound _ _ (by omega) kw)
    have lcost := lc.trans (mulBound _ _ (by omega) yd)
    have rcost := rc.trans (mulBound _ _ (by omega) xd)
    have dcost := dc.trans (mulBound _ _ (by omega) yd)
    nlinarith only [kcost,lcost,rcost,dcost,ac,ml]

private theorem shift_value (k : ℕ) (x : List Bool) :
    value (List.replicate k false++x)=2^k*value x := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ,value,ih,pow_succ]; ring

/-- Binary numerator of the difference of two positive-denominator fractions
rounded to a multiple of 2^(-bits), with ties upward on both signs. -/
def roundSub (l r : Fraction) (bits : ℕ) : ℤ × ℕ :=
  let p := multiply l.num r.den
  let q := multiply r.num l.den
  let d := multiply l.den r.den
  let shift := List.replicate (bits+1) false
  let top := shift++p.1
  let bottom := shift++q.1
  let plus := addDigits (max top.length d.1.length) top d.1 false
  let s := signedDifference ⟨false,plus.1⟩ ⟨false,bottom⟩
  let mag := canonical s.1.digits
  let den := canonical (false::d.1)
  let out := divmod (signed s.1.negative (value mag.1)) (value den.1)
  (out.quotient,p.2+q.2+d.2+top.length+bottom.length+plus.2+s.2+mag.2+den.2+out.gates+1)

private theorem select_width (w : ℕ) (b c : Bool) (xs ys : List Bool) :
    (selectDigits w b c xs ys).1.length=w := by
  induction w generalizing xs ys with
  | zero => rfl
  | succ w ih => simp [selectDigits,ih]

set_option maxHeartbeats 800000 in
theorem roundSub_full (l r : Fraction) (bits W : ℕ) (lp : 0<value l.den) (rp : 0<value r.den)
    (hw : bits≤W) (ln : l.num.length≤W) (ld : l.den.length≤W) (rn : r.num.length≤W) (rd : r.den.length≤W) :
    let out := roundSub l r bits
    (out.1:ℚ)/2^bits=ArchNumerics.roundDyadic
      ((value l.num:ℚ)/value l.den-(value r.num:ℚ)/value r.den) bits ∧ out.2≤10000*(W+1)^2 ∧ out.1.natAbs.size≤4*W+3 := by
  let p := multiply l.num r.den
  let q := multiply r.num l.den
  let d := multiply l.den r.den
  let top := List.replicate (bits+1) false++p.1
  let bottom := List.replicate (bits+1) false++q.1
  let plus := addDigits (max top.length d.1.length) top d.1 false
  let s := signedDifference ⟨false,plus.1⟩ ⟨false,bottom⟩
  let mag := canonical s.1.digits
  let den := canonical (false::d.1)
  let z := signed s.1.negative (value mag.1)
  let D := value den.1
  obtain ⟨pv,pl,pc⟩ := multiply_spec l.num r.den
  obtain ⟨qv,ql,qc⟩ := multiply_spec r.num l.den
  obtain ⟨dv,dl,dc⟩ := multiply_spec l.den r.den
  change value p.1=_ at pv; change p.1.length≤_ at pl; change p.2≤_ at pc
  change value q.1=_ at qv; change q.1.length≤_ at ql; change q.2≤_ at qc
  change value d.1=_ at dv; change d.1.length≤_ at dl; change d.2≤_ at dc
  have tv : value top=2^(bits+1)*value p.1 := shift_value ..
  have bv : value bottom=2^(bits+1)*value q.1 := shift_value ..
  have tl : top.length=bits+1+p.1.length := by simp [top]
  have bl : bottom.length=bits+1+q.1.length := by simp [bottom]
  obtain ⟨al,ac,av⟩ := addDigits_spec _ top d.1 false (le_max_left ..) (le_max_right ..)
  change plus.1.length=_ at al; change plus.2=_ at ac; change value plus.1=_ at av
  obtain ⟨sv,sc⟩ := signedDifference_spec ⟨false,plus.1⟩ ⟨false,bottom⟩
  change s.1.decode=(value plus.1:ℤ)-value bottom at sv
  change s.2=25*max plus.1.length bottom.length+8 at sc
  have sl : s.1.digits.length=max plus.1.length bottom.length+1 := select_width ..
  obtain ⟨mv,mc⟩ := canonical_spec s.1.digits
  obtain ⟨dv',dc'⟩ := canonical_spec (false::d.1)
  change mag.1=_ at mv; change mag.2=_ at mc
  change den.1=_ at dv'; change den.2=_ at dc'
  have de : D=2*(value r.den*value l.den) := by simp [D,dv',value,dv]
  have ze : z=(2^(bits+1)*(value r.den*value l.num)+(value r.den*value l.den):ℕ)-
      ((2^(bits+1)*(value l.den*value r.num):ℕ):ℤ) := by
    have same : z=s.1.decode := by simp [z,mv,SignedWord.decode]
    rw [same,sv,av,tv,bv,pv,qv,dv]
    simp
  have dp : 0<D := de ▸ (by positivity)
  have aw : max top.length d.1.length≤4*W+1 := max_le (by omega) (by omega)
  have sw : max plus.1.length bottom.length≤4*W+2 := max_le (by omega) (by omega)
  have zw : z.natAbs.size≤4*W+3 := by
    have e : z.natAbs=value s.1.digits := by
      simp only [z,mv,value_bits,signed]
      cases s.1.negative <;> simp
    rw [e]; exact (Nat.size_le.mpr (value_lt _)).trans (by omega)
  have dw : D.size≤4*W+3 := by
    have e : D=value (false::d.1) := by simp [D,dv']
    rw [e]; exact (Nat.size_le.mpr (value_lt _)).trans (by simp; omega)
  obtain ⟨floor,_,divCost⟩ := divmod_spec z D (4*W+3) dp zw dw
  refine ⟨?_,?_,?_⟩
  · have floorEq : (divmod z D).quotient=⌊(((value l.num:ℚ)/value l.den-
          (value r.num:ℚ)/value r.den)*2^bits+1/2)⌋ := by
      rw [floor,←Rat.floor_intCast_div_natCast]
      apply congrArg Int.floor
      rw [ze,de]
      push_cast
      rw [pow_succ]
      field_simp; ring
    change ((divmod z D).quotient:ℚ)/2^bits=_
    rw [floorEq]
    rfl
  · change p.2+q.2+d.2+top.length+bottom.length+plus.2+s.2+mag.2+den.2+(divmod z D).gates+1≤_
    have mb (a b : ℕ) (aw : a≤W) (bw : b≤W) : b*(a+5*(a+2*b))≤16*W^2 := by
      calc _ ≤ W*(W+5*(W+2*W)) := by gcongr
           _ = _ := by ring
    have P := pc.trans (mb _ _ ln rd)
    have Q := qc.trans (mb _ _ rn ld)
    have E := dc.trans (mb _ _ ld rd)
    have plusBound : plus.2≤5*(4*W+1) := ac.trans_le (Nat.mul_le_mul_left _ aw)
    have subBound : s.2≤25*(4*W+2)+8 := sc.trans_le (by omega)
    have magBound : mag.2≤3*(4*W+3) := by rw [mc,sl]; omega
    have denBound : den.2≤3*(3*W+1) := by rw [dc']; simp; omega
    nlinarith only [P,Q,E,tl,bl,pl,ql,hw,ln,ld,rn,rd,plusBound,subBound,magBound,denBound,divCost]

  · change (divmod z D).quotient.natAbs.size≤_
    rw [floor]
    exact (Nat.size_le_size (Int.natAbs_ediv_le_natAbs ..)).trans zw

theorem roundSub_spec (l r : Fraction) (bits W : ℕ) (lp : 0<value l.den) (rp : 0<value r.den)
    (hw : bits≤W) (ln : l.num.length≤W) (ld : l.den.length≤W) (rn : r.num.length≤W) (rd : r.den.length≤W) :
    let out := roundSub l r bits
    (out.1:ℚ)/2^bits=ArchNumerics.roundDyadic
      ((value l.num:ℚ)/value l.den-(value r.num:ℚ)/value r.den) bits ∧ out.2≤10000*(W+1)^2 :=
  let h := roundSub_full l r bits W lp rp hw ln ld rn rd
  ⟨h.1,h.2.1⟩

private def natWords (n : List Bool) (t : ℕ) : Fraction :=
  weighted (BinaryIndexCap.count n.tail).1 (logTwoSeries t) (mantSeries n t)

private theorem natWords_spec {n : ℕ} (pos : 0<n) (t H : ℕ) (nw : n.size≤H) (tw : 1+t≤H) (two : 2≤H) :
    let f := natWords n.bits t
    let D := 1+t*(4*H+1)
    0<value f.den ∧ (value f.num:ℚ)/value f.den=(natParts n.bits t).1 ∧
      f.num.length≤5*(D+H)+1 ∧ f.den.length≤5*(D+H)+1 ∧
      f.gates + (BinaryIndexCap.count n.bits.tail).2≤200*(D+H+1)^2+(3*H+1)*H := by
  let D := 1+t*(4*H+1)
  have width : n.bits.length≤H := (Nat.size_eq_bits_len n).le.trans nw
  have ⟨bn,bd,mn,md⟩ := series_widths n.bits t H width tw two
  obtain ⟨bp,mp⟩ := series_den_pos pos t
  obtain ⟨kv,kl,kc⟩ := BinaryIndexCap.count_spec n.bits.tail
  have tl : n.bits.tail.length≤H := by rw [List.length_tail]; omega
  have packed := weighted_spec (BinaryIndexCap.count n.bits.tail).1 (logTwoSeries t) (mantSeries n.bits t)
    (D+H) bp mp (kl.le.trans (tl.trans (Nat.le_add_left ..))) (bn.trans (Nat.le_add_right ..))
    (bd.trans (Nat.le_add_right ..)) (mn.trans (Nat.le_add_right ..)) (md.trans (Nat.le_add_right ..))
  refine ⟨packed.1,packed.2.1.trans ?_,packed.2.2.1,packed.2.2.2.1,Nat.add_le_add packed.2.2.2.2 (kc.trans ?_)⟩
  · rw [kv,List.length_tail]; rfl
  · gcongr

private def countedNat (n : List Bool) (t : ℕ) : Fraction :=
  let parts := prepare n t
  let k := BinaryIndexCap.count n.tail
  let f := weighted k.1 parts.1 parts.2.1
  { f with gates := parts.2.2+(f.gates+k.2) }

private theorem counted_eq (n : List Bool) (t : ℕ) :
    countedNat n t={natWords n t with gates := (natParts n t).2+((natWords n t).gates+(BinaryIndexCap.count n.tail).2)} := rfl

private theorem roundSub_update (l r : Fraction) (a b bits : ℕ) :
    roundSub {l with gates := a} {r with gates := b} bits=roundSub l r bits := by
  cases l; cases r; rfl

/-- The exact fixed-point logarithm on positive canonical binary inputs. The
external precision supplies the requested digit count. All logarithm-series,
fraction assembly, signed floor division and width-counter gates are included. -/
def binaryLog (u v : List Bool) (bits : ℕ) : ℤ × ℕ :=
  let t := bits+(u.length-1)+(v.length-1)+4
  let l := countedNat u t
  let r := countedNat v t
  let out := roundSub l r bits
  (out.1,l.gates+r.gates+out.2+t+bits+4)

set_option maxHeartbeats 800000 in
theorem binaryLog_full {u v : ℕ} (up : 0<u) (vp : 0<v) (bits : ℕ) :
    let out := binaryLog u.bits v.bits bits
    let H := bits+u.size+v.size+8
    (out.1:ℚ)/2^bits=ArchNumerics.approxLog u v bits ∧ out.2≤16777216*H^5 ∧ out.1.natAbs.size≤148*H^2 := by
  intro out H
  let t := bits+u.log2+v.log2+4
  let D := 1+t*(4*H+1)
  have len {n : ℕ} (p : 0<n) : n.bits.length=n.log2+1 := by
    rw [Nat.size_eq_bits_len]
    exact Nat.le_antisymm (Nat.size_le.mpr Nat.lt_log2_self) (Nat.lt_size.mpr (Nat.log2_self_le p.ne'))
  have cut : bits+(u.bits.length-1)+(v.bits.length-1)+4=t := by simp [len up,len vp,t]
  have uu : u.log2<u.size := Nat.lt_size.mpr (Nat.log2_self_le up.ne')
  have vv : v.log2<v.size := Nat.lt_size.mpr (Nat.log2_self_le vp.ne')
  have tt : 1+t≤H := by dsimp [H,t]; omega
  have two : 2≤H := by dsimp [H]; omega
  have hw : bits≤H := by dsimp [H]; omega
  let l := natWords u.bits t
  let r := natWords v.bits t
  obtain ⟨lp,lv,ln,ld,lc⟩ := natWords_spec up t H (by dsimp [H]; omega) tt two
  obtain ⟨rp,rv,rn,rd,rc⟩ := natWords_spec vp t H (by dsimp [H]; omega) tt two
  let W := 5*(D+H)+1
  obtain ⟨val,gate,ow⟩ := roundSub_full l r bits W lp rp (by dsimp [W]; omega) ln ld rn rd
  have comp := approxLog_series_gates up vp bits
  have combined : (roundSub l r bits).1=out.1 := by simp only [out,binaryLog,cut,counted_eq,roundSub_update,l,r]
  have small : D≤6*H^2 := calc
    _ ≤ 1+H*(4*H+1) := by dsimp [D]; gcongr; omega
    _ ≤ _ := by nlinarith only [Nat.le_self_pow (by decide : 2≠0) H,two]
  have widen : D+H+1≤8*H^2 := by nlinarith only [small,Nat.le_self_pow (by decide : 2≠0) H,two]
  have ww : W+1≤37*H^2 := by dsimp [W]; nlinarith only [two,small,Nat.le_self_pow (by decide : 2≠0) H]
  refine ⟨?_,?_,?_⟩
  · rw [←combined,val]
    rw [show (value l.num:ℚ)/value l.den=(natParts u.bits t).1 from lv,
      show (value r.num:ℚ)/value r.den=(natParts v.bits t).1 from rv]
    exact comp.1
  · change (binaryLog u.bits v.bits bits).2≤_
    unfold binaryLog
    simp only [cut,counted_eq,roundSub_update]
    change ((natParts u.bits t).2+(l.gates+_))+((natParts v.bits t).2+(r.gates+_))+(roundSub l r bits).2+t+bits+4≤_
    have old : (natParts u.bits t).2+(natParts v.bits t).2≤100000*H^5 := comp.2
    have each : 200*(D+H+1)^2+(3*H+1)*H≤200*(8*H^2)^2+(3*H+1)*H := by gcongr
    have finalCost := gate.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ww 2))
    have fourth : H^4≤H^5 := Nat.pow_le_pow_right (by omega) (by decide)
    have left : l.gates+_≤_ := lc.trans each
    have right : r.gates+_≤_ := rc.trans each
    nlinarith only [old,left,right,finalCost,fourth,
      Nat.le_self_pow (by decide : 5≠0) H,Nat.pow_le_pow_right (by omega : 0<H) (by decide : 2≤5),tt,hw,two]

  · rw [←combined]
    omega

theorem binaryLog_spec {u v : ℕ} (up : 0<u) (vp : 0<v) (bits : ℕ) :
    let out := binaryLog u.bits v.bits bits
    let H := bits+u.size+v.size+8
    (out.1:ℚ)/2^bits=ArchNumerics.approxLog u v bits ∧ out.2≤16777216*H^5 :=
  let h := binaryLog_full up vp bits
  ⟨h.1,h.2.1⟩

end Cogentic.BinaryLogSeries
