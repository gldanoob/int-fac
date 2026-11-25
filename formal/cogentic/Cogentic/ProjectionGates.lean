import Cogentic.BinaryRootColumnsCost
import Cogentic.MarkSeparation
import Cogentic.CandidateRuntime

namespace Cogentic.BinaryProjection
open BinaryDivision BinaryPivot BinaryLogSeries Finset

/-- Signed dyadic rounding uses the same floor and tie rule as the logarithm. -/
def roundWord (x : SignedWord) (src dst : ℕ) : ℤ × ℕ :=
  let denom := List.replicate src false++[true]
  let a : Fraction := ⟨x.digits,denom,0⟩
  let zero : Fraction := ⟨[],[true],0⟩
  let out := if x.negative then roundSub zero a dst else roundSub a zero dst
  (out.1,out.2+denom.length+1)

theorem roundWord_spec (x : SignedWord) (src dst W : ℕ) (xw : x.digits.length≤W)
    (sw : src+1≤W) (dw : dst≤W) :
    let out := roundWord x src dst
    (out.1:ℚ)/2^dst=ArchNumerics.roundDyadic ((x.decode:ℚ)/2^src) dst ∧
      out.2≤11000*(W+1)^2 := by
  let denom := List.replicate src false++[true]
  let a : Fraction := ⟨x.digits,denom,0⟩
  let zero : Fraction := ⟨[],[true],0⟩
  have dv : value denom=2^src := by rw [show denom=List.replicate src false++[true] from rfl,BinaryPowerScan.value_low_zeros]; simp [value]
  have dl : denom.length=src+1 := by simp [denom]
  have dp : 0<value a.den := dv ▸ Nat.two_pow_pos _
  have zp : 0<value zero.den := by decide
  have zw : zero.den.length≤W := by change 1≤W; omega
  have pos := roundSub_spec a zero dst W dp zp dw xw (dl.le.trans sw) (Nat.zero_le _) zw
  have neg := roundSub_spec zero a dst W zp dp dw (Nat.zero_le _) zw xw (dl.le.trans sw)
  have budget : 10000*(W+1)^2+denom.length+1≤11000*(W+1)^2 := by rw [dl]; nlinarith only [sw]
  cases h : x.negative
  · change (((if x.negative then roundSub zero a dst else roundSub a zero dst).1:ℤ):ℚ)/_= _ ∧ _≤_
    simp only [h,Bool.false_eq_true,if_false]
    refine ⟨?_,?_⟩
    · simpa [a,zero,value,dv,SignedWord.decode,signed,h] using pos.1
    · simpa only [roundWord,h,Bool.false_eq_true,if_false] using (Nat.add_le_add_right (Nat.add_le_add_right pos.2 denom.length) 1).trans budget
  · refine ⟨?_,?_⟩
    · simpa [roundWord,h,a,zero,value,dv,SignedWord.decode,signed,neg_div] using neg.1
    · simpa only [roundWord,h,if_true] using (Nat.add_le_add_right (Nat.add_le_add_right neg.2 denom.length) 1).trans budget

/-- The common denominator of the logarithm words is implicit during summation. -/
def sumPrefix (y : ℕ → SignedWord) : ℕ → SignedWord × ℕ
  | 0 => (⟨false,[]⟩,0)
  | j+1 =>
    let r := sumPrefix y j
    let v := y j
    let add := signedDifference r.1 ⟨!v.negative,v.digits⟩
    (add.1,r.2+add.2+1)

theorem sumPrefix_spec (y : ℕ → SignedWord) (j W : ℕ) (bound : ∀ k<j,(y k).digits.length≤W) :
    let r := sumPrefix y j
    r.1.decode=∑ k∈range j,(y k).decode ∧ r.1.digits.length≤W+j ∧ r.2≤j*(25*(W+j)+9) := by
  induction j with
  | zero => simp [sumPrefix,SignedWord.decode,signed,value]
  | succ j ih =>
    let r := sumPrefix y j
    let v := y j
    let neg : SignedWord := ⟨!v.negative,v.digits⟩
    obtain ⟨rv,rl,rc⟩ := ih (fun i hi=>bound _ (by omega))
    change r.1.decode=_ at rv; change r.1.digits.length≤_ at rl; change r.2≤_ at rc
    have wv := bound j (Nat.lt_succ_self _)
    change v.digits.length≤W at wv
    have nv : neg.decode= -v.decode := by cases h : v.negative <;> simp [neg,SignedWord.decode,signed,h]
    have ⟨val,cost⟩ := signedDifference_spec r.1 neg
    have len := CandidateRuntime.difference_length r.1 neg
    have cap : max r.1.digits.length neg.digits.length≤W+j := max_le rl (wv.trans (Nat.le_add_right ..))
    change (signedDifference r.1 neg).1.decode=_ ∧ (signedDifference r.1 neg).1.digits.length≤_ ∧
      r.2+(signedDifference r.1 neg).2+1≤_
    rw [val,nv,rv,sub_neg_eq_add,sum_range_succ]
    exact ⟨rfl,by omega,by
      have step : (signedDifference r.1 neg).2≤25*(W+j)+8 := cost.trans_le (by omega)
      calc _ ≤ j*(25*(W+j)+9)+(25*(W+j)+9) := by omega
           _ = (j+1)*(25*(W+j)+9) := (Nat.succ_mul ..).symm
           _ ≤ _ := by gcongr; omega⟩

/-- Project a logarithm vector whose signed numerators have precision raw.
The supplied nonnegative h is the previously computed dyadic Helmert numerator. -/
def row (y : ℕ → SignedWord) (j : ℕ) (h : List Bool) (raw dst : ℕ) : ℤ × ℕ :=
  let total := sumPrefix y j
  let diff := cross ⟨false,[true]⟩ total.1 ⟨false,j.bits⟩ (y j)
  let p := multiply diff.1.digits h
  let out := roundWord ⟨diff.1.negative,p.1⟩ (2*raw) dst
  (out.1,total.2+diff.2+p.2+out.2+1)

theorem row_spec {d : ℕ} (q : Vector ℚ d) (y : ℕ → SignedWord) (j : ℕ) (h : List Bool) (raw dst W : ℕ)
    (_positive : 0<j) (logWords : ∀ k≤j,((y k).decode:ℚ)/2^raw=q.toArray[k]?.getD 0)
    (helm : (value h:ℚ)/2^raw=ArchNumerics.approxSqrt 1 (j*(j+1)) raw)
    (bound : ∀ k≤j,(y k).digits.length≤W) (jw : j≤W) (hw : h.length≤W) (pw : 2*raw+1≤W) (dw : dst≤W) :
    let out := row y j h raw dst
    (out.1:ℚ)/2^dst=ArchNumerics.roundDyadic (Concrete.projection q j raw) dst ∧
      out.2≤1000000*(W+1)^3 := by
  let total := sumPrefix y j
  let diff := cross ⟨false,[true]⟩ total.1 ⟨false,j.bits⟩ (y j)
  let p := multiply diff.1.digits h
  let x : SignedWord := ⟨diff.1.negative,p.1⟩
  obtain ⟨tv,tl,tc⟩ := sumPrefix_spec y j W (fun i hi=>bound i hi.le)
  change total.1.decode=_ at tv; change total.1.digits.length≤_ at tl; change total.2≤_ at tc
  have bw : j.bits.length≤W := (Nat.size_eq_bits_len j).le.trans ((Nat.size_le.mpr Nat.lt_two_pow_self).trans jw)
  have w0 : [true].length≤2*W := by change 1≤2*W; omega
  have tw : total.1.digits.length≤2*W := by omega
  obtain ⟨dv,dc⟩ := cross_spec ⟨false,[true]⟩ total.1 ⟨false,j.bits⟩ (y j) (2*W) w0 tw
    (by change j.bits.length≤_; omega) ((bound j le_rfl).trans (by omega))
  change diff.1.decode=_ at dv; change diff.2≤_ at dc
  have one : (⟨false,[true]⟩:SignedWord).decode=1 := rfl
  have idx : (⟨false,j.bits⟩:SignedWord).decode=(j:ℤ) := by simp [SignedWord.decode,signed]
  rw [one,idx,one_mul] at dv
  have dl := BinaryReconstruction.cross_length ⟨false,[true]⟩ total.1 ⟨false,j.bits⟩ (y j)
    w0 tw (by change j.bits.length≤_; omega) ((bound j le_rfl).trans (by omega))
  change diff.1.digits.length≤_ at dl
  obtain ⟨pv,pl,pc⟩ := multiply_spec diff.1.digits h
  change value p.1=_ at pv; change p.1.length≤_ at pl; change p.2≤_ at pc
  have xv : x.decode=(value h:ℤ)*diff.1.decode := by
    simp only [x,SignedWord.decode,signed,pv,Nat.cast_mul]
    cases diff.1.negative <;> simp
  obtain ⟨rounded,cost⟩ := roundWord_spec x (2*raw) dst (8*W+1) (by change p.1.length≤_; omega) (by omega) (by omega)
  have ve : (x.decode:ℚ)/2^(2*raw)=Concrete.projection q j raw := by
    unfold Concrete.projection
    rw [←helm,xv,dv]
    rw [tv]
    have sums : (∑ k∈range j,((y k).decode:ℚ))/2^raw=∑ k∈range j,q.toArray[k]?.getD 0 := by
      rw [sum_div]; exact sum_congr rfl (fun k hk=>logWords k (mem_range.mp hk).le)
    rw [←sums,←logWords j le_rfl,show (2:ℚ)^(2*raw)=2^raw*2^raw by rw [←pow_add]; congr 1; omega]
    push_cast; ring
  refine ⟨rounded.trans (congrArg (fun v=>ArchNumerics.roundDyadic v dst) ve),?_⟩
  have pm : p.2≤W*((6*W+1)+5*((6*W+1)+2*W)) := pc.trans (by gcongr <;> omega)
  have tm : total.2≤W*(25*(W+W)+9) := tc.trans (by gcongr)
  change total.2+diff.2+p.2+(roundWord x (2*raw) dst).2+1≤_
  nlinarith only [tm,dc,pm,cost]

/-- Returned fixed-point words of the two mark vectors. Failed guards may use
zero here since the executable abandons the whole column in that case. -/
def logWord (s : Marking.Input) (a : ℕ) (side : Bool) (P k : ℕ) : ℤ :=
  if hk : k<s.degree then
    match RootLogs.isolate s side ⟨k,hk⟩ (2*P) with
    | none => 0
    | some x =>
      let dist := |(a:ℚ)/s.A-x|
      if (1/2:ℚ)^(s.L₀+1)≤dist then (binaryLog dist.num.natAbs.bits dist.den.bits (2*P+16)).1 else 0
  else 0

theorem logWord_value (s : Marking.Input) (a : ℕ) (side : Bool) (P : ℕ) (k : Fin s.degree) {x v : ℚ}
    (root : RootLogs.isolate s side k (2*P)=some x)
    (log : RootLogs.markLog s.A a x s.L₀ (2*P+16)=some v) :
    (logWord s a side P k.val:ℚ)/2^(2*P+16)=v := by
  let t := |(a:ℚ)/s.A-x|
  change (if (1/2:ℚ)^(s.L₀+1)≤t then some (ArchNumerics.approxLog t.num.natAbs t.den (2*P+16)) else none)=some v at log
  split at log
  next guard =>
    cases log
    have dp : 0<t := (show (0:ℚ)<(1/2:ℚ)^(s.L₀+1) by positivity).trans_le guard
    have up := Nat.pos_of_ne_zero (by simpa only [Int.natAbs_ne_zero,Rat.num_ne_zero] using dp.ne' : t.num.natAbs≠0)
    simp only [logWord,dif_pos k.isLt,root,←show t=|(a:ℚ)/s.A-x| from rfl,if_pos guard]
    exact (binaryLog_spec up t.pos _).1
  next => cases log

private theorem logWord_width {n g : ℕ} {pair : TryPair.PairData} {rel : Marking.Relations}
    (marked : Marking.stageOne (TryPair.fixedInput n g pair)=some rel) {a : ℕ} (am : a∈rel.marks)
    (side : Bool) (k : ℕ) :
    let s := TryPair.fixedInput n g pair
    let P := TryPair.localBits s rel
    (logWord s a side P k).natAbs.size≤2^(2100*TwoThirdsCost.scale (n.log2+1)) := by
  intro s P
  let b := n.log2+1
  let S := TwoThirdsCost.scale b
  let W := 2^(1013*S)
  have hb : 0<b := Nat.succ_pos _
  have hs : Fixed.h b≤S := (Nat.le_mul_of_pos_left _ (Fixed.degree_pos hb)).trans (Fixed.scale_bounds hb).1
  have zs : Fixed.z b≤S := (Nat.le_mul_of_pos_left _ (Fixed.degree_pos hb)).trans hs
  have sp : 0<S := (Nat.succ_pos b.log2).trans_le zs
  have dz : s.degree≤2^S := (Fixed.degree_le_bits b).trans
    (Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right Nat.zero_lt_two zs))
  have sw : 2^S≤W := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  have ss : S≤W := (Nat.lt_two_pow_self (n:=S)).le.trans sw
  have dw : s.degree.size≤W := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (dz.trans sw)
  have pw : P≤W := BinaryHelmert.fixed_local_bits marked
  have wp : 0<W := Nat.two_pow_pos _
  have area : s.A.size=10000*Fixed.h b+1 := by change (2^(10000*Fixed.h b)).size=_; rw [Nat.size_pow]
  have band : (19*s.K₁.log2+19)/20=95*Fixed.h b := by
    change (19*(2^(100*Fixed.h b)).log2+19)/20=_; rw [Nat.log2_two_pow]; omega
  change _≤2^(2100*S)
  unfold logWord
  split
  next hk =>
    split
    next => simp
    next x hit =>
      simp only []
      split
      next guard =>
        let t := |(a:ℚ)/s.A-x|
        have pos : 0<t := (show (0:ℚ)<(1/2:ℚ)^(s.L₀+1) by positivity).trans_le guard
        have up := Nat.pos_of_ne_zero (by simpa only [Int.natAbs_ne_zero,Rat.num_ne_zero] using pos.ne' : t.num.natAbs≠0)
        have ⟨num,den⟩ := RootLogs.isolate_distance_width marked am hit
        change t.num.natAbs.size≤ s.A.size+s.degree.size+(19*s.K₁.log2+19)/20+2*P+5 at num
        change t.den.size≤ s.A.size+s.degree.size+(19*s.K₁.log2+19)/20+2*P+5 at den
        rw [area,band] at num den
        have hW : 2*P+16+t.num.natAbs.size+t.den.size+8≤32768*W := by omega
        apply (binaryLog_full up t.pos (2*P+16)).2.2.trans
        calc _ ≤ 2^8*(2^15*W)^2 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left hW 2)
             _ = 2^(8+(15+1013*S)*2) := by dsimp only [W]; simp only [←pow_add,←pow_mul]
             _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
      next => simp
  next => simp

/-- Cost of applying the projection and rounding its result, with the log and
Helmert words supplied by their separately charged computations. -/
def columnsWork (s : Marking.Input) (rel : Marking.Relations) : ℕ :=
  let P := TryPair.localBits s rel
  ∑ i : Fin rel.marks.length, ∑ r : Fin (2*s.degree-2),
    let j := r.val%(s.degree-1)+1
    let side := decide (s.degree-1≤r.val)
    let h := (BinaryHelmert.coefficient j.bits (2*P+16)).1
    (row (fun k=>encode (logWord s (rel.marks.get i) side P k)) j h (2*P+16) (3*P/2)).2

theorem fixed_columns_gates {n g : ℕ} {pair : TryPair.PairData} {rel : Marking.Relations}
    (marked : Marking.stageOne (TryPair.fixedInput n g pair)=some rel) (big : 2≤Fixed.d (n.log2+1)) :
    columnsWork (TryPair.fixedInput n g pair) rel≤2^(17000*TwoThirdsCost.scale (n.log2+1)) := by
  let b := n.log2+1
  let S := TwoThirdsCost.scale b
  let s := TryPair.fixedInput n g pair
  let P := TryPair.localBits s rel
  let W := 2^(2100*S)
  have hb : 0<b := Nat.succ_pos _
  have hs : Fixed.h b≤S := (Nat.le_mul_of_pos_left _ (Fixed.degree_pos hb)).trans (Fixed.scale_bounds hb).1
  have zs : Fixed.z b≤S := (Nat.le_mul_of_pos_left _ (Fixed.degree_pos hb)).trans hs
  have sp : 0<S := (Nat.succ_pos b.log2).trans_le zs
  have dz : s.degree≤2^S := (Fixed.degree_le_bits b).trans (Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right Nat.zero_lt_two zs))
  have small : 2^S≤W := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  have wp : 0<W := Nat.two_pow_pos _
  have pw : P≤2^(1013*S) := BinaryHelmert.fixed_local_bits marked
  have room : 64*2^(1013*S)≤W := (show 2^6*2^(1013*S)=2^(6+1013*S) from (pow_add ..).symm).le.trans
    (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
  have unitW : 0<2^(1013*S) := Nat.two_pow_pos _
  have fixed (i : Fin rel.marks.length) (r : Fin (2*s.degree-2)) :
      let j := r.val%(s.degree-1)+1
      let side := decide (s.degree-1≤r.val)
      let h := (BinaryHelmert.coefficient j.bits (2*P+16)).1
      (row (fun k=>encode (logWord s (rel.marks.get i) side P k)) j h (2*P+16) (3*P/2)).2≤1000000*(W+1)^3 := by
    intro j side h
    have dp : 2≤ s.degree := big
    have jl : j<s.degree := by have := Nat.mod_lt r.val (by omega : 0 < s.degree-1); dsimp [j]; omega
    have jp : 0<j := Nat.succ_pos _
    have ⟨vv,hl,_⟩ := BinaryHelmert.coefficient_spec j.bits (by simpa) (2*P+16)
    change h.length=_ at hl
    let y := fun k=>encode (logWord s (rel.marks.get i) side P k)
    let q : Vector ℚ s.degree := Vector.ofFn (fun k=>((y k.val).decode:ℚ)/2^(2*P+16))
    apply (row_spec q y j h (2*P+16) (3*P/2) W jp ?_ (by simpa only [value_bits] using vv) ?_
      (jl.le.trans (dz.trans small)) (by omega) (by omega) (by omega)).2
    · intro k hk
      have kl : k<s.degree := hk.trans_lt jl
      have kk : k<q.toArray.size := by simpa using kl
      rw [Array.getElem?_eq_getElem kk]; simp [q]
    · intro k _
      simpa only [y,encode,Nat.size_eq_bits_len] using logWord_width marked (rel.marks.get_mem i) side k
  have m : rel.marks.length≤2^(10000*S) := (Concrete.retained_size marked).trans
    (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_left _ hs))
  have both := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>
    Finset.sum_le_sum (s:=Finset.univ) (fun r _=>fixed i r))
  change columnsWork s rel≤2^(17000*S)
  calc
    _ ≤ rel.marks.length*((2*s.degree-2)*(1000000*(W+1)^3)) := by
      simpa only [columnsWork,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using both
    _ ≤ 2^(10000*S)*((2^1*2^S)*(2^20*(2^1*W)^3)) := by
      have dim : 2*s.degree-2≤2^1*2^S := (Nat.sub_le ..).trans (Nat.mul_le_mul_left _ dz)
      gcongr <;> first | decide | omega
    _ = 2^(10000*S+(1+S+(20+(1+2100*S)*3))) := by dsimp only [W]; simp only [←pow_mul,←pow_add]
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)

end Cogentic.BinaryProjection
