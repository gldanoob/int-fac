import Cogentic.CorrectedBaseCost

namespace Cogentic.BinaryPreliminary
open BinaryDivision BinaryPivot BinarySaturation CandidateRuntime BinaryPerturbation Construction

/-- A signed affine operation a*x+c with canonical output. -/
def affine (a : List Bool) (x c : SignedWord) : SignedWord × ℕ :=
  let v := horner a [c,x]
  let norm := adjust v.1 [] false
  (norm.1,v.2+norm.2+1)

theorem affine_spec (a : List Bool) (x c : ℤ) {W : ℕ} (aw : a.length ≤ W)
    (xw : x.natAbs.size ≤ W) (cw : c.natAbs.size ≤ W) :
    let out := affine a (encode x) (encode c)
    out.1=encode (c+(value a:ℤ)*x) ∧ out.1.digits.length ≤ 6*(W+1) ∧
      out.2 ≤ 2000*(W+1)^2 := by
  let V := 5*W+2
  let v := horner a [encode c,encode x]
  obtain ⟨val,len,pay⟩ := horner_spec a [c,x] W V (by simpa using And.intro cw xw)
    (by dsimp [V]; omega) (by simp [V]; omega)
  change v.1.decode=_ at val
  change v.1.digits.length ≤ _ at len
  change v.2 ≤ _ at pay
  simp only [List.length_cons,List.length_nil] at len pay
  simp [Marking.horner] at val
  obtain ⟨eq,nl,nc⟩ := adjust_spec v.1 [] false
  simp only [value,signed,Bool.false_eq_true,if_false,Nat.cast_zero,sub_zero,val,
    List.length_nil,Nat.max_zero] at eq nl nc
  change (adjust v.1 [] false).1=_ ∧ (adjust v.1 [] false).1.digits.length ≤ _ ∧ v.2+(adjust v.1 [] false).2+1 ≤ _
  refine ⟨eq,by omega,?_⟩
  rw [nc]
  unfold evalStep at pay
  dsimp only [V] at pay
  nlinarith only [pay,len,aw,Nat.zero_le W]

def natProduct (a b : List Bool) : List Bool × ℕ :=
  let p := multiply a b
  let c := canonical p.1
  (c.1,p.2+c.2+1)

theorem natProduct_spec (a b : ℕ) {W : ℕ} (aw : a.size ≤ W) (bw : b.size ≤ W) :
    let p := natProduct a.bits b.bits
    p.1=(a*b).bits ∧ p.1.length ≤ 3*W ∧ p.2 ≤ 30*(W+1)^2 := by
  let p := multiply a.bits b.bits
  obtain ⟨v,l,c⟩ := multiply_spec a.bits b.bits
  change value p.1=_ at v
  change p.1.length ≤ _ at l
  change p.2 ≤ _ at c
  simp only [value_bits,Nat.size_eq_bits_len] at v l c
  have cap := c.trans (Nat.mul_le_mul bw (show a.size+5*(a.size+2*b.size) ≤ W+5*(W+2*W) by omega))
  have ⟨val,work⟩ := canonical_spec p.1
  have sz : (value p.1).size ≤ p.1.length := Nat.size_le.mpr (value_lt _)
  rw [v,Nat.mul_comm b a] at val sz
  change (canonical p.1).1=_ ∧ (canonical p.1).1.length ≤ _ ∧ p.2+(canonical p.1).2+1 ≤ _
  rw [val,work,Nat.size_eq_bits_len]
  exact ⟨rfl,by omega,by nlinarith only [cap,aw,bw,l]⟩

/-- The quotient word of exact signed Euclidean division. A zero numerator
or a zero quotient is returned in its canonical signed form. -/
def floorWord (x : SignedWord) (den : List Bool) : SignedWord × ℕ :=
  let d := divide den x.digits
  let nz := BinaryReconstruction.below [] d.remainder
  let q := addDigits d.quotient.length d.quotient [] (x.negative && nz.1)
  let norm := adjust ⟨x.negative,q.1⟩ [] false
  (norm.1,d.gates+nz.2+q.2+norm.2+3)

theorem floorWord_spec (x : ℤ) {D W : ℕ} (dp : 0<D) (xw : x.natAbs.size ≤ W) (dw : D.size ≤ W) :
    let r := floorWord (encode x) D.bits
    r.1=encode (x/(D:ℤ)) ∧ r.1.digits.length ≤ W+2 ∧ r.2 ≤ 200*(W+1)^2 := by
  let d := divide D.bits x.natAbs.bits
  let nz := BinaryReconstruction.below [] d.remainder
  let fix := decide (x<0) && nz.1
  let q := addDigits d.quotient.length d.quotient [] fix
  let raw : SignedWord := ⟨decide (x<0),q.1⟩
  have ql : d.quotient.length=x.natAbs.size := (BinaryIndexCap.quotient_length ..).trans (Nat.size_eq_bits_len _)
  obtain ⟨al,ac,_⟩ := addDigits_spec d.quotient.length d.quotient [] fix le_rfl (by simp)
  change q.1.length=_ at al
  change q.2=_ at ac
  obtain ⟨v,_,pg⟩ := BinaryReconstruction.divmod_spec x D W dp xw dw
  change signed (decide (x<0)) (value (canonical q.1).1)=_ at v
  rw [(canonical_spec q.1).1,value_bits] at v
  change raw.decode=x/(D:ℤ) at v
  have paid : d.gates+nz.2+q.2 ≤ (BinaryReconstruction.divmod x D).gates := by
    dsimp only [BinaryReconstruction.divmod,q,fix,d,nz]; omega
  obtain ⟨eq,l,g⟩ := adjust_spec raw [] false
  change (adjust raw [] false).1=encode (raw.decode-signed false (value [])) at eq
  simp only [value,signed,Bool.false_eq_true,if_false,Nat.cast_zero,sub_zero,v] at eq
  change (adjust raw [] false).1=_ ∧ (adjust raw [] false).1.digits.length ≤ _ ∧
    d.gates+nz.2+q.2+(adjust raw [] false).2+3 ≤ _
  change (adjust raw [] false).1.digits.length ≤ max q.1.length [].length+1 at l
  change (adjust raw [] false).2=28*max q.1.length [].length+14 at g
  simp only [List.length_nil,Nat.max_zero,al,ql] at l g
  exact ⟨eq,by omega,by nlinarith only [paid.trans pg,g,xw,Nat.zero_le (W^2)]⟩

private theorem nearest_fraction {step : ℕ} (sp : 0<step) (res : ℕ) (z : ℤ) {D : ℕ} (dp : 0<D) :
    nearest step res ((z:ℚ)/D) = res+(step:ℤ)*
      ((2*(z-(res:ℤ)*D)+(step*D:ℕ))/(2*step*D:ℕ)) := by
  have a : (D:ℚ)≠0 := by exact_mod_cast dp.ne'
  have b : (step:ℚ)≠0 := by exact_mod_cast sp.ne'
  unfold nearest
  congr 2
  rw [←Rat.floor_intCast_div_natCast]
  congr 1
  push_cast
  field_simp

/-- Round a signed fraction to the nearest integer in the supplied residue
class, resolving ties by the same floor rule as Construction.nearest. -/
def round (step res : List Bool) (num : SignedWord) (den : List Bool) : SignedWord × ℕ :=
  let offset := natProduct res den
  let shifted := adjust num offset.1 false
  let scale := natProduct step den
  let twice := natProduct [false,true] scale.1
  let top := affine [false,true] shifted.1 ⟨false,scale.1⟩
  let q := floorWord top.1 twice.1
  let output := affine step q.1 ⟨false,res⟩
  (output.1,offset.2+shifted.2+scale.2+twice.2+top.2+q.2+output.2+7)

theorem round_spec {step res D W : ℕ} (sp : 0<step) (dp : 0<D) (z : ℤ) (sw : step.size ≤ W)
    (rw' : res.size ≤ W) (dw : D.size ≤ W) (zw : z.natAbs.size ≤ W) :
    let out := round step.bits res.bits (encode z) D.bits
    out.1=encode (nearest step res ((z:ℚ)/D)) ∧ out.2 ≤ 2^26*(W+1)^2 := by
  let offset := natProduct res.bits D.bits
  let shifted := adjust (encode z) offset.1 false
  let scale := natProduct step.bits D.bits
  let twice := natProduct [false,true] scale.1
  let top := affine [false,true] shifted.1 ⟨false,scale.1⟩
  let q := floorWord top.1 twice.1
  let out := affine step.bits q.1 ⟨false,res.bits⟩
  have ⟨ov,ol,oc⟩ := natProduct_spec res D rw' dw
  have ⟨sv,sl,sc⟩ := natProduct_spec step D sw dw
  change offset.1=_ at ov
  change offset.1.length ≤ _ at ol
  change offset.2 ≤ _ at oc
  change scale.1=_ at sv
  change scale.1.length ≤ _ at sl
  change scale.2 ≤ _ at sc
  have ⟨av,al,ac⟩ := adjust_spec (encode z) offset.1 false
  change shifted.1=_ at av
  change shifted.1.digits.length ≤ _ at al
  change shifted.2=_ at ac
  simp only [decode_encode,signed,Bool.false_eq_true,if_false,ov,value_bits,Nat.cast_mul] at av
  let u := z-(res:ℤ)*D
  change shifted.1=encode u at av
  have zs : (encode z).digits.length ≤ W := by simpa [encode,Nat.size_eq_bits_len] using zw
  have ul : u.natAbs.size ≤ 3*W+1 := by rw [av] at al; change u.natAbs.bits.length ≤ _ at al; rw [Nat.size_eq_bits_len] at al; omega
  let T := 3*(W+1)
  have dl : (step*D).size ≤ T := by rw [sv,Nat.size_eq_bits_len] at sl; dsimp [T]; omega
  have two : (2:ℕ).size ≤ T := by dsimp [T]; change 2 ≤ _; omega
  obtain ⟨tv,tl,tc⟩ := natProduct_spec 2 (step*D) two dl
  change (natProduct [false,true] (step*D).bits).1=_ at tv
  change (natProduct [false,true] (step*D).bits).1.length ≤ _ at tl
  change (natProduct [false,true] (step*D).bits).2 ≤ _ at tc
  rw [←sv] at tv tl tc
  change twice.1=_ at tv
  change twice.1.length ≤ _ at tl
  change twice.2 ≤ _ at tc
  have enc (v : ℕ) : encode (v:ℤ)=⟨false,v.bits⟩ := by simp [encode]
  have st : u.natAbs.size ≤ T := by dsimp [T]; omega
  obtain ⟨hv,hl,hc⟩ := affine_spec [false,true] u ((step*D:ℕ):ℤ) (W:=T) two st (by change (step*D).size ≤ T; exact dl)
  rw [←av,enc,←sv] at hv hl hc
  change top.1=_ at hv
  change top.1.digits.length ≤ _ at hl
  change top.2 ≤ _ at hc
  let num : ℤ := 2*u+(step*D:ℕ)
  have hi : top.1=encode num := hv.trans (congrArg encode (by change (step*D:ℕ)+2*u=2*u+(step*D:ℕ); ring))
  let H := 6*(T+1)
  have hw : num.natAbs.size ≤ H := by rw [hi] at hl; exact (Nat.size_eq_bits_len _).ge.trans hl
  have den : (2*(step*D)).size ≤ H := by rw [tv,Nat.size_eq_bits_len] at tl; dsimp [H]; omega
  have pos : 0<2*(step*D) := by positivity
  have ⟨qv,ql,qc⟩ := floorWord_spec num pos hw den
  rw [←hi,←tv] at qv ql qc
  change q.1=_ at qv
  change q.1.digits.length ≤ _ at ql
  change q.2 ≤ _ at qc
  let Q := num/(2*(step*D):ℕ)
  have qw : Q.natAbs.size ≤ H+2 := by rw [qv] at ql; exact (Nat.size_eq_bits_len _).ge.trans ql
  have sH : W ≤ H+2 := by dsimp [H,T]; omega
  have ⟨yv,_,yc⟩ := affine_spec step.bits Q (res:ℤ) (W:=H+2)
    ((Nat.size_eq_bits_len _).le.trans (sw.trans sH)) qw (by simpa using rw'.trans sH)
  change q.1=encode Q at qv
  rw [←qv,enc] at yv yc
  change out.1=_ at yv
  change out.2 ≤ _ at yc
  rw [value_bits] at yv
  change out.1=_ ∧ offset.2+shifted.2+scale.2+twice.2+top.2+q.2+out.2+7 ≤ _
  refine ⟨yv.trans (congrArg encode ?_),?_⟩
  · rw [nearest_fraction sp res z dp]; dsimp only [Q,num,u]; rw [Nat.mul_assoc 2 step D]
  · have maxsize : max (encode z).digits.length offset.1.length ≤ 3*W := by omega
    dsimp only [H,T] at hc tc qc yc
    nlinarith only [oc,sc,tc,hc,qc,yc,ac,maxsize,Nat.zero_le (W^2),Nat.zero_le W]


private def flag (b : Bool) : List Bool := if b then [true] else []

private theorem flag_bits (b : Bool) : flag b=b.toNat.bits := by cases b <;> rfl

/-- One coefficient of the preliminary polynomial. The step is shared across
the coefficient loop and the target fraction may have an unreduced denominator. -/
def coefficient (P ell step leading den : List Bool) (bit first : Bool) (localWord targetWord : SignedWord) :
    SignedWord × ℕ :=
  let low := BinaryCorrectedBase.liftedCRT [false,true] P.tail (flag bit) (flag first)
  let loc := BinaryCorrectedBase.signedResidue localWord ell
  let crtWord := BinaryCorrectedBase.liftedCRT P ell low.1.1 loc.1
  let scaled := affine leading targetWord (encode 0)
  let rounded := round step crtWord.1.1 scaled.1 den
  (rounded.1,low.2+loc.2+crtWord.2+scaled.2+rounded.2+4)

def coefficientBudget (P ell W : ℕ) := 2^40*(P+ell+1)*(W+1)^2

theorem coefficient_spec {P ell leading den W : ℕ} (two : 2∣P) (apos : 1<P/2)
    (cop₁ : (2:ℕ).Coprime (P/2)) (cop₂ : P.Coprime ell) (ep : 0<ell) (dp : 0<den)
    (bit first : Bool) (v z : ℤ) (vw : v.natAbs.size ≤ W) (zw : z.natAbs.size ≤ W)
    (lw : leading.size ≤ W) (dw : den.size ≤ W) (top : P+ell*P ≤ W) :
    let lo := crt 2 (P/2) bit.toNat first.toNat
    let r := crt P ell lo (modulusResidue v ell)
    let out := coefficient P.bits ell.bits (P*ell).bits leading.bits den.bits bit first (encode v) (encode z)
    out.1=encode (nearest (P*ell) r ((leading:ℚ)*((z:ℚ)/den))) ∧ out.2 ≤ coefficientBudget P ell W := by
  intro lo r out
  have pp : 0<P := by omega
  have stp := Nat.mul_pos pp ep
  have half : P.bits.tail=(P/2).bits := (Nat.div2_bits_eq_tail _).symm
  have split : (P/2)*2=P := Nat.div_mul_cancel two
  have ns (a : ℕ) : a.size ≤ a := Nat.size_le.mpr Nat.lt_two_pow_self
  have pw : P ≤ W := by omega
  have ee : ell ≤ ell*P := Nat.le_mul_of_pos_right _ pp
  have ew : ell ≤ W := by omega
  have hW : (P/2).size ≤ W := (ns _).trans (by omega)
  have bs (b : Bool) : b.toNat<2 := by cases b <;> decide
  have flags : first.toNat<P/2 := by have := bs first; omega
  let low := BinaryCorrectedBase.liftedCRT [false,true] P.bits.tail (flag bit) (flag first)
  obtain ⟨ev,ec⟩ := BinaryCorrectedBase.liftedCRT_spec (W:=W) cop₁ (bs bit) flags
    ((ns _).trans (show bit.toNat+(P/2)*2 ≤ W by
      have := bs bit
      have : P ≤ ell*P := Nat.le_mul_of_pos_left _ ep
      omega)) hW
  rw [←half,←flag_bits,←flag_bits] at ev ec
  change low.1=(lo.bits,(lo/(P/2)).bits) at ev
  change low.2 ≤ _ at ec
  have ll : lo<P := by
    have small := Nat.chineseRemainder_lt_mul cop₁ bit.toNat first.toNat (by decide) (by omega)
    change crt 2 (P/2) bit.toNat first.toNat < P
    unfold crt; rw [dif_pos cop₁]
    exact small.trans_eq ((Nat.mul_comm 2 (P/2)).trans split)
  let loc := BinaryCorrectedBase.signedResidue (encode v) ell.bits
  obtain ⟨lv,lc⟩ := BinaryCorrectedBase.signedResidue_spec v ep vw ((ns _).trans ew)
  change loc.1=_ at lv
  change loc.2 ≤ _ at lc
  have rs : modulusResidue v ell<ell := by
    have np : (0:ℤ)<ell := by exact_mod_cast ep
    unfold modulusResidue
    have := Int.emod_nonneg v np.ne'
    have := Int.emod_lt_of_pos v np
    omega
  obtain ⟨rv,rc⟩ := BinaryCorrectedBase.liftedCRT_spec (W:=W) cop₂ ll rs
    ((ns _).trans (show lo+ell*P ≤ W by omega)) ((ns _).trans ew)
  let comb := BinaryCorrectedBase.liftedCRT P.bits ell.bits low.1.1 loc.1
  have lowbits : low.1.1=lo.bits := congrArg Prod.fst ev
  rw [←lv,←lowbits] at rv rc
  change comb.1=(r.bits,(r/ell).bits) at rv
  change comb.2 ≤ _ at rc
  have rbits : comb.1.1=r.bits := congrArg Prod.fst rv
  have rlen : r<P*ell := by
    dsimp only [r,crt]; rw [dif_pos cop₂]
    exact Nat.chineseRemainder_lt_mul cop₂ _ _ pp.ne' ep.ne'
  have stepW : P*ell ≤ W := by rw [Nat.mul_comm]; omega
  let sc := affine leading.bits (encode z) (encode 0)
  obtain ⟨sv,sl,sg⟩ := affine_spec leading.bits z 0 ((Nat.size_eq_bits_len _).le.trans lw) zw (by simp)
  simp only [value_bits,zero_add] at sv
  change sc.1=_ at sv
  change sc.1.digits.length ≤ _ at sl
  change sc.2 ≤ _ at sg
  let L := 6*(W+1)
  have WL : W ≤ L := by dsimp [L]; omega
  have sn : ((leading:ℤ)*z).natAbs.size ≤ L := by rw [sv] at sl; exact (Nat.size_eq_bits_len _).ge.trans sl
  have ⟨val,cost⟩ := round_spec stp dp ((leading:ℤ)*z) ((ns _).trans (stepW.trans WL))
    ((ns _).trans (rlen.le.trans (stepW.trans WL))) (dw.trans WL) sn
  rw [←rbits,←sv] at val cost
  change (round (P*ell).bits comb.1.1 sc.1 den.bits).1=_ at val
  change (round (P*ell).bits comb.1.1 sc.1 den.bits).2 ≤ _ at cost
  change (round (P*ell).bits comb.1.1 sc.1 den.bits).1=_ ∧
    low.2+loc.2+comb.2+sc.2+(round (P*ell).bits comb.1.1 sc.1 den.bits).2+4 ≤ _
  refine ⟨val.trans (congrArg encode (congrArg (nearest (P*ell) r) ?_)),?_⟩
  · push_cast; ring
  · have Eu := (ns ell).trans ew
    have p2 : P/2 ≤ P := Nat.div_le_self _ _
    have e' : P/2*(100*(W+1)^2) ≤ P*(100*(W+1)^2) := Nat.mul_le_mul_right _ p2
    dsimp only [L] at cost
    unfold coefficientBudget
    nlinarith only [ec,lc,rc,sg,cost,hW,Eu,e',p2,Nat.zero_le P,Nat.zero_le ell,
      Nat.zero_le (P*W),Nat.zero_le (P*W^2),Nat.zero_le (ell*W),Nat.zero_le (ell*W^2),
      Nat.zero_le (W^2),Nat.zero_le W]


/-- Scan the mask and both coefficient arrays in ascending degree order.
The target numerator words share one positive denominator. -/
def loop (P ell step leading den : List Bool) : List Unit → List Bool → Bool →
    List SignedWord → List SignedWord → List SignedWord × ℕ
  | [],_,_,_,_ => ([],1)
  | _::xs,mask,first,locals,nums =>
    let head := coefficient P ell step leading den (mask.headD false) first
      (locals.headD (encode 0)) (nums.headD (encode 0))
    let tail := loop P ell step leading den xs mask.tail false locals.tail nums.tail
    (head.1::tail.1,head.2+tail.2+6)

private theorem head_drop {α : Type*} (xs : List α) (i : ℕ) (d : α) :
    (xs.drop i).headD d=xs.getD i d := by
  induction i generalizing xs with
  | zero => cases xs <;> rfl
  | succ i ih => cases xs with
    | nil => simp
    | cons a xs => simpa only [List.drop_succ_cons,List.getD_cons_succ] using ih xs

private def coefficients (P ell leading D mask : ℕ) (localWords nums : List ℤ) (j : ℕ) :=
  let lo := crt 2 (P/2) (bitCoeff mask j) (if j=0 then 1 else 0)
  let r := crt P ell lo (modulusResidue (localWords.getD j 0) ell)
  nearest (P*ell) r ((leading:ℚ)*((nums.getD j 0:ℚ)/D))

private theorem loop_spec {P ell leading D W : ℕ} (two : 2∣P) (apos : 1<P/2)
    (cop₁ : (2:ℕ).Coprime (P/2)) (cop₂ : P.Coprime ell) (ep : 0<ell) (dp : 0<D)
    (lw : leading.size ≤ W) (dw : D.size ≤ W) (top : P+ell*P ≤ W)
    (mask : ℕ) (localWords nums : List ℤ) (ts : List Unit) (i : ℕ)
    (width : ∀ j∈List.range' i ts.length,
      (localWords.getD j 0).natAbs.size ≤ W ∧ (nums.getD j 0).natAbs.size ≤ W) :
    let out := loop P.bits ell.bits (P*ell).bits leading.bits D.bits ts (mask.bits.drop i) (decide (i=0))
      ((localWords.map encode).drop i) ((nums.map encode).drop i)
    out.1=(List.range' i ts.length).map (fun j=>encode (coefficients P ell leading D mask localWords nums j)) ∧
      out.2 ≤ 1+ts.length*(coefficientBudget P ell W+6) := by
  induction ts generalizing i with
  | nil => simp [loop]
  | cons t ts ih =>
    have hdr (xs : List ℤ) : ((xs.map encode).drop i).headD (encode 0)=encode (xs.getD i 0) := by
      rw [head_drop,List.getD_map]
    have maskBit : (mask.bits.drop i).headD false=mask.testBit i := by
      rw [head_drop,Nat.testBit_eq_inth]
      exact List.getD_default_eq_getI _
    have main := width i (by simp [List.range'_succ])
    obtain ⟨val,paid⟩ := coefficient_spec two apos cop₁ cop₂ ep dp (mask.testBit i) (decide (i=0))
      (localWords.getD i 0) (nums.getD i 0) main.1 main.2 lw dw top
    obtain ⟨tail,cost⟩ := ih (i+1) (fun j hj=>width j (by simp [List.range'_succ,hj]))
    simp only [Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,decide_false] at tail cost
    change (loop _ _ _ _ _ (t::ts) _ _ _ _).1=_ ∧ (loop _ _ _ _ _ (t::ts) _ _ _ _).2 ≤ _
    simp only [loop,maskBit,hdr,List.tail_drop,List.length_cons,List.range'_succ,List.map_cons,Nat.succ_mul ts.length]
    rw [tail,val]
    have flagFirst : (decide (i=0)).toNat=if i=0 then 1 else 0 := by by_cases h : i=0 <;> simp [h]
    exact ⟨by simp only [flagFirst,coefficients,bitCoeff],by omega⟩

/-- Produce the full preliminary output. The upstream root products are supplied
as signed integer coefficients, with a shared denominator for the target list. -/
def preliminaryWord (degree P ell leading D mask : List Bool) (localWords nums : List SignedWord) :
    List SignedWord × ℕ :=
  let step := natProduct P ell
  let fuel := tokens degree
  let output := loop P ell step.1 leading D fuel.1 mask true localWords nums
  (output.1,step.2+fuel.2+output.2+2)

theorem preliminaryWord_spec {d A m P ell leading D W : ℕ} (side : Bool)
    (two : 2∣P) (apos : 1<P/2) (cop₁ : (2:ℕ).Coprime (P/2)) (cop₂ : P.Coprime ell)
    (ep : 0<ell) (dp : 0<D) (lw : leading.size ≤ W) (dw : D.size ≤ W) (top : P+ell*P ≤ W)
    (nums : List ℤ)
    (fractions : ∀ j<d, (nums.getD j 0:ℚ)/D=(fromRoots ((targets d side).map ((A:ℚ)*·))).getD j 0)
    (width : ∀ j<d, ((localCoeffs d ell m leading side).getD j 0).natAbs.size ≤ W ∧
      (nums.getD j 0).natAbs.size ≤ W) :
    let L := localCoeffs d ell m leading side
    let out := preliminaryWord d.bits P.bits ell.bits leading.bits D.bits (binaryMask d).bits (L.map encode) (nums.map encode)
    out.1=(preliminary d A m P ell leading side).map encode ∧
      out.2 ≤ 30*(W+1)^2+d+2*d.size+3+d*(coefficientBudget P ell W+6) := by
  intro L out
  let fuel := tokens d.bits
  let step := natProduct P.bits ell.bits
  obtain ⟨fl,fc⟩ := token_spec d.bits
  change fuel.1.length=_ at fl
  change fuel.2 ≤ _ at fc
  simp only [value_bits,Nat.size_eq_bits_len] at fl fc
  have s (v : ℕ) : v.size ≤ v := Nat.size_le.mpr Nat.lt_two_pow_self
  have eP := Nat.le_mul_of_pos_right ell (show 0<P by omega)
  obtain ⟨sv,_,sc⟩ := natProduct_spec P ell ((s _).trans (by omega : P ≤ W)) ((s _).trans (by omega : ell ≤ W))
  change step.1=_ at sv
  change step.2 ≤ _ at sc
  obtain ⟨ev,ec⟩ := loop_spec two apos cop₁ cop₂ ep dp lw dw top (binaryMask d) L nums fuel.1 0 (by
    intro j hj; rw [fl,←List.range_eq_range'] at hj; exact width j (List.mem_range.mp hj))
  rw [fl,←List.range_eq_range'] at ev
  rw [fl] at ec
  simp only [List.drop_zero,decide_true] at ev ec
  change (loop P.bits ell.bits step.1 leading.bits D.bits fuel.1 (binaryMask d).bits true (L.map encode) (nums.map encode)).1=_ ∧
    step.2+fuel.2+(loop P.bits ell.bits step.1 leading.bits D.bits fuel.1 (binaryMask d).bits true (L.map encode) (nums.map encode)).2+2 ≤ _
  rw [sv,ev]
  refine ⟨?_,by omega⟩
  unfold preliminary
  rw [List.map_map]
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp_apply,coefficients,fractions j (List.mem_range.mp hj),L]

end Cogentic.BinaryPreliminary

#print axioms Cogentic.BinaryPreliminary.preliminaryWord_spec
