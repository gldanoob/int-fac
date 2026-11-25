import Cogentic.PerturbationCost
import Cogentic.ReconstructionCost
import Cogentic.IndexCapCost

namespace Cogentic.BinaryCorrectedBase
open BinaryDivision BinaryPivot BinarySaturation CandidateRuntime Construction

/-- Scan one arithmetic progression using restoring division. On a hit keep the
candidate and the quotient from that same division. -/
def scan (stride modulus wanted : List Bool) : List Unit → List Bool → Option (List Bool × List Bool) × ℕ
  | [], _ => (none,1)
  | _::rest, x =>
    let d := divide modulus x
    let eq := equalWords d.remainder wanted
    if eq.1 then
      let q := canonical d.quotient
      (some (x,q.1),d.gates+eq.2+q.2+2)
    else
      let add := addDigits (max x.length stride.length) x stride false
      let next := canonical add.1
      let restOut := scan stride modulus wanted rest next.1
      (restOut.1,d.gates+eq.2+add.2+next.2+restOut.2+2)

private def first (stride modulus wanted : ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | k+1, x => if x%modulus=wanted then some x else first stride modulus wanted k (x+stride)

private def pack (m x : ℕ) := (x.bits,(x/m).bits)

private theorem scan_spec (stride m r x W : ℕ) (ts : List Unit) (mp : 0 < m)
    (sw : stride.size ≤ W) (mw : m.size ≤ W) (rw' : r.size ≤ W)
    (room : (x+ts.length*stride).size ≤ W) :
    let out := scan stride.bits m.bits r.bits ts x.bits
    out.1=(first stride m r ts.length x).map (pack m) ∧
      out.2 ≤ 1+ts.length*(100*(W+1)^2) := by
  induction ts generalizing x with
  | nil => simp [scan,first]
  | cons t ts ih =>
    simp only [List.length_cons,Nat.succ_mul] at room
    have xw := (Nat.size_le_size (show x ≤ x+(ts.length*stride+stride) by omega)).trans room
    have room' : (x+stride+ts.length*stride).size ≤ W := by simpa only [Nat.add_assoc,Nat.add_comm stride (ts.length*stride)] using room
    let d := divide m.bits x.bits
    let test := equalWords d.remainder r.bits
    obtain ⟨qv,rv,dc⟩ := divide_naturals x m mp
    obtain ⟨width,len,_,_,_⟩ := divide_spec m.bits x.bits (by simpa)
    change value d.quotient=x/m at qv
    change value d.remainder=x%m at rv
    change d.gates ≤ _ at dc
    change d.width=_ at width
    change d.remainder.length ≤ d.width at len
    simp only [Nat.size_eq_bits_len] at width
    have divCost := dc.trans (Nat.mul_le_mul xw (show 10*(m.size+x.size)+1 ≤ 20*W+1 by omega))
    obtain ⟨eq,ec⟩ := equalWords_spec d.remainder r.bits
    change (test.1=true ↔ _) at eq
    change test.2=_ at ec
    rw [rv,value_bits] at eq
    rw [Nat.size_eq_bits_len] at ec
    have testCost : test.2 ≤ 28*W+3 := by omega
    change (scan stride.bits m.bits r.bits (t::ts) x.bits).1=_ ∧ _ ≤ _
    cases he : test.1 with
    | true =>
      have hit := eq.mp he
      have ql : d.quotient.length=x.size := (BinaryIndexCap.quotient_length ..).trans (Nat.size_eq_bits_len _)
      obtain ⟨qv',qc⟩ := canonical_spec d.quotient
      rw [qv] at qv'
      rw [ql] at qc
      change (equalWords (divide m.bits x.bits).remainder r.bits).1=true at he
      simp only [scan,he,List.length_cons,first,hit,Option.map_some,pack,↓reduceIte]
      change some (x.bits,(canonical d.quotient).1)=_ ∧ d.gates+test.2+(canonical d.quotient).2+2 ≤ _
      rw [qv',qc,Nat.succ_mul ts.length]
      exact ⟨rfl,by nlinarith only [testCost,divCost,xw,Nat.zero_le (ts.length*(100*(W+1)^2))]⟩
    | false =>
      have miss : x%m≠r := fun h=>by simpa [he] using eq.mpr h
      let a := addDigits (max x.bits.length stride.bits.length) x.bits stride.bits false
      let next := canonical a.1
      obtain ⟨al,ac,av⟩ := addDigits_spec (max x.bits.length stride.bits.length) x.bits stride.bits false
        (le_max_left ..) (le_max_right ..)
      change a.1.length=_ at al
      change a.2=_ at ac
      change value a.1=_ at av
      simp only [value_bits,Bool.toNat_false,Nat.add_zero] at av
      simp only [Nat.size_eq_bits_len] at al ac
      obtain ⟨nv,nc⟩ := canonical_spec a.1
      change next.1=_ at nv
      change next.2=_ at nc
      rw [av] at nv
      rw [al] at nc
      obtain ⟨tail,tc⟩ := ih (x+stride) room'
      change (equalWords (divide m.bits x.bits).remainder r.bits).1=false at he
      simp only [scan,he,Bool.false_eq_true,if_false,List.length_cons,first,miss]
      change (scan stride.bits m.bits r.bits ts next.1).1=_ ∧ d.gates+test.2+a.2+next.2+
        (scan stride.bits m.bits r.bits ts next.1).2+2 ≤ _
      rw [nv,ac,nc,Nat.succ_mul ts.length]
      exact ⟨tail,by nlinarith only [tc,divCost,testCost,show max x.size stride.size ≤ W from max_le xw sw]⟩

private theorem first_hits {stride m r z : ℕ} (k x : ℕ)
    (existsHit : ∃ j < k, z=x+j*stride ∧ z%m=r)
    (unique : ∀ j < k, (x+j*stride)%m=r → x+j*stride=z) : first stride m r k x=some z := by
  induction k generalizing x with
  | zero => obtain ⟨j,b,_⟩ := existsHit; omega
  | succ k ih =>
    by_cases h : x%m=r
    · have eq := unique 0 (Nat.succ_pos k) (by simpa using h)
      simpa [first,h] using eq
    · rw [first,if_neg h]; apply ih
      · obtain ⟨j,hj,hz,hr⟩ := existsHit
        cases j with
        | zero => simp_all
        | succ j => exact ⟨j,by omega,by rw [hz,Nat.succ_mul]; omega,hr⟩
      · intro j hj eq
        have : x+stride+j*stride=x+(j+1)*stride := by rw [Nat.succ_mul]; omega
        rw [this] at eq ⊢
        exact unique (j+1) (by omega) eq

/-- Inputs are already reduced residues. Scan m lifts of a by multiples of n.
The bound depends on m and the bit length of n, allowing n itself to be the
integer being factored. The quotient can be used directly for modular inversion. -/
def liftedCRT (n m a b : List Bool) : (List Bool × List Bool) × ℕ :=
  let fuel := tokens m
  let out := scan n m b fuel.1 a
  (out.1.getD ([],[]),fuel.2+out.2+1)

theorem liftedCRT_spec {n m a b W : ℕ} (co : n.Coprime m) (an : a < n) (bm : b < m)
    (width : (a+m*n).size ≤ W) (mw : m.size ≤ W) :
    let v := crt n m a b
    let out := liftedCRT n.bits m.bits a.bits b.bits
    out.1=(v.bits,(v/m).bits) ∧ out.2 ≤ m+2*m.size+2+m*(100*(W+1)^2) := by
  let z := (Nat.chineseRemainder co a b).val
  have np : 0 < n := by omega
  have mp : 0 < m := by omega
  have small : z < n*m := Nat.chineseRemainder_lt_mul co a b np.ne' mp.ne'
  obtain ⟨left,right⟩ := (Nat.chineseRemainder co a b).property
  change z%n=a%n at left
  change z%m=b%m at right
  rw [Nat.mod_eq_of_lt an] at left
  rw [Nat.mod_eq_of_lt bm] at right
  have existsHit : ∃ j < m, z=a+j*n ∧ z%m=b := by
    refine ⟨z/n,(Nat.div_lt_iff_lt_mul np).mpr (by rwa [Nat.mul_comm m n]),?_,right⟩
    rw [←left,Nat.mul_comm (z/n) n,Nat.mod_add_div]
  have unique (j : ℕ) (smallj : j < m) (hit : (a+j*n)%m=b) : a+j*n=z := by
    have h₁ : a+j*n ≡ a [MOD n] := Nat.add_mul_modulus_modEq_iff.mpr .rfl
    have h₂ : a+j*n ≡ b [MOD m] := by change _=b%m; rwa [Nat.mod_eq_of_lt bm]
    apply (Nat.chineseRemainder_modEq_unique co h₁ h₂).eq_of_lt_of_lt _ small
    calc a+j*n < n+j*n := Nat.add_lt_add_right an _
         _ = (j+1)*n := by ring
         _ ≤ n*m := by rw [Nat.mul_comm n m]; exact Nat.mul_le_mul_right n smallj
  have found := first_hits m a existsHit unique
  let fuel := tokens m.bits
  obtain ⟨fl,fc⟩ := token_spec m.bits
  change fuel.1.length=_ at fl
  change fuel.2 ≤ _ at fc
  simp only [value_bits,Nat.size_eq_bits_len] at fl fc
  have nn : n ≤ a+m*n := (Nat.le_mul_of_pos_left _ mp).trans (Nat.le_add_left ..)
  obtain ⟨v,c⟩ := scan_spec n m b a W fuel.1 mp ((Nat.size_le_size nn).trans width) mw
    ((Nat.size_le_size bm.le).trans mw) (by rwa [fl])
  rw [fl,found] at v
  rw [fl] at c
  change (scan n.bits m.bits b.bits fuel.1 a.bits).1.getD _=_ ∧ fuel.2+(scan n.bits m.bits b.bits fuel.1 a.bits).2+1 ≤ _
  rw [v]
  have eqz : crt n m a b=z := dif_pos co
  exact ⟨by rw [eqz]; rfl,by omega⟩


/-- The CRT lift divisible by `step`, divided by `step`, equals the exact
least nonnegative Bézout correction used by the constructor. -/
theorem quotient_eq_correction {n step : ℕ} (hn : 0 < n) (hs : 0 < step)
    (co : step.Coprime n) (y : ℤ) :
    crt n step (modulusResidue y n) 0 / step = correction step n y := by
  let r := modulusResidue y n
  let z := crt n step r 0
  let t := z/step
  have np : (0:ℤ) < n := by exact_mod_cast hn
  have rr : (r:ℤ)=y%(n:ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ np.ne')
  obtain ⟨hz,div⟩ := crt_spec co.symm r 0
  change z≡r [MOD n] at hz
  change z≡0 [MOD step] at div
  have mul : t*step=z := Nat.div_mul_cancel (Nat.modEq_zero_iff_dvd.mp div)
  have small : z < n*step := by
    dsimp only [z,crt]; rw [dif_pos co.symm]
    exact Nat.chineseRemainder_lt_mul co.symm _ _ hn.ne' hs.ne'
  have tn : t < n := (Nat.div_lt_iff_lt_mul hs).mpr small
  have hy : (r:ℤ)≡y [ZMOD n] := by change (r:ℤ)%(n:ℤ)=_; rw [rr,Int.emod_emod]
  have lifted := (Int.natCast_modEq_iff.mpr hz).trans hy
  have zm : (step:ℤ)*t=(z:ℤ) := by exact_mod_cast (Nat.mul_comm step t).trans mul
  rw [←zm] at lifted
  have bez := Nat.gcd_eq_gcd_ab step n
  rw [co.gcd_eq_one] at bez
  have inv : Nat.gcdA step n*(step:ℤ)≡1 [ZMOD n] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨Nat.gcdB step n,?_⟩
    linear_combination bez
  have id := (inv.mul_right (t:ℤ)).symm
  rw [one_mul,mul_assoc] at id
  have canonical := id.trans (lifted.mul_left (Nat.gcdA step n))
  change (t:ℤ)%(n:ℤ)=_ at canonical
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast tn)] at canonical
  exact (congrArg Int.toNat canonical : t=correction step n y)


/-- The signed Euclidean remainder, leaving the result in canonical binary form. -/
def signedResidue (z : SignedWord) (m : List Bool) : List Bool × ℕ :=
  let d := divide m z.digits
  let nz := BinaryReconstruction.below [] d.remainder
  let sub := subtract (max m.length d.remainder.length) m d.remainder false
  let out := canonical (if z.negative && nz.1 then sub.digits else d.remainder)
  (out.1,d.gates+nz.2+sub.gates+out.2+3)

theorem signedResidue_spec (z : ℤ) {m W : ℕ} (mp : 0 < m) (zw : z.natAbs.size ≤ W) (mw : m.size ≤ W) :
    (signedResidue (encode z) m.bits).1=(modulusResidue z m).bits ∧
    (signedResidue (encode z) m.bits).2 ≤ 100*(W+1)^2 := by
  let d := divide m.bits z.natAbs.bits
  let nz := BinaryReconstruction.below [] d.remainder
  let fix := decide (z < 0) && nz.1
  let sub := subtract (max m.bits.length d.remainder.length) m.bits d.remainder false
  let rem := if fix then sub.digits else d.remainder
  let out := canonical rem
  obtain ⟨_,val,cost⟩ := BinaryReconstruction.divmod_spec z m W mp zw mw
  change value out.1=modulusResidue z m at val
  have bits := (canonical_spec rem).1
  change out.1=_ at bits
  rw [bits,value_bits] at val
  let q := addDigits d.quotient.length d.quotient [] fix
  change d.gates+nz.2+q.2+sub.gates+(canonical q.1).2+out.2+3 ≤ _ at cost
  change out.1=_ ∧ d.gates+nz.2+sub.gates+out.2+3 ≤ _
  exact ⟨bits.trans (congrArg Nat.bits val),by omega⟩

/-- Lift the canonical signed residue by multiples of n. The fuel is the
constructor's smaller CRT step. -/
def correctionWord (n step : List Bool) (y : SignedWord) : List Bool × ℕ :=
  let d := signedResidue y n
  let lift := liftedCRT n step d.1 []
  (lift.1.2,d.2+lift.2+1)

theorem correctionWord_spec {n step W : ℕ} (hn : 0 < n) (hs : 0 < step)
    (co : step.Coprime n) (y : ℤ) (hw : y.natAbs.size ≤ W)
    (nw : n.size ≤ W) (sw : step.size ≤ W) (bound : (n+step*n).size ≤ W) :
    (correctionWord n.bits step.bits (encode y)).1=(correction step n y).bits ∧
    (correctionWord n.bits step.bits (encode y)).2 ≤ (step+1)*(100*(W+1)^2)+step+2*step.size+3 := by
  let r := modulusResidue y n
  have np : (0:ℤ) < n := by exact_mod_cast hn
  have rsmall : r < n := by
    change (y%(n:ℤ)).toNat < n
    have pos := Int.emod_nonneg y np.ne'
    have small := Int.emod_lt_of_pos y np
    omega
  obtain ⟨rem,cost⟩ := signedResidue_spec y hn hw nw
  change (signedResidue (encode y) n.bits).1=r.bits at rem
  obtain ⟨eq,work⟩ := liftedCRT_spec (a:=r) (b:=0) co.symm rsmall hs
    ((Nat.size_le_size (Nat.add_le_add_right rsmall.le (step*n))).trans bound) sw
  change (liftedCRT n.bits step.bits r.bits []).1=_ at eq
  change (liftedCRT n.bits step.bits r.bits []).2 ≤ _ at work
  dsimp only [correctionWord]
  rw [rem,eq]
  exact ⟨congrArg Nat.bits (quotient_eq_correction hn hs co y),by rw [Nat.succ_mul]; omega⟩

/-- Divide out one base-m digit, subtract its step multiple from the matching
coefficient, and retain the supplied leading coefficient at the end. -/
def lower (m step : List Bool) (leading : SignedWord) : List SignedWord → List Bool → List SignedWord × ℕ
  | [], _ => ([leading],1)
  | c::cs, t =>
    let d := divide m t
    let next := canonical d.quotient
    let digit := canonical d.remainder
    let prod := multiply step digit.1
    let val := BinaryPerturbation.adjust c prod.1 false
    let tail := lower m step leading cs next.1
    (val.1::tail.1,d.gates+next.2+digit.2+prod.2+val.2+tail.2+3)

theorem lower_spec (m step : ℕ) (leading : ℤ) (cs : List ℤ) (t W : ℕ)
    (mp : 0 < m) (mw : m.size ≤ W) (sw : step.size ≤ W) (tw : t.size ≤ W)
    (cw : ∀ z∈cs,z.natAbs.size ≤ W) :
    let out := lower m.bits step.bits (encode leading) (cs.map encode) t.bits
    out.1=((correctLower m step t cs)++[leading]).map encode ∧
    out.2 ≤ 1+cs.length*(200*(W+1)^2) := by
  induction cs generalizing t with
  | nil => simp [lower,correctLower]
  | cons c cs ih =>
    let d := divide m.bits t.bits
    let next := canonical d.quotient
    let digit := canonical d.remainder
    let prod := multiply step.bits digit.1
    let val := BinaryPerturbation.adjust (encode c) prod.1 false
    obtain ⟨qv,rv,dc⟩ := divide_naturals t m mp
    obtain ⟨width,rl,_,_,_⟩ := divide_spec m.bits t.bits (by simpa)
    change value d.quotient=t/m at qv
    change value d.remainder=t%m at rv
    change d.gates ≤ _ at dc
    change d.width=_ at width
    change d.remainder.length ≤ d.width at rl
    simp only [Nat.size_eq_bits_len] at width
    have ql : d.quotient.length=t.size := (BinaryIndexCap.quotient_length ..).trans (Nat.size_eq_bits_len _)
    obtain ⟨qb,qc⟩ := canonical_spec d.quotient
    obtain ⟨rb,rc⟩ := canonical_spec d.remainder
    change next.1=_ at qb
    change next.2=_ at qc
    change digit.1=_ at rb
    change digit.2=_ at rc
    rw [qv] at qb
    rw [rv] at rb
    rw [ql] at qc
    have rw' : digit.1.length ≤ W := by rw [rb,Nat.size_eq_bits_len]; exact (Nat.size_le_size (Nat.mod_lt t mp).le).trans mw
    have sw' : step.bits.length ≤ W := by rwa [Nat.size_eq_bits_len]
    obtain ⟨pv,pl,pc⟩ := multiply_spec step.bits digit.1
    change value prod.1=_ at pv
    change prod.1.length ≤ _ at pl
    change prod.2 ≤ _ at pc
    have mult := pc.trans (Nat.mul_le_mul rw' (show _ ≤ W+5*(W+2*W) by omega))
    rw [rb,value_bits,value_bits,Nat.mul_comm] at pv
    obtain ⟨av,_,ac⟩ := BinaryPerturbation.adjust_spec (encode c) prod.1 false
    change val.1=_ at av
    change val.2=_ at ac
    simp only [signed,Bool.false_eq_true,if_false,decode_encode,pv,Nat.cast_mul] at av
    have hc : (encode c).digits.length ≤ W := by simpa [encode,Nat.size_eq_bits_len] using cw c (by simp)
    have maxlen : max (encode c).digits.length prod.1.length ≤ 3*W := by omega
    have divCost := dc.trans (Nat.mul_le_mul tw (show 10*(m.size+t.size)+1 ≤ 20*W+1 by omega))
    obtain ⟨e,wc⟩ := ih (t/m) ((Nat.size_le_size (Nat.div_le_self t m)).trans tw)
      (fun z h=>cw z (by simp [h]))
    change val.1::(lower m.bits step.bits (encode leading) (cs.map encode) next.1).1=_ ∧
      d.gates+next.2+digit.2+prod.2+val.2+(lower m.bits step.bits (encode leading) (cs.map encode) next.1).2+3 ≤ _
    rw [qb,av,e,ac,List.length_cons,Nat.succ_mul cs.length]
    refine ⟨rfl,?_⟩
    nlinarith only [mult,divCost,maxlen,wc,qc,rc,rl,width,mw,tw]


/-- Given the preliminary coefficient words, evaluate at the exact common
root and apply every least-nonnegative correction digit. -/
def fromPreliminary (n m step lead : List Bool) (cs : List SignedWord) : List SignedWord × ℕ :=
  let leading := ⟨false,lead⟩
  let polynomial := cs++[leading]
  let evaluated := CandidateRuntime.horner m polynomial
  let y := BinaryPerturbation.adjust evaluated.1 [] false
  let t := correctionWord n step y.1
  let out := lower m step leading cs t.1
  (out.1,evaluated.2+y.2+t.2+out.2+2*cs.length+3)

def fieldBudget (len step W : ℕ) := (500*(len+1)+200*(step+1))*(W+1)^2

theorem fromPreliminary_spec {n m step lead h W : ℕ} (low : List ℤ)
    (hn : 0 < n) (hm : 0 < m) (hs : 0 < step) (co : step.Coprime n)
    (height : ∀ z∈low,z.natAbs.size ≤ h) (lw : lead.size ≤ h)
    (nw : n.size ≤ W) (mw : m.size ≤ W) (sw : step.size ≤ W) (limit : (n+step*n).size ≤ W)
    (room : h+(low.length+1)*(2*m.size+1) ≤ W) :
    let r := fromPreliminary n.bits m.bits step.bits lead.bits (low.map encode)
    r.1=(corrected n m step lead low).map encode ∧ r.2 ≤ fieldBudget low.length step W := by
  let cs := low++[(lead:ℤ)]
  let ev := CandidateRuntime.horner m.bits (cs.map encode)
  let y := eval (m:ℤ) cs
  let canon := BinaryPerturbation.adjust ev.1 [] false
  let t := correctionWord n.bits step.bits canon.1
  have hr : ∀ z∈cs,z.natAbs.size ≤ h := by
    intro z hz
    rcases List.mem_append.mp hz with hz|hz
    · exact height z hz
    · simpa only [List.mem_singleton.mp hz,Int.natAbs_natCast] using lw
  have len : cs.length=low.length+1 := by simp [cs]
  have room' : h+cs.length*(2*m.bits.length+1) ≤ W := by rwa [len,Nat.size_eq_bits_len]
  obtain ⟨ee,el,eg⟩ := CandidateRuntime.horner_spec m.bits cs h W hr (by rwa [Nat.size_eq_bits_len]) room'
  change ev.1.decode=_ at ee
  change ev.1.digits.length ≤ _ at el
  change ev.2 ≤ _ at eg
  have same (c : List ℤ) : (Marking.horner (m:ℤ) c).1=eval (m:ℤ) c := by
    induction c with
    | nil => rfl
    | cons a cs ih => simp [Marking.horner,eval,ih]
  rw [value_bits,same] at ee
  have elW := el.trans room'
  obtain ⟨cv,_,cg⟩ := BinaryPerturbation.adjust_spec ev.1 [] false
  change canon.1=_ at cv
  change canon.2=_ at cg
  simp only [value,signed,Bool.false_eq_true,if_false,Nat.cast_zero,sub_zero,ee] at cv
  simp only [List.length_nil,Nat.max_zero] at cg
  have abs : ev.1.decode.natAbs=value ev.1.digits := by
    cases e : ev.1 with | mk s ds => cases s <;> simp [SignedWord.decode,signed]
  change ev.1.decode=y at ee
  have yw : y.natAbs.size ≤ W := (show y.natAbs.size ≤ ev.1.digits.length by
    rw [←ee,abs]; exact Nat.size_le.mpr (value_lt _)).trans elW
  obtain ⟨tv,tc⟩ := correctionWord_spec hn hs co y yw nw sw limit
  change canon.1=encode y at cv
  rw [←cv] at tv tc
  change t.1=_ at tv
  change t.2 ≤ _ at tc
  have np : (0:ℤ) < n := by exact_mod_cast hn
  have tsmall : correction step n y < n := by
    unfold correction modulusResidue
    have := Int.emod_nonneg (Nat.gcdA step n*y) np.ne'
    have := Int.emod_lt_of_pos (Nat.gcdA step n*y) np
    omega
  have hw : h ≤ W := by omega
  obtain ⟨lv,lc⟩ := lower_spec m step (lead:ℤ) low (correction step n y) W hm mw sw
    ((Nat.size_le_size tsmall.le).trans nw) (fun z hz=>(height z hz).trans hw)
  have leq : (⟨false,lead.bits⟩:SignedWord)=encode (lead:ℤ) := by simp [encode]
  have poly : low.map encode++[encode (lead:ℤ)]=cs.map encode := by simp [cs]
  dsimp only [fromPreliminary]
  rw [leq,poly]
  change (lower m.bits step.bits (encode (lead:ℤ)) (low.map encode) t.1).1=_ ∧
    ev.2+canon.2+t.2+(lower m.bits step.bits (encode (lead:ℤ)) (low.map encode) t.1).2+2*(low.map encode).length+3 ≤ _
  rw [tv,List.length_map,cg]
  rw [len] at eg
  refine ⟨lv,?_⟩
  unfold evalStep at eg
  unfold fieldBudget
  have sw' : step.size ≤ step := Nat.size_le.mpr Nat.lt_two_pow_self
  nlinarith only [eg,elW,tc,lc,sw',Nat.zero_le (W*step),Nat.zero_le (W*low.length)]


/-- Compute the common CRT step once and correct both polynomial lists. -/
def pairFromPreliminary (n m P ell leading : List Bool) (left right : List SignedWord) :
    (List SignedWord × List SignedWord) × ℕ :=
  let prod := multiply P ell
  let step := canonical prod.1
  let l := fromPreliminary n m step.1 leading left
  let r := fromPreliminary n m step.1 leading right
  ((l.1,r.1),prod.2+step.2+l.2+r.2+1)

def preliminaryBase (n ell : ℕ) (side : Bool) : List ℤ :=
  let b := n.log2+1
  preliminary (Fixed.d b) (Fixed.A b) (Fixed.rootBase n) (primorial (Fixed.d b)) ell (leadingCoefficient n) side

/-- Both fields of the actual target constructor, through signed Horner,
modular correction and base-m digits, given the preliminary coefficient words. -/
theorem fixed_from_preliminary {n ell : ℕ} (hn : 2 ≤ n) (comp : ¬n.Prime)
    (target : ell∈dyadicTargets (Fixed.beta (n.log2+1)))
    (sieved : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none) :
    let b := n.log2+1
    let out := pairFromPreliminary n.bits (Fixed.rootBase n).bits (primorial (Fixed.d b)).bits ell.bits
      (leadingCoefficient n).bits ((preliminaryBase n ell false).map encode) ((preliminaryBase n ell true).map encode)
    out.1=(((BinaryPerturbation.correctedBase n ell false).map encode),
      ((BinaryPerturbation.correctedBase n ell true).map encode)) ∧
    out.2 ≤ 2^(610000*TwoThirdsCost.scale b) := by
  intro b out
  let d := Fixed.d b
  let S := TwoThirdsCost.scale b
  let P := primorial d
  let m := Fixed.rootBase n
  let A := Fixed.A b
  let c := leadingCoefficient n
  let step := P*ell
  let X := 2^(121125*S)
  let W := 10*(X+1)^2
  have bp : 0 < b := Nat.succ_pos _
  have dp := Fixed.degree_pos bp
  have zp : 0 < Fixed.z b := Nat.succ_pos _
  have ds : d ≤ Fixed.h b := Nat.le_mul_of_pos_right _ zp
  have hvs : Fixed.h b ≤ Fixed.v b := Nat.le_mul_of_pos_left _ dp
  have vs : Fixed.v b ≤ S := (Fixed.scale_bounds bp).1
  have hs := hvs.trans vs
  have zs : Fixed.z b ≤ S := (Nat.le_mul_of_pos_left _ dp).trans hs
  have sp : 0 < S := zp.trans_le zs
  have db := Fixed.degree_le_bits b
  have mp : 0 < m := by simp [m,Fixed.rootBase]
  have pp := primorial_pos d
  have ep := (mem_dyadicTargets.mp target).1.pos
  have stp : 0 < step := Nat.mul_pos pp ep
  have within {k l : ℕ} (h : k ≤ l) : 2^(k*S) ≤ 2^(l*S) := Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_right S h)
  have pmax : P ≤ 2^(2*S) := (primorial_le_four_pow _).trans (by
    change (2^2)^d ≤ _; rw [←pow_mul]; exact Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
  have emax : ell ≤ 2^(1000*S) := (mem_dyadicTargets.mp target).2.2.trans
    (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_left 1000 hs))
  have stmax : step ≤ 2^(1002*S) := (Nat.mul_le_mul pmax emax).trans_eq (by rw [←pow_add]; congr 1; ring)
  have xs : step ≤ X := stmax.trans (within (by decide))
  have xp : P ≤ X := pmax.trans (within (by decide))
  have xe : ell ≤ X := emax.trans (within (by decide))
  have b1 : b+1 ≤ 2^S := Nat.succ_le_of_lt (Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two zs))
  have xb : b+1 ≤ X := b1.trans (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
  have cn : c ≤ 2^(111120*S) := (leading_size hn).trans (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_left _ vs))
  have Ap : 0 < A := Nat.two_pow_pos _
  have am : (1+A)^d ≤ 2^(10001*S) := calc
    _ ≤ (2*A)^d := Nat.pow_le_pow_left (by omega) _
    _ = 2^((1+10000*Fixed.h b)*d) := by
      conv_rhs => rw [pow_mul,pow_add,pow_one]
      rfl
    _ ≤ _ := by
      apply Nat.pow_le_pow_right Nat.zero_lt_two
      have hd : Fixed.h b*d=Fixed.v b := Nat.mul_comm ..
      rw [Nat.add_mul,Nat.mul_assoc,hd,one_mul]; omega
  have coeff : c*(1+A)^d + step ≤ X := by
    have prod := Nat.mul_le_mul cn am
    rw [←pow_add,show 111120*S+10001*S=121121*S by ring] at prod
    have st := stmax.trans (within (by decide : 1002 ≤ 121121))
    exact (Nat.add_le_add prod st).trans (calc
      _ = 2^(1+121121*S) := by rw [pow_add,pow_one,two_mul]
      _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
  have sizeSelf (v : ℕ) : v.size ≤ v := Nat.size_le.mpr Nat.lt_two_pow_self
  have sizeC : c.size ≤ X := (sizeSelf _).trans (cn.trans (within (by decide)))
  have nw : n.size ≤ X := (Nat.size_le.mpr Nat.lt_log2_self).trans (by omega : b ≤ X)
  have mw : m.size ≤ X := (Nat.size_le.mpr ((Fixed.rootBase_spec hn).2.2.trans_lt
    (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self b)))).trans xb
  have xw : X ≤ W := by dsimp only [W]; nlinarith only [Nat.zero_le (X^2)]
  have top : (n+step*n).size ≤ W := by
    have npos := Nat.two_pow_pos n.size
    have nn := Nat.lt_size_self n
    have cc := Nat.lt_size_self step
    have bnd : n+step*n < 2^(step.size+n.size) := by
      rw [pow_add]
      calc n+step*n=(step+1)*n := by ring
           _ < (step+1)*2^n.size := Nat.mul_lt_mul_of_pos_left nn (Nat.succ_pos _)
           _ ≤ _ := Nat.mul_le_mul_right _ cc
    have sw := (sizeSelf step).trans xs
    exact (Nat.size_le.mpr bnd).trans (by unfold W; nlinarith only [sw,nw,Nat.zero_le (X^2)])
  have dw : d ≤ X := db.trans (by omega)
  have len (side) : (preliminaryBase n ell side).length=d := by simp [preliminaryBase,preliminary,d,b]
  have budget (side) := fromPreliminary_spec (preliminaryBase n ell side) (show 0 < n by omega) mp stp
    (surviving_coprime hn comp target sieved) (h:=X) (W:=W)
    (fun z hz=> (sizeSelf _).trans ((preliminary_height stp side hz).trans coeff)) sizeC (nw.trans xw)
    (mw.trans xw) ((sizeSelf _).trans (xs.trans xw)) top (by
      rw [len]; unfold W; nlinarith only [Nat.mul_le_mul (Nat.succ_le_succ dw) (show 2*m.size+1 ≤ 2*X+1 by omega),Nat.zero_le (X^2)])
  let prod := multiply P.bits ell.bits
  let sb := canonical prod.1
  obtain ⟨pv,pl,pc⟩ := multiply_spec P.bits ell.bits
  change value prod.1=_ at pv
  change prod.1.length ≤ _ at pl
  change prod.2 ≤ _ at pc
  obtain ⟨bits,bc⟩ := canonical_spec prod.1
  change sb.1=_ at bits
  change sb.2=_ at bc
  rw [pv,value_bits,value_bits,Nat.mul_comm ell P] at bits
  change sb.1=step.bits at bits
  have pb : P.bits.length ≤ X := (Nat.size_eq_bits_len P).le.trans ((sizeSelf _).trans xp)
  have eb : ell.bits.length ≤ X := (Nat.size_eq_bits_len ell).le.trans ((sizeSelf _).trans xe)
  have mult := pc.trans (Nat.mul_le_mul eb (show _ ≤ X+5*(X+2*X) by omega))
  obtain ⟨le,lc⟩ := budget false
  obtain ⟨re,rc⟩ := budget true
  rw [len] at lc rc
  change ((fromPreliminary n.bits m.bits sb.1 c.bits _).1,(fromPreliminary n.bits m.bits sb.1 c.bits _).1)=_ ∧
    prod.2+sb.2+(fromPreliminary n.bits m.bits sb.1 c.bits _).2+(fromPreliminary n.bits m.bits sb.1 c.bits _).2+1 ≤ _
  rw [bits,le,re,bc]
  refine ⟨rfl,?_⟩
  have budgetCap : fieldBudget d step W ≤ 100000*(X+1)^5 := by
    calc fieldBudget d step W ≤ (500*(X+1)+200*(X+1))*(10*(X+1)^2+1)^2 := by unfold fieldBudget; gcongr
         _ ≤ _ := by nlinarith only [Nat.zero_le (X^5),Nat.zero_le (X^4),Nat.zero_le (X^3),Nat.zero_le (X^2),Nat.zero_le X]
  have lc' := lc.trans budgetCap
  have rc' := rc.trans budgetCap
  have main : prod.2+3*prod.1.length+
      (fromPreliminary n.bits m.bits step.bits c.bits ((preliminaryBase n ell false).map encode)).2+
      (fromPreliminary n.bits m.bits step.bits c.bits ((preliminaryBase n ell true).map encode)).2+1 ≤ 2^18*(X+1)^5 := by
    nlinarith only [lc',rc',mult,pl,pb,eb,Nat.zero_le (X^5),Nat.zero_le (X^4),Nat.zero_le (X^3),Nat.zero_le (X^2),Nat.zero_le X]
  have xx : X+1 ≤ 2^(121126*S) := calc
    X+1 ≤ X+X := Nat.add_le_add_left Nat.one_le_two_pow _
    _ = 2^(1+121125*S) := by rw [pow_add,pow_one,two_mul]
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  refine main.trans ((Nat.mul_le_mul_left (2^18) (Nat.pow_le_pow_left xx 5)).trans ?_)
  rw [←pow_mul,←pow_add]
  exact Nat.pow_le_pow_right Nat.zero_lt_two (by omega)

end Cogentic.BinaryCorrectedBase

#print axioms Cogentic.BinaryCorrectedBase.fixed_from_preliminary
