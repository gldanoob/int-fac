import Cogentic.CandidateRuntime
import Cogentic.ConstructionCofactors
import Cogentic.CandidateSieveCost

namespace Cogentic.CandidateMarks
open BinaryDivision BinaryPivot CandidateRuntime Construction

structure Info where
  length : List Bool
  lastOk : Bool
  heightOk : Bool
  gates : ℕ

/-- In one pass check the height of every coefficient, track the exact binary
coefficient count, and check the sign and magnitude of the leading coefficient. -/
def inspect (leading cap : List Bool) : List SignedWord → Info
  | [] => ⟨[],false,true,1⟩
  | c::cs =>
    let tail := inspect leading cap cs
    let count := addDigits tail.length.length tail.length [] true
    let same := equalWords c.digits leading
    let small := leq c.digits cap
    let last := if cs.isEmpty then !c.negative && same.1 else tail.lastOk
    ⟨count.1,last,small.1 && tail.heightOk,tail.gates+count.2+same.2+small.2+4⟩

private theorem inspect_spec (leading cap : List Bool) (cs : List ℤ) (w : ℕ)
    (wl : leading.length≤w) (wc : cap.length≤w) (len : cs.length≤w)
    (widths : ∀ c ∈ cs,c.natAbs.size≤w) :
    let z := inspect leading cap (cs.map encode)
    value z.length = cs.length ∧ z.length.length = cs.length ∧
    (z.lastOk=true ↔ cs.getLast? = some (value leading :ℤ)) ∧
    (z.heightOk=true ↔ ∀ c ∈ cs, c.natAbs≤value cap) ∧ z.gates≤1+cs.length*(26*w+8) := by
  induction cs with
  | nil => simp [inspect,value]
  | cons c cs ih =>
    let tail := inspect leading cap (cs.map encode)
    let e := encode c
    have ec : e.digits.length≤w := by simpa [e,encode,Nat.size_eq_bits_len] using widths c (by simp)
    have clen : cs.length≤w := (Nat.le_succ cs.length).trans len
    obtain ⟨v,l,last,high,k⟩ := ih clen (fun c hc=>widths c (by simp [hc]))
    change value tail.length=_ at v
    change tail.length.length=_ at l
    change tail.lastOk=true ↔ _ at last
    change tail.heightOk=true ↔ _ at high
    change tail.gates≤_ at k
    obtain ⟨nl,nc,nv⟩ := addDigits_spec tail.length.length tail.length [] true le_rfl (by simp)
    obtain ⟨ev,ex⟩ := equalWords_spec e.digits leading
    obtain ⟨sv,sx⟩ := leq_spec e.digits cap
    have eq : ((!e.negative && (equalWords e.digits leading).1)=true) ↔ c=(value leading :ℤ) := by
      rw [Bool.and_eq_true,ev]
      simp [e,encode]
      omega
    have sm : (leq e.digits cap).1 = true ↔ c.natAbs≤value cap := by
      simpa [e,encode] using sv
    have exw := max_le ec wl
    have sxw := max_le ec wc
    change value (addDigits tail.length.length tail.length [] true).1=_ ∧
      (addDigits tail.length.length tail.length [] true).1.length=_ ∧
      ((if (cs.map encode).isEmpty then !e.negative && (equalWords e.digits leading).1 else tail.lastOk)=true ↔ _) ∧
      (((leq e.digits cap).1 && tail.heightOk)=true ↔ _) ∧
      tail.gates+_+_+_+4≤_
    refine ⟨by simp [nv,v,value],by rw [nl,l,List.length_cons],?_,?_,?_⟩
    · cases cs with
      | nil => simpa using eq
      | cons d ds => simpa using last
    · simp only [Bool.and_eq_true,sm,high,List.forall_mem_cons]
    · rw [ex,sx,nc,List.length_cons,Nat.succ_mul cs.length]; omega

private def powWord (k : List Unit) : List Bool := k.foldr (fun _ xs => false::xs) [true]

private theorem powWord_spec (k : List Unit) :
    value (powWord k)=2^k.length ∧ (powWord k).length=k.length+1 := by
  induction k with
  | nil => decide
  | cons i xs ih => change value (false::powWord xs)=_ ∧ (false::powWord xs).length=_
                    simp [value,ih,pow_succ,Nat.mul_comm]

/-- Check all four conditions in the stage-one polynomial guard directly on
binary coefficients and integer parameters. -/
def polynomial (n m degree leading height : List Bool) (coeffs : List SignedWord) : Bool × ℕ :=
  let ts := BinarySaturation.tokens height
  let cap := powWord ts.1
  let info := inspect leading cap coeffs
  let degree1 := addDigits degree.length degree [] true
  let count := equalWords info.length degree1.1
  let atBase := norm m coeffs
  let zero := residueEq atBase.1 n []
  (count.1 && info.lastOk && info.heightOk && zero.1,
    ts.2+ts.1.length+1+info.gates+degree1.2+count.2+atBase.2+zero.2+3)

def polyBudget (L d w : ℕ) :=
  L+2*w+L+1+(1+d*(26*w+8))+5*w+(14*w+17)+(1+d*evalStep w+3*w)+(w*(20*w+1)+28*w+4)+3

theorem polynomial_spec (s : Marking.Input) (cs : List ℤ) (h w : ℕ) (pos : 0 < s.n)
    (nw : s.n.size≤w) (mw : s.m.size≤w) (dw : s.degree.size≤w) (lw : s.leading.size≤w)
    (hw : s.L₀+1≤w) (cw : cs.length≤w) (coefficients : ∀ c ∈ cs,c.natAbs.size≤h)
    (room : h+cs.length*(2*s.m.size+1)≤w) :
    let out := polynomial s.n.bits s.m.bits s.degree.bits s.leading.bits s.L₀.bits (cs.map encode)
    (out.1=true ↔ s.polynomialGuard cs) ∧ out.2≤polyBudget s.L₀ cs.length w := by
  let ts := BinarySaturation.tokens s.L₀.bits
  have ⟨tl,tc⟩ := BinarySaturation.token_spec s.L₀.bits
  change ts.1.length=_ at tl
  change ts.2≤_ at tc
  simp only [value_bits,Nat.size_eq_bits_len] at tl tc
  let cap := powWord ts.1
  have ⟨cv,cl⟩ := powWord_spec ts.1
  change value cap=_ at cv
  change cap.length=_ at cl
  rw [tl] at cv cl
  let info := inspect s.leading.bits cap (cs.map encode)
  have ⟨mv,ml,me,mh,mc⟩ := inspect_spec s.leading.bits cap cs w (by simpa [Nat.size_eq_bits_len] using lw)
    (cl ▸ hw) cw (fun c hc=>(coefficients c hc).trans (by omega))
  change value info.length=_ at mv
  change info.length.length=_ at ml
  change info.lastOk=true ↔ _ at me
  change info.heightOk=true ↔ _ at mh
  change info.gates≤_ at mc
  let d1 := addDigits s.degree.bits.length s.degree.bits [] true
  have ⟨dl,dc,dv⟩ := addDigits_spec s.degree.bits.length s.degree.bits [] true le_rfl (by simp)
  change d1.1.length=_ at dl
  change d1.2=_ at dc
  change value d1.1=_ at dv
  simp only [Nat.size_eq_bits_len,value_bits,value,Nat.add_zero,Bool.toNat_true] at dl dc dv
  have ⟨eq,ec⟩ := equalWords_spec info.length d1.1
  let eval := norm s.m.bits (cs.map encode)
  obtain ⟨ev,ew⟩ := norm_spec s.m cs h w coefficients mw room
  change eval.1=_ at ev
  change eval.2≤_ at ew
  have len := norm_length s.m cs h w coefficients mw room
  have ⟨zero,zc⟩ := residue_spec eval.1 s.n.bits [] (by simpa using pos) w len
    (by simpa [Nat.size_eq_bits_len] using nw) (by simp)
  have modular := (Marking.zero_at_mark cs s.m s.n).1
  rw [ZMod.natCast_mod] at modular
  conv at zero => rhs; rw [ev]; simp only [value_bits,value,←Nat.dvd_iff_mod_eq_zero]
  rw [mv,dv] at eq; rw [value_bits] at me; rw [cv] at mh
  change (((equalWords info.length d1.1).1 && info.lastOk && info.heightOk && (residueEq eval.1 s.n.bits []).1)=true ↔ _) ∧
    ts.2+ts.1.length+1+info.gates+d1.2+(equalWords info.length d1.1).2+eval.2+(residueEq eval.1 s.n.bits []).2+3≤_
  constructor
  · simp only [Bool.and_eq_true,eq,me,mh,zero,←modular,Marking.Input.polynomialGuard,and_assoc]
    rfl
  · have lim : max info.length.length d1.1.length ≤ w+1 := by omega
    have small := (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=s.L₀))).trans (by omega : s.L₀≤w)
    rw [dc,ec,tl]; unfold polyBudget; omega

private def plus (x y : List Bool) := addDigits (max x.length y.length) x y false

private theorem plus_spec (x y : List Bool) :
    value (plus x y).1 = value x+value y ∧ (plus x y).1.length=max x.length y.length+1 ∧
    (plus x y).2=5*max x.length y.length := by
  obtain ⟨l,c,v⟩ := addDigits_spec (max x.length y.length) x y false (le_max_left ..) (le_max_right ..)
  exact ⟨by simpa [plus] using v,l,c⟩

/-- Test the closed rational interval by cross multiplication in the naturals.
The initial grid interval has offset zero and every root interval has offset one. -/
def window (p d A w a : List Bool) (offset : Bool) : Bool × ℕ :=
  let pw := multiply p w
  let dw := multiply d w
  let l := plus pw.1 (if offset then d else [])
  let u := plus l.1 d
  let left := multiply l.1 A
  let mid := multiply dw.1 a
  let right := multiply u.1 A
  let low := leq left.1 mid.1
  let high := leq mid.1 right.1
  (low.1 && high.1,pw.2+dw.2+l.2+u.2+left.2+mid.2+right.2+low.2+high.2+2)

private theorem window_spec (p d A w a : List Bool) (o : Bool) (W : ℕ)
    (pw : p.length≤W) (dw : d.length≤W) (Aw : A.length≤W) (ww : w.length≤W) (aw : a.length≤W) (pos : 0<W) :
    let low := value p*value w+o.toNat*value d
    let x := value a*(value d*value w)
    ((window p d A w a o).1=true ↔ value A*low ≤ x ∧ x ≤ value A*(low+value d)) ∧
    (window p d A w a o).2 ≤ 200*W^2+200*W+4 := by
  let pW := multiply p w
  let dW := multiply d w
  let extra := if o then d else []
  let l := plus pW.1 extra
  let u := plus l.1 d
  have ⟨pv,pl,pc⟩ := multiply_spec p w
  have ⟨dv,dl,dc⟩ := multiply_spec d w
  change value pW.1=_ at pv
  change pW.1.length≤_ at pl
  change pW.2≤_ at pc
  change value dW.1=_ at dv
  change dW.1.length≤_ at dl
  change dW.2≤_ at dc
  have e : value extra=o.toNat*value d ∧ extra.length≤W := by cases o <;> simp [extra,value,dw]
  have ⟨lv,ll,lc⟩ := plus_spec pW.1 extra
  have ⟨uv,ul,uc⟩ := plus_spec l.1 d
  change value l.1=_ at lv
  change value u.1=_ at uv
  change l.1.length=_ at ll
  change u.1.length=_ at ul
  change l.2=_ at lc
  change u.2=_ at uc
  let left := multiply l.1 A
  let mid := multiply dW.1 a
  let right := multiply u.1 A
  have ⟨av,al,ac⟩ := multiply_spec l.1 A
  have ⟨bv,bl,bc⟩ := multiply_spec dW.1 a
  have ⟨cv,cl,cc⟩ := multiply_spec u.1 A
  change value left.1=_ at av
  change value mid.1=_ at bv
  change value right.1=_ at cv
  change left.1.length≤_ at al
  change mid.1.length≤_ at bl
  change right.1.length≤_ at cl
  change left.2≤_ at ac
  change mid.2≤_ at bc
  change right.2≤_ at cc
  have ⟨lo,lowCost⟩ := leq_spec left.1 mid.1
  have ⟨hi,hiCost⟩ := leq_spec mid.1 right.1
  constructor
  · change (((leq left.1 mid.1).1 && (leq mid.1 right.1).1)=true ↔ _)
    rw [Bool.and_eq_true,lo,hi,av,bv,cv,lv,uv,lv,pv,dv,e.1]
    simp only [Nat.mul_comm (value w)]
  · have l4 : l.1.length≤4*W := by omega
    have u5 : u.1.length≤5*W := by omega
    have d3 : dW.1.length≤3*W := by omega
    have c₁ := pc.trans (Nat.mul_le_mul ww (show _ ≤ W+5*(W+2*W) by omega))
    have c₂ := dc.trans (Nat.mul_le_mul ww (show _ ≤ W+5*(W+2*W) by omega))
    have c₃ := ac.trans (Nat.mul_le_mul Aw (show _ ≤ 4*W+5*(4*W+2*W) by omega))
    have c₄ := bc.trans (Nat.mul_le_mul aw (show _ ≤ 3*W+5*(3*W+2*W) by omega))
    have c₅ := cc.trans (Nat.mul_le_mul Aw (show _ ≤ 5*W+5*(5*W+2*W) by omega))
    change pW.2+dW.2+l.2+u.2+left.2+mid.2+right.2+(leq left.1 mid.1).2+(leq mid.1 right.1).2+2≤_
    rw [lc,uc,lowCost,hiCost]
    have m₁ : max pW.1.length extra.length ≤ 3*W := by omega
    have m₂ : max l.1.length d.length ≤ 4*W := by omega
    have m₃ : max left.1.length mid.1.length ≤ 6*W := by omega
    have m₄ : max mid.1.length right.1.length ≤ 7*W := by omega
    nlinarith only [c₁,c₂,c₃,c₄,c₅,m₁,m₂,m₃,m₄]

private theorem window_rational (p d A w a : ℕ) (o : Bool) (dp : 0<d) (Ap : 0<A) (wp : 0<w) :
    let y := (p:ℚ)/d + (o.toNat:ℚ)/w
    ((a:ℚ)/A ∈ Set.Icc y (y+(w:ℚ)⁻¹)) ↔
      A*(p*w+o.toNat*d) ≤ a*(d*w) ∧ a*(d*w) ≤ A*(p*w+o.toNat*d+d) := by
  have D : (0:ℚ)<d := by exact_mod_cast dp
  have P : (0:ℚ)<A := by exact_mod_cast Ap
  have W : (0:ℚ)<w := by exact_mod_cast wp
  simp only [Set.mem_Icc]
  constructor
  · rintro ⟨l,h⟩
    field_simp [D,W,P] at l h
    constructor
    · exact_mod_cast (by linarith only [l] : (A:ℚ)*((p:ℚ)*w+o.toNat*d) ≤ a*(d*w))
    · exact_mod_cast (by linarith only [h] : (a:ℚ)*(d*w) ≤ A*(p*w+o.toNat*d+d))
  · rintro ⟨l,h⟩
    have l' : (A:ℚ)*((p:ℚ)*w+o.toNat*d) ≤ a*(d*w) := by exact_mod_cast l
    have h' : (a:ℚ)*(d*w) ≤ A*((p:ℚ)*w+o.toNat*d+d) := by exact_mod_cast h
    constructor <;> field_simp [D,W,P] <;> linarith

private def interval (p d A w a : ℕ) (o : Bool) : Prop :=
  A*(p*w+o.toNat*d) ≤ a*(d*w) ∧ a*(d*w) ≤ A*(p*w+o.toNat*d+d)

def windowBudget (w : ℕ) := 200*w^2+205*w+7

/-- Scan the integer numerators of one family of roots, advancing by two in
binary. The two families start at one and two. -/
def sweep (den A width a : List Bool) : List Unit → List Bool → Bool × ℕ
  | [], _ => (false,1)
  | _::rest, p =>
    let check := window p den A width a true
    if check.1 then (true,check.2+1) else
      let q := addDigits (max 2 p.length) p [false,true] false
      let tail := sweep den A width a rest q.1
      (tail.1,check.2+q.2+tail.2+2)

private theorem sweep_spec (den A wid a : List Bool) (ts : List Unit) (p : List Bool) (W : ℕ)
    (room : p.length+3*ts.length≤W) (tw : 2≤W)
    (dd : den.length≤W) (aa : A.length≤W) (ww : wid.length≤W) (aw : a.length≤W) :
    ((sweep den A wid a ts p).1=true ↔ ∃ j<ts.length,
      interval (value p+2*j) (value den) (value A) (value wid) (value a) true) ∧
    (sweep den A wid a ts p).2≤1+ts.length*windowBudget W := by
  induction ts generalizing p with
  | nil => simp [sweep]
  | cons t ts ih =>
    have pw : p.length≤W := by omega
    have ⟨v,c⟩ := window_spec p den A wid a true W pw dd aa ww aw (by omega)
    change (window p den A wid a true).1=true ↔ interval _ _ _ _ _ true at v
    let q := addDigits (max 2 p.length) p [false,true] false
    obtain ⟨ql,qc,qv⟩ := addDigits_spec (max 2 p.length) p [false,true] false (le_max_right ..) (le_max_left ..)
    change q.1.length=_ at ql
    change q.2=_ at qc
    change value q.1=_ at qv
    simp only [value,Bool.toNat_false,Bool.toNat_true,Nat.mul_zero,Nat.add_zero,Nat.zero_add,Nat.mul_one] at qv
    simp only [List.length_cons] at room ⊢
    have ⟨tv,tc⟩ := ih q.1 (by omega)
    change (sweep den A wid a ts q.1).2≤_ at tc
    have splitting : (∃ j<ts.length+1, interval (value p+2*j) (value den) (value A) (value wid) (value a) true) ↔
        interval (value p) (value den) (value A) (value wid) (value a) true ∨
        ∃ j<ts.length, interval (value q.1+2*j) (value den) (value A) (value wid) (value a) true := by
      constructor
      · rintro ⟨j,hj,h⟩
        cases j with
        | zero => exact Or.inl (by simpa using h)
        | succ j => exact Or.inr ⟨j,by omega,by rwa [show value q.1+2*j=value p+2*(j+1) by omega]⟩
      · rintro (h|⟨j,hj,h⟩)
        · exact ⟨0,by omega,by simpa using h⟩
        · exact ⟨j+1,by omega,by rwa [show value p+2*(j+1)=value q.1+2*j by omega]⟩
    rw [splitting,←v,←tv]
    cases h : (window p den A wid a true).1 <;> simp only [sweep,h,if_true,Bool.false_eq_true,if_false,
      true_or,false_or,iff_self,true_and,Nat.succ_mul ts.length]
    · refine ⟨Iff.rfl,?_⟩
      change _+q.2+(sweep den A wid a ts q.1).2+2≤_
      have step : (window p den A wid a true).2+q.2+2≤windowBudget W := by
        rw [qc]; unfold windowBudget; linarith only [c, max_le tw pw]
      linarith only [step,tc]
    · have step : (window p den A wid a true).2+1≤windowBudget W := by unfold windowBudget; linarith only [c]
      exact step.trans (by omega)

def grid (degree A wid a : List Bool) : Bool × ℕ :=
  let main := window [true,true] [false,false,true] A wid a false
  let d4 := false::false::degree
  let ts := BinarySaturation.tokens degree
  let odds := sweep d4 A wid a ts.1 [true]
  let evens := sweep d4 A wid a ts.1 [false,true]
  (main.1 || odds.1 || evens.1,main.2+ts.2+odds.2+evens.2+4)

private theorem grid_intervals (d A w a : ℕ) (dp : 0<d) (Ap : 0<A) (wp : 0<w) :
    onGrid d A w a=true ↔ interval 3 4 A w a false ∨
      (∃ j<d,interval (1+2*j) (4*d) A w a true) ∨ (∃ j<d,interval (2+2*j) (4*d) A w a true) := by
  have main := window_rational 3 4 A w a false (by decide) Ap wp
  have roots (p : ℕ) := window_rational p (4*d) A w a true (by positivity) Ap wp
  simp only [Set.mem_Icc,Bool.toNat_false,Bool.toNat_true,Nat.cast_zero,zero_div,add_zero,
    Nat.cast_one,one_div,Nat.zero_mul,Nat.one_mul] at main roots
  simp only [onGrid,targets,List.any_append,List.any_map,Bool.or_eq_true,List.any_eq_true,
    List.mem_range,Function.comp_apply,decide_eq_true_eq,Bool.false_eq_true,if_false,if_true]
  simp only [interval,Bool.toNat_true,Bool.toNat_false,Nat.one_mul,Nat.zero_mul,add_zero,
    ←main]
  have eq (p : ℕ) : (A*(p*w+4*d)≤a*(4*d*w) ∧ a*(4*d*w)≤A*(p*w+4*d+4*d)) ↔
      (p:ℚ)/(4*d)+(w:ℚ)⁻¹ ≤ (a:ℚ)/A ∧ (a:ℚ)/A ≤ (p:ℚ)/(4*d)+2*(w:ℚ)⁻¹ := by
    push_cast at roots
    simpa only [add_assoc,←two_mul] using (roots p).symm
  simp_rw [eq]
  push_cast
  simp [add_comm]

theorem grid_spec (d A w a W : ℕ) (dp : 0<d) (Ap : 0<A) (wp : 0<w)
    (cap : 3+3*d+d.size≤W) (aw : A.size≤W) (ww : w.size≤W) (ma : a.size≤W) :
    (grid d.bits A.bits w.bits a.bits).1=onGrid d A w a ∧
    (grid d.bits A.bits w.bits a.bits).2≤(2*d+1)*windowBudget W+d+2*d.size+6 := by
  let d4 := false::false::d.bits
  let ts := BinarySaturation.tokens d.bits
  obtain ⟨tl,tc⟩ := BinarySaturation.token_spec d.bits
  change ts.1.length=_ at tl
  change ts.2≤_ at tc
  simp only [value_bits,Nat.size_eq_bits_len] at tl tc
  have d4len : d4.length≤W := by simp [d4,Nat.size_eq_bits_len]; omega
  have d4val : value d4=4*d := by simp [d4,value]; omega
  have main := window_spec [true,true] [false,false,true] A.bits w.bits a.bits false W
    (by change 2≤W; omega) (by change 3≤W; omega) (by simpa [Nat.size_eq_bits_len] using aw)
    (by simpa [Nat.size_eq_bits_len] using ww) (by simpa [Nat.size_eq_bits_len] using ma) (by omega)
  have sweepRun (p : List Bool) (hp : p.length≤2) := sweep_spec d4 A.bits w.bits a.bits ts.1 p W
    (by rw [tl]; omega) (by omega) d4len (by simpa [Nat.size_eq_bits_len] using aw)
    (by simpa [Nat.size_eq_bits_len] using ww) (by simpa [Nat.size_eq_bits_len] using ma)
  obtain ⟨odd,oc⟩ := sweepRun [true] (by decide)
  obtain ⟨even,ec⟩ := sweepRun [false,true] (by decide)
  rw [tl] at odd even oc ec
  obtain ⟨mv,mc⟩ := main
  change (window [true,true] [false,false,true] A.bits w.bits a.bits false).1=true ↔
    interval 3 4 (value A.bits) (value w.bits) (value a.bits) false at mv
  rw [d4val] at odd even
  simp only [value_bits] at mv odd even
  refine ⟨Bool.eq_iff_iff.mpr ?_,?_⟩
  · change (((window [true,true] [false,false,true] A.bits w.bits a.bits false).1 ||
      (sweep d4 A.bits w.bits a.bits ts.1 [true]).1 || (sweep d4 A.bits w.bits a.bits ts.1 [false,true]).1)=true ↔ _)
    rw [Bool.or_eq_true,Bool.or_eq_true,mv,odd,even,grid_intervals d A w a dp Ap wp]
    simp [value,or_assoc]
  · change _+ts.2+(sweep d4 A.bits w.bits a.bits ts.1 [true]).2+(sweep d4 A.bits w.bits a.bits ts.1 [false,true]).2+4≤_
    rw [Nat.succ_mul (2*d),Nat.mul_assoc]
    unfold windowBudget at *; omega

def coprime (x y : List Bool) : Bool × ℕ :=
  let g := BinaryModularPower.gcdBits x y
  let e := equalWords g.1 [true]
  (e.1,g.2+e.2)

private theorem coprime_spec (x y : List Bool) (w : ℕ) (xp : x.length≤w) (yp : y.length≤w) (pos : 0<w) :
    ((coprime x y).1=true ↔ (value x).Coprime (value y)) ∧
    (coprime x y).2≤BinaryModularPower.gcdBudget w+14*w+3 := by
  obtain ⟨v,l,c⟩ := BinaryModularPower.gcdBits_spec x y w xp yp
  have count := (Elimination.gcdWithCount_le (value x) (value y)).trans
    (Nat.mul_le_mul_left 2 ((Nat.size_le.mpr (value_lt x)).trans xp))
  have work := c.trans (show _ ≤ BinaryModularPower.gcdBudget w by unfold BinaryModularPower.gcdBudget; gcongr)
  obtain ⟨eq,cost⟩ := equalWords_spec (BinaryModularPower.gcdBits x y).1 [true]
  refine ⟨by simpa [coprime,v,value,Nat.Coprime] using eq,?_⟩
  change _+(equalWords (BinaryModularPower.gcdBits x y).1 [true]).2≤_
  rw [cost]; simp only [List.length_cons,List.length_nil] at *; omega

def mark (d A wid m k n : List Bool) (elig : Bool) (a : List Bool) : Bool × ℕ :=
  let on := grid d A wid a
  let z := BinaryPresieve.gap m a
  let co := coprime z.1 k
  let unit := coprime z.1 n
  (on.1 && co.1 && (!elig || unit.1),on.2+z.2+co.2+unit.2+3)

def scanBudget (d w : ℕ) :=
  (2*d+1)*windowBudget w+d+2*w+6+17*w+1+2*(BinaryModularPower.gcdBudget w+14*w+3)+3

private theorem mark_spec (d A wid m k n a w : ℕ) (elig : Bool)
    (dp : 0<d) (ap : 0<A) (wp : 0<wid) (cap : 3+3*d+d.size≤w)
    (Afit : A.size≤w) (wfit : wid.size≤w) (mfit : m.size≤w) (kfit : k.size≤w)
    (nfit : n.size≤w) (afit : a.size≤w) :
    let z := ((a:ℤ)-m).natAbs
    (mark d.bits A.bits wid.bits m.bits k.bits n.bits elig a.bits).1 =
      (onGrid d A wid a && decide (z.Coprime k) && (!elig || decide (z.Coprime n))) ∧
    (mark d.bits A.bits wid.bits m.bits k.bits n.bits elig a.bits).2 ≤ scanBudget d w := by
  obtain ⟨gv,gc⟩ := grid_spec d A wid a w dp ap wp cap Afit wfit afit
  let z := BinaryPresieve.gap m.bits a.bits
  obtain ⟨zv,zl,zc⟩ := BinaryPresieve.gap_spec m.bits a.bits
  change value z.1=_ at zv
  change z.1.length=_ at zl
  change z.2=_ at zc
  simp only [Nat.size_eq_bits_len,value_bits] at zv zl zc
  have zw : z.1.length≤w := zl ▸ (max_le mfit afit)
  obtain ⟨kv,kc⟩ := coprime_spec z.1 k.bits w zw (by simpa [Nat.size_eq_bits_len] using kfit) (by omega)
  obtain ⟨nv,nc⟩ := coprime_spec z.1 n.bits w zw (by simpa [Nat.size_eq_bits_len] using nfit) (by omega)
  rw [zv,value_bits] at kv nv
  have ke := Bool.eq_iff_iff.mpr (kv.trans decide_eq_true_iff.symm)
  have ne := Bool.eq_iff_iff.mpr (nv.trans decide_eq_true_iff.symm)
  refine ⟨?_,?_⟩
  · change ((grid d.bits A.bits wid.bits a.bits).1 && (coprime z.1 k.bits).1 && (!elig || (coprime z.1 n.bits).1))=_
    rw [gv,ke,ne]
  · change (grid d.bits A.bits wid.bits a.bits).2+z.2+(coprime z.1 k.bits).2+(coprime z.1 n.bits).2+3≤_
    rw [zc]; unfold scanBudget; omega

/-- The scan retains canonical binary marks. The counter is incremented and
trimmed even when the grid or either coprimality check rejects a mark. -/
def visit (test : List Bool→Bool × ℕ) : List Unit → List Bool → List (List Bool) × ℕ
  | [], _ => ([],1)
  | _::rest, a =>
    let inc := addDigits a.length a [] true
    let next := BinarySaturation.canonical inc.1
    let hit := test next.1
    let tail := visit test rest next.1
    (if hit.1 then next.1::tail.1 else tail.1,inc.2+next.2+hit.2+tail.2+2)

private theorem visit_spec (test : List Bool→Bool × ℕ) (pred : ℕ→Bool) (M w work : ℕ)
    (checks : ∀ a≤M, (test a.bits).1=pred a ∧ (test a.bits).2≤work)
    (mw : M.size≤w) (ts : List Unit) (start : ℕ) (room : start+ts.length≤M) :
    (visit test ts start.bits).1.map value=(List.range' (start+1) ts.length).filter pred ∧
    (visit test ts start.bits).2≤1+ts.length*(8*w+work+5) := by
  induction ts generalizing start with
  | nil => simp [visit]
  | cons i rest ih =>
    let inc := addDigits start.bits.length start.bits [] true
    let next := BinarySaturation.canonical inc.1
    obtain ⟨il,ic,iv⟩ := addDigits_spec start.bits.length start.bits [] true le_rfl (by simp)
    change inc.1.length=_ at il
    change inc.2=_ at ic
    change value inc.1=_ at iv
    simp only [value_bits,value,Nat.add_zero,Bool.toNat_true] at iv
    obtain ⟨nv,nc⟩ := BinarySaturation.canonical_spec inc.1
    change next.1=_ at nv
    change next.2=_ at nc
    rw [iv] at nv
    rw [il] at nc
    simp only [Nat.size_eq_bits_len] at ic nc
    simp only [List.length_cons] at room ⊢
    have sw := (Nat.size_le_size (by omega : start≤M)).trans mw
    have ⟨ev,ec⟩ := checks (start+1) (by omega)
    obtain ⟨rv,rc⟩ := ih (start+1) (by omega)
    change (if (test next.1).1 then next.1::(visit test rest next.1).1 else (visit test rest next.1).1).map value= _ ∧
      inc.2+next.2+(test next.1).2+(visit test rest next.1).2+2 ≤ _
    rw [nv,ev,List.range'_succ,List.filter_cons]
    constructor
    · cases p : pred (start+1) <;> simp [rv]
    · rw [Nat.succ_mul rest.length]; omega

def enumerate (d A wid m k n : ℕ) (elig : Bool) : List (List Bool) × ℕ :=
  let ts := BinarySaturation.tokens A.bits
  let scan := visit (mark d.bits A.bits wid.bits m.bits k.bits n.bits elig) ts.1 []
  (scan.1,ts.2+scan.2+1)

def allBudget (d A w : ℕ) := A+2*w+2+A*(8*w+scanBudget d w+5)

theorem enumerate_spec (d A wid m k n w : ℕ) (elig : Bool)
    (dp : 0<d) (ap : 0<A) (wp : 0<wid) (cap : 3+3*d+d.size≤w)
    (afit : A.size≤w) (wfit : wid.size≤w) (mfit : m.size≤w) (kfit : k.size≤w) (nfit : n.size≤w) :
    (enumerate d A wid m k n elig).1.map value =
      (List.range' 1 A).filter (fun a =>
        onGrid d A wid a && decide (((a:ℤ)-m).natAbs.Coprime k) &&
          (!elig || decide (((a:ℤ)-m).natAbs.Coprime n))) ∧
    (enumerate d A wid m k n elig).2≤allBudget d A w := by
  let ts := BinarySaturation.tokens A.bits
  obtain ⟨tl,tc⟩ := BinarySaturation.token_spec A.bits
  change ts.1.length=_ at tl
  change ts.2≤_ at tc
  simp only [value_bits,Nat.size_eq_bits_len] at tl tc
  obtain ⟨v,c⟩ := visit_spec _ _ A w (scanBudget d w) (fun a ha =>
    mark_spec d A wid m k n a w elig dp ap wp cap afit wfit mfit kfit nfit ((Nat.size_le_size ha).trans afit))
    afit ts.1 0 (by omega)
  rw [tl] at v c
  refine ⟨v,?_⟩
  change ts.2+_+1≤allBudget d A w
  unfold allBudget; simpa only [Nat.zero_bits] using (by omega : ts.2+
    (visit (mark d.bits A.bits wid.bits m.bits k.bits n.bits elig) ts.1 (0:ℕ).bits).2+1≤_)

def constructedMarks (n ell : ℕ) (eligible : Bool) : List (List Bool) × ℕ :=
  let b := n.log2+1
  enumerate (Fixed.d b) (Fixed.A b) (Fixed.invWidth b) (Fixed.rootBase n) (markModulus n ell) n eligible

private theorem sameList (n ell u v x y : ℕ) (elig : Bool) :
    let b := n.log2+1
    let s := TryPair.fixedInput n ell (construct n ell u v x y)
    (List.range' 1 (Fixed.A b)).filter (fun a => onGrid (Fixed.d b) (Fixed.A b) (Fixed.invWidth b) a &&
      decide (((a:ℤ)-Fixed.rootBase n).natAbs.Coprime (markModulus n ell)) &&
      (!elig || decide (((a:ℤ)-Fixed.rootBase n).natAbs.Coprime n))) =
      if elig then s.eligibleMarks else s.marks := by
  intro b s
  cases elig with
  | false =>
    simp only [Bool.not_false,Bool.true_or,Bool.and_true,Bool.false_eq_true,if_false]
    simp [s,TryPair.fixedInput,construct,b,markModulus,perturb_at_base]
  | true =>
    simp only [Bool.not_true,Bool.false_or,if_true]
    let pred := fun a => onGrid (Fixed.d b) (Fixed.A b) (Fixed.invWidth b) a &&
      decide (((a:ℤ)-Fixed.rootBase n).natAbs.Coprime (markModulus n ell)) &&
      decide (((a:ℤ)-Fixed.rootBase n).natAbs.Coprime n)
    let xs := (List.range' 1 (Fixed.A b)).filter pred
    let f := s.marks.toFinset.filter (fun a => 1≤a ∧ a ≤ s.A ∧ ((a:ℤ)-s.m).natAbs.Coprime s.n)
    have sets : xs.toFinset=f := by
      ext a
      simp only [xs,pred,List.mem_toFinset,List.mem_filter,List.mem_range'_1,Bool.and_eq_true,
        decide_eq_true_eq,f,Finset.mem_filter]
      change _ ↔ a ∈ (construct n ell u v x y).marks ∧ 1≤a ∧ a≤Fixed.A b ∧ _
      rw [constructed_marks_iff]
      change _ ↔ (1≤a ∧ a≤Fixed.A b ∧ _ ∧ _) ∧ 1≤a ∧ a≤Fixed.A b ∧ ((a:ℤ)-Fixed.rootBase n).natAbs.Coprime n
      dsimp only [b]
      constructor <;> rintro ⟨h₁,h₂⟩ <;> (split_ands <;> (first | omega | tauto))
    change xs=f.sort
    rw [←sets]
    exact ((List.toFinset_sort _ ((List.nodup_range' ..).filter _)).mpr
      ((List.pairwise_le_range' (s:=1) (n:=Fixed.A b) 1).filter _)).symm

private theorem fixedWork (n ell : ℕ) (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1))
    (comp : ¬n.Prime) (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none) :
    let b := n.log2+1
    let t := TwoThirdsCost.scale b
    let W := 1048576*2^(10000*t)
    3+3*Fixed.d b+(Fixed.d b).size≤W ∧ (Fixed.A b).size≤W ∧ (Fixed.invWidth b).size≤W ∧
      (Fixed.rootBase n).size≤W ∧ (markModulus n ell).size≤W ∧ n.size≤W ∧
      allBudget (Fixed.d b) (Fixed.A b) W ≤ 2^(40100*t) := by
  intro b t W
  let X := 2^(10000*t)
  have dp := Fixed.degree_pos (Nat.succ_pos n.log2)
  have vt := (Fixed.scale_bounds (Nat.succ_pos n.log2)).1
  have h : Fixed.h b≤t := (Nat.le_mul_of_pos_left _ dp).trans vt
  have z : b.log2+1≤t := (Nat.le_mul_of_pos_left _ dp).trans h
  have tx : t≤X := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have bx : b≤X := Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have xp : 0<X := Nat.two_pow_pos _
  have t0 : 0<t := by omega
  have wx : X≤W := Nat.le_mul_of_pos_left _ (by decide : 0<1048576)
  have dX := (Fixed.degree_le_bits b).trans bx
  have asX : Fixed.A b≤X := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 10000 h)
  have aw := (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=Fixed.A b))).trans asX
  have wi : Fixed.invWidth b≤X := Nat.pow_le_pow_right (by decide) (show 3*Fixed.h b≤10000*t by omega)
  have iw := (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=Fixed.invWidth b))).trans wi
  have dw := (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=Fixed.d b))).trans dX
  have nw : n.size≤b := Nat.size_le.mpr Nat.lt_log2_self
  have mw : (Fixed.rootBase n).size≤b+1 := Nat.size_le.mpr ((Fixed.rootBase_spec hn).2.2.trans_lt
    (Nat.pow_lt_pow_right (by decide : 1<2) (Nat.lt_succ_self b)))
  have ks := (markModulus_spec hn big comp target absent).2.1
  have ls := leading_size hn
  have kc : (markModulus n ell).size ≤ (1+111120*Fixed.v b)*2 := by
    apply Nat.size_le.mpr
    refine ks.trans_le ((Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 ls) 2).trans ?_)
    rw [show 2*2^(111120*Fixed.v b)=2^(1+111120*Fixed.v b) by rw [pow_add,pow_one],←pow_mul]
  have wp : 0<W := xp.trans_le wx
  have eq : W=1048576*X := rfl
  have vt' : Fixed.v b≤t := vt
  refine ⟨by omega,aw.trans wx,iw.trans wx,by omega,by omega,nw.trans (bx.trans wx),?_⟩
  have mono : allBudget (Fixed.d b) (Fixed.A b) W ≤ allBudget W W W := by
    unfold allBudget scanBudget; gcongr <;> omega
  calc _ ≤ allBudget W W W := mono
       _ ≤ 16384*W^4 := by
        unfold allBudget scanBudget windowBudget BinaryModularPower.gcdBudget
        have h0 := Nat.one_le_pow 4 W wp
        have h1 := Nat.le_self_pow (by decide : 4≠0) W
        have h2 := Nat.pow_le_pow_right wp (by decide : 2≤4)
        have h3 := Nat.pow_le_pow_right wp (by decide : 3≤4)
        nlinarith only [h0,h1,h2,h3]
       _ ≤ 2^(40100*t) := by
        change 2^14*(2^20*2^(10000*t))^4≤_
        rw [←pow_add,←pow_mul,←pow_add]
        exact Nat.pow_le_pow_right (by decide) (by omega)

/-- The constructor and stage-one mark lists are both obtained in increasing
order from binary inputs. Set conversion and sorting can be omitted. -/
theorem fixed_constructed_marks {n ell : ℕ} (u v x y : ℕ) (elig : Bool)
    (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none) :
    let s := TryPair.fixedInput n ell (construct n ell u v x y)
    (constructedMarks n ell elig).1.map value = (if elig then s.eligibleMarks else s.marks) ∧
    (constructedMarks n ell elig).2 ≤ 2^(40100*TwoThirdsCost.scale (n.log2+1)) := by
  let b := n.log2+1
  let w := 1048576*2^(10000*TwoThirdsCost.scale b)
  obtain ⟨room,aw,ww,mw,kw,nw,cost⟩ := fixedWork n ell hn big comp target absent
  obtain ⟨eq,c⟩ := enumerate_spec (Fixed.d b) (Fixed.A b) (Fixed.invWidth b) (Fixed.rootBase n)
    (markModulus n ell) n w elig (Fixed.degree_pos (Nat.succ_pos _)) (Nat.two_pow_pos _) (Nat.two_pow_pos _)
    room aw ww mw kw nw
  exact ⟨eq.trans (sameList n ell u v x y elig), c.trans cost⟩

private theorem visit_canonical (t : List Bool→Bool × ℕ) (ts : List Unit) (a : List Bool) :
    ∀ p ∈ (visit t ts a).1, p=(value p).bits := by
  induction ts generalizing a with
  | nil => simp [visit]
  | cons i xs ih =>
    let q := (BinarySaturation.canonical (addDigits a.length a [] true).1).1
    have eq := (BinarySaturation.canonical_spec (addDigits a.length a [] true).1).1
    change q=_ at eq
    intro p hp
    change p ∈ (if (t q).1 then q::(visit t xs q).1 else (visit t xs q).1) at hp
    split at hp
    · rcases List.mem_cons.mp hp with rfl|h
      · rw [eq,value_bits]
      · exact ih q p h
    · exact ih q p hp

private theorem wireScreen {α : Type*} (emit : α→ℕ) (t : α→Bool × ℕ) (u : ℕ→Bool × ℕ)
    (as : List α) (same : ∀ a ∈ as, t a = u (emit a)) :
    let o := screenWith t as
    (o.1.map emit,o.2) = screenWith u (as.map emit) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have m := same a (by simp)
    have tail := ih (fun a ha=>same a (by simp [ha]))
    have vals := congrArg Prod.fst tail
    have cost := congrArg Prod.snd tail
    change (screenWith t as).1.map emit=_ at vals
    change (screenWith t as).2=_ at cost
    simp only [List.map_cons,screenWith,m,cost]
    cases (u (emit a)).1 <;> simp [vals]

structure WireRelations where
  rows : List Marking.Row
  marks : List (List Bool)
  target : ℕ

def WireRelations.decode (s : WireRelations) : Marking.Relations :=
  ⟨s.rows,s.marks.map value,s.target⟩

/-- The produced binary marks flow directly into the two signed Horner
evaluations and the smoothness scan. Decoding is used in the specification. -/
def solveMarks (n ell u v x y : ℕ) : WireRelations × ℕ :=
  let s := TryPair.fixedInput n ell (construct n ell u v x y)
  let marks := constructedMarks n ell true
  let rows := prepareRows s
  let t := markWord (s.first.map encode) (s.second.map encode) s.L₀.bits (s.base.map Nat.bits)
    (rows.bad.map (fun r => (r.q.bits,r.r.bits)))
  let result := screenWith t marks.1
  (⟨rows.clean,result.1,s.target⟩,marks.2+rows.gates+result.2+1)

theorem fixed_mark_stage {n ell u v x y : ℕ} (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1))
    (comp : ¬n.Prime) (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    {rel : Marking.Relations} (ok : Marking.stageOne (TryPair.fixedInput n ell (construct n ell u v x y))=some rel) :
    (solveMarks n ell u v x y).1.decode = rel ∧
    (solveMarks n ell u v x y).2 ≤ 2^(90026*TwoThirdsCost.scale (n.log2+1)) := by
  let b := n.log2+1
  let z := TwoThirdsCost.scale b
  let s := TryPair.fixedInput n ell (construct n ell u v x y)
  let marks := constructedMarks n ell true
  let rows := prepareRows s
  let t := markWord (s.first.map encode) (s.second.map encode) s.L₀.bits (s.base.map Nat.bits)
    (rows.bad.map (fun r => (r.q.bits,r.r.bits)))
  let natT (a : ℕ) := t a.bits
  obtain ⟨mv,mc⟩ := fixed_constructed_marks u v x y true hn big comp target absent
  change marks.1.map value=s.eligibleMarks at mv
  change marks.2≤2^(40100*z) at mc
  have canonical : ∀ p∈marks.1, p=(value p).bits := fun p hp => visit_canonical _ _ _ p hp
  have same := wireScreen value t natT marks.1 (fun a ha=>congrArg t (canonical a ha))
  rw [mv] at same
  obtain ⟨rs,rc⟩ := fixed_rows_and_marks ok
  change Marking.Relations.mk rows.clean (screenWith natT s.eligibleMarks).1 s.target = rel at rs
  change rows.gates+(screenWith natT s.eligibleMarks).2+1≤2^(90024*z) at rc
  have v' := congrArg Prod.fst same
  have c' := congrArg Prod.snd same
  change (screenWith t marks.1).1.map value=_ at v'
  change (screenWith t marks.1).2=_ at c'
  change Marking.Relations.mk rows.clean ((screenWith t marks.1).1.map value) s.target = rel ∧
    marks.2+rows.gates+(screenWith t marks.1).2+1≤2^(90026*z)
  rw [v',c']
  refine ⟨rs,?_⟩
  have d := Fixed.degree_pos (Nat.succ_pos n.log2)
  have pos : 0<z := (Nat.mul_pos d (Nat.succ_pos _)).trans_le
    ((Nat.le_mul_of_pos_left _ d).trans (Fixed.scale_bounds (Nat.succ_pos n.log2)).1)
  have mc' := mc.trans (Nat.pow_le_pow_right (by decide : 0<2) (show 40100*z≤90024*z by omega))
  calc _ ≤ 2^(90024*z+1) := by rw [pow_succ]; omega
       _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

def fieldChecks (s : Marking.Input) : Bool × ℕ :=
  let check := polynomial s.n.bits s.m.bits s.degree.bits s.leading.bits s.L₀.bits
  let l := check (s.first.map encode)
  let r := check (s.second.map encode)
  (l.1 && r.1,l.2+r.2+1)

private theorem fixed_field_width (n : ℕ) (hn : 2≤n) :
    let b := n.log2+1
    let w := 1048576*(2^(10000*TwoThirdsCost.scale b))^2
    n.size≤w ∧ (Fixed.rootBase n).size≤w ∧ (Fixed.d b).size≤w ∧ (leadingCoefficient n).size≤w ∧
      b+1≤w ∧ Fixed.d b+1≤w ∧ b+1+(Fixed.d b+1)*(2*(Fixed.rootBase n).size+1)≤w ∧
      2*polyBudget b (Fixed.d b+1) w+1≤2^(60070*TwoThirdsCost.scale b) := by
  intro b w
  let t := TwoThirdsCost.scale b
  let X := 2^(10000*t)
  have d := Fixed.degree_pos (Nat.succ_pos n.log2)
  have vt := (Fixed.scale_bounds (Nat.succ_pos n.log2)).1
  have ht : Fixed.h b≤t := (Nat.le_mul_of_pos_left _ d).trans vt
  have z : b.log2+1≤t := (Nat.le_mul_of_pos_left _ d).trans ht
  have tx : t≤X := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have bx : b≤X := Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have dx := (Fixed.degree_le_bits b).trans bx
  have ds := (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=Fixed.d b))).trans dx
  have m : (Fixed.rootBase n).size≤b+1 := Nat.size_le.mpr ((Fixed.rootBase_spec hn).2.2.trans_lt
    (Nat.pow_lt_pow_right (by decide : 1<2) (Nat.lt_succ_self b)))
  have ns : n.size≤b := Nat.size_le.mpr Nat.lt_log2_self
  have ls := Nat.size_le_size (leading_size hn)
  rw [Nat.size_pow] at ls
  change (leadingCoefficient n).size≤111120*Fixed.v b+1 at ls
  have xp : 0<X := Nat.two_pow_pos _
  have sq := Nat.le_self_pow (by decide : 2≠0) X
  have we : w=1048576*X^2 := rfl
  have bound := Nat.mul_le_mul (show Fixed.d b+1≤2*X by omega) (show 2*(Fixed.rootBase n).size+1≤5*X by omega)
  have vert : Fixed.v b≤t := vt
  have room : b+1+(Fixed.d b+1)*(2*(Fixed.rootBase n).size+1)≤w := by
    rw [we]; nlinarith only [bound,sq,xp,bx]
  have bb : b≤w := by omega
  have dd : Fixed.d b+1≤w := by omega
  refine ⟨by omega,by omega,by omega,by omega,by omega,dd,room,?_⟩
  have mono : polyBudget b (Fixed.d b+1) w ≤ polyBudget w w w := by unfold polyBudget; gcongr
  have wp : 0<w := by omega
  calc _ ≤ 2*polyBudget w w w+1 := by gcongr
       _ ≤ 1024*w^3 := by
         unfold polyBudget evalStep
         have h0 := Nat.one_le_pow 3 w wp
         have h1 := Nat.le_self_pow (by decide : 3≠0) w
         have h2 := Nat.pow_le_pow_right wp (by decide : 2≤3)
         nlinarith only [h0,h1,h2]
       _ ≤ 2^(60070*t) := by
         change 2^10*(2^20*(2^(10000*t))^2)^3≤_
         rw [←pow_mul,←pow_add,←pow_mul,←pow_add]
         exact Nat.pow_le_pow_right (by decide) (by omega)

private theorem fields_of_guards {n ell u v x y : ℕ} (hn : 2≤n)
    (guards : let s := TryPair.fixedInput n ell (construct n ell u v x y)
      s.polynomialGuard s.first ∧ s.polynomialGuard s.second) :
    let b := n.log2+1
    let s := TryPair.fixedInput n ell (construct n ell u v x y)
    (fieldChecks s).1=true ∧ (fieldChecks s).2≤2^(60070*TwoThirdsCost.scale b) := by
  intro b s
  let w := 1048576*(2^(10000*TwoThirdsCost.scale b))^2
  obtain ⟨nw,mw,dw,lw,hw,cw,room,cap⟩ := fixed_field_width n hn
  have checks {cs : List ℤ} (g : s.polynomialGuard cs) :
      let z := polynomial s.n.bits s.m.bits s.degree.bits s.leading.bits s.L₀.bits (cs.map encode)
      z.1=true ∧ z.2≤polyBudget b (Fixed.d b+1) w := by
    have len : cs.length=Fixed.d b+1 := g.1
    obtain ⟨e,c⟩ := polynomial_spec s cs (b+1) w (by change 0<n; omega) nw mw dw lw hw (len ▸ cw)
      (fun t ht => Nat.size_le.mpr ((g.2.2.1 t ht).trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self b))))
      (by rw [len]; exact room)
    rw [len] at c
    exact ⟨e.mpr g,c⟩
  obtain ⟨v₁,c₁⟩ := checks guards.1
  obtain ⟨v₂,c₂⟩ := checks guards.2
  let test := polynomial s.n.bits s.m.bits s.degree.bits s.leading.bits s.L₀.bits
  change ((test (s.first.map encode)).1 && (test (s.second.map encode)).1)=true ∧
    (test (s.first.map encode)).2+(test (s.second.map encode)).2+1≤_
  refine ⟨by rw [Bool.and_eq_true]; exact ⟨v₁,v₂⟩,?_⟩
  exact (Nat.add_le_add_right (Nat.add_le_add c₁ c₂) 1).trans (by simpa [two_mul] using cap)

/-- Evaluate the polynomial guards and stream the binary eligible marks to the
row and smoothness computation on the large surviving branch. -/
def checkedStage (n ell u v x y : ℕ) : Option WireRelations × ℕ :=
  let s := TryPair.fixedInput n ell (construct n ell u v x y)
  let checked := fieldChecks s
  if checked.1 then
    let out := solveMarks n ell u v x y
    (some out.1,checked.2+out.2+1)
  else (none,checked.2+1)

/-- On every point of the actual search box, this stage computes the complete
relation record. The supplied data are the constructed polynomials, schedule,
factor base, residue enumeration and cofactor product. The guard, grid,
coprimality, classifications, and both field-norm filters are accounted for. -/
theorem fixed_checked_stage {n ell u v x y : ℕ} (hn : 2≤n) (big : 130000≤Fixed.d (n.log2+1))
    (comp : ¬n.Prime) (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (box : let b := n.log2+1
      u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b ∧
      x≤2*b^2*Fixed.U b*Fixed.A b ∧ y≤2*b^2*Fixed.U b) :
    let s := TryPair.fixedInput n ell (construct n ell u v x y)
    let out := checkedStage n ell u v x y
    out.1.map WireRelations.decode = Marking.stageOne s ∧ out.2≤2^(90028*TwoThirdsCost.scale (n.log2+1)) := by
  let s := TryPair.fixedInput n ell (construct n ell u v x y)
  let t := TwoThirdsCost.scale (n.log2+1)
  obtain ⟨rel,ok⟩ := stageOne_succeeds hn big comp target absent box
  obtain ⟨field,fc⟩ := fields_of_guards hn (box_polynomialGuards hn big comp target absent box)
  obtain ⟨vals,sc⟩ := fixed_mark_stage hn (by omega) comp target absent ok
  change (fieldChecks s).1=true at field
  change (fieldChecks s).2≤2^(60070*t) at fc
  change (checkedStage n ell u v x y).1.map WireRelations.decode=Marking.stageOne s ∧ _≤2^(90028*t)
  change Marking.stageOne s=some rel at ok
  have produced : checkedStage n ell u v x y =
      (some (solveMarks n ell u v x y).1,(fieldChecks s).2+(solveMarks n ell u v x y).2+1) := by
    dsimp only [s] at field ⊢
    simp only [checkedStage,field,if_true]
  rw [produced,ok]
  have d := Fixed.degree_pos (Nat.succ_pos n.log2)
  have pos : 0<t := (Nat.mul_pos d (Nat.succ_pos _)).trans_le
    ((Nat.le_mul_of_pos_left _ d).trans (Fixed.scale_bounds (Nat.succ_pos n.log2)).1)
  have fc' := fc.trans (Nat.pow_le_pow_right (by decide : 0<2) (show 60070*t≤90026*t by omega))
  change (solveMarks n ell u v x y).2≤2^(90026*t) at sc
  change _ ∧ (fieldChecks s).2+(solveMarks n ell u v x y).2+1≤2^(90028*t)
  refine ⟨congrArg some vals,?_⟩
  have p := Nat.two_pow_pos (90026*t)
  calc _ ≤ 2^(90026*t+2) := by rw [pow_add _ _ 2]; norm_num; omega
       _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

/-- On a surviving composite, the factor-base guard retains every raw prime
in its original order. All such primes exceed the degree, and trial division
has excluded every factor of the modulus up to B. -/
theorem constructed_base_eq {n : ℕ} (ell u v x y : ℕ) (hn : 2≤n)
    (big : 3≤Fixed.d (n.log2+1)) (comp : ¬n.Prime)
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none) :
    let p := construct n ell u v x y
    (TryPair.fixedInput n ell p).base = p.factorBase := by
  let p := construct n ell u v x y
  let b := n.log2+1
  let d := Fixed.d b
  let B := Fixed.B b
  change 3≤d at big
  have dH : d≤Fixed.h b := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have db : d^2≤B := by
    have pb := Nat.pow_le_pow_left ((Nat.lt_two_pow_self (n:=d)).le) 2
    refine pb.trans ?_
    rw [←pow_mul]; change 2^(d*2)≤2^(1000*Fixed.h b)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have bound : B ≤ indexCap b (Fixed.beta b) := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have nodup : p.factorBase.Nodup := (List.nodup_range' ..).filter _
  change (p.factorBase.filter (fun q=>decide (q.Prime ∧ q≤B ∧ q.Coprime (leadingCoefficient n*n)))).dedup =
    p.factorBase
  rw [(show (p.factorBase.filter (fun q=>decide (q.Prime ∧ q≤B ∧ q.Coprime (leadingCoefficient n*n)))) =
    p.factorBase from ?_),List.dedup_eq_self.mpr nodup]
  apply List.filter_eq_self.mpr
  intro q hq
  obtain ⟨qp,qB,qs,_⟩ := (constructed_factorBase_iff n ell u v x y q).mp hq
  change B<q^2 at qs
  change q≤B at qB
  have dq : d<q := by
    by_contra! small
    exact (qs.not_ge ((Nat.pow_le_pow_left small 2).trans db))
  have pn : ¬q∣n := by
    intro divides
    have small : q<n := lt_of_le_of_ne (Nat.le_of_dvd (by omega) divides) (fun e=>comp (e ▸ qp))
    exact presieve_hits (show TwoThirdsSearch.ProperDivisor n q from ⟨qp.one_lt,small,divides⟩)
      (qB.trans bound) absent
  have half : (primorial d/2).Coprime q := by
    apply Nat.Coprime.of_dvd_left (Nat.div_dvd_of_dvd (Nat.prime_two.dvd_primorial_iff.mpr (by omega : 2≤d)))
    exact (qp.coprime_iff_not_dvd.mpr (fun h=>dq.not_ge (qp.dvd_primorial_iff.mp h))).symm
  have three : Nat.Coprime 3 q := (Nat.coprime_primes Nat.prime_three qp).mpr (by change 3≤d at big; omega)
  have lead : (leadingCoefficient n).Coprime q := Nat.coprime_mul_iff_left.mpr ⟨half,three.pow_left _⟩
  exact decide_eq_true ⟨qp,qB,Nat.coprime_mul_iff_right.mpr ⟨lead.symm,qp.coprime_iff_not_dvd.mpr pn⟩⟩

end Cogentic.CandidateMarks

#print axioms Cogentic.CandidateMarks.polynomial_spec
#print axioms Cogentic.CandidateMarks.fixed_constructed_marks
#print axioms Cogentic.CandidateMarks.fixed_checked_stage
#print axioms Cogentic.CandidateMarks.constructed_base_eq
