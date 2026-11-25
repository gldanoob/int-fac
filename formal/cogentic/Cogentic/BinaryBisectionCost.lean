import Cogentic.RootSignCost

namespace Cogentic.BinaryBisection
open BinaryDivision BinaryPivot BinaryRootSign

/-- Two signed endpoint numerators sharing one positive denominator. -/
structure Grid where
  left : SignedWord
  right : SignedWord
  den : List Bool

def Grid.bracket (g : Grid) : Bisection.Bracket :=
  ⟨(g.left.decode:ℚ)/value g.den,(g.right.decode:ℚ)/value g.den⟩

def Grid.Fits (g : Grid) (W : ℕ) : Prop :=
  g.left.digits.length≤W ∧ g.right.digits.length≤W ∧ g.den.length≤W

def twice (x : SignedWord) : SignedWord := ⟨x.negative,false::x.digits⟩

private theorem twice_val (x : SignedWord) : (twice x).decode=2*x.decode := by
  cases x with | mk s ds => cases s <;> simp [twice,SignedWord.decode,signed,value]

private def chooseWord (take : Bool) (x y : SignedWord) : SignedWord × ℕ :=
  let w := max x.digits.length y.digits.length
  let m := selectDigits w take (!take) x.digits y.digits
  (⟨(take && x.negative) || (!take && y.negative),m.1⟩,m.2+4)

private theorem choose_spec (take : Bool) (x y : SignedWord) :
    let out := chooseWord take x y; let w := max x.digits.length y.digits.length
    out.1.decode=(if take then x.decode else y.decode) ∧ out.1.digits.length=w ∧ out.2=3*w+4 := by
  have ⟨len,cost,eq⟩ := select_spec _ take x.digits y.digits (le_max_left ..) (le_max_right ..)
  refine ⟨?_,len,congrArg (·+4) cost⟩
  cases take <;> simp_all [chooseWord,SignedWord.decode]

private def nonpositive (a b : Bool×Bool) := !a.2 || !b.2 || xor a.1 b.1
private def negative (a b : Bool×Bool) := a.2 && b.2 && xor a.1 b.1

private theorem product_flags (u v : ℚ) (a b : Bool×Bool)
    (au : (a.1=true ↔ u<0) ∧ (a.2=true ↔ u≠0))
    (bv : (b.1=true ↔ v<0) ∧ (b.2=true ↔ v≠0)) :
    (nonpositive a b=true ↔ u*v≤0) ∧ (negative a b=true ↔ u*v<0) := by
  have bit (b : Bool) (P : Prop) [Decidable P] (h : b=true ↔ P) : b=decide P := by
    by_cases p : P <;> cases b <;> simp_all
  have fa : a=(decide (u<0),decide (u≠0)) := Prod.ext (bit _ _ au.1) (bit _ _ au.2)
  have fb : b=(decide (v<0),decide (v≠0)) := Prod.ext (bit _ _ bv.1) (bit _ _ bv.2)
  rw [fa,fb]
  rcases lt_trichotomy u 0 with hu|hu|hu <;> rcases lt_trichotomy v 0 with hv|hv|hv <;>
    simp [nonpositive,negative,mul_nonpos_iff,mul_neg_iff, *] <;> grind

private def addWord (x y : SignedWord) := signedDifference x (BinaryRootSign.neg y)

private theorem add_spec (x y : SignedWord) :
    (addWord x y).1.decode=x.decode+y.decode ∧
    (addWord x y).1.digits.length=max x.digits.length y.digits.length+1 ∧
    (addWord x y).2=25*max x.digits.length y.digits.length+8 := by
  obtain ⟨v,c⟩ := signedDifference_spec x (BinaryRootSign.neg y)
  rw [BinaryRootSign.neg_val,sub_neg_eq_add] at v
  exact ⟨v,diff_width ..,c⟩

/-- Midpoints use twice the common denominator, so one round increases
each word width by at most one, without a rational gcd or a division. -/
def halve (A : List Bool) (cs : List SignedWord) (g : Grid) : Grid × ℕ :=
  let m := addWord g.left g.right
  let q := false::g.den
  let l := atPoint A g.left g.den cs
  let t := atPoint A m.1 q cs
  let flag := nonpositive l.1 t.1
  let lo := chooseWord flag (twice g.left) m.1
  let hi := chooseWord flag m.1 (twice g.right)
  (⟨lo.1,hi.1,q⟩,m.2+1+l.2+t.2+5+lo.2+hi.2)

private theorem scaled_points (g : Grid) (qp : 0<value g.den) :
    let q := false::g.den; let m := (addWord g.left g.right).1
    ((twice g.left).decode:ℚ)/value q=g.bracket.left ∧
    (m.decode:ℚ)/value q=g.bracket.mid ∧ ((twice g.right).decode:ℚ)/value q=g.bracket.right := by
  intro q m
  have den : value q=2*value g.den := by simp [q,value]
  dsimp only [Grid.bracket,Bisection.Bracket.mid,m]
  rw [den,(add_spec ..).1,twice_val,twice_val]
  push_cast
  constructor
  · field_simp
  constructor <;> field_simp

theorem halve_value (A : List Bool) (cs : List ℤ) (g : Grid) (qp : 0<value g.den) :
    (halve A (cs.map encode) g).1.bracket=Bisection.halve (RootLogs.normalized (value A) cs) g.bracket ∧
    0<value (halve A (cs.map encode) g).1.den := by
  let m := (addWord g.left g.right).1; let q := false::g.den
  let f := RootLogs.normalized (R:=ℚ) (value A) cs
  let left := (atPoint A g.left g.den (cs.map encode)).1
  let mid := (atPoint A m q (cs.map encode)).1
  have qp' : 0<value q := by simpa [q,value] using qp
  obtain ⟨dl,dm,dr⟩ := scaled_points g qp
  change ((twice g.left).decode:ℚ)/value q=g.bracket.left at dl
  change (m.decode:ℚ)/value q=g.bracket.mid at dm
  change ((twice g.right).decode:ℚ)/value q=g.bracket.right at dr
  have ls := atPoint_value A g.left qp cs
  have ms := atPoint_value A m qp' cs
  change (mid.1=true ↔ f ((m.decode:ℚ)/value q)<0) ∧ (mid.2=true ↔ f ((m.decode:ℚ)/value q)≠0) at ms
  rw [show (m.decode:ℚ)/value q=g.bracket.mid from dm] at ms
  have flag := (product_flags (f g.bracket.left) (f g.bracket.mid) left mid ls ms).1
  refine ⟨?_,qp'⟩
  let s := nonpositive left mid
  let l := chooseWord s (twice g.left) m; let r := chooseWord s m (twice g.right)
  change (⟨(l.1.decode:ℚ)/value q,(r.1.decode:ℚ)/value q⟩:Bisection.Bracket)=Bisection.halve f g.bracket
  have le := (choose_spec s (twice g.left) m).1; have re := (choose_spec s m (twice g.right)).1
  change l.1.decode=_ at le;change r.1.decode=_ at re
  rw [le,re]
  by_cases h : s=true
  · simp only [h,if_true,Bisection.halve,if_pos (flag.mp h),dl,dm]
  · simp only [if_neg h,Bisection.halve,if_neg (fun t=>h (flag.mpr t)),dr,dm]

def refine (A : List Bool) (cs : List SignedWord) : ℕ→Grid→Grid×ℕ
  | 0,g => (g,0)
  | k+1,g => let u := halve A cs g; let v := refine A cs k u.1; (v.1,u.2+v.2)

theorem refine_value (A : List Bool) (cs : List ℤ) (bits : ℕ) (g : Grid) (qp : 0<value g.den) :
    (refine A (cs.map encode) bits g).1.bracket=Bisection.refine (RootLogs.normalized (value A) cs) bits g.bracket ∧
    0<value (refine A (cs.map encode) bits g).1.den := by
  induction bits generalizing g with
  | zero => exact ⟨rfl,qp⟩
  | succ k ih =>
    obtain ⟨step,pos⟩ := halve_value A cs g qp
    obtain ⟨eval,den⟩ := ih _ pos
    exact ⟨eval.trans (congrArg (Bisection.refine _ k) step),den⟩

/-- A single polynomial bound on the gate count per bisection round with
all input word lengths at most W. The extra bit includes the new midpoint. -/
def roundCap (length W : ℕ) :=
  1200*(length+1)*(2+(length+1)*(12*(W+1)+1))^2

theorem halve_gates (A : List Bool) (cs : List SignedWord) (g : Grid) (W : ℕ)
    (al : A.length≤W) (coeff : ∀ c∈cs,c.digits.length≤W) (fit : g.Fits W) :
    (halve A cs g).1.Fits (W+1) ∧ (halve A cs g).2≤roundCap cs.length W := by
  obtain ⟨ll,rl,ql⟩ := fit
  let m := addWord g.left g.right; let q := false::g.den
  let l := atPoint A g.left g.den cs; let t := atPoint A m.1 q cs
  let flag := nonpositive l.1 t.1
  let lo := chooseWord flag (twice g.left) m.1; let hi := chooseWord flag m.1 (twice g.right)
  obtain ⟨_,mw,mc⟩ := add_spec g.left g.right
  change m.1.digits.length=_ at mw;change m.2=_ at mc
  have middle : m.1.digits.length≤W+1 := mw.le.trans (Nat.add_le_add_right (max_le ll rl) 1)
  obtain ⟨_,lw,lc⟩ := choose_spec flag (twice g.left) m.1
  obtain ⟨_,rw',rc⟩ := choose_spec flag m.1 (twice g.right)
  have ml : (twice g.left).digits.length≤W+1 := Nat.succ_le_succ ll
  have mr : (twice g.right).digits.length≤W+1 := Nat.succ_le_succ rl
  have lwm := max_le ml middle;have rwm := max_le middle mr
  refine ⟨⟨lw.le.trans lwm,rw'.le.trans rwm,Nat.succ_le_succ ql⟩,?_⟩
  let H := 2+(cs.length+1)*(12*(W+1)+1)
  have left := atPoint_gates A g.left g.den cs (W+1) (by omega) (by omega) (by omega) (fun i hi'=>(coeff i hi').trans (Nat.le_succ _))
  have md := atPoint_gates A m.1 q cs (W+1) (by omega) middle (Nat.succ_le_succ ql) (fun i hi'=>(coeff i hi').trans (Nat.le_succ _))
  have adj : 1+(cs.length+1)*(12*(W+1)+1)+1=H := by dsimp only [H];omega
  dsimp only at left md
  rw [adj] at left md
  change l.2≤_ at left;change t.2≤_ at md
  have one : W+1≤H := by
    have h := Nat.le_mul_of_pos_left (12*(W+1)+1) (Nat.succ_pos cs.length)
    change W+1≤2+cs.length.succ*(12*(W+1)+1);omega
  have mlc : m.2≤25*W+8 := by rw [mc];gcongr;exact max_le ll rl
  have ac : lo.2≤3*(W+1)+4 := lc.le.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ lwm) 4)
  have bc : hi.2≤3*(W+1)+4 := rc.le.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ rwm) 4)
  change m.2+1+l.2+t.2+5+lo.2+hi.2 ≤ 1200*(cs.length+1)*H^2
  nlinarith only [left,md,mlc,ac,bc,one,Nat.le_mul_self H]

theorem refine_gates (A : List Bool) (cs : List SignedWord) (bits : ℕ) (g : Grid) (W : ℕ)
    (al : A.length≤W) (coeff : ∀ c∈cs,c.digits.length≤W) (fit : g.Fits W) :
    (refine A cs bits g).1.Fits (W+bits) ∧ (refine A cs bits g).2≤bits*roundCap cs.length (W+bits) := by
  induction bits generalizing g W with
  | zero => exact ⟨fit,by simp [refine]⟩
  | succ k ih =>
    let u := halve A cs g
    obtain ⟨uw,ug⟩ := halve_gates A cs g W al coeff fit
    obtain ⟨vw,vg⟩ := ih u.1 (W+1) (by omega) (fun c hc=>(coeff c hc).trans (Nat.le_succ _)) uw
    have adds : W+1+k = W+(k+1) := by omega
    rw [adds] at vw vg
    have mono : roundCap cs.length W≤roundCap cs.length (W+(k+1)) := by
      unfold roundCap;gcongr;omega
    refine ⟨vw,?_⟩
    change u.2+(refine A cs k u.1).2≤(k+1)*roundCap cs.length (W+(k+1))
    rw [Nat.succ_mul]
    exact (Nat.add_le_add (ug.trans mono) vg).trans_eq (Nat.add_comm ..)

/-- Evaluate the strict isolating sign test, refine precisely on acceptance,
and output the midpoint in the same unreduced integer-grid representation. -/
def isolateGrid (A : List Bool) (cs : List SignedWord) (bits : ℕ) (g : Grid) :
    Option (SignedWord × List Bool) × ℕ :=
  let l := atPoint A g.left g.den cs; let r := atPoint A g.right g.den cs
  let base := l.2+r.2+4
  if negative l.1 r.1 then
    let u := refine A cs bits g
    let m := addWord u.1.left u.1.right
    (some (m.1,false::u.1.den),base+u.2+m.2+1)
  else (none,base)

def decodePoint (s : SignedWord × List Bool) : ℚ := (s.1.decode:ℚ)/value s.2

theorem isolateGrid_value (A : List Bool) (cs : List ℤ) (bits : ℕ) (g : Grid) (qp : 0<value g.den) :
    let f := RootLogs.normalized (value A) cs
    (isolateGrid A (cs.map encode) bits g).1.map decodePoint =
      if f g.bracket.left*f g.bracket.right<0 then some (Bisection.refine f bits g.bracket).mid else none := by
  intro f
  let l := (atPoint A g.left g.den (cs.map encode)).1
  let r := (atPoint A g.right g.den (cs.map encode)).1
  have flag := (product_flags (f g.bracket.left) (f g.bracket.right) l r
    (atPoint_value A g.left qp cs) (atPoint_value A g.right qp cs)).2
  let u := refine A (cs.map encode) bits g
  obtain ⟨ok,pos⟩ := refine_value A cs bits g qp
  have mid := (scaled_points u.1 pos).2.1
  by_cases h : negative l r=true
  · simp only [if_pos (flag.mp h)]
    unfold isolateGrid
    rw [if_pos h]
    exact congrArg some (mid.trans (congrArg Bisection.Bracket.mid ok))
  · simp only [if_neg (fun t=>h (flag.mpr t))]
    unfold isolateGrid
    rw [if_neg h];rfl

theorem isolateGrid_gates (A : List Bool) (cs : List SignedWord) (bits : ℕ) (g : Grid) (W : ℕ)
    (al : A.length≤W) (coeff : ∀ c∈cs,c.digits.length≤W) (fit : g.Fits W) :
    (isolateGrid A cs bits g).2 ≤ (bits+2)*roundCap cs.length (W+bits) ∧
    ∀ t∈(isolateGrid A cs bits g).1,t.1.digits.length≤W+bits+1 ∧ t.2.length≤W+bits+1 := by
  let Z := W+bits;let H := 2+(cs.length+1)*(12*(Z+1)+1)
  let u := refine A cs bits g
  obtain ⟨uw,ug⟩ := refine_gates A cs bits g W al coeff fit
  change u.2≤bits*roundCap cs.length Z at ug
  have ufit : u.1.Fits Z := uw
  obtain ⟨ll,rl,ql⟩ := fit
  have sig (x : SignedWord) (h : x.digits.length≤W) : (atPoint A x g.den cs).2≤500*(cs.length+1)*H^2 := by
    have step := atPoint_gates A x g.den cs (Z+1) (by dsimp [Z];omega) (by dsimp [Z];omega) (by dsimp [Z];omega)
      (fun c hc=>by have := coeff c hc;dsimp [Z];omega)
    dsimp only at step
    rwa [show 1+(cs.length+1)*(12*(Z+1)+1)+1=H by dsimp only [H];omega] at step
  have lh := sig _ ll; have rh := sig _ rl
  let mid := addWord u.1.left u.1.right
  obtain ⟨_,width,mc⟩ := add_spec u.1.left u.1.right
  have maxw := max_le ufit.1 ufit.2.1
  have charge : mid.2≤25*Z+8 := mc.le.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ maxw) 8)
  have zle : Z+1≤H := by
    have h := Nat.le_mul_of_pos_left (12*(Z+1)+1) (Nat.succ_pos cs.length)
    change Z+1≤2+cs.length.succ*(12*(Z+1)+1);omega
  have small : (atPoint A g.left g.den cs).2+(atPoint A g.right g.den cs).2+4+mid.2+1 ≤ roundCap cs.length Z := by
    change _ ≤ 1200*(cs.length+1)*H^2
    nlinarith only [lh,rh,charge,zle,Nat.le_mul_self H]
  dsimp only [isolateGrid]
  split
  · refine ⟨?_,?_⟩
    · change _ + u.2 + mid.2+1≤(bits+2)*roundCap cs.length Z
      rw [Nat.add_mul];omega
    · intro t ht
      cases Option.mem_some_iff.mp ht
      exact ⟨width.le.trans (Nat.add_le_add_right maxw 1),Nat.succ_le_succ ufit.2.2⟩
  · refine ⟨?_,by simp⟩
    change _ ≤ (bits+2)*roundCap cs.length Z
    rw [Nat.add_mul];omega

private def shifted : ℕ → List Bool → List Bool
  | 0,x=>x
  | k+1,x=>false::shifted k x

private theorem shift_spec (k : ℕ) (x : List Bool) :
    value (shifted k x)=2^k*value x ∧ (shifted k x).length=k+x.length := by
  induction k with
  | zero => simp [shifted]
  | succ k ih => simp [shifted,value,ih.1,ih.2,pow_succ];constructor <;> ring

/-- Construct the two numerators and common denominator of the root
bracket, using the degree and root index in binary and dyadic wire shifts. -/
def initial (degree index : List Bool) (side : Bool) (k : ℕ) : Grid × ℕ :=
  let d := false::false::degree;let j := false::index;let offset := if side then [false,true] else [true]
  let c := addDigits (max j.length offset.length) j offset false
  let center : SignedWord := ⟨false,shifted k c.1⟩;let width : SignedWord := ⟨false,d⟩
  let lo := signedDifference center width;let hi := addWord center width
  (⟨lo.1,hi.1,shifted k d⟩,c.2+lo.2+hi.2+1)

theorem initial_value (s : Marking.Input) (side : Bool) (j : Fin s.degree) :
    let k := (19*s.K₁.log2+19)/20;let g := (initial s.degree.bits j.val.bits side k).1
    g.bracket=RootLogs.bracket s side j ∧ 0<value g.den := by
  intro k g
  let d := false::false::s.degree.bits;let jj := false::j.val.bits
  let off : List Bool := if side then [false,true] else [true]
  let c := addDigits (max jj.length off.length) jj off false
  let x : SignedWord := ⟨false,shifted k c.1⟩;let h : SignedWord := ⟨false,d⟩
  have dv : value d=4*s.degree := by simp [d,value];omega
  have jv : value jj=2*j.val := by simp [jj,value]
  have ov : value off=if side then 2 else 1 := by cases side <;> decide
  obtain ⟨_,_,cv⟩ := addDigits_spec _ jj off false (le_max_left ..) (le_max_right ..)
  change value c.1=_ at cv
  rw [jv,ov] at cv
  let u := 2*j.val+(if side then 2 else 1)
  have xv : x.decode=((2^k*u:ℕ):ℤ) := by change (value (shifted k c.1):ℤ)=_; rw [(shift_spec ..).1,cv];rfl
  have wv : h.decode=((4*s.degree:ℕ):ℤ) := congrArg (Nat.cast (R:=ℤ)) dv
  have den : value g.den=2^k*(4*s.degree) := (shift_spec k d).1.trans (congrArg (2^k*·) dv)
  have left := (signedDifference_spec x h).1;have right := (add_spec x h).1
  change g.left.decode=x.decode-h.decode at left;change g.right.decode=x.decode+h.decode at right
  have dp : 0<s.degree := Nat.zero_lt_of_lt j.isLt
  refine ⟨?_,den.symm ▸ (by positivity)⟩
  unfold Grid.bracket RootLogs.bracket
  rw [left,right,xv,wv,den]
  push_cast
  have dd : (s.degree:ℚ)≠0 := by exact_mod_cast dp.ne'
  have unr : (u:ℚ)=2*j.val+if side then 2 else 1 := by cases side <;> simp [u]
  rw [←unr]
  rw [one_div_pow]
  congr 1 <;> field_simp <;> ring

theorem initial_gates (degree index : List Bool) (side : Bool) (k W : ℕ)
    (dl : degree.length≤W) (il : index.length≤W) :
    let u := initial degree index side k
    u.1.Fits (W+k+5) ∧ u.2≤60*(W+k+5) := by
  let d := false::false::degree;let j := false::index
  let off : List Bool := if side then [false,true] else [true]
  let c := addDigits (max j.length off.length) j off false
  let x : SignedWord := ⟨false,shifted k c.1⟩;let h : SignedWord := ⟨false,d⟩
  have o : off.length≤2 := by cases side <;> decide
  have jw : j.length≤W+1 := Nat.succ_le_succ il
  have dw : d.length≤W+2 := Nat.succ_le_succ (Nat.succ_le_succ dl)
  have ⟨cl,cc,_⟩ := addDigits_spec _ j off false (le_max_left ..) (le_max_right ..)
  change c.1.length=_ at cl;change c.2=_ at cc
  have maxc : max j.length off.length≤W+2 := max_le (by omega) (by omega)
  have xl : x.digits.length≤W+k+3 := by change (shifted k c.1).length≤_;rw [(shift_spec ..).2,cl];omega
  have mx : max x.digits.length h.digits.length≤W+k+3 := max_le xl (by change d.length≤_;omega)
  obtain ⟨_,lw⟩ := signedDifference_spec x h
  obtain ⟨_,rwidth,rw'⟩ := add_spec x h
  have fit : max x.digits.length h.digits.length+1≤W+k+5 := by omega
  refine ⟨⟨(diff_width x h).le.trans fit,rwidth.le.trans fit,?_⟩,?_⟩
  · change (shifted k d).length≤_;rw [(shift_spec ..).2];omega
  · change c.2+(signedDifference x h).2+(addWord x h).2+1≤60*(W+k+5)
    rw [cc,lw,rw'];omega

/-- Costed implementation of the original root-isolation entry point. -/
def isolate (s : Marking.Input) (side : Bool) (j : Fin s.degree) (bits : ℕ) :=
  let k := (19*s.K₁.log2+19)/20
  let g := initial s.degree.bits j.val.bits side k
  let t := isolateGrid s.A.bits ((s.coeffs side).map encode) bits g.1
  (t.1,g.2+t.2)

theorem isolate_value (s : Marking.Input) (side : Bool) (j : Fin s.degree) (bits : ℕ) :
    (isolate s side j bits).1.map decodePoint=RootLogs.isolate s side j bits := by
  let g := (initial s.degree.bits j.val.bits side ((19*s.K₁.log2+19)/20)).1
  obtain ⟨br,pos⟩ := initial_value s side j
  have exact := isolateGrid_value s.A.bits (s.coeffs side) bits g pos
  dsimp only at exact
  change g.bracket=RootLogs.bracket s side j at br
  rw [br,value_bits] at exact
  exact exact

theorem isolate_gates (s : Marking.Input) (side : Bool) (j : Fin s.degree) (bits W : ℕ)
    (boundA : s.A.size≤W) (boundD : s.degree.size≤W) (boundC : ∀ c∈s.coeffs side,c.natAbs.size≤W) :
    let k := (19*s.K₁.log2+19)/20
    let width := W+k+5
    (isolate s side j bits).2 ≤ 60*width+(bits+2)*roundCap (s.coeffs side).length (width+bits) ∧
    ∀ t∈(isolate s side j bits).1, t.1.digits.length≤width+bits+1 ∧ t.2.length≤width+bits+1 := by
  intro k width
  let g := initial s.degree.bits j.val.bits side k
  have deg : s.degree.bits.length≤W := (Nat.size_eq_bits_len _).le.trans boundD
  have idx : j.val.bits.length≤W := (Nat.size_eq_bits_len _).le.trans ((Nat.size_le_size j.isLt.le).trans boundD)
  obtain ⟨fit,build⟩ := initial_gates s.degree.bits j.val.bits side k W deg idx
  have al : s.A.bits.length≤width := (Nat.size_eq_bits_len _).le.trans (boundA.trans (by dsimp [width];omega))
  have coeff (c) (hc : c∈(s.coeffs side).map encode) : c.digits.length≤width := by
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hc
    change z.natAbs.bits.length≤width
    rw [Nat.size_eq_bits_len]
    exact (boundC z hz).trans (by dsimp [width];omega)
  obtain ⟨used,out⟩ := isolateGrid_gates s.A.bits ((s.coeffs side).map encode) bits g.1 width al coeff fit
  rw [List.length_map] at used
  exact ⟨Nat.add_le_add build used,out⟩

theorem isolate_stage_gates {s : Marking.Input} {rel : Marking.Relations} (stage : Marking.stageOne s=some rel)
    (side : Bool) (j : Fin s.degree) (bits : ℕ) :
    let k := (19*s.K₁.log2+19)/20;let width := s.L₀+s.degree.size+1+k+5
    (isolate s side j bits).2 ≤ 60*width+(bits+2)*roundCap (s.degree+1) (width+bits) ∧
    ∀ t∈(isolate s side j bits).1, t.1.digits.length≤width+bits+1 ∧ t.2.length≤width+bits+1 := by
  let W := s.L₀+s.degree.size+1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,ha,_,_,gf,gs⟩ := (Marking.rows_and_guards stage).1
  have guard : s.polynomialGuard (s.coeffs side) := by cases side <;> first | exact gf | exact gs
  have size (x : ℕ) (h : x≤2^s.L₀) : x.size≤W := by
    have a := Nat.size_le_size h
    rw [Nat.size_pow] at a
    dsimp only [W];omega
  have h := isolate_gates s side j bits W (size _ ha) (by dsimp only [W];omega)
    (fun c hc=>size _ (guard.2.2.1 c hc))
  simpa only [guard.1] using h

end Cogentic.BinaryBisection

#print axioms Cogentic.BinaryBisection.refine_value
#print axioms Cogentic.BinaryBisection.refine_gates

#print axioms Cogentic.BinaryBisection.isolate_value
#print axioms Cogentic.BinaryBisection.isolate_stage_gates
