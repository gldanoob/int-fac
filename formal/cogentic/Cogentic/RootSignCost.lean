import Cogentic.ReconstructionCost
import Cogentic.RootLogs

namespace Cogentic.BinaryRootSign
open BinaryDivision BinaryPivot

def neg (x : SignedWord) : SignedWord := ⟨!x.negative,x.digits⟩
theorem neg_val (x : SignedWord) : (neg x).decode = -x.decode := by
  cases x with | mk s ds => cases s <;> simp [neg,SignedWord.decode,signed]

private theorem mux_length (k : ℕ) (a b : Bool) (x y : List Bool) :
    (selectDigits k a b x y).1.length=k := by
  induction k generalizing x y with | zero => rfl | succ k ih => simp [selectDigits,ih]

theorem diff_width (a b : SignedWord) : (signedDifference a b).1.digits.length=max a.digits.length b.digits.length+1 :=
  mux_length ..

private theorem cross_width (a b c d : SignedWord) :
    (cross a b c d).1.digits.length≤ max (b.digits.length+2*a.digits.length) (d.digits.length+2*c.digits.length)+1 := by
  have l := (multiply_spec b.digits a.digits).2.1
  have r := (multiply_spec d.digits c.digits).2.1
  simp only [cross,diff_width]
  exact Nat.add_le_add_right (max_le_max l r) 1

structure Evaluation where
  num : SignedWord
  den : List Bool
  gates : ℕ

/-- Homogeneous Horner evaluation. The first argument of each cross product
is short, so the unreduced result grows linearly in the number of coefficients. -/
def polynomial (x : SignedWord) (q : List Bool) : List SignedWord → Evaluation
  | [] => ⟨⟨false,[]⟩,[true],0⟩
  | c::cs =>
    let v := polynomial x q cs
    let D := multiply v.den q
    let N := cross c ⟨false,D.1⟩ (neg x) v.num
    ⟨N.1,D.1,v.gates+D.2+N.2+1⟩

theorem polynomial_value (x : SignedWord) {q : List Bool} (qp : 0<value q) (cs : List ℤ) :
    let out := polynomial x q (cs.map encode)
    0<value out.den ∧ (out.num.decode:ℚ)/value out.den=
      (Marking.horner ((x.decode:ℚ)/value q) cs).1 := by
  induction cs with
  | nil => simp [polynomial,value,SignedWord.decode,signed,Marking.horner]
  | cons c cs ih =>
    let v := polynomial x q (cs.map encode)
    let D := multiply v.den q
    have dv : value D.1=value q*value v.den := (multiply_spec ..).1
    let u : SignedWord := ⟨false,D.1⟩
    let W := (encode c).digits.length+u.digits.length+(neg x).digits.length+v.num.digits.length
    have e := (cross_spec (encode c) u (neg x) v.num W (by dsimp [W]; omega) (by dsimp [W]; omega)
      (by dsimp [W]; omega) (by dsimp [W]; omega)).1
    obtain ⟨dp,eval⟩ := ih
    change 0<value v.den at dp
    change (v.num.decode:ℚ)/value v.den=_ at eval
    change 0<value D.1 ∧ ((cross (encode c) u (neg x) v.num).1.decode:ℚ)/value D.1=_
    have uv : u.decode=(value D.1:ℤ) := rfl
    rw [e,neg_val,decode_encode,uv,dv]
    refine ⟨Nat.mul_pos qp dp,?_⟩
    change _=(c:ℚ)+((x.decode:ℚ)/value q)*(Marking.horner _ cs).1
    rw [←eval]
    push_cast; field_simp; ring

theorem polynomial_gates (x : SignedWord) (q : List Bool) (cs : List SignedWord) (L W : ℕ)
    (xl : x.digits.length≤W) (ql : q.length≤W) (len : cs.length≤L)
    (coeff : ∀ c∈cs,c.digits.length≤W) :
    let f := polynomial x q cs
    let H := 1+(L+1)*(4*W+1)
    f.num.digits.length≤1+cs.length*(4*W+1) ∧ f.den.length≤1+cs.length*(4*W+1) ∧
      f.gates≤cs.length*(200*(H+1)^2) := by
  induction cs with
  | nil => simp [polynomial]
  | cons c cs ih =>
    let v := polynomial x q cs
    let D := multiply v.den q
    let u : SignedWord := ⟨false,D.1⟩
    let H := 1+(L+1)*(4*W+1)
    simp only [List.length_cons] at len ⊢
    obtain ⟨vl,vd,vc⟩ := ih (by omega) (fun i hi=>coeff i (List.mem_cons_of_mem _ hi))
    change v.num.digits.length≤_ at vl; change v.den.length≤_ at vd
    change v.gates≤cs.length*(200*(H+1)^2) at vc
    have cw := coeff c List.mem_cons_self
    have ⟨_,dl,dc⟩ := multiply_spec v.den q
    change D.1.length≤_ at dl; change D.2≤_ at dc
    have nw := cross_width c u (neg x) v.num
    change (cross c u (neg x) v.num).1.digits.length≤ max (D.1.length+2*c.digits.length) (v.num.digits.length+2*x.digits.length)+1 at nw
    have vh : 1+cs.length*(4*W+1)+(4*W+1)≤H := by
      calc
        _ = 1+(cs.length+1)*(4*W+1) := by ring
        _ ≤ 1+(L+1)*(4*W+1) := Nat.add_le_add_left (Nat.mul_le_mul_right _ (len.trans (Nat.le_succ L))) 1
    have wh : W≤H := by
      have h := Nat.le_mul_of_pos_left (4*W+1) (Nat.succ_pos L)
      dsimp [H]; omega
    have cg := (cross_spec c u (neg x) v.num H (cw.trans wh) (by change D.1.length≤H; omega)
      (xl.trans wh) (by omega)).2
    have dg : D.2≤16*H^2 := dc.trans (calc
      _ ≤ H*(H+5*(H+2*H)) := by gcongr <;> omega
      _ = _ := by ring)
    change (cross c u (neg x) v.num).1.digits.length≤_ ∧ D.1.length≤_ ∧ v.gates+D.2+(cross c u (neg x) v.num).2+1≤_
    simp only [Nat.succ_mul (n := cs.length)]
    refine ⟨by omega,by omega,?_⟩
    have step : D.2+(cross c u (neg x) v.num).2+1≤200*(H+1)^2 := by nlinarith only [dg,cg]
    change _≤cs.length*(200*(H+1)^2)+200*(H+1)^2
    omega

/-- The two bits encode negativity and nonzero magnitude. The scan also handles
untrimmed words and the signed zero representation produced by a subtraction. -/
def sign (s : SignedWord) : (Bool × Bool) × ℕ :=
  let nz := BinaryReconstruction.below [] s.digits
  ((s.negative && nz.1,nz.1),nz.2+1)

theorem sign_spec (s : SignedWord) :
    ((sign s).1.1=true ↔ s.decode<0) ∧ ((sign s).1.2=true ↔ s.decode≠0) ∧
      (sign s).2≤7*s.digits.length+1 := by
  have ⟨nz,cost⟩ := BinaryReconstruction.below_spec [] s.digits
  simp only [value] at nz
  simp only [sign,Bool.and_eq_true,nz]
  cases s with | mk v ds =>
    cases v <;> simp_all [SignedWord.decode,signed] <;> omega

end Cogentic.BinaryRootSign

namespace Cogentic.BinaryRootSign
open BinaryDivision BinaryPivot Bisection

/-- Signs of f(A z/q) at the supplied rational grid point. -/
def atPoint (A : List Bool) (z : SignedWord) (q : List Bool) (cs : List SignedWord) : (Bool × Bool) × ℕ :=
  let p := multiply z.digits A
  let v := polynomial ⟨z.negative,p.1⟩ q cs
  let s := sign v.num
  (s.1,p.2+v.gates+s.2)

theorem atPoint_value (A : List Bool) (z : SignedWord) {q : List Bool} (qp : 0<value q) (cs : List ℤ) :
    let out := atPoint A z q (cs.map encode)
    let y := RootLogs.normalized (value A) cs ((z.decode:ℚ)/value q)
    (out.1.1=true ↔ y<0) ∧ (out.1.2=true ↔ y≠0) := by
  let p := multiply z.digits A
  let x : SignedWord := ⟨z.negative,p.1⟩
  let v := polynomial x q (cs.map encode)
  have pv : value p.1=value A*value z.digits := (multiply_spec ..).1
  have xv : x.decode=(value A:ℤ)*z.decode := by
    simp only [x,SignedWord.decode,pv,signed]
    cases z.negative <;> simp
  obtain ⟨dp,ev⟩ := polynomial_value x qp cs
  change 0<value v.den at dp
  change (v.num.decode:ℚ)/value v.den=_ at ev
  have e : RootLogs.normalized (value A) cs ((z.decode:ℚ)/value q)=(v.num.decode:ℚ)/value v.den := by
    rw [ev,xv]
    unfold RootLogs.normalized
    push_cast; rw [mul_div_assoc]
  obtain ⟨sn,nz,_⟩ := sign_spec v.num
  change ((sign v.num).1.1=true ↔ _) ∧ ((sign v.num).1.2=true ↔ _)
  rw [e,sn,nz]
  have den : (0:ℚ)<value v.den := by exact_mod_cast dp
  constructor
  · rw [div_lt_iff₀ den,zero_mul];exact_mod_cast Iff.rfl
  · simp [den.ne']

theorem atPoint_gates (A : List Bool) (z : SignedWord) (q : List Bool) (cs : List SignedWord) (W : ℕ)
    (al : A.length≤W) (zl : z.digits.length≤W) (ql : q.length≤W) (coeff : ∀ c∈cs,c.digits.length≤W) :
    let H := 1+(cs.length+1)*(12*W+1)
    (atPoint A z q cs).2≤500*(cs.length+1)*(H+1)^2 := by
  let p := multiply z.digits A
  let x : SignedWord := ⟨z.negative,p.1⟩
  let v := polynomial x q cs
  let H := 1+(cs.length+1)*(12*W+1)
  have ⟨_,pl,pc⟩ := multiply_spec z.digits A
  change p.1.length≤_ at pl; change p.2≤_ at pc
  have ⟨nl,_,vc⟩ := polynomial_gates x q cs cs.length (3*W) (by change p.1.length≤_; omega)
    (by omega) le_rfl (fun i hi=>by have := coeff i hi; omega)
  rw [show 4*(3*W)=12*W by ring] at nl vc
  change v.num.digits.length≤_ at nl; change v.gates≤cs.length*(200*(H+1)^2) at vc
  have nh : v.num.digits.length≤H := nl.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _)
  have wh : W≤H := by
    have low := Nat.le_mul_of_pos_left (12*W+1) (Nat.succ_pos cs.length)
    change W≤1+cs.length.succ*(12*W+1);omega
  have pw : p.2≤16*H^2 := pc.trans (calc
    _ ≤ H*(H+5*(H+2*H)) := by gcongr <;> omega
    _ = _ := by ring)
  have sc := (sign_spec v.num).2.2.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ nh) 1)
  change p.2+v.gates+(sign v.num).2≤500*(cs.length+1)*(H+1)^2
  nlinarith only [pw,vc,sc]

end Cogentic.BinaryRootSign
