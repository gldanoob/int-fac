import Cogentic.CandidateRuntime
import Cogentic.ConstructionCofactors

namespace Cogentic.BinaryCofactor
open BinaryDivision BinaryPivot BinarySaturation CandidateRuntime Construction

private theorem value_eq_abs (m : ℕ) (cs : List ℤ) :
    Marking.value cs m = (Construction.eval (m:ℤ) cs).natAbs := by
  have h : (Marking.horner (m:ℤ) cs).1 = Construction.eval (m:ℤ) cs := by
    induction cs with
    | nil => rfl
    | cons c cs ih => simp [Marking.horner,Construction.eval,ih]
  exact congrArg Int.natAbs h

private theorem abs_quotient (n : ℕ) (pos : 0<n) (z : ℤ) (div : (n:ℤ)∣z) :
    z.natAbs/n = (z/(n:ℤ)).natAbs := by
  obtain ⟨a,rfl⟩ := div
  have nz : (n:ℤ) ≠ 0 := by exact_mod_cast pos.ne'
  simp [Int.natAbs_mul,Int.mul_ediv_cancel_left _ nz,Nat.mul_div_cancel_left _ pos]

private theorem quotient_length (n a : List Bool) : (divide n a).quotient.length=a.length := by
  induction a with
  | nil => rfl
  | cons b bs ih => simp [divide,ih]

/-- Exact division of a polynomial value at the common root. Since the
evaluated integer is a multiple of N, magnitude division handles either sign. -/
def cofactor (n m : List Bool) (cs : List SignedWord) : List Bool × ℕ :=
  let mag := norm m cs
  let d := divide n mag.1
  (d.quotient,mag.2+d.gates+1)

def partBudget (len w : ℕ) := 1+len*evalStep w+3*w+w*(20*w+1)+1

private theorem cofactor_spec (n m : ℕ) (cs : List ℤ) (height w : ℕ)
    (pos : 0<n) (nw : n.size≤w) (mw : m.size≤w) (bounds : ∀ c∈cs,c.natAbs.size≤height)
    (room : height+cs.length*(2*m.size+1)≤w) (div : (n:ℤ)∣Construction.eval (m:ℤ) cs) :
    let r := cofactor n.bits m.bits (cs.map encode)
    value r.1 = ((Construction.eval (m:ℤ) cs)/(n:ℤ)).natAbs ∧
    r.1.length ≤ w ∧ r.2≤partBudget cs.length w := by
  let mag := norm m.bits (cs.map encode)
  let d := divide n.bits mag.1
  obtain ⟨v,c⟩ := norm_spec m cs height w bounds mw room
  have l := norm_length m cs height w bounds mw room
  change mag.1=_ at v
  change mag.2≤_ at c
  change mag.1.length≤_ at l
  have dw : (Marking.value cs m).size≤w := by rw [v,Nat.size_eq_bits_len] at l; exact l
  have ⟨qv,_,dc⟩ := divide_naturals (Marking.value cs m) n pos
  have q : value d.quotient=(Marking.value cs m)/n := by simpa only [d,v] using qv
  have wc : d.gates ≤ w*(20*w+1) := by
    simpa only [d,v] using dc.trans (Nat.mul_le_mul dw (by omega))
  have dl := quotient_length n.bits mag.1
  change d.quotient.length=_ at dl
  refine ⟨q.trans ?_,dl.trans_le l,?_⟩
  · rw [value_eq_abs,abs_quotient n pos _ div]
  · change mag.2+d.gates+1≤_; unfold partBudget; omega

/-- Compute both cofactor magnitudes and return the canonical bits of their
product for use as the constructor's sieve modulus. -/
def run (n m : List Bool) (left right : List SignedWord) : List Bool × ℕ :=
  let l := cofactor n m left
  let r := cofactor n m right
  let mul := multiply l.1 r.1
  let out := canonical mul.1
  (out.1,l.2+r.2+mul.2+out.2+1)

def budget (len w : ℕ) := 2*partBudget len w+16*w^2+9*w+1

theorem run_spec (n m : ℕ) (left right : List ℤ) (len height w : ℕ)
    (pos : 0<n) (nw : n.size≤w) (mw : m.size≤w)
    (leftLen : left.length≤len) (rightLen : right.length≤len)
    (lc : ∀ c∈left,c.natAbs.size≤height) (rc : ∀ c∈right,c.natAbs.size≤height)
    (room : height+len*(2*m.size+1)≤w)
    (ld : (n:ℤ)∣Construction.eval (m:ℤ) left) (rd : (n:ℤ)∣Construction.eval (m:ℤ) right) :
    let out := run n.bits m.bits (left.map encode) (right.map encode)
    let k := fun cs => ((Construction.eval (m:ℤ) cs)/(n:ℤ)).natAbs
    out.1 = (k left*k right).bits ∧ out.2≤budget len w := by
  let l := cofactor n.bits m.bits (left.map encode)
  let r := cofactor n.bits m.bits (right.map encode)
  have space {xs : List ℤ} (h : xs.length≤len) := (Nat.add_le_add_left
    (Nat.mul_le_mul_right (2*m.size+1) h) height).trans room
  obtain ⟨lv,ll,lg⟩ := cofactor_spec n m left height w pos nw mw lc (space leftLen) ld
  obtain ⟨rv,rl,rg⟩ := cofactor_spec n m right height w pos nw mw rc (space rightLen) rd
  change value l.1=_ at lv
  change value r.1=_ at rv
  change l.1.length≤_ at ll
  change r.1.length≤_ at rl
  change l.2≤_ at lg
  change r.2≤_ at rg
  let z := multiply l.1 r.1
  have ⟨zv,zl,zc⟩ := multiply_spec l.1 r.1
  change value z.1=value r.1*value l.1 at zv
  change z.1.length≤_ at zl
  change z.2≤_ at zc
  have ⟨bits,bw⟩ := canonical_spec z.1
  have mb := zc.trans (Nat.mul_le_mul rl (show _ ≤ w+5*(w+2*w) by omega))
  have bound (x : ℕ) (le : x≤len) : partBudget x w≤partBudget len w := by unfold partBudget; gcongr
  have lc' := lg.trans (bound _ leftLen)
  have rc' := rg.trans (bound _ rightLen)
  refine ⟨?_,?_⟩
  · change (canonical z.1).1=_
    rw [bits,zv,lv,rv,Nat.mul_comm]
  · change l.2+r.2+z.2+(canonical z.1).2+1≤_
    rw [bw]; unfold budget
    nlinarith only [lc',rc',mb,zl,ll,rl]

/-- On every surviving trial in the fixed coefficient box, the cofactor
product costs polynomially many gates in the bit length of the original N. -/
theorem fixed_markModulus {n ell u v x y : ℕ} (hn : 2≤n) (big : 130000≤Fixed.d (n.log2+1))
    (comp : ¬n.Prime) (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (absent : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n)=none)
    (box : let b := n.log2+1
      u≤2*b^2*Fixed.U b*Fixed.A b ∧ v≤2*b^2*Fixed.U b ∧
      x≤2*b^2*Fixed.U b*Fixed.A b ∧ y≤2*b^2*Fixed.U b) :
    let b := n.log2+1
    let pair := construct n ell u v x y
    let out := run n.bits (Fixed.rootBase n).bits (pair.first.map encode) (pair.second.map encode)
    out.1=(markModulus n ell).bits ∧ out.2≤100000*(b+1)^5 ∧ out.2≤2^(30*TwoThirdsCost.scale b) := by
  intro b pair out
  let m := Fixed.rootBase n
  let z := b+1
  let w := 4*z^2+z
  let len := Fixed.d b+1
  have dx := Fixed.degree_le_bits b
  have ln : len≤z := Nat.succ_le_succ dx
  have ns : n.size≤b := Nat.size_le.mpr Nat.lt_log2_self
  have ms : m.size≤z := Nat.size_le.mpr ((Fixed.rootBase_spec hn).2.2.trans_lt
    (Nat.pow_lt_pow_right (by decide : 1<2) (Nat.lt_succ_self b)))
  have zp : 0<z := Nat.succ_pos _
  have zw : z≤w := by unfold w; omega
  have room : z+len*(2*m.size+1)≤w := by
    have bnd := Nat.mul_le_mul ln (show 2*m.size+1≤3*z by omega)
    unfold w; nlinarith only [bnd]
  obtain ⟨lg,rg⟩ := box_polynomialGuards hn big comp target absent box
  obtain ⟨ld,rd⟩ := roots_of_surviving_input hn comp target absent u v x y
  have leftLen : pair.first.length=len := lg.1
  have rightLen : pair.second.length=len := rg.1
  have size {cs : List ℤ} (gs : (TryPair.fixedInput n ell pair).polynomialGuard cs) :
      ∀ c∈cs,c.natAbs.size≤z := fun c hc => Nat.size_le.mpr
        ((gs.2.2.1 c hc).trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self b)))
  obtain ⟨result,c⟩ := run_spec n m pair.first pair.second len z w (by omega) (ns.trans (by unfold z at zw; omega))
    (ms.trans zw) leftLen.le rightLen.le (size lg) (size rg) room ld rd
  change out.1=_ at result
  change out.2≤_ at c
  have exactMod := markModulus_eq n ell u v x y
  have poly : budget len w≤100000*z^5 := by
    have h1 := Nat.le_self_pow (by decide : 5≠0) z
    have h2 := Nat.pow_le_pow_right zp (by decide : 2≤5)
    have h3 := Nat.pow_le_pow_right zp (by decide : 3≤5)
    have h4 := Nat.pow_le_pow_right zp (by decide : 4≤5)
    have h0 := Nat.one_le_pow 5 z zp
    have mono : budget len w ≤ budget z w := by unfold budget partBudget; gcongr
    refine mono.trans ?_
    unfold budget partBudget evalStep w
    nlinarith only [h0,h1,h2,h3,h4]
  refine ⟨?_,c.trans poly,(c.trans poly).trans ?_⟩
  · rw [result,exactMod]
  · let t := TwoThirdsCost.scale b
    have db := Fixed.degree_pos (Nat.succ_pos n.log2)
    have ht : Fixed.h b≤t := (Nat.le_mul_of_pos_left _ db).trans (Fixed.scale_bounds (Nat.succ_pos n.log2)).1
    have zz : b.log2+1≤t := (Nat.le_mul_of_pos_left _ db).trans ht
    have tp : 0<t := by omega
    have bz : b<2^t := Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by decide) zz)
    have zt : z≤2^t := Nat.succ_le_of_lt bz
    calc 100000*z^5 ≤ 2^17*(2^t)^5 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left zt 5)
         _ ≤ 2^(30*t) := by rw [←pow_mul,←pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)

end Cogentic.BinaryCofactor

#print axioms Cogentic.BinaryCofactor.run_spec
#print axioms Cogentic.BinaryCofactor.fixed_markModulus
