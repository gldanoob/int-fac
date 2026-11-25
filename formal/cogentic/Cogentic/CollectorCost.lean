import Cogentic.IndexCapCost
import Cogentic.TotalFactor

namespace Cogentic.BinaryCollector
open BinaryDivision BinaryPivot BinaryModularPower BinarySaturation TwoThirdsSearch

/-- Keep the accumulator canonical across successive LCMs. -/
def lcmBits (x y : List Bool) : List Bool × ℕ :=
  let g := gcdBits x y
  let q := divide g.1 x
  let p := multiply y q.quotient
  let out := canonical p.1
  (out.1,g.2+q.gates+p.2+out.2)

def lcmBudget (w : ℕ) := gcdBudget w+w*(20*w+1)+16*w^2+9*w

theorem lcm_spec (x y w : ℕ) (pos : 0 < x) (hx : x.size ≤ w) (hy : y.size ≤ w) :
    (lcmBits x.bits y.bits).1=(x.lcm y).bits ∧ (lcmBits x.bits y.bits).2 ≤ lcmBudget w := by
  let g := gcdBits x.bits y.bits
  let q := divide g.1 x.bits
  let p := multiply y.bits q.quotient
  obtain ⟨gv,gl,gc⟩ := gcd_gates x y w hx hy
  change value g.1=x.gcd y at gv
  change g.1.length ≤ w at gl
  have gp : 0 < value g.1 := gv ▸ Nat.gcd_pos_of_pos_left _ pos
  obtain ⟨_,_,eq,small,qc⟩ := divide_spec g.1 x.bits gp
  change value x.bits=value q.quotient*value g.1+value q.remainder at eq
  simp only [value_bits] at eq
  have qv : value q.quotient=x/value g.1 := by
    rw [eq,Nat.mul_comm (value q.quotient),Nat.mul_add_div gp,Nat.div_eq_of_lt small,Nat.add_zero]
  have ql : q.quotient.length=x.size := (BinaryIndexCap.quotient_length ..).trans (Nat.size_eq_bits_len x)
  obtain ⟨pv,pl,pc⟩ := multiply_spec y.bits q.quotient
  change value p.1=_ at pv
  change p.1.length ≤ _ at pl
  change p.2 ≤ _ at pc
  rw [qv,gv,value_bits] at pv
  rw [ql,Nat.size_eq_bits_len] at pl pc
  have pval : value p.1=x.lcm y := by
    rw [pv,Nat.lcm_comm x,Nat.lcm,Nat.mul_div_assoc _ (Nat.gcd_dvd_right ..),Nat.gcd_comm]
    exact Nat.mul_comm ..
  obtain ⟨out,cost⟩ := canonical_spec p.1
  have qCost : q.gates ≤ w*(20*w+1) := qc.trans (by rw [Nat.size_eq_bits_len]; apply Nat.mul_le_mul hx; omega)
  have pCost : p.2 ≤ 16*w^2 := pc.trans (calc
    _ ≤ w*(w+5*(w+2*w)) := by gcongr
    _ = _ := by ring)
  have cCost : (canonical p.1).2 ≤ 9*w := by rw [cost]; omega
  change _ ∧ g.2+q.gates+p.2+(canonical p.1).2 ≤ _
  change g.2 ≤ gcdBudget w at gc
  exact ⟨out.trans (congrArg Nat.bits pval), by unfold lcmBudget; omega⟩

inductive Payload where
  | divisor (d : ℕ)
  | orders (common : List Bool) (retained : List ℕ)
  deriving DecidableEq

def encode {n : ℕ} : Output n → Payload
  | .divisor d _ => .divisor d
  | .orders e _ _ retained _ => .orders e.bits retained

structure Result where
  output : Payload
  calls : ℕ
  overhead : ℕ

/-- The probe supplies its checked hit and pair-call count. Charge dispatch,
retention and binary arithmetic as each successful exponent is folded in. -/
def run {n : ℕ} (search : (g : ℕ) → Probe (Hit n g)) : List ℕ → Result
  | [] => ⟨.orders [false,true] [],0,0⟩
  | g::gs =>
    let head := search g
    match head.answer with
    | some (.divisor d _) => ⟨.divisor d,head.calls,1⟩
    | none =>
      let tail := run search gs
      ⟨tail.output,head.calls+tail.calls,tail.overhead+1⟩
    | some (.exponent e _) =>
      let tail := run search gs
      match tail.output with
      | .divisor d => ⟨.divisor d,head.calls+tail.calls,tail.overhead+2⟩
      | .orders m retained =>
        let next := lcmBits e.bits m
        ⟨.orders next.1 (g::retained),head.calls+tail.calls,tail.overhead+next.2+3⟩

theorem run_spec {n : ℕ} (hn : 2 ≤ n) (search : (g : ℕ) → Probe (Hit n g)) (t T : ℕ)
    (bounded : ∀ g h, (search g).answer=some h → h.exponentLe (2^t)) (gs : List ℕ)
    (lengthBound : gs.length ≤ T) :
    let w := 2+t*(T+1)
    (run search gs).output=encode (collect hn search gs).1 ∧
      (run search gs).calls=(collect hn search gs).2 ∧
      (run search gs).overhead ≤ gs.length*(lcmBudget w+3) := by
  let w := 2+t*(T+1)
  change _ ∧ _ ∧ _ ≤ gs.length*(lcmBudget w+3)
  induction gs with
  | nil => exact ⟨rfl,rfl,by simp [run]⟩
  | cons g gs ih =>
    have len : gs.length ≤ T := (Nat.le_succ _).trans lengthBound
    obtain ⟨output,calls,overhead⟩ := ih len
    have step : (run search gs).overhead+(lcmBudget w+3) ≤ (g::gs).length*(lcmBudget w+3) := by
      rw [List.length_cons,Nat.succ_mul]; omega
    cases hit : (search g).answer with
    | none =>
      simp only [run,collect,hit]
      exact ⟨output,congrArg ((search g).calls+·) calls,by omega⟩
    | some h =>
      cases h with
      | divisor d good =>
        simp only [run,collect,hit,encode]
        exact ⟨trivial,trivial,by omega⟩
      | exponent e good =>
        have eBound := bounded g _ hit
        change e ≤ 2^t at eBound
        have ew : e.size ≤ w := by
          apply Nat.size_le.mpr
          have exp : t+1 ≤ w := by dsimp [w]; rw [Nat.mul_succ]; omega
          exact (show e < 2^(t+1) by rw [pow_succ]; have := Nat.one_le_two_pow (n:=t); omega).trans_le
            (Nat.pow_le_pow_right (by decide) exp)
        have tail := collect_exponentLe hn search gs (by positivity : 0 < 2^t) bounded
        cases result : (collect hn search gs).1 with
        | divisor d proof =>
          rw [result] at output
          simp only [encode] at output
          simp only [run,collect,hit,output,result]
          exact ⟨rfl,congrArg ((search g).calls+·) calls,by omega⟩
        | orders m big even retained valid =>
          rw [result] at tail output
          change m ≤ 2*(2^t)^gs.length at tail
          simp only [encode] at output
          have mw : m.size ≤ w := by
            apply Nat.size_le.mpr
            rw [←pow_mul,Nat.mul_comm 2,←pow_succ] at tail
            have ex : t*gs.length+1+1 ≤ w := by
              have := Nat.mul_le_mul_left t len
              dsimp [w]; rw [Nat.mul_succ]; omega
            exact (show m < 2^(t*gs.length+1+1) by
              rw [pow_succ]; have := Nat.one_le_two_pow (n:=t*gs.length+1); omega).trans_le
              (Nat.pow_le_pow_right (by decide) ex)
          have ⟨eq,cost⟩ := lcm_spec e m w (by have := good.1; omega) ew mw
          simp only [run,collect,hit,output,result,eq]
          exact ⟨rfl,congrArg ((search g).calls+·) calls,by omega⟩

/-- Charge each visited target its own search work. A returned divisor stops
the traversal immediately, as in the arithmetic collector. -/
def probeWork {n : ℕ} (search : (g : ℕ) → Probe (Hit n g)) (charge : ℕ → ℕ) : List ℕ → ℕ
  | [] => 0
  | g::gs =>
    match (search g).answer with
    | some (.divisor ..) => charge g
    | _ => charge g+probeWork search charge gs

theorem probeWork_le {n : ℕ} (search : (g : ℕ) → Probe (Hit n g)) (charge : ℕ → ℕ)
    (gs : List ℕ) {P : ℕ} (perProbe : ∀ g ∈ gs, charge g ≤ P) :
    probeWork search charge gs ≤ gs.length*P := by
  induction gs with
  | nil => simp [probeWork]
  | cons g gs ih =>
    have h := perProbe g (by simp)
    have tail := ih (fun q hq => perProbe q (by simp [hq]))
    simp only [List.length_cons,Nat.succ_mul]
    cases hit : (search g).answer with
    | none => simp only [probeWork,hit]; omega
    | some h => cases h <;> simp only [probeWork,hit] <;> omega

theorem total_work_le {n : ℕ} (hn : 2 ≤ n) (search : (g : ℕ) → Probe (Hit n g)) (t : ℕ)
    (bounded : ∀ g h, (search g).answer=some h → h.exponentLe (2^t)) (gs : List ℕ)
    (charge : ℕ → ℕ) {P : ℕ} (perProbe : ∀ g ∈ gs, charge g ≤ P) :
    (run search gs).overhead+probeWork search charge gs ≤
      gs.length*(lcmBudget (2+t*(gs.length+1))+3+P) := by
  have cost := (run_spec hn search t gs.length bounded gs le_rfl).2.2
  rw [Nat.mul_add]
  exact Nat.add_le_add cost (probeWork_le search charge gs perProbe)

def fixed (n : ℕ) :=
  let b := n.log2+1
  run (searchBox n (2*b^2*Fixed.U b*Fixed.A b) (2*b^2*Fixed.U b) (Concrete.candidate n))
    (dyadicTargets (Fixed.beta b)).sort

/-- Canonical output, retained targets and pair-attempt counts agree with the
driver's verified collection. The overhead includes every intermediate LCM
arising on the actual path, including the final normalization of each one. -/
theorem fixed_collector {n : ℕ} (hn : 2 ≤ n) :
    (fixed n).output=encode (Concrete.fixedCollection n hn).1 ∧
    (fixed n).calls=(Concrete.fixedCollection n hn).2 ∧
    (fixed n).overhead ≤ 2^(8000*TwoThirdsCost.scale (n.log2+1)) := by
  let b := n.log2+1
  let t := Fixed.precision b
  let gs := (dyadicTargets (Fixed.beta b)).sort
  let search := searchBox n (2*b^2*Fixed.U b*Fixed.A b) (2*b^2*Fixed.U b) (Concrete.candidate n)
  have bound (g : ℕ) : ∀ h, (search g).answer=some h → h.exponentLe (2^t) :=
    searchBox_exponentLe _ _ _ _ _ _ (fun a j c k e => TryPair.attempt_bound _ _ _ g a j c k e)
  have ⟨result,calls,work⟩ := run_spec hn search t gs.length bound gs le_rfl
  refine ⟨result,calls,work.trans ?_⟩
  let s := TwoThirdsCost.scale b
  let w := 2+t*(gs.length+1)
  have hb : 0 < b := Nat.succ_pos _
  have d := Fixed.degree_pos hb
  have vs := (Fixed.scale_bounds hb).1
  have hs : Fixed.h b ≤ s := (Nat.le_mul_of_pos_left _ d).trans vs
  have zs : Fixed.z b ≤ s := (Nat.le_mul_of_pos_left _ d).trans hs
  have sp : 0 < s := (Nat.succ_pos b.log2).trans_le zs
  have len : gs.length ≤ Fixed.B b := by simpa only [gs,Finset.length_sort] using Fixed.target_card b
  have T : gs.length ≤ 2^(1000*s) := len.trans
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 1000 hs))
  have prec : t ≤ 2^(1013*s) := (Fixed.precision_bound b).trans
    (Nat.pow_le_pow_right (by decide) (by unfold Fixed.beta; omega))
  have product : t*gs.length ≤ 2^(2013*s) := (Nat.mul_le_mul prec T).trans_eq (by
    rw [←pow_add]; congr 1; ring)
  have prec' : t ≤ 2^(2013*s) := prec.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have wp : 1 ≤ w := by dsimp [w]; omega
  have ww : w ≤ 2^(2015*s) := calc
    _ ≤ 4*2^(2013*s) := by dsimp [w]; rw [Nat.mul_succ]; have := Nat.one_le_two_pow (n:=2013*s); omega
    _ = 2^(2+2013*s) := (Nat.pow_add 2 2 _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have budget : lcmBudget w+3 ≤ 2^8*w^3 := by
    unfold lcmBudget gcdBudget
    have h1 := Nat.le_self_pow (n:=2) (by decide) w
    have h2 : w^2 ≤ w^3 := Nat.pow_le_pow_right wp (by decide)
    nlinarith
  change gs.length*(lcmBudget w+3) ≤ 2^(8000*s)
  calc gs.length*(lcmBudget w+3) ≤ 2^(1000*s)*(2^8*(2^(2015*s))^3) := by gcongr; exact budget.trans (by gcongr)
       _ = 2^(1000*s+(8+2015*s*3)) := by rw [←pow_mul,←pow_add,←pow_add]
       _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

end Cogentic.BinaryCollector

#print axioms Cogentic.BinaryCollector.total_work_le
#print axioms Cogentic.BinaryCollector.fixed_collector
