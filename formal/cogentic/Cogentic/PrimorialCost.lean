import Cogentic.PreliminaryRoundingCost

namespace Cogentic.BinaryPrimorial
open BinaryDivision BinaryPivot BinarySaturation BinaryPresieve BinaryPreliminary

structure State where
  cursor : List Bool
  product : List Bool
  gates : ℕ

/-- Test every successive possible prime and maintain the canonical primorial. -/
def scan (trial : List Unit) : List Unit → State
  | [] => ⟨[true],[true],1⟩
  | _::ts =>
    let prev := scan trial ts
    let plus := addDigits prev.cursor.length prev.cursor [] true
    let q := canonical plus.1
    let prime := trialPrime q.1 trial
    let prod := if prime.1 then natProduct prev.product q.1 else (prev.product,0)
    ⟨q.1,prod.1,prev.gates+plus.2+q.2+prime.2+prod.2+3⟩

private theorem primorial_step (j : ℕ) :
    primorial (j+1)=if (j+1).Prime then primorial j*(j+1) else primorial j := by
  unfold primorial
  rw [Finset.range_add_one,Finset.filter_insert]
  by_cases prime : (j+1).Prime <;> simp [prime,Nat.mul_comm]

private def stepBudget (d W : ℕ) := 9*W+d*visitBudget W+30*(W+1)^2+9

private theorem scan_spec (trial ts : List Unit) (d : ℕ) (length : trial.length=d)
    (room : ts.length+1 ≤ d) :
    let out := scan trial ts
    let j := ts.length+1
    out.cursor=j.bits ∧ out.product=(primorial j).bits ∧ out.gates ≤ 1+ts.length*stepBudget d (2*d+4) := by
  induction ts with
  | nil => simp [scan,show (1:ℕ).bits=[true] by decide]
  | cons t ts ih =>
    simp only [List.length_cons] at room
    let j := ts.length+1
    let W := 2*d+4
    let prev := scan trial ts
    obtain ⟨cv,pv,pc⟩ := ih (by omega)
    change prev.cursor=j.bits at cv
    change prev.product=(primorial j).bits at pv
    change prev.gates ≤ _ at pc
    let plus := addDigits prev.cursor.length prev.cursor [] true
    let q := canonical plus.1
    let prime := trialPrime q.1 trial
    obtain ⟨al,ac,av⟩ := addDigits_spec prev.cursor.length prev.cursor [] true le_rfl (by simp)
    change plus.1.length=_ at al
    change plus.2=_ at ac
    change value plus.1=_ at av
    rw [cv,value_bits] at av
    simp only [value,Nat.add_zero,Bool.toNat_true] at av
    obtain ⟨qv,qc⟩ := canonical_spec plus.1
    change q.1=_ at qv
    change q.2=_ at qc
    rw [av] at qv
    have val : value q.1=j+1 := by rw [qv,value_bits]
    have sw : (j+1).size ≤ W := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp [j,W]; omega)
    have pw : (primorial j).size ≤ W := by
      have po : primorial j ≤ 2^(2*j) := by simpa only [show 4=2^2 by decide,←pow_mul] using primorial_le_four_pow j
      have sz := Nat.size_le_size po
      rw [Nat.size_pow] at sz
      dsimp only [j,W] at *; omega
    have ⟨test,tg⟩ := trialPrime_spec q.1 trial (by rw [val]; dsimp [j]; omega)
      (by rw [val,length]; dsimp [j]; omega) W (by rw [qv,Nat.size_eq_bits_len]; exact sw) (by rw [length]; unfold W; omega)
    change prime.1=_ at test
    change prime.2 ≤ _ at tg
    rw [val] at test
    rw [length] at tg
    obtain ⟨pr,_,pg⟩ := natProduct_spec (primorial j) (j+1) pw sw
    rw [←pv,←qv] at pr pg
    have cur : prev.cursor.length ≤ W := by rw [cv,Nat.size_eq_bits_len]; exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp [j,W]; omega)
    rw [al] at qc
    change q.1=(j+1).bits ∧ (if prime.1 then natProduct prev.product q.1 else (prev.product,0)).1=(primorial (j+1)).bits ∧
      prev.gates+plus.2+q.2+prime.2+(if prime.1 then natProduct prev.product q.1 else (prev.product,0)).2+3 ≤ _
    rw [test,primorial_step,List.length_cons,Nat.succ_mul ts.length]
    unfold stepBudget at pc ⊢
    dsimp only [W] at tg pg cur
    by_cases p : (j+1).Prime
    · simp only [p,decide_true,if_true]
      exact ⟨qv,pr,by omega⟩
    · simp only [p,decide_false,Bool.false_eq_true,if_false]
      exact ⟨qv,pv,by omega⟩

def run (degree : List Bool) : List Bool × ℕ :=
  let fuel := tokens degree
  let out := scan fuel.1 fuel.1.tail
  (out.product,fuel.2+out.gates+2)

theorem run_spec (d : ℕ) (dp : 0<d) :
    (run d.bits).1=(primorial d).bits ∧ (run d.bits).2 ≤ 1000000*(d+1)^5 := by
  let fuel := tokens d.bits
  obtain ⟨fl,fc⟩ := token_spec d.bits
  change fuel.1.length=_ at fl
  change fuel.2 ≤ _ at fc
  simp only [value_bits,Nat.size_eq_bits_len] at fl fc
  have tl : fuel.1.tail.length=d-1 := by simp [fl]
  obtain ⟨_,v,c⟩ := scan_spec fuel.1 fuel.1.tail d fl (by rw [tl]; omega)
  rw [tl,show d-1+1=d by omega] at v
  rw [tl] at c
  have sd : d.size ≤ d := Nat.size_le.mpr Nat.lt_two_pow_self
  change (scan fuel.1 fuel.1.tail).product=_ ∧ fuel.2+(scan fuel.1 fuel.1.tail).gates+2 ≤ _
  refine ⟨v,?_⟩
  have cost := c.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le d 1)) 1)
  unfold stepBudget visitBudget probeBudget BinaryModularPower.gcdBudget at cost
  nlinarith only [cost,fc,sd,Nat.zero_le d,Nat.zero_le (d^2),Nat.zero_le (d^3),Nat.zero_le (d^4),Nat.zero_le (d^5)]

theorem fixed_primorial {b : ℕ} (hb : 0<b) :
    (run (Fixed.d b).bits).1=(primorial (Fixed.d b)).bits ∧
    (run (Fixed.d b).bits).2 ≤ 2^(25*TwoThirdsCost.scale b) := by
  obtain ⟨eq,cost⟩ := run_spec _ (Fixed.degree_pos hb)
  let S := TwoThirdsCost.scale b
  have zs : Fixed.z b ≤ S := (Nat.le_mul_of_pos_left _ (Fixed.degree_pos hb)).trans
    ((Nat.le_mul_of_pos_left _ (Fixed.degree_pos hb)).trans (Fixed.scale_bounds hb).1)
  have pos : 0<S := (Nat.succ_pos _).trans_le zs
  have bd := (Nat.succ_le_succ (Fixed.degree_le_bits b)).trans
    (Nat.succ_le_of_lt (Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two zs)))
  refine ⟨eq,cost.trans ((Nat.mul_le_mul (by decide : 1000000 ≤ 2^20) (Nat.pow_le_pow_left bd 5)).trans ?_)⟩
  rw [←pow_mul,←pow_add]; exact Nat.pow_le_pow_right Nat.zero_lt_two (by omega)

end Cogentic.BinaryPrimorial

#print axioms Cogentic.BinaryPrimorial.fixed_primorial
