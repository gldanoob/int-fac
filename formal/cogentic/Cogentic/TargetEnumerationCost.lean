import Cogentic.CandidateSieveCost

namespace Cogentic.BinaryTargets
open BinaryPresieve BinaryDivision BinaryPivot

/-- Ascending binary cursors produce the target list directly in driver order. -/
def visit (trial : List Unit) : List Unit → List Bool → List (List Bool) × ℕ
  | [], _ => ([],0)
  | _::rest, prev =>
    let q := addDigits prev.length prev [] true
    let test := trialPrime q.1 trial
    let tail := visit trial rest q.1
    (if test.1 then q.1::tail.1 else tail.1,q.2+test.2+tail.2+2)

private theorem visit_spec (trial ts : List Unit) (prev : List Bool) (w : ℕ)
    (start : 0<value prev) (enough : value prev+ts.length≤trial.length+1)
    (work : 2+trial.length≤w) (width : prev.length+ts.length≤w) :
    (visit trial ts prev).1.map value =
      (List.range' (value prev+1) ts.length).filter (fun p=>decide p.Prime) ∧
    (visit trial ts prev).2 ≤ ts.length*(5*w+trial.length*visitBudget w+3) := by
  induction ts generalizing prev with
  | nil => simp [visit]
  | cons tok rest ih =>
    let q := addDigits prev.length prev [] true
    obtain ⟨ql,qc,qv⟩ := addDigits_spec prev.length prev [] true le_rfl (by simp)
    change q.1.length=_ at ql
    change q.2=_ at qc
    change value q.1=value prev+0+1 at qv
    rw [Nat.add_zero] at qv
    simp only [List.length_cons] at width enough ⊢
    obtain ⟨result,cost⟩ := trialPrime_spec q.1 trial (by omega) (by omega) w (by omega) work
    obtain ⟨list,paid⟩ := ih q.1 (by omega) (by omega) (by omega)
    change ((if (trialPrime q.1 trial).1 then q.1::(visit trial rest q.1).1 else (visit trial rest q.1).1).map value = _) ∧
      q.2+(trialPrime q.1 trial).2+(visit trial rest q.1).2+2 ≤ _
    rw [qv] at list result
    constructor
    · rw [List.range'_succ,List.filter_cons,result]
      by_cases h : (value prev+1).Prime <;> simp [h,qv,list]
    · rw [Nat.succ_mul]; omega

private def powBits (depth : List Unit) := depth.foldr (fun _ xs=>false::xs) [true]
private theorem powBits_spec (ts : List Unit) :
    value (powBits ts) = 2^ts.length ∧ (powBits ts).length=ts.length+1 := by
  induction ts with
  | nil => decide
  | cons tok rest ih =>
    change value (false::powBits rest)=_ ∧ (false::powBits rest).length=_
    simp [value,ih,pow_succ,Nat.mul_comm]

def enumerate (depth : List Unit) : List (List Bool) × ℕ :=
  match depth with
  | [] => ([],1)
  | _::rest =>
    let lo := powBits rest
    let fuel := BinarySaturation.tokens lo
    let scan := visit (fuel.1++fuel.1) fuel.1 lo
    (scan.1,scan.2+fuel.2+fuel.1.length+rest.length+2)

private theorem sorted_filter (k : ℕ) :
    ((List.range' (2^k+1) (2^k)).filter (fun p=>decide p.Prime)) = (dyadicTargets (k+1)).sort := by
  let xs := (List.range' (2^k+1) (2^k)).filter (fun p=>decide p.Prime)
  have same : xs.toFinset=dyadicTargets (k+1) := by
    ext p
    simp only [xs,List.mem_toFinset,List.mem_filter,List.mem_range'_1,decide_eq_true_eq,
      mem_dyadicTargets,Nat.add_sub_cancel,pow_succ]
    constructor
    · rintro ⟨⟨lb,ub⟩,hp⟩
      exact ⟨hp,by omega,by omega⟩
    · rintro ⟨hp,lb,ub⟩
      exact ⟨⟨by omega,by omega⟩,hp⟩
  rw [←same]
  exact ((List.toFinset_sort _ ((List.nodup_range' ..).filter _)).mpr
    ((List.pairwise_le_range' (s:=2^k+1) (n:=2^k) 1).filter _)).symm

/-- A polynomial in B=2^β charges generating the binary cursors, the list
traversals, and all division-based primality tests, including composite candidates. -/
theorem enumerate_spec (depth : List Unit) :
    let B := 2^depth.length
    (enumerate depth).1.map value=(dyadicTargets depth.length).sort ∧
      (enumerate depth).2 ≤ 100000*(B+2)^5 := by
  cases depth with
  | nil =>
    have empty : dyadicTargets 0=∅ := by simp [dyadicTargets]
    simp [enumerate,empty]
  | cons tok rest =>
    let lo := powBits rest
    let fuel := BinarySaturation.tokens lo
    let a := 2^rest.length
    have ⟨vl,wl⟩ := powBits_spec rest
    change value lo=a at vl
    change lo.length=rest.length+1 at wl
    have ⟨fl,fc⟩ := BinarySaturation.token_spec lo
    change fuel.1.length=_ at fl
    change fuel.2≤_ at fc
    rw [vl] at fl fc
    let W := 2+2*a
    have cap := Nat.lt_two_pow_self (n:=rest.length)
    have rr : rest.length<a := cap
    have fg : (fuel.1++fuel.1).length=2*a := by simp [fl,two_mul]
    obtain ⟨values,bound⟩ := visit_spec (fuel.1++fuel.1) fuel.1 lo W
      (vl ▸ Nat.two_pow_pos _) (by omega) (by dsimp [W]; omega) (by dsimp [W]; omega)
    rw [vl,fl] at values
    refine ⟨values.trans (sorted_filter rest.length),?_⟩
    change (visit (fuel.1++fuel.1) fuel.1 lo).2+fuel.2+fuel.1.length+rest.length+2 ≤ _
    rw [fg,fl] at bound
    rw [fl,wl] at *
    refine (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add bound fc) _) _) _).trans ?_
    simp only [List.length_cons,pow_succ]
    change a*(5*W+(2*a)*visitBudget W+3)+(a+2*(rest.length+1))+a+rest.length+2 ≤ 100000*(a*2+2)^5
    calc
      _ ≤ a*(5*W+(2*a)*visitBudget W+3)+(a+2*(a+1))+a+a+2 := by gcongr
      _ ≤ _ := by unfold W visitBudget probeBudget BinaryModularPower.gcdBudget; ring_nf; omega

def run (beta : List Bool) : List (List Bool) × ℕ :=
  let depth := BinarySaturation.tokens beta
  let out := enumerate depth.1
  (out.1,depth.2+out.2)

/-- Starting with binary β, produce the exact sorted list consumed by collect. -/
theorem fixed_targets {b : ℕ} (hb : 0<b) :
    let beta := Fixed.beta b
    let out := run beta.bits
    out.1.map value=(dyadicTargets beta).sort ∧ out.2≤2^(6000*Fixed.h b) := by
  let beta := Fixed.beta b
  let B := Fixed.B b
  let h := Fixed.h b
  have hp : 0<h := Nat.mul_pos (Fixed.degree_pos hb) (Nat.succ_pos _)
  have p : 0<beta := Nat.mul_pos (by decide : 0<1000) hp
  have lb : 2≤B := (show 2=2^1 by decide).le.trans (Nat.pow_le_pow_right (by decide) p)
  have bsize : beta.bits.length≤B := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr ((Nat.lt_two_pow_self (n:=beta)).trans_le
      (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.lt_two_pow_self (n:=beta)).le))
  have ⟨len,depth⟩ := BinarySaturation.token_spec beta.bits
  simp only [value_bits] at len depth
  obtain ⟨values,cost⟩ := enumerate_spec (BinarySaturation.tokens beta.bits).1
  rw [len] at values cost
  refine ⟨values,(Nat.add_le_add_right depth _).trans ?_⟩
  have bB : beta≤B := (Nat.lt_two_pow_self (n:=beta)).le
  change beta+2*beta.bits.length+(enumerate (BinarySaturation.tokens beta.bits).1).2 ≤ _
  have slack : B+2≤2*B := by omega
  calc
    _ ≤ 3*B+100000*(2*B)^5 := by
      have mono := Nat.pow_le_pow_left slack 5
      change _ ≤ 100000*(B+2)^5 at cost
      omega
    _ ≤ 2^22*B^5 := by have mono := Nat.le_self_pow (by decide : 5≠0) B; ring_nf; omega
    _ = 2^(22+5*beta) := by dsimp [B,Fixed.B,beta,Fixed.beta]; rw [pow_add,←pow_mul]; ring_nf
    _ ≤ 2^(6000*h) := Nat.pow_le_pow_right (by decide) (by change 22+5*(1000*h)≤6000*h; omega)

end Cogentic.BinaryTargets

#print axioms Cogentic.BinaryTargets.fixed_targets
