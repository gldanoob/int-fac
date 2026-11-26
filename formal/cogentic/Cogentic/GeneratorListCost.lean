import Cogentic.ScheduleWords
import Cogentic.ConstructorGridCost

namespace Cogentic.BinaryGenerators
open BinarySchedule BinarySaturation BinaryDivision BinaryConstructorGrid

/-- Flattening a Cartesian power of a unary list gives a clock of exactly the
polynomial cutoff length, including the one token for the zeroth power. -/
private def powerClock (xs : List Unit) : ℕ → List Unit × ℕ
  | 0 => ([()],1)
  | k+1 =>
    let t := powerClock xs k
    let r := copies t.1 xs
    (r.1,t.2+r.2+1)

private theorem powerClock_spec (xs : List Unit) (m : ℕ) :
    (powerClock xs m).1.length = xs.length^m ∧
    (powerClock xs m).2 ≤ (3*m+1)*(xs.length+1)^m := by
  induction m with
  | zero => simp [powerClock]
  | succ m ih =>
    obtain ⟨l,w⟩ := copies_spec (powerClock xs m).1 xs
    rw [ih.1] at l w
    have step := Nat.pow_le_pow_left (Nat.le_succ xs.length) m
    have p := Nat.one_le_pow m (xs.length+1) (by omega)
    constructor
    · simpa only [powerClock,pow_succ,Nat.mul_comm] using l
    · change (powerClock xs m).2 + (copies _ xs).2 + 1 ≤ _
      rw [w,pow_succ]
      nlinarith only [ih.2,Nat.mul_le_mul_left xs.length step,Nat.mul_le_mul_left xs.length p,
        Nat.mul_le_mul_left ((3*m+1)*(xs.length+1)^m) (Nat.le_succ xs.length),p]

/-- Generate the actual words passed to the primality and splitter guards.
The fixed generator constant is part of the algorithm, and the other argument
is its already computed binary input length. -/
def run (k : ℕ) (lengthBits : List Bool) : List (List Bool) × ℕ :=
  let bs := tokens lengthBits
  let seed := () :: List.replicate k () ++ bs.1
  let base := copies seed (List.replicate 1000 ())
  let clock := powerClock base.1 6
  let out := progression (1:ℕ).bits clock.1 (1:ℕ).bits
  (out.1,bs.2+2*k+1003+base.2+clock.2+out.2)

theorem fixed_list (k b : ℕ) (hb : 0<b) (hk : k≤b) :
    (run k b.bits).1 = (List.range' 1 (polyCutoff k b)).map Nat.bits ∧
    (run k b.bits).2 ≤ 2^(300*TwoThirdsCost.scale b) := by
  let S := TwoThirdsCost.scale b
  let seed := () :: List.replicate k () ++ (tokens b.bits).1
  let base := copies seed (List.replicate 1000 ())
  let cap := polyCutoff k b
  let u := 1000*(k+b+1)
  have ⟨bl,bc⟩ := token_spec b.bits
  simp only [value_bits,Nat.size_eq_bits_len] at bl bc
  have se : seed.length=k+b+1 := by simp [seed,bl,Nat.add_assoc]
  obtain ⟨len,gates⟩ := copies_spec seed (List.replicate 1000 ())
  change base.1.length=_ at len
  change base.2=_ at gates
  simp only [List.length_replicate,se] at len gates
  obtain ⟨size,cost⟩ := powerClock_spec base.1 6
  rw [len] at size cost
  change (powerClock base.1 6).1.length=cap at size
  let cpu := progression (1:ℕ).bits (powerClock base.1 6).1 (1:ℕ).bits
  have zle : Fixed.z b≤S := (Nat.le_mul_of_pos_left _ (Fixed.degree_pos hb)).trans
    ((Nat.le_mul_of_pos_left _ (Fixed.degree_pos hb)).trans (Fixed.scale_bounds hb).1)
  have sp : 0<S := (Nat.succ_pos _).trans_le zle
  have bw : b ≤ 2^S := Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right Nat.zero_lt_two zle)
  have pb := Nat.two_pow_pos S
  have ub : u+1 ≤ 2^(13+S) := by dsimp only [u]; rw [pow_add]; norm_num; omega
  let X := 2^(90*S)
  have hX : cap+1 ≤ X := by
    have e : cap≤2^((13+S)*6) := (Nat.pow_le_pow_left (Nat.le_of_succ_le ub) 6).trans_eq (Nat.pow_mul ..).symm
    calc
      _ ≤ 2^(1+(13+S)*6) := by rw [pow_add,pow_one,two_mul]; have := Nat.two_pow_pos ((13+S)*6); omega
      _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  have wu : (u+1)^6 ≤ X := (Nat.pow_le_pow_left ub 6).trans
    ((Nat.pow_mul ..).symm.le.trans (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
  have wsub : u≤X := (Nat.le_of_succ_le ub).trans (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
  have sb : b.size ≤ b := Nat.size_le.mpr Nat.lt_two_pow_self
  obtain ⟨values,work⟩ := progression_spec 1 1 (powerClock base.1 6).1 X
    ((by decide : (1:ℕ).size=1) ▸ Nat.two_pow_pos (90*S))
    (by simpa only [size,Nat.mul_one,Nat.add_comm 1] using ((Nat.size_le.mpr Nat.lt_two_pow_self : (cap+1).size≤cap+1).trans hX))
  change cpu.1=_ at values; change cpu.2≤_ at work
  rw [size] at values work
  change cpu.1=_ ∧ (tokens b.bits).2+2*k+1003+base.2+(powerClock base.1 6).2+cpu.2≤_
  refine ⟨values,?_⟩
  have bX : b≤X := bw.trans (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
  change (powerClock base.1 6).2≤19*(u+1)^6 at cost
  have h := cost.trans (Nat.mul_le_mul_left 19 wu)
  have total : (tokens b.bits).2+2*k+1003+base.2+(powerClock base.1 6).2+cpu.2≤2048*(X+1)^2 := by
    rw [gates]; dsimp only [u] at wsub
    nlinarith only [bc,sb,bX,hk,work,Nat.mul_le_mul_right (9*X+6) (Nat.le_of_succ_le hX),h,wsub,sq_nonneg X]
  have xp := Nat.two_pow_pos (90*S)
  calc
    _ ≤ 2048*(X+1)^2 := total
    _ ≤ 2048*(2*X)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    _ = 2^(13+90*S*2) := by dsimp only [X]; rw [pow_add,pow_mul 2 (90*S) 2]; ring
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by change 13+90*S*2≤300*S; omega)

end Cogentic.BinaryGenerators

#print axioms Cogentic.BinaryGenerators.fixed_list
