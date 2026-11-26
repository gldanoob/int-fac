import Cogentic.LeadingCoefficientCost
import Cogentic.ConstructorGridCost

namespace Cogentic.BinaryBox
open BinaryDivision BinarySaturation BinaryLeading BinaryConstructorGrid

/-- Build one coordinate list once, in the order used by the four scans. -/
def axis (bound : List Bool) : List (List Bool) × ℕ :=
  let clock := tokens bound
  let out := progression [true] clock.1 [true]
  (out.1,clock.2+out.2)

private theorem axis_spec (a W : ℕ) (ha : a ≤ W) :
    (axis a.bits).1=(List.range' 1 a).map Nat.bits ∧
      (axis a.bits).2 ≤ 20*(W+1)^2 := by
  obtain ⟨len,work⟩ := token_spec a.bits
  simp only [value_bits,Nat.size_eq_bits_len] at len work
  have self (j : ℕ) : j.size≤j := Nat.size_le.mpr Nat.lt_two_pow_self
  have room : (1+(tokens a.bits).1.length*1).size ≤ W+1 := by
    rw [len,mul_one,Nat.add_comm]; exact (self _).trans (Nat.succ_le_succ ha)
  obtain ⟨v,g⟩ := progression_spec 1 1 (tokens a.bits).1 (W+1) (by change 1≤W+1; omega) room
  rw [len] at v g
  refine ⟨v,?_⟩
  change (tokens a.bits).2 + (progression (1:ℕ).bits (tokens a.bits).1 (1:ℕ).bits).2 ≤ _
  have estimate := (Nat.add_le_add work g).trans (show a+2*a.size+(1+a*(9*(W+1)+6)) ≤
    W+2*W+(1+W*(9*(W+1)+6)) by gcongr; exact (self a).trans ha)
  exact estimate.trans (by ring_nf; omega)

/-- Both copies of each axis in a tuple reuse the same list. -/
def axes (b U A : List Bool) : (List (List Bool) × List (List Bool)) × ℕ :=
  let f := product [[false,true],b,b,U]
  let s := product [f.1,A]
  let fast := axis f.1
  let slow := axis s.1
  ((slow.1,fast.1),f.2+s.2+fast.2+slow.2+1)

theorem fixed_axes {b : ℕ} (bp : 0<b) :
    let fast := 2*b^2*Fixed.U b
    let slow := fast*Fixed.A b
    let out := axes b.bits (Fixed.U b).bits (Fixed.A b).bits
    out.1=((List.range' 1 slow).map Nat.bits,(List.range' 1 fast).map Nat.bits) ∧
      out.2 ≤ 2^(220020*TwoThirdsCost.scale b) := by
  intro fast slow out
  let S := TwoThirdsCost.scale b
  let X := 2^(110003*S)
  have ds := Fixed.degree_pos bp
  have vs : Fixed.v b≤S := (Fixed.scale_bounds bp).1
  have hs : Fixed.h b≤S := (Nat.le_mul_of_pos_left _ ds).trans vs
  have zs : Fixed.z b≤S := (Nat.le_mul_of_pos_left _ ds).trans hs
  have sp : 0<S := (Nat.succ_pos _).trans_le zs
  have bits : b≤2^S := Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right Nat.zero_lt_two zs)
  have posU : 0<Fixed.U b := Nat.two_pow_pos _
  have posA : 0<Fixed.A b := Nat.two_pow_pos _
  have fp : 0<fast := by dsimp only [fast]; positivity
  have large : slow≤X := calc
    _ ≤ 2*(2^S)^2*(2^(100000*S))*(2^(10000*S)) := by
      dsimp only [slow,fast,Fixed.U,Fixed.A]; gcongr <;> decide
    _ = 2^(1+2*S+100000*S+10000*S) := by rw [show 2*(2^S)^2=2^(1+2*S) by rw [pow_add,pow_one,←pow_mul,Nat.mul_comm S 2],←pow_add,←pow_add]
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  have small : fast≤X := (Nat.le_mul_of_pos_right _ posA).trans large
  have prodF : [2,b,b,Fixed.U b].prod=fast := by simp [fast]; ring
  have prodS : [fast,Fixed.A b].prod=slow := by simp [slow]
  obtain ⟨fw,fg⟩ := product_spec [2,b,b,Fixed.U b] X (by simp [bp,posU]) (by rw [prodF]; exact small)
  obtain ⟨sw,sg⟩ := product_spec [fast,Fixed.A b] X (by simp [fp,posA]) (by rw [prodS]; exact large)
  rw [prodF] at fw
  rw [prodS] at sw
  simp only [List.map_cons,List.map_nil,List.length_cons,List.length_nil] at fw sw fg sg
  obtain ⟨f,fc⟩ := axis_spec fast X small
  obtain ⟨s,sc⟩ := axis_spec slow X large
  rw [←fw] at sw sg
  dsimp only [axes,out]
  have val : [false,true]=(2:ℕ).bits := rfl
  rw [val]
  refine ⟨by rw [sw,fw,s,f],?_⟩
  rw [←fw] at fc
  rw [←sw] at sc
  calc
    _ ≤ 2^8*(X+1)^2 := by have : 0<(X+1)^2 := Nat.pow_pos (Nat.succ_pos _); omega
    _ ≤ 2^8*(2*X)^2 := by gcongr; have : 0<X := Nat.two_pow_pos _; omega
    _ = 2^(8+(1+110003*S)*2) := by rw [show 2*X=2^(1+110003*S) by rw [pow_add,pow_one],←pow_mul,←pow_add]
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)

end Cogentic.BinaryBox

#print axioms Cogentic.BinaryBox.fixed_axes
