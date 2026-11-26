import Cogentic.LeadingCoefficientCost
import Cogentic.ScheduleWords
import Cogentic.HelmertCost

namespace Cogentic.BinaryPrecision
open BinarySchedule BinaryDivision BinarySaturation BinaryLeading

/-- Compute the precision and the rational-reconstruction denominator bound
once from the retained rows and the two shared schedule words. -/
def run {α : Type*} (b d : List Bool) (rows : List α) : (List Bool × List Bool) × ℕ :=
  let r := lengthWord (false :: rows.map fun _ => false)
  let p := product [(64:ℕ).bits,d,d,d,r.1,b]
  let e := product [(3:ℕ).bits,d,r.1,b]
  let clock := tokens e.1
  let q := shiftOne clock.1
  ((p.1,q.1),rows.length+1+r.2+p.2+e.2+clock.2+q.2+3)

theorem fixed_words {n g : ℕ} {pair : TryPair.PairData} {rel : Marking.Relations}
    (marked : Marking.stageOne (TryPair.fixedInput n g pair)=some rel) :
    let b := n.log2+1
    let s := TryPair.fixedInput n g pair
    let out := run b.bits (Fixed.d b).bits rel.rows
    out.1=((min (TryPair.localBits s rel) (Fixed.precision b)).bits,(TryPair.denominatorCap s rel).bits) ∧
      out.2 ≤ 2^(2040*TwoThirdsCost.scale b) := by
  intro b s out
  let d := Fixed.d b
  let r := rel.rows.length+1
  let P := TryPair.localBits s rel
  let E := 3*d*r*b
  let S := TwoThirdsCost.scale b
  let X := 2^(1013*S)
  have bp : 0<b := Nat.succ_pos _
  have dp : 0<d := Fixed.degree_pos bp
  have rp : 0<r := Nat.succ_pos _
  have vp : 0<Fixed.v b := Nat.mul_pos dp (Nat.mul_pos dp (Nat.succ_pos _))
  have sp := vp.trans_le (Fixed.scale_bounds bp).1
  change 0<S at sp
  have pmax : P≤X := BinaryHelmert.fixed_local_bits marked
  have pval : P=64*d^3*r*b := rfl
  have ep : E≤P := by
    rw [pval]
    apply Nat.mul_le_mul_right
    apply Nat.mul_le_mul_right
    exact Nat.mul_le_mul (by decide) (Nat.le_self_pow (by decide) _)
  have row : r≤X := (show r≤E by
    calc r ≤ 3*d*r := Nat.le_mul_of_pos_left _ (by positivity)
         _ ≤ E := Nat.le_mul_of_pos_right _ bp).trans (ep.trans pmax)
  have cap : P≤Fixed.precision b := by
    change 64*d^3*r*b ≤ 64*d^3*(2*d*Fixed.B b+1)*b
    have bound := retained_root_row_cap marked
    dsimp only [r]; gcongr; exact bound
  let header := lengthWord (false :: rel.rows.map fun _ => false)
  obtain ⟨rv,rg⟩ := lengthWord_spec (false :: rel.rows.map fun _ => false)
  simp only [List.length_cons,List.length_map] at rv rg
  change header.1=r.bits at rv
  change header.2≤8*(r+1)^2 at rg
  have p : [64,d,d,d,r,b].prod=P := by simp [pval]; ring
  have e : [3,d,r,b].prod=E := by simp [E]; ring
  obtain ⟨pv,pg⟩ := product_spec [64,d,d,d,r,b] X (by simp [dp,rp,bp]) (by rw [p]; exact pmax)
  obtain ⟨ev,eg⟩ := product_spec [3,d,r,b] X (by simp [dp,rp,bp]) (by rw [e]; exact ep.trans pmax)
  rw [p] at pv
  rw [e] at ev
  simp only [List.map_cons,List.map_nil,List.length_cons,List.length_nil] at pv pg ev eg
  obtain ⟨len,fuel⟩ := token_spec E.bits
  simp only [value_bits,Nat.size_eq_bits_len] at len fuel
  obtain ⟨word,shift⟩ := shiftOne_spec (tokens E.bits).1
  rw [len] at word shift
  dsimp only [out,run]
  rw [rv,pv,ev,word,min_eq_left cap]
  refine ⟨rfl,?_⟩
  have rg' := rg.trans (show 8*(r+1)^2≤8*(X+1)^2 by gcongr)
  have es := (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=E))).trans (ep.trans pmax)
  have large : X ≤ (X+1)^2 := by nlinarith only [Nat.zero_le (X^2)]
  have pos : 0<(X+1)^2 := Nat.pow_pos (Nat.succ_pos _)
  have rx : rel.rows.length+1≤X := row
  have ex := ep.trans pmax
  dsimp only [header] at rg'
  dsimp only [d] at pg eg
  calc
    _ ≤ 2^9*(X+1)^2 := by omega
    _ ≤ 2^9*(2*X)^2 := by gcongr; have : 0<X := Nat.two_pow_pos _; omega
    _ = 2^(9+(1+1013*S)*2) := by rw [show 2*X=2^(1+1013*S) by rw [pow_add,pow_one],←pow_mul,←pow_add]
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)

end Cogentic.BinaryPrecision

#print axioms Cogentic.BinaryPrecision.fixed_words
