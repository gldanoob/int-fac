import Cogentic.MinorVerificationWork
import Cogentic.BinaryPivotCost

namespace Cogentic.SolverStage
open Concrete Concrete.SolverGrowth

/-- The bit length of the rounded augmented rows is bounded before elimination,
including for a matrix that proves singular. The same cap covers both system dimensions. -/
theorem fixed_parameters {n ell : ℕ} {pair : TryPair.PairData} {rel : Marking.Relations}
    (stage : Marking.stageOne (TryPair.fixedInput n ell pair)=some rel) :
    let b := n.log2+1; let S := TwoThirdsCost.scale b
    let s := TryPair.fixedInput n ell pair; let R := rel.rows.length+1
    let H := rel.marks.length*R.factorial*(2*s.degree*(s.L₀+1)+1)*2^(TryPair.localBits s rel)+1
    let W := 2^(30000*S)
    0<S ∧ rel.marks.length≤W ∧ R≤W ∧ 2*s.degree-2≤W ∧ H.size≤W := by
  intro b S s R H W
  have hb : 0<b := Nat.succ_pos _
  have hs : Fixed.h b≤S := (Nat.le_mul_of_pos_left _ (Fixed.degree_pos hb)).trans (Fixed.scale_bounds hb).1
  have zs : Fixed.z b≤S := (Nat.le_mul_of_pos_left _ (Fixed.degree_pos hb)).trans hs
  have pos : 0<S := (Nat.succ_pos b.log2).trans_le zs
  have bBound : Within S 1 b := (Nat.lt_log2_self (n:=b)).le.trans
    (Nat.pow_le_pow_right Nat.zero_lt_two (by simpa only [one_mul,Fixed.z] using zs))
  have dBound : Within S 1 s.degree := smaller bBound (Fixed.degree_le_bits _)
  have bBits : Within S 1 s.L₀ := bBound
  have BBound : Within S 1000 s.B := Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_left _ hs)
  have marks : Within S 10000 rel.marks.length := (retained_size stage).trans
    (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_left _ hs))
  have rows := smaller (product (numeral S 2 pos) (smallPower 2 (plus pos BBound (numeral S 1 pos)))) (ArchPrecision.retained_rows stage)
  have dim := smaller (product (numeral S 2 pos) dBound) (Nat.sub_le (2*s.degree) 2)
  have rBound := plus pos rows (numeral S 1 pos)
  have one := numeral S 1 pos
  have prec : Within S 2100 (TryPair.localBits s rel) := weaken
    (product (product (product (numeral S 64 pos) (smallPower 3 dBound)) rBound) bBits) (by decide)
  have logSize := plus pos (product (product (numeral S 2 pos) dBound) (plus pos bBits one)) one
  have magnitude : Within S 25000 H.size := weaken (succLength pos (productLength pos
    (productLength pos (productLength pos (bitLength marks) (factorialLength pos rBound)) (bitLength logSize))
    (powerLength pos prec))) (by decide)
  exact ⟨pos,weaken marks (by decide),weaken rBound (by decide),weaken dim (by decide),weaken magnitude (by decide)⟩

end Cogentic.SolverStage
