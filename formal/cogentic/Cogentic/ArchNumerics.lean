import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

namespace Cogentic.ArchNumerics
open Finset

/-- Evaluate the log series on [1,2] with rational arithmetic. -/
def reducedLog (x : ℚ) (terms : ℕ) : ℚ :=
  ∑ i ∈ range terms, (1-x⁻¹)^(i+1)/(i+1)

theorem reducedLog_error {x : ℚ} (lo : 1 ≤ x) (hi : x ≤ 2) (terms : ℕ) :
    |(reducedLog x terms : ℝ)-Real.log x| ≤ (1/2:ℝ)^terms := by
  let y := 1-(x:ℝ)⁻¹
  have xl : (1:ℝ) ≤ x := by exact_mod_cast lo
  have xh : (x:ℝ) ≤ 2 := by exact_mod_cast hi
  have xp : (0:ℝ) < x := by linarith
  have yl : 0 ≤ y := sub_nonneg.mpr ((inv_le_one₀ xp).mpr xl)
  have yh : y ≤ 1/2 := by
    have h := one_div_le_one_div_of_le xp xh
    have h' : (1/2:ℝ) ≤ (x:ℝ)⁻¹ := by simpa only [one_div] using h
    dsimp [y]; linarith
  have err := Real.abs_log_sub_add_sum_range_le (x := y) (by rw [abs_of_nonneg yl]; linarith) terms
  rw [abs_of_nonneg yl, show 1-y = (x:ℝ)⁻¹ by dsimp [y]; ring,Real.log_inv] at err
  have castSum : (reducedLog x terms : ℝ) = ∑ i ∈ range terms, y^(i+1)/((i:ℝ)+1) := by
    simp [reducedLog,y]
  rw [castSum,sub_eq_add_neg]
  apply err.trans
  calc
    _ ≤ (1/2:ℝ)^(terms+1)/(1/2) := by
      apply div_le_div₀ (by positivity) (pow_le_pow_left₀ yl yh _) (by norm_num)
      linarith
    _ = _ := by rw [pow_succ]; ring

def mantissa (n : ℕ) : ℚ := n / (2:ℚ)^n.log2

def natLog (n terms : ℕ) : ℚ := n.log2 * reducedLog 2 terms + reducedLog (mantissa n) terms

theorem natLog_error {n : ℕ} (hn : 0 < n) (terms : ℕ) :
    |(natLog n terms:ℝ)-Real.log n| ≤ (n.log2+1)*(1/2:ℝ)^terms := by
  have p : 0 < (2:ℚ)^n.log2 := by positivity
  have low : 1 ≤ mantissa n := by
    change 1 ≤ (n:ℚ)/2^n.log2
    rw [le_div_iff₀ p,one_mul]
    exact_mod_cast Nat.log2_self_le hn.ne'
  have high : mantissa n ≤ 2 := by
    change (n:ℚ)/2^n.log2 ≤ 2
    rw [div_le_iff₀ p,mul_comm, ← pow_succ]
    exact_mod_cast (Nat.lt_log2_self (n := n)).le
  have castMant : ((mantissa n:ℚ):ℝ) = (n:ℝ)/2^n.log2 := by simp [mantissa]
  have logid : Real.log n = (n.log2:ℝ)*Real.log 2 + Real.log (mantissa n) := by
    rw [castMant, Real.log_div (by exact_mod_cast hn.ne') (by positivity), Real.log_pow]; ring
  have a := reducedLog_error (x := 2) (by norm_num) (by norm_num) terms
  norm_num only [Rat.cast_ofNat] at a
  have b := reducedLog_error low high terms
  rw [logid,natLog]
  push_cast
  rw [show (n.log2:ℝ)*(reducedLog 2 terms:ℝ) + (reducedLog (mantissa n) terms:ℝ) -
      ((n.log2:ℝ)*Real.log 2 + Real.log (mantissa n)) =
      (n.log2:ℝ)*((reducedLog 2 terms:ℝ)-Real.log 2)+((reducedLog (mantissa n) terms:ℝ)-Real.log (mantissa n)) by ring]
  refine (abs_add_le ..).trans ?_
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
  nlinarith [mul_le_mul_of_nonneg_left a (Nat.cast_nonneg n.log2)]

/-- The nearest dyadic rational at a specified precision; ties round upward. -/
def roundDyadic (x : ℚ) (bits : ℕ) : ℚ := (⌊x*(2:ℚ)^bits+1/2⌋:ℤ)/(2:ℚ)^bits

theorem roundDyadic_error (x : ℚ) (bits : ℕ) :
    |roundDyadic x bits-x| ≤ (1/2:ℚ)^bits/2 := by
  have a := Int.floor_le (x*(2:ℚ)^bits+1/2)
  have b := Int.lt_floor_add_one (x*(2:ℚ)^bits+1/2)
  rw [one_div_pow,roundDyadic,abs_le]
  constructor
  · apply (le_sub_iff_add_le).mpr
    rw [le_div_iff₀ (by positivity)]
    have c : 2^bits*(1/(2:ℚ)^bits/2) = 1/2 := by field_simp
    linarith
  · apply (sub_le_iff_le_add).mpr
    rw [div_le_iff₀ (by positivity)]
    have c : 2^bits*(1/(2:ℚ)^bits/2) = 1/2 := by field_simp
    linarith

def approxLog (u v bits : ℕ) : ℚ :=
  let terms := bits+u.log2+v.log2+4
  roundDyadic (natLog u terms - natLog v terms) bits

theorem approxLog_error {u v : ℕ} (hu : 0 < u) (hv : 0 < v) (bits : ℕ) :
    |(approxLog u v bits : ℝ)-Real.log ((u:ℝ)/v)| < (1/2:ℝ)^bits := by
  let extra := u.log2+v.log2+4
  let terms := bits+extra
  let x := natLog u terms - natLog v terms
  have cap : u.log2+v.log2+2 < 2^(extra-1) := by
    dsimp [extra]
    have h := Nat.lt_two_pow_self (n := u.log2+v.log2+3)
    omega
  have digits : (u.log2:ℝ)+v.log2+2 < (2:ℝ)^(extra-1) := by exact_mod_cast cap
  have savings : ((u.log2:ℝ)+v.log2+2)*(1/2:ℝ)^terms < (1/2:ℝ)^bits/2 := by
    have eq : extra = (extra-1)+1 := by dsimp [extra]
    dsimp only [terms]
    rw [pow_add,show (1/2:ℝ)^extra = (1/(2:ℝ)^(extra-1))*(1/2) by
      conv_lhs => rw [eq,pow_succ,one_div_pow]]
    field_simp
    nlinarith [mul_lt_mul_of_pos_right digits (by positivity : 0 < (2:ℝ)^bits)]
  have e1 := natLog_error hu terms
  have e2 := natLog_error hv terms
  have rounded : |((roundDyadic x bits:ℚ):ℝ)-(x:ℝ)| ≤ (1/2:ℝ)^bits/2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr (roundDyadic_error x bits)
    simpa only [Rat.cast_abs,Rat.cast_sub,Rat.cast_div,Rat.cast_pow,Rat.cast_one,Rat.cast_ofNat] using h
  have delta : |(x:ℝ)-Real.log ((u:ℝ)/v)| < (1/2:ℝ)^bits/2 := by
    dsimp [x]
    rw [Rat.cast_sub, Real.log_div (by exact_mod_cast hu.ne') (by exact_mod_cast hv.ne')]
    rw [show (natLog u terms:ℝ) - (natLog v terms:ℝ) - (Real.log u - Real.log v) =
      ((natLog u terms:ℝ)-Real.log u)-((natLog v terms:ℝ)-Real.log v) by ring]
    apply lt_of_le_of_lt (abs_sub ..)
    linarith
  have eq : approxLog u v bits = roundDyadic x bits := by
    simp only [approxLog,x,terms,extra,Nat.add_assoc]
  rw [eq]
  have total := abs_add_le (((roundDyadic x bits:ℚ):ℝ)-(x:ℝ)) ((x:ℝ)-Real.log ((u:ℝ)/v))
  rw [sub_add_sub_cancel] at total
  linarith

/-- Exact integer square root at the requested dyadic scale. -/
def approxSqrt (u v bits : ℕ) : ℚ :=
  (Nat.sqrt ((2^bits)^2*u/v):ℕ)/(2:ℚ)^bits

theorem approxSqrt_error {u v : ℕ} (hv : 0 < v) (bits : ℕ) :
    0 ≤ Real.sqrt ((u:ℝ)/v)-(approxSqrt u v bits:ℝ) ∧
    Real.sqrt ((u:ℝ)/v)-(approxSqrt u v bits:ℝ) < (1/2:ℝ)^bits := by
  let k := 2^bits
  let w := k^2*u/v
  let a := Nat.sqrt w
  have low : a^2*v ≤ k^2*u := (Nat.le_div_iff_mul_le hv).mp (Nat.sqrt_le' w)
  have high : k^2*u < (a+1)^2*v := (Nat.div_lt_iff_lt_mul hv).mp (Nat.lt_succ_sqrt' w)
  have kp : (0:ℝ) < k := by dsimp [k]; positivity
  have vp : (0:ℝ) < v := by exact_mod_cast hv
  have sq := Real.sq_sqrt (div_nonneg (Nat.cast_nonneg u) vp.le)
  have sp := Real.sqrt_nonneg ((u:ℝ)/v)
  have al : (a:ℝ)^2 ≤ (k:ℝ)^2*((u:ℝ)/v) := by
    rw [← mul_div_assoc,le_div_iff₀ vp]
    exact_mod_cast low
  have ah : (k:ℝ)^2*((u:ℝ)/v) < ((a:ℝ)+1)^2 := by
    rw [← mul_div_assoc,div_lt_iff₀ vp]
    exact_mod_cast high
  have prod : ((k:ℝ)*Real.sqrt ((u:ℝ)/v))^2 = (k:ℝ)^2*((u:ℝ)/v) := by rw [mul_pow,sq]
  have nonn := mul_nonneg kp.le sp
  have lb : (a:ℝ) ≤ k*Real.sqrt ((u:ℝ)/v) := by nlinarith [Nat.cast_nonneg (α := ℝ) a]
  have ub : (k:ℝ)*Real.sqrt ((u:ℝ)/v) < a+1 := by nlinarith [Nat.cast_nonneg (α := ℝ) a]
  have castApprox : ((approxSqrt u v bits:ℚ):ℝ) = (a:ℝ)/k := by simp [a,k,w,approxSqrt]
  rw [castApprox,one_div_pow,show (2:ℝ)^bits = k by simp [k]]
  constructor
  · exact sub_nonneg.mpr ((div_le_iff₀ kp).mpr (by linarith))
  · rw [sub_lt_iff_lt_add, ← add_div,lt_div_iff₀ kp]; linarith

example : approxSqrt 2 1 4 = 11/8 := by norm_num [approxSqrt]

end Cogentic.ArchNumerics
