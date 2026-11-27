import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace Cogentic.RandomizedUnitaryDivisorSign

private theorem cancel_factor {n a x y : ℤ} (ha : IsCoprime n a)
    (he : a * x ≡ a * y [ZMOD n]) : x ≡ y [ZMOD n] := by
  rw [Int.modEq_iff_dvd, ← mul_sub] at he
  exact Int.modEq_iff_dvd.mpr (ha.dvd_of_dvd_mul_left he)

/-- Both the signed difference and the sum are units modulo the full product. -/
theorem sum_sub_units {d e : ℕ} (h : d.Coprime e) :
    IsCoprime ((d : ℤ) + e) ((d : ℤ) * e) ∧
    IsCoprime ((d : ℤ) - e) ((d : ℤ) * e) := by
  obtain ⟨s, t, he⟩ := h.isCoprime
  constructor
  · apply IsCoprime.mul_right
    · refine ⟨t, s - t, ?_⟩
      linear_combination he
    · refine ⟨s, t - s, ?_⟩
      linear_combination he
  · apply IsCoprime.mul_right
    · refine ⟨-t, s + t, ?_⟩
      linear_combination he
    · refine ⟨s, t + s, ?_⟩
      linear_combination he

/-- The quotient of the sum by the signed difference prescribes exactly one
negative divisor block and one positive divisor block. -/
theorem quotient_iff_signs {d e : ℕ} (h : d.Coprime e) (x : ℤ) :
    ((d : ℤ) - e) * x ≡ (d : ℤ) + e [ZMOD (d : ℤ) * e] ↔
      x ≡ -1 [ZMOD (d : ℤ)] ∧ x ≡ 1 [ZMOD (e : ℤ)] := by
  have hcrt (a b : ℤ) :
      a ≡ b [ZMOD (d : ℤ)] ∧ a ≡ b [ZMOD (e : ℤ)] ↔
        a ≡ b [ZMOD (d : ℤ) * e] :=
    Int.modEq_and_modEq_iff_modEq_mul (by simpa using h)
  have hm : ((d : ℤ) - e) * (-1) ≡ (d : ℤ) + e [ZMOD (d : ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨2, by ring⟩
  have hp : ((d : ℤ) - e) * 1 ≡ (d : ℤ) + e [ZMOD (e : ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨2, by ring⟩
  constructor
  · intro hx
    obtain ⟨hd, he⟩ := (hcrt _ _).mpr hx
    have hu := (sum_sub_units h).2
    exact ⟨cancel_factor hu.of_mul_right_left.symm (hd.trans hm.symm),
      cancel_factor hu.of_mul_right_right.symm (he.trans hp.symm)⟩
  · rintro ⟨hd, he⟩
    exact (hcrt _ _).mp ⟨(hd.mul_left _).trans hm, (he.mul_left _).trans hp⟩

/-- Every coprime divisor pair provides a modular quotient and its square is one. -/
theorem exists_quotient_square {d e : ℕ} (h : d.Coprime e) :
    ∃ x : ℤ, ((d : ℤ) - e) * x ≡ (d : ℤ) + e [ZMOD (d : ℤ) * e] ∧
      x ^ 2 ≡ 1 [ZMOD (d : ℤ) * e] := by
  obtain ⟨s, t, he⟩ := h.isCoprime
  let x : ℤ := s * (d : ℤ) - t * (e : ℤ)
  have hd : x ≡ -1 [ZMOD (d : ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-2 * s, ?_⟩
    dsimp [x]
    linear_combination he
  have he' : x ≡ 1 [ZMOD (e : ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨2 * t, ?_⟩
    dsimp [x]
    linear_combination -he
  refine ⟨x, (quotient_iff_signs h x).mpr ⟨hd, he'⟩, ?_⟩
  apply Int.modEq_and_modEq_iff_modEq_mul (m := (d : ℤ)) (n := (e : ℤ))
    (by simpa using h) |>.mp
  exact ⟨by simpa using hd.pow 2, by simpa using he'.pow 2⟩

/-- Proper odd divisor blocks force a sign different from either global sign. -/
theorem proper_quotient_nontrivial {d e : ℕ} (hc : d.Coprime e)
    (ho : Odd (d * e)) (hd : 1 < d) (he : 1 < e) {x : ℤ}
    (hx : ((d : ℤ) - e) * x ≡ (d : ℤ) + e [ZMOD (d : ℤ) * e]) :
    (¬ x ≡ -1 [ZMOD (d : ℤ) * e]) ∧ (¬ x ≡ 1 [ZMOD (d : ℤ) * e]) := by
  obtain ⟨hsd, hse⟩ := (quotient_iff_signs hc x).mp hx
  have not_two {a : ℕ} (ha : 1 < a) (hoa : Odd a) : ¬ (a : ℤ) ∣ 2 := by
    intro h
    have hs : a ∣ (2 : ℕ) := by exact_mod_cast h
    have hle := Nat.le_of_dvd (by decide : 0 < (2 : ℕ)) hs
    obtain ⟨k, hk⟩ := hoa
    omega
  constructor
  · intro h
    have hh : x ≡ -1 [ZMOD (e : ℤ)] := h.of_mul_left _
    have hs := Int.modEq_iff_dvd.mp (hh.symm.trans hse)
    exact not_two he (Nat.odd_mul.mp ho).2 (by simpa using hs)
  · intro h
    have hh : x ≡ 1 [ZMOD (d : ℤ)] := h.of_mul_right _
    have hs := Int.modEq_iff_dvd.mp (hsd.symm.trans hh)
    exact not_two hd (Nat.odd_mul.mp ho).1 (by simpa using hs)

/-- Every nontrivial square root of one modulo odd N arises from a proper
coprime divisor pair with the indicated quotient. -/
theorem covers_nontrivial_signs {N : ℕ} (hodd : Odd N) {x : ℤ}
    (hx : x ^ 2 ≡ 1 [ZMOD (N : ℤ)]) (hxminus : ¬ x ≡ -1 [ZMOD (N : ℤ)])
    (hxplus : ¬ x ≡ 1 [ZMOD (N : ℤ)]) :
    ∃ d e : ℕ, d * e = N ∧ d.Coprime e ∧ 1 < d ∧ 1 < e ∧
      x ≡ -1 [ZMOD (d : ℤ)] ∧ x ≡ 1 [ZMOD (e : ℤ)] ∧
      ((d : ℤ) - e) * x ≡ (d : ℤ) + e [ZMOD (N : ℤ)] := by
  have hNpos : 0 < N := by rcases hodd with ⟨q, hq⟩; omega
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hNpos.ne'
  let d := Int.gcd (x + 1) (N : ℤ)
  have hdpos : 0 < d := Int.gcd_pos_of_ne_zero_right _ hNz
  have hdz : (d : ℤ) ≠ 0 := by exact_mod_cast hdpos.ne'
  obtain ⟨a, b, hab, ha, hb⟩ := Int.exists_gcd_one hdpos
  have hbpos : 0 < b := by
    have hd : (0 : ℤ) < d := by exact_mod_cast hdpos
    exact pos_of_mul_pos_left (hb ▸ (by exact_mod_cast hNpos : 0 < (N : ℤ))) hd.le
  let e := b.toNat
  have hecast : (e : ℤ) = b := Int.toNat_of_nonneg hbpos.le
  have hepos : 0 < e := by exact_mod_cast hecast.symm ▸ hbpos
  have hn : d * e = N := by
    exact_mod_cast (show (d : ℤ) * (e : ℤ) = (N : ℤ) by rw [hecast, mul_comm, ← hb])
  have hprod : (N : ℤ) ∣ (x + 1) * (x - 1) := by
    have h := Int.modEq_iff_dvd.mp hx
    rw [show (x + 1) * (x - 1) = -(1 - x ^ 2) by ring]
    exact dvd_neg.mpr h
  have hdiv : b ∣ x - 1 := by
    have hm : b * (d : ℤ) ∣ (a * (x - 1)) * (d : ℤ) := by
      have hmul : (x + 1) * (x - 1) = (a * (x - 1)) * (d : ℤ) :=
        (congrArg (fun q : ℤ => q * (x - 1)) ha).trans (mul_right_comm _ _ _)
      exact Eq.mp (congrArg₂ (· ∣ ·) hb hmul) hprod
    exact ((Int.isCoprime_iff_gcd_eq_one.mpr hab).symm).dvd_of_dvd_mul_left
      (Int.dvd_of_mul_dvd_mul_right hdz hm)
  have hddiv : (d : ℤ) ∣ x + 1 := ⟨a, by rw [ha, mul_comm]⟩
  have hediv : (e : ℤ) ∣ x - 1 := by simpa only [hecast] using hdiv
  have hg₂ : ((d.gcd e : ℕ) : ℤ) ∣ 2 := by
    have hlo : ((d.gcd e : ℕ) : ℤ) ∣ x + 1 :=
      (Int.ofNat_dvd_natCast.mpr (Nat.gcd_dvd_left d e)).trans hddiv
    have hhi : ((d.gcd e : ℕ) : ℤ) ∣ x - 1 :=
      (Int.ofNat_dvd_natCast.mpr (Nat.gcd_dvd_right d e)).trans hediv
    rw [show (2 : ℤ) = (x + 1) - (x - 1) by ring]
    exact dvd_sub hlo hhi
  have hcop : d.Coprime e := by
    apply Nat.dvd_one.mp
    rw [← hodd.coprime_two_left.gcd_eq_one]
    exact Nat.dvd_gcd (by exact_mod_cast hg₂) ((Nat.gcd_dvd_left d e).trans ⟨e, hn.symm⟩)
  have hsminus : x ≡ -1 [ZMOD (d : ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    rw [show (-1 : ℤ) - x = -(x + 1) by ring]
    exact dvd_neg.mpr hddiv
  have hsplus : x ≡ 1 [ZMOD (e : ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    rw [show (1 : ℤ) - x = -(x - 1) by ring]
    exact dvd_neg.mpr hediv
  have hdgt : 1 < d := by
    by_contra! hd
    have hh : d = 1 := by omega
    have hen : e = N := by simpa [hh] using hn
    exact hxplus (by simpa [hen] using hsplus)
  have hegt : 1 < e := by
    by_contra! he
    have hh : e = 1 := by omega
    have hdn : d = N := by simpa [hh] using hn
    exact hxminus (by simpa [hdn] using hsminus)
  refine ⟨d, e, hn, hcop, hdgt, hegt, hsminus, hsplus, ?_⟩
  have hquot := (quotient_iff_signs hcop x).mpr ⟨hsminus, hsplus⟩
  simpa only [← Nat.cast_mul, hn] using hquot

/-- The same sum and difference arise from the imaginary quadratic identity.
The equality is stated in any field containing the specified square root. -/
theorem quadratic_identity {K : Type*} [Field K] {d e w : K} (hd : d ≠ 0)
    (hw : w ^ 2 = -(d * e)) : (d + w) ^ 2 / d = d - e + 2 * w := by
  apply (div_eq_iff hd).mpr
  linear_combination hw

end Cogentic.RandomizedUnitaryDivisorSign
