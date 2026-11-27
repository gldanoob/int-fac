import Cogentic.RandomizedTwoMarkResidue
import Cogentic.RandomizedPrimeBinSupply
import Cogentic.RandomizedPrimeBinProgression
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Prime-multiplier polynomial construction, setup checks, affine two-mark phase support,
exact marginal unit-phase uniformity, and prime-multiplier equidistribution from the
critical-line hypothesis. -/

namespace Cogentic.Randomized

open Polynomial Finset
open scoped BigOperators

/-! ## Section 1: Centered base-`Q` construction and dehomogenization -/

/-- Centered representative of `a` modulo `Q` (for `0 < Q`), lying in `[-Q/2, Q/2]`. -/
def centeredMod (a Q : ℤ) : ℤ :=
  let u := a % Q
  if 2 * u ≤ Q then u else u - Q

theorem centeredMod_modEq (a Q : ℤ) : centeredMod a Q ≡ a [ZMOD Q] := by
  unfold centeredMod
  dsimp only
  split_ifs
  · exact Int.mod_modEq a Q
  · have h1 : a % Q - Q ≡ a % Q - 0 [ZMOD Q] :=
      Int.ModEq.sub rfl (Int.modEq_zero_iff_dvd.mpr dvd_rfl)
    rw [sub_zero] at h1
    exact h1.trans (Int.mod_modEq a Q)

theorem two_mul_abs_centeredMod_le (a : ℤ) {Q : ℤ} (hQ : 0 < Q) :
    2 * |centeredMod a Q| ≤ Q := by
  unfold centeredMod
  dsimp only
  have h0 : 0 ≤ a % Q := Int.emod_nonneg a hQ.ne'
  have hlt : a % Q < Q := Int.emod_lt_of_pos a hQ
  split_ifs with h
  · rw [abs_of_nonneg h0]
    exact h
  · rw [abs_of_neg (by omega)]
    omega

theorem abs_centeredMod_le_ediv_two (a : ℤ) {Q : ℤ} (hQ : 0 < Q) :
    |centeredMod a Q| ≤ Q / 2 := by
  have h := two_mul_abs_centeredMod_le a hQ
  omega

/-- Remainder sequence in the centered base-`Q` expansion of `target` at `(r, Q)`. -/
def centeredBaseQRem (d' : ℕ) (r Q target : ℤ) : ℕ → ℤ
  | 0 => target
  | i + 1 =>
    let rem := centeredBaseQRem d' r Q target i
    let digit := centeredMod (rem * (Int.gcdA r Q) ^ (d' - i)) Q
    (rem - digit * r ^ (d' - i)) / Q

/-- Coefficients of the centered base-`Q` homogeneous form `F₀(X, Y)` of degree `d'`.
Lower indices `i < d'` are centered digits in `[-Q/2, Q/2]`; index `d'` is the top
base-`Q` coefficient. -/
def centeredBaseQCoeffs (d' : ℕ) (r Q target : ℤ) (i : ℕ) : ℤ :=
  if i < d' then
    centeredMod (centeredBaseQRem d' r Q target i * (Int.gcdA r Q) ^ (d' - i)) Q
  else if i = d' then
    centeredBaseQRem d' r Q target d'
  else 0

private theorem r_mul_gcdA_modEq_one {r Q : ℤ} (hcop : Int.gcd r Q = 1) :
    r * Int.gcdA r Q ≡ 1 [ZMOD Q] := by
  have h := Int.gcd_eq_gcd_ab r Q
  rw [hcop, Nat.cast_one] at h
  rw [Int.modEq_iff_dvd]
  refine ⟨Int.gcdB r Q, ?_⟩
  linarith

private theorem centeredBaseQRem_step {d' : ℕ} {r Q target : ℤ}
    (hcop : Int.gcd r Q = 1) {i : ℕ} (hi : i < d') :
    centeredBaseQRem d' r Q target i =
      centeredBaseQCoeffs d' r Q target i * r ^ (d' - i) +
        Q * centeredBaseQRem d' r Q target (i + 1) := by
  let rem := centeredBaseQRem d' r Q target i
  let digit := centeredMod (rem * (Int.gcdA r Q) ^ (d' - i)) Q
  have hcoeff : centeredBaseQCoeffs d' r Q target i = digit := by
    simp [centeredBaseQCoeffs, hi, digit, rem]
  have hmod1 : digit ≡ rem * (Int.gcdA r Q) ^ (d' - i) [ZMOD Q] :=
    centeredMod_modEq _ Q
  have hmod2 : digit * r ^ (d' - i) ≡ rem * (r * Int.gcdA r Q) ^ (d' - i) [ZMOD Q] := by
    have hmul := hmod1.mul_right (r ^ (d' - i))
    have heq : rem * Int.gcdA r Q ^ (d' - i) * r ^ (d' - i) =
        rem * (r * Int.gcdA r Q) ^ (d' - i) := by
      rw [mul_pow]
      ring
    rwa [heq] at hmul
  have hmod3 : rem * (r * Int.gcdA r Q) ^ (d' - i) ≡ rem [ZMOD Q] := by
    have hpow := (r_mul_gcdA_modEq_one hcop).pow (d' - i)
    simpa only [one_pow, mul_one] using hpow.mul_left rem
  have hdvd : Q ∣ rem - digit * r ^ (d' - i) :=
    Int.modEq_iff_dvd.mp (hmod2.trans hmod3)
  rw [hcoeff]
  change rem = digit * r ^ (d' - i) + Q * ((rem - digit * r ^ (d' - i)) / Q)
  rw [Int.mul_ediv_cancel' hdvd]
  ring

private theorem centeredBaseQRem_invariant (d' : ℕ) {r Q target : ℤ}
    (hcop : Int.gcd r Q = 1) : ∀ n ≤ d',
    target =
      (∑ j ∈ Finset.range n, centeredBaseQCoeffs d' r Q target j * r ^ (d' - j) * Q ^ j) +
        Q ^ n * centeredBaseQRem d' r Q target n := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [centeredBaseQRem]
  | succ n ih =>
    intro hn
    have hprev := ih (Nat.le_of_succ_le hn)
    have hstep := centeredBaseQRem_step (target := target) hcop (Nat.lt_of_succ_le hn)
    rw [Finset.sum_range_succ, pow_succ]
    rw [hstep] at hprev
    linear_combination hprev

/-- The centered base-`Q` form evaluates at `(r, Q)` to `target`. -/
theorem centeredBaseQCoeffs_eval_eq (d' : ℕ) {r Q target : ℤ}
    (hcop : Int.gcd r Q = 1) :
    homogeneousFormEval d' (centeredBaseQCoeffs d' r Q target) r Q = target := by
  have h := centeredBaseQRem_invariant d' (target := target) hcop d' le_rfl
  rw [homogeneousFormEval, Finset.sum_range_succ]
  have htop : centeredBaseQCoeffs d' r Q target d' = centeredBaseQRem d' r Q target d' := by
    simp [centeredBaseQCoeffs]
  rw [htop, Nat.sub_self, pow_zero, mul_one, mul_comm (centeredBaseQRem d' r Q target d') (Q ^ d')]
  exact h.symm

/-- Specialized at degree `d' = d + L₀` and target `k * N`: `F₀(r, Q) = k * N`. -/
theorem centeredBaseQCoeffs_multiplier_eval_eq (d L₀ : ℕ) {r Q : ℤ} (k N : ℕ)
    (hcop : Int.gcd r Q = 1) :
    homogeneousFormEval (d + L₀) (centeredBaseQCoeffs (d + L₀) r Q ((k : ℤ) * (N : ℤ))) r Q =
      (k : ℤ) * (N : ℤ) :=
  centeredBaseQCoeffs_eval_eq (d + L₀) hcop

/-- All lower base-`Q` coefficients lie in `[-Q/2, Q/2]`. -/
theorem centeredBaseQCoeffs_lower_bound (d' : ℕ) (r : ℤ) {Q : ℤ} (target : ℤ)
    (hQ : 0 < Q) {i : ℕ} (hi : i < d') :
    2 * |centeredBaseQCoeffs d' r Q target i| ≤ Q ∧
      |centeredBaseQCoeffs d' r Q target i| ≤ Q / 2 := by
  have hcoeff : centeredBaseQCoeffs d' r Q target i =
      centeredMod (centeredBaseQRem d' r Q target i * (Int.gcdA r Q) ^ (d' - i)) Q := by
    simp [centeredBaseQCoeffs, hi]
  rw [hcoeff]
  exact ⟨two_mul_abs_centeredMod_le _ hQ, abs_centeredMod_le_ediv_two _ hQ⟩

/-- Integer form of the top base-`Q` coefficient bound. -/
theorem centeredBaseQCoeffs_top_bound_int (d' : ℕ) {r Q target : ℤ}
    (hcop : Int.gcd r Q = 1) (hQ : 0 < Q) (hr : |r| ≤ Q) :
    2 * Q ^ d' * |centeredBaseQCoeffs d' r Q target d'| ≤
      2 * |target| + (d' : ℤ) * Q * Q ^ d' := by
  have heval := centeredBaseQCoeffs_eval_eq d' (target := target) hcop
  rw [homogeneousFormEval, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one] at heval
  have htop : centeredBaseQCoeffs d' r Q target d' * Q ^ d' =
      target - ∑ j ∈ Finset.range d',
        centeredBaseQCoeffs d' r Q target j * r ^ (d' - j) * Q ^ j := by
    linarith
  have hQpow : 0 ≤ Q ^ d' := pow_nonneg hQ.le d'
  have habs : Q ^ d' * |centeredBaseQCoeffs d' r Q target d'| ≤
      |target| + ∑ j ∈ Finset.range d',
        |centeredBaseQCoeffs d' r Q target j| * |r| ^ (d' - j) * Q ^ j := by
    calc
      Q ^ d' * |centeredBaseQCoeffs d' r Q target d'|
          = |centeredBaseQCoeffs d' r Q target d' * Q ^ d'| := by
              rw [abs_mul, abs_of_nonneg hQpow, mul_comm]
      _ = |target - ∑ j ∈ Finset.range d',
            centeredBaseQCoeffs d' r Q target j * r ^ (d' - j) * Q ^ j| := by rw [htop]
      _ ≤ |target| + |∑ j ∈ Finset.range d',
            centeredBaseQCoeffs d' r Q target j * r ^ (d' - j) * Q ^ j| := abs_sub _ _
      _ ≤ |target| + ∑ j ∈ Finset.range d',
            |centeredBaseQCoeffs d' r Q target j * r ^ (d' - j) * Q ^ j| := by
              gcongr; exact Finset.abs_sum_le_sum_abs _ _
      _ = |target| + ∑ j ∈ Finset.range d',
            |centeredBaseQCoeffs d' r Q target j| * |r| ^ (d' - j) * Q ^ j := by
              congr 1
              apply Finset.sum_congr rfl
              intro j _
              rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg hQ.le]
  have hsum : 2 * (∑ j ∈ Finset.range d',
      |centeredBaseQCoeffs d' r Q target j| * |r| ^ (d' - j) * Q ^ j) ≤
      (d' : ℤ) * Q * Q ^ d' := by
    rw [Finset.mul_sum]
    calc
      ∑ j ∈ Finset.range d',
          2 * (|centeredBaseQCoeffs d' r Q target j| * |r| ^ (d' - j) * Q ^ j)
        ≤ ∑ _j ∈ Finset.range d', Q * Q ^ d' := by
          apply Finset.sum_le_sum
          intro j hj
          have hjlt : j < d' := Finset.mem_range.mp hj
          have hc := (centeredBaseQCoeffs_lower_bound d' r target hQ hjlt).1
          have hrpow : |r| ^ (d' - j) ≤ Q ^ (d' - j) :=
            pow_le_pow_left₀ (abs_nonneg r) hr (d' - j)
          have hprod : |r| ^ (d' - j) * Q ^ j ≤ Q ^ d' := by
            calc
              |r| ^ (d' - j) * Q ^ j ≤ Q ^ (d' - j) * Q ^ j :=
                mul_le_mul_of_nonneg_right hrpow (pow_nonneg hQ.le j)
              _ = Q ^ (d' - j + j) := (pow_add Q (d' - j) j).symm
              _ = Q ^ d' := by rw [Nat.sub_add_cancel hjlt.le]
          calc
            2 * (|centeredBaseQCoeffs d' r Q target j| * |r| ^ (d' - j) * Q ^ j)
                = (2 * |centeredBaseQCoeffs d' r Q target j|) * (|r| ^ (d' - j) * Q ^ j) := by ring
            _ ≤ Q * Q ^ d' :=
                mul_le_mul hc hprod (mul_nonneg (pow_nonneg (abs_nonneg r) _) (pow_nonneg hQ.le _))
                  hQ.le
      _ = (d' : ℤ) * Q * Q ^ d' := by simp [mul_assoc]
  linarith

/-- Real-valued top base-`Q` coefficient bound `|c_{d'}| ≤ |target / Q^{d'}| + d' * Q / 2`. -/
theorem centeredBaseQCoeffs_top_bound (d' : ℕ) {r Q target : ℤ}
    (hcop : Int.gcd r Q = 1) (hQ : 0 < Q) (hr : |r| ≤ Q) :
    |(centeredBaseQCoeffs d' r Q target d' : ℝ)| ≤
      |(target : ℝ) / (Q : ℝ) ^ d'| + (d' : ℝ) * (Q : ℝ) / 2 := by
  have hint := centeredBaseQCoeffs_top_bound_int d' (target := target) hcop hQ hr
  have hQr : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hQpow : (0 : ℝ) < (Q : ℝ) ^ d' := pow_pos hQr d'
  have hreal : 2 * (Q : ℝ) ^ d' * |(centeredBaseQCoeffs d' r Q target d' : ℝ)| ≤
      2 * |(target : ℝ)| + (d' : ℝ) * (Q : ℝ) * (Q : ℝ) ^ d' := by
    exact_mod_cast hint
  rw [abs_div, abs_of_pos hQpow]
  have hdiv : (2 * (Q : ℝ) ^ d' * |(centeredBaseQCoeffs d' r Q target d' : ℝ)|) /
      (2 * (Q : ℝ) ^ d') ≤
      (2 * |(target : ℝ)| + (d' : ℝ) * (Q : ℝ) * (Q : ℝ) ^ d') / (2 * (Q : ℝ) ^ d') :=
    div_le_div_of_nonneg_right hreal (by positivity)
  have hne : (Q : ℝ) ^ d' ≠ 0 := hQpow.ne'
  calc
    |(centeredBaseQCoeffs d' r Q target d' : ℝ)|
        = (2 * (Q : ℝ) ^ d' * |(centeredBaseQCoeffs d' r Q target d' : ℝ)|) /
            (2 * (Q : ℝ) ^ d') := by field_simp [hne]
    _ ≤ (2 * |(target : ℝ)| + (d' : ℝ) * (Q : ℝ) * (Q : ℝ) ^ d') / (2 * (Q : ℝ) ^ d') := hdiv
    _ = |(target : ℝ)| / (Q : ℝ) ^ d' + (d' : ℝ) * (Q : ℝ) / 2 := by field_simp [hne]

/-- Specialized top base-`Q` coefficient bound for `target = k * N` at degree `d' = d + L₀`. -/
theorem centeredBaseQCoeffs_multiplier_top_bound (d L₀ : ℕ) {r Q : ℤ} (k N : ℕ)
    (hcop : Int.gcd r Q = 1) (hQ : 0 < Q) (hr : |r| ≤ Q) :
    |(centeredBaseQCoeffs (d + L₀) r Q ((k : ℤ) * (N : ℤ)) (d + L₀) : ℝ)| ≤
      |((k : ℝ) * (N : ℝ)) / (Q : ℝ) ^ (d + L₀)| + ((d + L₀ : ℕ) : ℝ) * (Q : ℝ) / 2 := by
  simpa only [Int.cast_mul, Int.cast_natCast] using
    centeredBaseQCoeffs_top_bound (d + L₀) (target := (k : ℤ) * (N : ℤ)) hcop hQ hr

/-- Dehomogenization `F(X, 1)` of a degree-`d` homogeneous coefficient sequence `c`. -/
noncomputable def dehomogenize (d : ℕ) (c : ℕ → ℤ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range (d + 1), Polynomial.C (c i) * Polynomial.X ^ (d - i)

/-- Coefficients of the product `(Q * X - r * Y) * S(X, Y)` of degree `d'`, where `S` has
degree `d' - 1`. -/
def gsCoeff (d' : ℕ) (Q r : ℤ) (s : ℕ → ℤ) (i : ℕ) : ℤ :=
  (if i < d' then Q * s i else 0) - (if 0 < i then r * s (i - 1) else 0)

/-- Coefficients of the perturbed form `F₀ + 2 * G * S` with `G(X, Y) = Q * X - r * Y`. -/
def perturbationCoeffs (d' : ℕ) (Q r : ℤ) (c₀ s : ℕ → ℤ) (i : ℕ) : ℤ :=
  c₀ i + 2 * gsCoeff d' Q r s i

theorem homogeneousFormEval_gsCoeff {d' : ℕ} (hd : 1 ≤ d') (Q r : ℤ) (s : ℕ → ℤ) (a b : ℤ) :
    homogeneousFormEval d' (gsCoeff d' Q r s) a b =
      (Q * a - r * b) * homogeneousFormEval (d' - 1) s a b := by
  obtain ⟨e, rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, (Nat.sub_add_cancel hd).symm⟩
  simp only [Nat.add_sub_cancel]
  unfold homogeneousFormEval gsCoeff
  have hsplit :
      (∑ i ∈ Finset.range (e + 1 + 1),
          ((if i < e + 1 then Q * s i else 0) - (if 0 < i then r * s (i - 1) else 0)) *
            a ^ (e + 1 - i) * b ^ i) =
      (∑ i ∈ Finset.range (e + 1 + 1),
          (if i < e + 1 then Q * s i else 0) * a ^ (e + 1 - i) * b ^ i) -
      (∑ i ∈ Finset.range (e + 1 + 1),
          (if 0 < i then r * s (i - 1) else 0) * a ^ (e + 1 - i) * b ^ i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsplit]
  have h1 :
      (∑ i ∈ Finset.range (e + 1 + 1),
          (if i < e + 1 then Q * s i else 0) * a ^ (e + 1 - i) * b ^ i) =
      Q * a * ∑ i ∈ Finset.range (e + 1), s i * a ^ (e - i) * b ^ i := by
    rw [Finset.sum_range_succ]
    simp only [lt_self_iff_false, ↓reduceIte, zero_mul, add_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hilt : i < e + 1 := Finset.mem_range.mp hi
    have hsub : e + 1 - i = (e - i) + 1 := by omega
    rw [if_pos hilt, hsub, pow_succ]
    ring
  have h2 :
      (∑ i ∈ Finset.range (e + 1 + 1),
          (if 0 < i then r * s (i - 1) else 0) * a ^ (e + 1 - i) * b ^ i) =
      r * b * ∑ i ∈ Finset.range (e + 1), s i * a ^ (e - i) * b ^ i := by
    rw [Finset.sum_range_succ']
    simp only [lt_self_iff_false, ↓reduceIte, zero_mul, add_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hpos : 0 < i + 1 := Nat.succ_pos i
    have hsub : e + 1 - (i + 1) = e - i := by omega
    rw [if_pos hpos, Nat.add_sub_cancel, hsub, pow_succ]
    ring
  rw [h1, h2]
  ring

theorem homogeneousFormEval_perturbation {d' : ℕ} (hd : 1 ≤ d') (Q r : ℤ)
    (c₀ s : ℕ → ℤ) (a b : ℤ) :
    homogeneousFormEval d' (perturbationCoeffs d' Q r c₀ s) a b =
      homogeneousFormEval d' c₀ a b +
        2 * (Q * a - r * b) * homogeneousFormEval (d' - 1) s a b := by
  have hlin :
      homogeneousFormEval d' (perturbationCoeffs d' Q r c₀ s) a b =
        homogeneousFormEval d' c₀ a b + 2 * homogeneousFormEval d' (gsCoeff d' Q r s) a b := by
    simp only [homogeneousFormEval, perturbationCoeffs, add_mul, mul_assoc,
      Finset.sum_add_distrib, Finset.mul_sum]
  rw [hlin, homogeneousFormEval_gsCoeff hd, mul_assoc]

/-- Perturbing `F₀` by `2 * G * S` preserves the anchor value at `(r, Q)`. -/
theorem homogeneousFormEval_perturbation_anchor {d' : ℕ} (hd : 1 ≤ d') (Q r : ℤ)
    (c₀ s : ℕ → ℤ) :
    homogeneousFormEval d' (perturbationCoeffs d' Q r c₀ s) r Q =
      homogeneousFormEval d' c₀ r Q := by
  rw [homogeneousFormEval_perturbation hd]
  ring

theorem dehomogenize_gsCoeff {d' : ℕ} (hd : 1 ≤ d') (Q r : ℤ) (s : ℕ → ℤ) :
    dehomogenize d' (gsCoeff d' Q r s) =
      (Polynomial.C Q * Polynomial.X - Polynomial.C r) * dehomogenize (d' - 1) s := by
  obtain ⟨e, rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, (Nat.sub_add_cancel hd).symm⟩
  simp only [Nat.add_sub_cancel]
  unfold dehomogenize gsCoeff
  have hsplit :
      (∑ i ∈ Finset.range (e + 1 + 1),
          Polynomial.C ((if i < e + 1 then Q * s i else 0) -
            (if 0 < i then r * s (i - 1) else 0)) * Polynomial.X ^ (e + 1 - i)) =
      (∑ i ∈ Finset.range (e + 1 + 1),
          Polynomial.C (if i < e + 1 then Q * s i else 0) * Polynomial.X ^ (e + 1 - i)) -
      (∑ i ∈ Finset.range (e + 1 + 1),
          Polynomial.C (if 0 < i then r * s (i - 1) else 0) * Polynomial.X ^ (e + 1 - i)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_sub, sub_mul]
  rw [hsplit]
  have h1 :
      (∑ i ∈ Finset.range (e + 1 + 1),
          Polynomial.C (if i < e + 1 then Q * s i else 0) * Polynomial.X ^ (e + 1 - i)) =
      Polynomial.C Q * Polynomial.X *
        ∑ i ∈ Finset.range (e + 1), Polynomial.C (s i) * Polynomial.X ^ (e - i) := by
    rw [Finset.sum_range_succ]
    simp only [lt_self_iff_false, ↓reduceIte, map_zero, zero_mul, add_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hilt : i < e + 1 := Finset.mem_range.mp hi
    have hsub : e + 1 - i = (e - i) + 1 := by omega
    rw [if_pos hilt, map_mul, hsub, pow_succ]
    ring
  have h2 :
      (∑ i ∈ Finset.range (e + 1 + 1),
          Polynomial.C (if 0 < i then r * s (i - 1) else 0) * Polynomial.X ^ (e + 1 - i)) =
      Polynomial.C r *
        ∑ i ∈ Finset.range (e + 1), Polynomial.C (s i) * Polynomial.X ^ (e - i) := by
    rw [Finset.sum_range_succ']
    simp only [lt_self_iff_false, ↓reduceIte, map_zero, zero_mul, add_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hpos : 0 < i + 1 := Nat.succ_pos i
    have hsub : e + 1 - (i + 1) = e - i := by omega
    rw [if_pos hpos, Nat.add_sub_cancel, map_mul, hsub]
    ring
  rw [h1, h2]
  ring

theorem dehomogenize_perturbation {d' : ℕ} (hd : 1 ≤ d') (Q r : ℤ) (c₀ s : ℕ → ℤ) :
    dehomogenize d' (perturbationCoeffs d' Q r c₀ s) =
      dehomogenize d' c₀ +
        Polynomial.C 2 * (Polynomial.C Q * Polynomial.X - Polynomial.C r) *
          dehomogenize (d' - 1) s := by
  have hlin :
      dehomogenize d' (perturbationCoeffs d' Q r c₀ s) =
        dehomogenize d' c₀ + Polynomial.C 2 * dehomogenize d' (gsCoeff d' Q r s) := by
    simp only [dehomogenize, perturbationCoeffs, map_add, map_mul, add_mul, mul_assoc,
      Finset.sum_add_distrib, Finset.mul_sum]
  rw [hlin, dehomogenize_gsCoeff hd, mul_assoc]

/-- Evaluating a dehomogenized polynomial at `r * Q⁻¹` scales by `Q^d` to the homogeneous
evaluation at `(r, Q)`. -/
theorem pow_mul_dehomogenize_eval₂ {R : Type*} [CommRing R] (d : ℕ) (c : ℕ → ℤ)
    (r Q : ℤ) (qInv : R) (hinv : (Q : R) * qInv = 1) :
    (Q : R) ^ d * (dehomogenize d c).eval₂ (Int.castRingHom R) ((r : R) * qInv) =
      (homogeneousFormEval d c r Q : R) := by
  unfold dehomogenize homogeneousFormEval
  rw [Polynomial.eval₂_finsetSum, Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hile : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow,
    Int.coe_castRingHom, Int.cast_mul, Int.cast_pow]
  have hQpow : (Q : R) ^ d = (Q : R) ^ (d - i) * (Q : R) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hile]
  calc
    (Q : R) ^ d * ((c i : R) * ((r : R) * qInv) ^ (d - i))
        = (c i : R) * (r : R) ^ (d - i) * ((Q : R) ^ d * qInv ^ (d - i)) := by
            rw [mul_pow]; ring
    _ = (c i : R) * (r : R) ^ (d - i) * (((Q : R) * qInv) ^ (d - i) * (Q : R) ^ i) := by
            rw [hQpow, mul_pow]; ring
    _ = (c i : R) * (r : R) ^ (d - i) * (Q : R) ^ i := by
            rw [hinv, one_pow, one_mul]

/-- If `N ∣ F(r, Q)` and `Q` is a unit modulo `N`, then `m_N = r * Q⁻¹` is a root of
`F(X, 1)` in `ZMod N`. -/
theorem dehomogenize_eval₂_modN_eq_zero_of_dvd {N d : ℕ} {c : ℕ → ℤ} {r Q : ℤ}
    (hQ : IsUnit (Q : ZMod N)) (hdvd : (N : ℤ) ∣ homogeneousFormEval d c r Q) :
    (dehomogenize d c).eval₂ (Int.castRingHom (ZMod N))
      ((r : ZMod N) * (Q : ZMod N)⁻¹) = 0 := by
  have hinv : (Q : ZMod N) * (Q : ZMod N)⁻¹ = 1 := by
    rw [ZMod.mul_inv_of_unit _ hQ]
  have hscaled := pow_mul_dehomogenize_eval₂ (R := ZMod N) d c r Q (Q : ZMod N)⁻¹ hinv
  have hzero : (homogeneousFormEval d c r Q : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr hdvd
  rw [hzero] at hscaled
  exact (hQ.pow d).mul_right_eq_zero.mp hscaled

/-- For the centered base-`Q` form `F₀` with `F₀(r, Q) = k * N`, `m_N = r * Q⁻¹` is a root
in `ZMod N`. -/
theorem dehomogenize_centeredBaseQ_root_modN (d' : ℕ) {r Q : ℤ} (k N : ℕ)
    (hcop : Int.gcd r Q = 1) (hQ : IsUnit (Q : ZMod N)) :
    (dehomogenize d' (centeredBaseQCoeffs d' r Q ((k : ℤ) * (N : ℤ)))).eval₂
      (Int.castRingHom (ZMod N)) ((r : ZMod N) * (Q : ZMod N)⁻¹) = 0 := by
  apply dehomogenize_eval₂_modN_eq_zero_of_dvd hQ
  rw [centeredBaseQCoeffs_eval_eq d' hcop]
  exact dvd_mul_left (N : ℤ) (k : ℤ)

/-- Any perturbation `F = F₀ + 2 * G * S` preserves the root `m_N = r * Q⁻¹` in `ZMod N`. -/
theorem dehomogenize_perturbation_root_modN {d' : ℕ} (hd : 1 ≤ d') {r Q : ℤ} {c₀ s : ℕ → ℤ}
    {N : ℕ} (hQ : IsUnit (Q : ZMod N)) (hdvd : (N : ℤ) ∣ homogeneousFormEval d' c₀ r Q) :
    (dehomogenize d' (perturbationCoeffs d' Q r c₀ s)).eval₂
      (Int.castRingHom (ZMod N)) ((r : ZMod N) * (Q : ZMod N)⁻¹) = 0 := by
  apply dehomogenize_eval₂_modN_eq_zero_of_dvd hQ
  rwa [homogeneousFormEval_perturbation_anchor hd]

/-! ## Section 2: Content, leading coefficient, and derivative setup checks -/

/-- Integer content of a degree-`d` homogeneous form, defined as the gcd of its `d + 1`
coefficient absolute values. -/
def formContent (d : ℕ) (c : ℕ → ℤ) : ℕ :=
  (Finset.range (d + 1)).gcd (fun i => (c i).natAbs)

theorem formContent_dvd_coeff (d : ℕ) (c : ℕ → ℤ) {i : ℕ} (hi : i ≤ d) :
    (formContent d c : ℤ) ∣ c i :=
  Int.natCast_dvd.mpr (Finset.gcd_dvd (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))

theorem formContent_dvd_eval (d : ℕ) (c : ℕ → ℤ) (a b : ℤ) :
    (formContent d c : ℤ) ∣ homogeneousFormEval d c a b := by
  unfold homogeneousFormEval
  apply Finset.dvd_sum
  intro i hi
  have hile : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (formContent_dvd_coeff d c hile) _) _

/-- If `F(r, Q) = k * N` with `k` prime and every coefficient has absolute value `< min k N`,
then nontrivial content (`formContent > 1`) divides `N` and exposes a proper divisor of `N`. -/
theorem formContent_proper_divisor_of_prime_multiplier {d k N : ℕ} {c : ℕ → ℤ} {r Q : ℤ}
    (hk : Nat.Prime k) (hN : 1 < N)
    (heval : homogeneousFormEval d c r Q = (k : ℤ) * (N : ℤ))
    (hcap : ∀ i ≤ d, (c i).natAbs < min k N)
    (hgt : 1 < formContent d c) :
    formContent d c ∣ N ∧
      1 < (formContent d c).gcd N ∧ (formContent d c).gcd N < N ∧
        (formContent d c).gcd N ∣ N := by
  have hdvd_kN : formContent d c ∣ k * N := by
    have h := formContent_dvd_eval d c r Q
    rw [heval] at h
    exact_mod_cast h
  have hex : ∃ i ≤ d, c i ≠ 0 := by
    by_contra h
    push Not at h
    have hzero : homogeneousFormEval d c r Q = 0 := by
      unfold homogeneousFormEval
      apply Finset.sum_eq_zero
      intro i hi
      rw [h i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
      simp
    rw [hzero] at heval
    have hpos : (0 : ℤ) < (k : ℤ) * (N : ℤ) := by
      have hkpos : (0 : ℤ) < k := by exact_mod_cast hk.pos
      have hNpos : (0 : ℤ) < N := by exact_mod_cast (by omega : 0 < N)
      positivity
    omega
  obtain ⟨i₀, hi₀, hne⟩ := hex
  have hle : formContent d c ≤ (c i₀).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hne)
      (Finset.gcd_dvd (Finset.mem_range.mpr (Nat.lt_succ_of_le hi₀)))
  have hlt_min : formContent d c < min k N := lt_of_le_of_lt hle (hcap i₀ hi₀)
  have hlt_k : formContent d c < k := lt_of_lt_of_le hlt_min (min_le_left k N)
  have hlt_N : formContent d c < N := lt_of_lt_of_le hlt_min (min_le_right k N)
  have hcop : Nat.Coprime (formContent d c) k := by
    rw [Nat.coprime_comm, hk.coprime_iff_not_dvd]
    intro hkdvd
    exact absurd (Nat.le_of_dvd (by omega) hkdvd) (not_le_of_gt hlt_k)
  have hdvd_N : formContent d c ∣ N := hcop.dvd_of_dvd_mul_left hdvd_kN
  have hgcd : (formContent d c).gcd N = formContent d c := Nat.gcd_eq_left hdvd_N
  rw [hgcd]
  exact ⟨hdvd_N, hgt, hlt_N, hdvd_N⟩

/-- A nonunit nonzero leading coefficient strictly smaller than `N` exposes a proper divisor
of `N`. -/
theorem leadingCoeff_proper_divisor {N : ℕ} {c₀ : ℤ}
    (hgt : 1 < c₀.natAbs.gcd N) (hpos : 0 < c₀.natAbs) (hlt : c₀.natAbs < N) :
    1 < c₀.natAbs.gcd N ∧ c₀.natAbs.gcd N < N ∧ c₀.natAbs.gcd N ∣ N :=
  ⟨hgt, lt_of_le_of_lt (Nat.gcd_le_left N hpos) hlt, Nat.gcd_dvd_right _ _⟩

/-- One-coordinate derivative variation identity: evaluating `(F₀ + 2 * G * S)'` at
`m_N = r * Q⁻¹` in `ZMod N` kills the `G * S'` term and leaves `F₀'(m_N) + 2 * Q * S(m_N)`. -/
theorem derivative_eval₂_perturbation_modN {N d' : ℕ} (hd : 1 ≤ d') {Q r : ℤ}
    (c₀ s : ℕ → ℤ) (hQ : IsUnit (Q : ZMod N)) :
    let mN : ZMod N := (r : ZMod N) * (Q : ZMod N)⁻¹
    (Polynomial.derivative (dehomogenize d' (perturbationCoeffs d' Q r c₀ s))).eval₂
      (Int.castRingHom (ZMod N)) mN =
    (Polynomial.derivative (dehomogenize d' c₀)).eval₂ (Int.castRingHom (ZMod N)) mN +
      2 * (Q : ZMod N) * (dehomogenize (d' - 1) s).eval₂ (Int.castRingHom (ZMod N)) mN := by
  intro mN
  have hinv : (Q : ZMod N) * (Q : ZMod N)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hQ
  have hQmN : (Q : ZMod N) * mN - (r : ZMod N) = 0 := by
    dsimp only [mN]
    calc
      (Q : ZMod N) * ((r : ZMod N) * (Q : ZMod N)⁻¹) - (r : ZMod N)
          = (r : ZMod N) * ((Q : ZMod N) * (Q : ZMod N)⁻¹) - (r : ZMod N) := by ring
      _ = 0 := by rw [hinv, mul_one, sub_self]
  rw [dehomogenize_perturbation hd, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_C, Polynomial.derivative_X, zero_mul, zero_add, mul_one, sub_zero]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_sub,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Int.coe_castRingHom, Int.cast_ofNat]
  rw [hQmN]
  ring

/-- Varying the constant term `s₀` (at index `d' - 1` of `S`) shifts `F'(m_N)` in `ZMod N`
linearly with slope `2 * Q`. -/
theorem derivative_eval₂_constShift_modN {N d' : ℕ} (hd : 1 ≤ d') {Q r : ℤ}
    (c₀ s : ℕ → ℤ) (s₀ : ℤ) (hQ : IsUnit (Q : ZMod N)) :
    let mN : ZMod N := (r : ZMod N) * (Q : ZMod N)⁻¹
    let sShift (v : ℤ) : ℕ → ℤ := Function.update s (d' - 1) v
    (Polynomial.derivative (dehomogenize d' (perturbationCoeffs d' Q r c₀ (sShift s₀)))).eval₂
      (Int.castRingHom (ZMod N)) mN =
    (Polynomial.derivative (dehomogenize d' (perturbationCoeffs d' Q r c₀ (sShift 0)))).eval₂
      (Int.castRingHom (ZMod N)) mN + 2 * (Q : ZMod N) * (s₀ : ZMod N) := by
  intro mN sShift
  have hS : dehomogenize (d' - 1) (sShift s₀) =
      dehomogenize (d' - 1) (sShift 0) + Polynomial.C s₀ := by
    unfold dehomogenize
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hpref :
        (∑ i ∈ Finset.range (d' - 1),
          Polynomial.C (sShift s₀ i) * Polynomial.X ^ (d' - 1 - i)) =
        ∑ i ∈ Finset.range (d' - 1),
          Polynomial.C (sShift 0 i) * Polynomial.X ^ (d' - 1 - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hne : i ≠ d' - 1 := ne_of_lt (Finset.mem_range.mp hi)
      simp [sShift, hne]
    rw [hpref]
    simp [sShift]
  rw [derivative_eval₂_perturbation_modN hd c₀ (sShift s₀) hQ,
    derivative_eval₂_perturbation_modN hd c₀ (sShift 0) hQ, hS]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_C, Int.coe_castRingHom]
  ring

/-- When `N` is odd and `Q` is a unit modulo `N`, two constant coefficients giving
`F'(m_N) = 0` in `ZMod N` must be congruent modulo `N`. -/
theorem derivative_zero_modN_dvd_sub {N d' : ℕ} (hd : 1 ≤ d') {Q r : ℤ}
    (c₀ s : ℕ → ℤ) {s₁ s₂ : ℤ}
    (hodd : IsUnit (2 : ZMod N)) (hQ : IsUnit (Q : ZMod N))
    (h₁ : (Polynomial.derivative (dehomogenize d'
      (perturbationCoeffs d' Q r c₀ (Function.update s (d' - 1) s₁)))).eval₂
      (Int.castRingHom (ZMod N)) ((r : ZMod N) * (Q : ZMod N)⁻¹) = 0)
    (h₂ : (Polynomial.derivative (dehomogenize d'
      (perturbationCoeffs d' Q r c₀ (Function.update s (d' - 1) s₂)))).eval₂
      (Int.castRingHom (ZMod N)) ((r : ZMod N) * (Q : ZMod N)⁻¹) = 0) :
    (N : ℤ) ∣ s₁ - s₂ := by
  have heq₁ := derivative_eval₂_constShift_modN hd (r := r) c₀ s s₁ hQ
  have heq₂ := derivative_eval₂_constShift_modN hd (r := r) c₀ s s₂ hQ
  dsimp only at heq₁ heq₂
  rw [h₁] at heq₁
  rw [h₂] at heq₂
  have hdiff : (2 * (Q : ZMod N)) * ((s₁ - s₂ : ℤ) : ZMod N) = 0 := by
    push_cast
    linear_combination heq₂ - heq₁
  have hz : ((s₁ - s₂ : ℤ) : ZMod N) = 0 := (hodd.mul hQ).mul_right_eq_zero.mp hdiff
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (s₁ - s₂) N).mp hz

/-- In any finite set of diameter `< N`, at most one constant coefficient `s₀` causes
`F'(m_N) = 0` in `ZMod N`. -/
theorem card_derivative_zero_le_one_of_diam_lt {N d' : ℕ} (hd : 1 ≤ d') {Q r : ℤ}
    (c₀ s : ℕ → ℤ) (hodd : IsUnit (2 : ZMod N)) (hQ : IsUnit (Q : ZMod N))
    (I : Finset ℤ) (hdiam : ∀ a ∈ I, ∀ b ∈ I, |a - b| < (N : ℤ)) :
    (I.filter (fun s₀ =>
      (Polynomial.derivative (dehomogenize d'
        (perturbationCoeffs d' Q r c₀ (Function.update s (d' - 1) s₀)))).eval₂
        (Int.castRingHom (ZMod N)) ((r : ZMod N) * (Q : ZMod N)⁻¹) = 0)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  obtain ⟨haI, ha0⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbI, hb0⟩ := Finset.mem_filter.mp hb
  have hdvd := derivative_zero_modN_dvd_sub hd c₀ s hodd hQ ha0 hb0
  have hlt := hdiam a haI b hbI
  by_contra hne
  have hpos : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hdvd_abs : (N : ℤ) ∣ |a - b| := by
    rcases abs_cases (a - b) with ⟨h, _⟩ | ⟨h, _⟩
    · rwa [h]
    · rw [h]; exact dvd_neg.mpr hdvd
  have hle : (N : ℤ) ≤ |a - b| := Int.le_of_dvd hpos hdvd_abs
  omega

/-- When `s₀` is restricted to a congruence class modulo `q` with `Coprime q N`, at most one
value in any finite set of diameter `< q * N` causes `F'(m_N) = 0` in `ZMod N`. -/
theorem card_derivative_zero_congr_le_one_of_diam_lt {N q d' : ℕ} (hd : 1 ≤ d')
    {Q r : ℤ} (c₀ s : ℕ → ℤ) (a₀ : ℤ)
    (hodd : IsUnit (2 : ZMod N)) (hQ : IsUnit (Q : ZMod N)) (hqN : Nat.Coprime q N)
    (I : Finset ℤ) (hdiam : ∀ a ∈ I, ∀ b ∈ I, |a - b| < (q : ℤ) * (N : ℤ)) :
    (I.filter (fun s₀ => s₀ ≡ a₀ [ZMOD (q : ℤ)] ∧
      (Polynomial.derivative (dehomogenize d'
        (perturbationCoeffs d' Q r c₀ (Function.update s (d' - 1) s₀)))).eval₂
        (Int.castRingHom (ZMod N)) ((r : ZMod N) * (Q : ZMod N)⁻¹) = 0)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  obtain ⟨haI, haq, ha0⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbI, hbq, hb0⟩ := Finset.mem_filter.mp hb
  have hdvdN := derivative_zero_modN_dvd_sub hd c₀ s hodd hQ ha0 hb0
  have hdvdq : (q : ℤ) ∣ a - b := Int.modEq_iff_dvd.mp (hbq.trans haq.symm)
  have hcop : IsCoprime (q : ℤ) (N : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (by
    simpa [Int.gcd] using hqN)
  have hdvdqN : (q : ℤ) * (N : ℤ) ∣ a - b := hcop.mul_dvd hdvdq hdvdN
  have hlt := hdiam a haI b hbI
  by_contra hne
  have hpos : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hdvd_abs : (q : ℤ) * (N : ℤ) ∣ |a - b| := by
    rcases abs_cases (a - b) with ⟨h, _⟩ | ⟨h, _⟩
    · rwa [h]
    · rw [h]; exact dvd_neg.mpr hdvdqN
  have hle : (q : ℤ) * (N : ℤ) ≤ |a - b| := Int.le_of_dvd hpos hdvd_abs
  omega

/-- An integer interval `Ico L (L + M)` contains at least `M / q` elements in any congruence
class modulo `q > 0`. -/
theorem card_Ico_congr_ge_div (L : ℤ) {M q : ℕ} (hq : 0 < q) (a₀ : ℤ) :
    M / q ≤ ((Finset.Ico L (L + (M : ℤ))).filter (fun s₀ => s₀ ≡ a₀ [ZMOD (q : ℤ)])).card := by
  let r₀ : ℤ := (a₀ - L) % (q : ℤ)
  have hr₀_nonneg : 0 ≤ r₀ := Int.emod_nonneg (a₀ - L) (by omega)
  have hr₀_lt : r₀ < (q : ℤ) := Int.emod_lt_of_pos (a₀ - L) (by omega)
  let f : ℕ → ℤ := fun j => L + r₀ + (j : ℤ) * (q : ℤ)
  have hinj : Set.InjOn f ↑(Finset.range (M / q)) := by
    intro i _ j _ hij
    dsimp only [f] at hij
    have hqne : (q : ℤ) ≠ 0 := by omega
    have : (i : ℤ) = (j : ℤ) := by
      apply mul_right_cancel₀ hqne
      linarith
    exact_mod_cast this
  have hsub : (Finset.range (M / q)).image f ⊆
      (Finset.Ico L (L + (M : ℤ))).filter (fun s₀ => s₀ ≡ a₀ [ZMOD (q : ℤ)]) := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    have hjlt : j < M / q := Finset.mem_range.mp hj
    have hjq : (j + 1) * q ≤ M := by
      calc
        (j + 1) * q ≤ (M / q) * q := Nat.mul_le_mul_right q hjlt
        _ ≤ M := Nat.div_mul_le_self M q
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by nlinarith, ?_⟩, ?_⟩
    · have hjqz : ((j : ℤ) + 1) * (q : ℤ) ≤ (M : ℤ) := by exact_mod_cast hjq
      nlinarith
    · dsimp only [f, r₀]
      have h1 : (a₀ - L) % (q : ℤ) ≡ a₀ - L [ZMOD (q : ℤ)] := Int.mod_modEq _ _
      have h2 : (j : ℤ) * (q : ℤ) ≡ 0 [ZMOD (q : ℤ)] :=
        Int.modEq_zero_iff_dvd.mpr (dvd_mul_left (q : ℤ) (j : ℤ))
      have h3 := (Int.ModEq.add_left L h1).add h2
      simpa [add_assoc] using h3
  calc
    M / q = (Finset.range (M / q)).card := (Finset.card_range _).symm
    _ = ((Finset.range (M / q)).image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- On an interval of length `M` with `0 < M ≤ N`, the full-gcd derivative failure fraction
is at most `1 / M`. -/
theorem derivative_failure_fraction_Ico {N d' M : ℕ} (hd : 1 ≤ d') (hMpos : 0 < M)
    (hMN : M ≤ N) {Q r : ℤ} (c₀ s : ℕ → ℤ) (L : ℤ)
    (hodd : IsUnit (2 : ZMod N)) (hQ : IsUnit (Q : ZMod N)) :
    let I := Finset.Ico L (L + (M : ℤ))
    let bad := I.filter (fun s₀ =>
      (Polynomial.derivative (dehomogenize d'
        (perturbationCoeffs d' Q r c₀ (Function.update s (d' - 1) s₀)))).eval₂
        (Int.castRingHom (ZMod N)) ((r : ZMod N) * (Q : ZMod N)⁻¹) = 0)
    (bad.card : ℝ) / (I.card : ℝ) ≤ 1 / (M : ℝ) := by
  intro I bad
  have hIcard : I.card = M := by
    simp only [I, Int.card_Ico]
    omega
  have hbad : bad.card ≤ 1 := by
    apply card_derivative_zero_le_one_of_diam_lt hd c₀ s hodd hQ I
    intro a ha b hb
    rw [Finset.mem_Ico] at ha hb
    rw [abs_lt]
    omega
  rw [hIcard]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hbad) (Nat.cast_nonneg M)

/-- Restricted to a congruence class modulo `q` on `Ico L (L + M)` with `q ≤ M ≤ N`, the
derivative failure fraction is at most `2 * q / M`. -/
theorem derivative_failure_fraction_congr_Ico {N q d' M : ℕ} (hd : 1 ≤ d') (hq : 0 < q)
    (hqM : q ≤ M) (hMN : M ≤ N) {Q r : ℤ} (c₀ s : ℕ → ℤ) (L a₀ : ℤ)
    (hodd : IsUnit (2 : ZMod N)) (hQ : IsUnit (Q : ZMod N)) :
    let I := Finset.Ico L (L + (M : ℤ))
    let cls := I.filter (fun s₀ => s₀ ≡ a₀ [ZMOD (q : ℤ)])
    let bad := cls.filter (fun s₀ =>
      (Polynomial.derivative (dehomogenize d'
        (perturbationCoeffs d' Q r c₀ (Function.update s (d' - 1) s₀)))).eval₂
        (Int.castRingHom (ZMod N)) ((r : ZMod N) * (Q : ZMod N)⁻¹) = 0)
    (bad.card : ℝ) / (cls.card : ℝ) ≤ 2 * (q : ℝ) / (M : ℝ) := by
  intro I cls bad
  have hbad : bad.card ≤ 1 := by
    have hsub : bad ⊆ I.filter (fun s₀ =>
        (Polynomial.derivative (dehomogenize d'
          (perturbationCoeffs d' Q r c₀ (Function.update s (d' - 1) s₀)))).eval₂
          (Int.castRingHom (ZMod N)) ((r : ZMod N) * (Q : ZMod N)⁻¹) = 0) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨(Finset.mem_filter.mp hx.1).1, hx.2⟩
    refine (Finset.card_le_card hsub).trans ?_
    apply card_derivative_zero_le_one_of_diam_lt hd c₀ s hodd hQ I
    intro a ha b hb
    rw [Finset.mem_Ico] at ha hb
    rw [abs_lt]
    omega
  have hcls : M / q ≤ cls.card := card_Ico_congr_ge_div L hq a₀
  have hdiv_pos : 0 < M / q := Nat.div_pos hqM hq
  have h2div : M ≤ 2 * (M / q) * q := by
    have hrem : M = q * (M / q) + M % q := (Nat.div_add_mod M q).symm
    have hmodlt : M % q < q := Nat.mod_lt M hq
    have h1 : 1 ≤ M / q := hdiv_pos
    nlinarith
  have hcls_r : (M : ℝ) / (2 * (q : ℝ)) ≤ (cls.card : ℝ) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (q : ℝ))]
    have h2div_r : (M : ℝ) ≤ 2 * ((M / q : ℕ) : ℝ) * (q : ℝ) := by exact_mod_cast h2div
    have hcls_r' : ((M / q : ℕ) : ℝ) ≤ (cls.card : ℝ) := by exact_mod_cast hcls
    nlinarith
  have hcls_pos : (0 : ℝ) < (cls.card : ℝ) := by
    exact_mod_cast lt_of_lt_of_le hdiv_pos hcls
  have hMpos_r : (0 : ℝ) < (M : ℝ) := by exact_mod_cast lt_of_lt_of_le hq hqM
  have hqpos_r : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  calc
    (bad.card : ℝ) / (cls.card : ℝ) ≤ 1 / (cls.card : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hbad) hcls_pos.le
    _ ≤ 1 / ((M : ℝ) / (2 * (q : ℝ))) :=
      one_div_le_one_div_of_le (by positivity) hcls_r
    _ = 2 * (q : ℝ) / (M : ℝ) := by rw [one_div_div]

/-! ## Section 3: Affine phase support and exact marginal uniformity -/

/-- For primitive marks `P₁ = (a₁, b₁)` and `P₂ = (a₂, b₂)` with determinant
`D = a₁ * b₂ - b₁ * a₂` and `Δ = |D|`, the unimodular coordinate `u₀ = x * a₂ + y * b₂`
is coprime to `Δ` and satisfies `P₂ ≡ u₀ * P₁ [ZMOD Δ]`. -/
theorem unimodular_mark_congruence {a₁ b₁ a₂ b₂ : ℤ}
    (h₁ : Int.gcd a₁ b₁ = 1) (h₂ : Int.gcd a₂ b₂ = 1) :
    let x := Int.gcdA a₁ b₁
    let y := Int.gcdB a₁ b₁
    let u₀ := x * a₂ + y * b₂
    let D := a₁ * b₂ - b₁ * a₂
    let Δ := D.natAbs
    x * a₁ + y * b₁ = 1 ∧
      a₂ - u₀ * a₁ = -y * D ∧
      b₂ - u₀ * b₁ = x * D ∧
      a₂ ≡ u₀ * a₁ [ZMOD (Δ : ℤ)] ∧
      b₂ ≡ u₀ * b₁ [ZMOD (Δ : ℤ)] ∧
      Int.gcd u₀ Δ = 1 ∧
      IsUnit (u₀ : ZMod Δ) := by
  intro x y u₀ D Δ
  have hbez : x * a₁ + y * b₁ = 1 := by
    have h := Int.gcd_eq_gcd_ab a₁ b₁
    rw [h₁, Nat.cast_one] at h
    linarith
  have ha : a₂ - u₀ * a₁ = -y * D := by
    dsimp only [u₀, D]
    linear_combination -a₂ * hbez
  have hb : b₂ - u₀ * b₁ = x * D := by
    dsimp only [u₀, D]
    linear_combination -b₂ * hbez
  have hΔD : (Δ : ℤ) ∣ D := Int.natAbs_dvd.mpr dvd_rfl
  have hma : a₂ ≡ u₀ * a₁ [ZMOD (Δ : ℤ)] :=
    Int.modEq_iff_dvd.mpr (by rw [show u₀ * a₁ - a₂ = y * D by linarith]; exact dvd_mul_of_dvd_right hΔD y)
  have hmb : b₂ ≡ u₀ * b₁ [ZMOD (Δ : ℤ)] :=
    Int.modEq_iff_dvd.mpr (by rw [show u₀ * b₁ - b₂ = -x * D by linarith]; exact dvd_mul_of_dvd_right hΔD (-x))
  have hgcd : Int.gcd u₀ Δ = 1 := by
    apply Nat.eq_one_of_dvd_one
    have hdu : (Int.gcd u₀ Δ : ℤ) ∣ u₀ := Int.gcd_dvd_left u₀ (Δ : ℤ)
    have hdΔ : (Int.gcd u₀ Δ : ℤ) ∣ (Δ : ℤ) := Int.gcd_dvd_right u₀ (Δ : ℤ)
    have hdD : (Int.gcd u₀ Δ : ℤ) ∣ D := hdΔ.trans hΔD
    have hda₂ : (Int.gcd u₀ Δ : ℤ) ∣ a₂ := by
      have : a₂ = u₀ * a₁ - y * D := by linarith
      rw [this]
      exact dvd_sub (dvd_mul_of_dvd_left hdu a₁) (dvd_mul_of_dvd_right hdD y)
    have hdb₂ : (Int.gcd u₀ Δ : ℤ) ∣ b₂ := by
      have : b₂ = u₀ * b₁ + x * D := by linarith
      rw [this]
      exact dvd_add (dvd_mul_of_dvd_left hdu b₁) (dvd_mul_of_dvd_right hdD x)
    have hd12 : Int.gcd u₀ Δ ∣ Int.gcd a₂ b₂ := by
      exact Nat.dvd_gcd (Int.natCast_dvd.mp hda₂) (Int.natCast_dvd.mp hdb₂)
    rwa [h₂] at hd12
  have hunit : IsUnit (u₀ : ZMod Δ) := by
    have hcop : IsCoprime u₀ (Δ : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
    obtain ⟨c, d, hcd⟩ := hcop
    refine isUnit_iff_exists_inv.mpr ⟨(c : ZMod Δ), ?_⟩
    have hmod : ((c * u₀ + d * (Δ : ℤ) : ℤ) : ZMod Δ) = 1 := by rw [hcd]; simp
    push_cast at hmod
    simpa [ZMod.natCast_self, mul_zero, add_zero, mul_comm] using hmod
  exact ⟨hbez, ha, hb, hma, hmb, hgcd, hunit⟩

/-- Congruent marks `P₂ ≡ u₀ * P₁ [ZMOD M]` force `S(P₂) ≡ u₀^e * S(P₁) [ZMOD M]` for every
degree-`e` homogeneous form `S`. -/
theorem homogeneousFormEval_modEq_of_mark_congruence (e : ℕ) (s : ℕ → ℤ)
    {a₁ b₁ a₂ b₂ u₀ M : ℤ}
    (ha : a₂ ≡ u₀ * a₁ [ZMOD M]) (hb : b₂ ≡ u₀ * b₁ [ZMOD M]) :
    homogeneousFormEval e s a₂ b₂ ≡ u₀ ^ e * homogeneousFormEval e s a₁ b₁ [ZMOD M] := by
  unfold homogeneousFormEval
  rw [Finset.mul_sum]
  apply Int.ModEq.sum
  intro i hi
  have hile : i ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hterm : s i * a₂ ^ (e - i) * b₂ ^ i ≡
      s i * (u₀ * a₁) ^ (e - i) * (u₀ * b₁) ^ i [ZMOD M] :=
    ((ha.pow (e - i)).mul_left (s i)).mul (hb.pow i)
  have heq : s i * (u₀ * a₁) ^ (e - i) * (u₀ * b₁) ^ i =
      u₀ ^ e * (s i * a₁ ^ (e - i) * b₁ ^ i) := by
    rw [mul_pow, mul_pow]
    have hpow : u₀ ^ (e - i) * u₀ ^ i = u₀ ^ e := by
      rw [← pow_add, Nat.sub_add_cancel hile]
    calc
      s i * (u₀ ^ (e - i) * a₁ ^ (e - i)) * (u₀ ^ i * b₁ ^ i)
          = (u₀ ^ (e - i) * u₀ ^ i) * (s i * a₁ ^ (e - i) * b₁ ^ i) := by ring
      _ = u₀ ^ e * (s i * a₁ ^ (e - i) * b₁ ^ i) := by rw [hpow]
  rwa [heq] at hterm

/-- When `q ∣ Δ`, divisibility by `q` at the two marks is equivalent for every homogeneous
form, and the divided evaluations satisfy the determinant congruence modulo `ℓ = Δ / q`. -/
theorem homogeneousFormEval_div_modEq_of_mark_congruence (e : ℕ) (s : ℕ → ℤ)
    {a₁ b₁ a₂ b₂ u₀ : ℤ} {Δ q : ℕ}
    (ha : a₂ ≡ u₀ * a₁ [ZMOD (Δ : ℤ)]) (hb : b₂ ≡ u₀ * b₁ [ZMOD (Δ : ℤ)])
    (hu : Int.gcd u₀ Δ = 1) (hqΔ : q ∣ Δ) (hqpos : 0 < q) :
    (((q : ℤ) ∣ homogeneousFormEval e s a₁ b₁) ↔ ((q : ℤ) ∣ homogeneousFormEval e s a₂ b₂)) ∧
      ((q : ℤ) ∣ homogeneousFormEval e s a₁ b₁ →
        homogeneousFormEval e s a₂ b₂ / (q : ℤ) ≡
          u₀ ^ e * (homogeneousFormEval e s a₁ b₁ / (q : ℤ)) [ZMOD ((Δ / q : ℕ) : ℤ)]) := by
  have hmodΔ := homogeneousFormEval_modEq_of_mark_congruence e s ha hb
  have hqΔz : (q : ℤ) ∣ (Δ : ℤ) := Int.ofNat_dvd.mpr hqΔ
  have hmodq : homogeneousFormEval e s a₂ b₂ ≡
      u₀ ^ e * homogeneousFormEval e s a₁ b₁ [ZMOD (q : ℤ)] :=
    hmodΔ.of_dvd hqΔz
  have hcopq : IsCoprime (q : ℤ) (u₀ ^ e) := by
    have hcopΔ : IsCoprime (Δ : ℤ) u₀ := (Int.isCoprime_iff_gcd_eq_one.mpr hu).symm
    obtain ⟨c, d, hcd⟩ := hcopΔ
    obtain ⟨m, hm⟩ := hqΔz
    have hq1 : IsCoprime (q : ℤ) u₀ := ⟨c * m, d, by linear_combination hcd - c * hm⟩
    exact hq1.pow_right
  refine ⟨?_, ?_⟩
  · constructor
    · intro h1
      have h1' : (q : ℤ) ∣ u₀ ^ e * homogeneousFormEval e s a₁ b₁ := dvd_mul_of_dvd_right h1 _
      exact (Int.modEq_zero_iff_dvd.mp (hmodq.trans (Int.modEq_zero_iff_dvd.mpr h1')))
    · intro h2
      have h1' : (q : ℤ) ∣ u₀ ^ e * homogeneousFormEval e s a₁ b₁ :=
        Int.modEq_zero_iff_dvd.mp (hmodq.symm.trans (Int.modEq_zero_iff_dvd.mpr h2))
      exact hcopq.dvd_of_dvd_mul_left h1'
  · intro h1
    have h2 : (q : ℤ) ∣ homogeneousFormEval e s a₂ b₂ := by
      have h1' : (q : ℤ) ∣ u₀ ^ e * homogeneousFormEval e s a₁ b₁ := dvd_mul_of_dvd_right h1 _
      exact Int.modEq_zero_iff_dvd.mp (hmodq.trans (Int.modEq_zero_iff_dvd.mpr h1'))
    have hqℓ : (q : ℤ) * ((Δ / q : ℕ) : ℤ) = (Δ : ℤ) := by
      exact_mod_cast Nat.mul_div_cancel' hqΔ
    have hdvd : (q : ℤ) * ((Δ / q : ℕ) : ℤ) ∣
        u₀ ^ e * homogeneousFormEval e s a₁ b₁ - homogeneousFormEval e s a₂ b₂ := by
      rw [hqℓ]
      exact Int.modEq_iff_dvd.mp hmodΔ
    have hfactor : u₀ ^ e * homogeneousFormEval e s a₁ b₁ - homogeneousFormEval e s a₂ b₂ =
        (q : ℤ) * (u₀ ^ e * (homogeneousFormEval e s a₁ b₁ / (q : ℤ)) -
          homogeneousFormEval e s a₂ b₂ / (q : ℤ)) := by
      rw [mul_sub, ← mul_assoc, mul_comm (q : ℤ) (u₀ ^ e), mul_assoc,
        Int.mul_ediv_cancel' h1, Int.mul_ediv_cancel' h2]
    rw [hfactor] at hdvd
    have hqne : (q : ℤ) ≠ 0 := by omega
    exact Int.modEq_iff_dvd.mpr ((mul_dvd_mul_iff_left hqne).mp hdvd)

/-- Additive phase shift `t ↦ 2 * g * t` from `ZMod ℓ` into `ZMod (2 * |g| * ℓ)`. -/
def phaseShift (g : ℤ) (ℓ : ℕ) : ZMod ℓ →+ ZMod (2 * g.natAbs * ℓ) :=
  ZMod.lift ℓ
    ⟨(AddMonoidHom.mulLeft ((2 * g : ℤ) : ZMod (2 * g.natAbs * ℓ))).comp
      (Int.castAddHom (ZMod (2 * g.natAbs * ℓ))), by
    change ((2 * g : ℤ) : ZMod (2 * g.natAbs * ℓ)) * ((ℓ : ℤ) : ZMod (2 * g.natAbs * ℓ)) = 0
    rw [← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hg : |g| ∣ g := (abs_dvd g g).mpr dvd_rfl
    push_cast
    exact mul_dvd_mul_right (mul_dvd_mul_left 2 hg) (ℓ : ℤ)⟩

@[simp] theorem phaseShift_intCast (g : ℤ) (ℓ : ℕ) (z : ℤ) :
    phaseShift g ℓ (z : ZMod ℓ) = ((2 * g * z : ℤ) : ZMod (2 * g.natAbs * ℓ)) := by
  unfold phaseShift
  rw [ZMod.lift_coe]
  simp [mul_assoc]

theorem phaseShift_injective {g : ℤ} {ℓ : ℕ} (hg : g ≠ 0) (hℓ : 0 < ℓ) :
    Function.Injective (phaseShift g ℓ) := by
  have : NeZero ℓ := ⟨hℓ.ne'⟩
  rw [injective_iff_map_eq_zero]
  intro t ht
  have hcast : ((t.val : ℤ) : ZMod ℓ) = t := by simp
  rw [← hcast, phaseShift_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at ht
  have hdvd : 2 * g.natAbs * ℓ ∣ (2 * g * (t.val : ℤ)).natAbs := Int.natCast_dvd.mp ht
  have hnat : (2 * g * (t.val : ℤ)).natAbs = 2 * g.natAbs * t.val := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast]
    norm_num
  rw [hnat] at hdvd
  have hpos : 0 < 2 * g.natAbs := by
    have := Int.natAbs_pos.mpr hg
    omega
  have hℓdvd : ℓ ∣ t.val := (Nat.mul_dvd_mul_iff_left hpos).mp hdvd
  have hzero : t.val = 0 := Nat.eq_zero_of_dvd_of_lt hℓdvd (ZMod.val_lt t)
  exact (ZMod.val_eq_zero t).mp hzero

/-- Joint phase subgroup map `t ↦ (2 * g₁ * t, 2 * g₂ * u₀^(d'-1) * t)` in
`ZMod (2 * |g₁| * ℓ) × ZMod (2 * |g₂| * ℓ)`. -/
def jointPhaseHom (g₁ g₂ u₀ : ℤ) (d' ℓ : ℕ) :
    ZMod ℓ →+ ZMod (2 * g₁.natAbs * ℓ) × ZMod (2 * g₂.natAbs * ℓ) :=
  (phaseShift g₁ ℓ).prod
    ((phaseShift g₂ ℓ).comp (AddMonoidHom.mulLeft ((u₀ ^ (d' - 1) : ℤ) : ZMod ℓ)))

theorem jointPhaseHom_intCast (g₁ g₂ u₀ : ℤ) (d' ℓ : ℕ) (z : ℤ) :
    jointPhaseHom g₁ g₂ u₀ d' ℓ (z : ZMod ℓ) =
      (((2 * g₁ * z : ℤ) : ZMod (2 * g₁.natAbs * ℓ)),
        ((2 * g₂ * (u₀ ^ (d' - 1) * z) : ℤ) : ZMod (2 * g₂.natAbs * ℓ))) := by
  unfold jointPhaseHom
  ext
  · simp [phaseShift_intCast]
  · change phaseShift g₂ ℓ (((u₀ ^ (d' - 1) : ℤ) : ZMod ℓ) * (z : ZMod ℓ)) = _
    rw [← Int.cast_mul, phaseShift_intCast]

theorem jointPhaseHom_injective {g₁ g₂ u₀ : ℤ} {d' ℓ : ℕ} (hg₁ : g₁ ≠ 0) (hℓ : 0 < ℓ) :
    Function.Injective (jointPhaseHom g₁ g₂ u₀ d' ℓ) := by
  intro t₁ t₂ h
  exact phaseShift_injective hg₁ hℓ (congrArg Prod.fst h)

/-- The phase subgroup `H = im(jointPhaseHom)` has exact cardinality `ℓ`. -/
theorem jointPhaseHom_image_card {g₁ g₂ u₀ : ℤ} {d' ℓ : ℕ} [NeZero ℓ]
    (hg₁ : g₁ ≠ 0) :
    (Finset.univ.image (jointPhaseHom g₁ g₂ u₀ d' ℓ)).card = ℓ := by
  rw [Finset.card_image_of_injective _ (jointPhaseHom_injective hg₁ (NeZero.pos ℓ)),
    Finset.card_univ, ZMod.card]

/-- Binomial coefficients of the degree-`e` form `c * (x * X + y * Y)^e`. -/
def linearPowerCoeffs (e : ℕ) (c x y : ℤ) (i : ℕ) : ℤ :=
  c * (Nat.choose e i : ℤ) * x ^ (e - i) * y ^ i

theorem homogeneousFormEval_linearPowerCoeffs (e : ℕ) (c x y a b : ℤ) :
    homogeneousFormEval e (linearPowerCoeffs e c x y) a b = c * (x * a + y * b) ^ e := by
  unfold homogeneousFormEval linearPowerCoeffs
  rw [add_comm (x * a) (y * b), add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow, mul_pow]
  ring

/-- Exact affine coset structure in `ZMod m₁ × ZMod m₂`: for any fixed reference form `F₀`
with `q ∣ F₀(P₁)` and `q ∣ F₀(P₂)`, the divided evaluation pairs of `F₀ + 2 * G * S` (over
all degree-`(d'-1)` forms `S` with `q ∣ S(P₁)`) form precisely the coset
`z₀ + im(jointPhaseHom)` of cardinality `ℓ`. -/
theorem perturbation_affine_coset_iff {d' q : ℕ} (hd : 1 ≤ d')
    {Q r a₁ b₁ a₂ b₂ : ℤ} (c₀ : ℕ → ℤ)
    (h₁ : Int.gcd a₁ b₁ = 1) (h₂ : Int.gcd a₂ b₂ = 1)
    (hΔ : 0 < (a₁ * b₂ - b₁ * a₂).natAbs)
    (hqΔ : q ∣ (a₁ * b₂ - b₁ * a₂).natAbs) (hqpos : 0 < q)
    (hF₁ : (q : ℤ) ∣ homogeneousFormEval d' c₀ a₁ b₁)
    (hF₂ : (q : ℤ) ∣ homogeneousFormEval d' c₀ a₂ b₂) :
    let g₁ := Q * a₁ - r * b₁
    let g₂ := Q * a₂ - r * b₂
    let Δ := (a₁ * b₂ - b₁ * a₂).natAbs
    let ℓ := Δ / q
    let u₀ := Int.gcdA a₁ b₁ * a₂ + Int.gcdB a₁ b₁ * b₂
    let z₀ : ZMod (2 * g₁.natAbs * ℓ) × ZMod (2 * g₂.natAbs * ℓ) :=
      (((homogeneousFormEval d' c₀ a₁ b₁ / (q : ℤ) : ℤ) : ZMod (2 * g₁.natAbs * ℓ)),
       ((homogeneousFormEval d' c₀ a₂ b₂ / (q : ℤ) : ℤ) : ZMod (2 * g₂.natAbs * ℓ)))
    ∀ z : ZMod (2 * g₁.natAbs * ℓ) × ZMod (2 * g₂.natAbs * ℓ),
      (∃ s : ℕ → ℤ,
        (q : ℤ) ∣ homogeneousFormEval (d' - 1) s a₁ b₁ ∧
        (q : ℤ) ∣ homogeneousFormEval (d' - 1) s a₂ b₂ ∧
        z = (((homogeneousFormEval d' (perturbationCoeffs d' Q r c₀ s) a₁ b₁ / (q : ℤ) : ℤ) :
                ZMod (2 * g₁.natAbs * ℓ)),
             ((homogeneousFormEval d' (perturbationCoeffs d' Q r c₀ s) a₂ b₂ / (q : ℤ) : ℤ) :
                ZMod (2 * g₂.natAbs * ℓ)))) ↔
      ∃ t : ZMod ℓ, z = z₀ + jointPhaseHom g₁ g₂ u₀ d' ℓ t := by
  intro g₁ g₂ Δ ℓ u₀ z₀ z
  obtain ⟨hbez, _, _, hma, hmb, hgcd, _⟩ := unimodular_mark_congruence h₁ h₂
  have hqne : (q : ℤ) ≠ 0 := by omega
  have hℓpos : 0 < ℓ := Nat.div_pos (Nat.le_of_dvd hΔ hqΔ) hqpos
  have : NeZero ℓ := ⟨hℓpos.ne'⟩
  constructor
  · rintro ⟨s, hs₁, hs₂, rfl⟩
    have hdivmod := (homogeneousFormEval_div_modEq_of_mark_congruence (d' - 1) s
      hma hmb hgcd hqΔ hqpos).2 hs₁
    let t₁ : ℤ := homogeneousFormEval (d' - 1) s a₁ b₁ / (q : ℤ)
    let t₂ : ℤ := homogeneousFormEval (d' - 1) s a₂ b₂ / (q : ℤ)
    refine ⟨(t₁ : ZMod ℓ), ?_⟩
    rw [jointPhaseHom_intCast]
    ext
    · simp only [Prod.fst_add, z₀]
      rw [homogeneousFormEval_perturbation hd,
        Int.add_ediv_of_dvd_left hF₁, Int.mul_ediv_assoc _ hs₁]
      dsimp only [g₁, t₁]
      push_cast
      ring
    · simp only [Prod.snd_add, z₀]
      rw [homogeneousFormEval_perturbation hd,
        Int.add_ediv_of_dvd_left hF₂, Int.mul_ediv_assoc _ hs₂]
      have h2eq : ((2 * g₂ * t₂ : ℤ) : ZMod (2 * g₂.natAbs * ℓ)) =
          ((2 * g₂ * (u₀ ^ (d' - 1) * t₁) : ℤ) : ZMod (2 * g₂.natAbs * ℓ)) := by
        rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
        have hdvdℓ : (ℓ : ℤ) ∣ u₀ ^ (d' - 1) * t₁ - t₂ := Int.modEq_iff_dvd.mp hdivmod
        have hfactor : 2 * g₂ * t₂ - 2 * g₂ * (u₀ ^ (d' - 1) * t₁) =
            -(2 * g₂ * (u₀ ^ (d' - 1) * t₁ - t₂)) := by ring
        rw [hfactor]
        have hg₂ : |g₂| ∣ g₂ := (abs_dvd g₂ g₂).mpr dvd_rfl
        push_cast
        exact dvd_neg.mpr (mul_dvd_mul (mul_dvd_mul_left 2 hg₂) hdvdℓ)
      rw [Int.cast_add]
      congr 1
      all_goals simpa only [g₂, t₂] using h2eq
  · rintro ⟨t, rfl⟩
    let x := Int.gcdA a₁ b₁
    let y := Int.gcdB a₁ b₁
    have htcast : ((t.val : ℤ) : ZMod ℓ) = t := by simp
    let s : ℕ → ℤ := linearPowerCoeffs (d' - 1) ((q : ℤ) * (t.val : ℤ)) x y
    have hs₁_eq : homogeneousFormEval (d' - 1) s a₁ b₁ = (q : ℤ) * (t.val : ℤ) := by
      rw [homogeneousFormEval_linearPowerCoeffs, hbez, one_pow, mul_one]
    have hs₂_eq : homogeneousFormEval (d' - 1) s a₂ b₂ = (q : ℤ) * (t.val : ℤ) * u₀ ^ (d' - 1) := by
      rw [homogeneousFormEval_linearPowerCoeffs]
    have hs₁ : (q : ℤ) ∣ homogeneousFormEval (d' - 1) s a₁ b₁ := by
      rw [hs₁_eq]; exact dvd_mul_right _ _
    have hs₂ : (q : ℤ) ∣ homogeneousFormEval (d' - 1) s a₂ b₂ := by
      rw [hs₂_eq, mul_assoc]; exact dvd_mul_right _ _
    refine ⟨s, hs₁, hs₂, ?_⟩
    rw [← htcast, jointPhaseHom_intCast]
    ext
    · simp only [Prod.fst_add, z₀]
      rw [homogeneousFormEval_perturbation hd,
        Int.add_ediv_of_dvd_left hF₁, Int.mul_ediv_assoc _ hs₁, hs₁_eq,
        Int.mul_ediv_cancel_left _ hqne]
      dsimp only [g₁]
      push_cast
      ring
    · simp only [Prod.snd_add, z₀]
      rw [homogeneousFormEval_perturbation hd,
        Int.add_ediv_of_dvd_left hF₂, Int.mul_ediv_assoc _ hs₂, hs₂_eq,
        mul_assoc (q : ℤ), Int.mul_ediv_cancel_left _ hqne]
      dsimp only [g₂]
      push_cast
      ring

/-- Anchor-mark evaluation congruence: for primitive anchor `R = (r, Q)` with
`J(X, Y) = gcdA(r, Q) * X + gcdB(r, Q) * Y` (`J(R) = 1`) and primitive mark `P = (a, b)`
with `g = Q * a - r * b`, every degree-`d'` homogeneous form satisfies
`D(P) ≡ J(P)^d' * D(R) [ZMOD g]`, and `J(P)` is coprime to `g`. -/
theorem anchor_mark_eval_modEq (d' : ℕ) (c : ℕ → ℤ) {r Q a b : ℤ}
    (hR : Int.gcd r Q = 1) (hP : Int.gcd a b = 1) :
    let J := Int.gcdA r Q * a + Int.gcdB r Q * b
    let g := Q * a - r * b
    homogeneousFormEval d' c a b ≡ J ^ d' * homogeneousFormEval d' c r Q [ZMOD g] ∧
      Nat.Coprime J.natAbs g.natAbs := by
  intro J g
  have hbez : Int.gcdA r Q * r + Int.gcdB r Q * Q = 1 := by
    have h := Int.gcd_eq_gcd_ab r Q
    rw [hR, Nat.cast_one] at h
    linarith
  have ha : a = J * r + Int.gcdB r Q * g := by
    dsimp only [J, g]
    linear_combination -a * hbez
  have hb : b = J * Q - Int.gcdA r Q * g := by
    dsimp only [J, g]
    linear_combination -b * hbez
  have hma : a ≡ J * r [ZMOD g] :=
    Int.modEq_iff_dvd.mpr ⟨-Int.gcdB r Q, by linarith⟩
  have hmb : b ≡ J * Q [ZMOD g] :=
    Int.modEq_iff_dvd.mpr ⟨Int.gcdA r Q, by linarith⟩
  refine ⟨homogeneousFormEval_modEq_of_mark_congruence d' c hma hmb, ?_⟩
  rw [Nat.coprime_iff_gcd_eq_one]
  apply Nat.eq_one_of_dvd_one
  have hdJ : (J.natAbs.gcd g.natAbs : ℤ) ∣ J :=
    (Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _))
  have hdg : (J.natAbs.gcd g.natAbs : ℤ) ∣ g :=
    (Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _))
  have hda : (J.natAbs.gcd g.natAbs : ℤ) ∣ a := by
    rw [ha]
    exact dvd_add (dvd_mul_of_dvd_left hdJ r) (dvd_mul_of_dvd_right hdg _)
  have hdb : (J.natAbs.gcd g.natAbs : ℤ) ∣ b := by
    rw [hb]
    exact dvd_sub (dvd_mul_of_dvd_left hdJ Q) (dvd_mul_of_dvd_right hdg _)
  have hdab : J.natAbs.gcd g.natAbs ∣ Int.gcd a b :=
    Nat.dvd_gcd (Int.natCast_dvd.mp hda) (Int.natCast_dvd.mp hdb)
  rwa [hP] at hdab

/-- The supported residues in `ZMod (M * ℓ)` are those coprime to the base modulus `M`. -/
def supportedResidues (M ℓ : ℕ) [NeZero (M * ℓ)] : Finset (ZMod (M * ℓ)) :=
  Finset.univ.filter (fun z => z.val.Coprime M)

/-- Exact cardinality of `{z : ZMod (M * ℓ) | Coprime z.val M}` is `φ(M) * ℓ`. -/
theorem card_supportedResidues (M ℓ : ℕ) (hM : 0 < M) (hℓ : 0 < ℓ) :
    haveI : NeZero (M * ℓ) := ⟨Nat.mul_ne_zero hM.ne' hℓ.ne'⟩
    (supportedResidues M ℓ).card = M.totient * ℓ := by
  have : NeZero M := ⟨hM.ne'⟩
  have : NeZero (M * ℓ) := ⟨Nat.mul_ne_zero hM.ne' hℓ.ne'⟩
  let φ : (ZMod M)ˣ × Fin ℓ → ZMod (M * ℓ) :=
    fun p => ((p.1.val.val + M * p.2.val : ℕ) : ZMod (M * ℓ))
  have hval (p : (ZMod M)ˣ × Fin ℓ) : (φ p).val = p.1.val.val + M * p.2.val := by
    apply ZMod.val_natCast_of_lt
    have h1 : p.1.val.val < M := ZMod.val_lt p.1.val
    have h2 : p.2.val + 1 ≤ ℓ := p.2.isLt
    calc
      p.1.val.val + M * p.2.val < M + M * p.2.val := Nat.add_lt_add_right h1 _
      _ = M * (p.2.val + 1) := by ring
      _ ≤ M * ℓ := Nat.mul_le_mul_left M h2
  have hinj : Function.Injective φ := by
    intro p q hpq
    have hveq : p.1.val.val + M * p.2.val = q.1.val.val + M * q.2.val := by
      rw [← hval p, ← hval q, hpq]
    have hmod : p.1.val.val = q.1.val.val := by
      have hm := congrArg (· % M) hveq
      simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ZMod.val_lt p.1.val),
        Nat.mod_eq_of_lt (ZMod.val_lt q.1.val)] using hm
    have hdiv : p.2.val = q.2.val := by
      have hd := congrArg (· / M) hveq
      simpa [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt (ZMod.val_lt p.1.val),
        Nat.div_eq_of_lt (ZMod.val_lt q.1.val)] using hd
    ext
    · exact (ZMod.val_injective M hmod)
    · exact hdiv
  have himg : Finset.univ.image φ = supportedResidues M ℓ := by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and, supportedResidues, Finset.mem_filter]
    constructor
    · rintro ⟨p, rfl⟩
      rw [hval p, mul_comm M, Nat.coprime_add_mul_right_left]
      exact (ZMod.isUnit_iff_coprime p.1.val.val M).mp (by simpa using p.1.isUnit)
    · intro hcop
      have hu : IsUnit ((z.val % M : ℕ) : ZMod M) := by
        rw [ZMod.isUnit_iff_coprime, Nat.coprime_iff_gcd_eq_one, ← Nat.gcd_rec,
          Nat.gcd_comm]
        exact hcop.gcd_eq_one
      have hdiv_lt : z.val / M < ℓ := by
        exact Nat.div_lt_of_lt_mul (ZMod.val_lt z)
      refine ⟨(hu.unit, ⟨z.val / M, hdiv_lt⟩), ?_⟩
      apply ZMod.val_injective (M * ℓ)
      rw [hval]
      change (z.val % M : ZMod M).val + M * (z.val / M) = z.val
      rw [ZMod.val_natCast_of_lt (Nat.mod_lt _ hM), add_comm, Nat.div_add_mod]
  rw [← himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod,
    ZMod.card_units_eq_totient, Fintype.card_fin]

/-- Base-residue affine map on `(ZMod (2 * |g|))ˣ`: for `z_*` odd, `|g| ∣ (z_* - h)`, and
`Coprime |h| |g|`, the map `k ↦ z_* + (k - 1) * h` permutes `(ZMod (2 * |g|))ˣ` bijectively
(covering both odd and even `g` uniformly). -/
theorem baseResidue_unit_bijective {g : ℤ} (hg : g ≠ 0) {zStar h : ℤ}
    (hzOdd : Int.gcd zStar 2 = 1) (hdiv : (g.natAbs : ℤ) ∣ zStar - h)
    (hhcop : Nat.Coprime h.natAbs g.natAbs) :
    let M := 2 * g.natAbs
    haveI : NeZero M := ⟨by have := Int.natAbs_pos.mpr hg; omega⟩
    ∃ f : (ZMod M)ˣ → (ZMod M)ˣ,
      (∀ k, (f k : ZMod M) = ((zStar + ((k.val.val : ℤ) - 1) * h : ℤ) : ZMod M)) ∧
      Function.Bijective f := by
  intro M
  haveI : NeZero M := ⟨by have := Int.natAbs_pos.mpr hg; omega⟩
  have hunit (k : (ZMod M)ˣ) : IsUnit ((zStar + ((k.val.val : ℤ) - 1) * h : ℤ) : ZMod M) := by
    have hkcop : Nat.Coprime k.val.val M :=
      (ZMod.isUnit_iff_coprime k.val.val M).mp (by simpa using k.isUnit)
    have hval_cop : Nat.Coprime (zStar + ((k.val.val : ℤ) - 1) * h).natAbs M := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
      have hp1 : (p : ℤ) ∣ zStar + ((k.val.val : ℤ) - 1) * h :=
        Int.natCast_dvd.mpr (hpdvd.trans (Nat.gcd_dvd_left _ _))
      have hpM : p ∣ 2 * g.natAbs := hpdvd.trans (Nat.gcd_dvd_right _ _)
      rcases hp.dvd_mul.mp hpM with hp2 | hpg
      · have hp_eq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
        subst hp_eq
        have hk2 : Nat.Coprime k.val.val 2 := hkcop.coprime_dvd_right (dvd_mul_right 2 g.natAbs)
        have hkeven : (2 : ℤ) ∣ (k.val.val : ℤ) - 1 := by
          obtain ⟨m, hm⟩ := Nat.coprime_two_right.mp hk2
          exact ⟨(m : ℤ), by rw [hm]; push_cast; ring⟩
        have hz2 : (2 : ℤ) ∣ zStar := by
          have := dvd_sub hp1 (dvd_mul_of_dvd_left hkeven h)
          simpa using this
        have : 2 ∣ Int.gcd zStar 2 := Nat.dvd_gcd (Int.natCast_dvd.mp hz2) dvd_rfl
        rw [hzOdd] at this
        omega
      · have hpgz : (p : ℤ) ∣ (g.natAbs : ℤ) := Int.ofNat_dvd.mpr hpg
        have hpzh : (p : ℤ) ∣ zStar - h := hpgz.trans hdiv
        have hphk : (p : ℤ) ∣ (k.val.val : ℤ) * h := by
          have heq : (k.val.val : ℤ) * h = (zStar + ((k.val.val : ℤ) - 1) * h) - (zStar - h) := by
            ring
          rw [heq]
          exact dvd_sub hp1 hpzh
        have hphk' : p ∣ k.val.val * h.natAbs := by
          have := Int.natCast_dvd.mp hphk
          rwa [Int.natAbs_mul, Int.natAbs_natCast] at this
        rcases hp.dvd_mul.mp hphk' with hpk | hph
        · have : p ∣ k.val.val.gcd M := Nat.dvd_gcd hpk hpM
          rw [hkcop] at this
          exact hp.not_dvd_one this
        · have : p ∣ h.natAbs.gcd g.natAbs := Nat.dvd_gcd hph hpg
          rw [hhcop] at this
          exact hp.not_dvd_one this
    have hcop_z : IsCoprime (zStar + ((k.val.val : ℤ) - 1) * h) (M : ℤ) :=
      Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd] using hval_cop)
    obtain ⟨c, d, hcd⟩ := hcop_z
    refine isUnit_iff_exists_inv.mpr ⟨(c : ZMod M), ?_⟩
    have hmod : ((c * (zStar + ((k.val.val : ℤ) - 1) * h) + d * (M : ℤ) : ℤ) : ZMod M) = 1 := by
      rw [hcd]; simp
    push_cast at hmod
    simpa [ZMod.natCast_self, mul_zero, add_zero, mul_comm] using hmod
  let f : (ZMod M)ˣ → (ZMod M)ˣ := fun k => (hunit k).unit
  refine ⟨f, fun k => rfl, ?_⟩
  rw [← Finite.injective_iff_bijective]
  intro k₁ k₂ hfk
  have heq : ((zStar + ((k₁.val.val : ℤ) - 1) * h : ℤ) : ZMod M) =
      ((zStar + ((k₂.val.val : ℤ) - 1) * h : ℤ) : ZMod M) := congrArg Units.val hfk
  have hdvd : (M : ℤ) ∣ ((k₁.val.val : ℤ) - (k₂.val.val : ℤ)) * h := by
    have hsub : ((zStar + ((k₁.val.val : ℤ) - 1) * h -
        (zStar + ((k₂.val.val : ℤ) - 1) * h) : ℤ) : ZMod M) = 0 := by
      rw [Int.cast_sub, heq, sub_self]
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp hsub
    convert h using 1
    ring
  have hk₁2 : Nat.Coprime k₁.val.val 2 :=
    ((ZMod.isUnit_iff_coprime k₁.val.val M).mp (by simpa using k₁.isUnit)).coprime_dvd_right
      (dvd_mul_right 2 g.natAbs)
  have hk₂2 : Nat.Coprime k₂.val.val 2 :=
    ((ZMod.isUnit_iff_coprime k₂.val.val M).mp (by simpa using k₂.isUnit)).coprime_dvd_right
      (dvd_mul_right 2 g.natAbs)
  have h2diff : (2 : ℤ) ∣ (k₁.val.val : ℤ) - (k₂.val.val : ℤ) := by
    obtain ⟨a₁, ha₁⟩ := Nat.coprime_two_right.mp hk₁2
    obtain ⟨a₂, ha₂⟩ := Nat.coprime_two_right.mp hk₂2
    exact ⟨(a₁ : ℤ) - a₂, by rw [ha₁, ha₂]; push_cast; ring⟩
  have hdvdM : (M : ℤ) ∣ (k₁.val.val : ℤ) - (k₂.val.val : ℤ) := by
    by_cases h2g : 2 ∣ g.natAbs
    · have h2zh : (2 : ℤ) ∣ zStar - h := (Int.ofNat_dvd.mpr h2g).trans hdiv
      have hhodd : Nat.Coprime h.natAbs 2 := by
        rw [Nat.coprime_two_right]
        by_contra heven
        have h2h : (2 : ℤ) ∣ h :=
          Int.natCast_dvd.mpr (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp heven))
        have h2z : (2 : ℤ) ∣ zStar := by
          have := dvd_add h2zh h2h
          simpa using this
        have : 2 ∣ Int.gcd zStar 2 := Nat.dvd_gcd (Int.natCast_dvd.mp h2z) dvd_rfl
        rw [hzOdd] at this
        omega
      have hhM : IsCoprime (M : ℤ) h := by
        apply Int.isCoprime_iff_gcd_eq_one.mpr
        change Nat.gcd (2 * g.natAbs) h.natAbs = 1
        rw [Nat.gcd_comm]
        exact (hhodd.mul_right hhcop).gcd_eq_one
      exact hhM.dvd_of_dvd_mul_right hdvd
    · have hg_dvd : (g.natAbs : ℤ) ∣ ((k₁.val.val : ℤ) - (k₂.val.val : ℤ)) * h :=
        (Int.ofNat_dvd.mpr (dvd_mul_left g.natAbs 2)).trans hdvd
      have hcop_gh : IsCoprime (g.natAbs : ℤ) h := by
        apply Int.isCoprime_iff_gcd_eq_one.mpr
        change Nat.gcd g.natAbs h.natAbs = 1
        rw [Nat.gcd_comm]
        exact hhcop.gcd_eq_one
      have hg_diff : (g.natAbs : ℤ) ∣ (k₁.val.val : ℤ) - (k₂.val.val : ℤ) :=
        hcop_gh.dvd_of_dvd_mul_right hg_dvd
      have hcop2g : IsCoprime (2 : ℤ) (g.natAbs : ℤ) := by
        apply Int.isCoprime_iff_gcd_eq_one.mpr
        change Nat.gcd 2 g.natAbs = 1
        exact (Nat.prime_two.coprime_iff_not_dvd.mpr h2g).gcd_eq_one
      have hprod := hcop2g.mul_dvd h2diff hg_diff
      simpa [M] using hprod
  have hzeq : ((k₁.val.val : ℤ) : ZMod M) = ((k₂.val.val : ℤ) : ZMod M) := by
    rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hdvdM
  ext
  simpa using hzeq

/-- Exact marginal uniformity: as `k` ranges uniformly over `(ZMod (2 * |g|))ˣ` (lifted by
any section `lift`) and `t` ranges uniformly over `ZMod ℓ`, the residue
`z(k, t) = z_* + (lift k - 1) * h + 2 * g * (w * t) mod (2 * |g| * ℓ)` is a bijection onto
`{z : ZMod (2 * |g| * ℓ) | Coprime z.val (2 * |g|)}`, hence exact uniform on all `φ(2|g|) * ℓ`
supported residues. -/
theorem marginalPhase_exact_uniform {g : ℤ} {ℓ : ℕ} (hg : g ≠ 0) (hℓ : 0 < ℓ)
    {zStar h : ℤ} (hzOdd : Int.gcd zStar 2 = 1)
    (hdiv : (g.natAbs : ℤ) ∣ zStar - h) (hhcop : Nat.Coprime h.natAbs g.natAbs)
    (lift : (ZMod (2 * g.natAbs))ˣ → ℤ)
    (hlift : ∀ k, (lift k : ZMod (2 * g.natAbs)) = k.val)
    (w : (ZMod ℓ)ˣ) :
    let M := 2 * g.natAbs
    let m := M * ℓ
    haveI : NeZero M := ⟨by have := Int.natAbs_pos.mpr hg; omega⟩
    haveI : NeZero ℓ := ⟨hℓ.ne'⟩
    haveI : NeZero m := ⟨Nat.mul_ne_zero (by have := Int.natAbs_pos.mpr hg; omega) hℓ.ne'⟩
    let Φ : (ZMod M)ˣ × ZMod ℓ → ZMod m := fun p =>
      ((zStar + (lift p.1 - 1) * h : ℤ) : ZMod m) + phaseShift g ℓ (w.val * p.2)
    Function.Injective Φ ∧
      Finset.univ.image Φ = supportedResidues M ℓ ∧
      (∀ z : ZMod m,
        (Finset.univ.filter (fun p : (ZMod M)ˣ × ZMod ℓ => Φ p = z)).card =
          if z.val.Coprime M then 1 else 0) := by
  intro M m
  haveI : NeZero M := ⟨by have := Int.natAbs_pos.mpr hg; omega⟩
  haveI : NeZero ℓ := ⟨hℓ.ne'⟩
  haveI : NeZero m := ⟨Nat.mul_ne_zero (by have := Int.natAbs_pos.mpr hg; omega) hℓ.ne'⟩
  intro Φ
  have hMpos : 0 < M := by have := Int.natAbs_pos.mpr hg; omega
  obtain ⟨f, hfval, hfbi⟩ := baseResidue_unit_bijective hg hzOdd hdiv hhcop
  let red : ZMod m →+* ZMod M := ZMod.castHom (dvd_mul_right M ℓ) (ZMod M)
  have hred_shift (t : ZMod ℓ) : red (phaseShift g ℓ t) = 0 := by
    have ht : ((t.val : ℤ) : ZMod ℓ) = t := by simp
    rw [← ht, phaseShift_intCast, map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hg' : |g| ∣ g := (abs_dvd g g).mpr dvd_rfl
    change ((2 * g.natAbs : ℕ) : ℤ) ∣ 2 * g * (t.val : ℤ)
    push_cast
    exact dvd_mul_of_dvd_left (mul_dvd_mul_left 2 hg') _
  have hred_Φ (p : (ZMod M)ˣ × ZMod ℓ) : red (Φ p) = (f p.1 : ZMod M) := by
    dsimp only [Φ]
    rw [map_add, hred_shift, add_zero, map_intCast, hfval p.1]
    push_cast
    rw [hlift p.1]
    simp
  have hinj : Function.Injective Φ := by
    intro p₁ p₂ hp
    have hred_eq : (f p₁.1 : ZMod M) = (f p₂.1 : ZMod M) := by
      rw [← hred_Φ p₁, ← hred_Φ p₂, hp]
    have hk : p₁.1 = p₂.1 := hfbi.injective (Units.ext hred_eq)
    have hshift : phaseShift g ℓ (w.val * p₁.2) = phaseShift g ℓ (w.val * p₂.2) := by
      dsimp only [Φ] at hp
      rw [hk] at hp
      exact add_left_cancel hp
    have ht : p₁.2 = p₂.2 := w.isUnit.mul_left_cancel (phaseShift_injective hg hℓ hshift)
    exact Prod.ext hk ht
  have hsub : Finset.univ.image Φ ⊆ supportedResidues M ℓ := by
    intro z hz
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hz
    rw [supportedResidues, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← ZMod.isUnit_iff_coprime]
    have hcast : ((Φ p).val : ZMod M) = red (Φ p) := by
      have hz' : (((Φ p).val : ℕ) : ZMod m) = Φ p := ZMod.natCast_zmod_val (Φ p)
      rw [← map_natCast red (Φ p).val, ZMod.natCast_zmod_val]
    rw [hcast, hred_Φ p]
    exact (f p.1).isUnit
  have himg : Finset.univ.image Φ = supportedResidues M ℓ := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod,
      ZMod.card_units_eq_totient, ZMod.card, card_supportedResidues M ℓ hMpos hℓ]
  refine ⟨hinj, himg, ?_⟩
  intro z
  split_ifs with hcop
  · have hmem : z ∈ Finset.univ.image Φ := by
      rw [himg, supportedResidues, Finset.mem_filter]
      exact ⟨Finset.mem_univ z, hcop⟩
    obtain ⟨p₀, _, rfl⟩ := Finset.mem_image.mp hmem
    have hfilt : Finset.univ.filter (fun p : (ZMod M)ˣ × ZMod ℓ => Φ p = Φ p₀) = {p₀} := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun hp => hinj hp, fun hp => hp ▸ rfl⟩
    rw [hfilt, Finset.card_singleton]
  · have hfilt : Finset.univ.filter (fun p : (ZMod M)ˣ × ZMod ℓ => Φ p = z) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p _ hp
      have hmem : z ∈ supportedResidues M ℓ := by
        rw [← himg]
        exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, hp⟩
      exact hcop (Finset.mem_filter.mp hmem).2
    rw [hfilt, Finset.card_empty]

/-- Form-level marginal uniformity theorem: given a primitive anchor `R = (r, Q)`, a primitive
mark `P = (a, b)` with `g = Q * a - r * b ≠ 0`, `N` and `q` coprime to `g`, and reference forms
`F_*` (`F_*(R) = N`, `F_*(P)` odd, `q ∣ F_*(P)`) and `L` (`L(R) = 1`, `q ∣ L(P)`), the divided
coordinate `(F_* + (k - 1) * N * L + 2 * G * S)(P) / q mod (2 * |g| * ℓ)` is exact uniform on
`{z : ZMod (2 * |g| * ℓ) | z.val.Coprime (2 * |g|)}` as `(k, t)` varies uniformly over
`(ZMod (2 * |g|))ˣ × ZMod ℓ`. -/
theorem multiplier_marginal_uniform_from_forms {d' N q ℓ : ℕ} {r Q a b : ℤ}
    (cStar cL : ℕ → ℤ)
    (hR : Int.gcd r Q = 1) (hP : Int.gcd a b = 1)
    (hg : Q * a - r * b ≠ 0) (hℓ : 0 < ℓ) (hqpos : 0 < q)
    (hNg : Nat.Coprime N (Q * a - r * b).natAbs)
    (hqg : Nat.Coprime q (Q * a - r * b).natAbs)
    (hFstarR : homogeneousFormEval d' cStar r Q = (N : ℤ))
    (hLR : homogeneousFormEval d' cL r Q = 1)
    (hFstarOdd : Int.gcd (homogeneousFormEval d' cStar a b) 2 = 1)
    (hqF : (q : ℤ) ∣ homogeneousFormEval d' cStar a b)
    (hqL : (q : ℤ) ∣ homogeneousFormEval d' cL a b)
    (lift : (ZMod (2 * (Q * a - r * b).natAbs))ˣ → ℤ)
    (hlift : ∀ k, (lift k : ZMod (2 * (Q * a - r * b).natAbs)) = k.val)
    (w : (ZMod ℓ)ˣ) :
    let g := Q * a - r * b
    let M := 2 * g.natAbs
    let m := M * ℓ
    let zStar := homogeneousFormEval d' cStar a b / (q : ℤ)
    let h := ((N : ℤ) * homogeneousFormEval d' cL a b) / (q : ℤ)
    haveI : NeZero M := ⟨by have := Int.natAbs_pos.mpr hg; omega⟩
    haveI : NeZero ℓ := ⟨hℓ.ne'⟩
    haveI : NeZero m := ⟨Nat.mul_ne_zero (by have := Int.natAbs_pos.mpr hg; omega) hℓ.ne'⟩
    let Φ : (ZMod M)ˣ × ZMod ℓ → ZMod m := fun p =>
      ((zStar + (lift p.1 - 1) * h : ℤ) : ZMod m) + phaseShift g ℓ (w.val * p.2)
    Function.Injective Φ ∧
      Finset.univ.image Φ = supportedResidues M ℓ ∧
      (∀ z : ZMod m,
        (Finset.univ.filter (fun p : (ZMod M)ˣ × ZMod ℓ => Φ p = z)).card =
          if z.val.Coprime M then 1 else 0) := by
  intro g M m zStar h Φ
  obtain ⟨hmodF, hJg⟩ := anchor_mark_eval_modEq d' cStar hR hP
  obtain ⟨hmodL, _⟩ := anchor_mark_eval_modEq d' cL hR hP
  rw [hFstarR] at hmodF
  rw [hLR, mul_one] at hmodL
  have hqz : (q : ℤ) * zStar = homogeneousFormEval d' cStar a b := Int.mul_ediv_cancel' hqF
  have hqh : (q : ℤ) * h = (N : ℤ) * homogeneousFormEval d' cL a b :=
    Int.mul_ediv_cancel' (dvd_mul_of_dvd_right hqL (N : ℤ))
  have hzOdd : Int.gcd zStar 2 = 1 := by
    apply Nat.eq_one_of_dvd_one
    have h2 : (Int.gcd zStar 2 : ℤ) ∣ homogeneousFormEval d' cStar a b := by
      rw [← hqz]
      exact dvd_mul_of_dvd_right (Int.gcd_dvd_left zStar 2) (q : ℤ)
    have hd : Int.gcd zStar 2 ∣ Int.gcd (homogeneousFormEval d' cStar a b) 2 :=
      Nat.dvd_gcd (Int.natCast_dvd.mp h2) (Int.natCast_dvd.mp (Int.gcd_dvd_right zStar 2))
    rwa [hFstarOdd] at hd
  have hdiv : (g.natAbs : ℤ) ∣ zStar - h := by
    have hmodNL : (N : ℤ) * homogeneousFormEval d' cL a b ≡
        (Int.gcdA r Q * a + Int.gcdB r Q * b) ^ d' * (N : ℤ) [ZMOD g] := by
      have := hmodL.mul_left (N : ℤ)
      rw [mul_comm _ (N : ℤ)]
      exact this
    have hdiff : g ∣ homogeneousFormEval d' cStar a b - (N : ℤ) * homogeneousFormEval d' cL a b :=
      Int.modEq_iff_dvd.mp (hmodNL.trans hmodF.symm)
    have hdiff' : (g.natAbs : ℤ) ∣ (q : ℤ) * (zStar - h) := by
      rw [mul_sub, hqz, hqh]
      exact (Int.natAbs_dvd.mpr dvd_rfl).trans hdiff
    have hcop_gq : IsCoprime (g.natAbs : ℤ) (q : ℤ) := by
      apply Int.isCoprime_iff_gcd_eq_one.mpr
      change Nat.gcd g.natAbs q = 1
      rw [Nat.gcd_comm]
      exact hqg.gcd_eq_one
    exact hcop_gq.dvd_of_dvd_mul_left hdiff'
  have hhcop : Nat.Coprime h.natAbs g.natAbs := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hph : (p : ℤ) ∣ h := Int.natCast_dvd.mpr (hpdvd.trans (Nat.gcd_dvd_left _ _))
    have hpg : p ∣ g.natAbs := hpdvd.trans (Nat.gcd_dvd_right _ _)
    have hpgz : (p : ℤ) ∣ g := (Int.ofNat_dvd.mpr hpg).trans (Int.natAbs_dvd.mpr dvd_rfl)
    have hpNL : (p : ℤ) ∣ (N : ℤ) * homogeneousFormEval d' cL a b := by
      rw [← hqh]
      exact dvd_mul_of_dvd_right hph (q : ℤ)
    have hmodp : (N : ℤ) * homogeneousFormEval d' cL a b ≡
        (N : ℤ) * (Int.gcdA r Q * a + Int.gcdB r Q * b) ^ d' [ZMOD (p : ℤ)] :=
      (hmodL.mul_left (N : ℤ)).of_dvd hpgz
    have hpNJ : (p : ℤ) ∣ (N : ℤ) * (Int.gcdA r Q * a + Int.gcdB r Q * b) ^ d' :=
      Int.modEq_zero_iff_dvd.mp (hmodp.symm.trans (Int.modEq_zero_iff_dvd.mpr hpNL))
    have hpNJ' : p ∣ N * (Int.gcdA r Q * a + Int.gcdB r Q * b).natAbs ^ d' := by
      have := Int.natCast_dvd.mp hpNJ
      rwa [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_pow] at this
    rcases hp.dvd_mul.mp hpNJ' with hpN | hpJpow
    · have : p ∣ N.gcd g.natAbs := Nat.dvd_gcd hpN hpg
      rw [hNg] at this
      exact hp.not_dvd_one this
    · have hpJ : p ∣ (Int.gcdA r Q * a + Int.gcdB r Q * b).natAbs := hp.dvd_of_dvd_pow hpJpow
      have : p ∣ (Int.gcdA r Q * a + Int.gcdB r Q * b).natAbs.gcd g.natAbs := Nat.dvd_gcd hpJ hpg
      rw [hJg] at this
      exact hp.not_dvd_one this
  exact marginalPhase_exact_uniform hg hℓ hzOdd hdiv hhcop lift hlift w

/-! ## Section 4: Prime-multiplier equidistribution bound from `DirichletLZerosOnLine` -/

/-- Specializing `PrimeBinProgressionBound` to a single prime bin `(A, B]`. -/
theorem primeBin_single_progression_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℕ) [NeZero M] (r : (ZMod M)ˣ) (A B : ℕ),
      2 ≤ A → A ≤ B →
      |(((primeBin A B).filter (fun n : ℕ => (r : ZMod M) = (n : ZMod M))).card : ℝ) -
        (((primeBin A B).filter (fun n => n.Coprime M)).card : ℝ) / M.totient| ≤
          2 * K * (1 + Real.log (3 * M * B)) ^ 2 * Real.sqrt B := by
  obtain ⟨K, hK, hprog⟩ :=
    primeBin_progression_of_product_bound (primeBin_product_from_critical_line line)
  refine ⟨K, hK, ?_⟩
  intro M _ r A B hA hAB
  have hdisj : Pairwise (fun i j : Unit => Disjoint (primeBin A B) (primeBin A B)) := by
    intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  have hS : primeBinProducts (fun _ : Unit => A) (fun _ : Unit => B) = primeBin A B := by
    ext n
    simp only [primeBinProducts, Finset.mem_image, Fintype.mem_piFinset, Fintype.prod_unique]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp ()
    · intro hn
      exact ⟨fun _ => n, fun _ => hn, rfl⟩
  have h := hprog M r (fun _ : Unit => A) (fun _ : Unit => B) hdisj (fun _ => hA) (fun _ => hAB)
  simpa only [hS, Fintype.prod_unique] using h

private theorem two_pow_primeFactors_card_le {M : ℕ} (hM : 0 < M) :
    2 ^ M.primeFactors.card ≤ M := by
  calc
    2 ^ M.primeFactors.card = ∏ _p ∈ M.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ M.primeFactors, p := by
        apply Finset.prod_le_prod'
        intro p hp
        exact (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ M := Nat.le_of_dvd hM (Nat.prod_primeFactors_dvd M)

private theorem primeFactors_card_le_two_log {M : ℕ} (hM : 0 < M) :
    (M.primeFactors.card : ℝ) ≤ 2 * Real.log M := by
  have hpow : (2 : ℝ) ^ M.primeFactors.card ≤ (M : ℝ) := by
    exact_mod_cast two_pow_primeFactors_card_le hM
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ M.primeFactors.card) hpow
  rw [Real.log_pow] at hlog
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have he : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
    have hlog4 : 1 < Real.log 4 := by
      rw [← Real.log_exp 1]
      exact Real.log_lt_log (Real.exp_pos 1) he
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    linarith
  nlinarith [Nat.cast_nonneg (α := ℝ) M.primeFactors.card]

private theorem log_le_eight_rpow_one_eighth {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 8 * x ^ (1 / 8 : ℝ) := by
  have hpos : 0 < x ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hx _
  have h := Real.log_le_sub_one_of_pos hpos
  rw [Real.log_rpow hx] at h
  linarith

/-- Prime-multiplier equidistribution from `DirichletLZerosOnLine`: for primes `k ∈ (W, 2W]`
with `W` sufficiently large and any modulus `M ≥ 1`, the residue distribution of `k mod M` on
`(ZMod M)ˣ` has relative error `O(W^(-1/2) * M * (1 + log(W * M))^3)`. -/
theorem prime_multiplier_equidistribution_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ 2 ≤ W₀ ∧
      ∀ (W M : ℕ) [NeZero M], W₀ ≤ W → ∀ r : (ZMod M)ˣ,
        0 < (primeBin W (2 * W)).card ∧
        |(M.totient : ℝ) *
            (((primeBin W (2 * W)).filter (fun k : ℕ => (k : ZMod M) = (r : ZMod M))).card : ℝ) /
            ((primeBin W (2 * W)).card : ℝ) - 1| ≤
          C * (W : ℝ) ^ (-(1 / 2 : ℝ)) * (M : ℝ) * (1 + Real.log ((W : ℝ) * (M : ℝ))) ^ 3 := by
  obtain ⟨K₁, hK₁, hsupply⟩ := primeBin_supply_from_critical_line line
  obtain ⟨K₂, hK₂, hprog⟩ := primeBin_single_progression_from_critical_line line
  let W₀ : ℕ := max 2 (Nat.ceil ((1944 * K₁) ^ 4) + 1)
  refine ⟨72 * K₂ + 4, W₀, by positivity, le_max_left 2 _, ?_⟩
  intro W M _ hW r
  have hW2 : 2 ≤ W := (le_max_left 2 _).trans hW
  have hWr : (2 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW2
  have hWpos : (0 : ℝ) < (W : ℝ) := by linarith
  have hMpos : 0 < M := NeZero.pos M
  have hMr : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMpos
  have hWM1 : (1 : ℝ) ≤ (W : ℝ) * (M : ℝ) := one_le_mul_of_one_le_of_one_le (by linarith) hMr
  have hlogWM_nonneg : 0 ≤ Real.log ((W : ℝ) * (M : ℝ)) := Real.log_nonneg hWM1
  let L : ℝ := 1 + Real.log ((W : ℝ) * (M : ℝ))
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith
  -- Step 1: Lower bound on `(primeBin W (2 * W)).card` from `PrimeBinSupplyBound`.
  have h6W_pos : (0 : ℝ) < 6 * (W : ℝ) := by positivity
  have h6W_ge1 : (1 : ℝ) ≤ 6 * (W : ℝ) := by linarith
  have hlog6W : 1 + Real.log (6 * (W : ℝ)) ≤ 9 * (6 * (W : ℝ)) ^ (1 / 8 : ℝ) := by
    have h1 := log_le_eight_rpow_one_eighth h6W_pos
    have h2 : (1 : ℝ) ≤ (6 * (W : ℝ)) ^ (1 / 8 : ℝ) := Real.one_le_rpow h6W_ge1 (by norm_num)
    linarith
  have hsq6W : (1 + Real.log (6 * (W : ℝ))) ^ 2 ≤ 81 * (6 * (W : ℝ)) ^ (1 / 4 : ℝ) := by
    have hnonneg : 0 ≤ 1 + Real.log (6 * (W : ℝ)) := by
      linarith [Real.log_nonneg h6W_ge1]
    have hsq := pow_le_pow_left₀ hnonneg hlog6W 2
    calc
      (1 + Real.log (6 * (W : ℝ))) ^ 2
          ≤ (9 * (6 * (W : ℝ)) ^ (1 / 8 : ℝ)) ^ 2 := hsq
      _ = 81 * ((6 * (W : ℝ)) ^ (1 / 8 : ℝ)) ^ (2 : ℕ) := by ring
      _ = 81 * (6 * (W : ℝ)) ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul h6W_pos.le]
          norm_num
  have h6_rpow : (6 : ℝ) ^ (1 / 4 : ℝ) ≤ 6 := by
    calc
      (6 : ℝ) ^ (1 / 4 : ℝ) ≤ (6 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 6 := Real.rpow_one 6
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hsupply_err : K₁ * (1 + Real.log (3 * ((2 * W : ℕ) : ℝ))) ^ 2 *
      Real.sqrt ((2 * W : ℕ) : ℝ) ≤ (W : ℝ) / 2 := by
    have h6eq : 3 * ((2 * W : ℕ) : ℝ) = 6 * (W : ℝ) := by push_cast; ring
    have h2eq : ((2 * W : ℕ) : ℝ) = 2 * (W : ℝ) := by push_cast; ring
    rw [h6eq, h2eq, Real.sqrt_mul (by norm_num)]
    have hW_big : (1944 * K₁) ^ 4 ≤ (W : ℝ) := by
      have hceil : Nat.ceil ((1944 * K₁) ^ 4) ≤ W := by
        have := (le_max_right 2 (Nat.ceil ((1944 * K₁) ^ 4) + 1)).trans hW
        omega
      exact (Nat.le_ceil _).trans (by exact_mod_cast hceil)
    have hW_quarter : 1944 * K₁ ≤ (W : ℝ) ^ (1 / 4 : ℝ) := by
      have h := Real.rpow_le_rpow (by positivity) hW_big (by norm_num : (0 : ℝ) ≤ 1 / 4)
      rw [← Real.rpow_natCast (1944 * K₁) 4, ← Real.rpow_mul (by positivity)] at h
      simpa using h
    have hcombine : (1 + Real.log (6 * (W : ℝ))) ^ 2 * (Real.sqrt 2 * Real.sqrt (W : ℝ)) ≤
        972 * (W : ℝ) ^ (3 / 4 : ℝ) := by
      calc
        (1 + Real.log (6 * (W : ℝ))) ^ 2 * (Real.sqrt 2 * Real.sqrt (W : ℝ))
            ≤ (81 * (6 * (W : ℝ)) ^ (1 / 4 : ℝ)) * (2 * Real.sqrt (W : ℝ)) := by
              apply mul_le_mul hsq6W
                (mul_le_mul_of_nonneg_right hsqrt2 (Real.sqrt_nonneg _))
                (by positivity) (by positivity)
        _ = 162 * (6 : ℝ) ^ (1 / 4 : ℝ) * ((W : ℝ) ^ (1 / 4 : ℝ) * (W : ℝ) ^ (1 / 2 : ℝ)) := by
              rw [Real.mul_rpow (by norm_num) hWpos.le, Real.sqrt_eq_rpow]
              ring
        _ ≤ 162 * 6 * ((W : ℝ) ^ (1 / 4 : ℝ) * (W : ℝ) ^ (1 / 2 : ℝ)) := by
              gcongr
        _ = 972 * (W : ℝ) ^ (3 / 4 : ℝ) := by
              rw [← Real.rpow_add hWpos]
              norm_num
    calc
      K₁ * (1 + Real.log (6 * (W : ℝ))) ^ 2 * (Real.sqrt 2 * Real.sqrt (W : ℝ))
          = K₁ * ((1 + Real.log (6 * (W : ℝ))) ^ 2 * (Real.sqrt 2 * Real.sqrt (W : ℝ))) := by ring
      _ ≤ K₁ * (972 * (W : ℝ) ^ (3 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hcombine hK₁
      _ = (1944 * K₁) * (W : ℝ) ^ (3 / 4 : ℝ) / 2 := by ring
      _ ≤ (W : ℝ) ^ (1 / 4 : ℝ) * (W : ℝ) ^ (3 / 4 : ℝ) / 2 := by
          gcongr
      _ = (W : ℝ) / 2 := by
          rw [← Real.rpow_add hWpos]
          norm_num
  have hsup := hsupply W (2 * W) hW2 (by omega)
  have hsubW : ((2 * W : ℕ) : ℝ) - (W : ℝ) = (W : ℝ) := by push_cast; ring
  rw [hsubW] at hsup
  have hPlog : (W : ℝ) / 2 ≤ ((primeBin W (2 * W)).card : ℝ) * Real.log ((2 * W : ℕ) : ℝ) := by
    linarith
  have hlog2W_pos : 0 < Real.log ((2 * W : ℕ) : ℝ) := by
    apply Real.log_pos
    have : (4 : ℝ) ≤ ((2 * W : ℕ) : ℝ) := by exact_mod_cast (by omega : 4 ≤ 2 * W)
    linarith
  have hPpos_r : (0 : ℝ) < ((primeBin W (2 * W)).card : ℝ) := by
    by_contra hle
    push Not at hle
    have : ((primeBin W (2 * W)).card : ℝ) * Real.log ((2 * W : ℕ) : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle hlog2W_pos.le
    linarith
  have hPpos : 0 < (primeBin W (2 * W)).card := by exact_mod_cast hPpos_r
  refine ⟨hPpos, ?_⟩
  -- Step 2: Combine progression bound with non-coprime prime adjustment.
  have hpr := hprog M r W (2 * W) hW2 (by omega)
  have hfilt_eq :
      (primeBin W (2 * W)).filter (fun k : ℕ => (k : ZMod M) = (r : ZMod M)) =
      (primeBin W (2 * W)).filter (fun n : ℕ => (r : ZMod M) = (n : ZMod M)) := by
    ext k
    simp only [Finset.mem_filter, eq_comm]
  rw [hfilt_eq]
  let P := primeBin W (2 * W)
  let P_r := P.filter (fun n : ℕ => (r : ZMod M) = (n : ZMod M))
  let P_cop := P.filter (fun n : ℕ => n.Coprime M)
  let P_ncop := P.filter (fun n : ℕ => ¬ n.Coprime M)
  have hpart : P_cop.card + P_ncop.card = P.card := by
    rw [← Finset.card_union_of_disjoint
      (Finset.disjoint_filter.mpr (fun _ _ h hn => hn h))]
    congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  have hncop_sub : P_ncop ⊆ M.primeFactors := by
    intro k hk
    obtain ⟨hkP, hnc⟩ := Finset.mem_filter.mp hk
    have hkPrime : k.Prime := (Finset.mem_filter.mp hkP).2
    have hkdvd : k ∣ M := by
      by_contra hnd
      exact hnc (hkPrime.coprime_iff_not_dvd.mpr hnd)
    exact Nat.mem_primeFactors.mpr ⟨hkPrime, hkdvd, hMpos.ne'⟩
  have hncop_card : (P_ncop.card : ℝ) ≤ 2 * Real.log M := by
    calc
      (P_ncop.card : ℝ) ≤ (M.primeFactors.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hncop_sub
      _ ≤ 2 * Real.log M := primeFactors_card_le_two_log hMpos
  have htot_pos : (0 : ℝ) < (M.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hMpos
  have htot_le : (M.totient : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.totient_le M
  have hdiff_cop :
      |(P_r.card : ℝ) - (P.card : ℝ) / (M.totient : ℝ)| ≤
        2 * K₂ * (1 + Real.log (3 * M * ((2 * W : ℕ) : ℝ))) ^ 2 * Real.sqrt ((2 * W : ℕ) : ℝ) +
          (P_ncop.card : ℝ) / (M.totient : ℝ) := by
    have hsplit : (P_r.card : ℝ) - (P.card : ℝ) / (M.totient : ℝ) =
        ((P_r.card : ℝ) - (P_cop.card : ℝ) / (M.totient : ℝ)) -
          (P_ncop.card : ℝ) / (M.totient : ℝ) := by
      have hpart_r : (P.card : ℝ) = (P_cop.card : ℝ) + (P_ncop.card : ℝ) := by
        exact_mod_cast hpart.symm
      rw [hpart_r, add_div]
      ring
    rw [hsplit]
    calc
      |((P_r.card : ℝ) - (P_cop.card : ℝ) / (M.totient : ℝ)) -
          (P_ncop.card : ℝ) / (M.totient : ℝ)|
          ≤ |(P_r.card : ℝ) - (P_cop.card : ℝ) / (M.totient : ℝ)| +
              |(P_ncop.card : ℝ) / (M.totient : ℝ)| := abs_sub _ _
      _ ≤ 2 * K₂ * (1 + Real.log (3 * M * ((2 * W : ℕ) : ℝ))) ^ 2 * Real.sqrt ((2 * W : ℕ) : ℝ) +
            (P_ncop.card : ℝ) / (M.totient : ℝ) := by
          rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) htot_pos.le)]
          exact add_le_add hpr le_rfl
  -- Step 3: Multiply by `φ(M) / |P|` and simplify logarithmic factors.
  have hrel_eq :
      |(M.totient : ℝ) * (P_r.card : ℝ) / (P.card : ℝ) - 1| =
        ((M.totient : ℝ) / (P.card : ℝ)) * |(P_r.card : ℝ) - (P.card : ℝ) / (M.totient : ℝ)| := by
    have hneP : (P.card : ℝ) ≠ 0 := hPpos_r.ne'
    have hneT : (M.totient : ℝ) ≠ 0 := htot_pos.ne'
    have halg : (M.totient : ℝ) * (P_r.card : ℝ) / (P.card : ℝ) - 1 =
        ((M.totient : ℝ) / (P.card : ℝ)) * ((P_r.card : ℝ) - (P.card : ℝ) / (M.totient : ℝ)) := by
      field_simp [hneP, hneT]
    rw [halg, abs_mul, abs_of_pos (div_pos htot_pos hPpos_r)]
  have hlog2_lt : Real.log 2 < 1 := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (by norm_num) (by linarith [Real.exp_one_gt_d9])
  have hlog6_lt : Real.log 6 < 2 := by
    have h6e2 : (6 : ℝ) < Real.exp 2 := by
      have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have hsq : (2.7 : ℝ) ^ 2 < (Real.exp 1) ^ 2 := by nlinarith
      have hexp2 : (Real.exp 1) ^ 2 = Real.exp 2 := by
        rw [← Real.exp_nat_mul]
        norm_num
      linarith
    rw [← Real.log_exp 2]
    exact Real.log_lt_log (by norm_num) h6e2
  have hlog2W_le : Real.log ((2 * W : ℕ) : ℝ) ≤ L := by
    have h2W : ((2 * W : ℕ) : ℝ) = 2 * (W : ℝ) := by push_cast; ring
    rw [h2W, Real.log_mul (by norm_num) hWpos.ne']
    have hWM : Real.log (W : ℝ) ≤ Real.log ((W : ℝ) * (M : ℝ)) :=
      Real.log_le_log hWpos (le_mul_of_one_le_right hWpos.le hMr)
    dsimp only [L]
    linarith
  have hlog6WM_le : 1 + Real.log (3 * (M : ℝ) * ((2 * W : ℕ) : ℝ)) ≤ 3 * L := by
    have h6WM : 3 * (M : ℝ) * ((2 * W : ℕ) : ℝ) = 6 * ((W : ℝ) * (M : ℝ)) := by push_cast; ring
    rw [h6WM, Real.log_mul (by norm_num) (by positivity)]
    dsimp only [L]
    linarith
  have hlogM_le : Real.log (M : ℝ) ≤ L := by
    have hMle : Real.log (M : ℝ) ≤ Real.log ((W : ℝ) * (M : ℝ)) :=
      Real.log_le_log (by positivity) (le_mul_of_one_le_left (by positivity) (by linarith))
    dsimp only [L]
    linarith
  have hinvP : 1 / (P.card : ℝ) ≤ 2 * L / (W : ℝ) := by
    have h1 : (W : ℝ) / 2 ≤ (P.card : ℝ) * L :=
      hPlog.trans (mul_le_mul_of_nonneg_left hlog2W_le hPpos_r.le)
    rw [div_le_div_iff₀ hPpos_r hWpos]
    linarith
  have hsqrt_div : Real.sqrt (W : ℝ) / (W : ℝ) = (W : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub_one hWpos.ne']
    norm_num
  have hinvW_le : 1 / (W : ℝ) ≤ (W : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← hsqrt_div]
    have h1W : 1 ≤ Real.sqrt (W : ℝ) := by
      rw [Real.le_sqrt (by norm_num) hWpos.le]
      linarith
    exact div_le_div_of_nonneg_right h1W hWpos.le
  rw [hrel_eq]
  have hstep1 :
      ((M.totient : ℝ) / (P.card : ℝ)) * |(P_r.card : ℝ) - (P.card : ℝ) / (M.totient : ℝ)| ≤
        (1 / (P.card : ℝ)) *
          ((M.totient : ℝ) *
            (2 * K₂ * (1 + Real.log (3 * M * ((2 * W : ℕ) : ℝ))) ^ 2 *
              Real.sqrt ((2 * W : ℕ) : ℝ)) + (P_ncop.card : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hdiff_cop (div_nonneg htot_pos.le hPpos_r.le)
    refine hmul.trans_eq ?_
    have hneT : (M.totient : ℝ) ≠ 0 := htot_pos.ne'
    have hneP : (P.card : ℝ) ≠ 0 := hPpos_r.ne'
    change (M.totient : ℝ) / (P.card : ℝ) * _ = _
    field_simp
    all_goals ring
  have hbracket :
      (M.totient : ℝ) *
        (2 * K₂ * (1 + Real.log (3 * M * ((2 * W : ℕ) : ℝ))) ^ 2 *
          Real.sqrt ((2 * W : ℕ) : ℝ)) + (P_ncop.card : ℝ) ≤
      (36 * K₂ * (M : ℝ) * L ^ 2 * Real.sqrt (W : ℝ)) + 2 * L := by
    have hterm1 :
        (M.totient : ℝ) *
          (2 * K₂ * (1 + Real.log (3 * M * ((2 * W : ℕ) : ℝ))) ^ 2 *
            Real.sqrt ((2 * W : ℕ) : ℝ)) ≤
        36 * K₂ * (M : ℝ) * L ^ 2 * Real.sqrt (W : ℝ) := by
      have hsq : (1 + Real.log (3 * (M : ℝ) * ((2 * W : ℕ) : ℝ))) ^ 2 ≤ 9 * L ^ 2 := by
        have hnonneg : 0 ≤ 1 + Real.log (3 * (M : ℝ) * ((2 * W : ℕ) : ℝ)) := by
          have : (1 : ℝ) ≤ 3 * (M : ℝ) * ((2 * W : ℕ) : ℝ) := by
            have : (2 : ℝ) ≤ ((2 * W : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * W)
            calc (1 : ℝ) ≤ 3 * 1 * 2 := by norm_num
              _ ≤ 3 * (M : ℝ) * ((2 * W : ℕ) : ℝ) := by gcongr
          linarith [Real.log_nonneg this]
        have := pow_le_pow_left₀ hnonneg hlog6WM_le 2
        exact this.trans_eq (by ring)
      have hrt : Real.sqrt ((2 * W : ℕ) : ℝ) ≤ 2 * Real.sqrt (W : ℝ) := by
        rw [show ((2 * W : ℕ) : ℝ) = 2 * (W : ℝ) by push_cast; ring, Real.sqrt_mul (by norm_num)]
        exact mul_le_mul_of_nonneg_right hsqrt2 (Real.sqrt_nonneg _)
      have hprod1 :
          2 * K₂ * (1 + Real.log (3 * (M : ℝ) * ((2 * W : ℕ) : ℝ))) ^ 2 *
            Real.sqrt ((2 * W : ℕ) : ℝ) ≤
          36 * K₂ * L ^ 2 * Real.sqrt (W : ℝ) := by
        calc
          2 * K₂ * (1 + Real.log (3 * (M : ℝ) * ((2 * W : ℕ) : ℝ))) ^ 2 *
              Real.sqrt ((2 * W : ℕ) : ℝ)
              ≤ (2 * K₂ * (9 * L ^ 2)) * (2 * Real.sqrt (W : ℝ)) := by
                apply mul_le_mul
                  (mul_le_mul_of_nonneg_left hsq (by positivity))
                  hrt (Real.sqrt_nonneg _) (by positivity)
          _ = 36 * K₂ * L ^ 2 * Real.sqrt (W : ℝ) := by ring
      calc
        (M.totient : ℝ) *
            (2 * K₂ * (1 + Real.log (3 * (M : ℝ) * ((2 * W : ℕ) : ℝ))) ^ 2 *
              Real.sqrt ((2 * W : ℕ) : ℝ))
            ≤ (M : ℝ) * (36 * K₂ * L ^ 2 * Real.sqrt (W : ℝ)) :=
              mul_le_mul htot_le hprod1 (by positivity) (by positivity)
        _ = 36 * K₂ * (M : ℝ) * L ^ 2 * Real.sqrt (W : ℝ) := by ring
    have hterm2 : (P_ncop.card : ℝ) ≤ 2 * L := hncop_card.trans (by linarith)
    exact add_le_add hterm1 hterm2
  calc
    ((M.totient : ℝ) / (P.card : ℝ)) * |(P_r.card : ℝ) - (P.card : ℝ) / (M.totient : ℝ)|
        ≤ (1 / (P.card : ℝ)) *
            ((M.totient : ℝ) *
              (2 * K₂ * (1 + Real.log (3 * M * ((2 * W : ℕ) : ℝ))) ^ 2 *
                Real.sqrt ((2 * W : ℕ) : ℝ)) + (P_ncop.card : ℝ)) := hstep1
    _ ≤ (2 * L / (W : ℝ)) * (36 * K₂ * (M : ℝ) * L ^ 2 * Real.sqrt (W : ℝ) + 2 * L) :=
        mul_le_mul hinvP hbracket (by positivity) (by positivity)
    _ = 72 * K₂ * (Real.sqrt (W : ℝ) / (W : ℝ)) * (M : ℝ) * L ^ 3 +
          4 * (1 / (W : ℝ)) * L ^ 2 := by ring
    _ ≤ 72 * K₂ * (W : ℝ) ^ (-(1 / 2 : ℝ)) * (M : ℝ) * L ^ 3 +
          4 * (W : ℝ) ^ (-(1 / 2 : ℝ)) * (M : ℝ) * L ^ 3 := by
        rw [hsqrt_div]
        apply add_le_add le_rfl
        have hL23 : L ^ 2 ≤ (M : ℝ) * L ^ 3 := by
          have h1 : L ^ 2 ≤ L ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
          have h2 : L ^ 3 ≤ (M : ℝ) * L ^ 3 :=
            le_mul_of_one_le_left (pow_nonneg (by linarith : 0 ≤ L) 3) hMr
          exact h1.trans h2
        calc
          4 * (1 / (W : ℝ)) * L ^ 2
              ≤ 4 * (W : ℝ) ^ (-(1 / 2 : ℝ)) * ((M : ℝ) * L ^ 3) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hinvW_le (by norm_num)) hL23
                  (sq_nonneg L) (by positivity)
          _ = 4 * (W : ℝ) ^ (-(1 / 2 : ℝ)) * (M : ℝ) * L ^ 3 := by ring
    _ = (72 * K₂ + 4) * (W : ℝ) ^ (-(1 / 2 : ℝ)) * (M : ℝ) * L ^ 3 := by ring

end Cogentic.Randomized

#print axioms Cogentic.Randomized.centeredBaseQCoeffs_multiplier_eval_eq
#print axioms Cogentic.Randomized.centeredBaseQCoeffs_lower_bound
#print axioms Cogentic.Randomized.centeredBaseQCoeffs_multiplier_top_bound
#print axioms Cogentic.Randomized.dehomogenize_centeredBaseQ_root_modN
#print axioms Cogentic.Randomized.dehomogenize_perturbation_root_modN
#print axioms Cogentic.Randomized.formContent_proper_divisor_of_prime_multiplier
#print axioms Cogentic.Randomized.leadingCoeff_proper_divisor
#print axioms Cogentic.Randomized.derivative_eval₂_constShift_modN
#print axioms Cogentic.Randomized.card_derivative_zero_le_one_of_diam_lt
#print axioms Cogentic.Randomized.card_derivative_zero_congr_le_one_of_diam_lt
#print axioms Cogentic.Randomized.derivative_failure_fraction_Ico
#print axioms Cogentic.Randomized.derivative_failure_fraction_congr_Ico
#print axioms Cogentic.Randomized.unimodular_mark_congruence
#print axioms Cogentic.Randomized.perturbation_affine_coset_iff
#print axioms Cogentic.Randomized.jointPhaseHom_image_card
#print axioms Cogentic.Randomized.marginalPhase_exact_uniform
#print axioms Cogentic.Randomized.multiplier_marginal_uniform_from_forms
#print axioms Cogentic.Randomized.prime_multiplier_equidistribution_from_critical_line
