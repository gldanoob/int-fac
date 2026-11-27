import Cogentic.RandomizedReducedFormMinimum
import Cogentic.RandomizedReducedFormRoot

namespace Cogentic.RandomizedQuadraticTargetRoot

open RandomizedReducedFormRoot

private theorem inverse_mod {q N : ℤ} (hq : q.gcd N = 1) :
    q * q.gcdA N ≡ 1 [ZMOD N] := by
  have hbez := Int.gcd_eq_gcd_ab q N
  rw [hq, Int.natCast_one] at hbez
  exact Int.modEq_iff_dvd.mpr ⟨q.gcdB N, by rw [hbez]; ring⟩

/-- A first-column norm numerator times any modular inverse of q squares
to the target times the represented value. The radicand is 2N. -/
theorem targeted_first_column_root_of_inverse {a b c q k N x y t : ℤ} (ha : a = q ^ 2 * t)
    (hdisc : b ^ 2 + 2 * N = a * c) (hk : q * k ≡ 1 [ZMOD N]) :
    ((a * x + b * y) * k) ^ 2 ≡ t * formValue a b c x y [ZMOD N] := by
  have hlead : (a * x + b * y) ^ 2 ≡ a * formValue a b c x y [ZMOD N] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨2 * y ^ 2, ?_⟩
    rw [← norm_identity (x := x) (y := y) hdisc]
    ring
  calc
    _ = (a * x + b * y) ^ 2 * k ^ 2 := by ring
    _ ≡ (a * formValue a b c x y) * k ^ 2 [ZMOD N] := hlead.mul_right _
    _ = (t * formValue a b c x y) * (q * k) ^ 2 := by rw [ha]; ring
    _ ≡ t * formValue a b c x y [ZMOD N] := by
      simpa using (hk.pow 2).mul_left (t * formValue a b c x y)

/-- The extended gcd supplies the inverse when q is a unit modulo N. -/
theorem targeted_first_column_root {a b c q N x y t : ℤ} (ha : a = q ^ 2 * t)
    (hdisc : b ^ 2 + 2 * N = a * c) (hq : q.gcd N = 1) :
    ((a * x + b * y) * q.gcdA N) ^ 2 ≡ t * formValue a b c x y [ZMOD N] :=
  targeted_first_column_root_of_inverse ha hdisc (inverse_mod hq)

/-- The chosen rational target need only agree with the desired target modulo N. -/
theorem targeted_first_column_root_mod {a b c q N x y t v : ℤ} (ha : a = q ^ 2 * t)
    (hdisc : b ^ 2 + 2 * N = a * c) (hq : q.gcd N = 1) (ht : t ≡ v [ZMOD N]) :
    ((a * x + b * y) * q.gcdA N) ^ 2 ≡ v * formValue a b c x y [ZMOD N] :=
  (targeted_first_column_root ha hdisc hq).trans (ht.mul_right _)

/-- Removing the same content from numerator and denominator leaves the
extracted residue unchanged, also for signed integer lifts. -/
theorem cancel_content {n g q w N : ℤ} (hn : n = g * q)
    (hnu : n.gcd N = 1) (hqu : q.gcd N = 1) :
    (g * w) * n.gcdA N ≡ w * q.gcdA N [ZMOD N] := by
  have hi : g * n.gcdA N ≡ q.gcdA N [ZMOD N] := by
    calc
      _ ≡ (q * q.gcdA N) * (g * n.gcdA N) [ZMOD N] := by
        simpa using (inverse_mod hqu).symm.mul_right (g * n.gcdA N)
      _ = q.gcdA N * (n * n.gcdA N) := by rw [hn]; ring
      _ ≡ _ [ZMOD N] := by simpa using (inverse_mod hnu).mul_left (q.gcdA N)
  simpa only [mul_left_comm, mul_assoc] using hi.mul_left w

/-- A known square multiplier of the target is applied directly to the root. -/
theorem retarget_root {z A v v' s N : ℤ} (hz : z ^ 2 ≡ v * A [ZMOD N])
    (hv : s ^ 2 * v ≡ v' [ZMOD N]) : (s * z) ^ 2 ≡ v' * A [ZMOD N] := by
  rw [mul_pow]
  exact (hz.mul_left (s ^ 2)).trans (by simpa only [mul_assoc] using hv.mul_right A)

/-- A nonunit reduced leading coefficient for discriminant -8N gives a
proper factor once N is at least three. -/
theorem proper_gcd_of_reduced_nonunit {A b C N : ℤ} (hN : 3 ≤ N)
    (hA : 0 < A) (hb : |2 * b| ≤ A) (hAC : A ≤ C) (hdisc : b ^ 2 + 2 * N = A * C)
    (hnonunit : A.gcd N ≠ 1) :
    1 < A.gcd N ∧ (A.gcd N : ℤ) < N ∧ (A.gcd N : ℤ) ∣ N := by
  have hNpos : 0 < N := by omega
  have hbound := RandomizedReducedFormMinimum.leading_square_bound hA hb hAC hdisc.symm
  have hlt : A < N := by
    by_contra! h
    have hsq := pow_le_pow_left₀ hNpos.le h 2
    have hmul := mul_nonneg (show 0 ≤ N - 3 by omega) hNpos.le
    nlinarith only [hbound, hsq, hmul, hNpos]
  have hg := Int.gcd_pos_of_ne_zero_left N hA.ne'
  have hle : (A.gcd N : ℤ) ≤ A := Int.le_of_dvd hA (Int.gcd_dvd_left A N)
  exact ⟨by omega, hle.trans_lt hlt, Int.gcd_dvd_right A N⟩

end Cogentic.RandomizedQuadraticTargetRoot
