import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Tactic

namespace Cogentic.Reconstruction

/-- The signed first quotient uses Euclidean division. Each subsequent quotient
    is the one for the previous denominator and its nonnegative remainder. -/
def convergents (u : ℤ) (v : ℕ) : List ℚ :=
  if hv : v = 0 then [0] else
    let a := u / (v:ℤ)
    let r := (u % (v:ℤ)).toNat
    if r = 0 then [a] else
      a :: (convergents (v:ℤ) r).map (fun x => (a:ℚ) + x⁻¹)
termination_by v
decreasing_by
  have pos : (0:ℤ) < v := by exact_mod_cast (Nat.pos_of_ne_zero hv)
  have := Int.emod_lt_of_pos u pos
  omega

private theorem remainder_halves (v r : ℕ) (hr : 0 < r) (within : r < v) : 2*(v%r) ≤ v := by
  by_cases h : 2*r ≤ v
  · have := Nat.mod_lt v hr
    omega
  · have quotient : v/r = 1 := by
      apply Nat.div_eq_of_lt_le <;> omega
    have eq := Nat.mod_add_div v r
    rw [quotient, Nat.mul_one] at eq
    omega

/-- Two Euclidean divisions halve the denominator. This charges every list
    entry even when the final scan stops at its first accepted convergent. -/
theorem convergents_length (u : ℤ) (v : ℕ) (hv : 0 < v) :
    (convergents u v).length ≤ 2*v.log2+1 := by
  have growth (v : ℕ) (hv : 0 < v) (u : ℤ) : 2^((convergents u v).length / 2) ≤ v := by
    induction v using Nat.strong_induction_on generalizing u with
    | h v ih =>
      let r := (u%(v:ℤ)).toNat
      have vp : (0:ℤ) < v := by exact_mod_cast hv
      have rv : r < v := by
        have := Int.emod_lt_of_pos u vp
        dsimp [r]; omega
      rw [convergents, dif_neg hv.ne']
      dsimp only
      change 2^((if r = 0 then [_] else _ :: (convergents (v:ℤ) r).map _).length/2) ≤ v
      split_ifs with r0
      · simpa using (show 1 ≤ v by omega)
      · have rp : 0 < r := by omega
        let s := v%r
        have sv := remainder_halves v r rp rv
        have rs : s < r := Nat.mod_lt v rp
        have next : ((v:ℤ)%(r:ℤ)).toNat = s := by rw [← Int.natCast_mod]; rfl
        rw [List.length_cons, List.length_map, convergents, dif_neg r0]
        dsimp only
        rw [next]
        split_ifs with s0
        · simp only [List.length_cons, List.length_nil]
          norm_num
          omega
        · have bound := ih s (rs.trans rv) (by omega) (r:ℤ)
          simp only [List.length_cons, List.length_map]
          rw [show ∀ a : ℕ, (a+1+1)/2 = a/2+1 by intro; omega, pow_succ]
          dsimp [s] at bound ⊢
          omega
  have power := growth v hv u
  have l := (Nat.le_log2 hv.ne').mpr power
  omega

private theorem convergent_mem (u : ℤ) (v k : ℕ) (hv : 0 < v) :
    ((u:ℝ)/v).convergent k ∈ convergents u v := by
  induction k generalizing u v with
  | zero =>
    have fl : ⌊(u:ℝ)/v⌋ = u/(v:ℤ) := by
      have h := Rat.floor_cast (α := ℝ) ((u:ℚ)/v)
      simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, Rat.floor_intCast_div_natCast] using h
    rw [Real.convergent_zero, fl, convergents, dif_neg hv.ne']
    dsimp only
    split <;> simp
  | succ k ih =>
    have fl : ⌊(u:ℝ)/v⌋ = u/(v:ℤ) := by
      have h := Rat.floor_cast (α := ℝ) ((u:ℚ)/v)
      simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, Rat.floor_intCast_div_natCast] using h
    have pos : (0:ℤ) < v := by exact_mod_cast hv
    have nonneg := Int.emod_nonneg u pos.ne'
    let r := (u%(v:ℤ)).toNat
    have castR : (r:ℤ) = u%(v:ℤ) := Int.toNat_of_nonneg nonneg
    have rem : (((u%(v:ℤ)):ℤ):ℝ) = (r:ℝ) := by exact_mod_cast castR.symm
    rw [Real.convergent_succ, fl, Int.fract_div_intCast_eq_div_intCast_mod, rem, inv_div,
      convergents, dif_neg hv.ne']
    by_cases hr : r = 0
    · simp [show (u%(v:ℤ)).toNat = 0 from hr, hr]
    · rw [if_neg (show (u%(v:ℤ)).toNat ≠ 0 from hr)]
      apply List.mem_cons_of_mem
      apply List.mem_map_of_mem
      simpa only [Int.cast_natCast] using ih (v:ℤ) r (Nat.pos_of_ne_zero hr)

def reconstruct (u : ℤ) (v Q : ℕ) : Option ℚ :=
  let x : ℚ := (u:ℚ)/v
  (convergents u v).find? (fun y => decide (y.den ≤ Q ∧ |x-y| < 1/(2*(Q:ℚ)^2)))

private theorem separated {a b : ℚ} (ne : a ≠ b) :
    1 ≤ |a-b| * (a.den:ℚ) * (b.den:ℚ) := by
  have cross : a.num*(b.den:ℤ) - b.num*(a.den:ℤ) ≠ 0 := by
    intro eq
    exact ne (Rat.eq_iff_mul_eq_mul.mpr (sub_eq_zero.mp eq))
  have nz : (1:ℤ) ≤ |a.num*(b.den:ℤ)-b.num*(a.den:ℤ)| := by
    have := abs_pos.mpr cross
    omega
  have h : (a-b)*(a.den:ℚ)*b.den = (a.num:ℚ)*b.den-(b.num:ℚ)*a.den := by
    calc
      _ = (a*a.den)*b.den-(b*b.den)*a.den := by ring
      _ = _ := by rw [Rat.mul_den_eq_num, Rat.mul_den_eq_num]
  rw [← abs_of_pos (show (0:ℚ) < a.den by exact_mod_cast a.pos),
      ← abs_of_pos (show (0:ℚ) < b.den by exact_mod_cast b.pos), ← abs_mul, ← abs_mul, h]
  exact_mod_cast nz

/-- The strict half-spacing test makes the successful candidate unique. -/
theorem unique {x a b : ℚ} {Q : ℕ} (ha : a.den ≤ Q) (hb : b.den ≤ Q)
    (ea : |x-a| < 1/(2*(Q:ℚ)^2)) (eb : |x-b| < 1/(2*(Q:ℚ)^2)) : a = b := by
  by_contra ne
  have qp : (0:ℚ) < Q := by exact_mod_cast a.pos.trans_le ha
  have e : |a-b| < 1/(Q:ℚ)^2 := by
    have triangle := abs_sub_le a x b
    rw [abs_sub_comm a x] at triangle
    calc
      _ < 1/(2*(Q:ℚ)^2) + 1/(2*(Q:ℚ)^2) := triangle.trans_lt (add_lt_add ea eb)
      _ = _ := by field_simp; ring
  have s := separated ne
  have z : |a-b| *(a.den:ℚ)*(b.den:ℚ) ≤ |a-b| *(Q:ℚ)^2 := by
    rw [sq, ← mul_assoc]
    gcongr
  have t := (lt_div_iff₀ (sq_pos_of_pos qp)).mp e
  linarith

/-- Step 5 returns the exact rational with bounded denominator, including for
    negative coefficients. The result applies to non-reduced input pairs u,v. -/
theorem reconstruct_exact {u : ℤ} {v Q : ℕ} (hv : 0 < v) {y : ℚ} (small : y.den ≤ Q)
    (near : |(u:ℚ)/v-y| < 1/(2*(Q:ℚ)^2)) : reconstruct u v Q = some y := by
  have approx : |((u:ℝ)/v)-(y:ℝ)| < 1/(2*(y.den:ℝ)^2) := by
    have e : |((u:ℝ)/v)-(y:ℝ)| < 1/(2*(Q:ℝ)^2) := by
      have t := (Rat.cast_lt (K := ℝ)).mpr near
      push_cast at t
      exact t
    refine e.trans_le (one_div_le_one_div_of_le (by positivity) ?_)
    gcongr
  obtain ⟨k, eq⟩ := Real.exists_rat_eq_convergent approx
  have member : y ∈ convergents u v := eq ▸ convergent_mem u v k hv
  unfold reconstruct
  generalize findEq : List.find? _ (convergents u v) = got
  cases got with
  | none =>
    have := List.find?_eq_none.mp findEq y member
    exact False.elim (this (decide_eq_true ⟨small,near⟩))
  | some z =>
    have test := List.find?_some findEq
    simp only [decide_eq_true_eq] at test
    exact congrArg some (unique test.1 small test.2 near)

/-- The candidate exponent uses this lcm only when every coordinate has
    passed the strict rational reconstruction test. -/
def multiplier {ι : Type*} [Fintype ι] (approx : ι → ℚ) (Q : ℕ) : Option ℕ :=
  let get (i : ι) := reconstruct (approx i).num (approx i).den Q
  if ∀ i, (get i).isSome = true then
    some (Finset.univ.lcm (fun i => ((get i).getD 0).den))
  else none

theorem multiplier_exact {ι : Type*} [Fintype ι] (approx x : ι → ℚ) (Q : ℕ)
    (small : ∀ i, (x i).den ≤ Q) (near : ∀ i, |approx i-x i| < 1/(2*(Q:ℚ)^2)) :
    multiplier approx Q = some (Finset.univ.lcm (fun i => (x i).den)) := by
  have same (i) := reconstruct_exact (u := (approx i).num) (v := (approx i).den)
    (approx i).pos (small i) (by simpa only [Rat.num_div_den] using near i)
  simp [multiplier, same]

/-- The lcm of the recovered denominators, even when smaller than the lattice
    determinant, clears every rational coordinate of the exact linear system. -/
theorem clear_linear_system {ι κ : Type*} [Fintype ι] (A : κ → ι → ℤ) (b : κ → ℤ)
    (x : ι → ℚ) (solves : ∀ j, (b j:ℚ) + ∑ i, (A j i:ℚ)*x i = 0) :
    let m := Finset.univ.lcm (fun i => (x i).den)
    0 < m ∧ ∃ z : ι → ℤ, (∀ i, (z i:ℚ) = x i*(m:ℚ)) ∧
      ∀ j, b j*(m:ℤ) + ∑ i, A j i*z i = 0 := by
  let m := Finset.univ.lcm (fun i => (x i).den)
  let z (i : ι) := (x i).num*(m/(x i).den:ℕ)
  have nonzero : m ≠ 0 := by
    simp [m, Finset.lcm_eq_zero_iff]
  have coeff (i : ι) : (z i:ℚ) = x i*(m:ℚ) := by
    have d : (x i).den ∣ m := Finset.dvd_lcm (Finset.mem_univ i)
    have eq := Nat.mul_div_cancel' d
    simp only [z, Int.cast_mul, Int.cast_natCast]
    calc
      _ = (x i*(x i).den)*(m/(x i).den:ℕ) := by rw [Rat.mul_den_eq_num]
      _ = _ := by rw [mul_assoc, ← Nat.cast_mul, eq]
  refine ⟨Nat.pos_of_ne_zero nonzero, z, coeff, fun j => ?_⟩
  apply Rat.intCast_injective
  push_cast
  simp_rw [coeff, ← mul_assoc]
  rw [← Finset.sum_mul, ← add_mul, solves, zero_mul]

end Cogentic.Reconstruction
