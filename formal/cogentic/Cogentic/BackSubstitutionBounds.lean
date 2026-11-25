import Cogentic.FractionFreeBounds

/-! Sizes of the rational vectors actually constructed by recursive back substitution. -/
namespace Cogentic.Elimination
open Finset

/-- A single signed denominator certifies all vector coordinates. -/
def BoundedFraction {n : ℕ} (x : Fin n → ℚ) (B : ℤ) : Prop :=
  ∃ D : ℤ, D ≠ 0 ∧ |D| ≤ B ∧ ∃ z : Fin n → ℤ,
    (∀ i, |z i| ≤ B) ∧ ∀ i, x i*(D:ℚ) = z i

/-- Reducing each coordinate cannot grow either of its two integer entries. -/
theorem BoundedFraction.reduced {n : ℕ} {x : Fin n → ℚ} {B : ℤ}
    (h : BoundedFraction x B) (i : Fin n) : |(x i).num| ≤ B ∧ ((x i).den:ℤ) ≤ B := by
  obtain ⟨D,nz,bd,z,bz,eq⟩ := h
  have frac : x i = Rat.divInt (z i) D := by
    rw [Rat.divInt_eq_div]; exact (eq_div_iff (Int.cast_ne_zero.mpr nz)).mpr (eq i)
  obtain ⟨c,e,v⟩ := Rat.num_den_mk nz frac
  have lc : (1:ℤ) ≤ |c| := by
    have ne : c≠0 := by intro he; simp [he] at v; exact nz v
    have := abs_pos.mpr ne
    omega
  constructor
  · calc
      _ ≤ |c| * |(x i).num| := by simpa using mul_le_mul_of_nonneg_right lc (abs_nonneg (x i).num)
      _ = |z i| := by rw [e,abs_mul]
      _ ≤ B := bz i
  · calc
      _ ≤ |c| * ((x i).den:ℤ) := by simpa using mul_le_mul_of_nonneg_right lc (Int.natCast_nonneg (x i).den)
      _ = |D| := by rw [v,abs_mul,abs_of_nonneg (Int.natCast_nonneg _)]
      _ ≤ B := bd

/-- Every partial dot product in back substitution keeps the same denominator.
This covers all orders of evaluating the finite sum. -/
theorem BoundedFraction.partial_sum {n : ℕ} {x : Fin n → ℚ} {B C : ℤ}
    (h : BoundedFraction x B) (a : Fin n → ℤ) (ha : ∀ i, |a i|≤C)
    (nonneg : 0≤C) (s : Finset (Fin n)) :
    let q := ∑ i ∈ s, (a i:ℚ)*x i
    |q.num| ≤ ((s.card:ℤ)*C+1)*B ∧ (q.den:ℤ) ≤ ((s.card:ℤ)*C+1)*B := by
  obtain ⟨D,nz,bd,z,bz,eq⟩ := h
  let q := ∑ i ∈ s, (a i:ℚ)*x i
  let b := ((s.card:ℤ)*C+1)*B
  have bp : 0≤B := (abs_nonneg _).trans bd
  have bound : BoundedFraction (fun _ : Fin 1 => q) b := by
    refine ⟨D,nz,?_,fun _ => ∑ i ∈ s, a i*z i,?_,?_⟩
    · apply bd.trans
      dsimp [b]; nlinarith [mul_nonneg (Int.natCast_nonneg s.card) (mul_nonneg nonneg bp)]
    · intro _
      calc
        _ ≤ ∑ i ∈ s, |a i*z i| := abs_sum_le_sum_abs ..
        _ ≤ ∑ _i ∈ s, C*B := sum_le_sum fun i _ => by rw [abs_mul]; exact mul_le_mul (ha i) (bz i) (abs_nonneg _) nonneg
        _ ≤ b := by simp [b]; nlinarith
    · intro _; dsimp only [q]; push_cast; simp only [sum_mul,mul_assoc,eq]
  exact bound.reduced 0

private theorem BoundedFraction.mono {n : ℕ} {x : Fin n → ℚ} {b c : ℤ}
    (h : BoundedFraction x b) (le : b ≤ c) : BoundedFraction x c := by
  obtain ⟨D,nz,bd,z,bz,eq⟩ := h
  exact ⟨D,nz,bd.trans le,z,fun i => (bz i).trans le,eq⟩

private theorem free_fraction {n : ℕ} {x : Fin n → ℚ} {b : ℤ}
    (h : BoundedFraction x b) (a : ℤ) (ha : |a| ≤ 1) :
    BoundedFraction (Fin.cons (a:ℚ) x) b := by
  obtain ⟨D,nz,bd,z,bz,eq⟩ := h
  refine ⟨D,nz,bd,Fin.cons (a*D) z,?_,?_⟩
  · apply Fin.cases
    · change |a*D| ≤ b
      rw [abs_mul]; calc
        _ ≤ 1*|D| := mul_le_mul_of_nonneg_right ha (abs_nonneg D)
        _ ≤ b := by simpa using bd
    · simpa using bz
  · exact Fin.cases (by simp) (by simpa using eq)

/-- A pivot growing a vector with common denominator D needs only p.head * D,
regardless of the number of terms in the right-hand-side dot product. -/
private theorem pivot_fraction {n : ℕ} (p : Row (n+1)) (nz : p.head ≠ 0) {C b : ℤ}
    (hc : ∀ j, |p.aug j| ≤ C) {x : Fin n → ℚ} (h : BoundedFraction x b) :
    BoundedFraction (Fin.cons (p.recover x) x) (((n:ℤ)+1)*C*b) := by
  obtain ⟨D,dnz,bd,z,bz,eq⟩ := h
  have hd : |p.head| ≤ C := hc (some 0)
  have hr : |p.rhs| ≤ C := hc none
  have ht (i : Fin n) : |p.drop.coeffs.get i| ≤ C := by
    simpa [Row.drop,Row.aug,Vector.get_eq_getElem] using hc (some i.succ)
  have cp : 0≤C := (abs_nonneg _).trans hd
  have bp : 0≤b := (abs_nonneg _).trans bd
  let v := p.rhs*D-∑ i, p.drop.coeffs.get i*z i
  have cb : C*b ≤ ((n:ℤ)+1)*C*b := by nlinarith [mul_nonneg (Int.natCast_nonneg n) (mul_nonneg cp bp)]
  refine ⟨p.head*D,mul_ne_zero nz dnz,?_,Fin.cons v (fun i => p.head*z i),?_,?_⟩
  · rw [abs_mul]; exact (mul_le_mul hd bd (abs_nonneg _) cp).trans cb
  · apply Fin.cases
    · change |v| ≤ _
      calc
        |v| ≤ |p.rhs*D|+|∑ i, p.drop.coeffs.get i*z i| := abs_sub ..
        _ ≤ C*b+∑ i, |p.drop.coeffs.get i*z i| := add_le_add (by rw [abs_mul]; exact mul_le_mul hr bd (abs_nonneg _) cp) (abs_sum_le_sum_abs ..)
        _ ≤ C*b+∑ _ : Fin n, C*b := by
          gcongr with i
          rw [abs_mul]; exact mul_le_mul (ht i) (bz i) (abs_nonneg _) cp
        _ = _ := by simp; ring
    · intro i; simp only [Fin.cons_succ,abs_mul]; exact (mul_le_mul hd (bz i) (abs_nonneg _) cp).trans cb
  · apply Fin.cases
    · change p.recover x*((p.head*D:ℤ):ℚ)=(v:ℚ)
      have nzq : (p.head:ℚ)≠0 := Int.cast_ne_zero.mpr nz
      dsimp only [v,Row.recover,Row.eval]
      push_cast
      rw [show ((p.rhs:ℚ)-∑ i, (p.drop.coeffs.get i:ℚ)*x i)/p.head*((p.head:ℚ)*D) =
          ((p.rhs:ℚ)-∑ i, (p.drop.coeffs.get i:ℚ)*x i)*D by field_simp]
      simp only [sub_mul,Finset.sum_mul,mul_assoc,eq]
    · intro i; simp only [Fin.cons_succ,Int.cast_mul]; rw [mul_left_comm,eq]

private def backCap (C n : ℕ) : ℕ := (n+1).factorial*C^n

/-- On every successful suffix of the actual elimination, every allocation of
free variables from {-1,0,1} gives bounded integral numerators and a common
denominator. The integer height bound depends on the initial system, including
when this suffix begins after many content-normalized pivots. -/
theorem solve_back_substitution_height {N H : ℕ} (base : List (Row N)) (hp : 1≤H)
    (input : ∀ r∈base, ∀ j, (Row.aug r j).natAbs ≤ H)
    {n : ℕ} {rows : List (Row n)} (reachable : SolveStep base rows)
    {f : Family n} (ok : solve n rows = some f) (y : Fin f.free → ℤ) (yb : ∀ i, |y i|≤1) :
    BoundedFraction (f.values (fun i => (y i:ℚ)))
      (((n+1).factorial*((base.length+1).factorial*H^(base.length+1))^n : ℕ):ℤ) := by
  let C := (base.length+1).factorial*H^(base.length+1)
  have cp : 1≤C := Nat.mul_pos (Nat.factorial_pos _) (Nat.pow_pos hp)
  change BoundedFraction _ (backCap C n : ℤ)
  induction n with
  | zero => exact ⟨1,one_ne_zero,by simp [backCap],Fin.elim0,fun i => i.elim0,fun i => i.elim0⟩
  | succ n ih =>
    have cap : backCap C (n+1) = (n+2)*C*backCap C n := by simp [backCap,Nat.factorial_succ,pow_succ]; ring
    have bp : 0≤(backCap C n:ℤ) := by positivity
    have cpz : (1:ℤ)≤C := by exact_mod_cast cp
    rw [solve] at ok
    split at ok
    next empty =>
      cases v : solve n (rows.map Row.drop) with
      | none => simp [v] at ok
      | some tail =>
        have hf : freeLift tail=f := by simpa [v] using ok
        subst f
        change Fin (tail.free+1) → ℤ at y
        have b := ih (SolveStep.drop reachable empty) v (fun i => y i.succ) (fun i => yb i.succ)
        have vals : (freeLift tail).values (fun i => (y i:ℚ)) = Fin.cons (y 0:ℚ) (tail.values (fun i => (y i.succ:ℚ))) := by
          funext i; simp [Family.values,freeLift]
        rw [vals,cap]; push_cast
        apply (free_fraction b (y 0) (yb (0:Fin (tail.free+1)))).mono
        nlinarith [mul_nonneg (Int.natCast_nonneg n) (mul_nonneg (by omega : (0:ℤ)≤C) bp),mul_le_mul_of_nonneg_right cpz bp]
    next p found =>
      cases v : solve n (rows.map p.reduce) with
      | none => simp [v] at ok
      | some tail =>
        have hf : pivotLift p tail=f := by simpa [v] using ok
        subst f
        have b := ih (SolveStep.pivot reachable found) v y yb
        have vals : (pivotLift p tail).values (fun i => (y i:ℚ)) = Fin.cons (p.recover (tail.values (fun i => (y i:ℚ)))) (tail.values (fun i => (y i:ℚ))) := by
          funext i; simp [Family.values,pivotLift]
        have bound (j) : |p.aug j| ≤ (C:ℤ) := by
          rw [Int.abs_eq_natAbs]; exact_mod_cast solve_intermediate_height base hp input reachable p (List.mem_of_find?_eq_some found) j
        have nz : p.head ≠ 0 := by simpa using List.find?_some found
        rw [vals,cap]; push_cast
        apply (pivot_fraction p nz bound b).mono
        nlinarith [mul_nonneg (by omega : (0:ℤ)≤C) bp]

end Cogentic.Elimination

#print axioms Cogentic.Elimination.solve_back_substitution_height
