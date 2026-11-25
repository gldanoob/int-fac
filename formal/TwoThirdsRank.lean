import Std
open Std Lean.Grind

namespace TwoThirdsRank
variable {R : Type u} [CommRing R] [LE R] [LT R] [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R]

def total (s : List α) (f : α → R) : R :=
  match s with
  | [] => 0
  | i :: t => f i + total t f

private theorem total_ge {s : List α} {f g : α → R} (h : ∀ i ∈ s, f i ≤ g i) :
    total s f ≤ total s g := by
  induction s with
  | nil => exact le_refl _
  | cons a s ih =>
    simp only [total]
    have h₁ := h a (List.mem_cons_self ..)
    have h₂ := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    grind

private theorem total_nonneg {s : List α} {f : α → R} (h : ∀ i ∈ s, 0 ≤ f i) :
    0 ≤ total s f := by
  induction s with
  | nil => exact le_refl _
  | cons a s ih =>
    have h₁ := h a (List.mem_cons_self ..)
    have h₂ := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    simp only [total]; grind

omit [LE R] [LT R] [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R] in
private theorem total_lin (s : List α) (f g : α → R) (a b : R) :
    total s (fun i => a * f i + b * g i) = a * total s f + b * total s g := by
  induction s with
  | nil => simp only [total]; grind
  | cons i s ih => simp only [total, ih]; grind

omit [LE R] [LT R] [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R] in
private theorem total_mul (s : List α) (f : α → R) (a : R) :
    total s (fun i => a * f i) = a * total s f := by
  induction s with
  | nil => simp only [total]; grind
  | cons i s ih => simp only [total, ih]; grind

omit [LE R] [LT R] [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R] in
private theorem total_sq (s : List α) (f g : α → R) (a b : R) :
    total s (fun i => (a*f i - b*g i)^2) =
      a^2 * total s (fun i => (f i)^2) + b^2 * total s (fun i => (g i)^2) -
      2*a*b * total s (fun i => f i*g i) := by
  induction s with
  | nil => simp only [total]; grind
  | cons i s ih => simp only [total, ih]; grind

/-- Finite Cauchy–Schwarz from a double sum of squares. -/
theorem cauchy (s : List α) (f g : α → R) :
    (total s (fun i => f i*g i))^2 ≤
    total s (fun i => (f i)^2) * total s (fun i => (g i)^2) := by
  let A := total s (fun i => (f i)^2)
  let B := total s (fun i => (g i)^2)
  let c := total s (fun i => f i*g i)
  have pos : 0 ≤ total s (fun i => total s (fun j => (g i * f j - f i * g j)^2)) :=
    total_nonneg fun _ _ => total_nonneg fun _ _ => OrderedRing.sq_nonneg
  have id : total s (fun i => total s (fun j => (g i * f j - f i * g j)^2)) =
      2*(A*B - c^2) := by
    simp only [total_sq]
    have aux (t : List α) :
      total t (fun i => (g i)^2 * A + (f i)^2 * B - 2 * g i * f i * c) =
       total t (fun i => (g i)^2) * A + total t (fun i => (f i)^2) * B -
       2 * total t (fun i => f i*g i) * c := by
      induction t with
      | nil => simp only [total]; grind
      | cons i t ih => simp only [total, ih]; grind
    rw [aux]; dsimp [A,B,c]; grind
  rw [id] at pos
  change c^2 ≤ A*B
  grind

def energy (s : List α) (f : α → R) := total s (fun i => f i ^ 2)
def dot (s : List α) (f g : α → R) := total s (fun i => f i * g i)
def countR (s : List α) : R := total s (fun _ => 1)

omit [LE R] [LT R] [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R] in
private theorem total_const (s : List α) (c : R) : total s (fun _ => c) = c * countR s := by
  unfold countR; induction s with
  | nil => simp [total]; grind
  | cons i s ih => simp only [total, ih]; grind

private theorem energy_nonneg (s : List α) (v : α → R) : 0 ≤ energy s v :=
  total_nonneg fun _ _ => OrderedRing.sq_nonneg

private theorem square_sub (a b : R) : (a-b)^2 ≤ 2*(a^2+b^2) := by
  have h := OrderedRing.sq_nonneg (a := a+b)
  grind

/-- A diagonal model with an entrywise-bounded error controls the quadratic energy
of its actual outputs. The bound needs neither symmetry nor division. -/
theorem grid_energy (s : List α) (v diag image : α → R) (err : α → α → R)
    (D B : R) (hdiag : ∀ i ∈ s, D ≤ (diag i)^2)
    (herr : ∀ i ∈ s, ∀ j ∈ s, (err i j)^2 ≤ B)
    (himage : ∀ i ∈ s, image i = diag i * v i + dot s (err i) v) :
    (D - 2 * B * (countR s)^2) * energy s v ≤ 2 * energy s image := by
  have rowBound (i : α) (hi : i ∈ s) : energy s (err i) ≤ B * countR s := by
    calc
      energy s (err i) ≤ total s (fun _ => B) := total_ge (herr i hi)
      _ = _ := total_const ..
  have hErr : energy s (fun i => dot s (err i) v) ≤ (B * countR s * energy s v) * countR s := by
    apply Std.le_trans (b := total s (fun _ => B * countR s * energy s v))
    · apply total_ge
      intro i hi
      exact Std.le_trans (cauchy s (err i) v)
        (OrderedRing.mul_le_mul_of_nonneg_right (rowBound i hi) (energy_nonneg s v))
    · exact Std.le_of_eq (total_const ..)
  have each (i : α) (hi : i ∈ s) :
      D*(v i)^2 ≤ 2*(image i)^2 + 2*(dot s (err i) v)^2 := by
    have low := OrderedRing.mul_le_mul_of_nonneg_right (hdiag i hi) (OrderedRing.sq_nonneg (a := v i))
    have up := square_sub (image i) (dot s (err i) v)
    calc
      D*(v i)^2 ≤ (diag i)^2 * (v i)^2 := low
      _ = (image i - dot s (err i) v)^2 := by rw [himage i hi]; grind
      _ ≤ _ := by grind
  have sum := total_ge each
  rw [total_mul, total_lin] at sum
  change D * energy s v ≤ 2 * energy s image + 2 * energy s (fun i => dot s (err i) v) at sum
  grind

/-- Averaging over any normalized, nonnegative discrete weights loses no squared
energy below the square of the mean. -/
theorem weighted_jensen (s : List α) (w f : α → R)
    (hw : ∀ i ∈ s, 0 ≤ w i) (unitMass : total s w = 1) :
    (dot s w f)^2 ≤ total s (fun i => w i * (f i)^2) := by
  let m := dot s w f
  have pos := total_nonneg (s := s) (f := fun i => w i * (f i - m)^2)
    (fun i hi => OrderedRing.mul_nonneg (hw i hi) OrderedRing.sq_nonneg)
  have id (t : List α) : total t (fun i => w i * (f i - m)^2) =
      total t (fun i => w i * (f i)^2) - 2 * m * dot t w f + m^2 * total t w := by
    induction t with
    | nil => simp [total, dot]; grind
    | cons i t ih => simp only [total, dot] at ih ⊢; grind
  rw [id, unitMass] at pos
  change m^2 ≤ _
  change 0 ≤ _ - 2 * m * m + m^2 * 1 at pos
  grind

/-- An affine root grid. A baseline observation controls the intercept, while
differences against the same baseline see a dominant diagonal in all root directions. -/
theorem affine_grid (s : List α) (v baseline diag scores : α → R)
    (err : α → α → R) (v₀ s₀ D B : R)
    (hbase : s₀ = v₀ + dot s baseline v)
    (hdiag : ∀ i ∈ s, D ≤ (diag i)^2)
    (herr : ∀ i ∈ s, ∀ j ∈ s, (err i j)^2 ≤ B)
    (himage : ∀ i ∈ s, scores i - s₀ = diag i * v i + dot s (err i) v)
    (hn : (1 : R) ≤ countR s)
    (margin : 8 * countR s * (energy s baseline + 1) ≤ D - 2 * B * (countR s)^2) :
    v₀^2 + energy s v ≤ 3*(s₀^2 + energy s scores) := by
  let n : R := countR s
  let a := energy s v
  let b := energy s baseline
  let z := energy s scores
  have g := grid_energy s v diag (fun i => scores i - s₀) err D B hdiag herr himage
  have up (i : α) (_ : i ∈ s) : (scores i - s₀)^2 ≤ 2*(scores i)^2 + 2*s₀^2 := by
    have := square_sub (scores i) s₀
    grind
  have su := total_ge up
  rw [total_lin, total_const] at su
  change energy s (fun i => scores i - s₀) ≤ 2*z + 2*(s₀^2*n) at su
  have aNonneg : 0 ≤ a := energy_nonneg _ _
  have zNonneg : 0 ≤ z := energy_nonneg _ _
  have npos : 0 < n := Std.lt_of_lt_of_le OrderedRing.zero_lt_one hn
  have nz := OrderedRing.mul_le_mul_of_nonneg_right hn zNonneg
  have ma := OrderedRing.mul_le_mul_of_nonneg_right margin aNonneg
  change 8*n*(b+1)*a ≤ (D - 2*B*n^2)*a at ma
  change (D - 2*B*n^2)*a ≤ 2*energy s (fun i => scores i - s₀) at g
  have bound : n*(2*(b+1)*a) ≤ n*(s₀^2+z) := by grind
  have small : 2*(b+1)*a ≤ s₀^2+z := by
    apply Classical.byContradiction
    intro bad
    have opp : s₀^2+z < 2*(b+1)*a := by grind
    have gt := OrderedRing.mul_lt_mul_of_pos_left opp npos
    exact (Std.not_lt_of_ge bound) gt
  have cs : (dot s baseline v)^2 ≤ b*a := cauchy s baseline v
  have vi : v₀^2 ≤ 2*(s₀^2+(dot s baseline v)^2) := by
    calc
      v₀^2 = (s₀ - dot s baseline v)^2 := by rw [hbase]; grind
      _ ≤ _ := square_sub ..
  change v₀^2+a ≤ 3*(s₀^2+z)
  grind

/-- The energy of actual marks in normalized intervals controls the intercept and
all archimedean coefficients. The hypotheses concern means and individual matrix
entries, so no spectral or spanning conclusion is assumed. -/
theorem root_grid_gram (s : List α) (v baseline diag : α → R) (err : α → α → R)
    (marks : Option α → List β) (weight value : Option α → β → R) (v₀ D B : R)
    (positive : ∀ k j, j ∈ marks k → 0 ≤ weight k j)
    (mass : ∀ k, total (marks k) (weight k) = 1)
    (hbase : dot (marks none) (weight none) (value none) = v₀ + dot s baseline v)
    (hdiag : ∀ i ∈ s, D ≤ (diag i)^2)
    (herr : ∀ i ∈ s, ∀ j ∈ s, (err i j)^2 ≤ B)
    (himage : ∀ i ∈ s, dot (marks (some i)) (weight (some i)) (value (some i)) -
        dot (marks none) (weight none) (value none) = diag i * v i + dot s (err i) v)
    (hn : (1 : R) ≤ countR s)
    (margin : 8 * countR s * (energy s baseline + 1) ≤ D - 2 * B * (countR s)^2) :
    v₀^2 + energy s v ≤ 3 * (total (marks none) (fun j => weight none j * (value none j)^2) +
        total s (fun i => total (marks (some i))
          (fun j => weight (some i) j * (value (some i) j)^2))) := by
  let avg k := dot (marks k) (weight k) (value k)
  let obs k := total (marks k) (fun j => weight k j * (value k j)^2)
  have jensen (k : Option α) : (avg k)^2 ≤ obs k :=
    weighted_jensen _ _ _ (positive k) (mass k)
  have j₀ := jensen none
  have j₁ : energy s (fun i => avg (some i)) ≤ total s (fun i => obs (some i)) :=
    total_ge fun i _ => jensen (some i)
  have g := affine_grid s v baseline diag (fun i => avg (some i)) err v₀ (avg none)
    D B hbase hdiag herr himage hn margin
  change v₀^2 + energy s v ≤ 3*(obs none + total s (fun i => obs (some i)))
  grind

end TwoThirdsRank
