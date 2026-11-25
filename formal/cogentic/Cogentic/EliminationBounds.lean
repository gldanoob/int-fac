import Cogentic.EliminationUnits

/-! Heights of the executable elimination stage's reduced rational answers. -/

open scoped BigOperators Matrix
open Matrix
namespace Cogentic
open Elimination

/-- LCM reduction only decreases a single common positive denominator, and
does not enlarge the corresponding integer coefficient magnitudes. -/
theorem reduced_integer_height {n : ℕ} (x : Fin n → ℚ) (d : ℤ) (hd : d ≠ 0)
    (numerator : Fin n → ℤ) (rep : ∀ i, x i = (numerator i : ℚ)/d) :
    integerScale x ∣ d.natAbs ∧ ∀ i, |(integerVector x).get i| ≤ |numerator i| := by
  have div : integerScale x ∣ d.natAbs := by
    apply Finset.lcm_dvd
    intro i _
    rw [rep, ← Rat.divInt_eq_div]
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr (Rat.den_dvd (numerator i) d)
  refine ⟨div,fun i => ?_⟩
  have scale := Nat.le_of_dvd (Int.natAbs_pos.mpr hd) div
  have dr : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have eq := integerVector_spec x i
  rw [rep] at eq
  have clear : ((integerVector x).get i : ℚ) * (d : ℚ) = numerator i * (integerScale x : ℚ) := by
    rw [eq]; field_simp
  have mulEq := congrArg abs clear
  simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (integerScale x) : (0 : ℚ) ≤ _)] at mulEq
  have denom : (integerScale x : ℚ) ≤ |(d : ℚ)| := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast scale
  have le : |((integerVector x).get i : ℚ)| * |(d : ℚ)| ≤ |(numerator i : ℚ)| * |(d : ℚ)| :=
    mulEq.trans_le (mul_le_mul_of_nonneg_left denom (abs_nonneg _))
  exact_mod_cast (le_of_mul_le_mul_right le (abs_pos.mpr dr))

/-- For unit-sized right-hand sides, the common pivot determinant on the
nonfree positions clears all values returned by Cramer's rule. -/
theorem rational_pivot_numerators {P : Type*} [Fintype P] [DecidableEq P]
    (B : Matrix P P ℤ) (hB : ∀ i j, |B i j| ≤ 1) (d : B.det ≠ 0)
    (b : P → ℤ) (hb : ∀ i, |b i| ≤ 1) (x : P → ℚ)
    (eq : (B.map (Int.castRingHom ℚ)) *ᵥ x = fun i => (b i : ℚ)) :
    ∀ i, x i = (B.cramer b i : ℚ)/B.det ∧ |B.cramer b i| ≤ (Fintype.card P).factorial := by
  let R := B.map (Int.castRingHom ℚ)
  have eq' : R *ᵥ (fun i => (B.cramer b i : ℚ)) = (B.det : ℚ) • (fun i => (b i : ℚ)) := by
    funext i
    have e := congrFun (B.mulVec_cramer b) i
    change ∑ j, B i j * B.cramer b j = B.det * b i at e
    change ∑ j, (B i j : ℚ) * (B.cramer b j : ℚ) = (B.det : ℚ) * (b i : ℚ)
    exact_mod_cast e
  have det : R.det ≠ 0 := by
    change ((Int.castRingHom ℚ).mapMatrix B).det ≠ 0
    rw [← RingHom.map_det]
    change (B.det : ℚ) ≠ 0
    exact_mod_cast d
  have same : (fun i => (B.cramer b i : ℚ)) = (B.det : ℚ) • x := by
    apply (Matrix.mulVec_injective_iff_isUnit.mpr (R.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr det)))
    rw [eq', Matrix.mulVec_smul, eq]
  intro i
  refine ⟨(eq_div_iff (by exact_mod_cast d)).mpr ?_,incidence_cramer_bound B hB b hb i⟩
  simpa [mul_comm] using (congrFun same i).symm


/-- A rational kernel parametrized by the free coordinates has an invertible
minor on precisely the complementary columns, with at most as many columns
as original rows. -/
theorem complement_row_pivot {τ : Type*} [Fintype τ] {n : ℕ}
    (V : Matrix τ (Fin n) ℤ) (P : Finset (Fin n))
    (unique : ∀ x : Fin n → ℚ, (V.map (Int.castRingHom ℚ)) *ᵥ x = 0 →
      (∀ j, j ∉ P → x j = 0) → x = 0) :
    ∃ keep : P → τ, (V.submatrix keep Subtype.val).det ≠ 0 ∧ P.card ≤ Fintype.card τ := by
  classical
  let A := V.submatrix id ((↑) : P → Fin n)
  let M := A.map (Int.castRingHom ℚ)
  have ker : ∀ x, M *ᵥ x = 0 → x = 0 := by
    intro x hx
    let y (j : Fin n) : ℚ := if h : j ∈ P then x ⟨j,h⟩ else 0
    have hA : (V.map (Int.castRingHom ℚ)) *ᵥ y = 0 := by
      funext i
      change ∑ j, (V i j : ℚ) * y j = 0
      rw [← Fintype.sum_subtype_add_sum_subtype (fun j => j ∈ P)]
      have sel (j : P) : y j.val = x j := dif_pos j.prop
      have ex (j : {j // j ∉ P}) : y j.val = 0 := dif_neg j.prop
      simp only [sel,ex,mul_zero,Finset.sum_const_zero,add_zero]
      have z := congrFun hx i
      change ∑ j : P, (V i j.val : ℚ) * x j = 0 at z
      convert! z using 2
      congr 1
      exact Subsingleton.elim _ _
    have z := unique y hA (fun j hj => by simp [y,hj])
    funext j
    simpa [y,j.prop] using congrFun z j.val
  have lin : LinearIndependent ℚ M.col := Matrix.mulVec_injective_iff.mp
    (LinearMap.ker_eq_bot.mp (Matrix.ker_mulVecLin_eq_bot_iff.mpr ker))
  have size := lin.fintype_card_le_finrank
  have rk : M.rank = Fintype.card P := by
    rw [← Matrix.rank_transpose]
    exact LinearIndependent.rank_matrix (M := M.transpose) lin
  have span : Submodule.span ℚ (Set.range M.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← M.rank_eq_finrank_span_row, rk, Module.finrank_pi]
  obtain ⟨keep,nz⟩ := incidence_pivot_of_column_span (F := ℚ) A.transpose span
  refine ⟨keep,?_,by simpa [Module.finrank_pi] using size⟩
  have eq : A.transpose.submatrix id keep = (V.submatrix keep Subtype.val).transpose := rfl
  rwa [eq, Matrix.det_transpose] at nz


/-- Bounds for any solution whose prescribed free coordinates are zero or
signed units and whose restricted right-hand side has entries of modulus at most one. -/
theorem reduced_pivot_height {τ : Type*} [Fintype τ] {n : ℕ} (V : Matrix τ (Fin n) ℤ)
    (hV : ∀ i j, |V i j| ≤ 1) (P : Finset (Fin n)) (keep : P → τ)
    (nz : (V.submatrix keep Subtype.val).det ≠ 0) (x : Fin n → ℚ) (b : P → ℤ)
    (hb : ∀ i, |b i| ≤ 1) (eq : ∀ i, ∑ j : P, (V (keep i) j.val : ℚ)* x j.val = (b i : ℚ))
    (prescribed : ∀ j, j ∉ P → ∃ t : ℤ, x j = (t : ℚ) ∧ |t| ≤ 1) :
    integerScale x ≤ P.card.factorial ∧ ∀ i, |(integerVector x).get i| ≤ P.card.factorial := by
  classical
  let B : Matrix P P ℤ := V.submatrix keep Subtype.val
  have small (i j) : |B i j| ≤ 1 := hV _ _
  have det : |B.det| ≤ P.card.factorial := by simpa using incidence_det_bound B small
  have inner := rational_pivot_numerators B small nz b hb (fun j : P => x j.val) (funext eq)
  have rep (i) : ∃ t : ℤ, x i = (t : ℚ)/B.det ∧ |t| ≤ P.card.factorial := by
    by_cases hi : i ∈ P
    · exact ⟨_,(inner ⟨i,hi⟩).1,by simpa using (inner ⟨i,hi⟩).2⟩
    · obtain ⟨t,ht,small⟩ := prescribed i hi
      refine ⟨t*B.det,?_,?_⟩
      · rw [Int.cast_mul, mul_div_cancel_right₀ _ (by exact_mod_cast nz), ht]
      · rw [abs_mul]
        exact (mul_le_of_le_one_left (abs_nonneg _) small).trans det
  choose y hy bound using rep
  obtain ⟨div,coeff⟩ := reduced_integer_height x B.det nz y hy
  refine ⟨(Nat.le_of_dvd (Int.natAbs_pos.mpr nz) div).trans ?_,fun i => (coeff i).trans (bound i)⟩
  rwa [Int.abs_eq_natAbs, Int.ofNat_le] at det

private theorem restriction_eq {n : ℕ} (P : Finset (Fin n)) (h x u : Fin n → ℚ)
    (hu : ∀ j ∈ P, u j = 0) (free : ∀ j, j ∉ P → x j = u j) :
    ∑ i : P, h i.val * x i.val = (∑ i, h i * x i) - ∑ i, h i * u i := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun j => j ∈ P) (fun j => h j*x j),
    ← Fintype.sum_subtype_add_sum_subtype (fun j => j ∈ P) (fun j => h j*u j)]
  have a (j : P) := hu j.val j.prop
  have b (j : {j // j ∉ P}) := free j.val j.prop
  simp only [a,b,mul_zero,Finset.sum_const_zero,zero_add,add_sub_cancel_right]
  congr 1
  ext; simp


private theorem family_height {τ : Type*} [Fintype τ] {n : ℕ} (V : Matrix τ (Fin n) ℤ)
    (hV : ∀ i j, |V i j| ≤ 1) (b : τ → ℤ) (hb : ∀ i, |b i| ≤ 1) (f : Family n)
    (point : ∀ i, ∑ j, (V i j : ℚ) * f.point j = (b i : ℚ))
    (point_free : ∀ k, f.point (f.position k) = 0)
    (null : ∀ k i, ∑ j, (V i j : ℚ) * f.direction k j = 0)
    (diagonal : ∀ k l, f.direction k (f.position l) = if l = k then 1 else 0)
    (span : ∀ x : Fin n → ℚ, (∀ i, ∑ j, (V i j : ℚ)*x j = 0) →
      ∀ j, x j = ∑ k, x (f.position k) * f.direction k j) :
    let T := (Fintype.card τ).factorial
    (integerScale f.point ≤ T ∧ ∀ j, |(integerVector f.point).get j| ≤ T) ∧
    ∀ k, integerScale (f.direction k) ≤ T ∧ ∀ j, |(integerVector (f.direction k)).get j| ≤ T := by
  classical
  let P := Finset.univ.filter (fun j => j ∉ Set.range f.position)
  have excluded (j) : j ∉ P ↔ j ∈ Set.range f.position := by simp [P]
  have covered (k) : f.position k ∉ P := (excluded _).mpr ⟨k,rfl⟩
  obtain ⟨keep,nz,rank⟩ := complement_row_pivot V P (by
    intro x hx zero
    funext j
    rw [span x (fun i => congrFun hx i) j]
    simp only [fun k => zero (f.position k) (covered k), zero_mul,Finset.sum_const_zero]
    rfl)
  have bound := Nat.factorial_le rank
  have applyP (x : Fin n → ℚ) (rhs : P → ℤ) (h : ∀ i, |rhs i| ≤ 1)
      (eq : ∀ i, ∑ j : P, (V (keep i) j.val : ℚ)*x j.val = (rhs i : ℚ))
      (free : ∀ j, j ∉ P → ∃ t : ℤ, x j = (t : ℚ) ∧ |t| ≤ 1) :
      integerScale x ≤ (Fintype.card τ).factorial ∧
        ∀ i, |(integerVector x).get i| ≤ (Fintype.card τ).factorial := by
    have ⟨hs,hv⟩ := reduced_pivot_height V hV P keep nz x rhs h eq free
    exact ⟨hs.trans bound, fun i => (hv i).trans (by exact_mod_cast bound)⟩
  have freeZero (j) (hj : j ∉ P) : f.point j = 0 := by
    obtain ⟨k,rfl⟩ := (excluded _).mp hj
    exact point_free k
  constructor
  · apply applyP f.point (b ∘ keep) (fun i => hb _)
    · intro i
      have eq := restriction_eq P (fun j => (V (keep i) j : ℚ)) f.point 0 (by simp) freeZero
      simpa [point] using eq
    · exact fun j hj => ⟨0,by simpa using freeZero j hj,by norm_num⟩
  · intro k
    have pos_inj : Function.Injective f.position := by
      intro a b eq
      by_contra ne
      have h := congrArg (f.direction a) eq
      rw [diagonal,diagonal,if_pos rfl,if_neg (Ne.symm ne)] at h
      norm_num at h
    let u (j : Fin n) : ℚ := if j = f.position k then 1 else 0
    have free (j) (hj : j ∉ P) : f.direction k j = u j := by
      obtain ⟨l,rfl⟩ := (excluded _).mp hj
      simp only [diagonal,u,pos_inj.eq_iff]
    have no (j) (hj : j ∈ P) : u j = 0 := by
      have ne : j ≠ f.position k := fun eq => covered k (eq ▸ hj)
      simp [u,ne]
    apply applyP (f.direction k) (fun i => -V (keep i) (f.position k)) (fun i => by simp [hV])
    · intro i
      have eq := restriction_eq P (fun j => (V (keep i) j : ℚ)) (f.direction k) u no free
      simpa [null,u,mul_ite] using eq
    · intro j hj
      rw [free j hj]
      by_cases eq : j = f.position k
      · exact ⟨1,by simp [u,eq],by norm_num⟩
      · exact ⟨0,by simp [u,eq],by norm_num⟩


/-- The target multiplier, the separate denominator scales of the free
vectors, and all output integer coefficients are bounded by the factorial
of the original row count for every successful executable elimination. -/
theorem stageTwo_height {rel : Marking.Relations} {out : IntegerFamily rel.marks.length}
    (ok : stageTwo rel = some out) :
    let T := (rel.rows.length+1).factorial
    (out.scale ≤ T ∧ ∀ j, |out.particular.get j| ≤ T) ∧
    ∀ k, out.scales.get k ≤ T ∧ ∀ j, |(out.directions.get k).get j| ≤ T := by
  classical
  unfold stageTwo at ok
  cases h : solve rel.marks.length (relationRows rel) with
  | none => simp [h] at ok
  | some f =>
    rw [h] at ok
    cases ok
    have coeff (i j) : |rel.matrix i j| ≤ 1 := by
      refine Fin.cases ?_ (fun k => ?_) i
      · norm_num [Marking.Relations.matrix]
      · simp only [Marking.Relations.matrix, Fin.cases_succ]
        split <;> norm_num
    have rhs (i) : |-rel.rhs i| ≤ 1 := by
      refine Fin.cases ?_ (fun k => ?_) i
      · norm_num [Marking.Relations.rhs]
      · simp only [Marking.Relations.rhs, Fin.cases_succ]
        split <;> norm_num
    have correct := solve_correct _ (relationRows rel)
    rw [h] at correct
    have point_free := (correct.1 (fun _ => 0)).2
    obtain ⟨base,hom,diagonal,span⟩ := family_basis h
    have holds (x : Fin rel.marks.length → ℚ) : Holds (relationRows rel) x ↔
        ∀ i, ∑ j, (rel.matrix i j : ℚ)*x j = -(rel.rhs i : ℚ) := by
      simp [Holds,relationRows,List.mem_ofFn,Row.Holds,Row.eval,Fin.forall_fin_succ,Vector.get_eq_getElem]
    have ker (x : Fin rel.marks.length → ℚ) : Kernel (relationRows rel) x ↔
        ∀ i, ∑ j, (rel.matrix i j : ℚ)*x j = 0 := by
      simp [Kernel,relationRows,List.mem_ofFn,Row.eval,Fin.forall_fin_succ,Vector.get_eq_getElem]
    have bound := family_height rel.matrix coeff (fun i => -rel.rhs i) rhs f
      (by simpa only [Int.cast_neg] using (holds _).mp base) (fun i => congrFun point_free i)
      (fun k => (ker _).mp (hom k)) diagonal (fun x hx => span x ((ker _).mpr hx))
    simpa [Family.integers,Vector.get_eq_getElem] using bound

end Cogentic
