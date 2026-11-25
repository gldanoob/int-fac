import Cogentic.GramCandidate
import Mathlib.RingTheory.Coprime.Lemmas

/-! The exact two norm directions in the finite and archimedean columns. -/

open Polynomial
open scoped BigOperators Matrix
namespace Cogentic
open Marking

private theorem residue_eval (f : ℤ[X]) (a p : ℕ) :
    f.eval₂ (Int.castRingHom (ZMod p)) ((a%p:ℕ):ZMod p) = ((f.eval (a:ℤ):ℤ):ZMod p) := by
  rw [ZMod.natCast_mod]
  simpa only [Int.coe_castRingHom,Int.cast_natCast] using
    Polynomial.eval₂_at_apply (p:=f) (Int.castRingHom (ZMod p)) (a:ℤ)

/-- The logarithm of a retained squarefree polynomial value equals the sum
of the logarithmic prime rows actually hit in its own field. -/
theorem retained_prime_log {s : Input} {rel : Relations} (marked : stageOne s = some rel)
    (side : Bool) (j : Fin rel.marks.length) :
    let f := polynomial (s.coeffs side)
    let a := rel.marks.get j
    ∑ i : Fin rel.rows.length, (if (rel.rows.get i).second=side then Real.log (rel.rows.get i).q else 0) *
      (rel.matrix i.succ j:ℝ) = Real.log ((f.eval (a:ℤ)).natAbs:ℕ) := by
  classical
  intro f a
  let x := (f.eval (a:ℤ)).natAbs
  let q := fun i : Fin rel.rows.length => (rel.rows.get i).q
  let hits := Finset.univ.filter (fun i : Fin rel.rows.length =>
    (rel.rows.get i).second=side ∧ a%q i=(rel.rows.get i).r)
  have rows := (rows_and_guards marked).2.2.2.1
  have nd : rel.rows.Nodup := rows ▸ (List.nodup_dedup _).filter _
  have smooth := (stageOne_mark_primes marked side).1 j
  have range : hits.image q = x.primeFactors := by
    ext p
    constructor
    · rintro h
      obtain ⟨i,hit,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨sd,rr⟩ := (Finset.mem_filter.mp hit).2
      have mem : rel.rows.get i ∈ s.clean := by rw [← rows]; exact List.get_mem rel.rows i
      have info := mem_rows.mp (mem_clean.mp mem).1
      have prime := (mem_base.mp info.1).2.1
      have root := info.2.2
      change (polynomial (s.coeffs (rel.rows.get i).second)).eval₂ (Int.castRingHom (ZMod (q i)))
        (((rel.rows.get i).r:ℕ):ZMod (q i))=0 at root
      rw [sd,←rr,residue_eval] at root
      have div := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp root
      exact Nat.mem_primeFactors.mpr ⟨prime,by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr div,smooth.1⟩
    · intro h
      obtain ⟨pp,pd,_⟩ := Nat.mem_primeFactors.mp h
      have div : (p:ℤ) ∣ f.eval (a:ℤ) := Int.natAbs_dvd_natAbs.mp (by simpa only [Int.natAbs_natCast] using pd)
      have mem : Row.mk side p (a%p) ∈ rel.rows := rows ▸ (stageOne_mark_primes marked side).2 p pp j div
      obtain ⟨i,hrow⟩ := List.mem_iff_get.mp mem
      refine Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩,?_⟩ <;> simp only [q,hrow]
  have inj : Set.InjOn q ↑hits := by
    intro i hi k hk equal
    obtain ⟨si,ri⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨sk,rk⟩ := (Finset.mem_filter.mp hk).2
    apply nd.injective_get
    have ri' := ri.symm.trans ((congrArg (fun p => a%p) equal).trans rk)
    have ext (r s : Row) (hs : r.second=s.second) (hq : r.q=s.q) (hr : r.r=s.r) : r=s := by
      cases r; cases s; simp_all
    exact ext _ _ (si.trans sk.symm) equal ri'
  have primeProd : ∏ p ∈ x.primeFactors, (p:ℝ) = (x:ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast (Nat.prod_primeFactors_of_squarefree (n:=x) smooth.2.1)
  calc
    _ = ∑ i ∈ hits, Real.log (q i) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases sd : (rel.rows.get i).second=side <;> by_cases hit : a%q i=(rel.rows.get i).r <;>
        simp [Relations.matrix,q,a] at hit ⊢ <;> simp_all
    _ = ∑ p ∈ x.primeFactors, Real.log (p:ℝ) := by rw [←range,Finset.sum_image inj]
    _ = Real.log (x:ℝ) := by
      rw [←Real.log_prod (fun p hp => Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero),primeProd]

/-- A degree-d polynomial with d distinct known roots gives the exact
real-place log sum, including its leading coefficient and scale. -/
theorem polynomial_norm_logs {d : ℕ} (F : ℝ[X]) (A a : ℝ) (x : Fin d → ℝ) (apos : 0 < A)
    (degree : F.natDegree = d) (leading : F.leadingCoeff ≠ 0) (inj : Function.Injective x)
    (roots : ∀ i, F.eval (A*x i)=0) (nz : F.eval a ≠ 0) :
    Real.log |F.eval a| = Real.log |F.leadingCoeff|+(d:ℝ)*Real.log A+
      ∑ i, Real.log |a/A-x i| := by
  classical
  let r := fun i => A*x i
  have ri : Function.Injective r := fun i j h => inj (mul_left_cancel₀ apos.ne' h)
  have divide : (∏ i, (X-C (r i))) ∣ F := Fintype.prod_dvd_of_coprime
    (Polynomial.pairwise_coprime_X_sub_C ri) (fun i => (Polynomial.dvd_iff_isRoot).mpr (roots i))
  have form := Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    (Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)) divide
    (by simp [degree])
  have value := congrArg (fun p : ℝ[X] => p.eval a) form
  simp only [eval_mul,eval_C,eval_prod,eval_sub,eval_X] at value
  have factor (i) : a-r i = A*(a/A-x i) := by dsimp [r]; field_simp
  simp_rw [factor] at value
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at value
  have prodNZ : (∏ i, (a/A-x i)) ≠ 0 := by intro h; rw [h,mul_zero,mul_zero] at value; exact nz value
  have valLog : Real.log |F.eval a| = Real.log |F.leadingCoeff|+(d:ℝ)*Real.log A+
      Real.log (∏ i, (a/A-x i)) := by
    rw [value,abs_mul,Real.log_mul (abs_ne_zero.mpr leading) (abs_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ apos.ne') prodNZ)),
      Real.log_abs,Real.log_abs,Real.log_mul (pow_ne_zero _ apos.ne') prodNZ,Real.log_pow]
    ring
  rw [valLog,Real.log_prod (Finset.prod_ne_zero_iff.mp prodNZ)]
  simp [Real.log_abs]

/-- Both finite norm rows of the actual retained mark matrix have exactly
their prescribed expression in the ordered true bracket-root logarithms.
The identity holds separately on each side and mark. -/
theorem retained_norm_coordinates {N ell a b c d : ℕ} (hn : 2 ≤ N)
    (big : 10004 ≤ Fixed.d (N.log2+1)) (target : ell ∈ dyadicTargets (Fixed.beta (N.log2+1))) :
    let pair := Construction.construct N ell a b c d
    let s := TryPair.fixedInput N ell pair
    ∀ {rel}, stageOne s = some rel → ∀ (side : Bool) (x : Fin s.degree → ℝ),
    (∀ i, x i ∈ Set.Icc ((RootLogs.bracket s side i).left:ℝ) ((RootLogs.bracket s side i).right:ℝ) ∧
      RootLogs.normalized s.A (s.coeffs side) (x i)=0) →
    let f := polynomial (s.coeffs side)
    ∀ j : Fin rel.marks.length,
      ∑ i : Fin rel.rows.length,
        (if (rel.rows.get i).second=side then Real.log (rel.rows.get i).q else 0) * (rel.matrix i.succ j:ℝ) =
      (Real.log |(f.leadingCoeff:ℝ)|+(s.degree:ℝ)*Real.log s.A) +
        ∑ i, Real.log |(rel.marks.get j:ℝ)/s.A-x i| := by
  intro pair s rel marked side x atRoots f j
  let F := f.map (Int.castRingHom ℝ)
  have dz : 0 < s.degree := by change 0 < Fixed.d (N.log2+1); omega
  have deg : F.natDegree = s.degree := by
    have de := Construction.constructed_rational_fields (by omega) target a b c d
    rw [show F.natDegree=f.natDegree from natDegree_map_eq_of_injective (Int.cast_injective (α:=ℝ)) f]
    cases side
    · exact de.1.1
    · exact de.2.1
  have lc : F.leadingCoeff ≠ 0 := by
    intro zero
    have eq : F=0 := Polynomial.leadingCoeff_eq_zero.mp zero
    rw [eq,natDegree_zero] at deg
    omega
  have distinct : Function.Injective x := by
    have lt (i k : Fin s.degree) (lt : i<k) : x i<x k := by
      have bounds := Construction.brackets_ordered hn big ell pair side i k lt
      have le : ((RootLogs.bracket s side i).right:ℝ) < ((RootLogs.bracket s side k).left:ℝ) := by exact_mod_cast bounds
      exact ((atRoots i).1.2.trans_lt le).trans_le (atRoots k).1.1
    exact StrictMono.injective lt
  have root (i) : F.eval (s.A*x i)=0 := by
    change (f.map (Int.castRingHom ℝ)).eval _=0
    rw [eval_map]
    have eq := (atRoots i).2
    simpa only [RootLogs.normalized,horner_correct] using eq
  let a' := rel.marks.get j
  have val : F.eval (a':ℝ)=((f.eval (a':ℤ):ℤ):ℝ) := by
    simpa only [F,Int.coe_castRingHom,Int.cast_natCast] using f.eval_map_apply (Int.castRingHom ℝ) (a':ℤ)
  have nz : F.eval (a':ℝ) ≠ 0 := by
    rw [val]
    apply Int.cast_ne_zero.mpr
    intro zero
    exact (stageOne_mark_primes marked side).1 j |>.1 (by change (f.eval (a':ℤ)).natAbs=0; rw [zero]; rfl)
  have ap : 0 < (s.A:ℝ) := by
    have g := (rows_and_guards marked).1.2.2.2.2.1
    exact_mod_cast (by omega : 0<s.A)
  have norm := polynomial_norm_logs F s.A a' x ap deg lc distinct root nz
  rw [retained_prime_log marked side j]
  rw [val] at norm
  have hlead : F.leadingCoeff=(f.leadingCoeff:ℝ) := Polynomial.leadingCoeff_map_of_injective (Int.cast_injective (α:=ℝ)) f
  rw [hlead] at norm
  simpa only [Nat.cast_natAbs, Int.cast_abs] using norm

end Cogentic

#print axioms Cogentic.retained_norm_coordinates
