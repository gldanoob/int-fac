import Mathlib.LinearAlgebra.Eigenspace.Minpoly

open scoped Polynomial

namespace Cogentic.Randomized

variable {K V T : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup T] [Module K T]

/-- Polynomial evaluation on a vector killed by the endomorphism. -/
theorem tagged_aeval_of_mem_ker (S : Module.End K V) (Q : K[X]) {z : V}
    (hz : z ∈ LinearMap.ker S) : Polynomial.aeval S Q z = Q.eval 0 • z :=
  Module.End.aeval_apply_of_mem_apply_eq_smul (by simpa using hz)

/-- If the range component is killed by the polynomial, its evaluation
keeps exactly the kernel component scaled by the constant term. -/
theorem tagged_kernel_project (S : Module.End K V) (Q : K[X]) {x z w : V}
    (hx : x = z + w) (hz : z ∈ LinearMap.ker S)
    (hw : Polynomial.aeval S Q w = 0) :
    Polynomial.aeval S Q x = Q.eval 0 • z := by
  rw [hx, map_add, tagged_aeval_of_mem_ker S Q hz, hw, add_zero]

/-- A nonzero constant term preserves exactly the nonzero linear tags
of the kernel component. -/
theorem tagged_kernel_project_tag_ne_zero_iff (S : Module.End K V) (Q : K[X])
    (H : V →ₗ[K] T) {x z w : V}
    (hx : x = z + w) (hz : z ∈ LinearMap.ker S)
    (hw : Polynomial.aeval S Q w = 0) (hQ : Q.eval 0 ≠ 0) :
    H (Polynomial.aeval S Q x) ≠ 0 ↔ H z ≠ 0 := by
  rw [tagged_kernel_project S Q hx hz hw, map_smul]
  simp [hQ]

private theorem tagged_commute_aeval (S : Module.End K V) (Q : K[X]) :
    Polynomial.aeval S Q * S = S * Polynomial.aeval S Q := by
  calc
    Polynomial.aeval S Q * S = Polynomial.aeval S (Q * Polynomial.X) := by simp
    _ = Polynomial.aeval S (Polynomial.X * Q) := by rw [mul_comm]
    _ = S * Polynomial.aeval S Q := by simp

/-- If the kernel and range are disjoint, annihilation by `X * Q` on the
whole vector implies annihilation by `Q` on its range component. -/
theorem tagged_range_component_annihilated (S : Module.End K V) (Q : K[X]) {x z w : V}
    (hdisj : Disjoint (LinearMap.ker S) (LinearMap.range S))
    (hx : x = z + w) (hz : z ∈ LinearMap.ker S) (hw : w ∈ LinearMap.range S)
    (hP : Polynomial.aeval S (Polynomial.X * Q) x = 0) :
    Polynomial.aeval S Q w = 0 := by
  have hzero : S (Polynomial.aeval S Q w) = 0 := by
    rw [map_mul, Polynomial.aeval_X, Module.End.mul_apply, hx, map_add,
      map_add, tagged_aeval_of_mem_ker S Q hz, map_smul,
      LinearMap.mem_ker.mp hz, smul_zero, zero_add] at hP
    exact hP
  have hrange : Polynomial.aeval S Q w ∈ LinearMap.range S := by
    obtain ⟨v, rfl⟩ := hw
    refine ⟨Polynomial.aeval S Q v, ?_⟩
    exact (congrArg (fun f : Module.End K V => f v) (tagged_commute_aeval S Q)).symm
  exact Submodule.disjoint_def.mp hdisj _ (LinearMap.mem_ker.mpr hzero) hrange

/-- An annihilator of the form `X * Q` preserves nonzero tags on the
kernel component when `Q` has a nonzero constant term. -/
theorem tagged_kernel_project_tag_of_mul_annihilates (S : Module.End K V) (Q : K[X])
    (H : V →ₗ[K] T) {x z w : V}
    (hdisj : Disjoint (LinearMap.ker S) (LinearMap.range S))
    (hx : x = z + w) (hz : z ∈ LinearMap.ker S) (hw : w ∈ LinearMap.range S)
    (hP : Polynomial.aeval S (Polynomial.X * Q) x = 0) (hQ : Q.eval 0 ≠ 0) :
    H (Polynomial.aeval S Q x) ≠ 0 ↔ H z ≠ 0 :=
  tagged_kernel_project_tag_ne_zero_iff S Q H hx hz
    (tagged_range_component_annihilated S Q hdisj hx hz hw hP) hQ

/-- For complementary kernel and range, any vector annihilated by `X * Q`
admits the tagged projection across its kernel–range decomposition. -/
theorem tagged_kernel_decomposition (S : Module.End K V) (Q : K[X]) (x : V)
    (hcomp : IsCompl (LinearMap.ker S) (LinearMap.range S))
    (hP : Polynomial.aeval S (Polynomial.X * Q) x = 0) :
    ∃ z ∈ LinearMap.ker S, ∃ w ∈ LinearMap.range S, x = z + w ∧
      Polynomial.aeval S Q x = Q.eval 0 • z := by
  have hmem : x ∈ LinearMap.ker S ⊔ LinearMap.range S := by
    rw [hcomp.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨z, hz, w, hw, hx⟩ := Submodule.mem_sup.mp hmem
  have hQ := tagged_range_component_annihilated S Q hcomp.disjoint hx.symm hz hw hP
  exact ⟨z, hz, w, hw, hx.symm, tagged_kernel_project S Q hx.symm hz hQ⟩

end Cogentic.Randomized
