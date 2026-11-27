import Cogentic.RandomizedCappedTape
import Mathlib.Probability.Distributions.Uniform

namespace Cogentic.RandomizedFairEpochTape

open RandomizedCappedEpoch
open scoped BigOperators ENNReal

open Classical in
private theorem map_cons_apply {α : Type*} {r : ℕ} (p : PMF (Fin r → α))
    (a : α) (t : Fin (r + 1) → α) :
    (p.map (Fin.cons a)) t = if a = t 0 then p (Fin.tail t) else 0 := by
  by_cases ha : a = t 0
  · subst a
    rw [if_pos rfl, PMF.map_apply, tsum_eq_single (Fin.tail t)]
    · rw [if_pos (Fin.cons_self_tail t).symm]
    · intro v hv
      apply if_neg
      intro he
      exact hv (by simpa using (congrArg Fin.tail he).symm)
  · have hm (v : Fin r → α) : t ≠ Fin.cons a v := fun he ↦
      ha (by simpa using (congrFun he 0).symm)
    simp [PMF.map_apply, ha, hm]

/-- The tape has the product law, pointwise at every finite sequence of blocks. -/
theorem blockLaw_apply {α : Type*} (p : PMF α) (r : ℕ) (t : Fin r → α) :
    blockLaw p r t = ∏ i, p (t i) := by
  classical
  induction r with
  | zero =>
    have he : t = Fin.elim0 := Subsingleton.elim _ _
    subst t
    simp [blockLaw, PMF.pure_apply]
  | succ r ih =>
    rw [blockLaw, PMF.bind_apply, tsum_eq_single (t 0), Fin.prod_univ_succ]
    · rw [map_cons_apply, if_pos rfl, ih] <;> rfl
    · intro a ha
      rw [map_cons_apply, if_neg ha, mul_zero]

/-- Uniform blocks give a uniform tape on the whole finite product. -/
theorem blockLaw_uniform {α : Type*} [Fintype α] [Nonempty α] (r : ℕ) :
    blockLaw (PMF.uniformOfFintype α) r = PMF.uniformOfFintype (Fin r → α) := by
  apply PMF.ext
  intro t
  simp [blockLaw_apply, PMF.uniformOfFintype_apply, ENNReal.inv_pow]

/-- In particular, every specified tape of r blocks of b bits has probability
two to the power minus the total number of bits. -/
theorem fairBits_apply (r b : ℕ) (t : Fin r → Fin b → Bool) :
    blockLaw (PMF.uniformOfFintype (Fin b → Bool)) r t =
      ((2 : ℝ≥0∞)⁻¹) ^ (b * r) := by
  rw [blockLaw_uniform, PMF.uniformOfFintype_apply]
  simp [ENNReal.inv_pow, pow_mul]

/-- The number of blocks read through the first accepted block or exhaustion. -/
def blocksRead {α β : Type*} (attempt : α → Option β × ℕ) :
    (r : ℕ) → (Fin r → α) → ℕ
  | 0, _ => 0
  | r+1, tape =>
    match (attempt (tape 0)).1 with
    | some _ => 1
    | none => 1 + blocksRead attempt r (fun j ↦ tape j.succ)

/-- Charging b fair bits per visited attempt adds exactly the cost of the
prefix that the capped interpreter reads. -/
theorem runTape_read_charge {α β : Type*} (attempt : α → Option β × ℕ)
    (fallback : Unit → β × ℕ) (b r : ℕ) (tape : Fin r → α) :
    (runTape (fun a ↦ let out := attempt a; (out.1, out.2 + b)) fallback r tape).2 =
      (runTape attempt fallback r tape).2 + b * blocksRead attempt r tape := by
  induction r with
  | zero => simp [runTape, blocksRead]
  | succ r ih =>
    cases h : (attempt (tape 0)).1 <;>
      simp only [runTape, blocksRead, h, ih, Nat.mul_add, Nat.mul_one] <;> omega

#print axioms blockLaw_uniform
#print axioms fairBits_apply
#print axioms runTape_read_charge

end Cogentic.RandomizedFairEpochTape
