import Cogentic.PrincipalMass
import Cogentic.WindowProgression

namespace Cogentic.Window

/-- The principal character deletes precisely the primes dividing its modulus.
This also applies when the original band already omits selected primes. -/
theorem principal_twist_mass {q : ℕ} [NeZero q] (J : Finset ℕ) (prime : ∀ p ∈ J, p.Prime)
    (Y S : ℝ) :
    twist (squarefreeSupport J) (fun n => (gaussian Y S n : ℂ)) (1 : DirichletCharacter ℂ q) =
      (gaussianMass (J \ q.primeFactors) Y S : ℂ) := by
  classical
  have sub := fun p (hp : p ∈ J \ q.primeFactors) => prime p (Finset.mem_sdiff.mp hp).1
  have supp : squarefreeSupport (J \ q.primeFactors) = (squarefreeSupport J).filter (fun n => n.Coprime q) := by
    ext n
    rw [mem_squarefreeSupport _ sub,Finset.mem_filter,mem_squarefreeSupport _ prime]
    constructor
    · rintro ⟨sf,ss⟩
      refine ⟨⟨sf,fun p hp => (Finset.mem_sdiff.mp (ss hp)).1⟩,?_⟩
      apply Nat.coprime_of_dvd
      intro p pp pn pq
      exact (Finset.mem_sdiff.mp (ss (Nat.mem_primeFactors.mpr ⟨pp,pn,sf.ne_zero⟩))).2
        (Nat.mem_primeFactors.mpr ⟨pp,pq,NeZero.ne q⟩)
    · rintro ⟨⟨sf,ss⟩,cop⟩
      exact ⟨sf,fun p hp => Finset.mem_sdiff.mpr ⟨ss hp,Finset.disjoint_left.mp cop.disjoint_primeFactors hp⟩⟩
  simp only [twist,gaussianMass,supp,Complex.ofReal_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases cop : n.Coprime q
  · simp [cop,MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr cop)]
  · simp [cop,MulChar.map_nonunit (1 : DirichletCharacter ℂ q) (fun unit => cop ((ZMod.isUnit_iff_coprime n q).mp unit))]

/-- Absolute discrepancy of an actual reduced residue from an untwisted
Gaussian on the smaller band, including every prime dividing the modulus. -/
theorem clean_residue_saddle_input (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (B Y S : ℝ) (D : Finset ℕ),
      4 ≤ B → 0 < S → S ≤ Y → 1 ≤ Y → 404 ≤ B^(3/200:ℝ) →
      (1+Real.log (3*q*B)) ≤ B^(1/100:ℝ) → (D.card:ℝ) ≤ B^(1/100:ℝ) →
      Y/S ≤ B^(17/100:ℝ) → (q:ℝ) ≤ Y^(1/1000:ℝ) → Y/S ≤ Y^(1/2000:ℝ) →
      D ⊆ (Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime → ∀ r : (ZMod q)ˣ,
      let J := ((Finset.Ioc ⌊Real.sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime) \ D
      ‖(q:ℂ)*classMass (squarefreeSupport J) (fun n => (gaussian Y S n:ℂ)) r -
        ((q:ℂ)/q.totient)*(gaussianMass (J \ q.primeFactors) Y S:ℂ)‖ ≤ C*Y^(-3/1000:ℝ) := by
  obtain ⟨C,pos,estimate⟩ := clean_progression_error line
  refine ⟨C,pos,fun q _ B Y S D hB hS sy hy large logs size rb qy ry omitted r => ?_⟩
  have e := estimate q B Y S D hB hS sy hy large logs size rb qy ry omitted r
  dsimp only at e ⊢
  rwa [principal_twist_mass _ (fun _ p => (Finset.mem_filter.mp (Finset.mem_sdiff.mp p).1).2)] at e

end Cogentic.Window
