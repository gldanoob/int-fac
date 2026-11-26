import Main
import Cogentic

/-! Applications of the frozen Dirichlet GRH proof. This target also imports
    the original proof of the critical-line theorem for every character. -/
namespace Cogentic

theorem uniform_character_psi :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (x : ℝ), 2 ≤ x → ‖Formalism.MainNotions.GlobalTheoryTheory.psi0 χ x‖ ≤
        C*Real.sqrt x*(1+Real.log (3*q*x))^2 :=
  Window.uniform_psi_from_critical_line LFunction_eq_zero_re

theorem polynomial_generators :
    ∃ k : ℕ, ∀ (q bits : ℕ) [NeZero q], q < 2^bits →
      generatesUnits q (List.range' 1 (polyCutoff k bits)) :=
  polynomial_generators_from_critical_line LFunction_eq_zero_re

open Fixed TwoThirdsSearch TwoThirdsFactor Filter

/-- Complete prime factors with a trial-division fallback. -/
theorem concrete_factorization :
    ∃ (k : ℕ) (gen : ∀ n, 2 ≤ n → generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1)))),
      ∀ n (hn : 2 ≤ n),
        let factors := (Concrete.run k gen n hn).factors
        factors.prod = n ∧ (∀ p ∈ factors, p.Prime) ∧
          ∀ p, p.Prime → ∀ j, p^j ∣ n ↔ j ≤ factors.count p :=
  Concrete.total_factorization LFunction_eq_zero_re

/-- Apply the frozen critical-line theorem to the complete factoring bound. -/
theorem binary_factorization_two_thirds : Companion.LocalFactorizationBound :=
  Companion.factor_words_two_thirds LFunction_eq_zero_re

/-- The remaining hypothesis about candidate success quantifies over all large
    surviving inputs. The final inequality refers to supplied per-node charges. -/
theorem factor_of_eventual_coverage
    (covered : ∃ n₀ : ℕ, ∀ n ≥ n₀, (parameters Concrete.candidate n).Covers n) :
    ∃ (threshold k : ℕ) (schedules : (n : ℕ) → 2 ≤ n → RelationSchedule n)
      (gen : ∀ n, 2 ≤ n → generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1)))),
      (∀ n (hn : 2 ≤ n), threshold ≤ n → (schedules n hn).parameters = parameters Concrete.candidate n ∧
        (schedules n hn).candidates = (dyadicTargets (beta (n.log2+1))).sort) ∧
      ∀ (n : ℕ) (hn : 2 ≤ n) (charge : ℕ → ℕ) (cap : ℕ),
        (∀ a, 2 ≤ a → a ≤ n → charge a ≤ cap) →
        let tree := factor (fun a ha => scheduleDecision ha (schedules a ha) _ (gen a ha)) n hn
        tree.factors.prod = n ∧ (∀ p ∈ tree.factors, p.Prime) ∧
        (∀ p, p.Prime → ∀ j, p^j ∣ n ↔ j ≤ tree.factors.count p) ∧
        tree.work charge ≤ (2*n.log2-1)*cap :=
  Concrete.factor_of_box_coverage LFunction_eq_zero_re covered

end Cogentic
