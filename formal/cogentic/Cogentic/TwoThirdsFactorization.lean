import Cogentic.BinaryFactorization
import Cogentic.MissRank

namespace Cogentic.Companion
open Concrete TwoThirdsFactor TwoThirdsSearch TwoThirdsFinish CompanionSplitCost Real Filter

/-- The deterministic driver returns all prime words with multiplicity.
The same run has a uniform two-thirds bit bound on sufficiently large inputs. -/
theorem factor_words_two_thirds (line : DirichletLZerosOnLine)
    (split : Splitter) {C₁ A : ℝ} (hc : 0≤C₁) (ha : 0≤A) (spec : SplitterSpec split C₁ A) :
    ∃ (k : ℕ) (gen : ∀ n, 2 ≤ n → generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1)))),
      (∀ n (hn : 2≤n),
        let primes := (factorWords split k gen n hn).1.map BinaryDivision.value
        primes.prod=n ∧ (∀ p∈primes, p.Prime) ∧ (∀ p, p.Prime → ∀ j, p^j∣n ↔ j≤primes.count p)) ∧
      ∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in atTop, ∀ hn : 2≤n,
        ((factorWords split k gen n hn).2:ℝ) ≤
          exp ((max 6528665845 (C₁+12*A+131117)+ε)*scale n) := by
  obtain ⟨k,gen,correct,time⟩ := factor_words_of_dense_hits line split hc ha spec
  obtain ⟨b₀,rank⟩ := Construction.eventual_box_has_rank line
  refine ⟨k,gen,correct,time (dense_hits_of_box_rank line gen ?_)⟩
  filter_upwards [eventually_ge_atTop (2^b₀)] with n large gate composite ell target
  have hn := gate.1
  have bits := (Nat.le_log2 (show n≠0 by omega)).mpr large
  exact rank (by omega) hn composite target gate.2.2.2.2.2

end Cogentic.Companion

#print axioms Cogentic.Companion.factor_words_two_thirds
