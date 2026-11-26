import Cogentic.BinaryFactorization
import Cogentic.MissRank
import Cogentic.LocalExponentSplitter
import Cogentic.LocalSplitterBound

namespace Cogentic.Companion
open Concrete TwoThirdsFactor TwoThirdsSearch TwoThirdsFinish CompanionSplitCost Real Filter

/-- The deterministic driver returns all prime words with multiplicity.
The same run has a uniform two-thirds bit bound on sufficiently large inputs. -/
theorem factor_words_two_thirds_of_splitter (line : DirichletLZerosOnLine)
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

private theorem setup_le (k n : ℕ) :
    (BinarySchedule.lengthWord n.bits).2+(BinaryGenerators.run k (n.log2+1).bits).2+8 ≤
      (20000*(k+(n.log2+1)+1))^16 := by
  let b := n.log2+1
  let X := 10000*(k+b+1)
  have width : n.bits.length ≤ b := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_log2_self
  have length := (BinarySchedule.lengthWord_spec n.bits).2.trans
    (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (Nat.add_le_add_right width 1) 2))
  have generators : (BinaryGenerators.run k b.bits).2 ≤ X^16 :=
    (BinaryGenerators.local_polynomial k b).2
  have one : 1 ≤ (b+1)^2 := Nat.one_le_pow 2 _ (by omega)
  have lx : 4*(b+1) ≤ X := by dsimp [X]; omega
  have overhead : 8*(b+1)^2+8 ≤ X^16 := calc
    _ ≤ (4*(b+1))^2 := by rw [mul_pow]; norm_num; omega
    _ ≤ X^2 := Nat.pow_le_pow_left lx 2
    _ ≤ X^16 := Nat.pow_le_pow_right (by omega) (by decide)
  have doubled : X^16+X^16 ≤ (2*X)^16 := by
    rw [mul_pow 2 X 16, ← two_mul]
    exact Nat.mul_le_mul_right _ (by decide : 2 ≤ 2^16)
  have eq : 2*X = 20000*(k+b+1) := by dsimp [X]; ring
  rw [eq] at doubled
  change (BinarySchedule.lengthWord n.bits).2+(BinaryGenerators.run k b.bits).2+8 ≤ _
  exact (by omega : _ ≤ X^16+X^16).trans doubled

/-- A single fixed generator cutoff supplies the local splitter at every modulus. -/
theorem localExponentSplitter_spec (line : DirichletLZerosOnLine) :
    ∃ (s : ℕ) (C₁ A : ℝ), 0 ≤ C₁ ∧ 0 ≤ A ∧ SplitterSpec (localExponentSplitter s) C₁ A := by
  obtain ⟨s, gen⟩ := polynomial_generators_from_critical_line line
  obtain ⟨C₁, A, hc, ha, cost⟩ := BinarySplitter.local_splitter_bound s 20000 16
  refine ⟨s, C₁, A, hc, ha, ?_⟩
  intro n m hn comp nonpower hm _ exponent
  let : NeZero n := ⟨by omega⟩
  refine ⟨localExponentSplitter_success s n m hn comp nonpower hm exponent
    (gen n (n.log2+1) Nat.lt_log2_self), ?_⟩
  have setup := setup_le s n
  have charged := (localExponentSplitter_cost s n m).trans (Nat.add_le_add_left setup _)
  exact (Nat.cast_le.mpr charged).trans (cost n m hn hm)

/-- Complete prime factorization by the concrete deterministic local splitter.
Both cutoff constants and the asymptotic time constant are uniform in the input. -/
def LocalFactorizationBound : Prop :=
  ∃ (s k : ℕ) (gen : ∀ n, 2 ≤ n → generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1))))
      (C : ℝ), 0 < C ∧
      (∀ n (hn : 2 ≤ n),
        let primes := (factorWords (localExponentSplitter s) k gen n hn).1.map BinaryDivision.value
        primes.prod = n ∧ (∀ p ∈ primes, p.Prime) ∧
          (∀ p, p.Prime → ∀ j, p^j ∣ n ↔ j ≤ primes.count p)) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
        ((factorWords (localExponentSplitter s) k gen n hn).2 : ℝ) ≤ exp ((C+ε)*scale n)

/-- The archived critical-line statement suffices for the deterministic two-thirds bound. -/
theorem factor_words_two_thirds (line : DirichletLZerosOnLine) : LocalFactorizationBound := by
  obtain ⟨s, C₁, A, hc, ha, spec⟩ := localExponentSplitter_spec line
  obtain ⟨k, gen, correct, time⟩ :=
    factor_words_two_thirds_of_splitter line (localExponentSplitter s) hc ha spec
  exact ⟨s, k, gen, _, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 6528665845) (le_max_left ..),
    correct, time⟩

end Cogentic.Companion

#print axioms Cogentic.Companion.localExponentSplitter_spec
#print axioms Cogentic.Companion.factor_words_two_thirds
