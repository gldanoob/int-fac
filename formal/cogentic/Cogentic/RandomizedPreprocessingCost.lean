import Cogentic.RandomizedPreprocessing

namespace Cogentic.RandomizedPreprocessing

open BinaryDivision

private theorem primality_diagonal (X : ℕ) (positive : 0 < X) :
    BinarySplitter.primalityBudget X X ≤ 4096*X^5 := by
  obtain ⟨u, eq⟩ := Nat.exists_eq_succ_of_ne_zero positive.ne'
  rw [eq, Nat.succ_eq_add_one]
  unfold BinarySplitter.primalityBudget BinarySplitter.baseBudget BinarySplitter.scanStepBudget
    BinaryModularPower.powerBudget BinaryModularPower.gcdBudget
  ring_nf
  omega

private theorem primality_power (Y : ℕ) (large : 4096 ≤ Y) : 4096*(Y^6)^5 ≤ Y^31 := by
  calc
    _ ≤ Y*(Y^6)^5 := Nat.mul_le_mul_right _ large
    _ = Y*Y^(6*5) := congrArg (Y * ·) (pow_mul Y 6 5).symm
    _ = Y^31 := (pow_succ' Y 30).symm

private theorem primality_bound (k n : ℕ) :
    let b := n.log2+1
    let Y := 10000*(k+b+1)
    (BinarySplitter.primality n (List.range' 1 (polyCutoff k b))).2 ≤ Y^31 := by
  intro b Y
  let X := Y^6
  let cap := polyCutoff k b
  have y : 4096 ≤ Y := by dsimp [Y]; omega
  have x : 0 < X := Nat.pow_pos (by omega)
  have yx : Y ≤ X := by
    simpa only [pow_one] using (Nat.pow_le_pow_right (show 0 < Y by omega) (by decide : 1 ≤ 6))
  have capX : cap ≤ X := by
    unfold cap X polyCutoff
    apply Nat.pow_le_pow_left
    dsimp [Y]
    omega
  have capWidth : cap.size ≤ X := (Nat.size_le.mpr Nat.lt_two_pow_self).trans capX
  have bX : b ≤ X := (show b ≤ Y by dsimp [Y]; omega).trans yx
  have width : max b cap.size ≤ X := max_le bX capWidth
  obtain ⟨_, work⟩ := BinarySplitter.driver_primality n k
  calc
    _ ≤ BinarySplitter.primalityBudget (max b cap.size) cap := work
    _ ≤ BinarySplitter.primalityBudget X X := by
      unfold BinarySplitter.primalityBudget BinarySplitter.baseBudget BinarySplitter.scanStepBudget
        BinaryModularPower.powerBudget BinaryModularPower.gcdBudget
      gcongr
    _ ≤ 4096*X^5 := primality_diagonal X x
    _ ≤ Y^31 := primality_power Y y

private theorem combine_costs (k b : ℕ) :
    let Y := 10000*(k+b+1)
    (3*b+1)*b + 3*b + Y^16 + (Y^31 + 128*(b+1)^6 + 3) ≤
      (10000*(k+1))^32*(b+1)^32 := by
  intro Y
  have big : 128 ≤ Y := by dsimp [Y]; omega
  have byY : b+1 ≤ Y := by dsimp [Y]; omega
  have mono (j : ℕ) (hj : j ≤ 31) : Y^j ≤ Y^31 :=
    Nat.pow_le_pow_right (by omega) hj
  have countBound : (3*b+1)*b + 3*b + 3 ≤ Y^3 := by
    have a : (3*b+1)*b ≤ (3*Y)*Y := Nat.mul_le_mul (by omega) (by omega)
    have b' : 3*b+3 ≤ 4*Y := by omega
    have c : (3*Y)*Y+4*Y ≤ Y^3 := by
      nlinarith only [Nat.mul_le_mul_right (Y^2) (show 8 ≤ Y by omega),
        Nat.mul_le_mul_left Y (show 1 ≤ Y by omega)]
    omega
  have powerBound : 128*(b+1)^6 ≤ Y^7 := by
    calc
      _ ≤ Y*Y^6 := Nat.mul_le_mul big (Nat.pow_le_pow_left byY 6)
      _ = _ := (pow_succ' Y 6).symm
  have yscale : Y ≤ 10000*(k+1)*(b+1) := by
    dsimp [Y]
    nlinarith only [Nat.zero_le (k*b)]
  calc
    _ ≤ 4*Y^31 := by
      have small := countBound.trans (mono 3 (by decide))
      have powers := powerBound.trans (mono 7 (by decide))
      have genWork := mono 16 (by decide)
      omega
    _ ≤ Y*Y^31 := Nat.mul_le_mul_right _ (by omega)
    _ = Y^32 := (pow_succ' Y 31).symm
    _ ≤ (10000*(k+1)*(b+1))^32 := Nat.pow_le_pow_left yscale 32
    _ = (10000*(k+1))^32*(b+1)^32 := mul_pow ..

private theorem generator_values (xs : List ℕ) :
    (xs.map Nat.bits).map value = xs := by
  simp only [List.map_map, Function.comp_def, value_bits, List.map_id_fun', id_eq]

private theorem setup_spec (k n : ℕ) (pos : 0 < n) :
    let b := n.log2+1
    let count := BinaryIndexCap.count n.bits
    let length := BinarySaturation.canonical count.1
    let gen := BinaryGenerators.run k length.1
    gen.1.map value = List.range' 1 (polyCutoff k b) ∧
      count.2 + length.2 + gen.2 ≤ (3*b+1)*b + 3*b + (10000*(k+b+1))^16 := by
  intro b count length gen
  have bits : n.bits.length = b := by
    rw [Nat.size_eq_bits_len]
    exact Nat.le_antisymm (Nat.size_le.mpr Nat.lt_log2_self)
      (Nat.lt_size.mpr (Nat.log2_self_le pos.ne'))
  have ⟨cv, cl, cw⟩ := BinaryIndexCap.count_spec n.bits
  have ⟨lv, lw⟩ := BinarySaturation.canonical_spec count.1
  change value count.1 = _ at cv
  change count.1.length = _ at cl
  change count.2 ≤ _ at cw
  change length.1 = (value count.1).bits at lv
  change length.2 = 3*count.1.length at lw
  rw [cv, bits] at lv
  rw [cl, bits] at lw
  rw [bits] at cw
  have ⟨bv, bw⟩ := BinaryGenerators.local_polynomial k b
  have words : gen.1 = (List.range' 1 (polyCutoff k b)).map Nat.bits := by
    change (BinaryGenerators.run k length.1).1 = _
    exact (congrArg (fun w => (BinaryGenerators.run k w).1) lv).trans bv
  have work : gen.2 ≤ (10000*(k+b+1))^16 := by
    change (BinaryGenerators.run k length.1).2 ≤ _
    exact (congrArg (fun w => (BinaryGenerators.run k w).2) lv).trans_le bw
  have decoded : gen.1.map value = List.range' 1 (polyCutoff k b) :=
    (congrArg (List.map value) words).trans (generator_values (List.range' 1 (polyCutoff k b)))
  have countWork : count.2 + length.2 ≤ (3*b+1)*b + 3*b := Nat.add_le_add cw lw.le
  exact ⟨decoded, Nat.add_le_add countWork work⟩

/-- Uniform correctness and polynomial bit cost for all inputs in the
factorization domain. The constant depends only on the chosen generator cutoff. -/
theorem run_spec (k n : ℕ) (hn : 2 ≤ n)
    (gen : generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1)))) :
    (run k n).1.Sound n ∧
      (run k n).2 ≤ (10000*(k+1))^32*(n.log2+2)^32 := by
  let b := n.log2+1
  let Y := 10000*(k+b+1)
  let count := BinaryIndexCap.count n.bits
  let length := BinarySaturation.canonical count.1
  let generators := BinaryGenerators.run k length.1
  let bases := List.range' 1 (polyCutoff k b)
  let out := classify n bases
  have pos : 0 < n := by omega
  have ⟨baseEq, setup⟩ := setup_spec k n pos
  change generators.1.map value = bases at baseEq
  change count.2 + length.2 + generators.2 ≤ (3*b+1)*b + 3*b + Y^16 at setup
  have hRun : run k n = (out.1, count.2+length.2+generators.2 + out.2) := by
    have eq := congrArg (classify n) baseEq
    change ((classify n (generators.1.map value)).1,
      count.2+length.2+generators.2 + (classify n (generators.1.map value)).2) = _
    rw [eq]
  have ⟨sound, classWork⟩ := classify_spec (k := k) hn gen
  have p := primality_bound k n
  have q := (BinaryPowerScan.driver_power_scan pos).2
  have hcost : out.2 ≤ Y^31 + 128*(b+1)^6 + 3 :=
    classWork.trans (Nat.add_le_add_right (Nat.add_le_add p q) 3)
  rw [hRun]
  exact ⟨sound, (Nat.add_le_add setup hcost).trans (combine_costs k b)⟩

/-- The critical-line bound supplies one generator cutoff for all recursive
inputs. The preprocessing is deterministic, so it adds this cost once per call. -/
theorem of_critical_line (line : DirichletLZerosOnLine) :
    ∃ k : ℕ, ∀ n ≥ 2,
      (run k n).1.Sound n ∧
        (run k n).2 ≤ (10000*(k+1))^32*(n.log2+2)^32 := by
  obtain ⟨k, supply⟩ := polynomial_generators_from_critical_line line
  refine ⟨k, fun n hn => ?_⟩
  have : NeZero n := ⟨by omega⟩
  exact run_spec k n hn (supply n _ Nat.lt_log2_self)

end Cogentic.RandomizedPreprocessing
