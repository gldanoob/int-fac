import Cogentic.GeneratorListCost
import Cogentic.PowerScanCost

namespace Cogentic.RandomizedPreprocessing

open BinaryDivision TwoThirdsSearch

inductive Result where
  | prime
  | split (d : ℕ)
  | hard

def Result.Sound (n : ℕ) : Result → Prop
  | .prime => n.Prime
  | .split d => ProperDivisor n d
  | .hard => Odd n ∧ ¬ n.Prime ∧ ¬ IsPrimePow n

/-- The fixed guards before the randomized search. Splitting by two uses the
low input bit. The remaining easy inputs use the counted binary root scan. -/
def classify (n : ℕ) (bases : List ℕ) : Result × ℕ :=
  let test := BinarySplitter.primality n bases
  if test.1 then (.prime, test.2 + 1)
  else if n.bits.headD false = false then (.split 2, test.2 + 2)
  else
    let powers := BinaryPowerScan.run n.bits
    match powers.1 with
    | some d => (.split (value d), test.2 + powers.2 + 3)
    | none => (.hard, test.2 + powers.2 + 3)

/-- Build the generator words from the bit length of the input and run the
preprocessing. Values denote the same words in the splitter's interface. -/
def run (k n : ℕ) : Result × ℕ :=
  let count := BinaryIndexCap.count n.bits
  let length := BinarySaturation.canonical count.1
  let bases := BinaryGenerators.run k length.1
  let result := classify n (bases.1.map value)
  (result.1, count.2 + length.2 + bases.2 + result.2)

example : (classify 2 []).1 = .prime := rfl
example : (classify 4 []).1 = .split 2 := rfl

theorem classify_spec {k n : ℕ} (hn : 2 ≤ n)
    (gen : generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1)))) :
    let b := n.log2+1
    let bases := List.range' 1 (polyCutoff k b)
    let test := BinarySplitter.primality n bases
    (classify n bases).1.Sound n ∧
      (classify n bases).2 ≤ test.2 + (BinaryPowerScan.run n.bits).2 + 3 := by
  intro b bases test
  have valid : test.1 = true ↔ n.Prime := by
    change (BinarySplitter.primality n (List.range' 1 (polyCutoff k (n.log2+1)))).1 = true ↔ n.Prime
    rw [(BinarySplitter.driver_primality n k).1]
    exact primeCheck_correct n bases gen
  have bit : n % 2 = (n.bits.headD false).toNat := by
    calc
      n % 2 = value n.bits % 2 := by rw [value_bits]
      _ = _ := by
        rw [value_head]
        cases n.bits.headD false <;> simp
  obtain ⟨scan, _⟩ := BinaryPowerScan.driver_power_scan (show 0 < n by omega)
  change (BinaryPowerScan.run n.bits).1.map value = (powerDivisor n b).map Subtype.val at scan
  unfold classify
  dsimp only [test]
  split
  · rename_i prime
    exact ⟨valid.mp prime, by omega⟩
  · rename_i rejected
    have composite : ¬ n.Prime := mt valid.mpr rejected
    split
    · rename_i even
      have ne : n ≠ 2 := fun eq => composite (eq ▸ Nat.prime_two)
      have evenBit : n.bits.headD false = false := even
      have dvd : 2 ∣ n := Nat.dvd_iff_mod_eq_zero.mpr (by
        simpa only [evenBit, Bool.toNat_false] using bit)
      exact ⟨⟨by decide, by omega, dvd⟩, by omega⟩
    · rename_i odd
      have mod : n % 2 = 1 := by
        have hb : n.bits.headD false = true := Bool.eq_true_of_not_eq_false odd
        simpa only [hb, Bool.toNat_true] using bit
      split
      · rename_i d hd
        rw [hd] at scan
        cases hp : powerDivisor n b with
        | none => simp [hp] at scan
        | some divisor =>
          simp only [hp, Option.map_some, Option.some.injEq] at scan
          exact ⟨scan.symm ▸ divisor.property, le_rfl⟩
      · rename_i missing
        have no : powerDivisor n b = none := by
          rw [missing] at scan
          exact Option.map_eq_none_iff.mp scan.symm
        exact ⟨⟨⟨n/2, by omega⟩, composite,
          fun pp => powerDivisor_complete Nat.lt_log2_self composite pp no⟩, le_rfl⟩

end Cogentic.RandomizedPreprocessing
