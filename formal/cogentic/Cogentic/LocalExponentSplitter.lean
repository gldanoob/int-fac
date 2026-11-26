import Cogentic.CompanionReduction
import Cogentic.GeneratorListCost

namespace Cogentic.Companion
open TwoThirdsSearch TwoThirdsFinish BinaryDivision

private theorem binaryBase_sound {n : ℕ} (hn : 0 < n) (g : ℕ)
    (t : BinarySplitter.Stripped) {bits : List Bool}
    (found : (BinarySplitter.base n g t).1 = some bits) :
    ProperDivisor n (value bits) := by
  let init := BinaryModularPower.power g (value t.odd) n
  have width := (BinaryModularPower.power_gates g (value t.odd) n hn).1
  have eq := (BinarySplitter.scanBits_spec n.bits init.1 t.zeros
    (by simpa using hn) (by simpa only [init, ← Nat.size_eq_bits_len] using width)).1
  change (BinarySplitter.scanBits n.bits init.1 t.zeros).1 = some bits at found
  rw [found, Option.map_some, value_bits] at eq
  exact OrderCertificate.scan_sound eq.symm

private theorem binaryBases_sound {n : ℕ} (hn : 0 < n) (t : BinarySplitter.Stripped)
    (gs : List ℕ) (bits : List Bool) (found : (BinarySplitter.bases n t gs).1 = some bits) :
    ProperDivisor n (value bits) := by
  induction gs with
  | nil => simp [BinarySplitter.bases] at found
  | cons g gs ih =>
    cases h : (BinarySplitter.base n g t).1 with
    | none =>
      apply ih
      simpa only [BinarySplitter.bases, h] using found
    | some ds =>
      have same : ds = bits := by simpa only [BinarySplitter.bases, h, Option.some.injEq] using found
      exact same ▸ binaryBase_sound hn g t h

private def threeBits : List Bool → Bool
  | _ :: _ :: _ :: _ => true
  | _ => false

private theorem threeBits_spec (bits : List Bool) : threeBits bits = true ↔ 3 ≤ bits.length := by
  cases bits with
  | nil => decide
  | cons a bits =>
    cases bits with
    | nil => simp [threeBits]
    | cons b bits =>
      cases bits with
      | nil => simp [threeBits]
      | cons c bits =>
        simp only [threeBits, List.length_cons, true_iff]
        omega

private theorem oddBits_pos {n : ℕ} (h : n.bits.headD false = true) : 0 < n := by
  have eq := value_head n.bits
  rw [value_bits, h, Bool.toNat_true] at eq
  omega

private theorem oddBits_odd {n : ℕ} (h : n.bits.headD false = true) : ¬2 ∣ n := by
  have eq := value_head n.bits
  rw [value_bits, h, Bool.toNat_true] at eq
  omega

private theorem evenBits_divisor {n : ℕ} (odd : ¬n.bits.headD false = true)
    (big : threeBits n.bits = true) : ProperDivisor n 2 := by
  refine ⟨by decide, ?_, ?_⟩
  · by_contra! small
    have size := Nat.size_le.mpr (show n < 2^2 by omega)
    rw [← Nat.size_eq_bits_len] at size
    have long := (threeBits_spec n.bits).mp big
    omega
  · have eq := value_head n.bits
    have zero : n.bits.headD false = false := Bool.eq_false_iff.mpr odd
    rw [value_bits, zero, Bool.toNat_false, zero_add] at eq
    exact ⟨_,eq⟩

private theorem lengthWord_bits {n : ℕ} (hn : 0 < n) :
    (BinarySchedule.lengthWord n.bits).1 = (n.log2+1).bits := by
  have size : n.size = n.log2+1 := le_antisymm (Nat.size_le.mpr Nat.lt_log2_self)
    (Nat.succ_le_of_lt (Nat.lt_size.mpr (Nat.log2_self_le hn.ne')))
  rw [(BinarySchedule.lengthWord_spec n.bits).1, Nat.size_eq_bits_len, size]

private def typedBinarySplit (n m : ℕ) (gs : List ℕ) (hn : 0 < n) :
    Option {d // ProperDivisor n d} × ℕ :=
  let out := BinarySplitter.splitter n m gs
  (out.1.pmap (p := fun bits => ProperDivisor n (value bits)) (fun bits sound => ⟨value bits, sound⟩)
    (binaryBases_sound hn (BinarySplitter.strip m.bits) gs), out.2)

private def splitWithSetup (n m : ℕ) (emit : Unit → List ℕ × ℕ) :
    Option {d // ProperDivisor n d} × ℕ :=
  if odd : n.bits.headD false = true then
    let setup := emit ()
    let out := typedBinarySplit n m setup.1 (oddBits_pos odd)
    (out.1,out.2+(setup.2+8))
  else if big : threeBits n.bits = true then
    (some ⟨2, evenBits_divisor odd big⟩, 8)
  else (none, 8)

private def generatorSetup (k n : ℕ) : List ℕ × ℕ :=
  let len := BinarySchedule.lengthWord n.bits
  let gen := BinaryGenerators.run k len.1
  (gen.1.map value,len.2+gen.2)

private theorem map_encoded_values (gs : List ℕ) : (gs.map Nat.bits).map value = gs := by
  rw [List.map_map, show value ∘ Nat.bits = id from funext value_bits, List.map_id]

private theorem generatorSetup_eq (k : ℕ) {n : ℕ} (hn : 0 < n) :
    generatorSetup k n = (List.range' 1 (polyCutoff k (n.log2+1)),
      (BinarySchedule.lengthWord n.bits).2+(BinaryGenerators.run k (n.log2+1).bits).2) := by
  let len := BinarySchedule.lengthWord n.bits
  let b := n.log2+1
  let gen := BinaryGenerators.run k b.bits
  let gs := List.range' 1 (polyCutoff k b)
  have wordEq : gen.1 = gs.map Nat.bits :=
    (BinaryGenerators.local_polynomial k (n.log2+1)).1
  calc
    _ = (gen.1.map value,len.2+gen.2) :=
      congrArg (fun bits : List Bool =>
        ((BinaryGenerators.run k bits).1.map value,len.2+(BinaryGenerators.run k bits).2))
        (lengthWord_bits hn)
    _ = ((gs.map Nat.bits).map value,len.2+gen.2) :=
      congrArg (fun bs : List (List Bool) => (bs.map value,len.2+gen.2)) wordEq
    _ = _ := congrArg (fun ns : List ℕ => (ns,len.2+gen.2)) (map_encoded_values gs)

/-- The binary generator supplies the list of small bases. Eight gates cover
the parity and prefix tests and dispatch. Naturals at the interface encode
the same bits as the metered splitter. -/
def localExponentSplitter (k : ℕ) : Splitter := fun n m =>
  splitWithSetup n m (fun _ => generatorSetup k n)

private theorem splitWithSetup_cost (n m : ℕ) (emit : Unit → List ℕ × ℕ) :
    (splitWithSetup n m emit).2 ≤ (BinarySplitter.splitter n m (emit ()).1).2 + ((emit ()).2+8) := by
  by_cases odd : n.bits.headD false = true
  · rw [splitWithSetup, dif_pos odd]
    exact Nat.le_refl _
  · by_cases big : threeBits n.bits = true
    · rw [splitWithSetup, dif_neg odd, dif_pos big]
      exact (Nat.le_add_left 8 _).trans (Nat.le_add_left _ _)
    · rw [splitWithSetup, dif_neg odd, dif_neg big]
      exact (Nat.le_add_left 8 _).trans (Nat.le_add_left _ _)

private theorem splitWithSetup_cost_of_eq (n m : ℕ) (actual : Unit → List ℕ × ℕ)
    (expected : List ℕ × ℕ) (eq : actual () = expected) :
    (splitWithSetup n m actual).2 ≤ (BinarySplitter.splitter n m expected.1).2 + (expected.2+8) := by
  subst expected
  exact splitWithSetup_cost n m actual

theorem localExponentSplitter_cost (k n m : ℕ) :
    (localExponentSplitter k n m).2 ≤
      (BinarySplitter.splitter n m (List.range' 1 (polyCutoff k (n.log2+1)))).2+
        ((BinarySchedule.lengthWord n.bits).2+(BinaryGenerators.run k (n.log2+1).bits).2+8) := by
  by_cases hn : 0 < n
  · exact splitWithSetup_cost_of_eq n m (fun _ => generatorSetup k n)
      (List.range' 1 (polyCutoff k (n.log2+1)),
        (BinarySchedule.lengthWord n.bits).2+(BinaryGenerators.run k (n.log2+1).bits).2)
      (generatorSetup_eq k hn)
  · have zero : n = 0 := by omega
    subst n
    change 8≤_
    exact (Nat.le_add_left 8 _).trans (Nat.le_add_left _ _)

private theorem splitWithSetup_success (n m A : ℕ) (setup : List ℕ × ℕ)
    (large : 4 ≤ n) (comp : ¬n.Prime)
    (nonpower : ∀ x j : ℕ, 2 ≤ x → 2 ≤ j → x^j ≠ n) (hm : 2 ≤ m)
    (exponent : ∀ p : ℕ, p.Prime → p ∣ n → p-1 ∣ m)
    (gen : generatesUnits n setup.1) (width : ∀ g ∈ setup.1, g.size ≤ A) :
    (splitWithSetup n m (fun _ => setup)).1 ≠ none := by
  by_cases hodd : n.bits.headD false = true
  · rw [splitWithSetup, dif_pos hodd]
    have odd := oddBits_odd hodd
    have hn : 2 ≤ n := by omega
    have npp : ¬IsPrimePow n := by
      intro power
      obtain ⟨p,j,prime,jp,eq⟩ := (isPrimePow_nat_iff n).mp power
      have two : 2 ≤ j := by
        by_contra! h
        exact comp (by simpa only [←eq,show j=1 by omega,pow_one] using prime)
      exact nonpower p j prime.two_le two eq
    obtain ⟨p,pm,q,qm,neq⟩ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le hn).mp npp
    obtain ⟨pp,pn,_⟩ := Nat.mem_primeFactors.mp pm
    obtain ⟨qp,qn,_⟩ := Nat.mem_primeFactors.mp qm
    let : Fact p.Prime := ⟨pp⟩
    let : Fact q.Prime := ⟨qp⟩
    have gt (r : ℕ) (prime : r.Prime) (div : r ∣ n) : 2<r :=
      lt_of_le_of_ne prime.two_le (fun eq => odd (eq ▸ div))
    have success := saturated_splitter hn hm (gt p pp pn) (gt q qp qn) neq pn qn
      (exponent p pp pn) (exponent q qp qn) setup.1 gen
    have eq := (BinarySplitter.splitter_spec n m A setup.1 (by omega) (by omega) width).1
    simp only [typedBinarySplit]
    intro h
    have miss := Option.pmap_eq_none_iff.mp h
    rw [miss, Option.map_none] at eq
    exact success (Option.map_eq_none_iff.mp eq.symm)
  · have long : 3 ≤ n.bits.length := by
      by_contra! small
      have bound := value_lt n.bits
      rw [value_bits] at bound
      have pow := Nat.pow_le_pow_right (by decide : 0 < 2) (show n.bits.length ≤ 2 by omega)
      omega
    rw [splitWithSetup, dif_neg hodd, dif_pos ((threeBits_spec n.bits).mpr long)]
    exact Option.some_ne_none _

/-- The metered splitter succeeds on a composite non-power given generators
and a positive common multiple of the prime-factor exponents. -/
theorem localExponentSplitter_success (k n m : ℕ) (large : 4 ≤ n) (comp : ¬n.Prime)
    (nonpower : ∀ x j : ℕ, 2 ≤ x → 2 ≤ j → x^j ≠ n) (hm : 2 ≤ m)
    (exponent : ∀ p : ℕ, p.Prime → p ∣ n → p-1 ∣ m)
    (gen : generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1)))) :
    (localExponentSplitter k n m).1 ≠ none := by
  have range_width (cap : ℕ) : ∀ g ∈ List.range' 1 cap, g.size ≤ cap.size := by
    intro g hg
    have hi := (List.mem_range'_1.mp hg).2
    exact Nat.size_le_size (by omega : g ≤ cap)
  let cap := polyCutoff k (n.log2+1)
  let setup := (List.range' 1 cap,
    (BinarySchedule.lengthWord n.bits).2+(BinaryGenerators.run k (n.log2+1).bits).2)
  have ok := splitWithSetup_success n m cap.size setup
    large comp nonpower hm exponent gen (range_width cap)
  have eq : (localExponentSplitter k n m).1 = (splitWithSetup n m (fun _ => setup)).1 :=
    congrArg (fun data : List ℕ × ℕ => (splitWithSetup n m (fun _ => data)).1)
      (generatorSetup_eq k (by omega : 0 < n))
  exact fun none => ok (eq.symm.trans none)

end Cogentic.Companion

#print axioms Cogentic.Companion.localExponentSplitter_success
#print axioms Cogentic.Companion.localExponentSplitter_cost
