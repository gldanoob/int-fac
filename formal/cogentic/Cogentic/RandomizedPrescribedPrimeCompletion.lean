import Cogentic.RandomizedProductPerron
import Cogentic.RandomizedPrimeBinPatterns
import Cogentic.Window

namespace Cogentic.Randomized

open Finset
open scoped BigOperators

/-- The distinct products of the slots that remain after prescribing slot `j`. -/
def primeCompletionProducts {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ι → ℕ) (j : ι) : Finset ℕ :=
  primeBinProducts (fun i : {i : ι // i ≠ j} ↦ A i) (fun i ↦ B i)

private theorem prod_delete_slot {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → ℕ) (j : ι) :
    (∏ i, f i) = f j * ∏ i : {i : ι // i ≠ j}, f i := by
  rw [← Finset.prod_subtype (p := fun i : ι ↦ i ≠ j) (Finset.univ.erase j)
    (fun i ↦ by simp) f]
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm

private theorem completion_pairwise {ι : Type} [DecidableEq ι] {A B : ι → ℕ} (j : ι)
    (hdisj : Pairwise fun i k ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A k) (B k))) :
    Pairwise fun (i k : {i : ι // i ≠ j}) ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A k) (B k)) :=
  fun _ _ h ↦ hdisj (fun he ↦ h (Subtype.ext he))

/-- In disjoint prime bins, divisibility by a prime of slot `j` prescribes that
slot exactly. Multiplication by the prescribed prime recovers the original products. -/
theorem primeBinProducts_filter_dvd_eq_completion_image {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ι → ℕ) (j : ι) {p : ℕ} (hp : p ∈ primeBin (A j) (B j))
    (hdisj : Pairwise fun i k ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A k) (B k))) :
    (primeBinProducts A B).filter (p ∣ ·) = (primeCompletionProducts A B j).image (p * ·) := by
  classical
  ext n
  constructor
  · intro hn
    obtain ⟨hn, hpn⟩ := Finset.mem_filter.mp hn
    obtain ⟨g, hg, hgn⟩ := Finset.mem_image.mp hn
    have hprime := (Finset.mem_filter.mp hp).2
    have hd : p ∣ ∏ i, g i := hgn.symm ▸ hpn
    obtain ⟨i, _, hi⟩ := ((Nat.prime_iff.mp hprime).dvd_finsetProd_iff g).mp hd
    have hgi := Fintype.mem_piFinset.mp hg i
    have hpe : p = g i := (Nat.prime_dvd_prime_iff_eq hprime (Finset.mem_filter.mp hgi).2).mp hi
    have hij : i = j := by
      by_contra hne
      exact (Finset.disjoint_left.mp (hdisj hne)) hgi (hpe ▸ hp)
    subst i
    apply Finset.mem_image.mpr
    refine ⟨∏ i : {i : ι // i ≠ j}, g i, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨fun i ↦ g i,
        Fintype.mem_piFinset.mpr (fun i ↦ Fintype.mem_piFinset.mp hg i), rfl⟩
    · rw [hpe, ← prod_delete_slot]
      exact hgn
  · intro hn
    obtain ⟨n', hn', rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hn'
    let f : ι → ℕ := fun i ↦ if hi : i = j then p else g ⟨i, hi⟩
    have hf : f ∈ Fintype.piFinset (fun i ↦ primeBin (A i) (B i)) := by
      apply Fintype.mem_piFinset.mpr
      intro i
      by_cases hi : i = j
      · subst i
        simpa [f] using hp
      · simpa [f, hi] using Fintype.mem_piFinset.mp hg ⟨i, hi⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨f, hf, ?_⟩, dvd_mul_right _ _⟩
    rw [prod_delete_slot f j, show f j = p by simp [f]]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    exact dif_neg i.property

/-- The exact completion mass is the original pattern mass with one prime-bin
cardinality removed. This identity includes empty remaining bins. -/
theorem primeBinProducts_card_eq_slot_mul_completion_card {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ι → ℕ) (j : ι)
    (hdisj : Pairwise fun i k ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A k) (B k))) :
    (primeBinProducts A B).card = (primeBin (A j) (B j)).card * (primeCompletionProducts A B j).card := by
  rw [primeBinProducts_card A B hdisj, primeCompletionProducts,
    primeBinProducts_card _ _ (completion_pairwise j hdisj)]
  exact prod_delete_slot _ j

set_option maxHeartbeats 600000 in
/-- In a union of patterns, prescribing a prime removes exactly one bin factor
from the patterns that occupy its slot. -/
theorem primeBinPatternProducts_prescribed_card {ι : Type} [DecidableEq ι]
    (A B : ι → ℕ) (patterns : Finset (Finset ι)) (j : ι) {p : ℕ}
    (hp : p ∈ primeBin (A j) (B j))
    (hdisj : Pairwise fun i k ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A k) (B k))) :
    (primeBin (A j) (B j)).card *
      ((primeBinPatternProducts A B patterns).filter (p ∣ ·)).card =
    (primeBinPatternProducts A B (patterns.filter (j ∈ ·))).card := by
  let P (s : Finset ι) := primeBinProducts (fun i : s ↦ A i) (fun i ↦ B i)
  have hp0 : p ≠ 0 := (Finset.mem_filter.mp hp).2.ne_zero
  change (primeBin (A j) (B j)).card * ((patterns.biUnion P).filter (p ∣ ·)).card = _
  rw [Finset.filter_biUnion, Finset.card_biUnion, Finset.mul_sum,
    primeBinPatternProducts_card A B hdisj, Finset.sum_filter]
  · apply Finset.sum_congr rfl
    intro s _
    by_cases hj : j ∈ s
    · rw [if_pos hj]
      have hpair : Pairwise fun (i k : s) ↦
          Disjoint (primeBin (A i) (B i)) (primeBin (A k) (B k)) :=
        fun _ _ h ↦ hdisj (Subtype.val_injective.ne h)
      let js : ↥s := ⟨j, hj⟩
      let As (i : ↥s) := A i
      let Bs (i : ↥s) := B i
      have hpj : p ∈ primeBin (As js) (Bs js) := hp
      have himage := primeBinProducts_filter_dvd_eq_completion_image As Bs js hpj hpair
      have hcard := primeBinProducts_card_eq_slot_mul_completion_card As Bs js hpair
      change (P s).filter (p ∣ ·) = (primeCompletionProducts As Bs js).image (p * ·) at himage
      change (primeBin (A j) (B j)).card * ((P s).filter (p ∣ ·)).card = (P s).card
      rw [himage, Finset.card_image_of_injective _ (fun _ _ h ↦ mul_left_cancel₀ hp0 h)]
      exact hcard.symm
    · rw [if_neg hj]
      have hempty : (P s).filter (p ∣ ·) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro n hn
        obtain ⟨hn, hpn⟩ := Finset.mem_filter.mp hn
        obtain ⟨g, hg, hgn⟩ := Finset.mem_image.mp hn
        have hprime := (Finset.mem_filter.mp hp).2
        have hd : p ∣ ∏ i : s, g i := hgn.symm ▸ hpn
        obtain ⟨i, _, hi⟩ := ((Nat.prime_iff.mp hprime).dvd_finsetProd_iff g).mp hd
        have hgi := Fintype.mem_piFinset.mp hg i
        have hpe := (Nat.prime_dvd_prime_iff_eq hprime (Finset.mem_filter.mp hgi).2).mp hi
        exact (Finset.disjoint_left.mp (hdisj (show (i : ι) ≠ j from
          fun he ↦ hj (he ▸ i.property)))) hgi (hpe ▸ hp)
      rw [hempty, Finset.card_empty, mul_zero]
  · intro s _ t _ hst
    exact (primeBinProducts_disjoint_patterns A B hdisj hst).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- Exact passage from the original cutoff to the divided integer cutoff. -/
theorem primeBinProducts_prescribed_prefix_eq_completion_image
    {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → ℕ) (j : ι) {p : ℕ} (m : ℕ)
    (hp : p ∈ primeBin (A j) (B j))
    (hdisj : Pairwise fun i k ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A k) (B k))) :
    ((primeBinProducts A B).filter (p ∣ ·)).filter (· ≤ m) =
      ((primeCompletionProducts A B j).filter (· ≤ m / p)).image (p * ·) := by
  rw [primeBinProducts_filter_dvd_eq_completion_image A B j hp hdisj]
  have hp0 := (Finset.mem_filter.mp hp).2.pos
  ext n
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hle⟩
    exact ⟨w, ⟨hw, (Nat.le_div_iff_mul_le hp0).mpr (by simpa [Nat.mul_comm] using hle)⟩, rfl⟩
  · rintro ⟨w, ⟨hw, hle⟩, rfl⟩
    exact ⟨⟨w, hw, rfl⟩, by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp0).mp hle⟩

/-- The original residue `p*r mod p*q` becomes `r mod q` on the divided value. -/
theorem prescribed_prime_modEq_iff {p q r n : ℕ} (hp : p ≠ 0) :
    p * r ≡ p * n [MOD p * q] ↔ r ≡ n [MOD q] :=
  Nat.ModEq.mul_left_cancel_iff' hp

/-- The original prescribed prefix in a multiple-of-`p` residue class is
counted by the corresponding divided prefix modulo the divided modulus. -/
theorem prescribed_prime_prefix_residue_card {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : ι → ℕ) (j : ι) {p : ℕ} (m q r : ℕ)
    (hp : p ∈ primeBin (A j) (B j))
    (hdisj : Pairwise fun i k ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A k) (B k))) :
    ((((primeBinProducts A B).filter (p ∣ ·)).filter (· ≤ m)).filter
      (fun n ↦ p * r ≡ n [MOD p * q])).card =
    (((primeCompletionProducts A B j).filter (· ≤ m / p)).filter
      (fun n ↦ r ≡ n [MOD q])).card := by
  have hp0 := (Finset.mem_filter.mp hp).2.ne_zero
  rw [primeBinProducts_prescribed_prefix_eq_completion_image A B j m hp hdisj]
  let S := (primeCompletionProducts A B j).filter (· ≤ m / p)
  change ((S.image (p * ·)).filter (fun n ↦ p * r ≡ n [MOD p * q])).card =
    (S.filter (fun n ↦ r ≡ n [MOD q])).card
  have he : (S.image (p * ·)).filter (fun n ↦ p * r ≡ n [MOD p * q]) =
      (S.filter (fun n ↦ r ≡ n [MOD q])).image (p * ·) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, hres⟩
      exact ⟨v, ⟨hv, (prescribed_prime_modEq_iff hp0).mp hres⟩, rfl⟩
    · rintro ⟨v, ⟨hv, hres⟩, rfl⟩
      exact ⟨⟨v, hv, rfl⟩, (prescribed_prime_modEq_iff hp0).mpr hres⟩
  rw [he]
  exact Finset.card_image_of_injective _ (fun _ _ h ↦ mul_left_cancel₀ hp0 h)

private theorem residue_count_of_character_bound {q : ℕ} [NeZero q] (S : Finset ℕ)
    (E : ℝ) (hE : 0 ≤ E) (hχ : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖∑ n ∈ S, χ n‖ ≤ E) (r : (ZMod q)ˣ) :
    |((S.filter (fun n : ℕ ↦ (r : ZMod q) = (n : ZMod q))).card : ℝ) -
      ((S.filter (fun n ↦ n.Coprime q)).card : ℝ) / q.totient| ≤ E := by
  classical
  have hmass : Window.classMass S (fun _ ↦ 1) r =
      ((S.filter (fun n : ℕ ↦ (r : ZMod q) = (n : ZMod q))).card : ℂ) := by
    simp [Window.classMass]
  have hprincipal : Window.twist S (fun _ ↦ 1) (1 : DirichletCharacter ℂ q) =
      ((S.filter (fun n ↦ n.Coprime q)).card : ℂ) := by
    simp only [Window.twist, mul_one]
    have hunit (n : ℕ) : (1 : DirichletCharacter ℂ q) (n : ZMod q) =
        if n.Coprime q then 1 else 0 := by
      by_cases hn : n.Coprime q
      · rw [if_pos hn]
        exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hn)
      · rw [if_neg hn]
        exact MulChar.map_nonunit _ (fun h ↦ hn ((ZMod.isUnit_iff_coprime n q).mp h))
    simp_rw [hunit]
    simp
  have h := Window.uniform_progression_bound S (fun _ ↦ 1) E hE
    (fun χ hn ↦ by simpa [Window.twist] using hχ χ hn) r
  rw [hmass, hprincipal, div_mul_eq_mul_div, mul_div_assoc, ← mul_sub, norm_mul] at h
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hreal : (q : ℝ) *
      |((S.filter (fun n : ℕ ↦ (r : ZMod q) = (n : ZMod q))).card : ℝ) -
        ((S.filter (fun n ↦ n.Coprime q)).card : ℝ) / q.totient| ≤ q * E := by
    simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_div, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq] using h
  exact le_of_mul_le_mul_left hreal hq

/-- The prescribed-prime cutoff and the unit residue count at the divided size.
The fixed upper band edge leaves room for a half-integer cutoff at the full
support, and the principal term uses the actual coprime mass of the prefix. -/
theorem prescribed_prime_completion_from_prefix_bound (hprefix : PrimeBinProductPrefixBound) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (X : ℝ) (m q : ℕ) [NeZero q] {ι : Type} [Fintype ι] [DecidableEq ι]
        (A B : ι → ℕ) (j : ι) (p : ℕ),
        p ∈ primeBin (A j) (B j) →
        (Pairwise fun i k ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A k) (B k))) →
        (∀ i, 2 ≤ B i) → (∀ i, A i ≤ B i) →
        (∀ n ∈ primeBinProducts A B, X ≤ (n : ℝ) ∧ (n : ℝ) ≤ (3 / 2) * X) →
        let Y := X / (p : ℝ)
        2 ≤ Y → Real.exp 1 ≤ Y →
        let P := primeCompletionProducts A B j
        let S := P.filter (· ≤ m / p)
        let E := (4 * Real.exp 2 / Real.pi) *
          ((∏ i : {i : ι // i ≠ j}, C * Real.sqrt (B i) *
            (1 + Real.log (q * ((B i : ℝ) + Y ^ 3 + 2))) ^ 3) * Real.log Y) +
          (K / Y ^ 2) * P.card
        (∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖∑ n ∈ S, χ n‖ ≤ E) ∧
        (∀ r : (ZMod q)ˣ,
          |((S.filter (fun n : ℕ ↦ (r : ZMod q) = (n : ZMod q))).card : ℝ) -
            ((S.filter (fun n ↦ n.Coprime q)).card : ℝ) / q.totient| ≤ E) := by
  obtain ⟨C, K, hC, hK, bound⟩ := hprefix
  refine ⟨C, K, hC, hK, ?_⟩
  intro X m q _ ι _ _ A B j p hp hdisj hB hAB hsupport Y hY heY P S E
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.pos
  have hPS (n : ℕ) (hn : n ∈ P) : Y ≤ (n : ℝ) ∧ (n : ℝ) ≤ (3 / 2) * Y := by
    have he : p * n ∈ (primeBinProducts A B).filter (p ∣ ·) := by
      rw [primeBinProducts_filter_dvd_eq_completion_image A B j hp hdisj]
      exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
    have h := hsupport _ (Finset.mem_filter.mp he).1
    push_cast at h
    constructor
    · exact (div_le_iff₀ hp0).2 (by simpa [mul_comm] using h.1)
    · calc
        (n : ℝ) ≤ ((3 / 2) * X) / p := (le_div_iff₀ hp0).2 (by simpa [mul_comm] using h.2)
        _ = (3 / 2) * Y := by simp [Y, mul_div_assoc]
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hlog (i : {i : ι // i ≠ j}) : 0 ≤ Real.log (q * ((B i : ℝ) + Y ^ 3 + 2)) := by
    apply Real.log_nonneg
    apply one_le_mul_of_one_le_of_one_le hq
    have hBi : (0 : ℝ) ≤ B i := by positivity
    have hY3 : 0 ≤ Y ^ 3 := by positivity
    linarith
  have hprod : 0 ≤ ∏ i : {i : ι // i ≠ j}, C * Real.sqrt (B i) *
      (1 + Real.log (q * ((B i : ℝ) + Y ^ 3 + 2))) ^ 3 :=
    Finset.prod_nonneg fun i _ ↦ by have := hlog i; positivity
  have hYL : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hE : 0 ≤ E := by
    dsimp only [E]
    positivity
  have hχ (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) : ‖∑ n ∈ S, χ n‖ ≤ E := by
    by_cases hleft : Y ≤ ((m / p : ℕ) : ℝ) + 1 / 2
    · let U := ⌊(3 / 2) * Y⌋₊
      let k := min (m / p) U
      have hUnonneg : 0 ≤ (3 / 2) * Y := by positivity
      have hYU : Y ≤ (U : ℝ) + 1 / 2 := by
        have h := Nat.lt_floor_add_one ((3 / 2) * Y)
        change (3 / 2) * Y < (U : ℝ) + 1 at h
        linarith
      have hk₁ : Y ≤ (k : ℝ) + 1 / 2 := by
        dsimp only [k]
        rw [Nat.cast_min, ← min_add_add_right]
        exact le_min hleft hYU
      have hk₂ : (k : ℝ) + 1 / 2 ≤ 2 * Y := by
        have h : (k : ℝ) ≤ U := by exact_mod_cast min_le_right (m / p) U
        have hU := Nat.floor_le hUnonneg
        change (U : ℝ) ≤ (3 / 2) * Y at hU
        linarith
      have hSlice : S = P.filter (· ≤ k) := by
        ext n
        change n ∈ P.filter (· ≤ m / p) ↔ n ∈ P.filter (· ≤ k)
        simp only [Finset.mem_filter, k, le_min_iff]
        constructor
        · rintro ⟨hn, hm⟩
          exact ⟨hn, hm, Nat.le_floor ((hPS n hn).2)⟩
        · rintro ⟨hn, hm, _⟩
          exact ⟨hn, hm⟩
      rw [hSlice]
      exact bound Y k q χ hne (fun i : {i : ι // i ≠ j} ↦ A i) (fun i ↦ B i)
        hY heY hk₁ hk₂ (fun n hn ↦ ⟨(hPS n hn).1, by linarith [(hPS n hn).2]⟩)
        (completion_pairwise j hdisj) (fun i ↦ hB i) (fun i ↦ hAB i)
    · have hempty : S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro n hn
        obtain ⟨hP, hm⟩ := Finset.mem_filter.mp hn
        have hm' : (n : ℝ) ≤ (m / p : ℕ) := by exact_mod_cast hm
        exact hleft (by linarith [(hPS n hP).1])
      simpa [hempty] using hE
  exact ⟨hχ, residue_count_of_character_bound S E hE hχ⟩

#print axioms primeBinPatternProducts_prescribed_card
#print axioms prescribed_prime_prefix_residue_card
#print axioms prescribed_prime_completion_from_prefix_bound

end Cogentic.Randomized
