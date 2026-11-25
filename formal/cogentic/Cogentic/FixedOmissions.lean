import Cogentic.FixedPrincipalMass
import Cogentic.OmittedDecay

namespace Cogentic.Window
open Real

/-- The total Bernoulli mass of every polynomial deletion budget is
    at most u⁻⁵ on the executable dyadic schedule. -/
theorem fixed_prime_deletions (k : ℕ) :
    ∃ n₀ : ℕ, ∀ b ≥ n₀, ∀ (u α : ℝ),
    let B := (Fixed.B b:ℝ)
    let H := log B
    let J := (Finset.Ioc ⌊sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
    let m := B^(-199/400:ℝ)
    let δ := (b:ℝ)^k*m
    90*(Fixed.d b:ℝ) ≤ u → u ≤ 110*(Fixed.d b:ℝ) → 199/200 ≤ α →
    0 < H ∧ 2 ≤ u ∧ 0 ≤ m ∧ m ≤ δ ∧ δ ≤ 1/u^5 ∧
    (∀ p∈J, primeProbability α p ≤ m ∧ H/2 ≤ log p ∧ log p ≤ H) ∧
    ∀ D : Finset ℕ, D.card ≤ b^k → (∑ p∈J, if p∈D then primeProbability α p else 0) ≤ δ := by
  obtain ⟨n₁,budget⟩ := fixed_prime_overhead 0 le_rfl (k+10)
  obtain ⟨n₂,deg⟩ := Fixed.degree_grows 50000
  refine ⟨max n₁ n₂,?_⟩
  intro b huge u α B H J m δ lo hi ha
  obtain ⟨one,two⟩ := max_le_iff.mp huge
  have db := Fixed.degree_le_bits b
  have d := deg b two
  have d0 : 50000 ≤ (Fixed.d b:ℝ) := by exact_mod_cast d
  have bs : 50000 ≤ (b:ℝ) := by exact_mod_cast d.trans db
  have bb : 1 ≤ (b:ℝ) := by linarith only [bs]
  have large : 2 ≤ u := by linarith only [lo,d0]
  have up : 0 < u := by linarith only [large]
  have hp : 0 < H := by
    have HH := (fixed_band_log_bounds b (by omega) (by omega)).1
    change 1000*(Fixed.d b:ℝ) ≤ H at HH
    linarith only [HH,d0]
  have bp : 0 < B := by dsimp [B,Fixed.B]; positivity
  have b1 : 1≤B := (one_le_exp hp.le).trans_eq (exp_log bp)
  have mp : 0 ≤ m := rpow_nonneg bp.le _
  have rmax (p) (mem : p ∈ J) : primeProbability α p ≤ m := by
    let w := (p:ℝ)^(-α)
    have w0 : 0 ≤ w := rpow_nonneg (Nat.cast_nonneg _) _
    have low := Nat.lt_of_floor_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp mem).1).1
    have bound := rpow_le_rpow_of_nonpos (sqrt_pos.mpr bp) low.le (by linarith : -α ≤ 0)
    rw [sqrt_eq_rpow,←rpow_mul bp.le] at bound
    change w/(1+w) ≤ m
    refine le_trans ((div_le_iff₀ (by linarith : 0 < 1+w)).mpr (by nlinarith [sq_nonneg w]) : w/(1+w)≤w) ?_
    exact bound.trans (rpow_le_rpow_of_exponent_le b1 (by linarith))
  have band (p) (mem : p ∈ J) : H/2 ≤ log p ∧ log p ≤ H := by
    obtain ⟨h,pp⟩ := Finset.mem_filter.mp mem
    obtain ⟨pl,ph⟩ := Finset.mem_Ioc.mp h
    constructor
    · dsimp [H]; rw [←log_sqrt bp.le]
      exact log_le_log (sqrt_pos.mpr bp) (Nat.lt_of_floor_lt pl).le
    · exact log_le_log (by exact_mod_cast pp.pos) ((Nat.cast_le.mpr ph).trans (Nat.floor_le bp.le))
  have cap := budget b one (Finset.range (b^(k+10))) (by simp)
  simp only [Finset.card_range,Nat.cast_pow,zero_mul,zero_add] at cap
  change (b:ℝ)^(k+10)*m ≤ 1/4 at cap
  have db' : (Fixed.d b:ℝ) ≤ b := by exact_mod_cast db
  have ub : u ≤ (b:ℝ)^2 := by
    nlinarith only [hi,mul_le_mul_of_nonneg_left db' (by norm_num : (0:ℝ) ≤ 110),
      mul_nonneg (Nat.cast_nonneg (α:=ℝ) b) (by linarith only [bs] : 0≤(b:ℝ)-110)]
  have us : u^5 ≤ (b:ℝ)^10 := by simpa [←pow_mul] using pow_le_pow_left₀ up.le ub 5
  have small : δ ≤ 1/u^5 := by
    rw [le_div_iff₀ (by positivity)]
    calc δ*u^5 ≤ δ*(b:ℝ)^10 := mul_le_mul_of_nonneg_left us (mul_nonneg (by positivity) mp)
         _ = (b:ℝ)^(k+10)*m := by dsimp only [δ]; rw [pow_add]; ring
         _ ≤ 1 := cap.trans (by norm_num)
  have md : m ≤ δ := by simpa [δ] using mul_le_mul_of_nonneg_right (one_le_pow₀ (n:=k) bb) mp
  refine ⟨hp,large,mp,md,small,fun p h => ⟨rmax p h,band p h⟩,?_⟩
  intro D card
  let A := J.filter (·∈D)
  have sub : A⊆D := fun p h => (Finset.mem_filter.mp h).2
  have pcard : (A.card:ℝ) ≤ (b:ℝ)^k := by exact_mod_cast (Finset.card_le_card sub).trans card
  rw [←Finset.sum_filter]
  have z := Finset.sum_le_sum (s:=A) (fun p h => rmax p (Finset.mem_filter.mp h).1)
  simp only [Finset.sum_const,nsmul_eq_mul] at z
  exact z.trans (mul_le_mul_of_nonneg_right pcard mp)

/-- Actual central mass is uniformly bounded on every logarithmic shift,
    including those obtained by dividing a nonunit residue by its gcd. -/
theorem fixed_all_shift_upper (k : ℕ) :
    ∃ n₀ : ℕ, ∀ b ≥ n₀, ∀ (u α a : ℝ) (D : Finset ℕ),
    let B := (Fixed.B b:ℝ)
    let H := log B
    let J := (Finset.Ioc ⌊sqrt B⌋₊ ⌊B⌋₊).filter Nat.Prime
    90*(Fixed.d b:ℝ) ≤ u → u ≤ 110*(Fixed.d b:ℝ) → 199/200 ≤ α →
    saddleMean J α = H*u → D.card ≤ b^k →
    |omittedMass J D (primeProbability α) (fun p => log p) H a| ≤ sqrt (24*π)/(H*sqrt u) := by
  obtain ⟨n₀,data⟩ := fixed_prime_deletions k
  refine ⟨n₀,?_⟩
  intro b big u α a D B H J lo hi ha mean card
  obtain ⟨hp,large,_,_,tiny,band,del⟩ := data b big u α lo hi ha
  have up : 0<u := by linarith
  apply omitted_prime_mass_uniform J D α H u a (by linarith) hp up
    (fun p h => (Finset.mem_filter.mp h).2.one_le) (fun p h => (band p h).2) mean
  apply (del D card).trans (tiny.trans _)
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have pow := pow_le_pow_left₀ (by norm_num : 0≤(2:ℝ)) large 5
  norm_num at pow
  nlinarith only [mul_le_mul_of_nonneg_right large (pow_nonneg up.le 5),pow]

end Cogentic.Window
