import Cogentic.SmallGenerators
import Cogentic.DyadicTargets

namespace Cogentic

open TwoThirdsFactor TwoThirdsSearch TwoThirdsFinish

/-- Read the root one binary digit at a time, testing each proposed prefix. -/
def rootDigits (n k : ℕ) : ℕ → ℕ → ℕ
  | 0, lo => lo
  | bits+1, lo =>
    let middle := lo + 2^bits
    rootDigits n k bits (if middle^k ≤ n then middle else lo)

private theorem rootDigits_exact {r n k lo bits : ℕ} (hk : 0 < k) (eq : r^k = n)
    (lower : lo ≤ r) (upper : r < lo + 2^bits) : rootDigits n k bits lo = r := by
  subst n
  induction bits generalizing lo with
  | zero => simp only [Nat.pow_zero, rootDigits] at *; omega
  | succ bits ih =>
    rw [rootDigits]
    simp only [Nat.pow_le_pow_iff_left hk.ne']
    rw [Nat.pow_succ] at upper
    split <;> apply ih <;> omega

private def powerCandidate (n bits k : ℕ) : Option {d // ProperDivisor n d} :=
  let d := rootDigits n k bits 0
  if h : 1 < d ∧ d < n ∧ d ∣ n then some ⟨d,h⟩ else none

def powerDivisor (n bits : ℕ) := (List.range' 2 (bits-1)).findSome? (powerCandidate n bits)

theorem powerDivisor_complete {n bits : ℕ} (fits : n < 2^bits) (composite : ¬n.Prime)
    (pp : IsPrimePow n) : powerDivisor n bits ≠ none := by
  obtain ⟨p,k,prime,positive,eq⟩ := (isPrimePow_nat_iff n).mp pp
  have hk : 2 ≤ k := by
    by_contra! h; have : k = 1 := by omega
    exact composite (by simpa [← eq, this] using prime)
  have maxK : k < bits := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    ((Nat.pow_le_pow_left prime.two_le k).trans_lt (eq ▸ fits))
  have less : p < n := by
    calc p = p^1 := by simp
         _ < p^k := Nat.pow_lt_pow_right prime.one_lt (by omega)
         _ = n := eq
  have exactRoot := rootDigits_exact (lo := 0) positive eq (Nat.zero_le _) (by omega : p < 0 + 2^bits)
  have divides : p ∣ n := eq ▸ dvd_pow_self p positive.ne'
  intro h
  have miss := List.findSome?_eq_none_iff.mp h k (List.mem_range'_1.mpr ⟨hk,by omega⟩)
  simp [powerCandidate, exactRoot, prime.one_lt, less, divides] at miss

private def gcdCandidate (n z : ℕ) : Option {d // ProperDivisor n d} :=
  let d := n.gcd z
  if h : 1 < d ∧ d < n then some ⟨d,h.1,h.2,Nat.gcd_dvd_left ..⟩ else none

/-- Try small trial divisors and the paper's gcd checks on base differences. -/
def presieve (n bits beta A m : ℕ) : Option {d // ProperDivisor n d} :=
  ((List.range' 2 (indexCap bits beta - 1)).findSome? (gcdCandidate n)).orElse fun _ =>
    (List.range' 1 A).findSome? (fun a => gcdCandidate n ((a : ℤ) - m).natAbs)

/-- The remaining numerical parameters and candidate-relation extraction procedure. -/
structure RelationSchedule (n : ℕ) where
  beta : ℕ
  L₀ : ℕ
  U : ℕ
  A : ℕ
  m : ℕ
  candidates : List ℕ
  attempt : TryPair
  survives : ¬ n.Prime → ¬ 2 ∣ n → ¬ IsPrimePow n → presieve n (n.log2+1) beta A m = none →
    0 < beta ∧ (∀ a ∈ candidates, Nat.Prime a) ∧ (∀ a ∈ candidates, a ≤ 2^beta) ∧
    2^beta ≤ 3*beta*candidates.toFinset.card ∧
    ∀ a ∈ candidates, BoxWitness n (2*L₀^2*U*A) (2*L₀^2*U) attempt a

theorem presieve_hits {n bits beta A m d : ℕ} (hd : ProperDivisor n d)
    (bound : d ≤ indexCap bits beta) : presieve n bits beta A m ≠ none := by
  have occurs : d ∈ List.range' 2 (indexCap bits beta - 1) :=
    List.mem_range'_1.mpr ⟨hd.1, by have := hd.1; omega⟩
  have yes : gcdCandidate n d ≠ none := by simp [gcdCandidate, Nat.gcd_eq_right hd.2.2, hd.1, hd.2.1]
  have found : (List.range' 2 (indexCap bits beta - 1)).findSome? (gcdCandidate n) ≠ none :=
    fun h => yes (List.findSome?_eq_none_iff.mp h d occurs)
  unfold presieve
  cases h : (List.range' 2 (indexCap bits beta - 1)).findSome? (gcdCandidate n) with
  | none => exact (found h).elim
  | some _ => simp

/-- At the finitely many exceptional input sizes, trial division covers the entire input. -/
def trialSchedule (n : ℕ) (hn : 2 ≤ n) : RelationSchedule n where
  beta := n.log2+1
  L₀ := 0
  U := 0
  A := 0
  m := 0
  candidates := []
  attempt := fun _ _ _ _ _ => none
  survives composite _ _ absent := by
    have proper : ProperDivisor n n.minFac := ⟨(Nat.minFac_prime (by omega : n ≠ 1)).one_lt,
      (Nat.not_prime_iff_minFac_lt hn).mp composite, Nat.minFac_dvd n⟩
    have cap : 2^(n.log2+1) ≤ indexCap (n.log2+1) (n.log2+1) :=
      Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide : 0 < 2))
    exact (presieve_hits proper (proper.2.1.le.trans (Nat.lt_log2_self.le.trans cap)) absent).elim

/-- Only sufficiently large input moduli require efficient relation schedules. -/
def extendSchedules (threshold : ℕ) (large : (n : ℕ) → threshold ≤ n → 2 ≤ n → RelationSchedule n)
    (n : ℕ) (hn : 2 ≤ n) : RelationSchedule n :=
  if h : threshold ≤ n then large n h hn else trialSchedule n hn

theorem extendSchedules_of_large (threshold : ℕ)
    (large : (n : ℕ) → threshold ≤ n → 2 ≤ n → RelationSchedule n)
    {n : ℕ} (hn : 2 ≤ n) (big : threshold ≤ n) :
    extendSchedules threshold large n hn = large n big hn := dif_pos big

/-- The precise numerical inputs still needed from the smooth-window argument
    and the bounded two-field relation extractor. -/
structure BoxParameters where
  beta : ℕ
  L₀ : ℕ
  U : ℕ
  A : ℕ
  m : ℕ
  attempt : TryPair

def RelationSchedule.parameters {n : ℕ} (s : RelationSchedule n) : BoxParameters :=
  ⟨s.beta,s.L₀,s.U,s.A,s.m,s.attempt⟩

def BoxParameters.Covers (s : BoxParameters) (n : ℕ) : Prop :=
  ¬n.Prime → ¬2 ∣ n → ¬IsPrimePow n → presieve n (n.log2+1) s.beta s.A s.m = none →
    ∀ p ∈ dyadicTargets s.beta, BoxWitness n (2*s.L₀^2*s.U*s.A) (2*s.L₀^2*s.U) s.attempt p

/-- GRH supplies the generator count guard for the actual enumerated target primes.
    A finite initial range uses the complete trial fallback. -/
theorem schedules_from_dyadic_boxes (line : DirichletLZerosOnLine) (s : ℕ → BoxParameters)
    (grows : ∀ k : ℕ, ∃ n₀, ∀ n ≥ n₀, k ≤ (s n).beta)
    (boxes : ∃ n₀ : ℕ, ∀ n ≥ n₀, (s n).Covers n) :
    ∃ (threshold : ℕ) (schedules : (n : ℕ) → 2 ≤ n → RelationSchedule n),
      ∀ n (hn : 2 ≤ n), threshold ≤ n →
        (schedules n hn).parameters = s n ∧
        (schedules n hn).candidates = (dyadicTargets (s n).beta).sort := by
  obtain ⟨b,count⟩ := dyadic_count_from_critical_line line
  obtain ⟨n₁,h₁⟩ := grows (b+1)
  obtain ⟨n₂,h₂⟩ := boxes
  let threshold := max n₁ n₂
  let build (n : ℕ) (large : threshold ≤ n) (_ : 2 ≤ n) : RelationSchedule n := {
    beta := (s n).beta, L₀ := (s n).L₀, U := (s n).U, A := (s n).A, m := (s n).m
    candidates := (dyadicTargets (s n).beta).sort, attempt := (s n).attempt
    survives := by
      intro composite odd notPow absent
      have big := h₁ n ((le_max_left ..).trans large)
      have valid := h₂ n ((le_max_right ..).trans large) composite odd notPow absent
      have member {a : ℕ} (ha : a ∈ (dyadicTargets (s n).beta).sort) : a ∈ dyadicTargets (s n).beta := by
        have h := List.mem_toFinset.mpr ha
        simpa only [Finset.sort_toFinset] using h
      rw [Finset.sort_toFinset]
      exact ⟨by omega,
        fun a ha => (mem_dyadicTargets.mp (member ha)).1,
        fun a ha => (mem_dyadicTargets.mp (member ha)).2.2,
        count _ (by omega), fun a ha => valid a (member ha)⟩ }
  refine ⟨threshold, extendSchedules threshold build, fun n hn big => ?_⟩
  rw [extendSchedules_of_large threshold build hn big]
  exact ⟨rfl,rfl⟩

private theorem index_lcm_size (k : ℕ) : Nat.lcmUpto k ≤ 2^(10*k) := by
  have growth := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg k (α := ℝ))
  rw [Chebyshev.psi_eq_log_lcmUpto] at growth
  have lower : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at h ⊢
    exact h
  have four : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  rw [four] at growth
  have h : (Nat.lcmUpto k : ℝ) ≤ (2:ℝ)^(10*k) := by
    apply (Real.log_le_log_iff (by exact_mod_cast Nat.lcmUpto_pos k) (by positivity)).mp
    rw [Real.log_pow]
    push_cast
    exact growth.trans (by nlinarith [mul_le_mul_of_nonneg_right lower (Nat.cast_nonneg k)])
  exact_mod_cast h

/-- Exponents of at most `width` bits give a saturated splitter exponent with
    at most two initial bits, one width per generator and ten bits per index. -/
theorem search_saturated_size {n : ℕ} (hn : 2 ≤ n) (gs : List ℕ) (w₀ w₁ width bits beta : ℕ)
    (attempt : TryPair) (bounded : ∀ g a b c d e,
      attempt g a b c d = some (.exponent e) → e ≤ 2^width) :
    match (collect hn (searchBox n w₀ w₁ attempt) gs).1 with
    | .divisor .. => True
    | .orders e .. => saturate e bits beta ≤ 2^(1+width*gs.length+10*indexCap bits beta) := by
  have upper := collect_exponentLe hn (searchBox n w₀ w₁ attempt) gs (Nat.pow_pos (by decide : 0 < 2))
    (fun g => searchBox_exponentLe n w₀ w₁ g _ attempt (bounded g))
  generalize h : (collect hn (searchBox n w₀ w₁ attempt) gs).1 = res at *
  cases res with
  | divisor => trivial
  | orders e _ _ _ _ =>
    change e ≤ 2*(2^width)^gs.length at upper
    change e * Nat.lcmUpto (indexCap bits beta) ≤ _
    rw [Nat.pow_add, Nat.pow_add, Nat.pow_one, Nat.pow_mul]
    exact Nat.mul_le_mul upper (index_lcm_size _)

private def splitDecision {n : ℕ} (d : {d // ProperDivisor n d}) : Decision n :=
  .split d.val ⟨d.property.1,d.property.2.1⟩ d.property.2.2

/-- A single decision uses only the relation schedule after executable preprocessing. -/
def scheduleDecision {n : ℕ} (hn : 2 ≤ n) (s : RelationSchedule n) (bases : List ℕ)
    (gen : generatesUnits n bases) : Decision n := by
  let bits := n.log2+1
  have fits : n < 2^bits := Nat.lt_log2_self
  if h : primeCheck n bases = true then
    exact .prime (Nat.prime_def.mp ((primeCheck_correct n bases gen).mp h))
  else
    have composite : ¬ n.Prime := fun hp => h ((primeCheck_correct n bases gen).mpr hp)
    if even : 2 ∣ n then
      have : n ≠ 2 := fun he => composite (he ▸ Nat.prime_two)
      exact .split 2 ⟨by decide, by omega⟩ even
    else
      match pow : powerDivisor n bits with
      | some d => exact splitDecision d
      | none =>
        have npp : ¬IsPrimePow n := fun hp => (powerDivisor_complete fits composite hp) pow
        match pre : presieve n bits s.beta s.A s.m with
        | some d => exact splitDecision d
        | none =>
          have ⟨beta,primes,bounded,count,coverage⟩ := s.survives composite even npp pre
          let probe := searchBox n (2*s.L₀^2*s.U*s.A) (2*s.L₀^2*s.U) s.attempt
          let out := (collect hn probe s.candidates).1
          have covers : out.covers s.candidates :=
            collect_complete _ _ _ (fun a ha => searchBox_complete (coverage a ha))
          match result : out with
          | .divisor d hd => exact splitDecision ⟨d,hd⟩
          | .orders e big _ retained checked =>
            have eq : retained = s.candidates := covers
            have saturated (p : ℕ) (hp : p.Prime) (pn : p ∣ n) : p-1 ∣ saturate e bits s.beta := by
              apply collected_orders_saturate retained hn fits beta big (eq ▸ primes)
                (eq ▸ bounded) (eq ▸ count) checked hp pn
            have pos : 0 < (Finset.Icc 1 (indexCap bits s.beta)).lcm id := Nat.pos_of_ne_zero
              (Finset.lcm_ne_zero_iff.mpr (fun x hx => Nat.ne_of_gt (Finset.mem_Icc.mp hx).1))
            have succeeds : splitWithExponent n (saturate e bits s.beta) bases ≠ none := by
              obtain ⟨p,hp,q,hq,neq⟩ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le hn).mp npp
              obtain ⟨pp,pn,_⟩ := Nat.mem_primeFactors.mp hp
              obtain ⟨qp,qn,_⟩ := Nat.mem_primeFactors.mp hq
              have : Fact p.Prime := ⟨pp⟩
              have : Fact q.Prime := ⟨qp⟩
              have oddFactor (r : ℕ) (prime : r.Prime) (rn : r ∣ n) : 2 < r :=
                lt_of_le_of_ne prime.two_le (fun he => even (he ▸ rn))
              exact saturated_splitter hn (big.trans (Nat.le_mul_of_pos_right _ pos))
                (oddFactor p pp pn) (oddFactor q qp qn) neq pn qn
                (saturated p pp pn) (saturated q qp qn) _ gen
            match hs : splitWithExponent n (saturate e bits s.beta) bases with
            | some d => exact splitDecision d
            | none => exact False.elim (succeeds hs)

/-- Qualitative complete factorization with certified multiplicities and recursion
    charges, conditional only on the uniform schedules and the critical-line input. -/
theorem factor_from_relation_schedules (line : DirichletLZerosOnLine)
    (schedules : (n : ℕ) → 2 ≤ n → RelationSchedule n) :
    ∃ (k : ℕ) (gen : ∀ n, 2 ≤ n →
      generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1)))),
    ∀ (n : ℕ) (hn : 2 ≤ n) (charge : ℕ → ℕ) (cap : ℕ),
      (∀ a, 2 ≤ a → a ≤ n → charge a ≤ cap) →
      let tree := factor (fun a ha => scheduleDecision ha (schedules a ha) _ (gen a ha)) n hn
      tree.factors.prod = n ∧ (∀ p ∈ tree.factors, p.Prime) ∧
      (∀ p, p.Prime → ∀ j, p^j ∣ n ↔ j ≤ tree.factors.count p) ∧
      tree.work charge ≤ (2*n.log2-1)*cap := by
  obtain ⟨k,allGen⟩ := polynomial_generators_from_critical_line line
  have gen (n : ℕ) (hn : 2 ≤ n) : generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1))) := by
    have : NeZero n := ⟨by omega⟩
    exact allGen n _ Nat.lt_log2_self
  refine ⟨k, gen, fun n hn charge cap hcap => ?_⟩
  obtain ⟨prod,primes,mult,cost⟩ := factor_correct_and_cost
    (fun a ha => scheduleDecision ha (schedules a ha) _ (gen a ha)) n hn charge cap hcap
  exact ⟨prod, fun p hp => Nat.prime_def.mpr (primes p hp),
    fun p hp => mult p (Nat.prime_def.mp hp), cost⟩

/-- Qualitative end-to-end factoring from the large-input four-coordinate
    coverage premise. The finite exceptional sizes are handled by trial division. -/
theorem factor_from_dyadic_boxes (line : DirichletLZerosOnLine) (s : ℕ → BoxParameters)
    (grows : ∀ b : ℕ, ∃ n₀, ∀ n ≥ n₀, b ≤ (s n).beta)
    (boxes : ∃ n₀ : ℕ, ∀ n ≥ n₀, (s n).Covers n) :
    ∃ (threshold k : ℕ) (schedules : (n : ℕ) → 2 ≤ n → RelationSchedule n)
      (gen : ∀ n, 2 ≤ n → generatesUnits n (List.range' 1 (polyCutoff k (n.log2+1)))),
      (∀ n (hn : 2 ≤ n), threshold ≤ n → (schedules n hn).parameters = s n ∧
        (schedules n hn).candidates = (dyadicTargets (s n).beta).sort) ∧
      ∀ (n : ℕ) (hn : 2 ≤ n) (charge : ℕ → ℕ) (cap : ℕ),
        (∀ a, 2 ≤ a → a ≤ n → charge a ≤ cap) →
        let tree := factor (fun a ha => scheduleDecision ha (schedules a ha) _ (gen a ha)) n hn
        tree.factors.prod = n ∧ (∀ p ∈ tree.factors, p.Prime) ∧
        (∀ p, p.Prime → ∀ j, p^j ∣ n ↔ j ≤ tree.factors.count p) ∧
        tree.work charge ≤ (2*n.log2-1)*cap := by
  obtain ⟨threshold,schedules,large⟩ := schedules_from_dyadic_boxes line s grows boxes
  obtain ⟨k,gen,correct⟩ := factor_from_relation_schedules line schedules
  exact ⟨threshold,k,schedules,gen,large,correct⟩

end Cogentic

#print axioms Cogentic.factor_from_relation_schedules
#print axioms Cogentic.factor_from_dyadic_boxes
#print axioms Cogentic.search_saturated_size
