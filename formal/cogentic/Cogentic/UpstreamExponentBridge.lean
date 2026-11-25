import Cogentic.SplitterCost
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Cogentic
open Real TwoThirdsSearch TwoThirdsFinish BinaryDivision BinarySplitter

/-- The output-width bound in Theorem 1.3 of the deterministic companion
fits the exponent input of our two-thirds-scale Boolean splitter. -/
theorem companion_exponent_width {n m : ℕ} (hn : 2 ≤ n)
    (width : log m ≤ exp ((log n)^(13/20:ℝ))) :
    let b := n.log2+1
    m.size ≤ 2^(2017*TwoThirdsCost.scale b)+1 := by
  let b := n.log2+1
  let s := TwoThirdsCost.scale b
  have bp : 0<b := Nat.succ_pos _
  have sp : 0<s := Nat.two_pow_pos _
  have ns : (n:ℝ) ≤ (2:ℝ)^b := by exact_mod_cast (Nat.lt_log2_self (n:=n)).le
  have lv : log (n:ℝ) ≤ b := by
    have l := log_le_log (by positivity) ns
    rw [log_pow] at l
    have h := mul_le_mul_of_nonneg_left (show log (2:ℝ) ≤ 1 by linarith [log_two_lt_d9]) (Nat.cast_nonneg (α:=ℝ) b)
    linarith only [l,h]
  have c : b^2 ≤ s^3 :=
    (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans (TwoThirdsCost.scale_cubed b bp.ne').1
  have b1 : (1:ℝ) ≤ b := by exact_mod_cast bp
  have powle : (b:ℝ)^(2/3:ℝ) ≤ s := by
    apply (pow_le_pow_iff_left₀ (rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg (α:=ℝ) s) (by decide : (3:ℕ) ≠ 0)).mp
    rw [←rpow_mul_natCast (Nat.cast_nonneg (α:=ℝ) b)]
    norm_num
    exact_mod_cast c
  have expo : (log n)^(13/20:ℝ) ≤ s :=
    ((rpow_le_rpow (log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))) lv (by norm_num)).trans
      (rpow_le_rpow_of_exponent_le b1 (by norm_num : (13/20:ℝ) ≤ 2/3))).trans powle
  have half : (1/2:ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
  have grow : exp (s:ℝ) ≤ (2:ℝ)^(2*s) := by
    rw [←Real.log_le_log_iff (exp_pos _) (by positivity),log_exp,log_pow]
    push_cast
    linarith only [mul_le_mul_of_nonneg_right half (Nat.cast_nonneg (α:=ℝ) s)]
  have logbits := Real.log2_le_logb m
  rw [Real.logb] at logbits
  have logcap : (m.log2:ℝ) ≤ 2*(2:ℝ)^(2*s) := by
    apply logbits.trans
    rw [div_le_iff₀ (log_pos (by norm_num : (1:ℝ)<2))]
    have mcap := width.trans ((exp_le_exp.mpr expo).trans grow)
    linarith only [mcap,mul_le_mul_of_nonneg_left half (show 0 ≤ 2*(2:ℝ)^(2*s) by positivity)]
  have cb : m.log2 ≤ 2*2^(2*s) := by exact_mod_cast logcap
  have en : 2*2^(2*s) ≤ 2^(2017*s) := by
    rw [mul_comm 2,←Nat.pow_succ]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  exact (Nat.size_le.mpr Nat.lt_log2_self).trans (Nat.add_le_add_right (cb.trans en) 1)

/-- Consume either a verified divisor or a common exponent, as returned by
the deterministic companion's exponent algorithm. A direct divisor is
already in binary and can be forwarded without arithmetic gates. -/
def finishExponentOutput (k n : ℕ) : (List Bool ⊕ ℕ) → Option (List Bool) × ℕ
  | .inl d => (some d,0)
  | .inr m => BinarySplitter.splitter n m (List.range' 1 (polyCutoff k (n.log2+1)))

/-- Both alternatives of the companion's Theorem 1.3 feed our concrete
splitter. The budget counts postprocessing of the supplied output. -/
theorem finish_companion_output (line : DirichletLZerosOnLine) :
    ∃ k : ℕ, ∀ {n : ℕ}, let b := n.log2+1
      k ≤ b → 9 ≤ n → ¬2 ∣ n → ¬n.Prime → (∀ x j : ℕ, 2 ≤ x → 2 ≤ j → x^j ≠ n) →
      ∀ result : List Bool ⊕ ℕ,
      (match result with
        | .inl d => ProperDivisor n (value d)
        | .inr m => 2 ≤ m ∧ Even m ∧ (∀ p : ℕ, p.Prime → p ∣ n → p-1 ∣ m) ∧
          log m ≤ exp ((log n)^(13/20:ℝ))) →
      let out := finishExponentOutput k n result
      (∃ bits, out.1=some bits ∧ ProperDivisor n (value bits)) ∧
        out.2 ≤ 2^(10102*TwoThirdsCost.scale b) := by
  obtain ⟨k,bases⟩ := polynomial_generators_from_critical_line line
  refine ⟨k,?_⟩
  intro n b large nine odd composite nonpower result allowed out
  cases result with
  | inl d => exact ⟨⟨d,rfl,allowed⟩,Nat.zero_le _⟩
  | inr m =>
    obtain ⟨hm,_,annihilates,width⟩ := allowed
    have hn : 2 ≤ n := by omega
    have : NeZero n := ⟨by omega⟩
    have npp : ¬IsPrimePow n := by
      intro power
      obtain ⟨p,j,prime,jp,eq⟩ := (isPrimePow_nat_iff n).mp power
      have two : 2 ≤ j := by
        by_contra! h
        exact composite (by simpa only [←eq,show j=1 by omega,pow_one] using prime)
      exact nonpower p j prime.two_le two eq
    obtain ⟨p,pm,q,qm,neq⟩ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le hn).mp npp
    obtain ⟨pp,pn,_⟩ := Nat.mem_primeFactors.mp pm
    obtain ⟨qp,qn,_⟩ := Nat.mem_primeFactors.mp qm
    have : Fact p.Prime := ⟨pp⟩
    have : Fact q.Prime := ⟨qp⟩
    have gt (r : ℕ) (prime : r.Prime) (div : r ∣ n) : 2<r :=
      lt_of_le_of_ne prime.two_le (fun eq => odd (eq ▸ div))
    let cap := polyCutoff k b
    let gs := List.range' 1 cap
    let E := 2^(2017*TwoThirdsCost.scale b)+1
    have success := saturated_splitter hn hm (gt p pp pn) (gt q qp qn) neq pn qn
      (annihilates p pp pn) (annihilates q qp qn) gs (bases n b Nat.lt_log2_self)
    have hw {g : ℕ} (hg : g∈gs) : g.size ≤ cap.size := by
      have hi := (List.mem_range'_1.mp hg).2
      exact Nat.size_le_size (by omega : g ≤ cap)
    obtain ⟨val,cost⟩ := splitter_spec n m cap.size gs (by omega) (by omega) (fun g hg=>hw hg)
    change (∃ bits, (splitter n m gs).1=some bits ∧ ProperDivisor n (value bits)) ∧ _
    constructor
    · obtain ⟨d,hd⟩ := Option.ne_none_iff_exists'.mp success
      rw [hd,Option.map_some] at val
      cases h : (splitter n m gs).1 with
      | none => simp [h] at val
      | some bits =>
        refine ⟨bits,rfl,?_⟩
        simp only [h,Option.map_some,Option.some.injEq] at val
        exact val.symm ▸ d.property
    · have ew : m.size ≤ E := companion_exponent_width hn width
      have nw : n.size ≤ b := Nat.size_le.mpr Nat.lt_log2_self
      have bound : baseBudget cap.size m.size n.size ≤ baseBudget cap.size E b := by
        unfold baseBudget scanStepBudget BinaryModularPower.powerBudget BinaryModularPower.gcdBudget
        gcongr
      have len : gs.length=cap := by simp [gs]
      rw [len] at cost
      exact (cost.trans (Nat.add_le_add ew (Nat.mul_le_mul_left cap (Nat.add_le_add_right bound 1)))).trans
        (driver_budgets_scale b k (Nat.succ_pos _) large).2

end Cogentic

#print axioms Cogentic.companion_exponent_width
#print axioms Cogentic.finish_companion_output
