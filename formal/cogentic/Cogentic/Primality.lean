import Cogentic.Splitter
import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
import Mathlib.Data.Nat.Factorization.PrimePow

namespace Cogentic

open TwoThirdsFinish ArithmeticFunction

/-- Fermat checks on the unit bases and the gcd square chain for exponent n−1. -/
def primeCheck (n : ℕ) (gs : List ℕ) : Bool :=
  n == 2 || (decide (2 < n) && n % 2 == 1 &&
    gs.all (fun g => decide (g.Coprime n → ModularPower.powMod g (n-1) n = 1)) &&
    (splitWithExponent n (n-1) gs).isNone)

private theorem checked_exponent {n : ℕ} (hn : 2 < n) (gs : List ℕ) (gen : generatesUnits n gs)
    (checked : ∀ g ∈ gs, g.Coprime n → ModularPower.powMod g (n-1) n = 1) :
    carmichael n ∣ n-1 := by
  rw [carmichael_eq_exponent (by omega), Monoid.exponent_dvd_iff_forall_pow_eq_one]
  let f := powMonoidHom (α := (ZMod n)ˣ) (n-1)
  have all : (⊤ : Subgroup (ZMod n)ˣ) ≤ f.ker := by
    rw [← gen, Subgroup.closure_le]
    rintro x ⟨g,hg,xg⟩
    have cop := (ZMod.isUnit_iff_coprime g n).mp (xg ▸ x.isUnit)
    apply Units.ext
    change (↑x : ZMod n)^(n-1) = 1
    rw [xg]
    have h := congrArg (fun k : ℕ => (k : ZMod n)) (checked g hg cop)
    simpa [ModularPower.powMod_def] using h
  exact fun x => all (Subgroup.mem_top x)

private theorem odd_prime_factor {n p : ℕ} (odd : n % 2 = 1) (hp : p.Prime) (pn : p ∣ n) :
    2 < p := by
  have pos := hp.two_le
  by_contra! small
  have peq : p = 2 := by omega
  subst p
  have := Nat.dvd_iff_mod_eq_zero.mp pn
  omega

private theorem prime_of_primePower {n : ℕ} (hn : 2 < n) (odd : n % 2 = 1)
    (power : IsPrimePow n) (all : carmichael n ∣ n-1) : n.Prime := by
  obtain ⟨p,k,hp,hk,eq⟩ := (isPrimePow_nat_iff n).mp power
  have pn : p ∣ n := eq ▸ (dvd_pow_self p (by omega : k ≠ 0))
  have large := odd_prime_factor odd hp pn
  by_cases one : k = 1
  · simpa [← eq, one] using hp
  · have pk : p^2 ∣ n := eq ▸ Nat.pow_dvd_pow p (by omega)
    have sub := (carmichael_dvd pk).trans all
    rw [carmichael_pow_of_prime_ne_two 2 hp (by omega), Nat.totient_prime_pow_succ hp 1,
      pow_one] at sub
    have both := (Nat.dvd_mul_right p (p-1)).trans sub
    have := (Nat.dvd_sub_iff_right (by omega : 1 ≤ n) pn).mp both
    exact False.elim (hp.not_dvd_one this)

/-- With a generating list, the executable test recognizes every prime and rejects every composite,
    including prime powers. -/
theorem primeCheck_correct (n : ℕ) (gs : List ℕ) (gen : generatesUnits n gs) :
    primeCheck n gs = true ↔ n.Prime := by
  by_cases two : n = 2
  · simp [primeCheck, two, Nat.prime_two]
  simp only [primeCheck, beq_iff_eq, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Option.isNone_iff_eq_none, two, false_or]
  constructor
  · rintro ⟨⟨⟨hn,odd⟩,fermat⟩,scan⟩
    have all := checked_exponent hn gs gen fermat
    by_cases hpow : IsPrimePow n
    · exact prime_of_primePower hn odd hpow all
    · obtain ⟨p,hp,q,hq,neq⟩ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le (by omega)).mp hpow
      have ⟨pp,pn,_⟩ := Nat.mem_primeFactors.mp hp
      have ⟨qp,qn,_⟩ := Nat.mem_primeFactors.mp hq
      have : Fact p.Prime := ⟨pp⟩
      have : Fact q.Prime := ⟨qp⟩
      have localDvd (r : ℕ) (pr : r.Prime) (rn : r ∣ n) : r-1 ∣ n-1 := by
        have hr := odd_prime_factor odd pr rn
        have eq : carmichael r = r-1 := by
          simpa [Nat.totient_prime pr] using carmichael_pow_of_prime_ne_two 1 pr (by omega)
        exact eq ▸ (carmichael_dvd rn).trans all
      exact False.elim ((saturated_splitter (by omega) (by omega)
        (odd_prime_factor odd pp pn) (odd_prime_factor odd qp qn) neq pn qn
        (localDvd p pp pn) (localDvd q qp qn) gs gen) scan)
  · intro hp
    have hn := hp.two_le
    have odd := hp.odd_of_ne_two two
    have : Fact n.Prime := ⟨hp⟩
    refine ⟨⟨⟨by omega, by obtain ⟨k,hk⟩ := odd; omega⟩,?_⟩,?_⟩
    · intro g hg cg
      exact (powMod_order (ZMod.unitOfCoprime g cg) (ZMod.coe_unitOfCoprime _ _) _).mpr
        (ZMod.orderOf_units_dvd_card_sub_one _)
    · cases he : splitWithExponent n (n-1) gs with
      | none => rfl
      | some d => exact False.elim ((Nat.prime_def_lt'.mp hp).2 _ d.property.1 d.property.2.1 d.property.2.2)

theorem bounded_primeCheck {n bits : ℕ} (supply : SmallSubgroupWitness n bits) :
    primeCheck n (smallBases bits) = true ↔ n.Prime :=
  primeCheck_correct _ _ (small_bases_generate supply)

theorem bounded_primeCheck_driver {n bits : ℕ} (supply : SmallSubgroupWitness n bits) :
    primeCheck n (smallBases bits) = true ↔ TwoThirdsFactor.IsPrime n :=
  (bounded_primeCheck supply).trans Nat.prime_def

/-- Budget for all scheduled bases before early exits: the unit gcd, both modular
    powers, and at most one halving, gcd and modular squaring per square-chain step. -/
def primalityListBudget (n : ℕ) (bases : List ℕ) : ℕ :=
  let m := n-1
  let t := stripTwos m
  bases.length * (1 + ModularPower.multiplyCount m + ModularPower.multiplyCount t.2 + 3*t.1)

theorem primality_list_budget {n bits : ℕ} (hn : 2 ≤ n) (fits : n < 2^bits) (bases : List ℕ) :
    primalityListBudget n bases ≤ bases.length * (7*bits+1) := by
  let m := n-1
  have hm : 0 < m := by dsimp [m]; omega
  have small : m < 2^bits := (Nat.sub_le n 1).trans_lt fits
  have ⟨_,eq⟩ := stripTwos_spec m hm
  have a : (stripTwos m).2 ≤ m :=
    Nat.le_of_dvd hm ((Nat.dvd_mul_right _ _).trans (dvd_of_eq eq))
  have b : 2^(stripTwos m).1 ≤ m :=
    Nat.le_of_dvd hm ((Nat.dvd_mul_left _ _).trans (dvd_of_eq eq))
  have rounds := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (b.trans_lt small)
  have left := ModularPower.multiplyCount_le small
  have right := ModularPower.multiplyCount_le (a.trans_lt small)
  unfold primalityListBudget
  apply Nat.mul_le_mul_left
  change 1 + ModularPower.multiplyCount m + ModularPower.multiplyCount (stripTwos m).2 + 3*(stripTwos m).1 ≤ _
  omega

theorem primality_arithmetic_budget {n bits : ℕ} (hn : 2 ≤ n) (fits : n < 2^bits) :
    primalityListBudget n (smallBases bits) ≤ 3*bits^2 * (7*bits+1) := by
  simpa [smallBases] using primality_list_budget hn fits (smallBases bits)

end Cogentic

#print axioms Cogentic.bounded_primeCheck
#print axioms Cogentic.primality_arithmetic_budget
