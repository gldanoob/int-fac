import TwoThirdsFinish
import Cogentic.SearchSaturation
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Algebra.Group.Prod
import Mathlib.Tactic

namespace Cogentic

open TwoThirdsFinish

private abbrev PairUnits (p q : ℕ) := (ZMod p)ˣ × (ZMod q)ˣ

private def diagonalSigns (p q : ℕ) : Subgroup (PairUnits p q) where
  carrier := {x | x = 1 ∨ x = (-1,-1)}
  one_mem' := Or.inl rfl
  mul_mem' := by rintro x y (rfl | rfl) (rfl | rfl) <;> simp [Prod.mul_def]
  inv_mem' := by rintro x (rfl | rfl) <;> simp

private theorem unit_sign {p : ℕ} [Fact p.Prime] {x : (ZMod p)ˣ}
    (hx : x^2 = 1) : x = 1 ∨ x = -1 := by
  have sq : (x : ZMod p)^2 = 1 := congrArg Units.val hx
  rcases sq_eq_one_iff.mp sq with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext h)

private theorem neg_one_ne {p : ℕ} (hp : 2 < p) : (-1 : (ZMod p)ˣ) ≠ 1 := by
  intro h
  have eq : (-1 : ZMod p) = 1 := congrArg Units.val h
  have eq2 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination -eq
  exact (not_le.mpr hp) (Nat.le_of_dvd (by decide) ((ZMod.natCast_eq_zero_iff ..).mp eq2))

private theorem primitive_unit {p : ℕ} [Fact p.Prime] :
    ∃ x : (ZMod p)ˣ, orderOf x = p-1 := by
  simpa only [Nat.card_eq_fintype_card, ZMod.card_units] using
    (IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ))

private theorem diagonal_proper {p q t : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : 2 < p) (hq : 2 < q) (half : ¬ (p-1 ∣ t ∧ q-1 ∣ t)) :
    (diagonalSigns p q).comap (powMonoidHom t) ≠ ⊤ := by
  intro top
  have every (x : PairUnits p q) : x^t = 1 ∨ x^t = (-1,-1) :=
    show x ∈ (diagonalSigns p q).comap (powMonoidHom t) from top ▸ Subgroup.mem_top _
  apply half
  constructor
  · obtain ⟨a,ha⟩ := primitive_unit (p := p)
    rcases every (a,1) with h | h
    · rw [← ha]; exact orderOf_dvd_of_pow_eq_one (congrArg Prod.fst h)
    · have bad : (1 : (ZMod q)ˣ) = -1 := by simpa using congrArg Prod.snd h
      exact False.elim (neg_one_ne hq bad.symm)
  · obtain ⟨a,ha⟩ := primitive_unit (p := q)
    rcases every (1,a) with h | h
    · rw [← ha]; exact orderOf_dvd_of_pow_eq_one (congrArg Prod.snd h)
    · have bad : (1 : (ZMod p)ˣ) = -1 := by simpa using congrArg Prod.fst h
      exact False.elim (neg_one_ne hp bad.symm)

/-- In any generating family modulo two odd primes, some base has distinct
    signs at the half-lcm power. The subgroup of diagonal signs is proper. -/
theorem generating_pair_splits {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : 2 < p) (hq : 2 < q) (S : Set (PairUnits p q)) (gen : Subgroup.closure S = ⊤) :
    let t := (p-1).lcm (q-1) / 2
    ∃ x ∈ S, (x.1^t = 1 ∧ x.2^t ≠ 1) ∨ (x.2^t = 1 ∧ x.1^t ≠ 1) := by
  let l := (p-1).lcm (q-1)
  let t := l/2
  have ep := (Nat.Prime.odd_of_ne_two (Fact.out : p.Prime) (by omega))
  have ed : 2 ∣ p-1 := by obtain ⟨k,h⟩ := ep; exact ⟨k,by omega⟩
  have el := Nat.dvd_trans ed (Nat.dvd_lcm_left (p-1) (q-1))
  have pos : 0 < l := Nat.lcm_pos (by omega) (by omega)
  have twice : t*2 = l := Nat.div_mul_cancel el
  have half : ¬ (p-1 ∣ t ∧ q-1 ∣ t) := by
    rintro ⟨h1,h2⟩
    have hl : l ∣ t := Nat.lcm_dvd h1 h2
    exact (not_le.mpr (show t < l by dsimp [t]; omega)) (Nat.le_of_dvd (by omega) hl)
  by_contra missing
  apply diagonal_proper hp hq half
  apply top_unique
  rw [← gen, Subgroup.closure_le]
  intro x hx
  have sq₁ : (x.1^t)^2 = 1 := by
    rw [← pow_mul, twice]
    exact orderOf_dvd_iff_pow_eq_one.mp ((ZMod.orderOf_units_dvd_card_sub_one _).trans (Nat.dvd_lcm_left ..))
  have sq₂ : (x.2^t)^2 = 1 := by
    rw [← pow_mul, twice]
    exact orderOf_dvd_iff_pow_eq_one.mp ((ZMod.orderOf_units_dvd_card_sub_one _).trans (Nat.dvd_lcm_right ..))
  have hnot : ¬((x.1^t = 1 ∧ x.2^t ≠ 1) ∨ (x.2^t = 1 ∧ x.1^t ≠ 1)) :=
    fun h => missing ⟨x,hx,h⟩
  change x^t = 1 ∨ x^t = (-1,-1)
  rcases unit_sign sq₁ with h1 | h1 <;> rcases unit_sign sq₂ with h2 | h2
  · exact Or.inl (Prod.ext h1 h2)
  · exact False.elim (hnot (.inl ⟨h1, h2 ▸ neg_one_ne hq⟩))
  · exact False.elim (hnot (.inr ⟨h2, h1 ▸ neg_one_ne hp⟩))
  · exact Or.inr (Prod.ext h1 h2)

private theorem separated_orders {a b t : ℕ} (ap : 0 < a) (bp : 0 < b)
    (at' : a ∣ t) (bt : b ∣ 2*t) (bn : ¬ b ∣ t) :
    (stripTwos a).1 < (stripTwos b).1 := by
  have ⟨_,ea⟩ := stripTwos_spec a ap
  obtain ⟨odd,eb⟩ := stripTwos_spec b bp
  have cop : (stripTwos b).2.Coprime 2 := by
    show (stripTwos b).2.gcd 2 = 1
    rw [Nat.gcd_comm, Nat.gcd_rec, odd]
    decide
  have oddD : (stripTwos b).2 ∣ b :=
    (Nat.dvd_mul_right _ _).trans (dvd_of_eq eb)
  have oddT := cop.dvd_of_dvd_mul_left (oddD.trans bt)
  have powerD : 2^(stripTwos a).1 ∣ a :=
    (Nat.dvd_mul_left _ _).trans (dvd_of_eq ea)
  by_contra! h
  have powerT := (Nat.pow_dvd_pow 2 h).trans (powerD.trans at')
  exact bn ((dvd_of_eq eb.symm).trans ((cop.pow_right _).mul_dvd_of_dvd_of_dvd oddT powerT))

theorem powMod_order {g p : ℕ} [Fact p.Prime] (a : (ZMod p)ˣ) (hg : (a : ZMod p) = g)
    (e : ℕ) : ModularPower.powMod g e p = 1 ↔ orderOf a ∣ e := by
  rw [orderOf_dvd_iff_pow_eq_one, ← Units.val_inj, Units.val_one, Units.val_pow_eq_pow_val, hg,
    ← Nat.cast_pow]
  rw [← (Nat.cast_one : ((1 : ℕ) : ZMod p) = 1), ZMod.natCast_eq_natCast_iff', ModularPower.powMod_def,
    Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt]

private theorem half_separates {n m p q g t : ℕ} {gs : List ℕ} [Fact p.Prime] [Fact q.Prime]
    (hg : g ∈ gs) (hm : 2 ≤ m) (pn : p ∣ n) (qn : q ∣ n) (pm : p-1 ∣ m) (qm : q-1 ∣ m)
    (qt : q-1 ∣ 2*t) (a : (ZMod p)ˣ) (b : (ZMod q)ˣ) (ap : (a : ZMod p) = g) (bq : (b : ZMod q) = g)
    (ha : a^t = 1) (hb : b^t ≠ 1) : Separates n m gs := by
  have pa := ZMod.orderOf_units_dvd_card_sub_one a
  have qb := ZMod.orderOf_units_dvd_card_sub_one b
  have lt := separated_orders (orderOf_pos a) (orderOf_pos b) (orderOf_dvd_of_pow_eq_one ha)
    (qb.trans qt) (fun d => hb (orderOf_dvd_iff_pow_eq_one.mp d))
  have ⟨oddA,ea⟩ := stripTwos_spec _ (orderOf_pos a)
  have eb := (stripTwos_spec _ (orderOf_pos b)).2
  apply separates_of_local_orders hg hm ((powMod_order a ap m).mpr (pa.trans pm))
    ((powMod_order b bq m).mpr (qb.trans qm)) (Fact.out : p.Prime).one_lt
    (Fact.out : q.Prime).one_lt pn qn oddA lt
  · intro e; rw [ea]; exact powMod_order a ap e
  · intro e; rw [eb]; exact powMod_order b bq e

/-- The subgroup generated by the listed natural bases, discarding nonunits. -/
def generatesUnits (n : ℕ) (gs : List ℕ) : Prop :=
  Subgroup.closure {x : (ZMod n)ˣ | ∃ g ∈ gs, (x : ZMod n) = g} = ⊤

/-- A common multiple of p-1 and q-1 splits N using *any* generating list of units mod N.
    The CRT, primitive roots and the two unknown primes occur only in the proof. -/
theorem saturated_splitter {n m p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hn : 2 ≤ n)
    (hm : 2 ≤ m) (hp : 2 < p) (hq : 2 < q) (neq : p ≠ q) (pn : p ∣ n) (qn : q ∣ n)
    (pm : p-1 ∣ m) (qm : q-1 ∣ m) (gs : List ℕ) (gen : generatesUnits n gs) :
    splitWithExponent n m gs ≠ none := by
  have : NeZero n := ⟨by omega⟩
  have cop := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (fun h => neq (((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : q.Prime)).mp h)))
  have pqn := cop.mul_dvd_of_dvd_of_dvd pn qn
  let crt := (Units.mapEquiv (ZMod.chineseRemainder cop).toMulEquiv).trans MulEquiv.prodUnits
  let f : (ZMod n)ˣ →* PairUnits p q := crt.toMonoidHom.comp (ZMod.unitsMap pqn)
  have onto : Function.Surjective f := crt.surjective.comp (ZMod.unitsMap_surjective pqn)
  let S := {x : (ZMod n)ˣ | ∃ g ∈ gs, (x : ZMod n) = g}
  have imageGen : Subgroup.closure (f '' S) = ⊤ := by
    rw [← MonoidHom.map_closure, show Subgroup.closure S = ⊤ from gen,
      Subgroup.map_top_of_surjective _ onto]
  obtain ⟨_,⟨x,⟨g,hg,xg⟩,rfl⟩,diff⟩ := generating_pair_splits hp hq (f '' S) imageGen
  have xcast : (((f x).1 : ZMod p), ((f x).2 : ZMod q)) = ((g : ZMod p), (g : ZMod q)) := by
    change ZMod.chineseRemainder cop ((ZMod.castHom pqn (ZMod (p*q))) (x : ZMod n)) = _
    rw [xg, map_natCast, map_natCast]
    rfl
  let l := (p-1).lcm (q-1)
  have ep := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have ed : 2 ∣ p-1 := by obtain ⟨k,h⟩ := ep; exact ⟨k,by omega⟩
  have twice : 2*(l/2) = l := Nat.mul_div_cancel' (ed.trans (Nat.dvd_lcm_left ..))
  apply chain_hits hn
  rcases diff with h | h
  · exact half_separates hg hm pn qn pm qm (twice ▸ Nat.dvd_lcm_right ..)
      _ _ (congrArg Prod.fst xcast) (congrArg Prod.snd xcast) h.1 h.2
  · exact half_separates hg hm qn pn qm pm (twice ▸ Nat.dvd_lcm_left ..)
      _ _ (congrArg Prod.snd xcast) (congrArg Prod.fst xcast) h.1 h.2

def smallBases (bits : ℕ) : List ℕ := List.range' 1 (3*bits^2)

/-- The subgroup-omission consequence of Bach, with an integer bit-length cutoff. -/
def SmallSubgroupWitness (n bits : ℕ) : Prop :=
  ∀ H : Subgroup (ZMod n)ˣ, H ≠ ⊤ → ∃ a, 1 ≤ a ∧ a ≤ 3*bits^2 ∧
    ∃ cop : a.Coprime n, ZMod.unitOfCoprime a cop ∉ H

theorem small_bases_generate {n bits : ℕ} (supply : SmallSubgroupWitness n bits) :
    generatesUnits n (smallBases bits) := by
  by_contra h
  obtain ⟨a,lo,hi,cop,out⟩ := supply _ h
  apply out
  apply Subgroup.subset_closure
  exact ⟨a,List.mem_range'_1.mpr ⟨lo,by omega⟩,ZMod.coe_unitOfCoprime _ _⟩

/-- Saturation and the bounded-base gcd scan need only the actual retained prime
    certificates, the integer count guard and the small-subgroup witness theorem. -/
theorem collected_saturated_splitter {n e β bits p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hn : 2 ≤ n) (length : n < 2^bits) (beta : 0 < β) (big : 2 ≤ e)
    (hp : 2 < p) (hq : 2 < q) (neq : p ≠ q) (pn : p ∣ n) (qn : q ∣ n)
    (retained : List ℕ) (primes : ∀ a ∈ retained, Nat.Prime a)
    (bound : ∀ a ∈ retained, a ≤ 2^β) (accept : 2^β ≤ 3*β*retained.toFinset.card)
    (checked : ∀ a ∈ retained, ModularPower.powMod a e n = 1)
    (supply : SmallSubgroupWitness n bits) :
    splitWithExponent n (saturate e bits β) (smallBases bits) ≠ none := by
  have pos : 0 < (Finset.Icc 1 (indexCap bits β)).lcm id := Nat.pos_of_ne_zero
    (Finset.lcm_ne_zero_iff.mpr (fun x hx => by have := (Finset.mem_Icc.mp hx).1; exact Nat.ne_of_gt this))
  apply saturated_splitter hn (big.trans (Nat.le_mul_of_pos_right _ pos)) hp hq neq pn qn
    (collected_orders_saturate retained hn length beta big primes bound accept checked Fact.out pn)
    (collected_orders_saturate retained hn length beta big primes bound accept checked Fact.out qn)
    _ (small_bases_generate supply)

end Cogentic

#print axioms Cogentic.saturated_splitter
#print axioms Cogentic.collected_saturated_splitter
