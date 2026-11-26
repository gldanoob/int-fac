import Cogentic.RandomizedSignCount
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.FieldTheory.Finite.Basic

namespace Cogentic.RandomizedCRTSigns

open RandomizedSignCount

private theorem eq_one_or_neg_one {p e : ℕ} (hp : p.Prime) (hodd : Odd p)
    (x : ZMod (p ^ e)) (hx : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  let : Fact p.Prime := ⟨hp⟩
  have htwo : Nat.Coprime 2 (p ^ e) := (Nat.coprime_two_left.mpr hodd).pow_right e
  have horder : (orderOf x).Coprime (p ^ e) :=
    htwo.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hx)
  rcases ZMod.eq_one_or_isUnit_sub_one rfl x horder with h | h
  · exact Or.inl h
  · have hz : (x - 1) * (x + 1) = 0 := by
      calc
        (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
        _ = 0 := by rw [hx, sub_self]
    exact Or.inr (eq_neg_iff_add_eq_zero.mpr (h.mul_left_cancel (hz.trans (mul_zero _).symm)))

/-- The two square roots of one at an odd prime power, with true for +1. -/
noncomputable def primePowerSigns {p e : ℕ} (hp : p.Prime) (hodd : Odd p) (he : 0 < e) :
    SquareFiber (1 : (ZMod (p ^ e))ˣ) ≃ Bool := by
  classical
  have hp3 : 2 < p := by
    rcases hodd with ⟨q, hq⟩
    have := hp.two_le
    omega
  have hmod : 2 < p ^ e := hp3.trans_le (Nat.le_pow he)
  letI : Fact (2 < p ^ e) := ⟨hmod⟩
  have distinct : (-1 : (ZMod (p ^ e))ˣ) ≠ 1 := fun h =>
    ZMod.neg_one_ne_one (congrArg (fun u : (ZMod (p ^ e))ˣ => (u : ZMod (p ^ e))) h)
  refine {
    toFun := fun x => decide (x.val = 1)
    invFun := fun b => ⟨if b then 1 else -1, by cases b <;> simp⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro x
    have hx : (x.val : ZMod (p ^ e)) ^ 2 = 1 := by
      simpa using congrArg (fun u : (ZMod (p ^ e))ˣ => (u : ZMod (p ^ e))) x.property
    apply Subtype.ext
    rcases eq_one_or_neg_one hp hodd _ hx with h | h
    · have hu : x.val = 1 := Units.ext h
      simp [hu]
    · have hu : x.val = -1 := Units.ext h
      simp [hu, distinct]
  · intro b
    cases b <;> simp [distinct]

@[simp] theorem primePowerSigns_true {p e : ℕ} (hp : p.Prime) (hodd : Odd p) (he : 0 < e)
    (x : SquareFiber (1 : (ZMod (p ^ e))ˣ)) :
    primePowerSigns hp hodd he x = true ↔ x.val = 1 := by
  classical
  change decide (x.val = 1) = true ↔ x.val = 1
  simp

private def squareFiberCongr {A B : Type*} [CommGroup A] [CommGroup B] (e : A ≃* B) :
    SquareFiber (1 : A) ≃ SquareFiber (1 : B) where
  toFun x := ⟨e x.val, by simpa using congrArg e x.property⟩
  invFun y := ⟨e.symm y.val, by simpa using congrArg e.symm y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)

private def squareFiberPi {I : Type*} (A : I → Type*) [∀ i, CommGroup (A i)] :
    SquareFiber (1 : ∀ i, A i) ≃ (∀ i, SquareFiber (1 : A i)) where
  toFun x i := ⟨x.val i, by simpa using congrFun x.property i⟩
  invFun y := ⟨fun i => (y i).val, funext fun i => by simpa using (y i).property⟩
  left_inv x := Subtype.ext rfl
  right_inv y := funext fun i => Subtype.ext rfl

/-- The CRT sign cube in product-ring coordinates. -/
noncomputable def productSigns {k : ℕ} (p e : Fin k → ℕ) (hp : ∀ i, (p i).Prime)
    (hodd : ∀ i, Odd (p i)) (he : ∀ i, 0 < e i) :
    SquareFiber (1 : (∀ i, ZMod (p i ^ e i))ˣ) ≃ SignCube k :=
  (squareFiberCongr MulEquiv.piUnits).trans <|
    (squareFiberPi _).trans <| Equiv.piCongrRight fun i => primePowerSigns (hp i) (hodd i) (he i)

theorem productSigns_true {k : ℕ} (p e : Fin k → ℕ) (hp : ∀ i, (p i).Prime)
    (hodd : ∀ i, Odd (p i)) (he : ∀ i, 0 < e i)
    (x : SquareFiber (1 : (∀ i, ZMod (p i ^ e i))ˣ)) (i : Fin k) :
    productSigns p e hp hodd he x i = true ↔ (x.val : ∀ j, ZMod (p j ^ e j)) i = 1 := by
  change primePowerSigns (hp i) (hodd i) (he i)
    (squareFiberPi _ (squareFiberCongr MulEquiv.piUnits x) i) = true ↔ _
  rw [primePowerSigns_true]
  exact Units.ext_iff

/-- Simultaneous reduction modulo a finite family of pairwise coprime moduli. -/
noncomputable def zmodCRT {k : ℕ} (m : Fin k → ℕ) (hn : ∀ i, m i ≠ 0)
    (hc : Pairwise fun i j => (m i).Coprime (m j)) :
    ZMod (∏ i, m i) ≃+* ∀ i, ZMod (m i) := by
  classical
  letI : ∀ i, NeZero (m i) := fun i => ⟨hn i⟩
  letI : NeZero (∏ i, m i) := ⟨Finset.prod_ne_zero_iff.mpr fun i _ => hn i⟩
  let reduce (i : Fin k) : ZMod (∏ j, m j) →+* ZMod (m i) :=
    ZMod.castHom (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) _
  let f := RingHom.pi reduce
  apply RingEquiv.ofBijective f
  apply (Fintype.bijective_iff_surjective_and_card f).mpr
  constructor
  · intro x
    let solution := Nat.chineseRemainderOfFinset (fun i => (x i).val) m Finset.univ
      (fun i _ => hn i) (fun _ _ _ _ hij => hc hij)
    refine ⟨(solution.val : ZMod (∏ i, m i)), funext fun i => ?_⟩
    change reduce i (solution.val : ZMod (∏ i, m i)) = x i
    rw [map_natCast]
    calc
      (solution.val : ZMod (m i)) = ((x i).val : ZMod (m i)) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr (solution.property i (Finset.mem_univ i))
      _ = x i := ZMod.natCast_zmod_val (x i)
  · simp [Fintype.card_pi, ZMod.card]

theorem zmodCRT_apply {k : ℕ} (m : Fin k → ℕ) (hn : ∀ i, m i ≠ 0)
    (hc : Pairwise fun i j => (m i).Coprime (m j)) (x : ZMod (∏ i, m i)) (i : Fin k) :
    zmodCRT m hn hc x i = ZMod.castHom (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) _ x := rfl

/-- The sign equivalence for the units modulo a product of distinct odd prime powers. -/
noncomputable def crtSigns {k : ℕ} (p e : Fin k → ℕ) (distinct : Function.Injective p)
    (hp : ∀ i, (p i).Prime) (hodd : ∀ i, Odd (p i)) (he : ∀ i, 0 < e i) :
    SquareFiber (1 : (ZMod (∏ i, p i ^ e i))ˣ) ≃ SignCube k :=
  let crt := zmodCRT (fun i => p i ^ e i) (fun i => pow_ne_zero _ (hp i).ne_zero)
    (fun {i j} hij => Nat.coprime_pow_primes _ _ (hp i) (hp j) (fun h => hij (distinct h)))
  (squareFiberCongr (Units.mapEquiv crt.toMulEquiv)).trans (productSigns p e hp hodd he)

theorem crtSigns_true {k : ℕ} (p e : Fin k → ℕ) (distinct : Function.Injective p)
    (hp : ∀ i, (p i).Prime) (hodd : ∀ i, Odd (p i)) (he : ∀ i, 0 < e i)
    (x : SquareFiber (1 : (ZMod (∏ j, p j ^ e j))ˣ)) (i : Fin k) :
    crtSigns p e distinct hp hodd he x i = true ↔
      ZMod.castHom (Finset.dvd_prod_of_mem (fun j => p j ^ e j) (Finset.mem_univ i))
        (ZMod (p i ^ e i)) (x.val : ZMod (∏ j, p j ^ e j)) = 1 := by
  unfold crtSigns
  rw [Equiv.trans_apply, productSigns_true]
  rfl

/-- Both signs in the CRT cube give a proper gcd with the integer modulus. -/
theorem proper_gcd_of_mixed {k : ℕ} (p e : Fin k → ℕ) (distinct : Function.Injective p)
    (hp : ∀ i, (p i).Prime) (hodd : ∀ i, Odd (p i)) (he : ∀ i, 0 < e i)
    (x : SquareFiber (1 : (ZMod (∏ j, p j ^ e j))ˣ)) (n : ℕ) (hn : 1 ≤ n)
    (representative : (n : ZMod (∏ j, p j ^ e j)) = x.val)
    (positive : ∃ i, crtSigns p e distinct hp hodd he x i = true)
    (negative : ∃ j, crtSigns p e distinct hp hodd he x j = false) :
    1 < Nat.gcd (n - 1) (∏ j, p j ^ e j) ∧
      Nat.gcd (n - 1) (∏ j, p j ^ e j) < ∏ j, p j ^ e j := by
  let N := ∏ j, p j ^ e j
  change 1 < Nat.gcd (n - 1) N ∧ Nat.gcd (n - 1) N < N
  have hN : 0 < N := Finset.prod_pos fun j _ => pow_pos (hp j).pos _
  have local_dvd (j : Fin k) : p j ^ e j ∣ N :=
    Finset.dvd_prod_of_mem (fun i => p i ^ e i) (Finset.mem_univ j)
  have sign_dvd (j : Fin k) : crtSigns p e distinct hp hodd he x j = true ↔ p j ^ e j ∣ n - 1 := by
    rw [crtSigns_true, ← representative, map_natCast, ← Nat.cast_one,
      ZMod.natCast_eq_natCast_iff, Nat.ModEq.comm, Nat.modEq_iff_dvd' hn]
  obtain ⟨i, hi⟩ := positive
  obtain ⟨j, hj⟩ := negative
  have divisor_small := Nat.gcd_dvd_right (n - 1) N
  have divisor_pos := Nat.gcd_pos_of_pos_right (n - 1) hN
  have divisor_large := Nat.dvd_gcd ((sign_dvd i).mp hi) (local_dvd i)
  refine ⟨(hp i).one_lt.trans_le ((Nat.le_pow (he i)).trans (Nat.le_of_dvd divisor_pos divisor_large)),
    lt_of_le_of_ne (Nat.le_of_dvd hN divisor_small) ?_⟩
  intro eq
  have h := (sign_dvd j).mpr ((local_dvd j).trans (eq ▸ Nat.gcd_dvd_left (n - 1) N))
  rw [hj] at h
  contradiction

end Cogentic.RandomizedCRTSigns
