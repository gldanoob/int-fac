import Statements
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitFormulaClosedStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ZeroCountHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiChiSqrtLogBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogDerivSeriesOfExplicit
import Cogentic.PrimeCount

namespace Cogentic.Window
open GlobalTheory.Mem.An Formalism.MainNotions.GlobalTheoryTheory
open Finset Real

private theorem zero_sums (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ x : ℝ, 2 ≤ x →
    zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) ≤ 2*C*Real.log (3*q) ∧
    zsumR χ 0 x (fun ρ => 1 / ‖ρ‖) ≤ 2*C*Real.log (3*q) + C*Real.log (q*x)^2 := by
  obtain ⟨b, hb⟩ := zsumR_recip_le zeroCount_holds
  refine ⟨|b|, abs_nonneg _, fun q _ χ prim x hx => ?_⟩
  obtain ⟨hi, lo⟩ := hb q χ prim x hx
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have lowLog : 0 ≤ Real.log (3*q) := Real.log_nonneg (by linarith)
  have high := hi.trans (mul_le_mul_of_nonneg_right (le_abs_self b) (sq_nonneg _))
  have low := lo.trans (mul_le_mul_of_nonneg_right (le_abs_self b) lowLog)
  have finiteZ (T : ℝ) := (ZeroWindow.finite_and_one_le_zmult q χ 0 T).1
  have reciprocal (ρ : ℂ) (h : ρ ∈ zerosIn χ 0 1) : 1 / ‖ρ‖ ≤ 2 := by
    have hline := line q χ ρ h.1 h.2.1 h.2.2.2
    have hb := Complex.re_le_norm ρ
    apply (div_le_iff₀ (by linarith : 0 < ‖ρ‖)).mpr
    linarith
  have small : zsumR χ 0 1 (fun ρ => 1/‖ρ‖) ≤ 2*zsumR χ 0 1 (fun _ => 1) := by
    rw [zsumR_eq_sum_toFinset _ _ _ _ (finiteZ 1), zsumR_eq_sum_toFinset _ _ _ _ (finiteZ 1), mul_sum]
    apply sum_le_sum
    intro ρ hρ
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (reciprocal ρ (by simpa using hρ))
      (Nat.cast_nonneg (α := ℝ) (zmult χ ρ))
  have separate : zsumR χ 0 x (fun ρ => 1/‖ρ‖) ≤ zsumR χ 0 1 (fun ρ => 1/‖ρ‖) +
      zsumR χ 0 x (fun ρ => if 1 < |ρ.im| then 1/‖ρ‖ else 0) := by
    simp only [zsumR_eq_sum_toFinset _ _ _ _ (finiteZ _)]
    have subset : (finiteZ 1).toFinset = (finiteZ x).toFinset.filter (fun ρ => ¬1 < |ρ.im|) := by
      ext ρ
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, zerosIn, Set.mem_ofPred_eq, sub_zero, not_lt]
      constructor
      · rintro ⟨a,b,c,d⟩
        exact ⟨⟨a,b,by linarith,d⟩,c⟩
      · rintro ⟨⟨a,b,_,d⟩,c⟩
        exact ⟨a,b,c,d⟩
    rw [subset, sum_filter, ← sum_add_distrib]
    apply sum_le_sum
    intro ρ _
    by_cases h : 1 < |ρ.im| <;> simp [h]
  constructor <;> linarith

/-- The constants in the primitive explicit formula and unit-height zero count
    are absolute. Setting the truncation height to x keeps only logarithmic dependence on q. -/
theorem primitive_psi_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ x : ℝ, 2 ≤ x → ‖psi0 χ x‖ ≤ C * √x * (1+Real.log (3*q*x))^2 := by
  obtain ⟨a, explicit⟩ := GlobalTheory.T.norm_psi0_add_zsum_le
  obtain ⟨b, hb, zeros⟩ := zero_sums line
  refine ⟨|a| *(5+2*b)+3*b, by positivity, fun q _ χ prim x hx => ?_⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have xp : 0 < x := by linarith
  have qp : (0 : ℝ) < q := by linarith
  let D := 1+Real.log (3*q*x)
  have logpos : 0 ≤ Real.log (3*q*x) := Real.log_nonneg (by nlinarith)
  have D1 : 1 ≤ D := by dsimp [D]; linarith
  have base : 0 ≤ Real.log (q*x) := Real.log_nonneg (by nlinarith)
  have low : Real.log (3*q) ≤ D := by
    have := Real.log_le_log (show 0 < (3:ℝ)*q by positivity) (show 3*q ≤ (3:ℝ)*q*x by nlinarith)
    dsimp [D]; linarith
  have qt : Real.log (q*x) ≤ D := by
    have := Real.log_le_log (mul_pos qp xp) (show q*x ≤ (3:ℝ)*q*x by nlinarith)
    dsimp [D]; linarith
  have lx : Real.log x ≤ Real.log (q*x) := Real.log_le_log xp (by nlinarith)
  have multi : Real.log (q*x*x)^2 ≤ 4*D^2 := by
    rw [Real.log_mul (mul_pos qp xp).ne' xp.ne']
    nlinarith [sq_nonneg (D-Real.log (q*x)), sq_nonneg (D-Real.log x),
      mul_nonneg (show 0 ≤ 2*D-(Real.log (q*x)+Real.log x) by linarith)
        (show 0 ≤ 2*D+(Real.log (q*x)+Real.log x) by linarith [Real.log_nonneg (by linarith : 1 ≤ x)])]
  obtain ⟨zlow, zall⟩ := zeros q χ prim x hx
  have sqD : D ≤ D^2 := by nlinarith [mul_nonneg (show 0 ≤ D by linarith) (sub_nonneg.mpr D1)]
  have zlo : zsumR χ 0 1 (fun ρ => 1/‖ρ‖) ≤ 2*b*D^2 :=
    zlow.trans (mul_le_mul_of_nonneg_left (low.trans sqD) (by positivity))
  have zhi : zsumR χ 0 x (fun ρ => 1/‖ρ‖) ≤ (3*b)*D^2 := by
    have t := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ base qt 2) hb
    have u := mul_le_mul_of_nonneg_left (low.trans sqD) (show 0 ≤ 2*b by positivity)
    linarith
  have zerosTerm := GoodLarge.norm_zsum_le χ x x (√x) (by
    intro ρ hz
    rw [Complex.norm_cpow_eq_rpow_re_of_pos xp, line q χ ρ hz.1 hz.2.1 hz.2.2.2, Real.sqrt_eq_rpow])
  let Z := zsum χ 0 x (fun ρ => (x:ℂ)^ρ/ρ)
  have Zbound : ‖Z‖ ≤ √x*((3*b)*D^2) :=
    zerosTerm.trans (mul_le_mul_of_nonneg_left zhi (Real.sqrt_nonneg _))
  have small0 : 0 ≤ zsumR χ 0 1 (fun ρ => 1/‖ρ‖) := by
    rw [zsumR_eq_sum_toFinset _ _ _ _ (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1]
    exact sum_nonneg (fun _ _ => by positivity)
  have E := explicit q χ prim x x hx le_rfl
  rw [mul_div_cancel_left₀ _ xp.ne'] at E
  have E' := E.trans (mul_le_mul_of_nonneg_right (le_abs_self a) (by positivity))
  have Ebound : ‖psi0 χ x + Z‖ ≤ |a| *((5+2*b)*D^2) := by
    refine E'.trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg a))
    linarith
  have hs : 1 ≤ √x := Real.one_le_sqrt.mpr (by linarith)
  have lifted := le_mul_of_one_le_left (show 0 ≤ |a| *((5+2*b)*D^2) by positivity) hs
  calc
    _ = ‖(psi0 χ x + Z) - Z‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖psi0 χ x + Z‖ + ‖Z‖ := norm_sub_le ..
    _ ≤ √x*(|a| *((5+2*b)*D^2)) + √x*((3*b)*D^2) := add_le_add (Ebound.trans lifted) Zbound
    _ = _ := by dsimp [D]; ring

/-- All characters, including the principal character and imprimitive characters.
    The pole is subtracted exactly in the definition of the upstream psi0. -/
theorem uniform_psi_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (x : ℝ), 2 ≤ x → ‖psi0 χ x‖ ≤ C*√x*(1+Real.log (3*q*x))^2 := by
  obtain ⟨c, hc, bound⟩ := primitive_psi_from_critical_line line
  have lpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨c + (Real.log 2)⁻¹, by positivity, fun q _ χ x hx => ?_⟩
  let D := 1+Real.log (3*q*x)
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have q1 : (1:ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have f1 : (1:ℝ) ≤ χ.conductor := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero
  have fd : (χ.conductor:ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
  have x0 : 0 < x := by linarith
  have qp : (0:ℝ) < q := by linarith
  have primEq : χ.primitiveCharacter = 1 ↔ χ = 1 := by
    constructor
    · intro h
      rw [← χ.changeLevel_primitiveCharacter, h, map_one]
    · rintro rfl
      exact DirichletCharacter.primitiveCharacter_one
  have diff := GlobalTheory.MangoldtSeries.norm_sub_primitive_le χ ⌊x⌋₊
  have err : ‖psi0 χ x - psi0 χ.primitiveCharacter x‖ ≤ Nat.log 2 ⌊x⌋₊ * Real.log q := by
    have cancel (a b t : ℂ) : (a-t) - (b-t) = a-b := by ring
    by_cases h : χ = 1
    · simpa only [psi0, if_pos h, if_pos (primEq.mpr h), cancel] using diff
    · simpa only [psi0, if_neg h, if_neg (mt primEq.mp h), sub_zero] using diff
  have big (v : ℝ) (v1 : 0 < v) (v2 : v ≤ 3*q*x) : Real.log v ≤ D := by
    dsimp [D]; linarith [Real.log_le_log v1 v2]
  have dd : 0 ≤ D := by dsimp [D]; linarith [Real.log_nonneg (show 1 ≤ 3*q*x by nlinarith)]
  have floor1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
  have logbound : (Nat.log 2 ⌊x⌋₊ : ℝ) ≤ (Real.log 2)⁻¹ * D := by
    have t := Real.natLog_le_logb ⌊x⌋₊ 2
    simp only [Real.logb, Nat.cast_ofNat] at t
    rw [mul_comm, ← div_eq_mul_inv]
    apply t.trans
    apply div_le_div_of_nonneg_right _ lpos.le
    apply big
    · exact_mod_cast (by omega : 0 < ⌊x⌋₊)
    · have := Nat.floor_le x0.le; nlinarith
  have qlog : 0 ≤ Real.log q := Real.log_nonneg q1
  have err' : ‖psi0 χ x - psi0 χ.primitiveCharacter x‖ ≤ (Real.log 2)⁻¹*D^2 := by
    calc
      _ ≤ _ := err
      _ ≤ ((Real.log 2)⁻¹ * D)*D := mul_le_mul logbound (big _ qp (by nlinarith)) qlog (by positivity)
      _ = _ := by ring
  have pbound := bound χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive x hx
  have dcomp : 1+Real.log (3*(χ.conductor:ℝ)*x) ≤ D := by
    dsimp [D]
    apply add_le_add_right
    exact Real.log_le_log (by positivity) (by nlinarith [mul_le_mul_of_nonneg_right fd x0.le])
  have localpos : 0 ≤ 1+Real.log (3*(χ.conductor:ℝ)*x) := by
    linarith [Real.log_nonneg (show 1 ≤ 3*(χ.conductor:ℝ)*x by nlinarith)]
  have pb := pbound.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ localpos dcomp 2) (by positivity))
  have lift := le_mul_of_one_le_left (show 0 ≤ (Real.log 2)⁻¹ * D^2 by positivity)
    (Real.one_le_sqrt.mpr (by linarith : 1 ≤ x))
  calc
    _ = ‖(psi0 χ x - psi0 χ.primitiveCharacter x) + psi0 χ.primitiveCharacter x‖ := by rw [sub_add_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ √x*((Real.log 2)⁻¹*D^2) + c*√x*D^2 := add_le_add (err'.trans lift) pb
    _ = _ := by dsimp [D]; ring

private theorem psi0_eq_twistedPsi {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (x : ℝ) : psi0 χ x = twistedPsi χ x := by
  simp only [psi0, hχ, if_false, sub_zero, twistedPsi]
  congr 1

/-- Character prime counts with an absolute constant, uniform in q and B. -/
theorem nonprincipal_prime_count_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ B x : ℝ, 2 ≤ x → x ≤ B →
        ‖primeCount χ x‖ ≤ (K*(1+Real.log (3*q*B))^2)*x^(1/2:ℝ) := by
  obtain ⟨c, hc, bounds⟩ := uniform_psi_from_critical_line line
  have logtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(Real.log 2)⁻¹*(c+2), by positivity, fun q _ χ hχ B x hx hB => ?_⟩
  have q1 : (1:ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  let D := 1+Real.log (3*q*B)
  have D1 : 1 ≤ D := by dsimp [D]; linarith [Real.log_nonneg (show 1 ≤ 3*q*B by nlinarith)]
  have D0 : 0 ≤ D := by linarith
  have Dsq : D ≤ D^2 := by nlinarith [mul_nonneg D0 (sub_nonneg.mpr D1)]
  have theta (n : ℕ) (hn : n ≤ ⌊x⌋₊) :
      ‖twistedTheta χ n‖ ≤ (c+2)*√x*D^2 := by
    by_cases small : n < 2
    · interval_cases n <;> simp <;> positivity
    have n2 : (2:ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    have nx : (n:ℝ) ≤ x := (Nat.cast_le.mpr hn).trans (Nat.floor_le (by linarith))
    have dpos : 0 ≤ 1+Real.log (3*q*n) := by
      linarith [Real.log_nonneg (show 1 ≤ (3:ℝ)*q*n by nlinarith)]
    have dcomp : 1+Real.log (3*q*n) ≤ D := by
      dsimp [D]
      apply add_le_add_right
      apply Real.log_le_log (by positivity)
      exact mul_le_mul_of_nonneg_left (nx.trans hB) (by positivity)
    have logn : Real.log n ≤ D^2 := by
      apply le_trans _ Dsq
      dsimp [D]
      linarith [Real.log_le_log (show (0:ℝ)<n by linarith)
        (show (n:ℝ) ≤ 3*q*B by nlinarith [mul_le_mul_of_nonneg_right q1 (show 0 ≤ B by linarith)])]
    have estimate := bounds q χ n n2
    rw [psi0_eq_twistedPsi hχ] at estimate
    have scomp := Real.sqrt_le_sqrt nx
    have psi := estimate.trans (mul_le_mul (mul_le_mul_of_nonneg_left scomp hc)
      (pow_le_pow_left₀ dpos dcomp 2) (sq_nonneg _) (by positivity))
    have tail := (prime_power_tail χ (by linarith : 1 ≤ (n:ℝ))).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left scomp (by norm_num)) logn
        (Real.log_nonneg (by linarith)) (by positivity))
    calc
      _ = ‖twistedPsi χ n - (twistedPsi χ n-twistedTheta χ n)‖ := by rw [sub_sub_cancel]
      _ ≤ _ := norm_sub_le _ _
      _ ≤ c*√x*D^2 + 2*√x*D^2 := add_le_add psi tail
      _ = _ := by ring
  have h := prime_count_from_theta χ (by positivity) theta
  rw [← Real.sqrt_eq_rpow]
  convert h using 1
  dsimp [D]
  ring

end Cogentic.Window
