import Cogentic.FixedSchedule
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt

namespace Cogentic.Construction
open Real

/-- Any fixed polynomial in the bit length fits the gap between two fixed
logarithmic-square precision exponents. The constant can depend on the precision. -/
theorem rank_polynomial_savings (C : ℝ) (m : ℕ) {K k : ℝ} (gap : k<K) :
    ∃ b₀ : ℕ, ∀ b≥b₀, C*(b:ℝ)^m*exp (-K*(Fixed.z b:ℝ)^2) ≤ exp (-k*(Fixed.z b:ℝ)^2) := by
  obtain ⟨j,hj⟩ := exists_nat_ge (((m:ℝ)+1)/(K-k))
  obtain ⟨c,hc⟩ := exists_nat_ge C
  refine ⟨max c (2^j),?_⟩
  intro b hb
  obtain ⟨bc,bj⟩ := max_le_iff.mp hb
  have cb : C≤(b:ℝ) := hc.trans (by exact_mod_cast bc)
  let z : ℝ := Fixed.z b
  have zp : 0≤z := Nat.cast_nonneg _
  have bp : 0<b := (Nat.pow_pos (by decide : 0<2)).trans_le bj
  have jz : (j:ℝ)≤z := by
    dsimp only [z,Fixed.z]
    exact_mod_cast ((Nat.le_log2 bp.ne').mpr bj).trans (Nat.le_succ _)
  have room := (div_le_iff₀ (sub_pos.mpr gap)).mp (hj.trans jz)
  have bz : (b:ℝ)≤exp z := by
    have e := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2)
      (by linarith only [Real.add_one_le_exp 1] : (2:ℝ)≤exp 1) (Fixed.z b)
    rw [←exp_nat_mul,mul_one] at e
    exact (show (b:ℝ)≤(2:ℝ)^(Fixed.z b) by exact_mod_cast (Nat.lt_log2_self.le : b≤2^(Fixed.z b))).trans e
  calc
    _ ≤ ((exp z)*(exp z)^m)*exp (-K*z^2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul (cb.trans bz)
        (pow_le_pow_left₀ (Nat.cast_nonneg _) bz m) (by positivity) (exp_pos _).le) (exp_pos _).le
    _ = exp ((1+(m:ℝ))*z-K*z^2) := by rw [←exp_nat_mul,←exp_add,←exp_add]; congr 1;ring
    _ ≤ _ := exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_right room zp])

/-- Polynomial growth of the profile variation from the unsharpened mesh estimate. -/
theorem rank_mesh_prefactor_le {b : ℕ} (big : 4000≤b) :
    let d := (Fixed.d b:ℝ)
    let A := 3*(1760*d+4)^4
    let V := 40*d^2*(1760*d+4)^4*(24+32*sqrt (110*d))
    (1+27*A^2)*(3*A^2+2*A*V)≤(b:ℝ)^42 := by
  intro d A V
  let P := 3*A^2+2*A*V
  let t : ℝ := b
  have large : 4000≤t := by dsimp only [t]; exact_mod_cast big
  have one : 1≤t := by linarith
  have tp : 0≤t := zero_le_one.trans one
  have dp : 0≤d := Nat.cast_nonneg _
  have dt : d≤t := by dsimp only [d,t]; exact_mod_cast Fixed.degree_le_bits b
  have mono {i j : ℕ} (ij : i≤j) : t^i≤t^j := pow_le_pow_right₀ one ij
  have sqRoom : 1764*t≤t^2 := by nlinarith only [mul_nonneg tp (show 0≤t-1764 by linarith)]
  have base : 1760*d+4≤t^2 := (by linarith only [dt,one] : 1760*d+4≤1764*t).trans sqRoom
  have root : sqrt (110*d)≤t := (Real.sqrt_le_iff).mpr ⟨tp,by linarith⟩
  have cap : 24+32*sqrt (110*d)≤t^2 := by linarith
  have a : A≤t^9 := calc
    _ ≤ t*(t^2)^4 := by dsimp only [A]; gcongr <;> linarith
    _ = _ := by ring
  have v : V≤t^13 := calc
    _ ≤ t*t^2*(t^2)^4*t^2 := by dsimp only [V]; gcongr <;> linarith
    _ = _ := by ring
  have ap : 0≤A := by dsimp only [A]; positivity
  have vp : 0≤V := by dsimp only [V]; positivity
  have pp : 0≤P := by dsimp only [P]; positivity
  have a2 : A^2≤t^18 := (pow_le_pow_left₀ ap a 2).trans_eq (by ring)
  have av : A*V≤t^22 := (mul_le_mul a v vp (by positivity)).trans_eq (by ring)
  have p : P≤t^23 := calc
    _ ≤ 5*t^22 := by dsimp only [P]; linarith only [a2.trans (mono (by decide : 18≤22)),av]
    _ ≤ t*t^22 := by gcongr <;> linarith
    _ = _ := by ring
  have a2p : 1+27*A^2≤t^19 := calc
    _ ≤ 28*t^18 := by linarith only [a2,one_le_pow₀ (n:=18) one]
    _ ≤ t*t^18 := by gcongr <;> linarith
    _ = _ := by ring
  exact (mul_le_mul a2p p pp (by positivity)).trans_eq (by ring)

/-- The normalized costs of the ordinary pair, mixed and protected Gram blocks. -/
theorem rank_prefactor_savings (C : ℝ) (hc : 0≤C) {K k : ℝ} (gap : k<K) :
    ∃ b₀ : ℕ, ∀ b≥b₀, ∀ u : ℝ, 0≤u → u≤110*(Fixed.d b:ℝ) →
    let H := (Fintype.card (Option (Bool×Fin (Fixed.d b))):ℝ)
    let D := 3*(Fixed.h b:ℝ)+1
    let e := exp (-K*(Fixed.z b:ℝ)^2)
    let s := exp (-k*(Fixed.z b:ℝ)^2)
    256*u^2*(C*3^2*e)≤ s ∧ H*(32*u)*(C*(6*D)^2*e)≤ s ∧
    H^2*(C*(2*(D^2+2*D))^2*e)≤ s := by
  obtain ⟨b₀,save⟩ := rank_polynomial_savings C 14 gap
  refine ⟨max 4000 b₀,?_⟩
  intro b hb u up ub H D e s
  obtain ⟨big,bs⟩ := max_le_iff.mp hb
  let d : ℝ := Fixed.d b
  let t : ℝ := b
  have large : 4000≤t := by dsimp only [t]; exact_mod_cast big
  have one : 1≤t := by linarith
  have tp : 0≤t := zero_le_one.trans one
  have dp : 0≤d := Nat.cast_nonneg _
  have dt : d≤t := by dsimp only [d,t]; exact_mod_cast Fixed.degree_le_bits b
  have mono {i j : ℕ} (ij : i≤j) : t^i≤t^j := pow_le_pow_right₀ one ij
  have sqRoom : 1764*t≤t^2 := by nlinarith only [mul_nonneg tp (show 0≤t-1764 by linarith)]
  have deg : 1≤Fixed.d b := Fixed.degree_pos (by omega)
  have hh : (Fixed.h b:ℝ)≤t := by
    have lower : Fixed.d b≤(Fixed.d b)^3 := by simpa only [pow_one] using (Nat.pow_le_pow_right deg (by decide : 1≤3))
    dsimp only [t,Fixed.h]
    exact_mod_cast (Nat.mul_le_mul_right (Fixed.z b) lower).trans (Fixed.degree_floor b).1
  have db : D≤t^2 := by dsimp only [D];linarith
  have cp : 0≤D := by dsimp only [D];positivity
  have hbnd : H≤t^2 := by
    dsimp only [H]
    simp only [Fintype.card_option,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]
    push_cast
    change 2*d+1≤t^2
    linarith
  have hp : 0≤H := Nat.cast_nonneg _
  have ubnd : u≤t^2 := by change u≤110*d at ub; linarith
  have d2 : D^2≤t^4 := (pow_le_pow_left₀ cp db 2).trans_eq (by ring)
  have pr : 2*(D^2+2*D)≤t^5 := calc
    _ ≤ 6*t^4 := by linarith only [d2,db.trans (mono (by decide : 2≤4))]
    _ ≤ t*t^4 := by gcongr <;> linarith
    _ = _ := by ring
  have absorb (x : ℝ) (hx : x≤t^14) : x*(C*e)≤ s := by
    have := mul_le_mul_of_nonneg_right hx (show 0≤C*e by dsimp only [e]; positivity)
    exact this.trans ((show t^14*(C*e)=C*t^14*e by ring).le.trans (save b bs))
  constructor
  · rw [show 256*u^2*(C*3^2*e)=(256*u^2*3^2)*(C*e) by ring]
    apply absorb
    calc
      _ ≤ t*(t^2)^2*t^2 := by gcongr <;> linarith
      _ = t^7 := by ring
      _ ≤ _ := mono (by decide)
  constructor
  · rw [show H*(32*u)*(C*(6*D)^2*e)=(H*(32*u)*(6*D)^2)*(C*e) by ring]
    apply absorb
    calc
      _ ≤ t^2*(t*t^2)*(t*t^2)^2 := by gcongr <;> linarith
      _ = t^11 := by ring
      _ ≤ _ := mono (by decide)
  · rw [show H^2*(C*(2*(D^2+2*D))^2*e)=(H^2*(2*(D^2+2*D))^2)*(C*e) by ring]
    apply absorb
    calc
      _ ≤ (t^2)^2*(t^5)^2 := by gcongr
      _ = t^14 := by ring
      _ ≤ _ := mono (by decide)

end Cogentic.Construction

#print axioms Cogentic.Construction.rank_polynomial_savings
#print axioms Cogentic.Construction.rank_prefactor_savings
