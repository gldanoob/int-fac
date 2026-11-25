import Cogentic.ArchNumerics
import Cogentic.Bisection
import Cogentic.Construction

namespace Cogentic.RootLogs
open Set Marking ArchNumerics Bisection

/-- The normalized polynomial value f(A t), evaluated using the original coefficients. -/
def normalized {R : Type*} [CommRing R] (A : ℕ) (coeffs : List ℤ) (t : R) : R :=
  (horner ((A:R)*t) coeffs).1

private theorem normalized_cont (A : ℕ) (cs : List ℤ) :
    Continuous (normalized (R := ℝ) A cs) := by
  induction cs with
  | nil => exact continuous_const
  | cons x xs ih =>
    change Continuous (fun t : ℝ => (x:ℝ)+((A:ℝ)*t)*normalized A xs t)
    fun_prop

private theorem normalized_cast (A : ℕ) (cs : List ℤ) (t : ℚ) :
    normalized A cs (t:ℝ) = ((normalized A cs t:ℚ):ℝ) := by
  induction cs with
  | nil => simp [normalized,horner]
  | cons x xs ih =>
    change (x:ℝ)+((A:ℝ)*(t:ℝ))*normalized A xs (t:ℝ) = (((x:ℚ)+((A:ℚ)*t)*normalized A xs t:ℚ):ℝ)
    push_cast
    rw [ih]

def bracket (s : Input) (side : Bool) (j : Fin s.degree) : Bracket :=
  let center := ((2*j.val+(if side then 2 else 1):ℕ):ℚ)/(4*s.degree)
  let width := (1/2:ℚ)^((19*s.K₁.log2+19)/20)
  ⟨center-width,center+width⟩

def isolate (s : Input) (side : Bool) (j : Fin s.degree) (bits : ℕ) : Option ℚ :=
  let b := bracket s side j
  let f := normalized (R := ℚ) s.A (s.coeffs side)
  if f b.left*f b.right < 0 then some (refine f bits b).mid else none

/-- Each accepted midpoint from the concrete coefficient list encloses an
    actual root of f(A t) to within two to the minus requested precision. -/
theorem isolate_correct {s : Input} {side : Bool} {j : Fin s.degree} {bits : ℕ} {t : ℚ}
    (hit : isolate s side j bits = some t) :
    ∃ x ∈ Icc ((bracket s side j).left:ℝ) ((bracket s side j).right:ℝ),
      normalized s.A (s.coeffs side) x = 0 ∧ |(t:ℝ)-x| ≤ (1/2:ℝ)^bits := by
  let b := bracket s side j
  let f := normalized (R := ℚ) s.A (s.coeffs side)
  have ord : b.left ≤ b.right := by dsimp [b,bracket]; linarith [pow_nonneg (by norm_num : (0:ℚ) ≤ 1/2) ((19*s.K₁.log2+19)/20)]
  have width : (b.right:ℝ)-b.left ≤ 2 := by
    dsimp only [b,bracket]
    push_cast
    have h := pow_le_one₀ (n := (19*s.K₁.log2+19)/20) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1)
    linarith
  change (if f b.left*f b.right < 0 then some (refine f bits b).mid else none) = some t at hit
  split at hit
  next sign =>
    cases hit
    obtain ⟨x,hx,root,err⟩ := midpoint_near_root f _ (normalized_cont s.A (s.coeffs side))
      (normalized_cast s.A (s.coeffs side)) bits ord sign.le
    refine ⟨x,hx,root,err.trans ?_⟩
    rw [one_div_pow, div_le_div_iff₀ (by positivity) (by positivity),pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right width (by positivity : 0 ≤ (2:ℝ)^bits)]
  next _ => cases hit

def markLog (A a : ℕ) (root : ℚ) (lowBits bits : ℕ) : Option ℚ :=
  let dist := |(a:ℚ)/A-root|
  if (1/2:ℚ)^(lowBits+1) ≤ dist then some (approxLog dist.num.natAbs dist.den bits) else none

private lemma log_lipschitz {x y m : ℝ} (hm : 0 < m) (hx : m ≤ x) (hy : m ≤ y) :
    |Real.log x-Real.log y| ≤ |x-y|/m := by
  have side (x y : ℝ) (mx : m ≤ x) (my : m ≤ y) : Real.log x-Real.log y ≤ |x-y|/m := by
    have xp := hm.trans_le mx
    have yp := hm.trans_le my
    rw [← Real.log_div xp.ne' yp.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos xp yp)).trans ?_
    rw [show x/y-1=(x-y)/y by field_simp]
    exact (div_le_div_of_nonneg_right (le_abs_self _) yp.le).trans
      (div_le_div_of_nonneg_left (abs_nonneg _) hm my)
  have lower := side y x hy hx
  rw [abs_sub_comm y x] at lower
  exact abs_le.mpr ⟨by linarith,side x y hx hy⟩

/-- Perturbing a separated root by e contributes at most e/m to the
    logarithmic error, in addition to the certified dyadic rounding error. -/
theorem markLog_error {A a low bits : ℕ} {t v : ℚ} {x e : ℝ}
    (hit : markLog A a t low bits = some v) (near : |(t:ℝ)-x| ≤ e)
    (sep : (1/2:ℝ)^(low+1) ≤ |(a:ℝ)/A-x|) :
    |(v:ℝ)-Real.log (|(a:ℝ)/A-x|)| ≤ (1/2:ℝ)^bits + e/(1/2:ℝ)^(low+1) := by
  let z := |(a:ℚ)/A-t|
  let m := (1/2:ℝ)^(low+1)
  change (if (1/2:ℚ)^(low+1) ≤ z then some (approxLog z.num.natAbs z.den bits) else none) = some v at hit
  split at hit
  next ez =>
    cases hit
    have zpos : 0 < z := (by positivity : (0:ℚ) < (1/2:ℚ)^(low+1)).trans_le ez
    have npos : 0 < z.num := Rat.num_pos.mpr zpos
    have eq : ((z.num.natAbs:ℕ):ℝ)/(z.den:ℝ) = (z:ℝ) := by
      rw [Nat.cast_natAbs,abs_of_pos (by exact_mod_cast npos)]
      exact Rat.cast_def z |>.symm
    have val := approxLog_error (u := z.num.natAbs) (v := z.den)
      (Int.natAbs_pos.mpr npos.ne') z.den_pos bits
    rw [eq] at val
    have zr : (z:ℝ) = |(a:ℝ)/A-(t:ℝ)| := by simp [z]
    have zl : m ≤ (z:ℝ) := by
      simpa only [m, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using ((Rat.cast_le (K := ℝ)).mpr ez)
    have close : |(z:ℝ)-abs ((a:ℝ)/A-x)| ≤ e := by
      rw [zr]
      refine (abs_abs_sub_abs_le_abs_sub ..).trans ?_
      rw [sub_sub_sub_cancel_left,abs_sub_comm]; exact near
    have diff := (log_lipschitz (by dsimp [m]; positivity) zl sep).trans
      (div_le_div_of_nonneg_right close (by dsimp [m]; positivity))
    exact (abs_sub_le _ (Real.log z) _).trans (add_le_add val.le diff)
  next _ => cases hit

/-- A root at distance at least twice the guard survives both the midpoint
test and the dyadic logarithm approximation. -/
theorem markLog_of_separated {A a low bits : ℕ} {t : ℚ} {x e : ℝ}
    (near : |(t:ℝ)-x| ≤ e) (prec : e ≤ (1/2:ℝ)^(low+1))
    (sep : 2*(1/2:ℝ)^(low+1) ≤ |(a:ℝ)/A-x|) :
    ∃ v, markLog A a t low bits = some v ∧
      |(v:ℝ)-Real.log (|(a:ℝ)/A-x|)| ≤ (1/2:ℝ)^bits + e/(1/2:ℝ)^(low+1) := by
  have triangle := abs_sub_le ((a:ℝ)/A) (t:ℝ) x
  have dist : (1/2:ℝ)^(low+1) ≤ |(a:ℝ)/A-(t:ℝ)| := by linarith
  have accept : (1/2:ℚ)^(low+1) ≤ |(a:ℚ)/A-t| := by
    apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    exact dist
  have existsHit : ∃ v, markLog A a t low bits = some v := by
    unfold markLog
    rw [if_pos accept]; exact ⟨_,rfl⟩
  obtain ⟨v,h⟩ := existsHit
  exact ⟨v,h,markLog_error h near (le_trans (by nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) (low+1)]) sep)⟩

end Cogentic.RootLogs
