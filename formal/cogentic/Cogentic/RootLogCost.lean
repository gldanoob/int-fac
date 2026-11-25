import Cogentic.HelmertCost
import Cogentic.ExponentBounds
import Cogentic.BackSubstitutionBounds

namespace Cogentic.RootLogs
open Bisection

/-- Both endpoints share a denominator throughout bisection, regardless of
which polynomial signs choose the next half interval. -/
private def onGrid (x : ℚ) (D : ℕ) := ∃ m : ℤ, x*D=m

private theorem grid_double {x : ℚ} {D : ℕ} (hx : onGrid x D) : onGrid x (2*D) := by
  obtain ⟨a,ha⟩ := hx
  exact ⟨2*a,by push_cast; linarith⟩

private theorem grid_mid {b : Bracket} {D : ℕ} (l : onGrid b.left D) (r : onGrid b.right D) :
    onGrid b.mid (2*D) := by
  obtain ⟨a,ha⟩ := l
  obtain ⟨c,hc⟩ := r
  exact ⟨a+c,by unfold Bracket.mid; push_cast; linarith⟩

private theorem grid_refine (f : ℚ → ℚ) (t : ℕ) {b : Bracket} {D : ℕ}
    (l : onGrid b.left D) (r : onGrid b.right D) :
    onGrid (refine f t b).mid (2^(t+1)*D) := by
  induction t generalizing b D with
  | zero => simpa [refine] using grid_mid l r
  | succ t ih =>
    have hs : onGrid (halve f b).left (2*D) ∧ onGrid (halve f b).right (2*D) := by
      unfold halve
      split
      · exact ⟨grid_double l,grid_mid l r⟩
      · exact ⟨grid_mid l r,grid_double r⟩
    exact (show 2^(t+1+1)*D=2^(t+1)*(2*D) by rw [pow_succ,Nat.mul_assoc]) ▸ ih hs.1 hs.2

/-- Every accepted midpoint lies on the original rational grid with one
additional binary digit per halving and one for the final midpoint. -/
theorem isolate_grid {s : Marking.Input} {side : Bool} {j : Fin s.degree} {t : ℕ} {x : ℚ}
    (found : isolate s side j t=some x) :
    let k := (19*s.K₁.log2+19)/20
    ∃ m : ℤ, x*(2^(t+1)*((4*s.degree)*2^k):ℕ)=m := by
  intro k
  dsimp only [isolate] at found
  split at found
  next _ =>
    cases found
    let a := 2*j.val+(if side then 2 else 1)
    let d := 4*s.degree
    let D := d*2^k
    have dp : 0<s.degree := Nat.zero_lt_of_lt j.isLt
    have dpos : (d:ℚ)≠0 := by dsimp [d]; positivity
    have c : ((a:ℚ)/d)*(D:ℚ)=((a*2^k:ℕ):ℚ) := by dsimp [D]; push_cast; field_simp
    have w : (1/2:ℚ)^k*D=d := by dsimp [D]; push_cast; rw [one_div_pow]; field_simp
    have deq : (4:ℚ)*s.degree = (d:ℚ) := by simp [d]
    apply grid_refine
    · refine ⟨((a*2^k:ℕ):ℤ)-d,?_⟩
      change (((a:ℚ)/(4*s.degree))-(1/2:ℚ)^k)*(D:ℚ)=_
      rw [deq,sub_mul,c,w]; push_cast; rfl
    · refine ⟨((a*2^k:ℕ):ℤ)+d,?_⟩
      change (((a:ℚ)/(4*s.degree))+(1/2:ℚ)^k)*(D:ℚ)=_
      rw [deq,add_mul,c,w]; push_cast; rfl
  next => cases found

/-- Actual logarithm arguments, including the final midpoint and the mark's
division by A, have bit width linear in root precision and input widths. -/
theorem isolate_offset_width {s : Marking.Input} {a : ℕ} (Ap : 0<s.A) (fit : a ≤ s.A)
    {side : Bool} {j : Fin s.degree} {t : ℕ} {x : ℚ} (found : isolate s side j t=some x) :
    let k := (19*s.K₁.log2+19)/20
    let width := s.A.size+s.degree.size+k+t+5
    let dist := |(a:ℚ)/s.A-x|
    dist.num.natAbs.size≤width ∧ dist.den.size≤width := by
  intro k width dist
  let D := 2^(t+1)*((4*s.degree)*2^k)
  let G := s.A*D
  have dp : 0<s.degree := Nat.zero_lt_of_lt j.isLt
  have gp : 0<G := by dsimp [G,D]; positivity
  obtain ⟨m,grid⟩ := isolate_grid found
  change x*(D:ℚ)=(m:ℚ) at grid
  let z := (a:ℤ)*D-m*s.A
  have diff : ((a:ℚ)/s.A-x)*G=(z:ℚ) := by
    dsimp [G,z]; push_cast
    calc
      _ = (a:ℚ)*D-(x*D)*s.A := by field_simp
      _ = _ := by rw [grid]
  have absGrid : dist*G=(|z|:ℤ) := by
    have h := congrArg abs diff
    simpa [dist,abs_mul,abs_of_nonneg (Nat.cast_nonneg G : (0:ℚ)≤G)] using h
  have dist_le : dist≤2 := by
    let b := bracket s side j
    let f := normalized (R:=ℚ) s.A (s.coeffs side)
    have success : (if f b.left*f b.right<0 then some (refine f t b).mid else none)=some x := found
    split at success
    next sign =>
      cases success
      let u := 2*j.val+(if side then 2 else 1)
      have ub : u≤4*s.degree := by dsimp [u]; cases side <;> simp <;> omega
      have center : (u:ℚ)/(4*s.degree)≤1 := (div_le_one (by positivity)).mpr (by exact_mod_cast ub)
      have rad := pow_le_one₀ (n:=k) (by norm_num : (0:ℚ)≤1/2) (by norm_num : (1/2:ℚ)≤1)
      have ord : b.left≤b.right := by dsimp [b,bracket]; linarith [pow_nonneg (by norm_num : (0:ℚ)≤1/2) k]
      obtain ⟨l,o,r,_,_⟩ := refine_spec f t ord sign.le
      have bounds : (u:ℚ)/(4*s.degree)-(1/2:ℚ)^k≤(refine f t b).left ∧
          (refine f t b).right≤(u:ℚ)/(4*s.degree)+(1/2:ℚ)^k := ⟨l,r⟩
      have ratio : (a:ℚ)/s.A≤1 := (div_le_one (by positivity)).mpr (by exact_mod_cast fit)
      dsimp only [dist,Bracket.mid]
      rw [abs_le]
      constructor <;> linarith [bounds.1,bounds.2,show (0:ℚ)≤(u:ℚ)/(4*s.degree) by positivity,
        show (0:ℚ)≤(a:ℚ)/s.A by positivity]
    next => cases success
  have sz : |z|≤2*(G:ℤ) := by
    have h := (le_of_eq absGrid.symm).trans (mul_le_mul_of_nonneg_right dist_le (Nat.cast_nonneg G))
    exact_mod_cast h
  have frac : Elimination.BoundedFraction (fun _ : Fin 1 => dist) (2*(G:ℤ)) :=
    ⟨G,by exact_mod_cast gp.ne',by rw [abs_of_nonneg (Int.natCast_nonneg _)]; omega,
     fun _=>|z|,fun _=>by simpa only [abs_abs] using sz,fun _=>by simpa using absGrid⟩
  obtain ⟨hn,hd⟩ := frac.reduced 0
  change |dist.num|≤_ at hn; change (dist.den:ℤ)≤_ at hd
  rw [Int.abs_eq_natAbs] at hn
  have maxn : dist.num.natAbs≤2*G := by exact_mod_cast hn
  have maxd : dist.den≤2*G := by exact_mod_cast hd
  have maxG : 2*G≤2^(s.A.size+s.degree.size+k+t+4) := calc
    _ ≤ 2*(2^s.A.size*(2^(t+1)*((4*2^s.degree.size)*2^k))) := by
      dsimp [G,D]; gcongr <;> exact (Nat.lt_size_self _).le
    _ = _ := by
      change 2^1*(2^s.A.size*(2^(t+1)*((2^2*2^s.degree.size)*2^k)))=_
      simp only [←pow_add]; congr 1; omega
  have bound (a : ℕ) (h : a≤2*G) : a.size≤width := by
    simpa [width,Nat.size_pow] using Nat.size_le_size (h.trans maxG)
  exact ⟨bound _ maxn,bound _ maxd⟩

theorem isolate_distance_width {s : Marking.Input} {rel : Marking.Relations}
    (stage : Marking.stageOne s=some rel) {a : ℕ} (marked : a∈rel.marks)
    {side : Bool} {j : Fin s.degree} {t : ℕ} {x : ℚ} (found : isolate s side j t=some x) :
    let k := (19*s.K₁.log2+19)/20
    let width := s.A.size+s.degree.size+k+t+5
    let dist := |(a:ℚ)/s.A-x|
    dist.num.natAbs.size≤width ∧ dist.den.size≤width := by
  have ep := ((Marking.retained_iff stage a).mp marked).1
  simp only [Marking.Input.eligibleMarks,Finset.mem_sort,Finset.mem_filter] at ep
  exact isolate_offset_width (ep.2.1.trans ep.2.2.1) ep.2.2.1 found

end Cogentic.RootLogs
