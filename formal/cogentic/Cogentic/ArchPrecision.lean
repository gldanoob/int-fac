import Cogentic.ArchStability
import Cogentic.ProjectionErrors

/-! Binary height and precision arithmetic for the fixed two-field solve. -/

open NumberField
open scoped BigOperators Matrix
namespace Cogentic
namespace ArchPrecision

/-- Envelope inputs for the fixed-schedule integer linear system. The same Nat exponent covers the mark count, finite-row count,
per-mark logarithm bound and reciprocal Helmert separation. -/
structure Envelope (d R b marks k : ℕ) : Prop where
  degree : 1 ≤ d
  rowCount : 1 ≤ R
  budget : 8*k ≤ b
  bits : 1 ≤ b
  marks_le : marks ≤ 2^k
  rows_le : R ≤ 2^k
  logs_le : 2*d*(b+1) ≤ 2^k
  gap_le : 8*d*(d+1) ≤ 2^k

/-- The integer-coordinate determinant and the true inverse envelope fit the
actual denominator cap from TryPair. -/
theorem arch_height {d R b marks k n : ℕ} (e : Envelope d R b marks k)
    (dim : n ≤ 2*d) (T : ℝ) (one : 1 ≤ T)
    (height : T ≤ (2:ℝ)^(k*(R+2))) :
    let h := R*b
    let gap := Real.log 2 / (4*d*(d+1))
    let Q := (2:ℝ)^(3*d*h)
    (n.factorial*T^n/gap^n ≤ (2:ℝ)^(2*d*h)) ∧
      ((n:ℝ)*(n.factorial*T^n/gap^n) ≤ Q) ∧ (n : ℝ) ≤ Q ∧ T+1 ≤ Q := by
  intro h gap Q
  have dp := e.degree
  have rp := e.rowCount
  have bp := e.bits
  have kp : 1 ≤ k := by
    by_contra! z
    have a := e.logs_le
    have : k=0 := by omega
    rw [this,pow_zero] at a
    nlinarith
  have budget := e.budget
  have unit : (0:ℝ) < gap := by dsimp [gap]; positivity
  have logs : (1/2:ℝ) ≤ Real.log 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1/2)
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at this
    linarith
  have gapinv : gap⁻¹ ≤ (2:ℝ)^k := by
    have coeff : 8*(d:ℝ)*(d+1) ≤ (2:ℝ)^k := by exact_mod_cast e.gap_le
    refine le_trans ?_ coeff
    rw [show gap⁻¹ = (4*(d:ℝ)*(d+1))/Real.log 2 by simp [gap]]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left logs (by positivity : 0 ≤ 8*(d:ℝ)*(d+1))]
  have nk : (n : ℝ) ≤ (2:ℝ)^k := by
    exact_mod_cast dim.trans ((Nat.le_mul_of_pos_right (2*d) (by omega : 0<b+1)).trans e.logs_le)
  have kh : k*(R+4) ≤ h := by
    dsimp [h]
    calc k*(R+4) ≤ k*(8*R) := Nat.mul_le_mul_left _ (by omega)
         _ = R*(8*k) := by ring
         _ ≤ _ := Nat.mul_le_mul_left R budget
  have ntr : (n:ℝ)*T*gap⁻¹ ≤ (2:ℝ)^h := by
    calc
      _ ≤ (2:ℝ)^k * 2^(k*(R+2)) * 2^k := by gcongr
      _ = 2^(k*(R+4)) := by rw [← pow_add,← pow_add]; congr 1; ring
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) kh
  have entry : n.factorial*T^n/gap^n ≤ (2:ℝ)^(2*d*h) := by
    have fact : (n.factorial:ℝ) ≤ (n:ℝ)^n := by exact_mod_cast Nat.factorial_le_pow n
    calc
      _ ≤ ((n:ℝ)*T*gap⁻¹)^n := by
        rw [mul_pow,mul_pow,inv_pow,← div_eq_mul_inv]
        gcongr
      _ ≤ ((2:ℝ)^h)^n := pow_le_pow_left₀ (by positivity) ntr n
      _ = 2^(n*h) := by rw [← pow_mul,Nat.mul_comm]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right h dim)
  have khd : k ≤ d*h := by
    have a : k ≤ h := (Nat.le_mul_of_pos_right k (by omega : 0<R+4)).trans kh
    exact a.trans (Nat.le_mul_of_pos_left _ dp)
  refine ⟨entry,?_,?_,?_⟩
  · calc
      _ ≤ (2:ℝ)^(d*h) * 2^(2*d*h) := by
        apply mul_le_mul (nk.trans (pow_le_pow_right₀ (by norm_num) khd)) entry (by positivity) (by positivity)
      _ = Q := by dsimp [Q]; rw [← pow_add]; congr 1; ring
  · exact nk.trans (pow_le_pow_right₀ (by norm_num) (khd.trans (by nlinarith)))
  · have th : T ≤ (2:ℝ)^h := height.trans (pow_le_pow_right₀ (by norm_num)
        ((Nat.mul_le_mul_left k (by omega : R+2 ≤ R+4)).trans kh))
    have hpos : 0 < h := Nat.mul_pos rp bp
    calc
      _ ≤ (2:ℝ)^h + 2^h := add_le_add th (one_le_pow₀ (by norm_num))
      _ = 2^(h+1) := by rw [pow_succ]; ring
      _ ≤ Q := pow_le_pow_right₀ (by norm_num) (by nlinarith [Nat.le_mul_of_pos_left h dp])

/-- If the total rounding error is at most 2^(-P/2), the precision
inequalities in the real inverse/reconstruction theorem follow from the
actual Q and P formulas. -/
theorem local_precision {d R b n : ℕ} (dp : 1 ≤ d) (rp : 1 ≤ R) (bp : 1 ≤ b)
    (M S ε : ℝ) (mp : 0 ≤ M) (sp : 0 ≤ S) (ep : 0 ≤ ε) :
    let h := R*b
    let Q := (2:ℝ)^(3*d*h)
    let p := 32*d^3*h
    M ≤ Q → S ≤ Q → (n:ℝ) ≤ Q → ε ≤ (1/2:ℝ)^p →
    M*n*ε ≤ 1/2 ∧ M*(ε+n*(ε*(2*M*S))) < 1/(2*Q^2) := by
  intro h Q p mb sb nb ee
  have hp : 1 ≤ h := Nat.mul_pos rp bp
  have qp : 1 ≤ Q := one_le_pow₀ (by norm_num)
  have qpos : 0 < Q := zero_lt_one.trans_le qp
  have budget : 6*(3*d*h)+3 ≤ p := by
    have c1 := Nat.le_mul_of_pos_right (d*h) (show 0 < d*d by positivity)
    have c2 := Nat.mul_pos dp hp
    dsimp [p]; nlinarith
  have mass : 8*Q^6 ≤ (2:ℝ)^p := by
    calc
      _ = (2:ℝ)^(6*(3*d*h)+3) := by dsimp [Q]; rw [pow_add, ← pow_mul, Nat.mul_comm 6]; ring
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) budget
  have eweight : ε*(8*Q^6) ≤ 1 := by
    have bound : ε ≤ 1/(2:ℝ)^p := by simpa only [one_div_pow] using ee
    exact ((mul_le_mul_of_nonneg_left mass ep).trans ((le_div_iff₀ (by positivity)).mp bound))
  have q2 : 1 ≤ Q^2 := one_le_pow₀ qp
  have q3 : 1 ≤ Q^3 := one_le_pow₀ qp
  have q4 : 1 ≤ Q^4 := one_le_pow₀ qp
  have q4pos := pow_pos qpos 4
  have q2pos := pow_pos qpos 2
  constructor
  · have a : M*n*ε ≤ Q^2*ε := by rw [sq]; gcongr
    have denom := mul_le_mul_of_nonneg_left q4 (show 0 ≤ ε*Q^2 by positivity)
    nlinarith only [a,denom,eweight]
  · have a : M*(ε+n*(ε*(2*M*S))) ≤ Q*(ε+Q*(ε*(2*Q*Q))) := by gcongr
    apply (lt_div_iff₀ (by positivity)).mpr
    have scaled := mul_le_mul_of_nonneg_right a (show 0 ≤ 2*Q^2 by positivity)
    have term := mul_le_mul_of_nonneg_left q3 (show 0 ≤ ε*Q^3 by positivity)
    nlinarith only [scaled,term,eweight]


/-- Counting both sides, all possible primes and all possible residues gives
a uniform finite-row count directly from the executable marking stage. -/
theorem retained_rows {s : Marking.Input} {rel : Marking.Relations} (ok : Marking.stageOne s = some rel) :
    rel.rows.length ≤ 2*(s.B+1)^2 := by
  classical
  have same := (Marking.rows_and_guards ok).2.2.2.1
  have nodup : rel.rows.Nodup := by
    rw [same]
    exact (List.nodup_dedup _).filter _
  have bounds (i : Fin rel.rows.length) :
      (rel.rows.get i).q < s.B+1 ∧ (rel.rows.get i).r < s.B+1 := by
    have mem := rel.rows.get_mem i
    have mem' : rel.rows.get i ∈ s.clean := (congrArg (fun xs => rel.rows.get i ∈ xs) same).mp mem
    have h := Marking.mem_rows.mp (Marking.mem_clean.mp mem').1
    have q := (Marking.mem_base.mp h.1).2.2.1
    exact ⟨by omega,lt_of_lt_of_le h.2.1 (by omega)⟩
  let code (i : Fin rel.rows.length) : Bool × Fin (s.B+1) × Fin (s.B+1) :=
    ⟨(rel.rows.get i).second,⟨(rel.rows.get i).q,(bounds i).1⟩,⟨(rel.rows.get i).r,(bounds i).2⟩⟩
  have inj : Function.Injective code := by
    intro i j eq
    apply nodup.get_inj_iff.mp
    have a : (rel.rows.get i).second = (rel.rows.get j).second := congrArg Prod.fst eq
    have b : (rel.rows.get i).q = (rel.rows.get j).q :=
      congrArg (fun x : Bool × Fin (s.B+1) × Fin (s.B+1) => x.2.1.val) eq
    have c : (rel.rows.get i).r = (rel.rows.get j).r :=
      congrArg (fun x : Bool × Fin (s.B+1) × Fin (s.B+1) => x.2.2.val) eq
    cases e : rel.rows.get i
    cases e' : rel.rows.get j
    rw [e,e'] at a b c
    exact Marking.Row.mk.injEq .. |>.mpr ⟨a,b,c⟩
  simpa [sq] using Fintype.card_le_of_injective code inj

/-- Fixed-schedule geometry meets every binary height allowance eventually.
The condition d≥300 holds uniformly beyond a single finite threshold by
Fixed.degree_grows. -/
theorem fixed_envelope {N target : ℕ} {pair : TryPair.PairData} {rel : Marking.Relations}
    (ok : Marking.stageOne (TryPair.fixedInput N target pair) = some rel)
    (big : 300 ≤ Fixed.d (N.log2+1)) :
    let b := N.log2+1
    Envelope (Fixed.d b) (rel.rows.length+1) b rel.marks.length (10010*Fixed.h b) := by
  intro b
  let d := Fixed.d b
  let z := Fixed.z b
  let h := Fixed.h b
  let k := 10010*h
  have dp : 1 ≤ d := by change 300 ≤ d at big; omega
  have zp : 1 ≤ z := by simp [z,Fixed.z]
  have hp : 1 ≤ h := Nat.mul_pos dp zp
  have dz : z ≤ h := Nat.le_mul_of_pos_left _ dp
  have below : d^3*z ≤ b := (Fixed.degree_floor b).1
  have bnd : 8*k ≤ b := by
    apply le_trans _ below
    have square := Nat.pow_le_pow_left (show 300 ≤ d from big) 2
    have scaled := Nat.mul_le_mul_right (d*z) square
    dsimp [k,h,Fixed.h,d,z] at *
    nlinarith only [scaled]
  have bfit : b+1 ≤ 2^z := Nat.lt_log2_self
  have db : d ≤ b := (show d ≤ d^3*z by
    have a := Nat.le_self_pow (by decide : 3 ≠ 0) d
    exact a.trans (Nat.le_mul_of_pos_right _ zp)).trans below
  have basic : 8*d*(b+1) ≤ 2^k := by
    calc
      _ ≤ 8*(2^z)*(2^z) := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega : d ≤ 2^z)) bfit
      _ = 2^(3+z+z) := by rw [Nat.pow_add,Nat.pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by dsimp [k]; omega)
  have mark := Concrete.retained_size ok
  change rel.marks.length ≤ 2^(10000*h) at mark
  have row := retained_rows ok
  change rel.rows.length ≤ 2*(2^(1000*h)+1)^2 at row
  have largeBase : 1 ≤ 2^(1000*h) := Nat.one_le_two_pow
  have rowCap : rel.rows.length+1 ≤ 2^k := by
    calc
      _ ≤ 16*(2^(1000*h))^2 := by nlinarith
      _ = 2^(4+1000*h*2) := by rw [Nat.pow_add, Nat.pow_mul 2 (1000*h) 2]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by dsimp [k]; omega)
  exact ⟨dp,Nat.succ_pos _,bnd,Nat.succ_pos _,mark.trans (Nat.pow_le_pow_right (by decide) (by
    change 10000*h ≤ 10010*h; omega)),rowCap,((Nat.mul_le_mul_right (b+1) (Nat.mul_le_mul_right d (by decide : 2 ≤ 8))).trans basic),(Nat.mul_le_mul_left _ (Nat.add_le_add_right db 1)).trans basic⟩


/-- After projection, every actual particular or null column from stage two
has the advertised magnitude, and the last integer rounding has total error
at most 2^(-P/2) when the individual projected marks have error ≤2^(-P). -/
theorem retained_observation {s : Marking.Input} {rel : Marking.Relations}
    {out : Elimination.IntegerFamily rel.marks.length} (solved : Elimination.stageTwo rel = some out)
    {k dim : ℕ} (e : Envelope s.degree (rel.rows.length+1) s.L₀ rel.marks.length k)
    (cols : Vector (Vector ℚ dim) rel.marks.length) (row : Fin dim)
    (coeff : Vector ℤ rel.marks.length) (computed : coeff = out.particular ∨ ∃ j, coeff = out.directions.get j)
    (L : Fin rel.marks.length → ℝ) :
    let R := rel.rows.length+1
    let P := TryPair.localBits s rel
    let T := (2:ℝ)^(k*(R+2))
    let trueValue := ∑ i, (coeff.get i:ℝ) * L i
    let approx := ((Concrete.observation cols coeff P).get row:ℝ)/(2:ℝ)^P
    (∀ i, |L i| ≤ 2*s.degree*(s.L₀+1)) →
    (∀ i, |((cols.get i).get row:ℝ)-L i| ≤ (1/2:ℝ)^P) →
    |trueValue| ≤ T ∧ |approx-trueValue| ≤ (1/2:ℝ)^(P/2) ∧ |approx| ≤ T+1 := by
  intro R P T raw approx envelope close
  have heights := stageTwo_height solved
  have coeffCap (i) : |(coeff.get i:ℝ)| ≤ (R.factorial:ℝ) := by
    rcases computed with h | ⟨j,h⟩
    · rw [h]; exact_mod_cast heights.1.2 i
    · rw [h]; exact_mod_cast (heights.2 j).2 i
  have rp := e.rowCount
  have dp := e.degree
  have bp := e.bits
  have budget := e.budget
  have marks : (rel.marks.length:ℝ) ≤ (2:ℝ)^k := by exact_mod_cast e.marks_le
  have rows : (R:ℝ) ≤ (2:ℝ)^k := by exact_mod_cast e.rows_le
  have logs : 2*(s.degree:ℝ)*(s.L₀+1) ≤ (2:ℝ)^k := by exact_mod_cast e.logs_le
  have fact : (R.factorial:ℝ) ≤ (R:ℝ)^R := by exact_mod_cast R.factorial_le_pow
  have weight : (rel.marks.length:ℝ)*R.factorial ≤ (2:ℝ)^(k*(R+1)) := by
    calc
      _ ≤ (2:ℝ)^k * (2^k)^R := by gcongr; exact fact.trans (pow_le_pow_left₀ (by positivity) rows _)
      _ = _ := by rw [← pow_mul,← pow_add]; congr 1; ring
  have rawBound : |raw| ≤ T := by
    calc
      _ ≤ ∑ i, |(coeff.get i:ℝ)*L i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin rel.marks.length, (R.factorial:ℝ)*(2*s.degree*(s.L₀+1)) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul (coeffCap i) (envelope i) (abs_nonneg _) (by positivity)
      _ = (rel.marks.length * (R.factorial:ℝ))*(2*s.degree*(s.L₀+1)) := by simp; ring
      _ ≤ (2:ℝ)^(k*(R+1)) * 2^k := by gcongr
      _ = T := by dsimp [T]; rw [← pow_add]; congr 1
  let p := 32*s.degree^3*(R*s.L₀)
  have half : P = p+p := by dsimp [P,TryPair.localBits,p,R]; ring
  have expBudget : k*(R+1)+1 ≤ p := by
    have rp' : 1 ≤ R := rp
    have d1 := Nat.one_le_pow 3 s.degree dp
    have h1 : k*(R+1) ≤ R*s.L₀ := by
      calc _ ≤ k*(8*R) := Nat.mul_le_mul_left k (by omega)
           _ = R*(8*k) := by ring
           _ ≤ _ := Nat.mul_le_mul_left _ budget
    have dp' := Nat.mul_le_mul_right (R*s.L₀) d1
    have pos : 0 < R*s.L₀ := Nat.mul_pos rp' bp
    dsimp [p]; nlinarith only [h1,dp',pos]
  have plusCap : 1/2 + rel.marks.length*(R.factorial:ℝ) ≤ (2:ℝ)^p := by
    have ge1 : (1:ℝ) ≤ 2^(k*(R+1)) := one_le_pow₀ (by norm_num)
    calc
      _ ≤ (2:ℝ)^(k*(R+1)) + 2^(k*(R+1)) := by linarith
      _ = 2^(k*(R+1)+1) := by rw [pow_succ]; ring
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) expBudget
  have er := Concrete.observation_error cols coeff row P L R.factorial ((1/2:ℝ)^P) coeffCap close
  have eps : |approx-raw| ≤ (1/2:ℝ)^(P/2) := by
    apply er.trans
    rw [show P/2=p by omega,half,pow_add]
    calc
      _ = (1/2 + rel.marks.length*(R.factorial:ℝ)) * ((1/2:ℝ)^p*(1/2:ℝ)^p) := by ring
      _ ≤ 2^p * ((1/2:ℝ)^p*(1/2:ℝ)^p) := by gcongr
      _ = _ := by rw [one_div_pow]; field_simp
  have absApprox := abs_add_le (approx-raw) raw
  rw [sub_add_cancel] at absApprox
  exact ⟨rawBound,eps,(absApprox.trans (add_le_add eps rawBound)).trans (by
    linarith [pow_le_one₀ (n := P/2) (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)])⟩


/-- The exact real form used by numerical roundoff is the same normalized
Helmert row used by the integer unit-lattice gap. -/
theorem exactProjection_eq (j : ℕ) (L : ℕ → ℝ) :
    Concrete.exactProjection j L = helmertCoordinate L j := by
  simp [Concrete.exactProjection,helmertCoordinate,Real.sqrt_inv,div_eq_inv_mul]

/-- Raw logs with the bisection and log-series error proved by
RootLogs.markLog_error meet the per-mark projection requirement at the actual
two internal precision settings and the final dyadic rounding setting. -/
theorem projected_mark_precision {d R b j : ℕ} (dp : 1 ≤ d) (rp : 1 ≤ R) (bp : 1 ≤ b)
    (jp : 1 ≤ j) (jd : j ≤ d) (q : Vector ℚ d) (L : ℕ → ℝ) :
    let P := 64*d^3*R*b
    (∀ i ≤ j, |(((q.toArray[i]?.getD 0):ℚ):ℝ)-L i| ≤
      (1/2:ℝ)^(2*P+16)+(1/2:ℝ)^(2*P)/(1/2:ℝ)^(b+1)) →
    (∀ i ≤ j, |L i| ≤ b+1) →
    |((ArchNumerics.roundDyadic (Concrete.projection q j (2*P+16)) (3*P/2):ℚ):ℝ)-
      helmertCoordinate L j| ≤ (1/2:ℝ)^P ∧ |helmertCoordinate L j| ≤ 2*d*(b+1) := by
  intro P raw bound
  let p := 16*d^3*R*b
  let W := (2:ℝ)^p
  have dd := Nat.le_self_pow (by decide : 3 ≠ 0) d
  have rd := Nat.mul_le_mul_right R dd
  have rd' := Nat.le_mul_of_pos_right d rp
  have bd := Nat.le_mul_of_pos_right (d^3*R) bp
  have br : b ≤ (d^3*R)*b := Nat.le_mul_of_pos_left b (Nat.mul_pos (Nat.pow_pos dp) rp)
  have splitP : P = p*4 := by dsimp [P,p]; ring
  have mid : 3*P/2 = p*6 := by omega
  have high : 2*P = p*8 := by omega
  have bits : b+1 ≤ p := by dsimp [p]; nlinarith
  have twice : 2*j ≤ p := by dsimp [p]; nlinarith only [jd,dd,rd,rd',bd,br,bp]
  have ppos : 1 ≤ p := by omega
  have Wlo : 2 ≤ W := by
    simpa [W] using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) ppos)
  have Wp : 0 < W := by positivity
  have castW (a : ℕ) (ha : a ≤ p) : (a:ℝ) ≤ W := by
    have lt := (Nat.lt_two_pow_self (n := a)).le.trans (Nat.pow_le_pow_right (by decide) ha)
    dsimp [W]; exact_mod_cast lt
  have jW : 2*(j:ℝ) ≤ W := by exact_mod_cast castW (2*j) twice
  have bW : (b:ℝ)+1 ≤ W := by exact_mod_cast castW (b+1) bits
  have eW : (2:ℝ)^(b+1) ≤ W := pow_le_pow_right₀ (by norm_num) bits
  have powP (a : ℕ) : (1/2:ℝ)^(p*a) = 1/W^a := by rw [one_div_pow,pow_mul]
  have bits8 : (1/2:ℝ)^(2*P+16) ≤ 1/W^8 := by
    rw [← powP 8, ← high]
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  let err := (1/2:ℝ)^(2*P+16)+(1/2:ℝ)^(2*P)/(1/2:ℝ)^(b+1)
  have rawErr : err ≤ (1+W)/W^8 := by
    dsimp [err]
    calc
      _ ≤ 1/W^8 + (1/2:ℝ)^(2*P)/(1/2:ℝ)^(b+1) := add_le_add_left bits8 _
      _ = 1/W^8 + 2^(b+1)/W^8 := by rw [high,powP,one_div_pow 2 (b+1)]; simp only [div_div_eq_mul_div,div_one]; ring
      _ ≤ 1/W^8 + W/W^8 := add_le_add_right (div_le_div_of_nonneg_right eW (by positivity)) _
      _ = _ := by ring
  have proj := Concrete.projection_error q j (2*P+16) jp L err (b+1) raw bound
  rw [exactProjection_eq] at proj
  have numeric : |(Concrete.projection q j (2*P+16):ℝ)-helmertCoordinate L j| ≤ 3/W^6 := by
    apply proj.trans
    calc
      _ ≤ W*((1+W)/W^8+W*(1/W^8)) := by gcongr
      _ ≤ _ := by
        field_simp
        nlinarith [mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ W by linarith) (pow_nonneg Wp.le 7)]
  have round := Concrete.roundDyadic_real (Concrete.projection q j (2*P+16)) (3*P/2)
  rw [mid,powP] at round
  constructor
  · rw [mid]
    refine (abs_sub_le _ (Concrete.projection q j (2*P+16):ℝ) _).trans ((add_le_add round numeric).trans ?_)
    rw [splitP,powP]
    have square := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) Wlo 2
    have eq : 1/W^6/2+3/W^6 = (7/2)/W^6 := by ring
    rw [eq]
    calc
      _ ≤ W^2/W^6 := by gcongr; norm_num at square; linarith
      _ = _ := by field_simp
  · have pref : |∑ i ∈ Finset.range j, L i| ≤ j*((b:ℝ)+1) := by
      apply (Finset.abs_sum_le_sum_abs ..).trans
      simpa [mul_add] using Finset.sum_le_sum (fun i (h : i ∈ Finset.range j) => bound i (Finset.mem_range.mp h).le)
    have jp' : (1:ℝ) ≤ j := by exact_mod_cast jp
    have root : 1 ≤ Real.sqrt ((j:ℝ)*(j+1)) := by
      apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
      nlinarith
    rw [helmertCoordinate,abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (div_le_iff₀ (zero_lt_one.trans_le root)).mpr
    have part := abs_sub (∑ i ∈ Finset.range j, L i) (j*L j)
    simp only [abs_mul,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) j)] at part
    have bnd := part.trans (add_le_add pref (mul_le_mul_of_nonneg_left (bound j le_rfl) (Nat.cast_nonneg j)))
    have jd' : (j:ℝ) ≤ d := by exact_mod_cast jd
    calc
      _ ≤ 2*(j:ℝ)*(b+1) := by linarith
      _ ≤ 2*(d:ℝ)*(b+1) := by gcongr
      _ ≤ _ := le_mul_of_one_le_right (by positivity) root


/-- A separated normalized distance inside the root interval bounds the
natural logarithm needed in every numerical call. -/
theorem separated_log_bound {b : ℕ} {x : ℝ}
    (separated : (1/2:ℝ)^(b+1) ≤ x) (bounded : x ≤ 2) : |Real.log x| ≤ b+1 := by
  have positive : 0 < x := (by positivity : (0:ℝ)<(1/2:ℝ)^(b+1)).trans_le separated
  have log2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have upper := (Real.log_le_log positive bounded).trans log2
  have lower := Real.log_le_log (by positivity : (0:ℝ)<(1/2:ℝ)^(b+1)) separated
  rw [Real.log_pow,Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub,Nat.cast_add,Nat.cast_one] at lower
  have small := mul_le_mul_of_nonneg_left log2 (by positivity : 0 ≤ (b:ℝ)+1)
  exact abs_le.mpr ⟨by nlinarith,by linarith [Nat.cast_nonneg (α:=ℝ) b]⟩

/-- The archimedean solve at the actual fixed input recovers the exact
unit-coordinate denominators for a full selected integer unit minor.
The concrete projection lemmas supply the entry and right-hand-side bounds. -/
theorem fixed_selected_reconstruction {K₁ K₂ ι : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂] [IsTotallyReal K₁] [IsTotallyReal K₂] [Fintype ι] [DecidableEq ι]
    {N target : ℕ} {pair : TryPair.PairData} {rel : Marking.Relations}
    (marked : Marking.stageOne (TryPair.fixedInput N target pair) = some rel)
    (big : 300 ≤ Fixed.d (N.log2+1))
    (p₁ : Fin (Fixed.d (N.log2+1)) ≃ InfinitePlace K₁)
    (p₂ : Fin (Fixed.d (N.log2+1)) ≃ InfinitePlace K₂)
    (code : ι ≃ Fin (Fixed.d (N.log2+1)-1) ⊕ Fin (Fixed.d (N.log2+1)-1))
    (basis : Module.Basis ι ℤ (UnitClass K₁ × UnitClass K₂)) (v : ι → UnitClass K₁ × UnitClass K₂)
    (t : UnitClass K₁ × UnitClass K₂) (nz : (basis.toMatrix v).det ≠ 0) (C : Matrix ι ι ℝ) (s : ι → ℝ) :
    let b := N.log2+1
    let R := rel.rows.length+1
    let T := (2:ℝ)^((10010*Fixed.h b)*(R+2))
    let P := TryPair.localBits (TryPair.fixedInput N target pair) rel
    let Q := TryPair.denominatorCap (TryPair.fixedInput N target pair) rel
    let obs := observeUnitPair (orderedRealEmbeddings p₁) (orderedRealEmbeddings p₂) (pairedHelmertMatrix code)
    let B := Matrix.of (fun i j => obs (v j) i)
    let ε := (1/2:ℝ)^(P/2)
    (∀ i j, |B i j| ≤ T) → (∀ i j, |C i j-B i j| ≤ ε) →
    (∀ i, |s i+obs t i| ≤ ε) → (∀ i, |s i| ≤ T+1) →
    C.det ≠ 0 ∧ ∀ y : ι → ℚ, C *ᵥ (fun j => (y j : ℝ)) = s →
      ∃ x : ι → ℚ, (∀ j, (basis.repr t j : ℚ) + ∑ i, (basis.repr (v i) j : ℚ)*x i = 0) ∧
        (∀ i, (x i).den ≤ Q) ∧ (∀ i, |y i-x i| < 1/(2*(Q:ℚ)^2)) ∧
        Reconstruction.multiplier y Q = some (Finset.univ.lcm (fun i => (x i).den)) ∧
        Finset.univ.lcm (fun i => (x i).den) ≤ Q := by
  intro b R T P Q obs B ε entries close rhs rhsSize
  let d := Fixed.d b
  let n := Fintype.card ι
  let gap := Real.log 2 / (4*d*(d+1))
  let M := (n:ℝ)*(n.factorial*T^n/gap^n)
  have env := fixed_envelope marked big
  have dp : 1 ≤ d := env.degree
  have rp : 1 ≤ R := env.rowCount
  have bp : 1 ≤ b := env.bits
  have gp : 0 < gap := by dsimp [gap]; positivity
  have tp : 1 ≤ T := one_le_pow₀ (by norm_num)
  have tq : 0 ≤ T := zero_le_one.trans tp
  have card : n ≤ 2*d := by
    dsimp [n]
    rw [Fintype.card_congr code,Fintype.card_sum,Fintype.card_fin]
    change d-1+(d-1) ≤ 2*d
    omega
  have hQ : (Q:ℝ) = (2:ℝ)^(3*d*(R*b)) := by
    change ((2^(3*d*R*b):ℕ):ℝ) = _
    push_cast
    rw [Nat.mul_assoc (3*d)]
  have hP : P/2 = 32*d^3*(R*b) := by
    change 64*d^3*R*b/2 = _
    have e : 64*d^3*R*b = 32*d^3*(R*b)+32*d^3*(R*b) := by ring
    omega
  have ⟨index,Mcap,ncap,Scap⟩ := arch_height env card T tp le_rfl
  have both := paired_helmert_minor_bounds p₁ p₂ code basis v nz T entries
  have Qcap : (basis.toMatrix v).det.natAbs ≤ Q := by
    have cap : |((basis.toMatrix v).det:ℝ)| ≤ (Q:ℝ) := by
      rw [hQ]
      exact (both.2.trans index).trans (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right (R*b) (Nat.mul_le_mul_right d (by decide : 2 ≤ 3))))
    simpa only [← Nat.cast_le (α:=ℝ),Nat.cast_natAbs,Int.cast_abs] using cap
  have ep : 0 ≤ ε := by dsimp [ε]; positivity
  have mp : 0 ≤ M := by dsimp [M]; positivity
  have numerical := local_precision (n:=n) dp rp bp M (T+1) ε mp (by positivity) ep
    Mcap Scap ncap (by dsimp [ε]; rw [hP])
  exact apriori_archimedean_reconstruction basis v t obs nz Q Qcap C s T (gap^n) ε (T+1) tp
    (pow_pos gp _) ep (by positivity) entries both.1 close rhs rhsSize numerical.1 (hQ ▸ numerical.2)

end ArchPrecision
end Cogentic
