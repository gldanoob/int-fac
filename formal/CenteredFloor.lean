import Std

namespace CenteredFloor

/-- Divide the identity in either order. The error is less than one unit of q. -/
private theorem scaled_floor {n q z u e : Int} (hn : 0 < n) (hq : 0 < q)
    (h : n*z = q*u+e) (he : 0 ≤ e) (heq : e < q) : z/q = u/n := by
  have swap (x : Int) : x/n/q = x/q/n := by
    simp [Int.ediv_ediv, show ¬n < 0 by omega, show ¬q < 0 by omega, Int.mul_comm n q]
  have left : (n*z)/n = z := by
    simpa using Int.mul_add_ediv_left z 0 (by omega : n ≠ 0)
  have right : (n*z)/q = u := by
    rw [h, Int.mul_add_ediv_left u e (by omega : q ≠ 0), Int.ediv_eq_zero_of_lt he heq]
    simp
  simpa [left, right] using swap (n*z)

private theorem prev_floor {u n : Int} (hn : 0 < n) :
    (u-1)/n = u/n - (if u%n = 0 then 1 else 0) := by
  obtain ⟨lo, hi⟩ := (Int.ediv_eq_iff_of_pos hn).mp (rfl : u/n = u/n)
  have decomp := Int.emod_add_ediv_mul u n
  split <;> apply (Int.ediv_eq_iff_of_pos hn).mpr <;> grind

/-- Each symmetric pair contributes one bit exactly at a root of c² modulo n. -/
theorem pair {n K c x : Int} (hn : 3 ≤ n) (hc : 1 ≤ c) (hcK : c ≤ K)
    (hx : 1 ≤ x) (hxn : 4*x ≤ n) :
    let a := K^2*n
    let q := a*n+1
    let C := K*n*c
    (a*(C-x)^2/q + a*(C+x)^2/q) % 2 =
      if (x^2-c^2)%n = 0 then 1 else 0 := by
  intro a q C
  let B := K*n
  have hK : 1 ≤ K := by omega
  have hB : n ≤ B := by simpa [B] using Int.mul_le_mul_of_nonneg_right hK (by omega : 0 ≤ n)
  have hBc : 2*c ≤ B := by
    have := Int.mul_le_mul_of_nonneg_left (show 2 ≤ n by omega) (by omega : 0 ≤ K)
    dsimp [B]
    grind
  have hBx : 4*x ≤ B := by omega
  have hcx : 4*(c*x) ≤ B := by
    have := Int.mul_le_mul hcK hxn (by omega : 0 ≤ 4*x) (by omega : 0 ≤ K)
    dsimp [B]
    grind
  have hC : B ≤ C := by
    simpa [C,B] using Int.mul_le_mul_of_nonneg_left hc (by omega : 0 ≤ B)
  have hcross := Int.mul_le_mul_of_nonneg_left hcx (by omega : 0 ≤ B)
  have hcsq := Int.mul_le_mul hBc hBc (by omega : 0 ≤ 2*c) (by omega : 0 ≤ B)
  have hxsq := Int.mul_le_mul hBx hBx (by omega : 0 ≤ 4*x) (by omega : 0 ≤ B)
  have lowerX := Int.mul_le_mul_of_nonneg_right (by omega : x ≤ C) (by omega : 0 ≤ x)
  have lowerC := Int.mul_le_mul_of_nonneg_right (by omega : c ≤ B) (by omega : 0 ≤ c)
  have hCx := Int.mul_le_mul_of_nonneg_left hx (by omega : 0 ≤ C)
  have hxx := Int.sq_nonneg x
  have hcc := Int.sq_nonneg c
  have hBsq : 0 < B*B := Int.mul_pos (by omega) (by omega)
  have eqQ : q = B^2+1 := by dsimp [B,q,a]; grind
  have hq : 0 < q := by rw [eqQ]; grind
  have sqC : C^2 = (q-1)*c^2 := by dsimp [C,q,a]; grind
  have shift : C = B*c := rfl
  have boundsMinus : 0 ≤ q*c^2-(C-x)^2 ∧ q*c^2-(C-x)^2 < q := by
    grind
  have boundsPlus : 0 ≤ q*c^2+q-(C+x)^2 ∧ q*c^2+q-(C+x)^2 < q := by
    grind
  let u := x^2-c^2
  have minus := scaled_floor (z := a*(C-x)^2) (u := (C-x)^2-c^2)
    (by omega : 0<n) hq (by dsimp [q,a]; grind) boundsMinus.1 boundsMinus.2
  have plus := scaled_floor (z := a*(C+x)^2) (u := (C+x)^2-c^2-1)
    (by omega : 0<n) hq (by dsimp [q,a]; grind) boundsPlus.1 boundsPlus.2
  have em : (C-x)^2-c^2 = n*(K*c*(C-2*x)) + u := by dsimp [C,u]; grind
  have ep : (C+x)^2-c^2-1 = n*(K*c*(C+2*x)) + (u-1) := by dsimp [C,u]; grind
  rw [minus, plus, em, ep, Int.mul_add_ediv_left _ _ (by omega),
    Int.mul_add_ediv_left _ _ (by omega), prev_floor (by omega : 0<n)]
  have even : K*c*(C-2*x) + K*c*(C+2*x) = 2*(K*c*C) := by grind
  change _ = if u%n=0 then 1 else 0
  by_cases h : u%n = 0 <;> simp only [h, ite_true, ite_false] <;> omega

/-- Sum a function on consecutive integers starting at the given endpoint. -/
def intervalSum (F : Int → Int) (start : Int) : Nat → Int
  | 0 => 0
  | len+1 => F start + intervalSum F (start+1) len

private theorem intervalSum_last (F : Int → Int) (start : Int) (len : Nat) :
    intervalSum F start (len+1) = intervalSum F start len + F (start+len) := by
  induction len generalizing start with
  | zero => simp [intervalSum]
  | succ len ih =>
    rw [intervalSum, ih, intervalSum]
    simp [Int.add_assoc, Int.add_comm 1 (len : Int)]

/-- The centered interval's parity after removing its midpoint counts positive roots. -/
theorem centered {n K c : Int} (m : Nat) (hn : 3 ≤ n) (hc : 1 ≤ c) (hcK : c ≤ K)
    (hm : 4*(m : Int) ≤ n) :
    let a := K^2*n
    let C := K*n*c
    let F := fun t : Int => a*t^2/(a*n+1)
    (intervalSum F (C-m) (2*m+1) - F C) % 2 =
      ((List.range' 1 m).countP (fun x : Nat => (((x : Int)^2-c^2)%n == 0)) : Int) % 2 := by
  intro a C F
  induction m with
  | zero => simp [intervalSum]
  | succ m ih =>
    have ih' := ih (by omega)
    have hp := pair hn hc hcK (show (1 : Int) ≤ ((m+1 : Nat) : Int) by omega) hm
    change (F (C-((m+1 : Nat) : Int)) + F (C+((m+1 : Nat) : Int)))%2 = _ at hp
    rw [show 2*(m+1)+1 = (2*m+1+1)+1 by omega, intervalSum, intervalSum_last]
    rw [show C-((m+1 : Nat) : Int)+1 = C-m by omega,
        show C-(m : Int)+((2*m+1 : Nat) : Int) = C+((m+1 : Nat) : Int) by omega]
    rw [List.range'_concat, List.countP_append, List.countP_singleton]
    simp only [Nat.one_mul, Nat.add_comm 1 m, beq_iff_eq]
    by_cases root : (((m+1 : Nat) : Int)^2 - c^2)%n = 0 <;>
      simp only [root, ite_true, ite_false] at hp ⊢ <;> omega

/-- The outer quarters detect equality of the next two binary digits of z/n. -/
theorem adjacent {n : Int} (z : Int) (hn : 0 < n) (hodd : n%2=1) :
    (2*z/n)%2 = (4*z/n)%2 ↔ z%n ≤ n/4 ∨ n-z%n ≤ n/4 := by
  let s := z%n
  have hs : 0 ≤ s := Int.emod_nonneg _ (by omega)
  have hsn : s < n := Int.emod_lt_of_pos _ hn
  have decomp := Int.emod_add_ediv_mul z n
  have shift (k : Int) : k*z/n = k*s/n + k*(z/n) := by
    have factor : k*z = k*s + n*(k*(z/n)) := by
      dsimp [s]
      have := congrArg (k * ·) decomp
      grind
    rw [factor, Int.add_mul_ediv_left _ _ (by omega)]
  rw [shift 2, shift 4]
  change _ ↔ s ≤ n/4 ∨ n-s ≤ n/4
  by_cases first : 2*s < n
  · have h2 := Int.ediv_eq_zero_of_lt (by omega : 0≤2*s) first
    by_cases outer : 4*s < n
    · have h4 := Int.ediv_eq_zero_of_lt (by omega : 0≤4*s) outer
      omega
    · have h4 : 4*s/n=1 := (Int.ediv_eq_iff_of_pos hn).mpr (by omega)
      omega
  · have h2 : 2*s/n=1 := (Int.ediv_eq_iff_of_pos hn).mpr (by omega)
    by_cases outer : 3*n ≤ 4*s
    · have h4 : 4*s/n=3 := (Int.ediv_eq_iff_of_pos hn).mpr (by omega)
      omega
    · have h4 : 4*s/n=2 := (Int.ediv_eq_iff_of_pos hn).mpr (by omega)
      omega

/-- Assemble the prefix from equality bits, starting with a known zero digit. -/
def decode (same : Nat → Bool) : Nat → Int
  | 0 => 0
  | j+1 =>
    let word := decode same j
    2*word + (if same j then word%2 else 1-word%2)

/-- After j answers the word is the first j+1 binary digits of r/n. -/
theorem decode_eq {n r : Int} (hn : 0 < n) (hodd : n%2=1)
    (hr : 0 ≤ r) (hhalf : 2*r < n) (same : Nat → Bool)
    (answers : ∀ j, same j = decide (
      (2^j*r)%n ≤ n/4 ∨ n-(2^j*r)%n ≤ n/4)) (j : Nat) :
    decode same j = 2^(j+1)*r/n := by
  induction j with
  | zero =>
    simpa [decode] using (Int.ediv_eq_zero_of_lt (by omega : 0≤2*r) hhalf).symm
  | succ j ih =>
    let z := 2^j*r
    have prev : 2^(j+1)*r = 2*z := by dsimp [z]; rw [Int.pow_succ]; grind
    have next : 2^(j+1+1)*r = 4*z := by rw [Int.pow_succ]; grind
    have half : 4*z/n/2 = 2*z/n := by
      have swap : 4*z/n/2 = 4*z/2/n := by
        simp [Int.ediv_ediv, show ¬n < 0 by omega, Int.mul_comm n 2]
      rw [swap, show 4*z = 2*(2*z)+0 by grind, Int.mul_add_ediv_left _ _ (by decide)]
      simp
    have parity := Int.emod_add_ediv_mul (4*z/n) 2
    rw [half] at parity
    have criterion := adjacent z hn hodd
    rw [decode, ih, prev, next, answers]
    change 2*(2*z/n) + (if decide (z%n ≤ n/4 ∨ n-z%n ≤ n/4) then _ else _) = 4*z/n
    by_cases h : z%n ≤ n/4 ∨ n-z%n ≤ n/4
    · have := criterion.mpr h
      simp [h]
      omega
    · have := fun (e : (2*z/n)%2 = (4*z/n)%2) => h (criterion.mp e)
      simp [h]
      omega

end CenteredFloor
