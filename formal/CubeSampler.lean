import Std

namespace CubeSampler

def Cube : Nat → Type
  | 0 => Unit
  | n+1 => Bool × Cube n

def zero : (n : Nat) → Cube n
  | 0 => ()
  | n+1 => (false, zero n)

def xor : (n : Nat) → Cube n → Cube n → Cube n
  | 0, _, _ => ()
  | n+1, a, b => (a.1 ^^ b.1, xor n a.2 b.2)

def phase : (n : Nat) → Cube n → Cube n → Int
  | 0, _, _ => 1
  | n+1, a, b => (if a.1 && b.1 then -1 else 1) * phase n a.2 b.2

def sum : (n : Nat) → (Cube n → Int) → Int
  | 0, f => f ()
  | n+1, f => sum n (fun x => f (false,x)) + sum n (fun x => f (true,x))

def energy (n : Nat) (f : Cube n → Int) : Int := sum n (fun x => f x ^ 2)

def walsh : (n : Nat) → (Cube n → Int) → Cube n → Int
  | 0, f, _ => f ()
  | n+1, f, c =>
    walsh n (fun x => f (false,x)) c.2 +
      (if c.1 then -1 else 1) * walsh n (fun x => f (true,x)) c.2

private theorem sum_add (n) (f g : Cube n → Int) :
    sum n (fun x => f x + g x) = sum n f + sum n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sum]; rw [ih, ih]; omega

private theorem sum_scale (n) (t : Int) (f : Cube n → Int) :
    sum n (fun x => t * f x) = t * sum n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sum]; rw [ih, ih]; grind

private theorem sum_mono (n) (f g : Cube n → Int) (h : ∀ x, f x ≤ g x) :
    sum n f ≤ sum n g := by
  induction n with
  | zero => exact h ()
  | succ n ih =>
    exact Int.add_le_add (ih _ _ fun x => h (false,x)) (ih _ _ fun x => h (true,x))

private theorem sum_const (n) (t : Int) : sum n (fun _ => t) = 2^n * t := by
  induction n with
  | zero => simp [sum]
  | succ n ih => simp only [sum, ih, Int.pow_succ]; grind

theorem parseval (n) (f : Cube n → Int) :
    energy n (walsh n f) = 2^n * energy n f := by
  induction n with
  | zero => simp [energy,sum,walsh]
  | succ n ih =>
    let a := walsh n (fun x => f (false,x))
    let b := walsh n (fun x => f (true,x))
    change sum n (fun x => (a x + 1 * b x)^2) +
           sum n (fun x => (a x + (-1) * b x)^2) = _
    rw [←sum_add]
    have h : (fun x => (a x + 1 * b x)^2 + (a x + (-1)*b x)^2) =
        (fun x => 2*(a x ^ 2 + b x ^ 2)) := by funext x; grind
    rw [h, sum_scale, sum_add]
    change 2*(energy n a + energy n b) = 2^(n+1) *
      (energy n (fun x => f (false,x)) + energy n (fun x => f (true,x)))
    unfold a b
    rw [ih, ih, Int.pow_succ]; grind

private theorem walsh_add (n) (f g : Cube n → Int) (c) :
    walsh n (fun x => f x + g x) c = walsh n f c + walsh n g c := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [walsh]; rw [ih, ih]; grind

private theorem walsh_shift (n) (f : Cube n → Int) (s c) :
    walsh n (fun x => f (xor n x s)) c = phase n c s * walsh n f c := by
  induction n with
  | zero => simp [walsh,phase,xor]
  | succ n ih =>
    obtain ⟨sc,s⟩ := s
    obtain ⟨cc,c⟩ := c
    have h₀ := ih (fun x => f (false,x)) s c
    have h₁ := ih (fun x => f (true,x)) s c
    cases sc <;> cases cc <;> simp [walsh,phase,xor,h₀,h₁] <;> grind

private theorem walsh_zero (n) (f : Cube n → Int) :
    walsh n f (zero n) = sum n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp [walsh, zero, ih, sum]

def visits (n : Nat) (shifts : List (Cube n)) (f : Cube n → Int) (x : Cube n) : Int :=
  match shifts with
  | [] => 0
  | s :: ss => f (xor n x s) + visits n ss f x

def bias (n : Nat) (shifts : List (Cube n)) (c : Cube n) : Int :=
  (shifts.map (fun s => phase n c s)).sum

private theorem walsh_const_zero (n) (c) : walsh n (fun _ => 0) c = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [walsh, ih]

private theorem walsh_visits (n) (shifts : List (Cube n)) (f : Cube n → Int) (c) :
    walsh n (visits n shifts f) c = bias n shifts c * walsh n f c := by
  induction shifts with
  | nil => simp [visits,bias,walsh_const_zero]
  | cons s ss ih =>
    change walsh n (fun x => f (xor n x s) + visits n ss f x) c = _
    rw [walsh_add, walsh_shift, ih]
    simp only [bias,List.map_cons,List.sum_cons]; grind

theorem energy_contraction (n) (shifts : List (Cube n)) (bound : Int)
    (hb : ∀ c, c ≠ zero n → bias n shifts c ^ 2 ≤ bound^2)
    (f : Cube n → Int) (centered : sum n f = 0) :
    energy n (visits n shifts f) ≤ bound^2 * energy n f := by
  have col (c : Cube n) : walsh n (visits n shifts f) c ^ 2 ≤
      bound^2 * (walsh n f c)^2 := by
    rw [walsh_visits]
    by_cases z : c = zero n
    · simp [z,walsh_zero,centered]
    · have hs := Int.mul_le_mul_of_nonneg_right (hb c z) (Int.sq_nonneg (walsh n f c))
      grind
  have h := sum_mono n _ _ col
  rw [sum_scale] at h
  change energy n (walsh n (visits n shifts f)) ≤ bound^2 * energy n (walsh n f) at h
  rw [parseval,parseval] at h
  have pos : (0:Int) < 2^n := Int.pow_pos (by decide : (0:Int) < 2)
  exact (Int.mul_le_mul_left pos).mp (by simpa only [Int.mul_left_comm] using h)

def indicator (n) (hit : Cube n → Bool) (x : Cube n) : Int := if hit x then 1 else 0

def missed (n) (shifts : List (Cube n)) (hit : Cube n → Bool) (x : Cube n) : Bool :=
  shifts.all (fun s => !(hit (xor n x s)))

private theorem missed_visits (n) (shifts : List (Cube n)) (hit : Cube n → Bool)
    (x : Cube n) (d a : Int) (h : missed n shifts hit x = true) :
    visits n shifts (fun v => d * indicator n hit v - a) x = -(shifts.length : Int) * a := by
  induction shifts with
  | nil => simp [visits]
  | cons s ss ih =>
    simp [missed] at h
    have hs := h.1
    have rest : missed n ss hit x = true := by
      simpa [missed] using h.2
    change d * indicator n hit (xor n x s) - a +
      visits n ss (fun v => d * indicator n hit v - a) x = _
    rw [ih rest]
    simp [indicator,hs]; grind

/-- A deterministic collection of shifts whose nontrivial character sums are at most
    B in absolute value misses at most D(D-A)B²/(A times the squared list length)
    starting words, for a nonempty target of size A in a cube of size D. -/
theorem missing_starts (n) (shifts : List (Cube n)) (bound : Int)
    (hb : ∀ c, c ≠ zero n → bias n shifts c ^ 2 ≤ bound^2)
    (hit : Cube n → Bool) (ha : 0 < sum n (indicator n hit)) :
    sum n (indicator n (missed n shifts hit)) * sum n (indicator n hit) * (shifts.length : Int)^2 ≤
      (2:Int)^n * (2^n - sum n (indicator n hit)) * bound^2 := by
  let d : Int := 2^n
  let a := sum n (indicator n hit)
  let g := fun v => d * indicator n hit v - a
  have centered : sum n g = 0 := by
    change sum n (fun v => d * indicator n hit v + -a) = 0
    rw [sum_add, sum_scale, sum_const]; change d*a+d*(-a)=0; grind
  have square_fn : (fun v => g v ^ 2) =
      (fun v => (d^2-2*d*a)*indicator n hit v+a^2) := by
    funext v; cases h : hit v <;> simp [g,indicator,h] <;> grind
  have energy_g : energy n g = d*a*(d-a) := by
    unfold energy
    rw [square_fn, sum_add, sum_scale, sum_const]
    change (d^2-2*d*a)*a+d*a^2 = d*a*(d-a); grind
  let m := missed n shifts hit
  have lower (x : Cube n) : (((shifts.length : Int)*a)^2) * indicator n m x ≤
      visits n shifts g x ^ 2 := by
    cases hx : m x with
    | false => simpa [indicator,hx] using Int.sq_nonneg (visits n shifts g x)
    | true =>
      have hv := missed_visits n shifts hit x d a hx
      change visits n shifts g x = _ at hv
      simp only [indicator,hx,ite_true,Int.mul_one,hv]; grind
  have lo := sum_mono n _ _ lower
  rw [sum_scale] at lo
  change _ ≤ energy n (visits n shifts g) at lo
  have up := energy_contraction n shifts bound hb g centered
  rw [energy_g] at up
  have comb := Int.le_trans lo up
  change sum n (indicator n m)*a*(shifts.length : Int)^2 ≤ d*(d-a)*bound^2
  apply (Int.mul_le_mul_left ha).mp
  change a * (sum n (indicator n m)*a*(shifts.length : Int)^2) ≤ a * (d*(d-a)*bound^2)
  grind

end CubeSampler
