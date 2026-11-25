import Std

namespace TwoThirdsFactor

/-- The divisor definition of primality for natural numbers. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

/-- A decision for one input, with a checked prime or a proper divisor. -/
inductive Decision (n : Nat) where
  | prime (h : IsPrime n)
  | split (d : Nat) (proper : 1 < d ∧ d < n) (divides : d ∣ n)

/-- One node for each call to the decision procedure. -/
inductive Run : Nat → Type where
  | prime (p : Nat) (h : IsPrime p) : Run p
  | split {a b : Nat} (left : Run a) (right : Run b) : Run (a * b)

def factor (step : (n : Nat) → 2 ≤ n → Decision n) (n : Nat) (hn : 2 ≤ n) : Run n :=
  match step n hn with
  | .prime h => .prime n h
  | .split d proper divides => by
    have eq : d * (n / d) = n := by rw [Nat.mul_comm, Nat.div_mul_cancel divides]
    have hq : 2 ≤ n / d := by
      cases h : n / d with
      | zero => simp [h] at eq; omega
      | succ k => cases k with
        | zero => simp [h] at eq; omega
        | succ k => omega
    exact eq ▸ Run.split (factor step d proper.1) (factor step (n/d) hq)
termination_by n
decreasing_by
  · exact proper.2
  · exact Nat.div_lt_self (by omega) proper.1

def Run.factors : {n : Nat} → Run n → List Nat
  | _, .prime p _ => [p]
  | _, .split l r => l.factors ++ r.factors

theorem Run.correct {n : Nat} (t : Run n) :
    t.factors.prod = n ∧ ∀ p ∈ t.factors, IsPrime p := by
  induction t with
  | prime p h => simpa [Run.factors] using h
  | split l r hl hr =>
    simp only [Run.factors, List.prod_append, hl.1, hr.1, true_and, List.mem_append]
    exact fun p hp => hp.elim (hl.2 p) (hr.2 p)

/-- Charge the actual argument at each call, including the primality decisions. -/
def Run.work (charge : Nat → Nat) : {n : Nat} → Run n → Nat
  | _, .prime p _ => charge p
  | _, @Run.split a b l r => charge (a*b) + l.work charge + r.work charge

private theorem Run.size_bounds {n : Nat} (t : Run n) :
    2 ≤ n ∧ 2 ^ t.factors.length ≤ n ∧ t.work (fun _ => 1) + 1 = 2 * t.factors.length := by
  induction t with
  | prime _ h => exact ⟨h.1, h.1, rfl⟩
  | @split a b l r hl hr =>
    simp only [Run.factors, List.length_append, Nat.pow_add, Run.work]
    exact ⟨(by have := Nat.mul_le_mul hl.1 hr.1; omega),
      Nat.mul_le_mul hl.2.1 hr.2.1, by omega⟩

private theorem Run.work_le_calls {n cap : Nat} (t : Run n) (charge : Nat → Nat)
    (bound : ∀ a, 2 ≤ a → a ≤ n → charge a ≤ cap) :
    t.work charge ≤ t.work (fun _ => 1) * cap := by
  induction t with
  | prime p hp => simpa [Run.work] using bound p hp.1 (Nat.le_refl _)
  | @split a b l r hl hr =>
    have hab : a ≤ a*b := Nat.le_mul_of_pos_right _ (by have := r.size_bounds.1; omega)
    have hba : b ≤ a*b := Nat.le_mul_of_pos_left _ (by have := l.size_bounds.1; omega)
    have hc := bound (a*b) ((Run.split l r).size_bounds.1) (Nat.le_refl _)
    have hL := hl (fun k hk hka => bound k hk (Nat.le_trans hka hab))
    have hR := hr (fun k hk hkb => bound k hk (Nat.le_trans hkb hba))
    simp only [Run.work, Nat.add_mul, Nat.one_mul]
    omega

theorem Run.work_bound {n cap : Nat} (t : Run n) (charge : Nat → Nat)
    (bound : ∀ a, 2 ≤ a → a ≤ n → charge a ≤ cap) :
    t.work charge ≤ (2 * n.log2 - 1) * cap := by
  have ⟨hn, hpow, hc⟩ := t.size_bounds
  have hlen := (Nat.le_log2 (by omega : n ≠ 0)).2 hpow
  exact Nat.le_trans (t.work_le_calls charge bound) (Nat.mul_le_mul_right cap (by omega))

private theorem coprime_of_distinct_primes {p q : Nat} (hp : IsPrime p) (hq : IsPrime q)
    (hne : p ≠ q) : p.Coprime q := by
  rcases hp.2 _ (Nat.gcd_dvd_left p q) with h | h
  · exact h
  · have hd := Nat.gcd_dvd_right p q
    rw [h] at hd
    rcases hq.2 p hd with h1 | h2
    · have := hp.1; omega
    · exact False.elim (hne h2)

private theorem prime_list_multiplicity {p : Nat} (hp : IsPrime p) (xs : List Nat)
    (primes : ∀ q ∈ xs, IsPrime q) (k : Nat) : p ^ k ∣ xs.prod ↔ k ≤ xs.count p := by
  induction xs generalizing k with
  | nil =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.prod_nil, List.count_nil]
      constructor
      · intro h
        have := Nat.eq_one_of_dvd_one (Nat.dvd_of_pow_dvd (by omega) h)
        have := hp.1; omega
      · omega
  | cons q xs ih =>
    have hq := primes q (by simp)
    have rest := ih (fun r hr => primes r (by simp [hr]))
    by_cases h : q = p
    · subst q
      cases k with
      | zero => simp
      | succ k =>
        simp only [List.prod_cons, List.count_cons_self, Nat.pow_succ, Nat.mul_comm (p^k) p,
          Nat.mul_dvd_mul_iff_left (by have := hp.1; omega : 0 < p), Nat.add_le_add_iff_right]
        exact rest k
    · have hc := coprime_of_distinct_primes hp hq (Ne.symm h)
      simp [h, List.prod_cons]
      exact ⟨fun hd => (rest k).1 ((hc.pow_left k).dvd_of_dvd_mul_left hd),
        fun hk => Nat.dvd_mul_left_of_dvd ((rest k).2 hk) q⟩

/-- Counting repeated leaves gives precisely the prime-power divisibility of the input. -/
theorem Run.multiplicity {n p : Nat} (t : Run n) (hp : IsPrime p) (k : Nat) :
    p ^ k ∣ n ↔ k ≤ t.factors.count p := by
  have h := prime_list_multiplicity hp t.factors t.correct.2 k
  rwa [t.correct.1] at h

/-- The charge covers the decision on each visited integer and any local recursion work.
    Instantiating it with the constant one counts the decision calls. -/
theorem factor_correct_and_cost (step : (n : Nat) → 2 ≤ n → Decision n)
    (n : Nat) (hn : 2 ≤ n) (charge : Nat → Nat) (cap : Nat)
    (bound : ∀ a, 2 ≤ a → a ≤ n → charge a ≤ cap) :
    let t := factor step n hn
    t.factors.prod = n ∧ (∀ p ∈ t.factors, IsPrime p) ∧
      (∀ p, IsPrime p → ∀ k, p ^ k ∣ n ↔ k ≤ t.factors.count p) ∧
      t.work charge ≤ (2 * n.log2 - 1) * cap := by
  let t := factor step n hn
  exact ⟨t.correct.1, t.correct.2, fun _ hp k => t.multiplicity hp k, t.work_bound charge bound⟩

end TwoThirdsFactor

#print axioms TwoThirdsFactor.factor_correct_and_cost
