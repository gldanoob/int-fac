import Std

namespace TwoThirdsWindow

/-- A natural number greater than one with only the divisors one and itself. -/
def Prime (p : Nat) : Prop :=
  1 < p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

/-- Positive squarefree integers all of whose prime divisors are eligible. -/
def Supported (eligible : Nat → Prop) (n : Nat) : Prop :=
  0 < n ∧ ∀ p, Prime p → p ∣ n → eligible p ∧ ¬ p*p ∣ n

private theorem prime_coprime {p b : Nat} (hp : Prime p) (h : ¬ p ∣ b) :
    p.Coprime b := by
  rcases hp.2 (p.gcd b) (Nat.gcd_dvd_left _ _) with one | eq
  · exact one
  · exact False.elim (h (eq ▸ Nat.gcd_dvd_right p b))

private theorem prime_dvd_mul {p a b : Nat} (hp : Prime p) (hab : p ∣ a*b) :
    p ∣ a ∨ p ∣ b := by
  by_cases h : p ∣ a
  · exact Or.inl h
  · exact Or.inr ((prime_coprime hp h).dvd_of_dvd_mul_left hab)

private theorem supported_of_dvd {eligible : Nat → Prop} {m n : Nat}
    (hn : Supported eligible n) (hm : m ∣ n) : Supported eligible m := by
  refine ⟨Nat.pos_of_dvd_of_pos hm hn.1, ?_⟩
  intro p hp hpm
  obtain ⟨mem, sq⟩ := hn.2 p hp (Nat.dvd_trans hpm hm)
  exact ⟨mem, fun bad => sq (Nat.dvd_trans bad hm)⟩

private theorem supported_mul {eligible : Nat → Prop} {g m q : Nat}
    (hg : Supported eligible g) (hm : Supported (fun p => eligible p ∧ ¬ p ∣ q) m)
    (hgq : g ∣ q) : Supported eligible (g*m) := by
  refine ⟨Nat.mul_pos hg.1 hm.1, ?_⟩
  intro p hp hd
  rcases prime_dvd_mul hp hd with hpg | hpm
  · obtain ⟨mem, sq⟩ := hg.2 p hp hpg
    have cop : p.Coprime m := prime_coprime hp fun hpm =>
      (hm.2 p hp hpm).1.2 (Nat.dvd_trans hpg hgq)
    exact ⟨mem, fun bad => sq ((Nat.coprime_mul_iff_left.mpr ⟨cop, cop⟩).dvd_of_dvd_mul_right bad)⟩
  · obtain ⟨⟨mem, outside⟩, sq⟩ := hm.2 p hp hpm
    have cop : p.Coprime g := prime_coprime hp fun hpg => outside (Nat.dvd_trans hpg hgq)
    exact ⟨mem, fun bad => sq ((Nat.coprime_mul_iff_left.mpr ⟨cop, cop⟩).dvd_of_dvd_mul_left bad)⟩

private theorem gcd_of_same_class {n r q : Nat} (h : n % q = r % q) :
    n.gcd q = r.gcd q := by
  calc
    n.gcd q = (n % q).gcd q := (Nat.gcd_comm n q).trans (Nat.gcd_rec q n)
    _ = (r % q).gcd q := congrArg (fun a : Nat => a.gcd q) h
    _ = r.gcd q := ((Nat.gcd_comm r q).trans (Nat.gcd_rec q r)).symm

private theorem cancel_class {g n r q : Nat} (pos : 0 < g)
    (hn : g ∣ n) (hr : g ∣ r) (hq : g ∣ q) :
    n % q = r % q ↔ (n/g) % (q/g) = (r/g) % (q/g) := by
  have scale (a : Nat) (ha : g ∣ a) : a % q = g*((a/g) % (q/g)) := by
    calc
      a % q = (g*(a/g)) % (g*(q/g)) := by rw [Nat.mul_div_cancel' ha, Nat.mul_div_cancel' hq]
      _ = _ := Nat.mul_mod_mul_left ..
  rw [scale n hn, scale r hr]
  exact ⟨Nat.eq_of_mul_eq_mul_left pos, congrArg (g * ·)⟩

/-- The divided residue and modulus are always relatively prime, including when r = 0. -/
theorem reduced_class_coprime (r q : Nat) (hq : 0 < q) :
    (r / r.gcd q).Coprime (q / r.gcd q) :=
  Nat.gcd_div_gcd_div_gcd_of_pos_right hq

/-- Exact change of variables for a nonunit class in a squarefree smooth window.
    The quotient excludes primes of the entire original modulus. -/
theorem divide_squarefree_class (eligible : Nat → Prop) (n r q : Nat) (hq : 0 < q) :
    let g := r.gcd q
    n % q = r % q ∧ Supported eligible n ↔
      g ∣ n ∧ (n/g) % (q/g) = (r/g) % (q/g) ∧ Supported eligible g ∧
      Supported (fun p => eligible p ∧ ¬ p ∣ q) (n/g) := by
  let g := r.gcd q
  have pos : 0 < g := Nat.gcd_pos_of_pos_right _ hq
  have hr : g ∣ r := Nat.gcd_dvd_left ..
  have hmod : g ∣ q := Nat.gcd_dvd_right ..
  constructor
  · rintro ⟨hc, hs⟩
    have eq : n.gcd q = g := gcd_of_same_class hc
    have hn : g ∣ n := eq ▸ Nat.gcd_dvd_left n q
    have product : g * (n/g) = n := Nat.mul_div_cancel' hn
    have quotient : (n/g) ∣ n := Nat.div_dvd_of_dvd hn
    have part := supported_of_dvd hs quotient
    refine ⟨hn, (cancel_class pos hn hr hmod).mp hc, supported_of_dvd hs hn, part.1, ?_⟩
    intro p hp hpm
    obtain ⟨mem, sq⟩ := part.2 p hp hpm
    refine ⟨⟨mem, ?_⟩, sq⟩
    intro hpq
    have hpn := Nat.dvd_trans hpm quotient
    have hpg : p ∣ g := eq ▸ Nat.dvd_gcd hpn hpq
    exact (hs.2 p hp hpn).2 (product ▸ Nat.mul_dvd_mul hpg hpm)
  · rintro ⟨hn, hc, hg, hm⟩
    exact ⟨(cancel_class pos hn hr hmod).mpr hc,
      Nat.mul_div_cancel' hn ▸ supported_mul hg hm hmod⟩

/-- The weighted sum over the first `count` nonnegative members of a progression. -/
noncomputable def progressionMass {α : Type} [Zero α] [Add α]
    (eligible : Nat → Prop) (r q count : Nat) (weight : Nat → α) : α := by
  classical
  exact ((List.range count).map (fun i =>
    let n := r % q + q*i
    if Supported eligible n then weight n else 0)).sum

/-- Every finite partial sum has the reindexed weights, in the same order. -/
theorem divide_progression_mass {α : Type} [Zero α] [Add α]
    (eligible : Nat → Prop) (r q count : Nat) (weight : Nat → α) (hq : 0 < q)
    (hg : Supported eligible (r.gcd q)) :
    let g := r.gcd q
    progressionMass eligible r q count weight =
      progressionMass (fun p => eligible p ∧ ¬ p ∣ q) (r/g) (q/g) count (fun m => weight (g*m)) := by
  classical
  let g := r.gcd q
  have pos : 0 < g := Nat.gcd_pos_of_pos_right _ hq
  have hgq : g ∣ q := Nat.gcd_dvd_right ..
  have hgr : g ∣ r := Nat.gcd_dvd_left ..
  have scale : g*((r/g) % (q/g)) = r % q := by
    rw [← Nat.mul_mod_mul_left, Nat.mul_div_cancel' hgr, Nat.mul_div_cancel' hgq]
  simp only [progressionMass]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  let m := (r/g) % (q/g) + (q/g)*i
  let n := r % q + q*i
  have prod : g*m = n := by
    dsimp only [m,n]
    rw [Nat.mul_add, scale, ← Nat.mul_assoc, Nat.mul_div_cancel' hgq]
  have div : n/g = m := by rw [← prod, Nat.mul_div_cancel_left _ pos]
  have same : n % q = r % q := by simp [n]
  have support : Supported eligible n ↔ Supported (fun p => eligible p ∧ ¬ p ∣ q) m := by
    constructor
    · intro h
      exact div ▸ ((divide_squarefree_class eligible n r q hq).mp ⟨same, h⟩).2.2.2
    · intro h
      exact prod ▸ supported_mul hg h hgq
  change (if Supported eligible n then weight n else 0) =
    (if Supported (fun p => eligible p ∧ ¬ p ∣ q) m then weight (g*m) else 0)
  rw [propext support, prod]

end TwoThirdsWindow
