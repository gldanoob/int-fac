import ModularPower

namespace TwoThirdsSearch

inductive Proposal where
  | gcdWith (z : Nat)
  | exponent (e : Nat)

def ProperDivisor (n d : Nat) : Prop := 1 < d ∧ d < n ∧ d ∣ n

def ValidExponent (n g e : Nat) : Prop := 2 ≤ e ∧ 2 ∣ e ∧ ModularPower.powMod g e n = 1

inductive Hit (n g : Nat) where
  | divisor (d : Nat) (h : ProperDivisor n d)
  | exponent (e : Nat) (h : ValidExponent n g e)

def verify (n g : Nat) : Option Proposal → Option (Hit n g)
  | none => none
  | some (.gcdWith z) =>
    let d := n.gcd z
    if h : 1 < d ∧ d < n then some (.divisor d ⟨h.1, h.2, Nat.gcd_dvd_left _ _⟩)
    else none
  | some (.exponent e) =>
    if h : 2 ≤ e ∧ 2 ∣ e ∧ ModularPower.powMod g e n = 1 then some (.exponent e h) else none

theorem verify_exponent {n g e : Nat} (h : ValidExponent n g e) :
    verify n g (some (.exponent e)) ≠ none := by
  simp [verify, h.1, h.2.1, h.2.2]

/-- The counter increments only when a four-coordinate candidate is inspected. -/
structure Probe (α : Type) where
  answer : Option α
  calls : Nat

private def scan (f : Nat → Probe α) : List Nat → Probe α
  | [] => ⟨none, 0⟩
  | x :: xs =>
    let hit := f x
    match hit.answer with
    | some _ => hit
    | none =>
      let tail := scan f xs
      ⟨tail.answer, hit.calls + tail.calls⟩

private theorem scan_none {f : Nat → Probe α} {xs : List Nat} :
    (scan f xs).answer = none ↔ ∀ x ∈ xs, (f x).answer = none := by
  induction xs with
  | nil => simp [scan]
  | cons a xs ih => cases h : (f a).answer <;> simp [scan, h, ih]

private theorem scan_cost {f : Nat → Probe α} (xs : List Nat) (cap : Nat)
    (bound : ∀ x, (f x).calls ≤ cap) : (scan f xs).calls ≤ xs.length * cap := by
  induction xs with
  | nil => simp [scan]
  | cons a xs ih =>
    have ha := bound a
    cases h : (f a).answer <;> simp [scan, h, Nat.succ_mul] <;> omega

private theorem scan_range_cost {f : Nat → Probe α} {size cap : Nat}
    (bound : ∀ x, (f x).calls ≤ cap) : (scan f (List.range' 1 size)).calls ≤ size * cap := by
  simpa using scan_cost (List.range' 1 size) cap bound

abbrev TryPair := Nat → Nat → Nat → Nat → Nat → Option Proposal

/-- Visit [1,W₀] × [1,W₁] twice in lexicographic order, stopping at the first verified hit. -/
def searchBox (n w₀ w₁ : Nat) (attempt : TryPair) (g : Nat) : Probe (Hit n g) :=
  let slow := List.range' 1 w₀
  let fast := List.range' 1 w₁
  scan (fun a => scan (fun b => scan (fun c => scan (fun d =>
    ⟨verify n g (attempt g a b c d), 1⟩) fast) slow) fast) slow

def BoxWitness (n w₀ w₁ : Nat) (attempt : TryPair) (g : Nat) : Prop :=
  ∃ a b c d, (1 ≤ a ∧ a ≤ w₀) ∧ (1 ≤ b ∧ b ≤ w₁) ∧
    (1 ≤ c ∧ c ≤ w₀) ∧ (1 ≤ d ∧ d ≤ w₁) ∧ verify n g (attempt g a b c d) ≠ none

theorem searchBox_complete {n w₀ w₁ g : Nat} {attempt : TryPair}
    (witness : BoxWitness n w₀ w₁ attempt g) : (searchBox n w₀ w₁ attempt g).answer ≠ none := by
  obtain ⟨a,b,c,d,ha,hb,hc,hd,hit⟩ := witness
  intro missing
  simp only [searchBox, scan_none, List.mem_range'_1] at missing
  exact hit (missing a (by omega) b (by omega) c (by omega) d (by omega))

theorem searchBox_cost (n w₀ w₁ g : Nat) (attempt : TryPair) :
    (searchBox n w₀ w₁ attempt g).calls ≤ w₀ * (w₁ * (w₀ * w₁)) := by
  unfold searchBox
  apply scan_range_cost
  intro a
  apply scan_range_cost
  intro b
  apply scan_range_cost
  intro c
  simpa using scan_cost (List.range' 1 w₁) 1
    (f := fun d => ⟨verify n g (attempt g a b c d), 1⟩) (fun _ => Nat.le_refl 1)

private theorem power_multiple {n g e m : Nat} (hn : 2 ≤ n) (h : ModularPower.powMod g e n = 1)
    (dvd : e ∣ m) : ModularPower.powMod g m n = 1 := by
  obtain ⟨k, rfl⟩ := dvd
  rw [ModularPower.powMod_def] at h ⊢
  rw [Nat.pow_mul, Nat.pow_mod, h, Nat.one_pow, Nat.mod_eq_of_lt (by omega)]

/-- Every output carries a checked divisor or a common even exponent for exactly the retained list. -/
inductive Output (n : Nat) where
  | divisor (d : Nat) (h : ProperDivisor n d)
  | orders (m : Nat) (big : 2 ≤ m) (even : 2 ∣ m) (retained : List Nat)
      (valid : ∀ g ∈ retained, ModularPower.powMod g m n = 1)

private def addExponent {n g e : Nat} (hn : 2 ≤ n) (he : ValidExponent n g e) :
    Output n → Output n
  | .divisor d h => .divisor d h
  | .orders m big even gs valid => by
    let common := e.lcm m
    have pos : 0 < common := Nat.lcm_pos (by have := he.1; omega) (by omega)
    have em : e ∣ common := Nat.dvd_lcm_left _ _
    have mm : m ∣ common := Nat.dvd_lcm_right _ _
    refine .orders common (Nat.le_trans big (Nat.le_of_dvd pos mm)) (Nat.dvd_trans even mm)
      (g :: gs) ?_
    intro q hq
    rcases List.mem_cons.mp hq with h | h
    · subst q; exact power_multiple hn he.2.2 em
    · exact power_multiple hn (valid q h) mm

def collect {n : Nat} (hn : 2 ≤ n) (search : (g : Nat) → Probe (Hit n g)) :
    List Nat → Output n × Nat
  | [] => (.orders 2 (by decide) (Nat.dvd_refl 2) [] (by simp), 0)
  | g :: gs =>
    let head := search g
    match head.answer with
    | some (.divisor d h) => (.divisor d h, head.calls)
    | none =>
      let tail := collect hn search gs
      (tail.1, head.calls + tail.2)
    | some (.exponent _ he) =>
      let tail := collect hn search gs
      (addExponent hn he tail.1, head.calls + tail.2)

def Output.covers {n : Nat} (gs : List Nat) : Output n → Prop
  | .divisor .. => True
  | .orders _ _ _ retained _ => retained = gs

private theorem covers_cons {n g e : Nat} (hn : 2 ≤ n) (he : ValidExponent n g e)
    (gs : List Nat) (out : Output n) (h : out.covers gs) : (addExponent hn he out).covers (g :: gs) := by
  cases out <;> simp_all [addExponent, Output.covers]

theorem collect_complete {n : Nat} (hn : 2 ≤ n) (search : (g : Nat) → Probe (Hit n g))
    (gs : List Nat) (covered : ∀ g ∈ gs, (search g).answer ≠ none) :
    (collect hn search gs).1.covers gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have tail := ih (fun q hq => covered q (by simp [hq]))
    have head := covered g (by simp)
    cases h : (search g).answer with
    | none => exact False.elim (head h)
    | some candidate =>
      cases candidate with
      | divisor d hd => simp [collect, h, Output.covers]
      | exponent e he => simpa only [collect, h] using covers_cons hn he gs _ tail

theorem collect_cost {n : Nat} (hn : 2 ≤ n) (search : (g : Nat) → Probe (Hit n g))
    (gs : List Nat) (cap : Nat) (bound : ∀ g, (search g).calls ≤ cap) :
    (collect hn search gs).2 ≤ gs.length * cap := by
  induction gs with
  | nil => simp [collect]
  | cons g gs ih =>
    have hg := bound g
    cases h : (search g).answer with
    | none => simp only [collect, h, List.length_cons, Nat.succ_mul]; omega
    | some candidate =>
      cases candidate <;> simp only [collect, h, List.length_cons, Nat.succ_mul] <;> omega

/-- The Cogentic box has coordinate bounds 2 L₀² U A and 2 L₀² U in each field. -/
theorem gaussian_generator_search {n : Nat} (hn : 2 ≤ n) (L₀ U A : Nat)
    (generators : List Nat) (attempt : TryPair)
    (covered : ∀ g ∈ generators, BoxWitness n (2*L₀^2*U*A) (2*L₀^2*U) attempt g) :
    let run := collect hn (searchBox n (2*L₀^2*U*A) (2*L₀^2*U) attempt) generators
    run.1.covers generators ∧ run.2 ≤ generators.length * (16*L₀^8*U^4*A^2) := by
  constructor
  · exact collect_complete hn _ generators (fun g hg => searchBox_complete (covered g hg))
  · apply Nat.le_trans (collect_cost hn _ generators _ (fun g => searchBox_cost _ _ _ g attempt))
    apply Nat.le_of_eq
    congr 1
    change (2*L₀^2*U*A)*((2*L₀^2*U)*((2*L₀^2*U*A)*(2*L₀^2*U))) = (2*2*2*2)*L₀^8*U^4*A^2
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    ac_rfl

private theorem scan_preserves {f : Nat → Probe α} {good : α → Prop} (xs : List Nat)
    (step : ∀ x h, (f x).answer = some h → good h) :
    ∀ h, (scan f xs).answer = some h → good h := by
  induction xs with
  | nil => simp [scan]
  | cons a xs ih =>
    cases e : (f a).answer with
    | none => simpa [scan,e] using ih
    | some h => simpa [scan,e] using step a h e

def Hit.exponentLe {n g : Nat} (cap : Nat) : Hit n g → Prop
  | .divisor .. => True
  | .exponent e _ => e ≤ cap

theorem searchBox_exponentLe (n w₀ w₁ g cap : Nat) (attempt : TryPair)
    (bounded : ∀ a b c d e, attempt g a b c d = some (.exponent e) → e ≤ cap) :
    ∀ h, (searchBox n w₀ w₁ attempt g).answer = some h → h.exponentLe cap := by
  unfold searchBox
  apply scan_preserves
  intro a
  apply scan_preserves
  intro b
  apply scan_preserves
  intro c
  apply scan_preserves
  intro d h hit
  change verify n g (attempt g a b c d) = some h at hit
  cases eq : attempt g a b c d with
  | none => simp [eq,verify] at hit
  | some proposal =>
    cases proposal with
    | gcdWith z =>
      simp only [eq,verify] at hit
      split at hit <;> cases hit
      trivial
    | exponent e =>
      simp only [eq,verify] at hit
      split at hit <;> cases hit
      exact bounded a b c d e eq

def Output.exponentLe {n : Nat} (cap : Nat) : Output n → Prop
  | .divisor .. => True
  | .orders e .. => e ≤ cap

private theorem addExponent_bound {n g e bound cap : Nat} (hn : 2 ≤ n)
    (he : ValidExponent n g e) (size : e ≤ cap) (out : Output n) (old : out.exponentLe bound) :
    (addExponent hn he out).exponentLe (cap*bound) := by
  cases out with
  | divisor => trivial
  | orders m big _ _ _ =>
    change m ≤ bound at old
    exact Nat.le_trans (Nat.lcm_le_mul (m := e) (n := m) (by have := he.1; omega) (by omega))
      (Nat.mul_le_mul size old)

/-- At the actual lcm accumulator, each verified exponent contributes at most
    its own bit length, even when some generators have no hit. -/
theorem collect_exponentLe {n cap : Nat} (hn : 2 ≤ n) (search : (g : Nat) → Probe (Hit n g))
    (gs : List Nat) (pos : 0 < cap)
    (bounded : ∀ g h, (search g).answer = some h → h.exponentLe cap) :
    (collect hn search gs).1.exponentLe (2*cap^gs.length) := by
  induction gs with
  | nil => simp [collect,Output.exponentLe]
  | cons g gs ih =>
    simp only [List.length_cons, Nat.pow_succ, ← Nat.mul_assoc]
    cases hit : (search g).answer with
    | none =>
      simp only [collect,hit]
      cases h : (collect hn search gs).1 with
      | divisor => trivial
      | orders =>
        rw [h] at ih
        exact Nat.le_trans ih (Nat.le_mul_of_pos_right _ pos)
    | some h =>
      have small := bounded g h hit
      cases h with
      | divisor => simp [collect,hit,Output.exponentLe]
      | exponent e good =>
        simp only [collect,hit]
        rw [Nat.mul_comm _ cap]
        exact addExponent_bound hn good small _ ih

end TwoThirdsSearch

#print axioms TwoThirdsSearch.gaussian_generator_search
