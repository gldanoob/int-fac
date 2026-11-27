import Cogentic.RandomizedCappedEpoch

namespace Cogentic.RandomizedCappedEpoch

/-- Deterministic execution on blocks from a tape. Only missed attempts read
the next block, and the recursion is total for every possible tape. -/
def runTape {α β : Type*} (attempt : α → Option β × ℕ) (fallback : Unit → β × ℕ) :
    (r : ℕ) → (Fin r → α) → β × ℕ
  | 0, _ => fallback ()
  | r+1, tape =>
    let a := attempt (tape 0)
    match a.1 with
    | some b => (b, a.2+1)
    | none =>
      let tail := runTape attempt fallback r (fun j => tape j.succ)
      (tail.1, a.2+1+tail.2)

/-- Tail-recursive execution keeps the original tape, its current position
and the charge accumulated so far. -/
def runFrom {α β : Type*} (attempt : α → Option β × ℕ) (fallback : Unit → β × ℕ)
    (tape : ℕ → α) : (r start used : ℕ) → β × ℕ
  | 0, _, used =>
    let b := fallback ()
    (b.1, used+b.2)
  | r+1, start, used =>
    let a := attempt (tape start)
    match a.1 with
    | some b => (b, used+(a.2+1))
    | none => runFrom attempt fallback tape r (start+1) (used+(a.2+1))

theorem runFrom_eq_runTape {α β : Type*} (attempt : α → Option β × ℕ)
    (fallback : Unit → β × ℕ) (tape : ℕ → α) (r start used : ℕ) :
    runFrom attempt fallback tape r start used =
      let b := runTape attempt fallback r (fun i => tape (start+i.val))
      (b.1, used+b.2) := by
  induction r generalizing start used with
  | zero => rfl
  | succ r ih =>
    simp only [runFrom, runTape, Fin.val_zero, Nat.add_zero]
    cases h : (attempt (tape start)).1 with
    | some b => rfl
    | none =>
      have index (i : Fin r) : start+1+i.val = start+i.succ.val := by simp; omega
      simp only [ih, index, Nat.add_assoc]

/-- Product law of finitely many independent epoch blocks, used only to
interpret the tape. The program reads a prefix of these blocks. -/
noncomputable def blockLaw {α : Type*} (epoch : PMF α) : (r : ℕ) → PMF (Fin r → α)
  | 0 => PMF.pure Fin.elim0
  | r+1 => epoch.bind fun a => (blockLaw epoch r).map (Fin.cons a)

theorem runTape_law {α β : Type*} (epoch : PMF α) (attempt : α → Option β × ℕ)
    (fallback : Unit → β × ℕ) (r : ℕ) :
    (blockLaw epoch r).map (runTape attempt fallback r) = run epoch attempt fallback r := by
  induction r with
  | zero => rw [blockLaw, PMF.pure_map]; rfl
  | succ r ih =>
    rw [blockLaw, PMF.map_bind, run]
    congr 1
    funext a
    rw [PMF.map_comp]
    cases h : (attempt a).1 with
    | some b =>
      simp only [h]
      have hc : runTape attempt fallback (r+1) ∘ Fin.cons a =
          Function.const (Fin r → α) (b, (attempt a).2+1) := by
        funext tape
        simp [runTape, h]
      rw [hc, PMF.map_const]
    | none =>
      simp only [h]
      rw [← ih, PMF.map_comp]
      congr 1
      funext tape
      simp [runTape, h]

/-- A pathwise ceiling on all possible input blocks also bounds every
execution on tapes of probability zero. -/
theorem runTape_work_le {α β : Type*} (attempt : α → Option β × ℕ)
    (fallback : Unit → β × ℕ) (W : ℕ) (hW : ∀ a, (attempt a).2+1 ≤ W)
    (r : ℕ) (tape : Fin r → α) :
    (runTape attempt fallback r tape).2 ≤ r*W+(fallback ()).2 := by
  induction r with
  | zero => simp [runTape]
  | succ r ih =>
    rw [runTape, Nat.succ_mul]
    have h := hW (tape 0)
    cases e : (attempt (tape 0)).1 with
    | none =>
      have ht := ih (fun j => tape j.succ)
      change (attempt (tape 0)).2+1+(runTape attempt fallback r (fun j => tape j.succ)).2 ≤ _
      omega
    | some b =>
      change (attempt (tape 0)).2+1 ≤ _
      omega

#print axioms runTape_law
#print axioms runTape_work_le

end Cogentic.RandomizedCappedEpoch
