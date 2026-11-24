import Std

-- At each step choose a tape that leaves at most half the inputs uncovered.
theorem tapeCover {Input Tape : Type} (hit : Tape → Input → Bool)
    (halve : ∀ xs : List Input, ∃ t : Tape,
      2 * (xs.filter (fun x => !(hit t x))).length ≤ xs.length)
    (k : Nat) (xs : List Input) (small : xs.length < 2 ^ k) :
    ∃ ts : List Tape, ts.length ≤ k ∧ ∀ x ∈ xs, ∃ t ∈ ts, hit t x = true := by
  induction k generalizing xs with
  | zero =>
    simp at small
    subst xs
    exact ⟨[], by simp⟩
  | succ k ih =>
    obtain ⟨t, h⟩ := halve xs
    rw [Nat.pow_succ] at small
    obtain ⟨ts, size, cover⟩ := ih (xs.filter (fun x => !(hit t x))) (by omega)
    refine ⟨t :: ts, by simp; omega, ?_⟩
    intro x hx
    cases e : hit t x with
    | true => exact ⟨t, by simp, e⟩
    | false =>
      have mem : x ∈ xs.filter (fun y => !(hit t y)) := by simp [hx, e]
      obtain ⟨u, hu, yes⟩ := cover x mem
      exact ⟨u, List.mem_cons_of_mem _ hu, yes⟩

-- Count missed (tape, input) pairs by tape, then add one column by input.
private def missedPairs {I T : Type} (miss : T → I → Bool) (ts : List T) (xs : List I) : Nat :=
  (ts.map (fun t => xs.countP (miss t))).sum

private theorem missedPairs_cons {I T : Type} (miss : T → I → Bool) (ts : List T)
    (x : I) (xs : List I) :
    missedPairs miss ts (x :: xs) = missedPairs miss ts xs + ts.countP (fun t => miss t x) := by
  induction ts with
  | nil => simp [missedPairs]
  | cons t ts ih =>
    simp only [missedPairs, List.map_cons, List.sum_cons] at ih ⊢
    simp only [List.countP_cons] at ih ⊢
    omega

-- If at most half of a nonempty finite tape list misses each input,
-- choose the cover entirely from that list.
theorem finiteTapeCover {I T : Type} (hit : T → I → Bool) (pool : List T)
    (nonempty : 0 < pool.length)
    (density : ∀ x, 2 * pool.countP (fun t => !(hit t x)) ≤ pool.length)
    (k : Nat) (xs : List I) (small : xs.length < 2 ^ k) :
    ∃ ts : List T, ts.length ≤ k ∧ (∀ t ∈ ts, t ∈ pool) ∧
      ∀ x ∈ xs, ∃ t ∈ ts, hit t x = true := by
  let miss := fun t x => !(hit t x)
  have total (ys : List I) : 2 * missedPairs miss pool ys ≤ pool.length * ys.length := by
    induction ys with
    | nil =>
      have zero (ts : List T) : missedPairs miss ts [] = 0 := by
        induction ts with
        | nil => rfl
        | cons t ts ih => simpa [missedPairs] using ih
      simp [zero]
    | cons x ys ih =>
      rw [missedPairs_cons, List.length_cons, Nat.mul_succ]
      have h := density x
      change 2 * pool.countP (fun t => miss t x) ≤ pool.length at h
      omega
  have halve (ys : List I) : ∃ t : {t // t ∈ pool},
      2 * (ys.filter (fun x => !(hit t.val x))).length ≤ ys.length := by
    apply Classical.byContradiction
    intro absent
    have each (t : T) (ht : t ∈ pool) : ys.length + 1 ≤ 2 * ys.countP (miss t) := by
      rw [List.countP_eq_length_filter]
      have h : ¬ 2 * (ys.filter (miss t)).length ≤ ys.length := fun h => absent ⟨⟨t, ht⟩, h⟩
      omega
    have lower (us : List T) (inside : ∀ t ∈ us, t ∈ pool) :
        us.length * (ys.length + 1) ≤ 2 * missedPairs miss us ys := by
      induction us with
      | nil => simp [missedPairs]
      | cons u us ih =>
        have h := each u (inside u (by simp))
        have rest := ih (fun t ht => inside t (by simp [ht]))
        simp only [List.length_cons, Nat.succ_mul, missedPairs, List.map_cons, List.sum_cons] at *
        omega
    have low := lower pool (fun _ ht => ht)
    rw [Nat.mul_succ] at low
    have high := total ys
    omega
  obtain ⟨us, size, covers⟩ := tapeCover (fun (t : {t // t ∈ pool}) x => hit t.val x) halve k xs small
  refine ⟨us.map Subtype.val, by simpa using size, ?_, ?_⟩
  · intro t ht
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp ht
    exact u.property
  · intro x hx
    obtain ⟨u, hu, yes⟩ := covers x hx
    exact ⟨u.val, List.mem_map.mpr ⟨u, hu, rfl⟩, yes⟩
