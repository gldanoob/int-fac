import Cogentic.RandomizedRestartBudget

namespace Cogentic.Randomized

/-- Decode the positive service tick `t+1` by scanning its trailing zero bits.
The return values are the job index and the zero-based unit within that job. -/
def dyadicServiceAt (t : ℕ) : ℕ × ℕ :=
  if t % 2 = 0 then (0, t / 2)
  else
    let p := dyadicServiceAt (t / 2)
    (p.1 + 1, p.2)
termination_by t
decreasing_by omega

@[simp] theorem dyadicServiceAt_even (n : ℕ) : dyadicServiceAt (2*n) = (0,n) := by
  rw [dyadicServiceAt]
  simp

@[simp] theorem dyadicServiceAt_odd (n : ℕ) :
    dyadicServiceAt (2*n+1) = ((dyadicServiceAt n).1+1, (dyadicServiceAt n).2) := by
  rw [dyadicServiceAt]
  simp [Nat.add_div]

theorem dyadicServiceSlot_at (t : ℕ) :
    dyadicServiceSlot (dyadicServiceAt t).1 (dyadicServiceAt t).2 = t+1 := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    rcases Nat.mod_two_eq_zero_or_one t with he | ho
    · obtain ⟨n, rfl⟩ : ∃ n, t = 2*n := ⟨t / 2, by omega⟩
      simp [dyadicServiceSlot]
    · have hrec := ih (t / 2) (by omega)
      obtain ⟨n, rfl⟩ : ∃ n, t = 2*n+1 := ⟨t / 2, by omega⟩
      have hd : (2*n+1)/2 = n := by omega
      rw [hd] at hrec
      simp only [dyadicServiceAt_odd, dyadicServiceSlot, pow_succ] at *
      nlinarith only [hrec]

theorem dyadicServiceAt_slot (j k : ℕ) :
    dyadicServiceAt (dyadicServiceSlot j k - 1) = (j,k) := by
  apply dyadicServiceSlot_injective
  have hpos : 0 < dyadicServiceSlot j k := by unfold dyadicServiceSlot; positivity
  simpa [Nat.sub_add_cancel hpos] using dyadicServiceSlot_at (dyadicServiceSlot j k - 1)

/-- Each decoder visit examines one low bit, including its final odd bit. -/
def serviceBitInspections (T : ℕ) := ∑ t ∈ Finset.range T, ((dyadicServiceAt t).1 + 1)

private theorem serviceBitInspections_even (m : ℕ) :
    serviceBitInspections (2*m) = 2*m + serviceBitInspections m := by
  induction m with
  | zero => simp [serviceBitInspections]
  | succ m ih =>
    unfold serviceBitInspections at *
    rw [Nat.mul_succ]
    simp only [Finset.sum_range_succ, dyadicServiceAt_odd, dyadicServiceAt_even, ih]
    omega

/-- The first T ticks take at most 2T low-bit inspections in total. -/
theorem serviceBitInspections_le (T : ℕ) : serviceBitInspections T ≤ 2*T := by
  induction T using Nat.strong_induction_on with
  | h T ih =>
    by_cases hT : T = 0
    · simp [hT, serviceBitInspections]
    have hrec := ih (T / 2) (by omega)
    rcases Nat.mod_two_eq_zero_or_one T with he | ho
    · obtain ⟨m, rfl⟩ : ∃ m, T = 2*m := ⟨T/2, by omega⟩
      rw [serviceBitInspections_even]
      have hd : 2*m/2 = m := by omega
      rw [hd] at hrec
      omega
    · obtain ⟨m, rfl⟩ : ∃ m, T = 2*m+1 := ⟨T/2, by omega⟩
      have hd : (2*m+1)/2 = m := by omega
      rw [hd] at hrec
      change (∑ t ∈ Finset.range (2*m+1), _) ≤ _
      rw [Finset.sum_range_succ]
      change serviceBitInspections (2*m) + ((dyadicServiceAt (2*m)).1+1) ≤ _
      rw [serviceBitInspections_even, dyadicServiceAt_even]
      simpa using (show 2*m + serviceBitInspections m + (0+1) ≤ 2*(2*m+1) by omega)

/-- At the scheduled tick of unit `k`, exactly `k+1` ticks have served job `j`. -/
theorem serviceCount_at_slot (j k : ℕ) :
    ((Finset.range (dyadicServiceSlot j k)).filter
      (fun t ↦ (dyadicServiceAt t).1 = j)).card = k+1 := by
  classical
  let tick := fun l ↦ dyadicServiceSlot j l - 1
  have hpos (l : ℕ) : 0 < dyadicServiceSlot j l := by unfold dyadicServiceSlot; positivity
  have hmono : StrictMono (dyadicServiceSlot j) := by
    intro x y hxy
    unfold dyadicServiceSlot
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
  have htick (l : ℕ) : dyadicServiceAt (tick l) = (j,l) := dyadicServiceAt_slot j l
  have heq : (Finset.range (dyadicServiceSlot j k)).filter
      (fun t ↦ (dyadicServiceAt t).1 = j) = (Finset.range (k+1)).image tick := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨ht, hj⟩
      have hslot := dyadicServiceSlot_at t
      rw [hj] at hslot
      refine ⟨(dyadicServiceAt t).2, ?_, ?_⟩
      · exact Nat.lt_succ_of_le (hmono.le_iff_le.mp (hslot ▸ Nat.succ_le_of_lt ht))
      · simp [tick, hslot]
    · rintro ⟨l, hl, rfl⟩
      have hle := hmono.monotone (show l ≤ k by omega)
      have hlt : tick l < dyadicServiceSlot j k := by
        dsimp [tick]
        have := hpos l
        omega
      exact ⟨hlt, congrArg Prod.fst (htick l)⟩
  have hinj : Function.Injective tick := by
    intro l n h
    exact congrArg Prod.snd ((htick l).symm.trans ((congrArg dyadicServiceAt h).trans (htick n)))
  rw [heq, Finset.card_image_of_injective _ hinj, Finset.card_range]

end Cogentic.Randomized

#print axioms Cogentic.Randomized.serviceCount_at_slot
#print axioms Cogentic.Randomized.serviceBitInspections_le
