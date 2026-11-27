import Cogentic.RandomizedServiceDecoder

namespace Cogentic.Randomized

/-- Advance the selected job by one transition. Unvisited jobs have the common
initial state, which may itself represent a job awaiting initialization. -/
def advanceServiceState {S : Type*} (initial : S) (transition : S → S) :
    ℕ → List S → List S
  | 0, [] => [transition initial]
  | 0, x :: xs => transition x :: xs
  | j+1, [] => initial :: advanceServiceState initial transition j []
  | j+1, x :: xs => x :: advanceServiceState initial transition j xs

theorem advanceServiceState_read {S : Type*} (initial : S) (transition : S → S)
    (j i : ℕ) (xs : List S) :
    (advanceServiceState initial transition j xs).getD i initial =
      if i = j then transition (xs.getD i initial) else xs.getD i initial := by
  induction j generalizing i xs with
  | zero => cases xs <;> cases i <;> simp [advanceServiceState, List.getD_eq_getElem?_getD]
  | succ j ih =>
    cases xs with
    | nil =>
      cases i with
      | zero => simp [advanceServiceState]
      | succ i => simpa [advanceServiceState] using ih i []
    | cons x xs =>
      cases i with
      | zero => simp [advanceServiceState]
      | succ i => simpa [advanceServiceState] using ih i xs

/-- State of the multiplexed jobs after a bounded prefix of actual ticks. -/
def serviceStates {S : Type*} (initial : S) (step : ℕ → S → S) : ℕ → List S
  | 0 => []
  | t+1 =>
    let j := (dyadicServiceAt t).1
    advanceServiceState initial (step j) j (serviceStates initial step t)

/-- The selected job receives one transition on each of its ticks. All of its
other state, including any random-tape position, is saved between ticks. -/
theorem serviceStates_read {S : Type*} (initial : S) (step : ℕ → S → S) (j t : ℕ) :
    (serviceStates initial step t).getD j initial =
      (step j)^[((Finset.range t).filter (fun u ↦ (dyadicServiceAt u).1 = j)).card] initial := by
  induction t with
  | zero => simp [serviceStates]
  | succ t ih =>
    rw [serviceStates, advanceServiceState_read, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases h : (dyadicServiceAt t).1 = j
    · rw [if_pos h, h, if_pos rfl, Finset.card_insert_of_notMem (by simp),
        Function.iterate_succ_apply']
    · rw [if_neg h, if_neg (Ne.symm h)]

/-- For a job which emits by its w-th step, the multiplexed state at its w-th
tick is the exact same state as in an isolated execution. -/
theorem serviceStates_at_deadline {S : Type*} (initial : S) (step : ℕ → S → S)
    (j k : ℕ) :
    (serviceStates initial step (dyadicServiceSlot j k)).getD j initial =
      (step j)^[k+1] initial := by
  rw [serviceStates_read, serviceCount_at_slot]

end Cogentic.Randomized

#print axioms Cogentic.Randomized.serviceStates_at_deadline
