import Cogentic.RandomizedEpochCounter
import Cogentic.RandomizedEpochEventCost
import Cogentic.RandomizedFairEpochTape
import Cogentic.RandomizedInputAsymptotic
import Cogentic.RandomizedPreprocessingCost
import Cogentic.RandomizedSerializedDriver
import Cogentic.RandomizedTotalEpochSplit

namespace Cogentic.RandomizedWholeTreeTape

open RandomizedCostedFactorLaw RandomizedCappedEpoch RandomizedEpochCounter
open RandomizedEpochKernel RandomizedFairEpochTape RandomizedFactorSerialization
open RandomizedInputDriver RandomizedOneThirdAsymptotic RandomizedSerializedDriver
open Filter Real
open scoped BigOperators ENNReal

/-! ### Finite dependent product PMFs over `Fin k` -/

/-- Independent product of finitely many discrete distributions indexed by `Fin k`. -/
noncomputable def piFinLaw {β : ℕ → Type*} (p : ∀ m, PMF (β m)) :
    (k : ℕ) → PMF ((i : Fin k) → β i.1)
  | 0 => PMF.pure (fun i => Fin.elim0 i)
  | k + 1 =>
    (piFinLaw p k).bind fun f =>
      (p k).map fun x =>
        Fin.snoc (α := fun i : Fin (k + 1) => β i.1) f x

open Classical in
private theorem map_snoc_apply {β : ℕ → Type*} {k : ℕ} (q : PMF (β k))
    (g : (i : Fin k) → β i.1) (f : (i : Fin (k + 1)) → β i.1) :
    (q.map (Fin.snoc (α := fun i : Fin (k + 1) => β i.1) g)) f =
      if g = (Fin.init f : (i : Fin k) → β i.1) then q (f (Fin.last k)) else 0 := by
  by_cases hg : g = (Fin.init f : (i : Fin k) → β i.1)
  · subst hg
    rw [if_pos rfl, PMF.map_apply, tsum_eq_single (f (Fin.last k))]
    · rw [if_pos (Fin.snoc_init_self f).symm]
    · intro x hx
      apply if_neg
      intro he
      have hlast := congrFun he (Fin.last k)
      rw [Fin.snoc_last] at hlast
      exact hx hlast.symm
  · rw [if_neg hg, PMF.map_apply, ENNReal.tsum_eq_zero]
    intro x
    apply if_neg
    intro he
    have hinit := congrArg Fin.init he
    rw [Fin.init_snoc] at hinit
    exact hg hinit.symm

/-- Pointwise product formula for `piFinLaw`. -/
theorem piFinLaw_apply {β : ℕ → Type*} (p : ∀ m, PMF (β m)) (k : ℕ)
    (f : (i : Fin k) → β i.1) :
    piFinLaw p k f = ∏ i : Fin k, p i.1 (f i) := by
  classical
  induction k with
  | zero =>
    have hf : f = fun i => Fin.elim0 i := Subsingleton.elim _ _
    subst hf
    simp [piFinLaw, PMF.pure_apply]
  | succ k ih =>
    let initF : (i : Fin k) → β i.1 := Fin.init f
    rw [piFinLaw, PMF.bind_apply, tsum_eq_single initF, Fin.prod_univ_castSucc]
    · rw [map_snoc_apply, if_pos rfl, ih initF]
      rfl
    · intro g hg
      rw [map_snoc_apply, if_neg hg, mul_zero]

/-- Evaluating a `piFinLaw`-distributed tuple at coordinate `j` yields `p j.1`. -/
theorem piFinLaw_map_eval {β : ℕ → Type*} (p : ∀ m, PMF (β m)) (k : ℕ) (j : Fin k) :
    (piFinLaw p k).map (fun f => f j) = p j.1 := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    rw [piFinLaw, PMF.map_bind]
    refine j.lastCases ?_ ?_
    · have hconst :
          (fun f : (i : Fin k) → β i.1 =>
            ((p k).map (Fin.snoc (α := fun i : Fin (k + 1) => β i.1) f)).map
              (fun g => g (Fin.last k))) =
          fun _ => p k := by
        funext f
        rw [PMF.map_comp]
        have hid : (fun g : (i : Fin (k + 1)) → β i.1 => g (Fin.last k)) ∘
            Fin.snoc (α := fun i : Fin (k + 1) => β i.1) f = id := by
          funext x
          simp [Fin.snoc_last]
        rw [hid, PMF.map_id]
      rw [hconst, PMF.bind_const]
      rfl
    · intro i
      have hstep :
          (fun f : (i : Fin k) → β i.1 =>
            ((p k).map (Fin.snoc (α := fun i : Fin (k + 1) => β i.1) f)).map
              (fun g => g i.castSucc)) =
          PMF.pure ∘ (fun f : (i : Fin k) → β i.1 => f i) := by
        funext f
        rw [PMF.map_comp]
        have hconst : (fun g : (i : Fin (k + 1)) → β i.1 => g i.castSucc) ∘
            Fin.snoc (α := fun i : Fin (k + 1) => β i.1) f = Function.const _ (f i) := by
          funext x
          simp [Fin.snoc_castSucc]
        rw [hconst, PMF.map_const]
        rfl
      rw [hstep, PMF.bind_pure_comp]
      exact ih i

private theorem prod_natCast_inv_ennreal {ι : Type*} (s : Finset ι) (c : ι → ℕ)
    (hpos : ∀ i ∈ s, c i ≠ 0) :
    (∏ i ∈ s, ((c i : ℝ≥0∞))⁻¹) = ((∏ i ∈ s, c i : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have ha0 : c a ≠ 0 := hpos a (Finset.mem_insert_self a s)
    have hs0 : ∀ i ∈ s, c i ≠ 0 := fun i hi => hpos i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul, ih hs0,
      ENNReal.mul_inv (Or.inl (Nat.cast_ne_zero.mpr ha0)) (Or.inl (ENNReal.natCast_ne_top _))]

/-- Independent uniform coordinates yield the uniform law on the finite product. -/
theorem piFinLaw_uniform {β : ℕ → Type*} [∀ m, Fintype (β m)] [∀ m, Nonempty (β m)] (k : ℕ) :
    piFinLaw (fun m => PMF.uniformOfFintype (β m)) k =
      PMF.uniformOfFintype ((i : Fin k) → β i.1) := by
  apply PMF.ext
  intro f
  rw [piFinLaw_apply, PMF.uniformOfFintype_apply]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_pi]
  exact prod_natCast_inv_ennreal Finset.univ (fun i : Fin k => Fintype.card (β i.1))
    (fun i _ => Fintype.card_ne_zero)

/-! ### Finite node-addressed binary tree tapes and their product law -/

/-- A node-local finite tape of `cap m` epoch blocks for input size `m`. -/
abbrev LocalTape (α : ℕ → Type*) (m : ℕ) :=
  Fin (RandomizedTrialFallback.cap m) → α m

/-- At one tree node with input bound `N`, a finite table of node-local tapes
indexed by every possible input size `m ≤ N`. -/
abbrev NodeSlot (α : ℕ → Type*) (N : ℕ) :=
  (m : Fin (N + 1)) → LocalTape α m.1

/-- A finite binary tree of node-local epoch tapes of depth `d`, covering every
possible recursive factoring path of inputs `≤ N` with `n.log2 ≤ d`. -/
inductive TreeTape (α : ℕ → Type*) (N : ℕ) : ℕ → Type _ where
  | leaf : TreeTape α N 0
  | node {d : ℕ} (here : NodeSlot α N) (left right : TreeTape α N d) :
      TreeTape α N (d + 1)

def treeTapeZeroEquiv (α : ℕ → Type*) (N : ℕ) : TreeTape α N 0 ≃ Unit where
  toFun _ := ()
  invFun _ := .leaf
  left_inv
    | .leaf => rfl
  right_inv
    | () => rfl

def treeTapeSuccEquiv (α : ℕ → Type*) (N d : ℕ) :
    TreeTape α N (d + 1) ≃ NodeSlot α N × TreeTape α N d × TreeTape α N d where
  toFun
    | .node h l r => (h, l, r)
  invFun
    | (h, l, r) => .node h l r
  left_inv
    | .node _ _ _ => rfl
  right_inv
    | (_, _, _) => rfl

@[instance_reducible]
def fintypeTreeTape {α : ℕ → Type*} [∀ m, Fintype (α m)] (N : ℕ) :
    ∀ d, Fintype (TreeTape α N d)
  | 0 => Fintype.ofEquiv Unit (treeTapeZeroEquiv α N).symm
  | d + 1 =>
    letI : Fintype (TreeTape α N d) := fintypeTreeTape (α := α) N d
    Fintype.ofEquiv (NodeSlot α N × TreeTape α N d × TreeTape α N d)
      (treeTapeSuccEquiv α N d).symm

instance instFintypeTreeTape {α : ℕ → Type*} [∀ m, Fintype (α m)] (N d : ℕ) :
    Fintype (TreeTape α N d) :=
  fintypeTreeTape (α := α) N d

theorem nonemptyTreeTape {α : ℕ → Type*} [∀ m, Nonempty (α m)] (N : ℕ) :
    ∀ d, Nonempty (TreeTape α N d)
  | 0 => ⟨.leaf⟩
  | d + 1 =>
    let ⟨h⟩ := (inferInstance : Nonempty (NodeSlot α N))
    let ⟨l⟩ := nonemptyTreeTape (α := α) N d
    ⟨.node h l l⟩

instance instNonemptyTreeTape {α : ℕ → Type*} [∀ m, Nonempty (α m)] (N d : ℕ) :
    Nonempty (TreeTape α N d) :=
  nonemptyTreeTape (α := α) N d

/-- Product law on a single node's slot table. -/
noncomputable def slotLaw {α : ℕ → Type*} (epoch : ∀ m, PMF (α m)) (N : ℕ) :
    PMF (NodeSlot α N) :=
  piFinLaw (fun m => blockLaw (epoch m) (RandomizedTrialFallback.cap m)) (N + 1)

theorem slotLaw_apply {α : ℕ → Type*} (epoch : ∀ m, PMF (α m)) (N : ℕ)
    (slot : NodeSlot α N) :
    slotLaw epoch N slot =
      ∏ m : Fin (N + 1), blockLaw (epoch m.1) (RandomizedTrialFallback.cap m.1) (slot m) :=
  piFinLaw_apply _ (N + 1) slot

theorem slotLaw_map_eval {α : ℕ → Type*} (epoch : ∀ m, PMF (α m)) (N : ℕ)
    (m : Fin (N + 1)) :
    (slotLaw epoch N).map (fun slot => slot m) =
      blockLaw (epoch m.1) (RandomizedTrialFallback.cap m.1) :=
  piFinLaw_map_eval _ (N + 1) m

theorem slotLaw_uniform {α : ℕ → Type*} [∀ m, Fintype (α m)] [∀ m, Nonempty (α m)] (N : ℕ) :
    slotLaw (fun m => PMF.uniformOfFintype (α m)) N = PMF.uniformOfFintype (NodeSlot α N) := by
  unfold slotLaw
  have hfun : (fun m => blockLaw (PMF.uniformOfFintype (α m)) (RandomizedTrialFallback.cap m)) =
      (fun m => PMF.uniformOfFintype (LocalTape α m)) := by
    funext m
    exact blockLaw_uniform (RandomizedTrialFallback.cap m)
  rw [hfun]
  exact piFinLaw_uniform (N + 1)

/-- Independent product law over the entire finite binary tree of node tapes. -/
noncomputable def treeLaw {α : ℕ → Type*} (epoch : ∀ m, PMF (α m)) (N : ℕ) :
    (d : ℕ) → PMF (TreeTape α N d)
  | 0 => PMF.pure .leaf
  | d + 1 =>
    (slotLaw epoch N).bind fun here =>
      (treeLaw epoch N d).bind fun left =>
        (treeLaw epoch N d).map fun right =>
          .node here left right

theorem treeLaw_apply_leaf {α : ℕ → Type*} (epoch : ∀ m, PMF (α m)) (N : ℕ) :
    treeLaw epoch N 0 .leaf = 1 := by
  simp [treeLaw, PMF.pure_apply]

theorem treeLaw_apply_node {α : ℕ → Type*} (epoch : ∀ m, PMF (α m)) (N d : ℕ)
    (here : NodeSlot α N) (left right : TreeTape α N d) :
    treeLaw epoch N (d + 1) (.node here left right) =
      slotLaw epoch N here * treeLaw epoch N d left * treeLaw epoch N d right := by
  classical
  rw [treeLaw, PMF.bind_apply, tsum_eq_single here]
  · rw [PMF.bind_apply, tsum_eq_single left]
    · rw [PMF.map_apply, tsum_eq_single right]
      · simp [mul_assoc]
      · intro r hr
        simp [hr.symm]
    · intro l hl
      rw [PMF.map_apply, ENNReal.tsum_eq_zero.mpr (fun r => by simp [hl.symm]), mul_zero]
  · intro h hh
    rw [PMF.bind_apply, ENNReal.tsum_eq_zero.mpr, mul_zero]
    intro l
    rw [PMF.map_apply, ENNReal.tsum_eq_zero.mpr (fun r => by simp [hh.symm]), mul_zero]

/-- Uniform epoch blocks at every size yield the exact uniform law over the
entire finite binary tree of node tapes. -/
theorem treeLaw_uniform {α : ℕ → Type*} [∀ m, Fintype (α m)] [∀ m, Nonempty (α m)]
    (N d : ℕ) :
    treeLaw (fun m => PMF.uniformOfFintype (α m)) N d =
      PMF.uniformOfFintype (TreeTape α N d) := by
  induction d with
  | zero =>
    apply PMF.ext
    intro t
    cases t
    rw [treeLaw_apply_leaf, PMF.uniformOfFintype_apply]
    have hcard : Fintype.card (TreeTape α N 0) = 1 :=
      (Fintype.card_congr (treeTapeZeroEquiv α N)).trans Fintype.card_unit
    simp [hcard]
  | succ d ih =>
    apply PMF.ext
    intro t
    cases t with
    | node here left right =>
      rw [treeLaw_apply_node, slotLaw_uniform, ih]
      simp only [PMF.uniformOfFintype_apply]
      have hcard :
          Fintype.card (TreeTape α N (d + 1)) =
            Fintype.card (NodeSlot α N) *
              (Fintype.card (TreeTape α N d) * Fintype.card (TreeTape α N d)) := by
        calc
          Fintype.card (TreeTape α N (d + 1))
              = Fintype.card (NodeSlot α N × TreeTape α N d × TreeTape α N d) :=
            Fintype.card_congr (treeTapeSuccEquiv α N d)
          _ = _ := by simp [Fintype.card_prod]
      rw [hcard, Nat.cast_mul, Nat.cast_mul,
        ENNReal.mul_inv (Or.inl (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
          (Or.inl (ENNReal.natCast_ne_top _)),
        ENNReal.mul_inv (Or.inl (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
          (Or.inl (ENNReal.natCast_ne_top _)),
        mul_assoc]

/-! ### Fair-bit tree specialization -/

/-- A finite binary tree of fair-bit blocks `Fin (bits m) → Bool`. -/
abbrev FairTreeTape (bits : ℕ → ℕ) (N d : ℕ) :=
  TreeTape (fun m => Fin (bits m) → Bool) N d

/-- The independent uniform fair-bit tree distribution. -/
noncomputable def fairTreeLaw (bits : ℕ → ℕ) (N d : ℕ) : PMF (FairTreeTape bits N d) :=
  treeLaw (fun m => PMF.uniformOfFintype (Fin (bits m) → Bool)) N d

/-- Total number of fair bits in one node slot table. -/
def slotBits (bits : ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ m : Fin (N + 1), bits m.1 * RandomizedTrialFallback.cap m.1

/-- Total number of fair bits across the full binary tree of depth `d`. -/
def treeBits (bits : ℕ → ℕ) (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | d + 1 => slotBits bits N + 2 * treeBits bits N d

theorem treeBits_eq (bits : ℕ → ℕ) (N d : ℕ) :
    treeBits bits N d = (2 ^ d - 1) * slotBits bits N := by
  induction d with
  | zero => simp [treeBits]
  | succ d ih =>
    rw [treeBits, ih]
    have hpow : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by decide)
    have hsub : 2 ^ (d + 1) - 1 = 1 + 2 * (2 ^ d - 1) := by
      rw [pow_succ']
      omega
    rw [hsub, Nat.add_mul, one_mul, Nat.mul_assoc]

theorem fairTreeLaw_uniform (bits : ℕ → ℕ) (N d : ℕ) :
    fairTreeLaw bits N d = PMF.uniformOfFintype (FairTreeTape bits N d) :=
  treeLaw_uniform N d

theorem card_fairNodeSlot (bits : ℕ → ℕ) (N : ℕ) :
    Fintype.card (NodeSlot (fun m => Fin (bits m) → Bool) N) = 2 ^ slotBits bits N := by
  simp only [NodeSlot, LocalTape, Fintype.card_pi, Fintype.card_bool,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul,
    Finset.prod_pow_eq_pow_sum]
  rfl

theorem card_fairTreeTape (bits : ℕ → ℕ) (N d : ℕ) :
    Fintype.card (FairTreeTape bits N d) = 2 ^ treeBits bits N d := by
  induction d with
  | zero =>
    rw [Fintype.card_congr (treeTapeZeroEquiv _ N), Fintype.card_unit]
    rfl
  | succ d ih =>
    rw [Fintype.card_congr (treeTapeSuccEquiv _ N d), Fintype.card_prod, Fintype.card_prod,
      card_fairNodeSlot, ih, ← pow_add, ← pow_add, treeBits, two_mul]

/-- Every finite fair-bit tree tape has exact probability `2 ^ (-treeBits bits N d)`. -/
theorem fairTreeLaw_apply (bits : ℕ → ℕ) (N d : ℕ) (t : FairTreeTape bits N d) :
    fairTreeLaw bits N d t = ((2 : ℝ≥0∞)⁻¹) ^ (treeBits bits N d) := by
  rw [fairTreeLaw_uniform, PMF.uniformOfFintype_apply, card_fairTreeTape,
    Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]

/-! ### Counted single-node hard splitter with binary counter and bit-read charges -/

/-- Fixed bit-width of the binary decrement counter for input `n`. -/
def counterWidth (n : ℕ) : ℕ :=
  (RandomizedTrialFallback.cap n).bits.length

private def trialFallback {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime) (_ : Unit) :
    Factors n × ℕ :=
  let s := RandomizedTrialFallback.split n hn hp
  (⟨(s.left, s.right), s.left_ge, s.right_ge, s.product⟩, s.work)

private def toOutcome {n : ℕ} (v : Factors n × ℕ) : SplitOutcome n :=
  ⟨v.1.val.1, v.1.val.2, v.2, v.1.property.1, v.1.property.2.1, v.1.property.2.2⟩

/-- Attempt wrapped with both the fixed-width counter check and per-block read cost. -/
def chargedAttempt {α : Type*} (n readCost : ℕ) (attempt : α → Option (Factors n) × ℕ) :
    α → Option (Factors n) × ℕ :=
  fun a => ((attempt a).1, checkBudget (counterWidth n) + ((attempt a).2 + readCost))

/-- Lazy trial-division fallback wrapped with the final zero-test counter check. -/
def chargedFallback {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime) : Unit → Factors n × ℕ :=
  fun u => ((trialFallback hn hp u).1, checkBudget (counterWidth n) + (trialFallback hn hp u).2)

/-- Execute a hard epoch on a finite node tape using the executable binary
decrement counter `RandomizedEpochCounter.runCounter`, charging `readCost` per
visited block and running lazy trial division only if the counter exhausts. -/
def countedSplitTape {α : Type*} {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime)
    (readCost : ℕ) (attempt : α → Option (Factors n) × ℕ)
    (tape : Fin (RandomizedTrialFallback.cap n) → α) : SplitOutcome n :=
  let counter := (RandomizedTrialFallback.cap n).bits
  let res := runCounter
    (fun a => let out := attempt a; (out.1, out.2 + readCost))
    (trialFallback hn hp)
    counter.length counter (List.ofFn tape)
  toOutcome (res.result, res.work)

private theorem runTape_congr {α β : Type*} (attempt : α → Option β × ℕ)
    (fallback : Unit → β × ℕ) {r₁ r₂ : ℕ} (hr : r₁ = r₂)
    (t₁ : Fin r₁ → α) (t₂ : Fin r₂ → α)
    (ht : ∀ i : Fin r₁, t₁ i = t₂ (i.cast hr)) :
    runTape attempt fallback r₁ t₁ = runTape attempt fallback r₂ t₂ := by
  subst hr
  have hfun : t₁ = t₂ := funext ht
  rw [hfun]

private theorem runTape_ofFn {α β : Type*} (attempt : α → Option β × ℕ)
    (fallback : Unit → β × ℕ) {r : ℕ} (tape : Fin r → α) :
    runTape attempt fallback (List.ofFn tape).length (List.ofFn tape).get =
      runTape attempt fallback r tape :=
  runTape_congr attempt fallback (List.length_ofFn) (List.ofFn tape).get tape
    (fun i => by simp; rfl)

/-- The executable binary-counter node splitter agrees identically with the
capped tape interpreter carrying the counter and bit-read charges. -/
theorem countedSplitTape_eq_runTape {α : Type*} {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime)
    (readCost : ℕ) (attempt : α → Option (Factors n) × ℕ)
    (tape : Fin (RandomizedTrialFallback.cap n) → α) :
    countedSplitTape hn hp readCost attempt tape =
      toOutcome (runTape (chargedAttempt n readCost attempt) (chargedFallback hn hp)
        (RandomizedTrialFallback.cap n) tape) := by
  unfold countedSplitTape
  dsimp only
  have hspec := runCounter_spec
    (fun a => let out := attempt a; (out.1, out.2 + readCost))
    (trialFallback hn hp)
    (RandomizedTrialFallback.cap n).bits.length
    (RandomizedTrialFallback.cap n).bits
    (List.ofFn tape)
    rfl
    (by rw [BinaryDivision.value_bits, List.length_ofFn])
  rw [hspec.2.1]
  unfold chargedTape
  exact congrArg toOutcome (runTape_ofFn (chargedAttempt n readCost attempt)
    (chargedFallback hn hp) tape)

private theorem blocksRead_congr_fst {α β : Type*} (a₁ a₂ : α → Option β × ℕ)
    (hfst : ∀ x, (a₁ x).1 = (a₂ x).1) (r : ℕ) (tape : Fin r → α) :
    blocksRead a₁ r tape = blocksRead a₂ r tape := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [blocksRead, hfst]
    cases (a₂ (tape 0)).1 with
    | some _ => rfl
    | none => rw [ih]

/-- Charging `readCost` per visited block adds exactly `readCost * blocksRead`,
connecting `countedSplitTape` directly to `RandomizedFairEpochTape.runTape_read_charge`. -/
theorem countedSplitTape_read_charge {α : Type*} {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime)
    (readCost : ℕ) (attempt : α → Option (Factors n) × ℕ)
    (tape : Fin (RandomizedTrialFallback.cap n) → α) :
    (countedSplitTape hn hp readCost attempt tape).work =
      (countedSplitTape hn hp 0 attempt tape).work +
        readCost * blocksRead attempt (RandomizedTrialFallback.cap n) tape := by
  rw [countedSplitTape_eq_runTape, countedSplitTape_eq_runTape]
  simp only [toOutcome]
  have hfun : chargedAttempt n readCost attempt =
      fun a => let out := chargedAttempt n 0 attempt a; (out.1, out.2 + readCost) := by
    funext a
    simp [chargedAttempt, Nat.add_assoc]
  rw [hfun, runTape_read_charge,
    blocksRead_congr_fst (chargedAttempt n 0 attempt) attempt (fun _ => rfl)]

/-- Pushforward law of the counted single-node hard splitter on independent epoch blocks. -/
noncomputable def countedSplitLaw {α : Type*} {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime)
    (readCost : ℕ) (epoch : PMF α) (attempt : α → Option (Factors n) × ℕ) :
    PMF (SplitOutcome n) :=
  (blockLaw epoch (RandomizedTrialFallback.cap n)).map
    (countedSplitTape hn hp readCost attempt)

/-- Hard kernel using the counted binary-decrement and bit-read splitter. -/
noncomputable def countedEpochHard {α : ℕ → Type*} (readCost : ℕ → ℕ)
    (epoch : ∀ n, PMF (α n)) (attempt : ∀ n, α n → Option (Factors n) × ℕ) :
    HardKernel :=
  fun n hn _ hp _ => countedSplitLaw hn hp (readCost n) (epoch n) (attempt n)

theorem countedSplitLaw_eq_run {α : Type*} {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime)
    (readCost : ℕ) (epoch : PMF α) (attempt : α → Option (Factors n) × ℕ) :
    countedSplitLaw hn hp readCost epoch attempt =
      (run epoch (chargedAttempt n readCost attempt) (chargedFallback hn hp)
        (RandomizedTrialFallback.cap n)).map toOutcome := by
  rw [← runTape_law, PMF.map_comp]
  unfold countedSplitLaw
  have hfun : countedSplitTape hn hp readCost attempt =
      toOutcome ∘ runTape (chargedAttempt n readCost attempt) (chargedFallback hn hp)
        (RandomizedTrialFallback.cap n) :=
    funext fun tape => countedSplitTape_eq_runTape hn hp readCost attempt tape
  rw [hfun]

theorem countedSplitLaw_mean_ne_top {α : Type*} [Fintype α] {n : ℕ}
    (hn : 2 ≤ n) (hp : ¬n.Prime) (readCost : ℕ) (epoch : PMF α)
    (attempt : α → Option (Factors n) × ℕ) :
    mean (countedSplitLaw hn hp readCost epoch attempt) (fun s => s.work) ≠ ⊤ := by
  rw [countedSplitLaw, mean_map, mean, tsum_fintype]
  exact ENNReal.sum_ne_top.mpr (fun a _ =>
    ENNReal.mul_ne_top ((blockLaw epoch _).apply_ne_top a) (ENNReal.natCast_ne_top _))

private theorem cost_le_of_mul {α β : Type*} (epoch : PMF α) (attempt : α → Option β × ℕ)
    (fallback : Unit → β × ℕ) (r m : ℕ) (hr : (fallback ()).2 ≤ m * r) :
    let w := mean epoch (fun a => ((attempt a).2 + 1 : ℕ))
    let q := mean epoch (fun a => failFlag (attempt a).1)
    mean (run epoch attempt fallback r) (fun b => b.2) ≤ (w + (m : ℝ≥0∞)) / (1 - q) := by
  let w := mean epoch (fun a => ((attempt a).2 + 1 : ℕ))
  let q := mean epoch (fun a => failFlag (attempt a).1)
  have hflag (o : Option β) : failFlag o ≤ 1 := by cases o <;> simp [failFlag]
  have hq : q ≤ 1 := by
    rw [← mean_const epoch 1]
    apply ENNReal.tsum_le_tsum
    intro a
    exact mul_le_mul_right (hflag (attempt a).1) _
  let S := ∑ i ∈ Finset.range r, q ^ i
  have hpowers : (r : ℝ≥0∞) * q ^ r ≤ S := by
    calc
      _ = ∑ _i ∈ Finset.range r, q ^ r := by simp
      _ ≤ _ := Finset.sum_le_sum fun i hi =>
        pow_le_pow_of_le_one (show 0 ≤ q from zero_le) hq (Finset.mem_range.mp hi).le
  have hsum : S ≤ (1 - q)⁻¹ := by
    rw [← ENNReal.tsum_geometric]
    exact ENNReal.summable.sum_le_tsum _ (fun _ _ => zero_le)
  rw [cost_eq]
  change w * S + q ^ r * (fallback ()).2 ≤ _
  calc
    _ ≤ w * S + (m : ℝ≥0∞) * S := by
      refine add_le_add le_rfl ?_
      calc
        q ^ r * ((fallback ()).2 : ℝ≥0∞)
            ≤ q ^ r * ((m * r : ℕ) : ℝ≥0∞) := mul_le_mul_right (Nat.cast_le.mpr hr) _
        _ = (m : ℝ≥0∞) * ((r : ℝ≥0∞) * q ^ r) := by rw [Nat.cast_mul]; ring
        _ ≤ (m : ℝ≥0∞) * S := mul_le_mul_right hpowers _
    _ = (w + (m : ℝ≥0∞)) * S := by rw [add_mul]
    _ ≤ _ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_right hsum _

private theorem checkBudget_le_cap (n : ℕ) :
    checkBudget (counterWidth n) ≤ RandomizedTrialFallback.cap n := by
  have hcb := (initializedCounter_spec n).2
  have hsize : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have hpow : n + 2 ≤ (n + 2) ^ 4 := Nat.le_self_pow (by decide) _
  have h1 : 1 ≤ (n + 2) ^ 4 := Nat.one_le_pow _ _ (by omega)
  unfold counterWidth RandomizedTrialFallback.cap at *
  nlinarith only [hcb, hsize, hpow, h1]

theorem countedSplitLaw_mean_le {α : Type*} {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime)
    (readCost : ℕ) (epoch : PMF α) (attempt : α → Option (Factors n) × ℕ) :
    mean (countedSplitLaw hn hp readCost epoch attempt) (fun s => s.work) ≤
      (mean epoch (fun a => ((attempt a).2 + readCost + 1 : ℕ)) +
        (checkBudget (counterWidth n) : ℝ≥0∞) + 2) /
      (1 - mean epoch (fun a => failFlag (attempt a).1)) := by
  rw [countedSplitLaw_eq_run, mean_map]
  have hfb : (chargedFallback hn hp ()).2 ≤ 2 * RandomizedTrialFallback.cap n := by
    simp only [chargedFallback, trialFallback]
    have h1 := checkBudget_le_cap n
    have h2 := RandomizedTrialFallback.split_work_le n hn hp
    omega
  have hbase := cost_le_of_mul epoch (chargedAttempt n readCost attempt)
    (chargedFallback hn hp) (RandomizedTrialFallback.cap n) 2 hfb
  have hw :
      mean epoch (fun a => (((chargedAttempt n readCost attempt a).2 + 1 : ℕ) : ℝ≥0∞)) =
        (checkBudget (counterWidth n) : ℝ≥0∞) +
          mean epoch (fun a => ((attempt a).2 + readCost + 1 : ℕ)) := by
    rw [← mean_const epoch (checkBudget (counterWidth n) : ℝ≥0∞), ← mean_add]
    congr 1
    funext a
    simp only [chargedAttempt, ← Nat.cast_add]
    exact congrArg Nat.cast (by omega)
  have hq :
      mean epoch (fun a => failFlag (chargedAttempt n readCost attempt a).1) =
        mean epoch (fun a => failFlag (attempt a).1) := rfl
  refine hbase.trans_eq ?_
  rw [hw, hq, add_comm (checkBudget (counterWidth n) : ℝ≥0∞), Nat.cast_ofNat]

/-- Real single-epoch bounds (charging attempt work plus `readCost`) bound
`countedSplitLaw` up to a linear factor in `n.log2 + 1` from the fixed-width
binary counter. -/
theorem countedSplitLaw_mean_le_of_real_bounds {α : Type*} {n : ℕ}
    (hn : 2 ≤ n) (hp : ¬n.Prime) (readCost : ℕ) (epoch : PMF α)
    (attempt : α → Option (Factors n) × ℕ) {W S : ℝ} (hS : 0 < S)
    (work : mean epoch (fun a => ((attempt a).2 + readCost + 1 : ℕ)) + 1 ≤ ENNReal.ofReal W)
    (hit : S ≤ ((epoch.map attempt).toOuterMeasure {o | o.1 ≠ none}).toReal) :
    mean (countedSplitLaw hn hp readCost epoch attempt) (fun s => s.work) ≤
      ENNReal.ofReal (185 * ((n.log2 : ℝ) + 1) * (W / S)) := by
  have hW_pos : 0 ≤ W := by
    by_contra h
    push Not at h
    have hz : ENNReal.ofReal W = 0 := ENNReal.ofReal_eq_zero.mpr h.le
    rw [hz] at work
    have h1 : (1 : ℝ≥0∞) ≤ 0 := le_add_self.trans work
    exact absurd h1 (by simp)
  have hcb := (initializedCounter_spec n).2
  have hsize : n.size ≤ n.log2 + 1 := Nat.size_le.mpr Nat.lt_log2_self
  have hM : checkBudget (counterWidth n) + 2 ≤ 185 * (n.log2 + 1) := by
    unfold counterWidth at *
    omega
  set u := mean epoch (fun a => ((attempt a).2 + readCost + 1 : ℕ)) + 1
  have hu1 : (1 : ℝ≥0∞) ≤ u := le_add_self
  have hnum :
      mean epoch (fun a => ((attempt a).2 + readCost + 1 : ℕ)) +
        (checkBudget (counterWidth n) : ℝ≥0∞) + 2 ≤
      ENNReal.ofReal (185 * ((n.log2 : ℝ) + 1) * W) := by
    have hsplit :
        mean epoch (fun a => ((attempt a).2 + readCost + 1 : ℕ)) +
          (checkBudget (counterWidth n) : ℝ≥0∞) + 2 =
        u + ((checkBudget (counterWidth n) + 1 : ℕ) : ℝ≥0∞) := by
      dsimp only [u]
      rw [Nat.cast_add, Nat.cast_one]
      have h2 : (2 : ℝ≥0∞) = 1 + 1 := one_add_one_eq_two.symm
      rw [h2]
      ring
    rw [hsplit]
    calc
      u + ((checkBudget (counterWidth n) + 1 : ℕ) : ℝ≥0∞)
          ≤ u + ((checkBudget (counterWidth n) + 1 : ℕ) : ℝ≥0∞) * u :=
        add_le_add le_rfl (le_mul_of_one_le_right zero_le hu1)
      _ = ((checkBudget (counterWidth n) + 2 : ℕ) : ℝ≥0∞) * u := by
        conv_rhs =>
          rw [show checkBudget (counterWidth n) + 2 = 1 + (checkBudget (counterWidth n) + 1) by omega,
            Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      _ ≤ ((185 * (n.log2 + 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal W :=
        mul_le_mul' (Nat.cast_le.mpr hM) work
      _ = ENNReal.ofReal (185 * ((n.log2 : ℝ) + 1) * W) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        push_cast
        ring
  refine (countedSplitLaw_mean_le hn hp readCost epoch attempt).trans ?_
  rw [one_sub_failure_eq_success, ← mul_div_assoc, ENNReal.ofReal_div_of_pos hS]
  exact ENNReal.div_le_div hnum ((ENNReal.ofReal_le_ofReal hit).trans ENNReal.ofReal_toReal_le)

/-! ### Deterministic executable whole-tree factoring on a finite `TreeTape` -/

private def dispatchTree {α : ℕ → Type*} (readCost : ℕ → ℕ)
    (attempt : ∀ n, α n → Option (Factors n) × ℕ)
    (n : ℕ) (hn : 2 ≤ n) (work : ℕ) (tape : LocalTape α n) :
    (r : RandomizedPreprocessing.Result) → r.Sound n → Branch n
  | .prime, hp => .prime work hp
  | .split d, hd => .split (verifiedEasySplit n d hn hd work)
  | .hard, hs =>
    let s := countedSplitTape hn hs.2.1 (readCost n) (attempt n) tape
    .split {s with work := work + s.work}

/-- Single-node counted decision on a finite node-local tape: runs preprocessing,
verifies easy splits, or runs the counted binary-decrement epoch splitter with
bit-read charges and lazy trial-division fallback. -/
def decisionTree {α : ℕ → Type*} (k : ℕ)
    (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n)
    (readCost : ℕ → ℕ) (attempt : ∀ n, α n → Option (Factors n) × ℕ)
    (n : ℕ) (hn : 2 ≤ n) (tape : LocalTape α n) : Branch n :=
  let prep := RandomizedPreprocessing.run k n
  dispatchTree readCost attempt n hn prep.2 tape prep.1 (sound n hn)

/-- Single-node pushforward equivalence with `RandomizedInputDriver.decision`. -/
theorem decisionTree_law {α : ℕ → Type*} (k : ℕ)
    (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n)
    (readCost : ℕ → ℕ) (epoch : ∀ n, PMF (α n))
    (attempt : ∀ n, α n → Option (Factors n) × ℕ)
    (n : ℕ) (hn : 2 ≤ n) :
    (blockLaw (epoch n) (RandomizedTrialFallback.cap n)).map
      (decisionTree k sound readCost attempt n hn) =
    RandomizedInputDriver.decision k sound
      (countedEpochHard readCost epoch attempt) n hn := by
  unfold decisionTree RandomizedInputDriver.decision
  dsimp only
  generalize sound n hn = hsound
  revert hsound
  generalize (RandomizedPreprocessing.run k n).1 = r
  intro hsound
  cases r with
  | prime =>
    change (blockLaw (epoch n) _).map (Function.const _ (Branch.prime _ hsound)) = PMF.pure _
    exact PMF.map_const _ _
  | split d =>
    change (blockLaw (epoch n) _).map
      (Function.const _ (Branch.split (verifiedEasySplit n d hn hsound _))) = PMF.pure _
    exact PMF.map_const _ _
  | hard =>
    change (blockLaw (epoch n) _).map
      ((fun s : SplitOutcome n => Branch.split {s with work := (RandomizedPreprocessing.run k n).2 + s.work}) ∘
        countedSplitTape hn hsound.2.1 (readCost n) (attempt n)) =
      (countedSplitLaw hn hsound.2.1 (readCost n) (epoch n) (attempt n)).map _
    rw [← PMF.map_comp]
    rfl

private theorem log2_left_lt {n : ℕ} (s : SplitOutcome n) : s.left.log2 < n.log2 := by
  have h1 : 2 * s.left ≤ n := by
    calc
      2 * s.left ≤ s.right * s.left := Nat.mul_le_mul_right _ s.right_ge
      _ = n := by rw [Nat.mul_comm, s.product]
  have h2 : 2 ^ (s.left.log2 + 1) ≤ n := by
    rw [pow_succ']
    exact (Nat.mul_le_mul_left 2 (Nat.log2_self_le (by have := s.left_ge; omega))).trans h1
  have hn0 : n ≠ 0 := by have := s.left_lt; omega
  exact Nat.lt_of_succ_le ((Nat.le_log2 hn0).mpr h2)

private theorem log2_right_lt {n : ℕ} (s : SplitOutcome n) : s.right.log2 < n.log2 := by
  have h1 : 2 * s.right ≤ n := by
    calc
      2 * s.right ≤ s.left * s.right := Nat.mul_le_mul_right _ s.left_ge
      _ = n := s.product
  have h2 : 2 ^ (s.right.log2 + 1) ≤ n := by
    rw [pow_succ']
    exact (Nat.mul_le_mul_left 2 (Nat.log2_self_le (by have := s.right_ge; omega))).trans h1
  have hn0 : n ≠ 0 := by have := s.right_lt; omega
  exact Nat.lt_of_succ_le ((Nat.le_log2 hn0).mpr h2)

/-- Deterministic executable whole-tree factoring on a finite node-addressed
binary tree tape. Every node reads only its own local tape slot; recursive
children receive disjoint subtrees. -/
def factorTree {α : ℕ → Type*} (k : ℕ)
    (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n)
    (readCost : ℕ → ℕ) (attempt : ∀ n, α n → Option (Factors n) × ℕ)
    {N : ℕ} :
    ∀ {d : ℕ}, TreeTape α N d → (n : ℕ) → 2 ≤ n → n ≤ N → n.log2 ≤ d → List ℕ × ℕ
  | 0, _, n, hn, _, hd =>
    have hlog : 1 ≤ n.log2 := (Nat.le_log2 (by omega)).mpr (by simpa using hn)
    False.elim (by omega)
  | _ + 1, .node here left right, n, hn, hle, hd =>
    match decisionTree k sound readCost attempt n hn (here ⟨n, Nat.lt_succ_of_le hle⟩) with
    | .prime work _ => ([n], work)
    | .split s =>
      let a := factorTree k sound readCost attempt left s.left s.left_ge
        (s.left_lt.le.trans hle) (Nat.le_of_lt_succ ((log2_left_lt s).trans_le hd))
      let b := factorTree k sound readCost attempt right s.right s.right_ge
        (s.right_lt.le.trans hle) (Nat.le_of_lt_succ ((log2_right_lt s).trans_le hd))
      (a.1 ++ b.1, s.work + a.2 + b.2)

/-- Every-tape correctness for `factorTree`: for every finite tree tape (even
all-failure tapes), the returned list is a complete prime factorization of `n`. -/
theorem factorTree_correct {α : ℕ → Type*} (k : ℕ)
    (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n)
    (readCost : ℕ → ℕ) (attempt : ∀ n, α n → Option (Factors n) × ℕ)
    {N d : ℕ} (tape : TreeTape α N d) (n : ℕ) (hn : 2 ≤ n) (hle : n ≤ N) (hd : n.log2 ≤ d) :
    let out := factorTree k sound readCost attempt tape n hn hle hd
    out.1.prod = n ∧ ∀ p ∈ out.1, p.Prime := by
  induction d generalizing n with
  | zero =>
    have hlog : 1 ≤ n.log2 := (Nat.le_log2 (by omega)).mpr (by simpa using hn)
    omega
  | succ d ih =>
    cases tape with
    | node here left right =>
      dsimp only
      rw [factorTree]
      cases hdec : decisionTree k sound readCost attempt n hn (here ⟨n, Nat.lt_succ_of_le hle⟩) with
      | prime work hp => simp [hp]
      | split s =>
        obtain ⟨hl, hpl⟩ := ih left s.left s.left_ge
          (s.left_lt.le.trans hle) (Nat.le_of_lt_succ ((log2_left_lt s).trans_le hd))
        obtain ⟨hr, hpr⟩ := ih right s.right s.right_ge
          (s.right_lt.le.trans hle) (Nat.le_of_lt_succ ((log2_right_lt s).trans_le hd))
        refine ⟨?_, ?_⟩
        · dsimp only
          rw [List.prod_append, hl, hr, s.product]
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hpl p hp
          · exact hpr p hp

theorem factorTree_perm {α : ℕ → Type*} (k : ℕ)
    (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n)
    (readCost : ℕ → ℕ) (attempt : ∀ n, α n → Option (Factors n) × ℕ)
    {N d : ℕ} (tape : TreeTape α N d) (n : ℕ) (hn : 2 ≤ n) (hle : n ≤ N) (hd : n.log2 ≤ d) :
    (factorTree k sound readCost attempt tape n hn hle hd).1.Perm n.primeFactorsList :=
  (factorTree_correct k sound readCost attempt tape n hn hle hd).elim Nat.primeFactorsList_unique

/-- **Exact whole-tree distribution equivalence** for `factorTree`: pushing
forward the independent product `treeLaw` along `factorTree` equals the
recursive PMF `RandomizedInputDriver.factor` with the counted hard kernel. -/
theorem factorTree_law {α : ℕ → Type*} (k : ℕ)
    (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n)
    (readCost : ℕ → ℕ) (epoch : ∀ n, PMF (α n))
    (attempt : ∀ n, α n → Option (Factors n) × ℕ)
    {N d : ℕ} (n : ℕ) (hn : 2 ≤ n) (hle : n ≤ N) (hd : n.log2 ≤ d) :
    (treeLaw epoch N d).map (fun tape => factorTree k sound readCost attempt tape n hn hle hd) =
      RandomizedInputDriver.factor k sound (countedEpochHard readCost epoch attempt) n hn := by
  induction d generalizing n with
  | zero =>
    have hlog : 1 ≤ n.log2 := (Nat.le_log2 (by omega)).mpr (by simpa using hn)
    omega
  | succ d ih =>
    let hard := countedEpochHard readCost epoch attempt
    let cont : Branch n → PMF (List ℕ × ℕ) := fun
      | .prime work _ => PMF.pure ([n], work)
      | .split s =>
        (RandomizedInputDriver.factor k sound hard s.left s.left_ge).bind fun a =>
          (RandomizedInputDriver.factor k sound hard s.right s.right_ge).map fun b =>
            (a.1 ++ b.1, s.work + a.2 + b.2)
    have hbranch (here : NodeSlot α N) :
        ((treeLaw epoch N d).bind fun left =>
          (treeLaw epoch N d).map fun right =>
            factorTree k sound readCost attempt (.node here left right) n hn hle hd) =
        cont (decisionTree k sound readCost attempt n hn (here ⟨n, Nat.lt_succ_of_le hle⟩)) := by
      cases hdec : decisionTree k sound readCost attempt n hn (here ⟨n, Nat.lt_succ_of_le hle⟩) with
      | prime work hp =>
        have hinner :
            (fun left : TreeTape α N d =>
              (treeLaw epoch N d).map fun right =>
                factorTree k sound readCost attempt (.node here left right) n hn hle hd) =
            fun _ => PMF.pure ([n], work) := by
          funext left
          have hconst :
              (fun right : TreeTape α N d =>
                factorTree k sound readCost attempt (.node here left right) n hn hle hd) =
              Function.const _ ([n], work) := by
            funext right
            simp [factorTree, hdec]
          rw [hconst, PMF.map_const]
        rw [hinner, PMF.bind_const]
      | split s =>
        have hhl := s.left_lt.le.trans hle
        have hhr := s.right_lt.le.trans hle
        have hdl := Nat.le_of_lt_succ ((log2_left_lt s).trans_le hd)
        have hdr := Nat.le_of_lt_succ ((log2_right_lt s).trans_le hd)
        have hstep :
            (fun left : TreeTape α N d =>
              (treeLaw epoch N d).map fun right =>
                factorTree k sound readCost attempt (.node here left right) n hn hle hd) =
            (fun a : List ℕ × ℕ =>
              (RandomizedInputDriver.factor k sound hard s.right s.right_ge).map fun b =>
                (a.1 ++ b.1, s.work + a.2 + b.2)) ∘
            (fun left : TreeTape α N d =>
              factorTree k sound readCost attempt left s.left s.left_ge hhl hdl) := by
          funext left
          simp only [Function.comp_apply, factorTree, hdec]
          rw [← ih s.right s.right_ge hhr hdr, PMF.map_comp]
          rfl
        rw [hstep, ← PMF.bind_map, ih s.left s.left_ge hhl hdl]
    calc
      (treeLaw epoch N (d + 1)).map
          (fun tape => factorTree k sound readCost attempt tape n hn hle hd)
          = (slotLaw epoch N).bind fun here =>
              (treeLaw epoch N d).bind fun left =>
                (treeLaw epoch N d).map fun right =>
                  factorTree k sound readCost attempt (.node here left right) n hn hle hd := by
        simp [treeLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]
      _ = (slotLaw epoch N).bind (fun here =>
            cont (decisionTree k sound readCost attempt n hn (here ⟨n, Nat.lt_succ_of_le hle⟩))) := by
        congr 1
        funext here
        exact hbranch here
      _ = ((slotLaw epoch N).map (fun here => here ⟨n, Nat.lt_succ_of_le hle⟩)).bind
            (fun localTape => cont (decisionTree k sound readCost attempt n hn localTape)) := by
        rw [PMF.bind_map]
        rfl
      _ = (blockLaw (epoch n) (RandomizedTrialFallback.cap n)).bind
            (fun localTape => cont (decisionTree k sound readCost attempt n hn localTape)) := by
        rw [slotLaw_map_eval epoch N ⟨n, Nat.lt_succ_of_le hle⟩]
      _ = ((blockLaw (epoch n) (RandomizedTrialFallback.cap n)).map
            (decisionTree k sound readCost attempt n hn)).bind cont := by
        rw [PMF.bind_map]
        rfl
      _ = (RandomizedInputDriver.decision k sound hard n hn).bind cont := by
        rw [decisionTree_law k sound readCost epoch attempt n hn]
      _ = RandomizedInputDriver.factor k sound hard n hn := by
        conv_rhs => rw [RandomizedInputDriver.factor]
        rfl

/-! ### Serialized whole-tree executable machines -/

/-- Serialize the prime list and charge recursive list copying (`copyAllowance`)
plus framed bit output (`serialize`), matching `RandomizedSerializedDriver.serializedFactor`. -/
def serializeOutput (n : ℕ) (out : List ℕ × ℕ) : List Bool × ℕ :=
  let frame := serialize (out.1.map Nat.bits)
  (frame.1, out.2 + (copyAllowance n + frame.2))

/-- Top-level executable deterministic serialized whole-tree factoring machine
on a finite node-addressed tree tape of depth `n.log2`. -/
def serializedFactorTree {α : ℕ → Type*} (k : ℕ)
    (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n)
    (readCost : ℕ → ℕ) (attempt : ∀ n, α n → Option (Factors n) × ℕ)
    (n : ℕ) (hn : 2 ≤ n) (tape : TreeTape α n n.log2) : List Bool × ℕ :=
  serializeOutput n (factorTree k sound readCost attempt tape n hn le_rfl le_rfl)

/-- Top-level executable deterministic serialized whole-tree factoring machine
on a finite binary tree of fair-bit blocks `Fin (bits m) → Bool`. -/
def fairSerializedFactorTree (k : ℕ)
    (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n)
    (bits : ℕ → ℕ)
    (attempt : ∀ n, (Fin (bits n) → Bool) → Option (Factors n) × ℕ)
    (n : ℕ) (hn : 2 ≤ n) (tape : FairTreeTape bits n n.log2) : List Bool × ℕ :=
  serializedFactorTree k sound bits attempt n hn tape

/-- **Every-tape correctness**: for EVERY finite tree tape (including
all-failure tapes), `serializedFactorTree` emits framed bits that decode via
`decodeFactors` to a permutation of `n.primeFactorsList`. -/
theorem serializedFactorTree_correct {α : ℕ → Type*} (k : ℕ)
    (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n)
    (readCost : ℕ → ℕ) (attempt : ∀ n, α n → Option (Factors n) × ℕ)
    (n : ℕ) (hn : 2 ≤ n) (tape : TreeTape α n n.log2) :
    ∃ xs : List ℕ,
      decodeFactors (serializedFactorTree k sound readCost attempt n hn tape).1 = some xs ∧
      xs.Perm n.primeFactorsList :=
  ⟨(factorTree k sound readCost attempt tape n hn le_rfl le_rfl).1,
    decodeFactors_serialize _,
    factorTree_perm k sound readCost attempt tape n hn le_rfl le_rfl⟩

/-- **Every-tape correctness** for the fair-bit tree machine. -/
theorem fairSerializedFactorTree_correct (k : ℕ)
    (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n)
    (bits : ℕ → ℕ)
    (attempt : ∀ n, (Fin (bits n) → Bool) → Option (Factors n) × ℕ)
    (n : ℕ) (hn : 2 ≤ n) (tape : FairTreeTape bits n n.log2) :
    ∃ xs : List ℕ,
      decodeFactors (fairSerializedFactorTree k sound bits attempt n hn tape).1 = some xs ∧
      xs.Perm n.primeFactorsList :=
  serializedFactorTree_correct k sound bits attempt n hn tape

/-- **Exact whole-tree distribution equivalence** for `serializedFactorTree`:
pushing forward `treeLaw` equals `RandomizedSerializedDriver.serializedFactor`
with the binary-counter and bit-read charges attached to every attempt and fallback. -/
theorem serializedFactorTree_law {α : ℕ → Type*} (k : ℕ)
    (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n)
    (readCost : ℕ → ℕ) (epoch : ∀ n, PMF (α n))
    (attempt : ∀ n, α n → Option (Factors n) × ℕ)
    (n : ℕ) (hn : 2 ≤ n) :
    (treeLaw epoch n n.log2).map (serializedFactorTree k sound readCost attempt n hn) =
      serializedFactor k sound (countedEpochHard readCost epoch attempt) n hn := by
  have hcomp :
      serializedFactorTree k sound readCost attempt n hn =
        serializeOutput n ∘
          (fun tape => factorTree k sound readCost attempt tape n hn le_rfl le_rfl) := rfl
  rw [hcomp, ← PMF.map_comp, factorTree_law k sound readCost epoch attempt n hn le_rfl le_rfl]
  rfl

/-- **Exact whole-tree distribution equivalence** on the uniform finite fair-bit
tree space `PMF.uniformOfFintype (FairTreeTape bits n n.log2)`. -/
theorem fairSerializedFactorTree_law (k : ℕ)
    (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n)
    (bits : ℕ → ℕ)
    (attempt : ∀ n, (Fin (bits n) → Bool) → Option (Factors n) × ℕ)
    (n : ℕ) (hn : 2 ≤ n) :
    (PMF.uniformOfFintype (FairTreeTape bits n n.log2)).map
        (fairSerializedFactorTree k sound bits attempt n hn) =
      serializedFactor k sound
        (countedEpochHard bits (fun m => PMF.uniformOfFintype (Fin (bits m) → Bool)) attempt)
        n hn := by
  rw [← fairTreeLaw_uniform]
  exact serializedFactorTree_law k sound bits
    (fun m => PMF.uniformOfFintype (Fin (bits m) → Bool)) attempt n hn

/-! ### Combined end-to-end corollaries from `DirichletLZerosOnLine` -/

/-- General whole-tree expected-cost transfer from an observable single-epoch
`W / S` bound (charging attempt work plus `readCost`, with binary-counter
charges absorbed automatically into the `δ` slack). -/
theorem factor_expected_from_counted_epoch {α : ℕ → Type} [∀ n, Fintype (α n)]
    (k : ℕ)
    (prep : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n ∧
      (RandomizedPreprocessing.run k n).2 ≤ (10000 * (k + 1)) ^ 32 * (n.log2 + 2) ^ 32)
    (readCost : ℕ → ℕ) (epoch : ∀ n, PMF (α n))
    (attempt : ∀ n, α n → Option (Factors n) × ℕ)
    {C : ℝ} (hC : 0 ≤ C)
    (hEpoch : ∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Odd n → ¬n.Prime → ¬IsPrimePow n →
      ∃ W S : ℝ, 0 < S ∧
        mean (epoch n) (fun a => ((attempt n a).2 + readCost n + 1 : ℕ)) + 1 ≤ ENNReal.ofReal W ∧
        S ≤ (((epoch n).map (attempt n)).toOuterMeasure {o | o.1 ≠ none}).toReal ∧
        W / S ≤ exp ((C + δ) * scale n)) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
      mean (RandomizedInputDriver.factor k (fun m hm => (prep m hm).1)
        (countedEpochHard readCost epoch attempt) n hn) (fun out => out.2) ≤
        ENNReal.ofReal (exp ((C + ε) * scale n)) := by
  classical
  let B (n : ℕ) : ℝ :=
    if h : 2 ≤ n ∧ Odd n ∧ ¬n.Prime ∧ ¬IsPrimePow n then
      (mean (countedSplitLaw h.1 h.2.2.1 (readCost n) (epoch n) (attempt n))
        (fun s => s.work)).toReal
    else 0
  refine factor_expected_from_hard k prep (countedEpochHard readCost epoch attempt) B ?_ ?_ hC ?_
  · intro n
    dsimp only [B]
    split <;> positivity
  · intro n hn ho hp hpow
    have hd : 2 ≤ n ∧ Odd n ∧ ¬n.Prime ∧ ¬IsPrimePow n := ⟨hn, ho, hp, hpow⟩
    simp [countedEpochHard, B, hd,
      ENNReal.ofReal_toReal (countedSplitLaw_mean_ne_top hn hp (readCost n) (epoch n) (attempt n))]
  · intro δ hδ
    have hhalf : 0 < δ / 2 := by positivity
    filter_upwards [hEpoch (δ / 2) hhalf,
      eventually_bitPoly_le_exp (A := 185) hhalf 1] with n h hpoly
    dsimp only [B]
    split
    · rename_i hn
      obtain ⟨W, S, hS, work, hit, ratio⟩ := h hn.2.1 hn.2.2.1 hn.2.2.2
      simp only [pow_one] at hpoly
      have hprod : 185 * ((n.log2 : ℝ) + 1) * (W / S) ≤ exp ((C + δ) * scale n) := by
        calc
          185 * ((n.log2 : ℝ) + 1) * (W / S)
              ≤ exp ((δ / 2) * scale n) * exp ((C + δ / 2) * scale n) := by
            have hW_nonneg : 0 ≤ W / S := by
              have hW0 : 0 ≤ W := by
                by_contra hneg
                push Not at hneg
                rw [ENNReal.ofReal_eq_zero.mpr hneg.le] at work
                have h1 : (1 : ℝ≥0∞) ≤ 0 := le_add_self.trans work
                exact absurd h1 (by simp)
              exact div_nonneg hW0 hS.le
            exact mul_le_mul hpoly ratio hW_nonneg (exp_pos _).le
          _ = exp ((C + δ) * scale n) := by rw [← exp_add]; congr 1; ring
      have hb :=
        (countedSplitLaw_mean_le_of_real_bounds hn.1 hn.2.2.1 (readCost n) (epoch n) (attempt n)
          hS work hit).trans (ENNReal.ofReal_le_ofReal hprod)
      simpa [ENNReal.toReal_ofReal (exp_pos _).le] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    · exact (exp_pos _).le

/-- General combined end-to-end theorem from `DirichletLZerosOnLine` for any
finite epoch family `α` and per-block read charge `readCost`. -/
theorem whole_tree_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ {α : ℕ → Type} [∀ n, Fintype (α n)] (readCost : ℕ → ℕ)
      (epoch : ∀ n, PMF (α n))
      (attempt : ∀ n, α n → Option (Factors n) × ℕ) {C : ℝ}, 0 ≤ C →
      (∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, Odd n → ¬n.Prime → ¬IsPrimePow n →
        ∃ W S : ℝ, 0 < S ∧
          mean (epoch n) (fun a => ((attempt n a).2 + readCost n + 1 : ℕ)) + 1 ≤ ENNReal.ofReal W ∧
          S ≤ (((epoch n).map (attempt n)).toOuterMeasure {o | o.1 ≠ none}).toReal ∧
          W / S ≤ exp ((C + δ) * scale n)) →
      (∀ n (hn : 2 ≤ n) (tape : TreeTape α n n.log2),
        ∃ xs : List ℕ,
          decodeFactors (serializedFactorTree k sound readCost attempt n hn tape).1 = some xs ∧
          xs.Perm n.primeFactorsList) ∧
      (∀ n (hn : 2 ≤ n),
        (treeLaw epoch n n.log2).map (serializedFactorTree k sound readCost attempt n hn) =
          serializedFactor k sound (countedEpochHard readCost epoch attempt) n hn) ∧
      (∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
        mean (treeLaw epoch n n.log2)
          (fun tape => ((serializedFactorTree k sound readCost attempt n hn tape).2 : ℝ≥0∞)) ≤
          ENNReal.ofReal (exp ((C + ε) * scale n))) := by
  obtain ⟨k, prep⟩ := RandomizedPreprocessing.of_critical_line line
  let sound := fun m hm => (prep m hm).1
  refine ⟨k, sound, ?_⟩
  intro α _ readCost epoch attempt C hC hEpoch
  have hexp :=
    serializedFactor_expected_eventually k sound (countedEpochHard readCost epoch attempt) hC
      (factor_expected_from_counted_epoch k prep readCost epoch attempt hC hEpoch)
  refine ⟨fun n hn tape => serializedFactorTree_correct k sound readCost attempt n hn tape,
    fun n hn => serializedFactorTree_law k sound readCost epoch attempt n hn, ?_⟩
  intro ε hε
  filter_upwards [hexp ε hε] with n h hn
  have hmean :
      mean (treeLaw epoch n n.log2)
          (fun tape => ((serializedFactorTree k sound readCost attempt n hn tape).2 : ℝ≥0∞)) =
        mean (serializedFactor k sound (countedEpochHard readCost epoch attempt) n hn)
          (fun out => out.2) := by
    rw [← serializedFactorTree_law k sound readCost epoch attempt n hn, mean_map]
  rw [hmean]
  exact h hn

/-- **Combined end-to-end corollary on a finite fair-bit tree tape** from
`DirichletLZerosOnLine`: ONE single executable deterministic machine
`fairSerializedFactorTree` simultaneously achieves:
1. **Every-tape correctness**: on EVERY finite fair-bit tree tape (including
   all-failure tapes), its output decodes via `decodeFactors` to a permutation
   of `n.primeFactorsList`;
2. **Exact whole-tree distribution equivalence**: pushing forward the uniform
   law `PMF.uniformOfFintype (FairTreeTape bits n n.log2)` equals
   `RandomizedSerializedDriver.serializedFactor` (with fixed-width counter and
   fair-bit read charges);
3. **Asymptotic expected bit-cost bound**: for every `ε > 0`, eventually
   expected total work over the uniform fair-bit tree tape is
   `≤ exp ((C + ε) * scale n)`. -/
theorem fair_whole_tree_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ (k : ℕ) (sound : ∀ n ≥ 2, (RandomizedPreprocessing.run k n).1.Sound n),
    ∀ (bits : ℕ → ℕ)
      (attempt : ∀ n, (Fin (bits n) → Bool) → Option (Factors n) × ℕ)
      {C : ℝ}, 0 ≤ C →
      (∀ δ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, Odd n → ¬n.Prime → ¬IsPrimePow n →
        ∃ W S : ℝ, 0 < S ∧
          mean (PMF.uniformOfFintype (Fin (bits n) → Bool))
            (fun a => ((attempt n a).2 + bits n + 1 : ℕ)) + 1 ≤ ENNReal.ofReal W ∧
          S ≤ (((PMF.uniformOfFintype (Fin (bits n) → Bool)).map
            (attempt n)).toOuterMeasure {o | o.1 ≠ none}).toReal ∧
          W / S ≤ exp ((C + δ) * scale n)) →
      (∀ n (hn : 2 ≤ n) (tape : FairTreeTape bits n n.log2),
        ∃ xs : List ℕ,
          decodeFactors (fairSerializedFactorTree k sound bits attempt n hn tape).1 = some xs ∧
          xs.Perm n.primeFactorsList) ∧
      (∀ n (hn : 2 ≤ n),
        (PMF.uniformOfFintype (FairTreeTape bits n n.log2)).map
            (fairSerializedFactorTree k sound bits attempt n hn) =
          serializedFactor k sound
            (countedEpochHard bits (fun m => PMF.uniformOfFintype (Fin (bits m) → Bool)) attempt)
            n hn) ∧
      (∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n,
        mean (PMF.uniformOfFintype (FairTreeTape bits n n.log2))
          (fun tape => ((fairSerializedFactorTree k sound bits attempt n hn tape).2 : ℝ≥0∞)) ≤
          ENNReal.ofReal (exp ((C + ε) * scale n))) := by
  obtain ⟨k, sound, hmain⟩ := whole_tree_from_critical_line line
  refine ⟨k, sound, ?_⟩
  intro bits attempt C hC hEpoch
  obtain ⟨hcorr, hlaw, hexp⟩ :=
    hmain (α := fun m => Fin (bits m) → Bool) bits
      (fun m => PMF.uniformOfFintype (Fin (bits m) → Bool)) attempt hC hEpoch
  refine ⟨hcorr, ?_, ?_⟩
  · intro n hn
    rw [← fairTreeLaw_uniform]
    exact hlaw n hn
  · intro ε hε
    filter_upwards [hexp ε hε] with n h hn
    rw [← fairTreeLaw_uniform]
    exact h hn

#print axioms piFinLaw_uniform
#print axioms treeLaw_uniform
#print axioms fairTreeLaw_apply
#print axioms countedSplitTape_eq_runTape
#print axioms countedSplitTape_read_charge
#print axioms factorTree_correct
#print axioms factorTree_law
#print axioms serializedFactorTree_correct
#print axioms serializedFactorTree_law
#print axioms fairSerializedFactorTree_correct
#print axioms fairSerializedFactorTree_law
#print axioms whole_tree_from_critical_line
#print axioms fair_whole_tree_from_critical_line

end Cogentic.RandomizedWholeTreeTape
