import TwoThirdsFactor
import TwoThirdsSearch
import OrderQueries

namespace TwoThirdsFinish

open TwoThirdsFactor TwoThirdsSearch

/-- Divide out twos, returning their number and the odd part. -/
def stripTwos (m : Nat) : Nat × Nat :=
  if h : 0 < m ∧ m % 2 = 0 then
    let rest := stripTwos (m/2)
    (rest.1 + 1, rest.2)
  else (0,m)
termination_by m
decreasing_by omega

theorem stripTwos_spec (m : Nat) (hm : 0 < m) :
    let t := stripTwos m
    t.2 % 2 = 1 ∧ t.2 * 2^t.1 = m := by
  induction m using Nat.strongRecOn with
  | ind n ih =>
    rw [stripTwos]
    split
    · rename_i h
      have ⟨odd, product⟩ := ih (n/2) (by omega) (by omega)
      exact ⟨odd, by simp only [Nat.pow_succ, ← Nat.mul_assoc, product]; omega⟩
    · simpa using (show n % 2 = 1 by omega)

private theorem squareAt_powMod (n g t i : Nat) :
    OrderCertificate.squareAt n (ModularPower.powMod g t n) i = ModularPower.powMod g (t*2^i) n := by
  induction i generalizing t with
  | zero => simp [OrderCertificate.squareAt]
  | succ i ih =>
    have dbl : (ModularPower.powMod g t n * ModularPower.powMod g t n) % n = ModularPower.powMod g (t*2) n := by
      simp only [ModularPower.powMod_def, Nat.pow_mul, Nat.pow_two, Nat.mod_mul_mod, Nat.mul_mod_mod]
    rw [OrderCertificate.squareAt, dbl, ih, Nat.pow_succ]
    congr 1
    ac_rfl

/-- A local witness for one step of the square chain. The running algorithm never sees p or q. -/
def Separates (n m : Nat) (gs : List Nat) : Prop :=
  ∃ g ∈ gs, ∃ p q i, 1 < p ∧ 1 < q ∧ p ∣ n ∧ q ∣ n ∧ i < (stripTwos m).1 ∧
    ModularPower.powMod g ((stripTwos m).2 * 2^i) p = 1 ∧
    ModularPower.powMod g ((stripTwos m).2 * 2^i) q ≠ 1

private theorem two_power_dvd_odd {odd a b : Nat} (ho : odd % 2 = 1)
    (hd : 2^a ∣ odd * 2^b) : a ≤ b := by
  by_cases h : a ≤ b
  · exact h
  · have hs := Nat.pow_dvd_of_le_of_pow_dvd (by omega : b+1 ≤ a) hd
    rw [Nat.pow_succ, Nat.mul_comm (2^b) 2] at hs
    have even := Nat.dvd_of_mul_dvd_mul_right (by exact Nat.pow_pos (by decide : 0 < 2)) hs
    have := Nat.dvd_iff_mod_eq_zero.mp even
    omega

private theorem reduce_exponent {n g m p : Nat} (hp : 1 < p) (pn : p ∣ n)
    (killed : ModularPower.powMod g m n = 1) : ModularPower.powMod g m p = 1 := by
  rw [ModularPower.powMod_def] at killed ⊢
  have h := congrArg (fun x => x % p) killed
  simpa only [Nat.mod_mod_of_dvd _ pn, Nat.mod_eq_of_lt hp] using h

/-- Exact local orders of distinct 2-adic valuations force a separating square.
    Only the prime with the smaller valuation needs its odd part specified. -/
theorem separates_of_local_orders {n g m p q op oq u v : Nat} {gs : List Nat}
    (hg : g ∈ gs) (hm : 2 ≤ m)
    (killP : ModularPower.powMod g m p = 1) (killQ : ModularPower.powMod g m q = 1)
    (hp : 1 < p) (hq : 1 < q) (hpn : p ∣ n) (hqn : q ∣ n) (odd : op % 2 = 1) (uv : u < v)
    (orderP : ∀ e, ModularPower.powMod g e p = 1 ↔ op*2^u ∣ e)
    (orderQ : ∀ e, ModularPower.powMod g e q = 1 ↔ oq*2^v ∣ e) : Separates n m gs := by
  have pm := (orderP m).mp killP
  have qm := (orderQ m).mp killQ
  have ⟨oddM,recovers⟩ := stripTwos_spec m (by omega)
  have opm := Nat.dvd_trans (Nat.dvd_mul_right op (2^u)) pm
  have vm := Nat.dvd_trans (Nat.dvd_mul_left (2^v) oq) qm
  rw [← recovers] at opm vm
  have cop : op.Coprime 2 := by
    show op.gcd 2 = 1
    rw [Nat.gcd_comm, Nat.gcd_rec, odd]
    decide
  have dividesOdd := (cop.pow_right (stripTwos m).1).dvd_of_dvd_mul_right opm
  have within := two_power_dvd_odd oddM vm
  refine ⟨g,hg,p,q,u,hp,hq,hpn,hqn,by omega,(orderP _).mpr
    (Nat.mul_dvd_mul dividesOdd (Nat.dvd_refl _)),?_⟩
  intro h
  have hv := Nat.dvd_trans (Nat.dvd_mul_left (2^v) oq) ((orderQ _).mp h)
  have := two_power_dvd_odd oddM hv
  omega

def DistinctOrderTwos (n : Nat) (gs : List Nat) : Prop :=
  ∃ g ∈ gs, ∃ p q op oq u v, 1 < p ∧ 1 < q ∧ p ∣ n ∧ q ∣ n ∧ op % 2 = 1 ∧ u < v ∧
    (∀ e, ModularPower.powMod g e p = 1 ↔ op*2^u ∣ e) ∧
    (∀ e, ModularPower.powMod g e q = 1 ↔ oq*2^v ∣ e)

def splitBase (n m g : Nat) : Option {d // ProperDivisor n d} :=
  let t := stripTwos m
  match h : OrderCertificate.scan n (ModularPower.powMod g t.2 n) t.1 with
  | none => none
  | some d => some ⟨d, OrderCertificate.scan_sound h⟩

def finish {n : Nat} : Output n → Option {d // ProperDivisor n d}
  | .divisor d hd => some ⟨d, hd⟩
  | .orders m _ _ gs _ => gs.findSome? (splitBase n m)

/-- The common exponent only has to kill the bases modulo the two distinguishing primes. -/
def splitWithExponent (n m : Nat) (gs : List Nat) : Option {d // ProperDivisor n d} :=
  gs.findSome? (splitBase n m)

theorem chain_hits {n m : Nat} (hn : 2 ≤ n) (gs : List Nat) (sep : Separates n m gs) :
    splitWithExponent n m gs ≠ none := by
  obtain ⟨g,hg,p,q,i,hp,hq,hpn,hqn,hi,left,right⟩ := sep
  let x := OrderCertificate.squareAt n (ModularPower.powMod g (stripTwos m).2 n) i
  have xl : x % p = 1 := by
    simpa only [x, squareAt_powMod, ModularPower.powMod_def, Nat.mod_mod_of_dvd _ hpn] using left
  have xr : x % q ≠ 1 := by
    simpa only [x, squareAt_powMod, ModularPower.powMod_def, Nat.mod_mod_of_dvd _ hqn] using right
  have hx := Nat.mod_add_div x p
  rw [xl] at hx
  have pd : p ∣ x-1 := ⟨x/p, by omega⟩
  have qd : ¬q ∣ x-1 := by
    rintro ⟨k,hk⟩
    have eq : x = 1 + q*k := by omega
    apply xr
    simp [eq, Nat.add_mod, Nat.mod_eq_of_lt hq]
  obtain ⟨d,found⟩ := OrderCertificate.scan_hits (by omega) hp hpn hqn hi pd qd
  intro missing
  have miss := List.findSome?_eq_none_iff.mp missing g hg
  simp only [splitBase] at miss
  split at miss <;> grind

/-- A common verified exponent plus a distinguishing residue suffice for this explicit splitter. -/
theorem finish_hits {n : Nat} (hn : 2 ≤ n) (gs : List Nat) (out : Output n)
    (covered : out.covers gs)
    (separating : ∀ m, 2 ≤ m → 2 ∣ m → (∀ g ∈ gs, ModularPower.powMod g m n = 1) → Separates n m gs) :
    finish out ≠ none := by
  cases out with
  | divisor d hd => simp [finish]
  | orders m big even retained valid =>
    change retained = gs at covered
    subst retained
    exact chain_hits hn gs (separating m big even valid)

/-- The remaining supply assertions concern individual four-coordinate boxes
    and the arithmetic of the generator list, independently of the divisor search. -/
structure GeneratorData (n : Nat) where
  primeTest : Bool
  primeCorrect : primeTest = true ↔ IsPrime n
  early : Option {d // ProperDivisor n d}
  L₀ : Nat
  U : Nat
  A : Nat
  generators : List Nat
  attempt : TryPair
  coverage : ¬IsPrime n → early = none → ∀ g ∈ generators,
    BoxWitness n (2*L₀^2*U*A) (2*L₀^2*U) attempt g
  distinctOrders : ¬IsPrime n → early = none → DistinctOrderTwos n generators

def generatorDecision {n : Nat} (hn : 2 ≤ n) (s : GeneratorData n) : Decision n :=
  if h : s.primeTest = true then .prime (s.primeCorrect.mp h)
  else match he : s.early with
  | some ⟨d,hd⟩ => .split d ⟨hd.1,hd.2.1⟩ hd.2.2
  | none => by
    have composite : ¬ IsPrime n := fun hp => h (s.primeCorrect.mpr hp)
    let run := collect hn (searchBox n (2*s.L₀^2*s.U*s.A) (2*s.L₀^2*s.U) s.attempt) s.generators
    have covers := (gaussian_generator_search hn s.L₀ s.U s.A s.generators s.attempt
      (s.coverage composite he)).1
    have succeeds : finish run.1 ≠ none := by
      apply finish_hits hn s.generators run.1 covers
      intro m hm _ kills
      obtain ⟨g,hg,p,q,op,oq,u,v,hp,hq,pn,qn,odd,uv,ordP,ordQ⟩ := s.distinctOrders composite he
      exact separates_of_local_orders hg hm (reduce_exponent hp pn (kills g hg))
        (reduce_exponent hq qn (kills g hg)) hp hq pn qn odd uv ordP ordQ
    match hf : finish run.1 with
    | some ⟨d,hd⟩ => exact .split d ⟨hd.1,hd.2.1⟩ hd.2.2
    | none => exact False.elim (succeeds hf)

def factorFromGenerators (data : (k : Nat) → 2 ≤ k → GeneratorData k) (n : Nat) (hn : 2 ≤ n) : Run n :=
  factor (fun k hk => generatorDecision hk (data k hk)) n hn

theorem factor_from_generators (data : (k : Nat) → 2 ≤ k → GeneratorData k) (n : Nat) (hn : 2 ≤ n)
    (charge : Nat → Nat) (cap : Nat) (bound : ∀ k, 2 ≤ k → k ≤ n → charge k ≤ cap) :
    let t := factorFromGenerators data n hn
    t.factors.prod = n ∧ (∀ p ∈ t.factors, IsPrime p) ∧
      (∀ p, IsPrime p → ∀ k, p^k ∣ n ↔ k ≤ t.factors.count p) ∧
      t.work charge ≤ (2*n.log2-1)*cap :=
  factor_correct_and_cost _ n hn charge cap bound

end TwoThirdsFinish

#print axioms TwoThirdsFinish.factor_from_generators
