import Cogentic.AffineMark
import Cogentic.CleanWindows

namespace Cogentic.Construction

/-- Distinct non-target primes with one prescribed root per prime. -/
structure PrescribedRows (n ell : ℕ) where
  primes : Finset ℕ
  residue : ℕ → ℕ
  member : primes ⊆ sieveBand n ell 1
  limit : primes.card ≤ 2
  excluded : ell ∉ primes
  away : ∀ q ∈ primes, (residue q : ZMod q) ≠ Fixed.rootBase n

def PrescribedRows.hit {n ell : ℕ} (R : PrescribedRows n ell) (a : ℕ) :=
  R.primes.filter (fun q => (R.residue q:ZMod q) = a)

def PrescribedRows.miss {n ell : ℕ} (R : PrescribedRows n ell) (a : ℕ) :=
  R.primes \ R.hit a

def prodPrimes (s : Finset ℕ) := ∏ q ∈ s, q

def PrescribedRows.hitProduct {n ell : ℕ} (R : PrescribedRows n ell) (a : ℕ) := prodPrimes (R.hit a)

def targetPart (n ell a : ℕ) (side : Bool) := if hitsTarget n ell a side then ell else 1

def PrescribedRows.prefactor {n ell : ℕ} (R : PrescribedRows n ell) (a : ℕ) (side : Bool) :=
  targetPart n ell a side*R.hitProduct a

theorem PrescribedRows.prime {n ell : ℕ} (R : PrescribedRows n ell) {q : ℕ} (mem : q ∈ R.primes) :
    q.Prime := (mem_primeBand.mp (Finset.mem_filter.mp (R.member mem)).1).1

theorem PrescribedRows.subprod_bounds {n ell : ℕ} (R : PrescribedRows n ell) {s : Finset ℕ} (sub : s ⊆ R.primes) :
    0 < prodPrimes s ∧ prodPrimes s ≤ (Fixed.B (n.log2+1))^2 := by
  have bp : 0 < Fixed.B (n.log2+1) := Nat.pow_pos (by decide)
  refine ⟨Finset.prod_pos (fun p hp => (R.prime (sub hp)).pos),?_⟩
  calc prodPrimes s ≤ ∏ _p ∈ s, Fixed.B (n.log2+1) := Finset.prod_le_prod' (fun p hp =>
        (mem_primeBand.mp (Finset.mem_filter.mp (R.member (sub hp))).1).2.1)
       _ = (Fixed.B (n.log2+1))^s.card := by simp
       _ ≤ _ := Nat.pow_le_pow_right bp ((Finset.card_le_card sub).trans R.limit)

private theorem target_factorization (n ell a : ℕ) (side : Bool) :
    ell = (if hitsTarget n ell a side then 1 else ell)*targetPart n ell a side := by
  unfold targetPart; split <;> simp_all

theorem PrescribedRows.pre_bounds {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (a : ℕ) (side : Bool) :
    0<R.prefactor a side ∧ R.prefactor a side ≤ (Fixed.B (n.log2+1))^3 := by
  let B := Fixed.B (n.log2+1)
  have ⟨hp,hB⟩ := R.subprod_bounds (Finset.filter_subset (fun q => (R.residue q:ZMod q)=a) R.primes)
  have ep := (mem_dyadicTargets.mp target).1.pos
  have cap : ell ≤ B := (mem_dyadicTargets.mp target).2.2
  have tp : 0 < targetPart n ell a side := by unfold targetPart; split <;> omega
  have tb : targetPart n ell a side ≤ B := by unfold targetPart; split <;> omega
  exact ⟨Nat.mul_pos tp hp,(Nat.mul_le_mul tb hB).trans_eq (by ring)⟩

/-- The submitted coefficient pair satisfies the actual polynomial root
    condition modulo each prescribed rational prime. -/
def PrescribedRows.compatible {n ell : ℕ} (R : PrescribedRows n ell) (side : Bool) (u v : ℤ) : Prop :=
  ∀ q ∈ R.primes, (q:ℤ) ∣ affineValue n ell (R.residue q) side (u+(R.residue q)*v)

theorem affine_mark_congr {n ell a r q : ℕ} (side : Bool) (u v : ℤ) (eq : (a:ZMod q) = r) :
    ((affineValue n ell a side (u+a*v):ℤ):ZMod q) = ((affineValue n ell r side (u+r*v):ℤ):ZMod q) := by
  have cast (f : List ℤ) : ((eval (a:ℤ) f:ℤ):ZMod q) = ((eval (r:ℤ) f:ℤ):ZMod q) := by
    induction f with
    | nil => rfl
    | cons c l ih => simp [eval,eq,ih]
  simp [affineValue,eq,cast]

theorem PrescribedRows.pre_dvd {n ell : ℕ} (R : PrescribedRows n ell)
    (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1))) (a : ℕ) (side : Bool) (u v : ℤ)
    (ok : R.compatible side u v) :
    (R.prefactor a side:ℤ) ∣ affineValue n ell a side (u+a*v) := by
  let h := R.hit a
  let y := affineValue n ell a side (u+a*v)
  let T := targetPart n ell a side
  have hit (q : ℕ) (hq : q∈h) := Finset.mem_filter.mp hq
  have each (q : ℕ) (hq : q∈h) : (q:ℤ) ∣ y := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
    rw [show ((y:ℤ):ZMod q) = ((affineValue n ell (R.residue q) side (u+R.residue q*v):ℤ):ZMod q) from
      affine_mark_congr side u v (hit q hq).2.symm]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr (ok q (hit q hq).1)
  have whole (q : ℕ) (hq : q ∈ h) := R.prime (hit q hq).1
  have divH : (R.hitProduct a:ℤ) ∣ y := by
    change ((∏ q ∈ h, q : ℕ):ℤ) ∣ y
    rw [Nat.cast_prod]
    exact Finset.prod_dvd_of_coprime (s := fun q : ℕ => (q:ℤ)) (fun p hp q hq ne =>
      ((Nat.coprime_primes (whole p hp) (whole q hq)).mpr ne).isCoprime) each
  have divT : (T:ℤ) ∣ y := by
    dsimp [T,targetPart]; split
    next h => exact (target_hits_iff n ell a side _).mp h
    next => simp
  have co : T.Coprime (R.hitProduct a) := by
    dsimp [T,targetPart]; split
    · apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      exact (Nat.coprime_primes (mem_dyadicTargets.mp target).1 (whole q hq)).mpr
        (fun eq => R.excluded (eq ▸ (hit q hq).1))
    · simp
  change ((T*R.hitProduct a:ℕ):ℤ) ∣ y
  rw [Nat.cast_mul]
  exact co.isCoprime.mul_dvd divT divH

/-- The primes hitting both marks give exactly the factors dividing the
    difference of the two marks in the second lattice step. -/
theorem PrescribedRows.second_factors {n ell : ℕ} (R : PrescribedRows n ell) (a a' : ℕ) :
    let both := prodPrimes (R.hit a ∩ R.hit a')
    let fresh := prodPrimes (R.hit a' \ R.hit a)
    let free := prodPrimes (R.miss a \ R.hit a')
    R.hitProduct a' = both*fresh ∧ prodPrimes (R.miss a) = fresh*free ∧
      (both:ℤ) ∣ (a':ℤ)-a ∧ 0<both ∧ 0<fresh ∧ 0<free ∧ free ≤ (Fixed.B (n.log2+1))^2 := by
  classical
  let h := R.hit a; let h' := R.hit a'; let f := R.miss a
  have hsub : h ⊆ R.primes := Finset.filter_subset ..
  have hsub' : h' ⊆ R.primes := Finset.filter_subset ..
  have bsub : h ∩ h' ⊆ R.primes := Finset.Subset.trans Finset.inter_subset_left hsub
  have fsub : f ⊆ R.primes := Finset.sdiff_subset
  have freshSub : h' \ h ⊆ R.primes := Finset.Subset.trans Finset.sdiff_subset hsub'
  have remSub : f \ h' ⊆ R.primes := Finset.Subset.trans Finset.sdiff_subset fsub
  have eq1 : h' = (h ∩ h') ∪ (h' \ h) := by ext p; simp; tauto
  have eq2 : f = (h' \ h) ∪ (f \ h') := by
    ext p
    by_cases hp : p∈h'
    · have base := hsub' hp
      simp [f,PrescribedRows.miss,h',h,hp,base] at * <;> tauto
    · simp [hp]
  have ds1 : Disjoint (h∩h') (h'\h) := Finset.disjoint_left.mpr (fun _ hi hx => (Finset.mem_sdiff.mp hx).2 (Finset.mem_inter.mp hi).1)
  have ds2 : Disjoint (h'\h) (f\h') := Finset.disjoint_left.mpr (fun _ hi hx => (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hi).1)
  have pdiv (q : ℕ) (hq : q∈h∩h') : (q:ℤ) ∣ (a':ℤ)-a := by
    obtain ⟨one,two⟩ := Finset.mem_inter.mp hq
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
    push_cast
    exact sub_eq_zero.mpr ((Finset.mem_filter.mp two).2.symm.trans (Finset.mem_filter.mp one).2)
  refine ⟨?_,?_,?_,(R.subprod_bounds bsub).1,(R.subprod_bounds freshSub).1,(R.subprod_bounds remSub).1,(R.subprod_bounds remSub).2⟩
  · change prodPrimes h' = _
    conv_lhs => rw [eq1]
    exact Finset.prod_union ds1
  · change prodPrimes f = _
    conv_lhs => rw [eq2]
    exact Finset.prod_union ds2
  · change ((∏ q ∈ h∩h', q : ℕ):ℤ) ∣ _
    rw [Nat.cast_prod]
    exact Finset.prod_dvd_of_coprime (s := fun q : ℕ => (q:ℤ)) (fun p hp q hq ne =>
      ((Nat.coprime_primes (R.prime (bsub hp)) (R.prime (bsub hq))).mpr ne).isCoprime) pdiv

end Cogentic.Construction

#print axioms Cogentic.Construction.PrescribedRows.pre_dvd
#print axioms Cogentic.Construction.PrescribedRows.second_factors
