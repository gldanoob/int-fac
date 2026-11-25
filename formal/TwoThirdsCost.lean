import Std

namespace TwoThirdsCost

/-- The multiplier used by the fixed-schedule order splitter. -/
def indexLcm : Nat → Nat
  | 0 => 1
  | k+1 => Nat.lcm (indexLcm k) (k+1)

theorem index_dvd_lcm {i k : Nat} (pos : 0 < i) (bounded : i ≤ k) : i ∣ indexLcm k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : i ≤ k
    · exact Nat.dvd_trans (ih h) (Nat.dvd_lcm_left _ _)
    · have eq : i = k + 1 := by omega
      subst i
      exact Nat.dvd_lcm_right _ _

/-- The product count supplies the first inequality. Taking k to be the
    integer logarithm of the group order supplies the second. -/
theorem subgroup_index_bound {size index B h k : Nat}
    (count : B^k ≤ size * h^k) (order : size * index < B^(k+1)) :
    index < B * h^k := by
  apply Nat.lt_of_mul_lt_mul_left (a := size)
  calc
    size * index < B^(k+1) := order
    _ = B^k * B := Nat.pow_succ ..
    _ ≤ (size * h^k) * B := Nat.mul_le_mul_right B count
    _ = size * (B * h^k) := by ac_rfl

/-- A common exponent killing a subgroup suffices even when its order and
    index share a prime. The group and subgroup orders enter as integer data. -/
theorem saturate_order {order size index exponent k : Nat} (hOrder : order = size * index)
    (hSize : size ∣ exponent) (positive : 0 < index) (bounded : index ≤ k) :
    order ∣ exponent * indexLcm k := by
  rw [hOrder]
  exact Nat.mul_dvd_mul hSize (index_dvd_lcm positive bounded)

/-- An integer envelope for b^(2/3) (1 + log₂ b)^(1/3). -/
def scale (b : Nat) : Nat :=
  let j := b.log2 + 1
  let k := j.log2 + 1
  2 ^ ((2*j + k + 2) / 3)

private theorem dyadic_upper (b : Nat) (pos : b ≠ 0) :
    2 ^ (b.log2 + 1) ≤ b * 2 := by
  rw [Nat.pow_succ]
  exact Nat.mul_le_mul_right _ (Nat.log2_self_le pos)

theorem scale_cubed (b : Nat) (pos : b ≠ 0) :
    b^2 * (b.log2+1) ≤ (scale b)^3 ∧
    (scale b)^3 ≤ 32 * (b^2 * (b.log2+1)) := by
  let j := b.log2 + 1
  let k := j.log2 + 1
  let e := (2*j+k+2)/3
  have lo : 2*j+k ≤ e*3 := by dsimp [e]; omega
  have hi : e*3 ≤ 2*j+k+2 := by dsimp [e]; omega
  have prod : 2^(2*j+k) = (2^j)^2 * 2^k := by
    rw [Nat.pow_add, Nat.mul_comm 2 j, Nat.pow_mul]
  change b^2*j ≤ (2^e)^3 ∧ (2^e)^3 ≤ 32 * (b^2*j)
  rw [← Nat.pow_mul]
  constructor
  · calc
      b^2*j ≤ (2^j)^2*2^k := Nat.mul_le_mul
        (Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_log2_self) 2)
        (Nat.le_of_lt Nat.lt_log2_self)
      _ = 2^(2*j+k) := prod.symm
      _ ≤ 2^(e*3) := Nat.pow_le_pow_right (by decide) lo
  · calc
      2^(e*3) ≤ 2^(2*j+k+2) := Nat.pow_le_pow_right (by decide) hi
      _ = ((2^j)^2*2^k)*4 := by rw [Nat.pow_add _ (2*j+k), prod]
      _ ≤ ((b*2)^2*(j*2))*4 := Nat.mul_le_mul_right _ (Nat.mul_le_mul
        (Nat.pow_le_pow_left (dyadic_upper b pos) 2)
        (dyadic_upper j (by simp [j])))
      _ = 32 * (b^2*j) := by
        rw [Nat.mul_pow]
        change b^2*4*(j*2)*4 = (4*2*4)*(b^2*j)
        ac_rfl

/-- A completed or partial tree whose leaves are integers at least two. -/
inductive SplitTree where
  | leaf (n : Nat) (atLeastTwo : 2 ≤ n)
  | split (left right : SplitTree)

def SplitTree.product : SplitTree → Nat
  | .leaf n _ => n
  | .split l r => l.product*r.product

def SplitTree.leaves : SplitTree → Nat
  | .leaf .. => 1
  | .split l r => l.leaves+r.leaves

def SplitTree.nodes : SplitTree → Nat
  | .leaf .. => 1
  | .split l r => 1+l.nodes+r.nodes

theorem split_tree_cost (t : SplitTree) :
    2^t.leaves ≤ t.product ∧ t.nodes+1 = 2*t.leaves := by
  induction t with
  | leaf _ h => exact ⟨h,rfl⟩
  | split l r left right =>
    simp only [SplitTree.product, SplitTree.leaves, SplitTree.nodes, Nat.pow_add]
    exact ⟨Nat.mul_le_mul left.1 right.1, by omega⟩

/-- The six factors count recursion, generators, Gaussian box overhead, four
    perturbation coordinates, two mark-width factors, and work per call. -/
theorem four_coordinate_budget (nodes generators roundoff width marks perCall c s : Nat)
    (hn : nodes ≤ 2^(c*s)) (hg : generators ≤ 2^(c*s))
    (hr : roundoff ≤ 2^(c*s)) (hu : width ≤ 2^(c*s))
    (ha : marks ≤ 2^(c*s)) (hp : perCall ≤ 2^(c*s)) :
    nodes*generators*roundoff^8*width^4*marks^2*perCall ≤ 2^(17*(c*s)) := by
  let m := 2^(c*s)
  have h : nodes*generators*roundoff^8*width^4*marks^2*perCall ≤
      m*m*m^8*m^4*m^2*m :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
      (Nat.mul_le_mul hn hg) (Nat.pow_le_pow_left hr 8))
      (Nat.pow_le_pow_left hu 4)) (Nat.pow_le_pow_left ha 2)) hp
  calc
    _ ≤ _ := h
    _ = m^17 := by simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc]
    _ = 2^(17*(c*s)) := by rw [Nat.mul_comm 17, Nat.pow_mul]

end TwoThirdsCost
