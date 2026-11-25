import Cogentic.RootProductCost
import Cogentic.ConstructionTarget

namespace Cogentic.BinaryConstructorGrid
open BinaryDivision BinaryPivot BinarySaturation BinaryPreliminary BinaryRootProduct Construction

/-- Emit every canonical word in a finite arithmetic progression. -/
def progression (step : List Bool) : List Unit → List Bool → List (List Bool) × ℕ
  | [], _ => ([],1)
  | _::ts,a =>
    let sum := addDigits (max a.length step.length) a step false
    let next := canonical sum.1
    let tail := progression step ts next.1
    (a::tail.1,sum.2+next.2+tail.2+a.length+3)

theorem progression_spec (step a : ℕ) (ts : List Unit) (W : ℕ) (sw : step.size ≤ W)
    (room : (a+ts.length*step).size ≤ W) :
    let out := progression step.bits ts a.bits
    out.1=(List.range' a ts.length step).map Nat.bits ∧ out.2 ≤ 1+ts.length*(9*W+6) := by
  induction ts generalizing a with
  | nil => simp [progression]
  | cons t ts ih =>
    simp only [List.length_cons,Nat.succ_mul] at room
    have aw := (Nat.size_le_size (show a ≤ a+(ts.length*step+step) by omega)).trans room
    have bounds : (a+step+ts.length*step).size ≤ W := by simpa only [Nat.add_assoc,Nat.add_comm step (ts.length*step)] using room
    let sum := addDigits (max a.bits.length step.bits.length) a.bits step.bits false
    let next := canonical sum.1
    obtain ⟨sl,sc,sv⟩ := addDigits_spec _ a.bits step.bits false (le_max_left ..) (le_max_right ..)
    change sum.1.length=_ at sl
    change sum.2=_ at sc
    change value sum.1=_ at sv
    simp only [Nat.size_eq_bits_len] at sl sc
    simp only [value_bits,Bool.toNat_false,Nat.add_zero] at sv
    obtain ⟨nv,nc⟩ := canonical_spec sum.1
    change next.1=_ at nv
    change next.2=_ at nc
    rw [sv] at nv
    rw [sl] at nc
    obtain ⟨v,c⟩ := ih (a+step) bounds
    change a.bits::(progression step.bits ts next.1).1=_ ∧ sum.2+next.2+(progression step.bits ts next.1).2+a.bits.length+3 ≤ _
    rw [nv,v,List.length_cons,List.range'_succ,List.map_cons,Nat.succ_mul ts.length,sc,nc,Nat.size_eq_bits_len]
    exact ⟨rfl,by omega⟩

def start (A : ℕ) (side : Bool) := if side then 2*A else A

def gridRoots (d A : ℕ) (side : Bool) := List.range' (start A side) d (2*A)

theorem grid_fractions (d A : ℕ) (side : Bool) :
    (gridRoots d A side).map (fun r : ℕ=>(r:ℚ)/(4*d:ℕ))=(targets d side).map ((A:ℚ)*·) := by
  apply List.ext_getElem
  · simp [gridRoots,targets]
  · intro i hi hj
    simp only [List.getElem_map,gridRoots,List.getElem_range',targets,List.getElem_range]
    cases side <;> simp [start] <;> ring

/-- Construct every numerator of the grid target polynomial and their common
denominator from degree, amplitude and side. -/
def targetProduct (d A : List Bool) (side : Bool) : Product :=
  let step := natProduct [false,true] A
  let D := natProduct [false,false,true] d
  let fuel := tokens d
  let roots := progression step.1 fuel.1 (if side then step.1 else A)
  let out := build D.1 roots.1 [encode 1] [true]
  ⟨out.coeffs,out.den,step.2+D.2+fuel.2+roots.2+out.gates+3⟩

theorem targetProduct_spec (d A : ℕ) (side : Bool) {W : ℕ} (dp : 0<d) (ws : 3 ≤ W) (ds : d.size ≤ W)
    (ds' : (4*d).size ≤ W) (aw : A.size ≤ W) (gridWidth : (2*A+d*(2*A)).size ≤ W) :
    let out := targetProduct d.bits A.bits side
    let T := 16^d*W
    ∃ (nums : List ℤ) (D : ℕ), out.coeffs=nums.map encode ∧ out.den=D.bits ∧ 0<D ∧
      fractions nums D=fromRoots ((targets d side).map ((A:ℚ)*·)) ∧
      (∀ z∈nums,z.natAbs.size ≤ T) ∧ D.size ≤ T ∧
      out.gates ≤ 2^16*(d+1)^2*(T+1)^2 := by
  intro out T
  let step := natProduct [false,true] A.bits
  let den := natProduct [false,false,true] d.bits
  let fuel := tokens d.bits
  let roots := progression step.1 fuel.1 (if side then step.1 else A.bits)
  obtain ⟨sv,_,sc⟩ := natProduct_spec 2 A (W:=W) (by change 2 ≤ W; omega) aw
  obtain ⟨dv,_,dc⟩ := natProduct_spec 4 d (W:=W) ws ds
  change step.1=_ at sv
  change step.2 ≤ _ at sc
  change den.1=_ at dv
  change den.2 ≤ _ at dc
  obtain ⟨fl,fc⟩ := token_spec d.bits
  change fuel.1.length=_ at fl
  change fuel.2 ≤ _ at fc
  simp only [Nat.size_eq_bits_len,value_bits] at fl fc
  have x₀ : start A side ≤ 2*A := by cases side <;> simp [start]; omega
  have sW : (2*A).size ≤ W := (Nat.size_le_size (Nat.le_add_right ..)).trans gridWidth
  obtain ⟨v,c⟩ := progression_spec (2*A) (start A side) fuel.1 W sW (by
    rw [fl]
    exact (Nat.size_le_size (Nat.add_le_add_right x₀ _)).trans gridWidth)
  have initial : (start A side).bits=(if side then step.1 else A.bits) := by cases side <;> simp [start,sv]
  rw [←sv,initial,fl] at v c
  change roots.1=(gridRoots d A side).map Nat.bits at v
  change roots.2 ≤ _ at c
  have bounds (r : ℕ) (hr : r∈gridRoots d A side) : r.size ≤ W := by
    obtain ⟨j,sj,eq⟩ := List.mem_range'.mp hr
    have jr := Nat.mul_le_mul_left (2*A) sj.le
    have : r ≤ 2*A+d*(2*A) := by rw [Nat.mul_comm d (2*A)]; omega
    exact (Nat.size_le_size this).trans gridWidth
  have ⟨nums,D,e₁,e₂,positive,same,width,denw,work⟩ := root_product (4*d) (gridRoots d A side) (W:=W)
    (by omega) (by positivity) ds' bounds
  have len : (gridRoots d A side).length=d := List.length_range'
  rw [grid_fractions] at same
  rw [len] at width denw work
  rw [←dv,←v] at e₁ e₂ work
  refine ⟨nums,D,e₁,e₂,positive,same,width,denw,?_⟩
  have p : 0<16^d := Nat.pow_pos (by decide)
  have up : W ≤ T := Nat.le_mul_of_pos_left _ p
  have pt := sc.trans (show 30*(W+1)^2 ≤ 30*(T+1)^2 by gcongr)
  have dt := dc.trans (show 30*(W+1)^2 ≤ 30*(T+1)^2 by gcongr)
  have gg := c.trans (show 1+d*(9*W+6) ≤ 1+d*(9*T+6) by gcongr)
  change (build den.1 roots.1 [encode 1] [true]).gates ≤ 1+d*(d+3)*(6000*(T+1)^2) at work
  change step.2+den.2+fuel.2+roots.2+(build den.1 roots.1 [encode 1] [true]).gates+3 ≤ _
  nlinarith only [pt,dt,gg,fc,work,ds,up,Nat.zero_le (T^2),Nat.zero_le T,Nat.zero_le (d*T),
    Nat.zero_le (d*T^2),Nat.zero_le d,Nat.zero_le (d^2),Nat.zero_le (d^2*T),Nat.zero_le (d^2*T^2)]

end Cogentic.BinaryConstructorGrid

#print axioms Cogentic.BinaryConstructorGrid.targetProduct_spec
