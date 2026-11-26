import Cogentic.ScheduleWords
import Cogentic.LeadingCoefficientCost

namespace Cogentic.BinarySchedule
open BinaryDivision BinarySaturation

structure Setup where
  schedule : Words
  root : List Bool
  primorial : List Bool
  leading : List Bool

/-- Shared constructor state from the binary input. Canonicalize the padded
root before using it in the leading coefficient calculation. -/
def setup (n : List Bool) : Setup × ℕ :=
  let sc := run n
  let base := BinaryPowerScan.computedBase n
  let m := canonical base.1
  let p := BinaryPrimorial.run sc.1.degree
  let c := BinaryLeading.run sc.1.bits sc.1.degree sc.1.K₁ sc.1.B sc.1.U sc.1.A m.1 p.1
  (⟨sc.1,m.1,p.1,c.1⟩, sc.2+base.2+m.2+p.2+c.2+1)

attribute [local irreducible] run BinaryPowerScan.computedBase BinaryPrimorial.run BinaryLeading.run canonical

set_option maxHeartbeats 500000 in
theorem setup_spec {n : ℕ} (hn : 2≤n) (big : 2≤Fixed.d (n.log2+1)) :
    let b := n.log2+1
    let out := setup n.bits
    out.1=⟨⟨b.bits,(Fixed.d b).bits,(Fixed.beta b).bits,(Fixed.B b).bits,
       (Fixed.A b).bits,(Fixed.K₁ b).bits,(Fixed.invWidth b).bits,(Fixed.U b).bits⟩,
       (Fixed.rootBase n).bits,(primorial (Fixed.d b)).bits,(Construction.leadingCoefficient n).bits⟩ ∧
    out.2 ≤ 2^(600028*TwoThirdsCost.scale b) := by
  intro b out
  have np : 0<n := by omega
  have bp : 0<b := Nat.succ_pos _
  have len : n.bits.length=b := by
    rw [Nat.size_eq_bits_len]
    exact le_antisymm (Nat.size_le.mpr Nat.lt_log2_self) (Nat.lt_size.mpr (Nat.log2_self_le np.ne'))
  obtain ⟨sw,sc⟩ := fixed_words n.bits (len ▸ bp)
  rw [len] at sw sc
  obtain ⟨degree,_⟩ := BinaryPowerScan.degreeFuel_spec n.bits (len ▸ bp)
  have rv := BinaryPowerScan.driver_root_setup np
  have rl := (BinaryPowerScan.fixed_root_base np).2.1
  have raw : (BinaryPowerScan.computedBase n.bits).1.length = b+1 := by
    simpa only [BinaryPowerScan.computedBase,BinaryPowerScan.rootBase,degree] using rl
  obtain ⟨mv,mc⟩ := canonical_spec (BinaryPowerScan.computedBase n.bits).1
  rw [rv.1] at mv
  rw [raw] at mc
  obtain ⟨pv,pc⟩ := BinaryPrimorial.fixed_primorial bp
  obtain ⟨cv,cc⟩ := BinaryLeading.fixed_leading hn big
  dsimp only [setup,out]
  rw [sw,mv,pv]
  refine ⟨congrArg (fun w => Setup.mk _ _ _ w) cv,?_⟩
  let S := TwoThirdsCost.scale b
  let cap := 2^(600025*S)
  have dp := Fixed.degree_pos bp
  have zs : Fixed.z b≤S := (Nat.le_mul_of_pos_left _ dp).trans
    ((Nat.le_mul_of_pos_left _ dp).trans (Fixed.scale_bounds bp).1)
  have sp : 0<S := (Nat.succ_pos _).trans_le zs
  have weaken {k : ℕ} (h : k≤600025) : 2^(k*S)≤cap :=
    Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_right S h)
  have bit : b+1 ≤ 2^S := Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two zs)
  have mcap : 3*(b+1)≤cap := calc
    _ ≤ 2^2*2^S := Nat.mul_le_mul (by decide) bit
    _ = 2^(2+S) := (pow_add ..).symm
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  have rcap := (Nat.le_add_left (BinaryPowerScan.computedBase n.bits).2 _).trans (rv.2.2.trans (weaken (by decide)))
  have pcap := pc.trans (weaken (by decide))
  have scap := sc.trans (weaken (by decide))
  have ccap : 0<cap := Nat.two_pow_pos _
  rw [mc]
  dsimp only
  change (BinaryLeading.run b.bits (Fixed.d b).bits (Fixed.K₁ b).bits (Fixed.B b).bits (Fixed.U b).bits
    (Fixed.A b).bits (Fixed.rootBase n).bits (primorial (Fixed.d b)).bits).2 ≤ cap at cc
  change _ ≤ 2^(600028*S)
  calc
    _ ≤ 8*cap := by omega
    _ = 2^(3+600025*S) := (pow_add 2 3 (600025*S)).symm
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)

end Cogentic.BinarySchedule
