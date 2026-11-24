import Std

namespace PrimitiveCertificate

/-- The two bounded residues and their quotients are included in the witness. -/
structure Certificate (a m c : Nat) where
  d : Nat
  x : Nat
  y : Nat
  u : Nat
  v : Nat
  w : Nat
  t : Nat
  d_pos : 0 < d
  x_pos : 0 < x
  c_pos : 0 < c
  factor_a : a = d * x
  factor_m : m = d * y
  first_eq : y * u + 1 = x * v
  u_lt : u < x
  second_eq : d * w + 1 = c * t
  w_lt : w < c

private theorem gcd_of_eq {n k r q : Nat} (h : k * r + 1 = n * q) :
    n.gcd k = 1 := by
  apply Nat.eq_one_of_dvd_one
  apply (Nat.dvd_add_right (Nat.dvd_mul_right_of_dvd (Nat.gcd_dvd_right n k) r)).mp
  rw [h]
  exact Nat.dvd_mul_right_of_dvd (Nat.gcd_dvd_left n k) q

theorem Certificate.gcd_eq {a m c : Nat} (s : Certificate a m c) :
    a.gcd m = s.d := by
  calc
    _ = (s.d * s.x).gcd (s.d * s.y) := congr (congrArg Nat.gcd s.factor_a) s.factor_m
    _ = s.d := by rw [Nat.gcd_mul_left, gcd_of_eq s.first_eq, Nat.mul_one]

theorem Certificate.primitive {a m c : Nat} (s : Certificate a m c) :
    (a.gcd m).gcd c = 1 := by
  rw [s.gcd_eq, Nat.gcd_comm]
  exact gcd_of_eq s.second_eq

-- Euclidean induction produces an integer Bézout identity before reduction.
private theorem bezout (n k : Nat) :
    ∃ p q : Int, (n : Int) * p + (k : Int) * q = (n.gcd k : Nat) := by
  induction n, k using Nat.gcd.induction with
  | H0 k => exact ⟨0, 1, by simp⟩
  | H1 n k _ ih =>
    obtain ⟨p, q, h⟩ := ih
    refine ⟨q - (k / n : Nat) * p, p, ?_⟩
    rw [Nat.gcd_rec n k]
    rw [← h, Int.natCast_emod, Int.emod_def, Int.natCast_ediv]
    grind

private theorem bounded_exists {n k : Nat} (hn : 0 < n) (hc : n.gcd k = 1) :
    ∃ r q : Nat, r < n ∧ k * r + 1 = n * q := by
  obtain ⟨p, b, h⟩ := bezout n k
  rw [hc] at h
  let z := (-b) % (n : Int)
  have hz : 0 ≤ z := Int.emod_nonneg _ (by omega)
  have hlt : z < (n : Int) := Int.emod_lt_of_pos _ (by omega)
  have he : (k : Int) * z + 1 = (n : Int) * (p - k * ((-b) / n)) := by
    dsimp [z]
    rw [Int.emod_def]
    grind
  have hd : n ∣ k * z.toNat + 1 := by
    apply Int.ofNat_dvd.mp
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_one, Int.toNat_of_nonneg hz]
    exact ⟨_, he⟩
  obtain ⟨q, hq⟩ := hd
  exact ⟨z.toNat, q, by omega, hq⟩

private theorem bounded_unique {n k r q r' q' : Nat}
    (hr : r < n) (hr' : r' < n)
    (h : k * r + 1 = n * q) (h' : k * r' + 1 = n * q') :
    r = r' ∧ q = q' := by
  have cross : r + (q * r') * n = r' + (q' * r) * n := by
    calc
      _ = r + (n * q) * r' := by ac_rfl
      _ = r' + (n * q') * r := by rw [← h, ← h']; grind
      _ = _ := by ac_rfl
  have eqr := congrArg (· % n) cross
  simp [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr'] at eqr
  exact ⟨eqr, Nat.mul_left_cancel (n := n) (by omega) (by simpa [eqr, h'] using h.symm)⟩

theorem certificate_exists {a m c : Nat} (ha : 0 < a) (hc : 0 < c)
    (primitive : (a.gcd m).gcd c = 1) : Nonempty (Certificate a m c) := by
  let d := a.gcd m
  obtain ⟨u, v, hu, huv⟩ := bounded_exists (Nat.div_gcd_pos_of_pos_left m ha)
    (Nat.gcd_div_gcd_div_gcd_of_pos_left ha)
  obtain ⟨w, t, hw, hwt⟩ := bounded_exists hc ((Nat.gcd_comm c d).trans primitive)
  exact ⟨{
    d := d, x := a / d, y := m / d, u := u, v := v, w := w, t := t
    d_pos := Nat.gcd_pos_of_pos_left m ha
    x_pos := Nat.div_gcd_pos_of_pos_left m ha
    c_pos := hc
    factor_a := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a m)).symm
    factor_m := (Nat.mul_div_cancel' (Nat.gcd_dvd_right a m)).symm
    first_eq := huv, u_lt := hu, second_eq := hwt, w_lt := hw }⟩

theorem Certificate.unique {a m c : Nat} (s s' : Certificate a m c) : s = s' := by
  have hd := s.gcd_eq.symm.trans s'.gcd_eq
  have hx : s.x = s'.x := Nat.mul_left_cancel s'.d_pos (by
    simpa only [hd] using s.factor_a.symm.trans s'.factor_a)
  have hy : s.y = s'.y := Nat.mul_left_cancel s'.d_pos (by
    simpa only [hd] using s.factor_m.symm.trans s'.factor_m)
  obtain ⟨hu, hv⟩ := bounded_unique s.u_lt (hx ▸ s'.u_lt) s.first_eq
    (by simpa only [hx, hy] using s'.first_eq)
  obtain ⟨hw, ht⟩ := bounded_unique s.w_lt s'.w_lt s.second_eq
    (by simpa only [hd] using s'.second_eq)
  cases s
  cases s'
  simp_all

end PrimitiveCertificate
