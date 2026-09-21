/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
import LeanPool.ACMax.Band.CertUniform

/-!
# An exact Moore certificate for every order at least 48

The existing power estimate handles exponents four through seven.  For
exponent at least eight, the fourth nonconstant term of the binomial expansion
gives a uniform certificate with no upper bound on the order.
-/

namespace ACMax

/-- The small-exponent power estimate in the parameter range used by the
paper. -/
theorem small_exponent_power_growth (t v ell : ℕ)
    (ht43 : 43 ≤ t) (htv : t ≤ v) (hv107 : v ≤ 107)
    (hell4 : 4 ≤ ell) (hell7 : ell ≤ 7)
    (hlin : 5 * v + 41 ≤ 50 * ell + 3 * t) :
    (t - 9) * v ^ ell ≤ (v + 2 * t) ^ ell :=
  uniform_power_certificate t v ell ht43 htv (by omega) hell4 (by omega) hlin

/-- The binomial expansion through its fourth nonconstant term. -/
theorem binomial_lower_four (v t k : ℕ) :
    3 * (v + 2 * t) ^ (k + 4) ≥
      3 * v ^ (k + 4) +
        6 * (k + 4) * t * v ^ (k + 3) +
        6 * (k + 4) * (k + 3) * t ^ 2 * v ^ (k + 2) +
        4 * (k + 4) * (k + 3) * (k + 2) * t ^ 3 * v ^ (k + 1) +
        2 * (k + 4) * (k + 3) * (k + 2) * (k + 1) * t ^ 4 * v ^ k := by
  induction k with
  | zero =>
      norm_num [pow_succ]
      ring_nf
      exact le_rfl
  | succ k ih =>
      have hmul := Nat.mul_le_mul_left (v + 2 * t) ih
      calc
        3 * (v + 2 * t) ^ (k + 1 + 4) =
            (v + 2 * t) * (3 * (v + 2 * t) ^ (k + 4)) := by
              ring_nf
        _ ≥ (v + 2 * t) *
              (3 * v ^ (k + 4) +
                6 * (k + 4) * t * v ^ (k + 3) +
                6 * (k + 4) * (k + 3) * t ^ 2 * v ^ (k + 2) +
                4 * (k + 4) * (k + 3) * (k + 2) * t ^ 3 * v ^ (k + 1) +
                2 * (k + 4) * (k + 3) * (k + 2) * (k + 1) * t ^ 4 * v ^ k) :=
          hmul
        _ ≥ 3 * v ^ (k + 1 + 4) +
              6 * (k + 1 + 4) * t * v ^ (k + 1 + 3) +
              6 * (k + 1 + 4) * (k + 1 + 3) * t ^ 2 * v ^ (k + 1 + 2) +
              4 * (k + 1 + 4) * (k + 1 + 3) * (k + 1 + 2) * t ^ 3 *
                v ^ (k + 1 + 1) +
              2 * (k + 1 + 4) * (k + 1 + 3) * (k + 1 + 2) * (k + 1 + 1) *
                t ^ 4 * v ^ (k + 1) := by
            simp only [pow_succ]
            nlinarith [Nat.zero_le
              (4 * (k + 4) * (k + 3) * (k + 2) * (k + 1) * t ^ 5 * v ^ k)]

/-- At `t = 43`, the fourth-term inequality is minimized at `ell = 8`. -/
theorem fourth_term_corner_t43 (v ell : ℕ) (hell8 : 8 ≤ ell)
    (hlin : 5 * v + 41 ≤ 50 * ell + 3 * 43) :
    3 * v ^ 4 ≤
      2 * ell * (ell - 1) * (ell - 2) * (ell - 3) * 43 ^ 3 := by
  have hv : v ≤ 10 * ell + 17 := by omega
  have hvpow := Nat.pow_le_pow_left hv 4
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hell8
  have h1 : 8 + u - 1 = 7 + u := by omega
  have h2 : 8 + u - 2 = 6 + u := by omega
  have h3 : 8 + u - 3 = 5 + u := by omega
  rw [h1, h2, h3]
  calc
    3 * v ^ 4 ≤ 3 * (10 * (8 + u) + 17) ^ 4 := Nat.mul_le_mul_left 3 hvpow
    _ ≤ 3 * (10 * (8 + u) + 17) ^ 4 +
          (129014 * u ^ 4 + 2970364 * u ^ 3 + 22976314 * u ^ 2 +
            59988164 * u + 1555677) := by omega
    _ = 2 * (8 + u) * (7 + u) * (6 + u) * (5 + u) * 43 ^ 3 := by ring

/-- Increasing `t` by one cannot worsen the scaled fourth-term ratio when
`A ≥ 5t`. -/
theorem fourth_term_ratio_step (t A C : ℕ) (ht : 1 ≤ t) (hAt : 5 * t ≤ A)
    (hbase : 3 * A ^ 4 ≤ C * t ^ 3) :
    3 * (A + 3) ^ 4 ≤ C * (t + 1) ^ 3 := by
  have hratio : t ^ 3 * (A + 3) ^ 4 ≤ (t + 1) ^ 3 * A ^ 4 := by
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le ht
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hAt
    let R :=
      375 * q ^ 6 + 600 * q ^ 5 * u + 2775 * q ^ 5 +
        270 * q ^ 4 * u ^ 2 + 3960 * q ^ 4 * u + 8335 * q ^ 4 +
        48 * q ^ 3 * u ^ 3 + 1476 * q ^ 3 * u ^ 2 + 10232 * q ^ 3 * u +
        13009 * q ^ 3 + 3 * q ^ 2 * u ^ 4 + 204 * q ^ 2 * u ^ 3 +
        2958 * q ^ 2 * u ^ 2 + 12936 * q ^ 2 * u + 11142 * q ^ 2 +
        9 * q * u ^ 4 + 284 * q * u ^ 3 + 2568 * q * u ^ 2 + 8016 * q * u +
        4972 * q + 7 * u ^ 4 + 128 * u ^ 3 + 816 * u ^ 2 + 1952 * u + 904
    have hid :
        ((q + 1) + 1) ^ 3 * (5 * (q + 1) + u) ^ 4 =
          (q + 1) ^ 3 * (5 * (q + 1) + u + 3) ^ 4 + R := by
      dsimp [R]
      ring
    calc
      (1 + q) ^ 3 * (5 * (1 + q) + u + 3) ^ 4 ≤
          (1 + q) ^ 3 * (5 * (1 + q) + u + 3) ^ 4 + R := by omega
      _ = (1 + q + 1) ^ 3 * (5 * (1 + q) + u) ^ 4 := by
        simpa only [Nat.add_comm 1 q] using hid.symm
  have hratio3 := Nat.mul_le_mul_left 3 hratio
  have hbase' := Nat.mul_le_mul_right ((t + 1) ^ 3) hbase
  have hscaled :
      t ^ 3 * (3 * (A + 3) ^ 4) ≤ t ^ 3 * (C * (t + 1) ^ 3) := by
    calc
      t ^ 3 * (3 * (A + 3) ^ 4) = 3 * (t ^ 3 * (A + 3) ^ 4) := by ring
      _ ≤ 3 * ((t + 1) ^ 3 * A ^ 4) := hratio3
      _ = (3 * A ^ 4) * (t + 1) ^ 3 := by ring
      _ ≤ (C * t ^ 3) * (t + 1) ^ 3 := hbase'
      _ = t ^ 3 * (C * (t + 1) ^ 3) := by ring
  exact Nat.le_of_mul_le_mul_left hscaled (pow_pos (by omega) 3)

/-- The scaled corner inequality for `t ≥ 44`. -/
theorem fourth_term_corner_ge44 (ell a : ℕ) (hell8 : 8 ≤ ell) :
    2 * (44 + a) + 41 ≤ 50 * ell →
      3 * (50 * ell + 91 + 3 * a) ^ 4 ≤
        1250 * ell * (ell - 1) * (ell - 2) * (ell - 3) * (44 + a) ^ 3 := by
  induction a with
  | zero =>
      intro _
      obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hell8
      have h1 : 8 + u - 1 = 7 + u := by omega
      have h2 : 8 + u - 2 = 6 + u := by omega
      have h3 : 8 + u - 3 = 5 + u := by omega
      rw [h1, h2, h3]
      calc
        3 * (50 * (8 + u) + 91) ^ 4 ≤
            3 * (50 * (8 + u) + 91) ^ 4 +
              (87730000 * u ^ 4 + 2031980000 * u ^ 3 + 15877835000 * u ^ 2 +
                42485217400 * u + 4526254317) := by omega
        _ = 1250 * (8 + u) * (7 + u) * (6 + u) * (5 + u) * 44 ^ 3 := by ring
  | succ a ih =>
      intro hwindow
      have hprevWindow : 2 * (44 + a) + 41 ≤ 50 * ell := by omega
      have hprev := ih hprevWindow
      let A := 50 * ell + 91 + 3 * a
      let C := 1250 * ell * (ell - 1) * (ell - 2) * (ell - 3)
      have hAt : 5 * (44 + a) ≤ A := by
        dsimp [A]
        omega
      have hstep := fourth_term_ratio_step (44 + a) A C (by omega) hAt
        (by simpa [A, C] using hprev)
      dsimp [A, C] at hstep
      convert hstep using 1

/-- The census region implies the fourth-term inequality whenever `ell ≥ 8`. -/
theorem fourth_term_region (t v ell : ℕ) (ht43 : 43 ≤ t) (htv : t ≤ v)
    (hell8 : 8 ≤ ell) (hlin : 5 * v + 41 ≤ 50 * ell + 3 * t) :
    3 * v ^ 4 ≤
      2 * ell * (ell - 1) * (ell - 2) * (ell - 3) * t ^ 3 := by
  rcases eq_or_lt_of_le ht43 with rfl | ht44
  · exact fourth_term_corner_t43 v ell hell8 (by simpa using hlin)
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le ht44
    have hwindow : 2 * (44 + a) + 41 ≤ 50 * ell := by omega
    have hv5 : 5 * v ≤ 50 * ell + 91 + 3 * a := by omega
    have hvpow := Nat.pow_le_pow_left hv5 4
    have hcorner := fourth_term_corner_ge44 ell a hell8 hwindow
    have hscaled :
        625 * (3 * v ^ 4) ≤
          625 * (2 * ell * (ell - 1) * (ell - 2) * (ell - 3) * (44 + a) ^ 3) := by
      calc
        625 * (3 * v ^ 4) = 3 * (5 * v) ^ 4 := by ring
        _ ≤ 3 * (50 * ell + 91 + 3 * a) ^ 4 := Nat.mul_le_mul_left 3 hvpow
        _ ≤ 1250 * ell * (ell - 1) * (ell - 2) * (ell - 3) * (44 + a) ^ 3 :=
          hcorner
        _ = 625 *
            (2 * ell * (ell - 1) * (ell - 2) * (ell - 3) * (44 + a) ^ 3) := by
          ring
    exact Nat.le_of_mul_le_mul_left hscaled (by norm_num)

/-- The fourth binomial term implies the exact Moore side condition. -/
theorem sum_cert_of_fourth {t v ell : ℕ} (ht : 0 < t) (hv : 0 < v)
    (hell8 : 8 ≤ ell)
    (hfourth : 3 * v ^ 4 ≤
      2 * ell * (ell - 1) * (ell - 2) * (ell - 3) * t ^ 3) :
    t * (v - 1) * v ^ ell <
      (v + t) * ((v + 2 * t) ^ ell - v ^ ell) := by
  let k := ell - 4
  have hellk : ell = k + 4 := by dsimp [k]; omega
  have hbin := binomial_lower_four v t k
  rw [← hellk] at hbin
  have hk1 : ell - 1 = k + 3 := by omega
  have hk2 : ell - 2 = k + 2 := by omega
  have hk3 : ell - 3 = k + 1 := by omega
  rw [hk1, hk2, hk3] at hfourth
  have hbin' :
      3 * v ^ ell +
          2 * ell * (k + 3) * (k + 2) * (k + 1) * t ^ 4 * v ^ k ≤
        3 * (v + 2 * t) ^ ell := by
    omega
  have hfourth' := Nat.mul_le_mul_right (t * v ^ k) hfourth
  have hvpow : v ^ ell = v ^ k * v ^ 4 := by rw [hellk, pow_add]
  have htail :
      3 * t * v ^ ell ≤
        2 * ell * (k + 3) * (k + 2) * (k + 1) * t ^ 4 * v ^ k := by
    calc
      3 * t * v ^ ell = 3 * t * (v ^ k * v ^ 4) := by rw [hvpow]
      _ = (3 * v ^ 4) * (t * v ^ k) := by ring
      _ ≤ (2 * ell * (k + 3) * (k + 2) * (k + 1) * t ^ 3) *
          (t * v ^ k) := hfourth'
      _ = 2 * ell * (k + 3) * (k + 2) * (k + 1) * t ^ 4 * v ^ k := by ring
  have hmiddle :
      3 * ((t + 1) * v ^ ell) ≤ 3 * (v + 2 * t) ^ ell := by
    calc
      3 * ((t + 1) * v ^ ell) = 3 * v ^ ell + 3 * t * v ^ ell := by ring
      _ ≤ 3 * v ^ ell +
          2 * ell * (k + 3) * (k + 2) * (k + 1) * t ^ 4 * v ^ k :=
        Nat.add_le_add_left htail _
      _ ≤ 3 * (v + 2 * t) ^ ell := hbin'
  have hpower : (t + 1) * v ^ ell ≤ (v + 2 * t) ^ ell :=
    Nat.le_of_mul_le_mul_left hmiddle (by norm_num)
  have hdecomp : (t + 1) * v ^ ell = v ^ ell + t * v ^ ell := by ring
  have hdiff : t * v ^ ell ≤ (v + 2 * t) ^ ell - v ^ ell := by
    rw [hdecomp] at hpower
    omega
  have hstrict : t * (v - 1) * v ^ ell < (v + t) * (t * v ^ ell) := by
    have hp : 0 < t * v ^ ell := mul_pos ht (pow_pos hv ell)
    have hvt : v - 1 < v + t := by omega
    have hmul := (Nat.mul_lt_mul_right hp).2 hvt
    calc
      t * (v - 1) * v ^ ell = (v - 1) * (t * v ^ ell) := by ring
      _ < (v + t) * (t * v ^ ell) := hmul
  exact hstrict.trans_le (Nat.mul_le_mul_left (v + t) hdiff)

/-- The order-free parameter bounds supplied by the strengthened census. -/
theorem uniform_region_bounds_ge_48 (n X h : ℕ)
    (hM : 10 * X + 7 * h + 186 ≤ 4 * n)
    (hhX : h ≤ X) (hn48 : 48 ≤ n) :
    let t := n - 4 - X - 3 * h
    let v := n - h
    let ell := (2 * n - X) / 12 / 2
    43 ≤ t ∧ t ≤ v ∧ 4 ≤ ell ∧ 5 * v + 41 ≤ 50 * ell + 3 * t := by
  dsimp
  omega

/-- The exact non-backtracking side condition holds throughout the full census
region `n ≥ 48`. -/
theorem band_cert_uniform_ge_48 (n X h : ℕ)
    (hM : 10 * X + 7 * h + 186 ≤ 4 * n)
    (hhX : h ≤ X) (hn48 : 48 ≤ n) :
    (n - 4 - X - 3 * h) * (n - h - 1) *
        (n - h) ^ ((2 * n - X) / 12 / 2) <
      (n - h + (n - 4 - X - 3 * h)) *
        ((n - h + 2 * (n - 4 - X - 3 * h)) ^ ((2 * n - X) / 12 / 2) -
          (n - h) ^ ((2 * n - X) / 12 / 2)) := by
  let t := n - 4 - X - 3 * h
  let v := n - h
  let ell := (2 * n - X) / 12 / 2
  have hbounds := uniform_region_bounds_ge_48 n X h hM hhX hn48
  change 43 ≤ t ∧ t ≤ v ∧ 4 ≤ ell ∧ 5 * v + 41 ≤ 50 * ell + 3 * t at hbounds
  rcases hbounds with ⟨ht43, htv, hell4, hlin⟩
  have ht : 0 < t := by omega
  have hv : 0 < v := by omega
  by_cases hell7 : ell ≤ 7
  · have hn107 : n ≤ 107 := by
      dsimp [ell] at hell7
      omega
    have hv107 : v ≤ 107 := by
      dsimp [v]
      omega
    have hpower := small_exponent_power_growth t v ell
      ht43 htv hv107 hell4 hell7 hlin
    have ht10 : 10 ≤ t := by omega
    have ht_sub : t - 10 + 10 = t := Nat.sub_add_cancel ht10
    have hv_sub : v - 1 + 1 = v := Nat.sub_add_cancel (by omega)
    have hsquare : 43 * t ≤ t * t := Nat.mul_le_mul_right t ht43
    have hlinear : 10 * v + 1 + 9 * t ≤ 43 * t := by omega
    have hpoly : 10 * v + 1 + 9 * t ≤ t * t := hlinear.trans hsquare
    have hA : t * (v - 1) + 1 ≤ (t - 10) * (v + t) := by
      nlinarith
    change t * (v - 1) * v ^ ell <
      (v + t) * ((v + 2 * t) ^ ell - v ^ ell)
    exact sum_cert_of_power ht10 hA hpower hv
  · have hell8 : 8 ≤ ell := by omega
    have hfourth := fourth_term_region t v ell ht43 htv hell8 hlin
    change t * (v - 1) * v ^ ell <
      (v + t) * ((v + 2 * t) ^ ell - v ^ ell)
    exact sum_cert_of_fourth ht hv hell8 hfourth

end ACMax
