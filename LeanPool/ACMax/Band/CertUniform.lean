/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-!
# A uniform certificate for the finite Moore band

This file proves the SUM side condition on the full range `48 ≤ n ≤ 122` without subdividing
the range.  The census inequalities imply, for `t = n - 4 - X - 3h`, `v = n - h`, and
`ell = (2n - X) / 12 / 2`, that

* `43 ≤ t ≤ v ≤ 122`,
* `4 ≤ ell ≤ 10`, and
* `5v + 41 ≤ 50ell + 3t`.

These bounds give `(t - 9) * v ^ ell ≤ (v + 2t) ^ ell`.  The exponent-four case is an
endpoint estimate; the remaining exponents follow from the first three nonconstant binomial
terms and an exact chord identity for a cubic polynomial.  This replaces the five numerical
ratio certificates formerly used by `Band.Assembly`.
-/

@[expose] public section

namespace ACMax

theorem binomial_lower_three (v t k : ℕ) :
    3 * (v + 2 * t) ^ (k + 3) ≥
      3 * v ^ (k + 3) +
      6 * (k + 3) * t * v ^ (k + 2) +
      6 * (k + 3) * (k + 2) * t ^ 2 * v ^ (k + 1) +
      4 * (k + 3) * (k + 2) * (k + 1) * t ^ 3 * v ^ k := by
  induction k with
  | zero =>
      norm_num [pow_succ]
      ring_nf
      exact le_rfl
  | succ k ih =>
      have hmul := Nat.mul_le_mul_left (v + 2 * t) ih
      calc
        3 * (v + 2 * t) ^ (k + 1 + 3)
            = (v + 2 * t) *
                (3 * (v + 2 * t) ^ (k + 3)) := by
              ring_nf
        _ ≥ (v + 2 * t) *
              (3 * v ^ (k + 3) +
                6 * (k + 3) * t * v ^ (k + 2) +
                6 * (k + 3) * (k + 2) * t ^ 2 * v ^ (k + 1) +
                4 * (k + 3) * (k + 2) * (k + 1) * t ^ 3 * v ^ k) := hmul
        _ ≥ 3 * v ^ (k + 1 + 3) +
              6 * (k + 1 + 3) * t * v ^ (k + 1 + 2) +
              6 * (k + 1 + 3) * (k + 1 + 2) * t ^ 2 * v ^ (k + 1 + 1) +
              4 * (k + 1 + 3) * (k + 1 + 2) * (k + 1 + 1) * t ^ 3 * v ^ (k + 1) := by
            simp only [pow_succ]
            nlinarith [Nat.zero_le
              (8 * (k + 3) * (k + 2) * (k + 1) * t ^ 4 * v ^ k)]

theorem uniform_power_four (t v : ℕ)
    (ht43 : 43 ≤ t) (htv : t ≤ v) (hv122 : v ≤ 122)
    (hlin : 5 * v + 41 ≤ 200 + 3 * t) :
    (t - 9) * v ^ 4 ≤ (v + 2 * t) ^ 4 := by
  have ht9 : 9 ≤ t := by omega
  let T : ℤ := t
  let V : ℤ := v
  let A : ℤ := 159 + 3 * T
  have hT43 : (43 : ℤ) ≤ T := by
    simpa [T] using (show (43 : ℤ) ≤ (t : ℤ) by exact_mod_cast ht43)
  have hTV : T ≤ V := by
    simpa [T, V] using (show (t : ℤ) ≤ (v : ℤ) by exact_mod_cast htv)
  have hV122 : V ≤ 122 := by
    simpa [V] using (show (v : ℤ) ≤ 122 by exact_mod_cast hv122)
  have hVA : 5 * V ≤ A := by
    have hlinZ : (5 : ℤ) * v + 41 ≤ 200 + 3 * t := by
      exact_mod_cast hlin
    dsimp [A, T, V]
    linarith
  have hApos : (0 : ℤ) < A := by dsimp [A]; linarith
  set u : ℤ := T - 43 with hu
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  have hu36 : u ≤ 36 := by
    dsimp [u, A] at *
    linarith
  have hcoef : 0 ≤ 773272 - 81 * u ^ 2 - 5297 * u := by
    nlinarith [sq_nonneg (u - 36), sq_nonneg u]
  have hgap :
      0 ≤ (A + 10 * T) ^ 4 - (T - 9) * A ^ 4 := by
    have hid :
        (A + 10 * T) ^ 4 - (T - 9) * A ^ 4 =
          u ^ 3 * (773272 - 81 * u ^ 2 - 5297 * u) +
          83801688 * u ^ 2 + 2621645152 * u + 31854951952 := by
      dsimp [A, u, T]
      ring
    rw [hid]
    positivity
  have hend : (T - 9) * A ^ 4 ≤ (A + 10 * T) ^ 4 := by linarith
  have hcross : (A + 10 * T) * (5 * V) ≤ (5 * V + 10 * T) * A := by
    nlinarith
  have hcross4 := pow_le_pow_left₀ (by positivity) hcross 4
  have hcross4' :
      (A + 10 * T) ^ 4 * (5 * V) ^ 4 ≤
        (5 * V + 10 * T) ^ 4 * A ^ 4 := by
    simpa [mul_pow] using hcross4
  have hchain :
      (T - 9) * A ^ 4 * (5 * V) ^ 4 ≤
        (5 * V + 10 * T) ^ 4 * A ^ 4 := by
    exact le_trans (mul_le_mul_of_nonneg_right hend (by positivity)) hcross4'
  have hcancel :
      A ^ 4 * ((T - 9) * (5 * V) ^ 4) ≤
        A ^ 4 * (5 * V + 10 * T) ^ 4 := by
    convert hchain using 1 <;> ring
  have hscaled :
      (T - 9) * (5 * V) ^ 4 ≤ (5 * V + 10 * T) ^ 4 :=
    le_of_mul_le_mul_left hcancel (pow_pos hApos 4)
  have hfinalZ : (T - 9) * V ^ 4 ≤ (V + 2 * T) ^ 4 := by
    have h625 :
        (625 : ℤ) * ((T - 9) * V ^ 4) ≤
          625 * (V + 2 * T) ^ 4 := by
      convert hscaled using 1 <;> ring
    exact le_of_mul_le_mul_left h625 (by norm_num : (0 : ℤ) < 625)
  dsimp [T, V] at hfinalZ
  exact_mod_cast hfinalZ

theorem uniform_cubic_arith (t v ell : ℕ)
    (ht43 : 43 ≤ t) (htv : t ≤ v) (hv122 : v ≤ 122)
    (hell5 : 5 ≤ ell) (hell10 : ell ≤ 10)
    (hlin : 5 * v + 41 ≤ 50 * ell + 3 * t) :
    3 * (t - 10) * v ^ 3 ≤
      6 * ell * t * v ^ 2 +
      6 * ell * (ell - 1) * t ^ 2 * v +
      4 * ell * (ell - 1) * (ell - 2) * t ^ 3 := by
  have ht10 : 10 ≤ t := by omega
  have hell1 : 1 ≤ ell := by omega
  have hell2 : 2 ≤ ell := by omega
  let T : ℤ := t
  let V : ℤ := v
  let L : ℤ := ell
  let X : ℤ := 5 * V
  let A : ℤ := 50 * L + 3 * T - 41
  let P : ℤ → ℤ := fun x =>
    30 * L * T * x ^ 2 +
      150 * L * (L - 1) * T ^ 2 * x +
      500 * L * (L - 1) * (L - 2) * T ^ 3 -
      3 * (T - 10) * x ^ 3
  have hT43 : (43 : ℤ) ≤ T := by
    simpa [T] using (show (43 : ℤ) ≤ (t : ℤ) by exact_mod_cast ht43)
  have hTV : T ≤ V := by
    simpa [T, V] using (show (t : ℤ) ≤ (v : ℤ) by exact_mod_cast htv)
  have hV122 : V ≤ 122 := by
    simpa [V] using (show (v : ℤ) ≤ 122 by exact_mod_cast hv122)
  have hL5 : (5 : ℤ) ≤ L := by
    simpa [L] using (show (5 : ℤ) ≤ (ell : ℤ) by exact_mod_cast hell5)
  have hL10 : L ≤ 10 := by
    simpa [L] using (show (ell : ℤ) ≤ 10 by exact_mod_cast hell10)
  have hXA : X ≤ A := by
    have hlinZ : (5 : ℤ) * v + 41 ≤ 50 * ell + 3 * t := by
      exact_mod_cast hlin
    dsimp [X, A, L, T, V]
    linarith
  have hTX : 5 * T ≤ X := by dsimp [X]; linarith
  have hTA : 5 * T ≤ A := hTX.trans hXA
  have hT122 : T ≤ 122 := hTV.trans hV122
  set a : ℤ := L - 5 with ha
  set b : ℤ := T - 43 with hb
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have hb0 : 0 ≤ b := by dsimp [b]; linarith
  have hb79 : b ≤ 79 := by dsimp [b]; linarith
  have hLa : L = a + 5 := by dsimp [a]; ring
  have hTb : T = b + 43 := by dsimp [b]; ring
  have hbracket :
      0 ≤ 4 * L ^ 3 - 6 * L ^ 2 + 8 * L - 3 * T + 30 := by
    have hid :
        4 * L ^ 3 - 6 * L ^ 2 + 8 * L - 3 * T + 30 =
          4 * a ^ 3 + 54 * a ^ 2 + 248 * a + 54 + 3 * (79 - b) := by
      rw [hLa, hTb]
      ring
    rw [hid]
    positivity
  have hPlo : 0 ≤ P (5 * T) := by
    have hid :
        P (5 * T) =
          125 * T ^ 3 *
            (4 * L ^ 3 - 6 * L ^ 2 + 8 * L - 3 * T + 30) := by
      simp only [P]
      ring
    rw [hid]
    positivity
  have hcoef : 0 ≤ 10299 - 81 * b := by linarith
  have hPhi : 0 ≤ P A := by
    have hid :
        P A =
          500 * a ^ 3 * b ^ 3 + 72000 * a ^ 3 * b ^ 2 +
          3118500 * a ^ 3 * b + 44471000 * a ^ 3 +
          6450 * a ^ 2 * b ^ 3 + 872400 * a ^ 2 * b ^ 2 +
          36222750 * a ^ 2 * b + 504355800 * a ^ 2 +
          23770 * a * b ^ 3 + 3057300 * a * b ^ 2 +
          121507590 * a * b + 1658324560 * a +
          b ^ 3 * (10299 - 81 * b) + 2032188 * b ^ 2 +
          82837380 * b + 1174137072 := by
      simp only [P, A]
      rw [hLa, hTb]
      ring
    rw [hid]
    positivity
  let Q : ℤ :=
    (T - 10) * (A + X) + 5 * T * (T - 2 * L - 10)
  have hQ : 0 ≤ Q := by
    have hAX : 10 * T ≤ A + X := by linarith
    have hcore : 0 ≤ 3 * T - 2 * L - 30 := by linarith
    dsimp [Q]
    nlinarith
  have hPX : 0 ≤ P X := by
    by_cases heq : A = 5 * T
    · have hX : X = 5 * T := by linarith
      simpa [hX] using hPlo
    · have hstrict : 5 * T < A := lt_of_le_of_ne hTA (Ne.symm heq)
      have hwidth : 0 < A - 5 * T := sub_pos.mpr hstrict
      have hchord :
          (A - 5 * T) * P X =
            (A - X) * P (5 * T) + (X - 5 * T) * P A +
              3 * (A - 5 * T) * (A - X) * (X - 5 * T) * Q := by
        simp only [P, Q]
        ring
      have hmul : 0 ≤ (A - 5 * T) * P X := by
        rw [hchord]
        positivity
      exact nonneg_of_mul_nonneg_right hmul hwidth
  have hdesiredZ :
      3 * (T - 10) * V ^ 3 ≤
        6 * L * T * V ^ 2 +
        6 * L * (L - 1) * T ^ 2 * V +
        4 * L * (L - 1) * (L - 2) * T ^ 3 := by
    have hscale :
        P X = 125 *
          (6 * L * T * V ^ 2 +
            6 * L * (L - 1) * T ^ 2 * V +
            4 * L * (L - 1) * (L - 2) * T ^ 3 -
            3 * (T - 10) * V ^ 3) := by
      simp only [P, X]
      ring
    rw [hscale] at hPX
    have hdiff :
        0 ≤ 6 * L * T * V ^ 2 +
          6 * L * (L - 1) * T ^ 2 * V +
          4 * L * (L - 1) * (L - 2) * T ^ 3 -
          3 * (T - 10) * V ^ 3 :=
      nonneg_of_mul_nonneg_right hPX (by norm_num)
    linarith
  dsimp [T, V, L] at hdesiredZ
  exact_mod_cast hdesiredZ

theorem uniform_power_ge_five (t v k : ℕ)
    (ht43 : 43 ≤ t) (htv : t ≤ v) (hv122 : v ≤ 122)
    (hk2 : 2 ≤ k) (hk7 : k ≤ 7)
    (hlin : 5 * v + 41 ≤ 50 * (k + 3) + 3 * t) :
    (t - 9) * v ^ (k + 3) ≤ (v + 2 * t) ^ (k + 3) := by
  have ht10 : 10 ≤ t := by omega
  have hcubic := uniform_cubic_arith t v (k + 3)
    ht43 htv hv122 (by omega) (by omega) hlin
  have hk31 : k + 3 - 1 = k + 2 := by omega
  have hk32 : k + 3 - 2 = k + 1 := by omega
  simp only [hk31, hk32] at hcubic
  have htail :
      3 * (t - 10) * v ^ (k + 3) ≤
        6 * (k + 3) * t * v ^ (k + 2) +
        6 * (k + 3) * (k + 2) * t ^ 2 * v ^ (k + 1) +
        4 * (k + 3) * (k + 2) * (k + 1) * t ^ 3 * v ^ k := by
    calc
      3 * (t - 10) * v ^ (k + 3) =
          v ^ k * (3 * (t - 10) * v ^ 3) := by
            rw [pow_add]
            ring
      _ ≤ v ^ k *
          (6 * (k + 3) * t * v ^ 2 +
            6 * (k + 3) * (k + 2) * t ^ 2 * v +
            4 * (k + 3) * (k + 2) * (k + 1) * t ^ 3) :=
        Nat.mul_le_mul_left _ hcubic
      _ = 6 * (k + 3) * t * v ^ (k + 2) +
          6 * (k + 3) * (k + 2) * t ^ 2 * v ^ (k + 1) +
          4 * (k + 3) * (k + 2) * (k + 1) * t ^ 3 * v ^ k := by
            rw [show k + 2 = k + 2 by rfl, show k + 1 = k + 1 by rfl]
            simp only [pow_add]
            ring
  have hbin := binomial_lower_three v t k
  have htdecomp : t - 9 = 1 + (t - 10) := by omega
  have hthree :
      3 * ((t - 9) * v ^ (k + 3)) ≤
        3 * (v + 2 * t) ^ (k + 3) := by
    calc
      3 * ((t - 9) * v ^ (k + 3)) =
          3 * v ^ (k + 3) + 3 * (t - 10) * v ^ (k + 3) := by
            rw [htdecomp]
            ring
      _ ≤ 3 * v ^ (k + 3) +
          (6 * (k + 3) * t * v ^ (k + 2) +
            6 * (k + 3) * (k + 2) * t ^ 2 * v ^ (k + 1) +
            4 * (k + 3) * (k + 2) * (k + 1) * t ^ 3 * v ^ k) :=
        Nat.add_le_add_left htail _
      _ ≤ 3 * (v + 2 * t) ^ (k + 3) := by
        simpa only [add_assoc] using hbin
  exact Nat.le_of_mul_le_mul_left hthree (by norm_num)

theorem uniform_power_certificate (t v ell : ℕ)
    (ht43 : 43 ≤ t) (htv : t ≤ v) (hv122 : v ≤ 122)
    (hell4 : 4 ≤ ell) (hell10 : ell ≤ 10)
    (hlin : 5 * v + 41 ≤ 50 * ell + 3 * t) :
    (t - 9) * v ^ ell ≤ (v + 2 * t) ^ ell := by
  rcases eq_or_lt_of_le hell4 with rfl | hell5
  · exact uniform_power_four t v ht43 htv hv122 (by simpa using hlin)
  · let k := ell - 3
    have hellk : ell = k + 3 := by dsimp [k]; omega
    rw [hellk] at hlin ⊢
    exact uniform_power_ge_five t v k ht43 htv hv122
      (by dsimp [k]; omega) (by dsimp [k]; omega) hlin

theorem uniform_region_bounds (n X h : ℕ)
    (hM : 10 * X + 7 * h + 186 ≤ 4 * n)
    (hHoard : 3 * X + 26 ≤ n) (hhX : h ≤ X)
    (hn48 : 48 ≤ n) (hn122 : n ≤ 122) :
    let t := n - 4 - X - 3 * h
    let v := n - h
    let ell := (2 * n - X) / 12 / 2
    43 ≤ t ∧ t ≤ v ∧ v ≤ 122 ∧ 4 ≤ ell ∧ ell ≤ 10 ∧
      5 * v + 41 ≤ 50 * ell + 3 * t := by
  dsimp
  omega

theorem sum_cert_of_power {t v ell : ℕ}
    (ht10 : 10 ≤ t)
    (hA : t * (v - 1) + 1 ≤ (t - 10) * (v + t))
    (hpower : (t - 9) * v ^ ell ≤ (v + 2 * t) ^ ell)
    (hv : 0 < v) :
    t * (v - 1) * v ^ ell <
      (v + t) * ((v + 2 * t) ^ ell - v ^ ell) := by
  have htdecomp : t - 9 = (t - 10) + 1 := by omega
  have hpower' :
      (t - 10) * v ^ ell + v ^ ell ≤ (v + 2 * t) ^ ell := by
    calc
      (t - 10) * v ^ ell + v ^ ell =
          ((t - 10) + 1) * v ^ ell := by ring
      _ = (t - 9) * v ^ ell := by rw [htdecomp]
      _ ≤ (v + 2 * t) ^ ell := hpower
  have hdiff :
      (t - 10) * v ^ ell ≤ (v + 2 * t) ^ ell - v ^ ell := by
    omega
  have hscale :
      (v + t) * ((t - 10) * v ^ ell) ≤
        (v + t) * ((v + 2 * t) ^ ell - v ^ ell) :=
    Nat.mul_le_mul_left _ hdiff
  have hcorner :
      (t * (v - 1) + 1) * v ^ ell ≤
        (v + t) * ((t - 10) * v ^ ell) := by
    calc
      (t * (v - 1) + 1) * v ^ ell ≤
          ((t - 10) * (v + t)) * v ^ ell :=
        Nat.mul_le_mul_right _ hA
      _ = (v + t) * ((t - 10) * v ^ ell) := by ring
  have hvpow : 0 < v ^ ell := pow_pos hv ell
  have hstrict :
      t * (v - 1) * v ^ ell < (t * (v - 1) + 1) * v ^ ell := by
    rw [add_mul, one_mul]
    omega
  exact hstrict.trans_le (hcorner.trans hscale)

theorem band_cert_uniform_48_122 (n X h : ℕ)
    (hM : 10 * X + 7 * h + 186 ≤ 4 * n)
    (hHoard : 3 * X + 26 ≤ n) (hhX : h ≤ X)
    (hn48 : 48 ≤ n) (hn122 : n ≤ 122) :
    (n - 4 - X - 3 * h) * (n - h - 1) *
        (n - h) ^ ((2 * n - X) / 12 / 2) <
      (n - h + (n - 4 - X - 3 * h)) *
        ((n - h + 2 * (n - 4 - X - 3 * h)) ^ ((2 * n - X) / 12 / 2) -
          (n - h) ^ ((2 * n - X) / 12 / 2)) := by
  let t := n - 4 - X - 3 * h
  let v := n - h
  let ell := (2 * n - X) / 12 / 2
  have hbounds := uniform_region_bounds n X h hM hHoard hhX hn48 hn122
  change 43 ≤ t ∧ t ≤ v ∧ v ≤ 122 ∧ 4 ≤ ell ∧ ell ≤ 10 ∧
    5 * v + 41 ≤ 50 * ell + 3 * t at hbounds
  rcases hbounds with ⟨ht43, htv, hv122, hell4, hell10, hlin⟩
  have ht10 : 10 ≤ t := by omega
  have hv : 0 < v := by omega
  have ht_sub : t - 10 + 10 = t := Nat.sub_add_cancel ht10
  have hv_sub : v - 1 + 1 = v := Nat.sub_add_cancel (by omega)
  have hsquare : 43 * t ≤ t * t := Nat.mul_le_mul_right t ht43
  have hlinear : 10 * v + 1 + 9 * t ≤ 43 * t := by omega
  have hpoly : 10 * v + 1 + 9 * t ≤ t * t := hlinear.trans hsquare
  have hA : t * (v - 1) + 1 ≤ (t - 10) * (v + t) := by
    nlinarith
  have hpower := uniform_power_certificate t v ell
    ht43 htv hv122 hell4 hell10 hlin
  change t * (v - 1) * v ^ ell <
    (v + t) * ((v + 2 * t) ^ ell - v ^ ell)
  exact sum_cert_of_power ht10 hA hpower hv

end ACMax
