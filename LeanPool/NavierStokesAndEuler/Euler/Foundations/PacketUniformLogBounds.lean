/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketUniformScaleSums
import LeanPool.NavierStokesAndEuler.Euler.Foundations.Scale
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD

/-!
# Packet Uniform Log Bounds
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace EulerPacketUniformLogBounds

open Real EulerScale EulerPacketUniformScaleSums

/-- Every fixed polynomial logarithm is bounded by a simple product of
the stage and the square root of the scale. -/
theorem polynomial_log_bound {j X C p q : ℝ} (hj : 1 ≤ j) (hX : 1 ≤ X) :
    C + p * log j + q * log X ≤ (|C| + |p| + 2 * |q|) * j * sqrt X := by
  have hjp : 0 < j := by linarith
  have hXp : 0 < X := by linarith
  have hs : 1 ≤ sqrt X := one_le_sqrt.mpr hX
  have hsj : 1 ≤ j * sqrt X := one_le_mul_of_one_le_of_one_le hj hs
  have hlj : 0 ≤ log j := log_nonneg hj
  have hlX : 0 ≤ log X := log_nonneg hX
  have hljb : log j ≤ j := (log_le_sub_one_of_pos hjp).trans (by linarith)
  have hlXb : log X ≤ 2 * sqrt X := by
    have hh := log_le_sub_one_of_pos (sqrt_pos.mpr hXp)
    rw [log_sqrt hXp.le] at hh
    linarith
  have hCb : C ≤ |C| * j * sqrt X := by
    have hh := mul_le_mul_of_nonneg_left hsj (abs_nonneg C)
    nlinarith only [hh, le_abs_self C]
  have hp₁ := mul_le_mul_of_nonneg_right (le_abs_self p) hlj
  have hp₂ := mul_le_mul_of_nonneg_left hljb (abs_nonneg p)
  have hp₃ := mul_le_mul_of_nonneg_left hs (mul_nonneg (abs_nonneg p) hjp.le)
  have hq₁ := mul_le_mul_of_nonneg_right (le_abs_self q) hlX
  have hq₂ := mul_le_mul_of_nonneg_left hlXb (abs_nonneg q)
  have hq₃ := mul_le_mul_of_nonneg_right hj (mul_nonneg (by
      positivity : 0 ≤ 2 * |q|) (sqrt_nonneg X))
  nlinarith only [hCb, hp₁, hp₂, hp₃, hq₁, hq₂, hq₃]

/-- A single explicit lower bound on the initial scale absorbs the
polynomial logarithms at every subsequent quadratic stage. -/
theorem polynomial_logs_uniformly_absorbed
    (J A : ℕ) (hJ : 1 ≤ J)
    (hJA : (2 : ℝ) ^ (2 * A + 3) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (C p q b : ℝ) (hb : 0 < b)
    (hlarge : (2 * (|C| + |p| + 2 * |q|) / b) ^ 2 * (J : ℝ) ^ (2 * A + 2) ≤ x 0) :
    ∀ n, C + p * log ((J + n : ℕ) : ℝ) + q * log (x n) ≤
      (b / 2) * (x n / ((J + n : ℕ) : ℝ) ^ A) := by
  let S := |C| + |p| + 2 * |q|
  let L := 2 * S / b
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hJp : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hx1 := quadratic_growth_one_le J hJ x hx0 hx
  have hgeom := polynomial_scale_geometric_lower J (2 * A + 2) hJ
    (by simpa only [show 2 * A + 2 + 1 = 2 * A + 3 by omega] using hJA) x (by linarith) hx
  intro n
  have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hj : (0 : ℝ) < (J + n : ℕ) := by linarith
  have hstart : L ^ 2 ≤ x 0 / (J : ℝ) ^ (2 * A + 2) := by
    apply (le_div_iff₀ (pow_pos hJp _)).2
    exact hlarge
  have hone : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hbase := mul_le_mul_of_nonneg_right hone
    (div_nonneg (le_trans zero_le_one hx0) (pow_nonneg hJp.le (2 * A + 2)))
  have hscale : L ^ 2 ≤ x n / ((J + n : ℕ) : ℝ) ^ (2 * A + 2) := by
    nlinarith only [hstart, hbase, hgeom n]
  have hsquare := (le_div_iff₀ (pow_pos hj (2 * A + 2))).mp hscale
  have hroot : L * ((J + n : ℕ) : ℝ) ^ (A + 1) ≤ sqrt (x n) := by
    have hp : (((J + n : ℕ) : ℝ) ^ (A + 1)) ^ 2 = ((J + n : ℕ) : ℝ) ^ (2 * A + 2) := by
      rw [← pow_mul]
      congr 1
      omega
    have hs := sq_sqrt (le_trans zero_le_one (hx1 n))
    have hn : 0 ≤ L * ((J + n : ℕ) : ℝ) ^ (A + 1) := by positivity
    nlinarith only [hsquare, hp, hs, hn, sqrt_nonneg (x n)]
  have hlog := polynomial_log_bound (C := C) (p := p) (q := q) hj1 (hx1 n)
  have hlogmul := mul_le_mul_of_nonneg_right hlog (pow_nonneg hj.le A)
  have hrootmul := mul_le_mul_of_nonneg_right hroot
    (mul_nonneg (div_nonneg hb.le (by norm_num : (0 : ℝ) ≤ 2)) (sqrt_nonneg (x n)))
  have hLS : (b / 2) * L = S := by dsimp [L]; field_simp
  have hid : (b / 2) * (x n / ((J + n : ℕ) : ℝ) ^ A) =
      ((b / 2) * x n) / ((J + n : ℕ) : ℝ) ^ A := by ring
  rw [hid]
  apply (le_div_iff₀ (pow_pos hj A)).2
  have hmul : S * ((J + n : ℕ) : ℝ) ^ (A + 1) * sqrt (x n) ≤ (b / 2) * x n := by
    calc
      _ = (L * ((J + n : ℕ) : ℝ) ^ (A + 1)) * ((b / 2) * sqrt (x n)) := by rw [← hLS]; ring
      _ ≤ sqrt (x n) * ((b / 2) * sqrt (x n)) := hrootmul
      _ = (b / 2) * (sqrt (x n)) ^ 2 := by ring
      _ = _ := by rw [sq_sqrt (le_trans zero_le_one (hx1 n))]
  rw [pow_succ] at hmul
  dsimp only [S] at hmul
  nlinarith only [hlogmul, hmul]

end EulerPacketUniformLogBounds
