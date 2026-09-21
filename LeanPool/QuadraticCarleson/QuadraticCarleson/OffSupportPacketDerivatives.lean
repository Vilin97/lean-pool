/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.WavePacket
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# All derivatives of the rescaled off-support packet

The packet's `r`-th derivative has the exact `L¹` scaling `t⁻¹ ^ r`.
These facts provide the packet input for arbitrary-order integration by parts.
-/

open Function MeasureTheory Set
open scoped ContDiff

namespace QuadraticCarleson


/-- Explicit normalized derivative of the rescaled packet. -/
noncomputable def iteratedWavePacketDeriv (r : ℕ) (s t u : ℝ) : ℝ :=
  t⁻¹ ^ (r + 1) * iteratedDeriv r baseBump ((u - s) / t)

@[simp] theorem iteratedWavePacketDeriv_zero (s t : ℝ) :
    iteratedWavePacketDeriv 0 s t = wavePacket s t := by
  funext u
  simp [iteratedWavePacketDeriv, wavePacket]

theorem smooth_iteratedDeriv_baseBump (r : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv r baseBump) := by
  induction r with
  | zero => simpa using baseBump_smooth
  | succ r ih =>
    rw [iteratedDeriv_succ]
    exact (contDiff_infty_iff_deriv.mp ih).2

theorem smooth_iteratedWavePacketDeriv (r : ℕ) (s t : ℝ) :
    ContDiff ℝ ∞ (iteratedWavePacketDeriv r s t) := by
  exact contDiff_const.mul <|
    (smooth_iteratedDeriv_baseBump r).comp
      ((contDiff_id.sub contDiff_const).div_const t)

theorem continuous_iteratedWavePacketDeriv (r : ℕ) (s t : ℝ) :
    Continuous (iteratedWavePacketDeriv r s t) :=
  (smooth_iteratedWavePacketDeriv r s t).continuous

theorem hasDerivAt_iteratedWavePacketDeriv (r : ℕ) (s : ℝ) {t : ℝ}
    (_ht : t ≠ 0) (u : ℝ) :
    HasDerivAt (iteratedWavePacketDeriv r s t)
      (iteratedWavePacketDeriv (r + 1) s t u) u := by
  have hd := ((smooth_iteratedDeriv_baseBump r).differentiable (by simp)
    ((u - s) / t)).hasDerivAt
  have h := (hd.comp u (((hasDerivAt_id u).sub_const s).div_const t)).const_mul
    (t⁻¹ ^ (r + 1))
  apply h.congr_deriv
  simp only [iteratedWavePacketDeriv, iteratedDeriv_succ, pow_succ,
    div_eq_mul_inv, one_mul]
  ring

theorem iteratedWavePacketDeriv_eq_iteratedDeriv (r : ℕ) (s : ℝ) {t : ℝ}
    (ht : t ≠ 0) :
    iteratedWavePacketDeriv r s t = iteratedDeriv r (wavePacket s t) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ, ← ih]
    funext u
    exact (hasDerivAt_iteratedWavePacketDeriv r s ht u).deriv.symm

theorem iteratedDeriv_baseBump_tsupport_subset (r : ℕ) :
    tsupport (iteratedDeriv r baseBump) ⊆ Icc (-1 / 4 : ℝ) (1 / 4 : ℝ) := by
  induction r with
  | zero =>
    simpa only [iteratedDeriv_zero, tsupport] using
      (closure_minimal baseBump_support isClosed_Icc)
  | succ r ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem iteratedWavePacketDeriv_support (r : ℕ) {s t : ℝ} (ht : 0 < t) :
    support (iteratedWavePacketDeriv r s t) ⊆ Icc (s - t / 4) (s + t / 4) := by
  intro u hu
  have hbase : iteratedDeriv r baseBump ((u - s) / t) ≠ 0 := by
    intro hzero
    apply hu
    simp [iteratedWavePacketDeriv, hzero]
  have hmem := iteratedDeriv_baseBump_tsupport_subset r (subset_tsupport _ hbase)
  constructor
  · have hscaled := (le_div_iff₀ ht).mp hmem.1
    linarith
  · have hscaled := (div_le_iff₀ ht).mp hmem.2
    linarith

theorem iteratedWavePacketDeriv_hasCompactSupport (r : ℕ) (s : ℝ) {t : ℝ}
    (ht : 0 < t) : HasCompactSupport (iteratedWavePacketDeriv r s t) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (iteratedWavePacketDeriv_support r ht)

theorem iteratedWavePacketDeriv_left_third_eq_zero (r : ℕ) (s : ℝ) {t : ℝ}
    (ht : 0 < t) : iteratedWavePacketDeriv r s t (s - t / 3) = 0 := by
  apply notMem_support.mp
  intro hmem
  have h := iteratedWavePacketDeriv_support r ht hmem
  linarith [h.1]

theorem iteratedWavePacketDeriv_right_third_eq_zero (r : ℕ) (s : ℝ) {t : ℝ}
    (ht : 0 < t) : iteratedWavePacketDeriv r s t (s + t / 3) = 0 := by
  apply notMem_support.mp
  intro hmem
  have h := iteratedWavePacketDeriv_support r ht hmem
  linarith [h.2]

theorem integrable_iteratedDeriv_baseBump (r : ℕ) :
    Integrable (iteratedDeriv r baseBump) := by
  apply (smooth_iteratedDeriv_baseBump r).continuous.integrable_of_hasCompactSupport
  exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((subset_tsupport _).trans (iteratedDeriv_baseBump_tsupport_subset r))

theorem integrable_abs_iteratedDeriv_baseBump (r : ℕ) :
    Integrable (fun u : ℝ ↦ |iteratedDeriv r baseBump u|) :=
  (integrable_iteratedDeriv_baseBump r).abs

theorem integrable_iteratedWavePacketDeriv (r : ℕ) (s : ℝ) {t : ℝ}
    (ht : 0 < t) : Integrable (iteratedWavePacketDeriv r s t) :=
  (continuous_iteratedWavePacketDeriv r s t).integrable_of_hasCompactSupport
    (iteratedWavePacketDeriv_hasCompactSupport r s ht)

theorem integrable_abs_iteratedWavePacketDeriv (r : ℕ) (s : ℝ) {t : ℝ}
    (ht : 0 < t) : Integrable (fun u : ℝ ↦ |iteratedWavePacketDeriv r s t u|) :=
  (integrable_iteratedWavePacketDeriv r s ht).abs

theorem integral_abs_iteratedWavePacketDeriv (r : ℕ) (s : ℝ) {t : ℝ}
    (ht : 0 < t) :
    (∫ u : ℝ, |iteratedWavePacketDeriv r s t u|) =
      t⁻¹ ^ r * ∫ v : ℝ, |iteratedDeriv r baseBump v| := by
  simp_rw [iteratedWavePacketDeriv, abs_mul, abs_pow, abs_inv, abs_of_pos ht]
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun u : ℝ ↦ |iteratedDeriv r baseBump (u / t)|) s]
  have hscale : (∫ u : ℝ, |iteratedDeriv r baseBump (u / t)|) =
      t * ∫ v : ℝ, |iteratedDeriv r baseBump v| := by
    simpa [abs_of_pos ht, smul_eq_mul] using
      Measure.integral_comp_div (fun v : ℝ ↦ |iteratedDeriv r baseBump v|) t
  rw [hscale, pow_succ]
  field_simp [ht.ne']


end QuadraticCarleson
