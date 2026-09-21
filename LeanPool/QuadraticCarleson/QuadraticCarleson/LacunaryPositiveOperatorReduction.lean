/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryOscillatoryScaling
import LeanPool.QuadraticCarleson.QuadraticCarleson.OscillatoryReductionLimit

/-!
# The lacunary principal-value operator and its ordinary Hilbert remainder

The pointwise reduction is unconditional on all of `L0Infinity`. The
Hardy--Littlewood term is estimated by its proved weak `(1,1)` bound. The
remaining ordinary Hilbert maximal level set is kept literally in the
endpoint estimate, rather than being replaced by an unproved weak bound.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace QuadraticCarleson
namespace LacunaryPositiveOperatorReduction

open OscillatoryReduction PositiveGoodOscillatory PositiveFullOscillatoryEndpoint
open PositiveEndpointOptimization PositiveLevelIntegration
open LacunaryOscillatoryScaling


/-- Pointwise reduction of the actual canonical lacunary principal-value
limsup on the paper's entire test domain. No PV-existence hypothesis occurs. -/
theorem lacunaryQuadraticCarlesonL0_le_oscillatory_add_hilbert_add_maximal
    (f : L0Infinity) (x : ℝ) :
    lacunaryQuadraticCarlesonL0 f x ≤
      paperLacunaryOscillatoryMaximal f x +
        2 * quadraticHilbertMaximalTruncation 0 f x +
        maximalErrorConstant * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  apply iSup_le
  intro m
  apply (quadraticHilbertL0Limsup_le_oscillatory
    (dyadicModulation m) (dyadicModulation_pos m).ne' f x).trans
  apply add_le_add ?_ le_rfl
  apply add_le_add ?_ le_rfl
  exact le_iSup (fun m : ℤ ↦
    ‖paperOscillatoryAction (dyadicModulation m) (dyadicModulation_pos m).ne' f x‖ₑ) m

/-- A single ordinary Hilbert PV supplies every lacunary quadratic PV at
the same point. The converse follows already from modulation `2^0 = 1`. -/
theorem forall_lacunary_principalValue_iff_hilbert (f : L0Infinity) (x : ℝ) :
    (∀ m : ℤ, ∃ z : ℂ, HasQuadraticPrincipalValue (dyadicModulation m) f x z) ↔
      ∃ z : ℂ, HasQuadraticPrincipalValue 0 f x z := by
  constructor
  · intro h
    exact (exists_quadraticPrincipalValue_iff_hilbert
      (dyadicModulation 0) (dyadicModulation_pos 0).ne' f x).mp (h 0)
  · intro h m
    exact (exists_quadraticPrincipalValue_iff_hilbert
      (dyadicModulation m) (dyadicModulation_pos m).ne' f x).mpr h

theorem centeredHardyLittlewoodMaximal_const_mul_of_ne_top
    (g : ℝ → ℝ≥0∞) {c : ℝ≥0∞} (hc : c ≠ ∞) (x : ℝ) :
    centeredHardyLittlewoodMaximal (fun y ↦ c * g y) x =
      c * centeredHardyLittlewoodMaximal g x := by
  unfold centeredHardyLittlewoodMaximal centeredAverage
  simp_rw [lintegral_const_mul' _ _ hc, div_eq_mul_inv, mul_assoc]
  exact (ENNReal.mul_iSup _ _).symm

theorem scaled_centeredHardyLittlewoodMaximal_weak_bound
    (g : ℝ → ℝ≥0∞) {c : ℝ≥0∞} (hc : c ≠ ∞) (a : ℝ≥0∞) :
    a * volume {x | a < c * centeredHardyLittlewoodMaximal g x} ≤
      (4 * c) * ∫⁻ y, g y := by
  have h := centeredHardyLittlewoodMaximal_weak_bound (fun y ↦ c * g y) a
  simp_rw [centeredHardyLittlewoodMaximal_const_mul_of_ne_top g hc] at h
  rw [lintegral_const_mul' _ _ hc] at h
  simpa only [mul_assoc] using h

theorem lintegral_scaled_norm_le_lacunaryOrlicz
    (f : ℝ → ℂ) {α : ℝ} (hα : 0 < α) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ / α)) ≤
      ∫⁻ x, ENNReal.ofReal
        ((‖f x‖ / α) * paperLog 2 (‖f x‖ / α) ^ 2 * paperLog 4 (‖f x‖ / α)) := by
  apply lintegral_mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  have ht : 0 ≤ ‖f x‖ / α := by positivity
  simpa only [mul_one, mul_assoc] using
    mul_le_mul_of_nonneg_left (one_le_lacunaryEndpointFactor ht) ht

theorem lintegral_scaled_norm_eq (f : ℝ → ℂ) {α : ℝ} (hα : 0 < α) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ / α)) =
      (ENNReal.ofReal α)⁻¹ * ∫⁻ x, ‖f x‖ₑ := by
  simp_rw [ENNReal.ofReal_div_of_pos hα, ofReal_norm, div_eq_mul_inv,
    mul_comm _ (ENNReal.ofReal α)⁻¹]
  exact lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hα).ne')

theorem maximalError_levelSet_third_le_scaled_orlicz
    (f : L0Infinity) {α : ℝ} (hα : 0 < α) :
    volume {x | ENNReal.ofReal (α / 3) <
      maximalErrorConstant * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x} ≤
        (12 * maximalErrorConstant) * ∫⁻ x, ENNReal.ofReal
          ((‖f x‖ / α) * paperLog 2 (‖f x‖ / α) ^ 2 * paperLog 4 (‖f x‖ / α)) := by
  have hα3 : 0 < α / 3 := by positivity
  have h := scaled_centeredHardyLittlewoodMaximal_weak_bound (fun y ↦ ‖f y‖ₑ)
    maximalErrorConstant_lt_top.ne (ENNReal.ofReal (α / 3))
  have hc : ENNReal.ofReal (3 / α) * ENNReal.ofReal (α / 3) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 3 / α)]
    have heq : (3 / α) * (α / 3) = 1 := by field_simp
    rw [heq, ENNReal.ofReal_one]
  have hh := mul_le_mul' (le_refl (ENNReal.ofReal (3 / α))) h
  rw [← mul_assoc, hc, one_mul] at hh
  have heq : ENNReal.ofReal (3 / α) * ((4 * maximalErrorConstant) * ∫⁻ x, ‖f x‖ₑ) =
      (12 * maximalErrorConstant) * ∫⁻ x, ENNReal.ofReal (‖f x‖ / α) := by
    rw [lintegral_scaled_norm_eq f hα, ENNReal.ofReal_div_of_pos hα,
      ENNReal.ofReal_ofNat, div_eq_mul_inv]
    ring
  rw [heq] at hh
  exact hh.trans (mul_le_mul' le_rfl (lintegral_scaled_norm_le_lacunaryOrlicz f hα))

/-- The endpoint constant after adding the maximal regularization error. -/
noncomputable def lacunaryRemainderEndpointConstant (C : ℝ) : ℝ≥0∞ :=
  81 * lacunaryScaledEndpointConstant C + 12 * maximalErrorConstant

theorem lacunaryRemainderEndpointConstant_lt_top (C : ℝ) :
    lacunaryRemainderEndpointConstant C < ∞ := by
  exact ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top (by finiteness) (lacunaryScaledEndpointConstant_lt_top C),
      ENNReal.mul_lt_top (by finiteness) maximalErrorConstant_lt_top⟩

theorem lacunaryOscillatory_levelSet_third_le_scaled_orlicz
    {C : ℝ} (hblock : HasUniformL0LogSquaredFrozenBlockWeakBounds C)
    (f : L0Infinity) {α : ℝ} (hα : 0 < α) :
    volume {x | ENNReal.ofReal (α / 3) < paperLacunaryOscillatoryMaximal f x} ≤
      (81 * lacunaryScaledEndpointConstant C) * ∫⁻ x, ENNReal.ofReal
        ((‖f x‖ / α) * paperLog 2 (‖f x‖ / α) ^ 2 * paperLog 4 (‖f x‖ / α)) := by
  have h := paperLacunaryOscillatoryMaximal_L0Infinity_levelSet_le_scaled_orlicz
    hblock f (by positivity : 0 < α / 3)
  have hdiv (x : ℝ) : ‖f x‖ / (α / 3) = 3 * (‖f x‖ / α) := by ring
  simp_rw [hdiv] at h
  apply h.trans
  calc
    _ ≤ lacunaryScaledEndpointConstant C * ∫⁻ x, ENNReal.ofReal
        (81 * ((‖f x‖ / α) * paperLog 2 (‖f x‖ / α) ^ 2 * paperLog 4 (‖f x‖ / α))) := by
      apply mul_le_mul' le_rfl
      apply lintegral_mono
      intro x
      exact ENNReal.ofReal_le_ofReal (lacunaryOrlicz_three_mul_le (by positivity))
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 81)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      simp only [ENNReal.ofReal_ofNat]
      ring

/-- The full lacunary L0 operator at arbitrary threshold, with only the
literal ordinary Hilbert maximal level set left unestimated. The oscillatory
and Hardy--Littlewood terms are already bounded by the exact source modular. -/
theorem lacunaryQuadraticCarlesonL0_levelSet_le_hilbert_remainder_add_scaled_orlicz
    {C : ℝ} (hblock : HasUniformL0LogSquaredFrozenBlockWeakBounds C)
    (f : L0Infinity) {α : ℝ} (hα : 0 < α) :
    volume {x | ENNReal.ofReal α < lacunaryQuadraticCarlesonL0 f x} ≤
      volume {x | ENNReal.ofReal (α / 6) < quadraticHilbertMaximalTruncation 0 f x} +
        lacunaryRemainderEndpointConstant C * ∫⁻ x, ENNReal.ofReal
          ((‖f x‖ / α) * paperLog 2 (‖f x‖ / α) ^ 2 * paperLog 4 (‖f x‖ / α)) := by
  let O := paperLacunaryOscillatoryMaximal f
  let H := quadraticHilbertMaximalTruncation 0 f
  let M := fun x ↦ maximalErrorConstant * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x
  let J := ∫⁻ x, ENNReal.ofReal
    ((‖f x‖ / α) * paperLog 2 (‖f x‖ / α) ^ 2 * paperLog 4 (‖f x‖ / α))
  have hparts : ENNReal.ofReal (α / 3) + 2 * ENNReal.ofReal (α / 6) +
      ENNReal.ofReal (α / 3) = ENNReal.ofReal α := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hsub : {x | ENNReal.ofReal α < lacunaryQuadraticCarlesonL0 f x} ⊆
      {x | ENNReal.ofReal (α / 6) < H x} ∪
        ({x | ENNReal.ofReal (α / 3) < O x} ∪ {x | ENNReal.ofReal (α / 3) < M x}) := by
    intro x hx
    by_cases hh : ENNReal.ofReal (α / 6) < H x
    · exact Or.inl hh
    apply Or.inr
    by_cases ho : ENNReal.ofReal (α / 3) < O x
    · exact Or.inl ho
    apply Or.inr
    by_contra hm
    have hle : O x + 2 * H x + M x ≤ ENNReal.ofReal α := by
      rw [← hparts]
      exact add_le_add
        (add_le_add (le_of_not_gt ho) (mul_le_mul' le_rfl (le_of_not_gt hh)))
        (le_of_not_gt hm)
    exact hx.not_ge ((lacunaryQuadraticCarlesonL0_le_oscillatory_add_hilbert_add_maximal
      f x).trans hle)
  calc
    _ ≤ volume {x | ENNReal.ofReal (α / 6) < H x} +
        (volume {x | ENNReal.ofReal (α / 3) < O x} +
          volume {x | ENNReal.ofReal (α / 3) < M x}) :=
      (measure_mono hsub).trans ((measure_union_le _ _).trans
        (add_le_add le_rfl (measure_union_le _ _)))
    _ ≤ volume {x | ENNReal.ofReal (α / 6) < H x} +
        ((81 * lacunaryScaledEndpointConstant C) * J + (12 * maximalErrorConstant) * J) :=
      add_le_add le_rfl (add_le_add
        (lacunaryOscillatory_levelSet_third_le_scaled_orlicz hblock f hα)
        (maximalError_levelSet_third_le_scaled_orlicz f hα))
    _ = _ := by rw [← add_mul]; rfl


end LacunaryPositiveOperatorReduction
end QuadraticCarleson
