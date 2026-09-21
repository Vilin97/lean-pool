/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticL2AdjointTransfer

/-!
# Averaging the concrete fixed-height quadratic correlation majorant

The proved oscillatory estimate has height `B / S` on a diagonal strip of
width `u * S`, and height `8403968 * B * u / S` elsewhere in a strip of
width `2 * S`. Each term is a centered averaging kernel times a constant
proportional to `u`. This file makes that conversion and the finite maximal
linearization explicit.
-/

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace QuadraticCarleson

/-- The real normalized interval averaging kernel. -/
noncomputable def realCenteredAverageKernel (r x y : ℝ) : ℝ :=
  if |x - y| ≤ r then (2 * r)⁻¹ else 0

theorem realCenteredAverageKernel_nonneg {r : ℝ} (hr : 0 < r) (x y : ℝ) :
    0 ≤ realCenteredAverageKernel r x y := by
  unfold realCenteredAverageKernel
  split_ifs <;> positivity

/-- Exact identification with the selected averaging kernels in the `L²`
operator estimate. -/
theorem ofReal_realCenteredAverageKernel {N : ℕ} (r : Fin N → ℝ)
    (hr : ∀ i, 0 < r i) (σ : ℝ → Fin N) (x y : ℝ) :
    ENNReal.ofReal (realCenteredAverageKernel (r (σ x)) x y) =
      selectedAverageKernel r σ x y := by
  unfold realCenteredAverageKernel selectedAverageKernel
  have hmem : y ∈ closedBall x (r (σ x)) ↔ |x - y| ≤ r (σ x) := by
    simp only [mem_closedBall, Real.dist_eq, abs_sub_comm y x]
  by_cases h : |x - y| ≤ r (σ x)
  · simp only [h, ↓reduceIte, Set.indicator_of_mem (hmem.mpr h)]
    rw [ENNReal.ofReal_inv_of_pos (mul_pos (by norm_num) (hr (σ x)))]
  · simp only [h, ↓reduceIte, ENNReal.ofReal_zero,
      Set.indicator_of_notMem (mt hmem.mp h)]

/-- The precise real majorant already proved by `QuadraticTTStar` after
normalizing the amplitude product to `B / (R * S)`. -/
noncomputable def quadraticFixedHeightMajorant (B u S d : ℝ) : ℝ :=
  if |d| ≤ 2 * S then B / S * (if |d| < u * S then 1 else 8403968 * u) else 0

/-- The exceptional strip and its complement are each controlled by a
normalized centered interval average, with coefficients proportional to the
small decay parameter. -/
theorem quadraticFixedHeightMajorant_le_averages {B u S : ℝ}
    (hB : 0 ≤ B) (hu : 0 < u) (hS : 0 < S) (x y : ℝ) :
    quadraticFixedHeightMajorant B u S (x - y) ≤
      (2 * B * u) * realCenteredAverageKernel (u * S) x y +
      (4 * 8403968 * B * u) * realCenteredAverageKernel (2 * S) x y := by
  have huS : 0 < u * S := mul_pos hu hS
  have hlarge : 0 ≤ (4 * 8403968 * B * u) * realCenteredAverageKernel (2 * S) x y :=
    mul_nonneg (by positivity) (realCenteredAverageKernel_nonneg (by positivity) x y)
  have hsmall : 0 ≤ (2 * B * u) * realCenteredAverageKernel (u * S) x y :=
    mul_nonneg (by positivity) (realCenteredAverageKernel_nonneg huS x y)
  unfold quadraticFixedHeightMajorant
  split_ifs with hsupport hnear
  · have hid : (2 * B * u) * realCenteredAverageKernel (u * S) x y = B / S := by
      simp only [realCenteredAverageKernel, hnear.le, ↓reduceIte]
      field_simp
    rw [mul_one, hid]
    exact le_add_of_nonneg_right hlarge
  · have hid : (4 * 8403968 * B * u) * realCenteredAverageKernel (2 * S) x y =
        B / S * (8403968 * u) := by
      simp only [realCenteredAverageKernel, hsupport, ↓reduceIte]
      field_simp
      ring
    rw [hid]
    exact le_add_of_nonneg_left hsmall
  · exact add_nonneg hsmall hlarge

/-- The larger radius belongs to one of the two endpoints. Adding the two
endpoint-selected averages gives a symmetric majorant. -/
theorem quadraticFixedHeightMajorant_max_le_averages {B u R S : ℝ}
    (hB : 0 ≤ B) (hu : 0 < u) (hR : 0 < R) (hS : 0 < S) (x y : ℝ) :
    quadraticFixedHeightMajorant B u (max R S) (x - y) ≤
      (2 * B * u) * (realCenteredAverageKernel (u * R) x y +
        realCenteredAverageKernel (u * S) y x) +
      (4 * 8403968 * B * u) * (realCenteredAverageKernel (2 * R) x y +
        realCenteredAverageKernel (2 * S) y x) := by
  have hsymm (r : ℝ) : realCenteredAverageKernel r y x = realCenteredAverageKernel r x y := by
    simp only [realCenteredAverageKernel, abs_sub_comm y x]
  by_cases hRS : R ≤ S
  · rw [max_eq_right hRS]
    apply (quadraticFixedHeightMajorant_le_averages hB hu hS x y).trans
    simp_rw [hsymm]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (realCenteredAverageKernel_nonneg (mul_pos hu hR) x y))
        (by positivity)
    · exact mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (realCenteredAverageKernel_nonneg (by positivity) x y))
        (by positivity)
  · rw [max_eq_left (le_of_not_ge hRS)]
    apply (quadraticFixedHeightMajorant_le_averages hB hu hR x y).trans
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (realCenteredAverageKernel_nonneg (mul_pos hu hS) y x))
        (by positivity)
    · exact mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (realCenteredAverageKernel_nonneg (by positivity) y x))
        (by positivity)

/-- Conversion of the real fixed-height majorant to the two symmetric
selected-average kernels, without discarding the small decay factor. -/
theorem ofReal_quadraticFixedHeightMajorant_max_le {N : ℕ}
    (r : Fin N → ℝ) (hr : ∀ i, 0 < r i) (σ : ℝ → Fin N)
    {B u : ℝ} (hB : 0 ≤ B) (hu : 0 < u) (x y : ℝ) :
    ENNReal.ofReal (quadraticFixedHeightMajorant B u (max (r (σ x)) (r (σ y))) (x - y)) ≤
      ENNReal.ofReal (2 * B * u) *
        (selectedAverageKernel (fun i ↦ u * r i) σ x y +
          selectedAverageKernel (fun i ↦ u * r i) σ y x) +
      ENNReal.ofReal (4 * 8403968 * B * u) *
        (selectedAverageKernel (fun i ↦ 2 * r i) σ x y +
          selectedAverageKernel (fun i ↦ 2 * r i) σ y x) := by
  have h := ENNReal.ofReal_le_ofReal
    (quadraticFixedHeightMajorant_max_le_averages hB hu (hr (σ x)) (hr (σ y)) x y)
  have hsmall (a b : ℝ) (i : Fin N) : 0 ≤ realCenteredAverageKernel (u * r i) a b :=
    realCenteredAverageKernel_nonneg (mul_pos hu (hr i)) a b
  have hlarge (a b : ℝ) (i : Fin N) : 0 ≤ realCenteredAverageKernel (2 * r i) a b :=
    realCenteredAverageKernel_nonneg (mul_pos (by norm_num) (hr i)) a b
  rw [ENNReal.ofReal_add
      (mul_nonneg (by positivity) (add_nonneg (hsmall x y (σ x)) (hsmall y x (σ y))))
      (mul_nonneg (by positivity) (add_nonneg (hlarge x y (σ x)) (hlarge y x (σ y)))),
    ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * B * u),
    ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * 8403968 * B * u),
    ENNReal.ofReal_add (hsmall x y (σ x)) (hsmall y x (σ y)),
    ENNReal.ofReal_add (hlarge x y (σ x)) (hlarge y x (σ y))] at h
  simpa only [ofReal_realCenteredAverageKernel (fun i ↦ u * r i)
      (fun i ↦ mul_pos hu (hr i)) σ,
    ofReal_realCenteredAverageKernel (fun i ↦ 2 * r i)
      (fun i ↦ mul_pos (by norm_num) (hr i)) σ] using h

/-- Additivity for the nonnegative double integrals used in the majorant. -/
theorem lintegral_lintegral_add_left {F : ℝ → ℝ → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) (G : ℝ → ℝ → ℝ≥0∞) :
    (∫⁻ x, ∫⁻ y, F x y + G x y) = (∫⁻ x, ∫⁻ y, F x y) + ∫⁻ x, ∫⁻ y, G x y := by
  have hrow (x : ℝ) : Measurable (F x) :=
    hF.comp (measurable_const.prodMk measurable_id)
  simp_rw [lintegral_add_left (hrow _) _]
  exact lintegral_add_left hF.lintegral_prod_right' _

/-- A scalar multiple of the symmetric averaging majorant has the expected
uniform quadratic-form bound. -/
theorem scaled_symmetric_selectedAverageKernel_pairing_le {N : ℕ}
    (r : Fin N → ℝ) (hr : ∀ i, 0 < r i) {σ : ℝ → Fin N} (hσ : Measurable σ)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, ∫⁻ y, C * (selectedAverageKernel r σ x y + selectedAverageKernel r σ y x) *
      f x * f y) ≤ (66 * C) * ∫⁻ x, f x ^ 2 := by
  have hid (x y : ℝ) :
      C * (selectedAverageKernel r σ x y + selectedAverageKernel r σ y x) * f x * f y =
      C * ((selectedAverageKernel r σ x y + selectedAverageKernel r σ y x) * f x * f y) := by ring
  simp_rw [hid, lintegral_const_mul' C _ hC]
  calc
    _ ≤ C * (66 * ∫⁻ x, f x ^ 2) :=
      mul_le_mul' le_rfl (symmetric_selectedAverageKernel_pairing_le r hr hσ hf)
    _ = _ := by ring

/-- The exact fixed-height quadratic majorant gives a second-moment
quadratic-form bound with a uniform coefficient proportional to `u`. -/
theorem quadraticFixedHeightMajorant_pairing_le {N : ℕ}
    (r : Fin N → ℝ) (hr : ∀ i, 0 < r i) {σ : ℝ → Fin N} (hσ : Measurable σ)
    {B u : ℝ} (hB : 0 ≤ B) (hu : 0 < u) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, ∫⁻ y,
      ENNReal.ofReal (quadraticFixedHeightMajorant B u (max (r (σ x)) (r (σ y))) (x - y)) *
        f x * f y) ≤ ENNReal.ofReal (2218647684 * B * u) * ∫⁻ x, f x ^ 2 := by
  let C₁ := ENNReal.ofReal (2 * B * u)
  let C₂ := ENNReal.ofReal (4 * 8403968 * B * u)
  let r₁ := fun i ↦ u * r i
  let r₂ := fun i ↦ 2 * r i
  let F : ℝ → ℝ → ℝ≥0∞ := fun x y ↦
    C₁ * (selectedAverageKernel r₁ σ x y + selectedAverageKernel r₁ σ y x) * f x * f y
  let G : ℝ → ℝ → ℝ≥0∞ := fun x y ↦
    C₂ * (selectedAverageKernel r₂ σ x y + selectedAverageKernel r₂ σ y x) * f x * f y
  have hFm : Measurable (Function.uncurry F) := by
    have hm := measurable_selectedAverageKernel r₁ hσ
    exact ((measurable_const.mul (hm.add (hm.comp measurable_swap))).mul
      (hf.comp measurable_fst)).mul (hf.comp measurable_snd)
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, F x y + G x y := by
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro y
      calc
        _ ≤ (C₁ * (selectedAverageKernel r₁ σ x y + selectedAverageKernel r₁ σ y x) +
            C₂ * (selectedAverageKernel r₂ σ x y + selectedAverageKernel r₂ σ y x)) * f x * f y :=
          mul_le_mul' (mul_le_mul'
            (ofReal_quadraticFixedHeightMajorant_max_le r hr σ hB hu x y) le_rfl) le_rfl
        _ = _ := by dsimp [F, G]; ring
    _ = (∫⁻ x, ∫⁻ y, F x y) + ∫⁻ x, ∫⁻ y, G x y := lintegral_lintegral_add_left hFm G
    _ ≤ (66 * C₁) * (∫⁻ x, f x ^ 2) + (66 * C₂) * ∫⁻ x, f x ^ 2 :=
      add_le_add
        (scaled_symmetric_selectedAverageKernel_pairing_le r₁
          (fun i ↦ mul_pos hu (hr i)) hσ C₁ (by finiteness) hf)
        (scaled_symmetric_selectedAverageKernel_pairing_le r₂
          (fun i ↦ mul_pos (by norm_num) (hr i)) hσ C₂ (by finiteness) hf)
    _ = _ := by
      rw [← add_mul, ← mul_add]
      dsimp [C₁, C₂]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 66)]
      congr 2
      ring

end QuadraticCarleson
