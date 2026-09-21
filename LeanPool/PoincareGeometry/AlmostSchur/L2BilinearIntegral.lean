/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.MatrixBilinearBound
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! # L² bounds for measurable bilinear energy terms -/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators

namespace AlmostSchur

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {V : Type*} [NormedAddCommGroup V] {W : Type*} [NormedAddCommGroup W]

/-- Taking the pointwise norm preserves the L² norm exactly. -/
theorem norm_L2_pointwise_norm (u : Lp V 2 μ) :
    ‖((Lp.memLp u).norm.toLp (fun x => ‖u x‖))‖ = ‖u‖ := by
  apply le_antisymm
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(Lp.memLp u).norm.coeFn_toLp] with x hx
    rw [hx, Real.norm_of_nonneg (norm_nonneg _)]
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(Lp.memLp u).norm.coeFn_toLp] with x hx
    rw [hx, Real.norm_of_nonneg (norm_nonneg _)]

/-- Cauchy–Schwarz for pointwise norms, in the real L² norm convention. -/
theorem integral_norm_mul_norm_le (u : Lp V 2 μ) (v : Lp W 2 μ) :
    (∫ x, ‖u x‖ * ‖v x‖ ∂μ) ≤ ‖u‖ * ‖v‖ := by
  let a := (Lp.memLp u).norm.toLp (fun x => ‖u x‖)
  let b := (Lp.memLp v).norm.toLp (fun x => ‖v x‖)
  have he : (∫ x, ‖u x‖ * ‖v x‖ ∂μ) = inner ℝ a b := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(Lp.memLp u).norm.coeFn_toLp, (Lp.memLp v).norm.coeFn_toLp] with x hx hy
    simp only [RCLike.inner_apply, conj_trivial, hx, hy, mul_comm, a, b]
  rw [he]
  exact (real_inner_le_norm _ _).trans_eq (by rw [norm_L2_pointwise_norm, norm_L2_pointwise_norm])

/-- A pointwise mixed-form bound integrates to its expected L² estimate. -/
theorem abs_integral_le_bilinear_L2 (u : Lp V 2 μ) (v : Lp W 2 μ)
    {f : α → ℝ} (hf : Integrable f μ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ x ∂μ, |f x| ≤ C * ‖u x‖ * ‖v x‖) :
    |∫ x, f x ∂μ| ≤ C * ‖u‖ * ‖v‖ := by
  calc
    _ ≤ ∫ x, |f x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, C * (‖u x‖ * ‖v x‖) ∂μ := integral_mono_ae hf.abs
      (((Lp.memLp u).norm.integrable_mul (Lp.memLp v).norm).const_mul C)
      (hb.mono fun x hx => by simpa only [mul_assoc] using hx)
    _ = C * ∫ x, ‖u x‖ * ‖v x‖ ∂μ := integral_const_mul _ _
    _ ≤ _ := by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (integral_norm_mul_norm_le u v) hC

end AlmostSchur
