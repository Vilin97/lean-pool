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
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-! # Support-safe coefficient masks

The quotient is formed from original interior coefficient values before
masking. No Lipschitz or derivative claim is made for a masked function.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def interiorShiftedMatrix (S : Set E) (A : E → Matrix ι ι ℝ) (v : E) (h : ℝ) :
    E → Matrix ι ι ℝ := S.indicator (fun x => A (x + h • v))

def interiorQuotientMatrix (S : Set E) (A : E → Matrix ι ι ℝ) (v : E) (h : ℝ) :
    E → Matrix ι ι ℝ := S.indicator (fun x => h⁻¹ • (A (x + h • v) - A x))

theorem aestronglyMeasurable_interiorShiftedMatrix {S K : Set E} (hS : MeasurableSet S)
    (A : E → Matrix ι ι ℝ) (hA : ContinuousOn A K) (v : E) (h : ℝ)
    (hshift : ∀ x ∈ S, x + h • v ∈ K) (μ : Measure E) (i j : ι) :
    AEStronglyMeasurable (fun x => interiorShiftedMatrix S A v h x i j) μ := by
  have hc : ContinuousOn (fun x => A (x + h • v) i j) S :=
    ((continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hA)).comp
      (continuous_id.add continuous_const).continuousOn hshift
  have hm := (aestronglyMeasurable_indicator_iff hS).mpr (hc.aestronglyMeasurable hS (μ := μ))
  convert hm using 1
  ext x
  by_cases hx : x ∈ S <;> simp [interiorShiftedMatrix, hx]

theorem aestronglyMeasurable_interiorQuotientMatrix {S K : Set E} (hS : MeasurableSet S)
    (hSK : S ⊆ K) (A : E → Matrix ι ι ℝ) (hA : ContinuousOn A K) (v : E) (h : ℝ)
    (hshift : ∀ x ∈ S, x + h • v ∈ K) (μ : Measure E) (i j : ι) :
    AEStronglyMeasurable (fun x => interiorQuotientMatrix S A v h x i j) μ := by
  have ha : ContinuousOn (fun x => A x i j) K :=
    (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hA)
  have hc : ContinuousOn (fun x => h⁻¹ * (A (x + h • v) i j - A x i j)) S :=
    continuousOn_const.mul ((ha.comp (continuous_id.add continuous_const).continuousOn hshift).sub (ha.mono hSK))
  have hm := (aestronglyMeasurable_indicator_iff hS).mpr (hc.aestronglyMeasurable hS (μ := μ))
  convert hm using 1
  ext x
  by_cases hx : x ∈ S <;> simp [interiorQuotientMatrix, hx]

theorem interiorShiftedMatrix_bilinear_bound {S K : Set E}
    (A : E → Matrix ι ι ℝ) (v : E) (h : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hshift : ∀ x ∈ S, x + h • v ∈ K)
    (hb : ∀ x ∈ K, ∀ u w : EuclideanSpace ℝ ι,
      |∑ i, ∑ j, A x i j * u i * w j| ≤ C * ‖u‖ * ‖w‖)
    (x : E) (u w : EuclideanSpace ℝ ι) :
    |∑ i, ∑ j, interiorShiftedMatrix S A v h x i j * u i * w j| ≤ C * ‖u‖ * ‖w‖ := by
  by_cases hx : x ∈ S
  · simpa [interiorShiftedMatrix, hx] using hb (x + h • v) (hshift x hx) u w
  · simpa [interiorShiftedMatrix, hx] using mul_nonneg (mul_nonneg hC (norm_nonneg u)) (norm_nonneg w)

theorem interiorQuotientMatrix_bilinear_bound {S : Set E}
    (A : E → Matrix ι ι ℝ) (v : E) (h : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x ∈ S, ‖h⁻¹ • (A (x + h • v) - A x)‖ ≤ C)
    (x : E) (u w : EuclideanSpace ℝ ι) :
    |∑ i, ∑ j, interiorQuotientMatrix S A v h x i j * u i * w j| ≤
      (Fintype.card ι : ℝ) ^ 2 * C * ‖u‖ * ‖w‖ := by
  apply abs_matrix_bilinear_le _ hC
  intro i j
  by_cases hx : x ∈ S
  · simpa only [interiorQuotientMatrix, indicator_of_mem hx, Real.norm_eq_abs] using
      (Matrix.norm_entry_le_entrywise_sup_norm (h⁻¹ • (A (x + h • v) - A x)) (i := i) (j := j)).trans (hb x hx)
  · simpa [interiorQuotientMatrix, hx] using hC

end AlmostSchur
