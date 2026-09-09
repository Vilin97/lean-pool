/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Deformation Volume
-/

@[expose] public section

noncomputable section

namespace EulerDeformationVolume

open Matrix Set MeasureTheory

/-- Jacobi's formula along the three-dimensional deformation equation, including
singular matrices; no inverse determinant is used. -/
theorem determinant_hasDerivAt (F M : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ)
    (hF : ∀ i j, HasDerivAt (fun s => F s i j) ((M t * F t) i j) t) :
    HasDerivAt (fun s => (F s).det) ((M t).trace * (F t).det) t := by
  have h := (((((hF 0 0).mul (hF 1 1)).mul (hF 2 2)).sub
    (((hF 0 0).mul (hF 1 2)).mul (hF 2 1))).sub
    (((hF 0 1).mul (hF 1 0)).mul (hF 2 2))).add
    (((hF 0 1).mul (hF 1 2)).mul (hF 2 0))
  have h' := (h.add (((hF 0 2).mul (hF 1 0)).mul (hF 2 1))).sub
    (((hF 0 2).mul (hF 1 1)).mul (hF 2 0))
  have hd := h'.congr_deriv (g' := (M t).trace * (F t).det) (by
    simp only [Pi.mul_apply, mul_apply, Fin.sum_univ_three, trace, diag, det_fin_three]
    ring)
  convert hd using 1 <;> first | rfl | (funext s; exact det_fin_three (F s))

/-- A trace-free velocity gradient preserves the actual deformation determinant. -/
theorem determinant_eq_one (F M : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (a b : ℝ)
    (hF : ∀ t ∈ Icc a b, ∀ i j,
      HasDerivAt (fun s => F s i j) ((M t * F t) i j) t)
    (htrace : ∀ t ∈ Ico a b, (M t).trace = 0) (hinit : (F a).det = 1) :
    ∀ t ∈ Icc a b, (F t).det = 1 := by
  have hc : ContinuousOn (fun t => (F t).det) (Icc a b) :=
    fun t ht => (determinant_hasDerivAt F M t (hF t ht)).continuousAt.continuousWithinAt
  have hz : ∀ t ∈ Ico a b, HasDerivWithinAt (fun s => (F s).det) 0 (Ici t) t := by
    intro t ht
    have hd := determinant_hasDerivAt F M t (hF t ⟨ht.1, ht.2.le⟩)
    rw [htrace t ht, zero_mul] at hd
    exact hd.hasDerivWithinAt
  intro t ht
  exact (constant_of_has_deriv_right_zero hc hz t ht).trans hinit

section ChangeOfVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A bijective differentiable map with unit Jacobian preserves Lebesgue measure. -/
theorem measurePreserving_of_det_one (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (f : E → E) (F : E → E →L[ℝ] E)
    (hf : ∀ x, HasFDerivAt f (F x) x) (hbij : Function.Bijective f)
    (hdet : ∀ x, (F x).det = 1) : MeasurePreserving f μ μ := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  refine ⟨hc.measurable, ?_⟩
  have hm := map_withDensity_abs_det_fderiv_eq_addHaar μ
    (s := (univ : Set E)) (f' := F) MeasurableSet.univ.nullMeasurableSet
    (fun x _ => (hf x).hasFDerivWithinAt) hbij.1.injOn
  simp only [hdet, abs_one, ENNReal.ofReal_one, Measure.restrict_univ,
    image_univ, hbij.2.range_eq] at hm
  change Measure.map f (μ.withDensity 1) = μ at hm
  rwa [withDensity_one] at hm

end ChangeOfVariables

end EulerDeformationVolume
