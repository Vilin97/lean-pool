/-
Copyright (c) 2026 Petr Girg, Petr Nečesal, Martin Dvořák, Jakub Psutka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Petr Girg, Petr Nečesal, Martin Dvořák, Jakub Psutka
-/

module

public import LeanPool.NemytskiiLebesgue.Basic

/-!
# Nemytskii operators: RealIso

Adapted from `madvorak/nemytskii-lebesgue` (Apache-2.0).
-/

public section

namespace NemytskiiLebesgue

open scoped NemytskiiLebesgue

open MeasureTheory
open scoped ENNReal

/-- The canonical real linear isometry to one-dimensional Euclidean space. -/
@[expose] noncomputable def realLIE : ℝ ≃ₗᵢ[ℝ] ℝ^1 where
  toLinearEquiv :=
    (LinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.trans (WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ)).symm
  norm_map' := by
    intro
    rw [EuclideanSpace.norm_eq]
    simp [WithLp.linearEquiv, LinearEquiv.funUnique, Real.sqrt_sq_eq_abs]

lemma norm_realLIE (r : ℝ) : ‖realLIE r‖ = |r| := realLIE.norm_map r

lemma realLIE_mul (c s : ℝ) : realLIE (c * s) = c • realLIE s := by
  rw [←smul_eq_mul, map_smul]

lemma normSMulSelf_realLIE {T : Type} (t : T) (s : ℝ) :
    normSMulSelf t (realLIE s) = realLIE (|s| * s) := by
  rw [normSMulSelf, norm_realLIE, ←smul_eq_mul, map_smul]

lemma eLpNorm_realLIE {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ≥0∞} (u : Ω → ℝ) :
    eLpNorm (fun ω : Ω => realLIE (u ω)) p μ = eLpNorm u p μ := by
  by_cases hu : AEStronglyMeasurable u μ
  · have hru := realLIE.continuous.comp_aestronglyMeasurable hu
    rw [←eLpNorm_norm _ hru, ←eLpNorm_norm _ hu]
    simp
  · have hru : ¬ AEStronglyMeasurable (fun ω => realLIE (u ω)) μ := by
      intro h
      apply hu
      simpa using realLIE.symm.continuous.comp_aestronglyMeasurable h
    rw [eLpNorm_of_not_aestronglyMeasurable hu,
      eLpNorm_of_not_aestronglyMeasurable hru]

lemma memLp_realLIE {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ≥0∞} {u : Ω → ℝ} (hu : MemLp u p μ) :
    MemLp (fun ω : Ω => realLIE (u ω)) p μ :=
  hu.continuousLinearMap_comp realLIE.toLinearEquiv.toContinuousLinearMap

end NemytskiiLebesgue
