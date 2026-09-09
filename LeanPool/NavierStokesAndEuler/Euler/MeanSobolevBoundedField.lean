/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanSpatialEvaluation
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFieldAlgebra
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-!
# Actual bounded continuous representatives from smooth L² jets

The bounded map into uniform-norm fields is built from the already proved
Sobolev point evaluation. A finite coordinate reconstruction extends it to
any finite-dimensional real target. It is used only for qualitative closure;
the sharp word estimates use their previously proved direct bounds.
-/

noncomputable section

namespace EulerMeanSobolevBoundedField

open MeasureTheory Set ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerSobolevPointEvaluation
  EulerLpTranslation.SmoothL2Field EulerLpDerivative
open scoped BoundedContinuousFunction ContDiff

private local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The genuine cylinder Sobolev representative, restricted to ordinary space. -/
def sobolevField (u : SobolevSpace 1 3) : Space →ᵇ Space :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => pointEvaluation 1 (x,0) u)
    ((EulerSobolevPointEvaluation.representative_continuous 1 u).comp
      (continuous_id.prodMk continuous_const))
    (sobolevEmbeddingConstant 1 3*‖u‖) (fun x => EulerSobolevPointEvaluation.representative_bound 1
      u (x,0))

theorem sobolevField_norm (u : SobolevSpace 1 3) :
    ‖sobolevField u‖ ≤ sobolevEmbeddingConstant 1 3*‖u‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
    (mul_nonneg (sobolevEmbeddingConstant_nonneg 1 3) (norm_nonneg u)) _

def sobolevLinear : SobolevSpace 1 3 →ₗ[ℝ] (Space →ᵇ Space) where
  toFun := sobolevField
  map_add' u v := by
    apply BoundedContinuousFunction.ext
    intro x
    exact (pointEvaluation 1 (x,0)).map_add u v
  map_smul' c u := by
    apply BoundedContinuousFunction.ext
    intro x
    exact (pointEvaluation 1 (x,0)).map_smul c u

/-- Sobolev evaluation is bounded in the uniform norm, not just pointwise. -/
def sobolevMap : SobolevSpace 1 3 →L[ℝ] (Space →ᵇ Space) :=
  sobolevLinear.mkContinuous (sobolevEmbeddingConstant 1 3) sobolevField_norm

def spaceField (A : EulerLpTranslation.SmoothL2Field Space) : Space →ᵇ Space :=
  sobolevMap (ordinarySobolev 3 A.toLp A.translation_contDiff)

@[simp] theorem spaceField_apply (A : EulerLpTranslation.SmoothL2Field Space) (x : Space) :
    spaceField A x = A.field x := by
  have he := representative_unique A.toLp A.translation_contDiff A.field A.smooth.continuous
    A.toLp_ae
  exact (pointEvaluation_ordinary A.toLp A.translation_contDiff x).trans (congrFun he x)

theorem continuous_spaceField {K : Type*} [TopologicalSpace K]
    (A : K → EulerLpTranslation.SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) : Continuous (fun t => spaceField (A t)) := by
  apply sobolevMap.continuous.comp
  apply ordinarySobolev_continuous 3 (fun t => (A t).toLp) (fun t => (A t).translation_contDiff)
  intro n _
  have he : (fun t => iteratedFDeriv ℝ n (fun a : Space => translation a (A t).toLp) 0) =
      fun t => multilinearBundling (P := Space) (V := Space) volume n ((A t).jetLp n) := by
    funext t
    have h := (A t).iteratedFDeriv_translation_eq n 0
    rw [EulerLpTranslation.translation_zero] at h
    simpa only [EulerLpTranslation.translation, EulerMeanSolenoidal.translation] using h
  rw [he]
  exact (multilinearBundling (P := Space) (V := Space) volume n).continuous.comp (hA n)

def scalarEmbedding : ℝ →L[ℝ] Space :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single (0 : Fin 3) 1)

def scalarField (A : EulerLpTranslation.SmoothL2Field ℝ) : Space →ᵇ ℝ :=
  (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).compLeftContinuousBounded Space
    (spaceField (mapField scalarEmbedding A))

@[simp] theorem scalarField_apply (A : EulerLpTranslation.SmoothL2Field ℝ) (x : Space) :
    scalarField A x = A.field x := by
  change (spaceField (mapField scalarEmbedding A) x) (0 : Fin 3) = _
  rw [spaceField_apply]
  simp [scalarEmbedding]

theorem continuous_scalarField {K : Type*} [TopologicalSpace K]
    (A : K → EulerLpTranslation.SmoothL2Field ℝ)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) : Continuous (fun t => scalarField (A t)) :=
  ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).compLeftContinuousBounded
    Space).continuous.comp
    (continuous_spaceField (fun t => mapField scalarEmbedding (A t))
      (continuous_jetLp_mapField scalarEmbedding A hA))

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def coordinate (i : Fin (Module.finrank ℝ V)) : V →L[ℝ] ℝ :=
  ((Module.finBasis ℝ V).coord i).toContinuousLinearMap

def coordinateVector (i : Fin (Module.finrank ℝ V)) : ℝ →L[ℝ] V :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (Module.finBasis ℝ V i)

/-- Reconstruct a bounded field from the finitely many actual scalar coordinates. -/
def finiteField (A : EulerLpTranslation.SmoothL2Field V) : Space →ᵇ V :=
  ∑ i : Fin (Module.finrank ℝ V), (coordinateVector i).compLeftContinuousBounded Space
    (scalarField (mapField (coordinate i) A))

@[simp] theorem finiteField_apply (A : EulerLpTranslation.SmoothL2Field V) (x : Space) :
    finiteField A x = A.field x := by
  simp only [finiteField, BoundedContinuousFunction.sum_apply]
  change (∑ i : Fin (Module.finrank ℝ V), coordinateVector i (scalarField (mapField (coordinate i)
    A) x)) = _
  simp only [scalarField_apply, mapField_field]
  exact (Module.finBasis ℝ V).sum_repr (A.field x)

/-- Continuity of the real L² spatial jets implies continuity in the uniform field norm. -/
theorem continuous_finiteField {K : Type*} [TopologicalSpace K]
    (A : K → EulerLpTranslation.SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) : Continuous (fun t => finiteField (A t)) := by
  apply continuous_finsetSum
  intro i _
  exact ((coordinateVector (V := V) i).compLeftContinuousBounded Space).continuous.comp
    (continuous_scalarField (fun t => mapField (coordinate i) (A t))
      (continuous_jetLp_mapField (coordinate i) A hA))

end EulerMeanSobolevBoundedField
