/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasAffineCorrection
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasLocalUniqueness
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasStrongWellPosedness

/-!
# Closed-manifold tensor-heat existence without atlas assumptions

This file combines compact-atlas construction, the quantitative short-time
commutator contraction, and the arbitrary-trace affine correction.  The
result quantifies only over the geometric background and the time/Holder
parameters: the finite atlas and its strict commutator lift are conclusions,
not hypotheses.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology

namespace RicciFlow
namespace AnalyticPDE
namespace FiniteTensorHeatParametrixAtlas

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [CompactSpace M] [SigmaCompactSpace M] [I.Boundaryless] [Nonempty M]

variable {d : ℕ} {t₀ T α : ℝ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

@[reducible] local instance closedExistenceThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedAddCommGroup
@[reducible] local instance closedExistenceThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedSpace
@[reducible] local instance closedExistenceThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedAddCommGroup x
@[reducible] local instance closedExistenceThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedSpace x
local instance closedExistenceThreeTotalSpaceTopology :
    TopologicalSpace (TotalSpace
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance closedExistenceThreeFiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance closedExistenceThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂

/-- **Short-time existence for the tensor heat equation on a closed
Riemannian manifold, with no atlas or parametrix hypothesis.**

The theorem constructs a positive terminal time, a finite normalized atlas,
and the strict commutator lift.  For every higher atlas initial extension and
every atlas Holder source, the resulting classical field has the prescribed
geometric initial trace, solves the actual intrinsic connection heat
equation, and satisfies the explicit finite-atlas Schauder estimate.

The atlas data are part of the conclusion so subsequent intrinsic data-space
encoders can target the single atlas selected here without adding an analytic
solvability assumption. -/
theorem exists_short_affine_tensorHeat_solver
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (b : Module.Basis (Fin d) ℝ E)
    (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ (S : ℝ) (_hS : t₀ < S)
      (A : FiniteTensorHeatParametrixAtlas
        (E := E) (I := I) (M := M) cov b t₀ S α)
      (K : CommutatorLift cov A),
      HasLocalZeroTraceUniqueness cov A ∧
        ∀ (h : HigherCoefficientSpace cov A) (f : SourceSpace cov A),
          FiniteClassicalTensorHeatField.HasInitialTrace cov
              (affineCorrectedField cov A K h f) (atlasInitialTrace cov A h) ∧
            (∀ (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime) (x : M),
              (affineCorrectedField cov A K h f).tensorHeatOperator cov t ht x =
                A.physicalAtlasSourceSlice cov f t x) ∧
            ‖affineLocalSolutionFamily cov A h
                (affineCorrectedCoordinateSource cov K h f)‖ ≤
              ‖h‖ + ‖localSolutionFamilyL cov A‖ *
                (1 - ‖K.toContinuousLinearMap‖)⁻¹ *
                  ‖f - localCoordinateCauchyFamilyL cov A h +
                    higherAtlasCommutatorLiftL cov A h‖ := by
  obtain ⟨A₀, hmargin⟩ := exists_atlas_with_frozen_margin cov b hT hα hα1
  obtain ⟨S, hS, hST, ⟨K⟩⟩ :=
    exists_restrictedTerminalAtlas_commutatorLift cov A₀
  let A := A₀.restrictTerminalAtlas cov hS hST
  refine ⟨S, hS, A, K,
    hasLocalZeroTraceUniqueness_restrictTerminalAtlas
      cov A₀ hmargin hS hST, ?_⟩
  intro h f
  refine ⟨hasInitialTrace_affineCorrectedField cov A K h f, ?_, ?_⟩
  · intro t ht x
    exact affineCorrectedField_tensorHeatOperator cov A K h f t ht x
  · exact norm_affineCorrectedSolutionFamily_le cov K h f

/-- **Short-time existence, uniqueness, and global finite-atlas Schauder
estimate for the intrinsic covariant two-tensor heat equation on a closed
Riemannian manifold, with no atlas or parametrix hypothesis.**

The theorem constructs the positive time interval, finite atlas, and strict
commutator correction from the geometric background.  It then quantifies over
arbitrary initial extensions in the atlas `C^{2+α}` trace class and arbitrary
atlas `C^{α,α/2}` sources.  The unique higher family reconstructs to an actual
classical covariant two-tensor field, has the prescribed geometric initial
trace, satisfies `∂ₜu - Δu = f` intrinsically at every point, and obeys the
displayed global finite-atlas Schauder bound. -/
theorem exists_short_tensorHeat_wellPosed
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (b : Module.Basis (Fin d) ℝ E)
    (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ (S : ℝ) (_hS : t₀ < S) (_hST : S ≤ T)
      (A : FiniteTensorHeatParametrixAtlas
        (E := E) (I := I) (M := M) cov b t₀ S α)
      (Hlift : StrongCommutatorLift cov A),
      HasLocalZeroTraceUniqueness cov A ∧
        ∀ (h : HigherCoefficientSpace cov A) (f : SourceSpace cov A),
          (∃! u : HigherCoefficientSpace cov A,
            StrongAtlasClassicalSolution cov Hlift h f u) ∧
          ∀ u : HigherCoefficientSpace cov A,
            StrongAtlasClassicalSolution cov Hlift h f u →
              ‖u‖ ≤
                ‖h‖ + ‖localSolutionFamilyL cov A‖ *
                  (1 - ‖Hlift.sourceLift.toContinuousLinearMap‖)⁻¹ *
                    ‖f - localCoordinateCauchyFamilyL cov A h +
                      Hlift.higherMap h‖ := by
  obtain ⟨A₀, hmargin⟩ :=
    exists_atlas_with_frozen_margin cov b hT hα hα1
  obtain ⟨S, hS, hST, ⟨Hlift⟩⟩ :=
    exists_restrictedTerminalAtlas_strongCommutatorLift cov A₀
  let A := A₀.restrictTerminalAtlas cov hS hST
  have hunique : HasLocalZeroTraceUniqueness cov A :=
    hasLocalZeroTraceUniqueness_restrictTerminalAtlas
      cov A₀ hmargin hS hST
  refine ⟨S, hS, hST, A, Hlift, hunique, ?_⟩
  intro h f
  refine ⟨existsUnique_strongAtlasClassicalSolution
    cov hunique Hlift h f, ?_⟩
  intro u hu
  have hueq : u = strongSolutionFamily cov Hlift h f :=
    strongAtlasSolutionEquation_unique cov hunique Hlift h f
      hu.1 (strongSolutionFamily_solves cov Hlift h f)
  rw [hueq]
  exact norm_strongSolutionFamily_le cov Hlift h f

end FiniteTensorHeatParametrixAtlas
end AnalyticPDE
end RicciFlow
