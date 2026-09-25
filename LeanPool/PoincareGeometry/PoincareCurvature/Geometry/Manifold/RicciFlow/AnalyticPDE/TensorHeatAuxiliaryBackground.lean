/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatClosedExistence
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.TorsionFreeAuxiliaryBackground
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.InducedHomRegularity

/-!
# Auxiliary geometric background for tensor heat

This file selects a global `C²` affine connection on the tangent bundle and
derives the induced tensor-connection regularity used by the closed-manifold
tensor-heat solver.  It turns those background choices into conclusions along
with the solver's finite-atlas existence, uniqueness, and estimate package.
-/

@[expose] public section

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

@[reducible] local instance auxiliaryBackgroundThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedAddCommGroup
@[reducible] local instance auxiliaryBackgroundThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedSpace
@[reducible] local instance auxiliaryBackgroundThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedAddCommGroup x
@[reducible] local instance auxiliaryBackgroundThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedSpace x
local instance auxiliaryBackgroundThreeTotalSpaceTopology :
    TopologicalSpace (TotalSpace
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance auxiliaryBackgroundThreeFiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance auxiliaryBackgroundThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂

/-- **Closed-manifold tensor-heat well-posedness from an auxiliary smooth
connection.**

The theorem chooses one globally `C²` tangent-bundle connection, records its
`C¹` downgrade and the regularity of its induced covariant two- and
three-tensor connections, then supplies the complete finite-atlas tensor-heat
well-posedness package. -/
theorem exists_short_tensorHeat_wellPosed_auxiliaryBackground
    (b : Module.Basis (Fin d) ℝ E)
    (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ (cov : CovariantDerivative I E TM)
      (hcovOne : ContMDiffCovariantDerivative cov 1)
      (hcovTwo : ContMDiffCovariantDerivative cov 2)
      (htwoOne : ContMDiffCovariantDerivative
        (covariantTwoTensorCovariantDerivative
          (E := E) (I := I) (M := M) cov) 1)
      (htwoTwo : ContMDiffCovariantDerivative
        (covariantTwoTensorCovariantDerivative
          (E := E) (I := I) (M := M) cov) 2)
      (hthreeOne : ContMDiffCovariantDerivative
        (covariantThreeTensorCovariantDerivative
          (E := E) (I := I) (M := M) cov) 1),
      letI : ContMDiffCovariantDerivative cov 1 := hcovOne
      letI : ContMDiffCovariantDerivative cov 2 := hcovTwo
      letI : ContMDiffCovariantDerivative
          (covariantTwoTensorCovariantDerivative
            (E := E) (I := I) (M := M) cov) 1 := htwoOne
      letI : ContMDiffCovariantDerivative
          (covariantTwoTensorCovariantDerivative
            (E := E) (I := I) (M := M) cov) 2 := htwoTwo
      letI : ContMDiffCovariantDerivative
          (covariantThreeTensorCovariantDerivative
            (E := E) (I := I) (M := M) cov) 1 := hthreeOne
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
  obtain ⟨cov, hcovTwo⟩ :=
    CovariantDerivative.exists_contMDiffAffineConnection_two
      (I := I) (E := E) (M := M)
  letI covTwo : ContMDiffCovariantDerivative cov 2 := hcovTwo
  let hcovOne : ContMDiffCovariantDerivative cov 1 :=
    CovariantDerivative.contMDiffCovariantDerivative_one_of_contMDiffCovariantDerivative_two
      (I := I) (F := E) (V := TM)
  letI covOne : ContMDiffCovariantDerivative cov 1 := hcovOne
  letI tangentTwo : ContMDiffVectorBundle 2 E TM I :=
    ContMDiffVectorBundle.of_le (n := 3) (by norm_num)
  let htwoOne : ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1 :=
    CovariantDerivative.contMDiffCovariantDerivative_covariantTwoTensor_one
      (I := I) (E := E) (M := M) cov
  letI twoOne : ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1 := htwoOne
  let htwoTwo : ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2 :=
    CovariantDerivative.contMDiffCovariantDerivative_covariantTwoTensor_two
      (I := I) (E := E) (M := M) cov
  letI twoTwo : ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2 := htwoTwo
  let hthreeOne : ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1 :=
    CovariantDerivative.contMDiffCovariantDerivative_covariantThreeTensor_one
      (I := I) (E := E) (M := M) cov
  letI threeOne : ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1 := hthreeOne
  refine ⟨cov, hcovOne, hcovTwo, htwoOne, htwoTwo, hthreeOne, ?_⟩
  exact exists_short_tensorHeat_wellPosed cov b hT hα hα1

/-- **Closed-manifold linear tensor-heat well-posedness from a torsion-free
auxiliary background.**

The selected affine tangent-bundle connection is globally `C²` and has zero
torsion.  The conclusion remains the linear tensor-heat finite-atlas package;
it makes no nonlinear Ricci-flow existence claim. -/
theorem exists_short_tensorHeat_wellPosed_torsionFreeAuxiliaryBackground
    (b : Module.Basis (Fin d) ℝ E)
    (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ (cov : CovariantDerivative I E TM)
      (_hTorsionFree : cov.IsTorsionFree)
      (_hTorsionZero : cov.torsion = 0)
      (hcovOne : ContMDiffCovariantDerivative cov 1)
      (hcovTwo : ContMDiffCovariantDerivative cov 2)
      (htwoOne : ContMDiffCovariantDerivative
        (covariantTwoTensorCovariantDerivative
          (E := E) (I := I) (M := M) cov) 1)
      (htwoTwo : ContMDiffCovariantDerivative
        (covariantTwoTensorCovariantDerivative
          (E := E) (I := I) (M := M) cov) 2)
      (hthreeOne : ContMDiffCovariantDerivative
        (covariantThreeTensorCovariantDerivative
          (E := E) (I := I) (M := M) cov) 1),
      letI : ContMDiffCovariantDerivative cov 1 := hcovOne
      letI : ContMDiffCovariantDerivative cov 2 := hcovTwo
      letI : ContMDiffCovariantDerivative
          (covariantTwoTensorCovariantDerivative
            (E := E) (I := I) (M := M) cov) 1 := htwoOne
      letI : ContMDiffCovariantDerivative
          (covariantTwoTensorCovariantDerivative
            (E := E) (I := I) (M := M) cov) 2 := htwoTwo
      letI : ContMDiffCovariantDerivative
          (covariantThreeTensorCovariantDerivative
            (E := E) (I := I) (M := M) cov) 1 := hthreeOne
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
  let background :=
    fixedTorsionFreeAffineBackground (I := I) (M := M)
  let cov := background.covariantDerivative
  have hTorsionFree : cov.IsTorsionFree := by
    simpa only [cov] using background.isTorsionFree
  have hTorsionZero : cov.torsion = 0 := hTorsionFree
  have hcovTwo : ContMDiffCovariantDerivative cov 2 := by
    simpa only [cov] using background.contMDiff
  letI covTwo : ContMDiffCovariantDerivative cov 2 := hcovTwo
  let hcovOne : ContMDiffCovariantDerivative cov 1 :=
    CovariantDerivative.contMDiffCovariantDerivative_one_of_contMDiffCovariantDerivative_two
      (I := I) (F := E) (V := TM)
  letI covOne : ContMDiffCovariantDerivative cov 1 := hcovOne
  letI tangentTwo : ContMDiffVectorBundle 2 E TM I :=
    ContMDiffVectorBundle.of_le (n := 3) (by norm_num)
  let htwoOne : ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1 :=
    CovariantDerivative.contMDiffCovariantDerivative_covariantTwoTensor_one
      (I := I) (E := E) (M := M) cov
  letI twoOne : ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1 := htwoOne
  let htwoTwo : ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2 :=
    CovariantDerivative.contMDiffCovariantDerivative_covariantTwoTensor_two
      (I := I) (E := E) (M := M) cov
  letI twoTwo : ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2 := htwoTwo
  let hthreeOne : ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1 :=
    CovariantDerivative.contMDiffCovariantDerivative_covariantThreeTensor_one
      (I := I) (E := E) (M := M) cov
  letI threeOne : ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1 := hthreeOne
  refine ⟨cov, hTorsionFree, hTorsionZero, hcovOne, hcovTwo,
    htwoOne, htwoTwo, hthreeOne, ?_⟩
  exact exists_short_tensorHeat_wellPosed cov b hT hα hα1

end FiniteTensorHeatParametrixAtlas
end AnalyticPDE
end RicciFlow
