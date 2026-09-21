/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasShortCommutatorLift

/-!
# Quantitative short-time tensor-heat commutator contraction

This file bounds the concrete geometric commutator lift by two fixed finite
atlas constants times the zero-trace gradient and value interpolation
factors.  Both factors tend to zero with the cylinder thickness, producing
an actual time-restricted atlas whose commutator lift has norm below one.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff Topology NNReal

namespace RicciFlow
namespace AnalyticPDE
namespace FiniteTensorHeatParametrixAtlas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [CompactSpace M] [SigmaCompactSpace M] [I.Boundaryless]

variable {d : ℕ} {t₀ S T α : ℝ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "W₂" => (Fin d × Fin d → ℝ)
local notation "DW₂" => (E →L[ℝ] W₂)
local notation "D2W₂" => (E →L[ℝ] E →L[ℝ] W₂)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

@[reducible] local instance contractionFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup DW₂ := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance contractionFirstDerivativeNormedSpace :
    NormedSpace ℝ DW₂ := ContinuousLinearMap.toNormedSpace
@[reducible] local instance contractionFirstCoefficientNormedAddCommGroup :
    NormedAddCommGroup (DW₂ →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance contractionFirstCoefficientNormedSpace :
    NormedSpace ℝ (DW₂ →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance contractionZeroCoefficientNormedAddCommGroup :
    NormedAddCommGroup (W₂ →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance contractionZeroCoefficientNormedSpace :
    NormedSpace ℝ (W₂ →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance contractionSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup D2W₂ := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance contractionSecondDerivativeNormedSpace :
    NormedSpace ℝ D2W₂ := ContinuousLinearMap.toNormedSpace
@[reducible] local instance contractionScalarThirdNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedAddCommGroup
@[reducible] local instance contractionScalarThirdNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedSpace
@[reducible] local instance contractionThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedAddCommGroup x
@[reducible] local instance contractionThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedSpace x
local instance contractionThreeTotalSpaceTopology :
    TopologicalSpace (TotalSpace
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance contractionThreeFiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance contractionThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂

/-- The fixed operator-size cost of masking, changing frame, rescaling, and
pulling a source through one ordered pair of charts. -/
def shortPairOuterConstant
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) : ℝ :=
  (‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] W₂ →L[ℝ] W₂)‖ *
      ‖normalizedPairBufferedCutoffField cov A j i‖) *
    (‖A.radius (j : M) ^ 2‖ *
      ((‖operatorEvaluation W₂ W₂‖ *
          ‖normalizedPairFrameCoefficientField cov A j i‖) *
        (max 1 (pairSpacetimeLipschitzBound cov A j i ^ α) * 3)))

lemma shortPairOuterConstant_nonneg
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) :
    0 ≤ shortPairOuterConstant cov A j i := by
  unfold shortPairOuterConstant
  positivity

/-- Restricting the first-order geometric coefficient cannot increase its
Holder norm. -/
theorem norm_shortCutoffCommutatorFirstField_le
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) (hST : S ≤ T) :
    ‖shortCutoffCommutatorFirstField cov A i hST‖ ≤
      ‖normalizedCutoffCommutatorFirstField cov A i‖ := by
  let R : ParabolicC0AlphaSpace E (DW₂ →L[ℝ] W₂) α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      ParabolicC0AlphaSpace E (DW₂ →L[ℝ] W₂) α
        (parabolicFiniteCylinder E t₀ S) :=
    ParabolicC0AlphaSpace.restrictL
      (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST)
  calc
    ‖shortCutoffCommutatorFirstField cov A i hST‖ ≤
        ‖R‖ * ‖normalizedCutoffCommutatorFirstField cov A i‖ :=
      R.le_opNorm _
    _ ≤ 1 * ‖normalizedCutoffCommutatorFirstField cov A i‖ :=
      mul_le_mul_of_nonneg_right
        (ParabolicC0AlphaSpace.norm_restrictL_le
          (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST))
        (norm_nonneg _)
    _ = _ := one_mul _

/-- Restricting the zeroth-order geometric coefficient cannot increase its
Holder norm. -/
theorem norm_shortCutoffCommutatorZeroField_le
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) (hST : S ≤ T) :
    ‖shortCutoffCommutatorZeroField cov A i hST‖ ≤
      ‖normalizedCutoffCommutatorZeroField cov A i‖ := by
  let R : ParabolicC0AlphaSpace E (W₂ →L[ℝ] W₂) α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      ParabolicC0AlphaSpace E (W₂ →L[ℝ] W₂) α
        (parabolicFiniteCylinder E t₀ S) :=
    ParabolicC0AlphaSpace.restrictL
      (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST)
  calc
    ‖shortCutoffCommutatorZeroField cov A i hST‖ ≤
        ‖R‖ * ‖normalizedCutoffCommutatorZeroField cov A i‖ :=
      R.le_opNorm _
    _ ≤ 1 * ‖normalizedCutoffCommutatorZeroField cov A i‖ :=
      mul_le_mul_of_nonneg_right
        (ParabolicC0AlphaSpace.norm_restrictL_le
          (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST))
        (norm_nonneg _)
    _ = _ := one_mul _

/-- The local commutator residual is small by the zero-initial short-time
interpolation estimate, with coefficients bounded by the fixed parent
atlas. -/
theorem norm_shortCutoffCommutatorLocalResidualL_le
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) (hS : t₀ < S) (hST : S ≤ T)
    (hthin : S - t₀ ≤ 1) :
    ‖shortCutoffCommutatorLocalResidualL cov A i hS hST‖ ≤
      FiniteParabolicC2AlphaBanach.lowerOrderShortTimeFactor
          (X := E) (W := W₂)
          ‖normalizedCutoffCommutatorFirstField cov A i‖
          ‖normalizedCutoffCommutatorZeroField cov A i‖
          (S - t₀) α *
        (3 * ‖A.localInverse (i : M)‖) := by
  refine (A.norm_lowerOrderL_comp_shortLocalInverse_le cov (i : M)
    hS hST hthin
    (shortCutoffCommutatorFirstField cov A i hST)
    (shortCutoffCommutatorZeroField cov A i hST)).trans ?_
  unfold FiniteParabolicC2AlphaBanach.lowerOrderShortTimeFactor
  have hD : 0 ≤ S - t₀ := sub_nonneg.mpr hS.le
  have hg := FiniteParabolicC2AlphaBanach.gradientShortTimeFactor_nonneg
    (α := α) hD
  have hv := FiniteParabolicC2AlphaBanach.valueShortTimeFactor_nonneg
    (α := α) hD
  gcongr
  · exact norm_shortCutoffCommutatorFirstField_le cov A i hST
  · exact norm_shortCutoffCommutatorZeroField_le cov A i hST

theorem norm_shortPairFrameCoefficientField_le
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) (hST : S ≤ T) :
    ‖shortPairFrameCoefficientField cov A j i hST‖ ≤
      ‖normalizedPairFrameCoefficientField cov A j i‖ := by
  let R : ParabolicC0AlphaSpace E (W₂ →L[ℝ] W₂) α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      ParabolicC0AlphaSpace E (W₂ →L[ℝ] W₂) α
        (parabolicFiniteCylinder E t₀ S) :=
    ParabolicC0AlphaSpace.restrictL
      (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST)
  calc
    ‖shortPairFrameCoefficientField cov A j i hST‖ ≤
        ‖R‖ * ‖normalizedPairFrameCoefficientField cov A j i‖ :=
      R.le_opNorm _
    _ ≤ 1 * ‖normalizedPairFrameCoefficientField cov A j i‖ :=
      mul_le_mul_of_nonneg_right
        (ParabolicC0AlphaSpace.norm_restrictL_le
          (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST))
        (norm_nonneg _)
    _ = _ := one_mul _

theorem norm_shortPairBufferedCutoffField_le
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) (hST : S ≤ T) :
    ‖shortPairBufferedCutoffField cov A j i hST‖ ≤
      ‖normalizedPairBufferedCutoffField cov A j i‖ := by
  let R : ParabolicC0AlphaSpace E ℝ α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      ParabolicC0AlphaSpace E ℝ α
        (parabolicFiniteCylinder E t₀ S) :=
    ParabolicC0AlphaSpace.restrictL
      (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST)
  calc
    ‖shortPairBufferedCutoffField cov A j i hST‖ ≤
        ‖R‖ * ‖normalizedPairBufferedCutoffField cov A j i‖ :=
      R.le_opNorm _
    _ ≤ 1 * ‖normalizedPairBufferedCutoffField cov A j i‖ :=
      mul_le_mul_of_nonneg_right
        (ParabolicC0AlphaSpace.norm_restrictL_le
          (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST))
        (norm_nonneg _)
    _ = _ := one_mul _

/-- The short pairwise pullback costs only the fixed transition Lipschitz
factor and the norm-three whole-space extension. -/
theorem norm_shortPairResidualPullbackL_le
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) (hS : t₀ < S) (hST : S ≤ T) :
    ‖shortPairResidualPullbackL cov A j i hS hST‖ ≤
      max 1 (pairSpacetimeLipschitzBound cov A j i ^ α) *
        (3 * ‖shortCutoffCommutatorLocalResidualL cov A i hS hST‖) := by
  unfold shortPairResidualPullbackL
  calc
    ‖(ParabolicC0AlphaBanach.precompL
        A.alpha_pos.le (pairSpacetimeLipschitzBound_nonneg cov A j i)
        (Set.mapsTo_univ _ _)
        (fun p _ q _ =>
          parabolicDistance_extendedPairSpacetimeTransition_le
            cov A j i p q)).comp
      ((ParabolicC0AlphaBanach.finiteSourceExtensionL
        hS A.alpha_pos).comp
        (shortCutoffCommutatorLocalResidualL cov A i hS hST))‖ ≤
        ‖ParabolicC0AlphaBanach.precompL
          A.alpha_pos.le (pairSpacetimeLipschitzBound_nonneg cov A j i)
          (Set.mapsTo_univ _ _)
          (fun p _ q _ =>
            parabolicDistance_extendedPairSpacetimeTransition_le
              cov A j i p q)‖ *
        ‖(ParabolicC0AlphaBanach.finiteSourceExtensionL
          hS A.alpha_pos).comp
          (shortCutoffCommutatorLocalResidualL cov A i hS hST)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ max 1 (pairSpacetimeLipschitzBound cov A j i ^ α) *
        ‖(ParabolicC0AlphaBanach.finiteSourceExtensionL
          hS A.alpha_pos).comp
          (shortCutoffCommutatorLocalResidualL cov A i hS hST)‖ := by
      gcongr
      exact ParabolicC0AlphaBanach.norm_precompL_le
        A.alpha_pos.le (pairSpacetimeLipschitzBound_nonneg cov A j i)
        (Set.mapsTo_univ _ _)
        (fun p _ q _ =>
          parabolicDistance_extendedPairSpacetimeTransition_le
            cov A j i p q)
    _ ≤ max 1 (pairSpacetimeLipschitzBound cov A j i ^ α) *
        (3 * ‖shortCutoffCommutatorLocalResidualL cov A i hS hST‖) := by
      gcongr
      calc
        ‖(ParabolicC0AlphaBanach.finiteSourceExtensionL
            hS A.alpha_pos).comp
            (shortCutoffCommutatorLocalResidualL cov A i hS hST)‖ ≤
            ‖ParabolicC0AlphaBanach.finiteSourceExtensionL
              hS A.alpha_pos‖ *
              ‖shortCutoffCommutatorLocalResidualL cov A i hS hST‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 3 * ‖shortCutoffCommutatorLocalResidualL
              cov A i hS hST‖ :=
          mul_le_mul_of_nonneg_right
            (ParabolicC0AlphaBanach.norm_finiteSourceExtensionL_le
              hS A.alpha_pos) (norm_nonneg _)

/-- The complete supported pair transport is bounded by its fixed geometric
outer cost times the small local commutator residual. -/
theorem norm_shortSupportedPairResidualTransportL_le
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) (hS : t₀ < S) (hST : S ≤ T) :
    ‖shortSupportedPairResidualTransportL cov A j i hS hST‖ ≤
      shortPairOuterConstant cov A j i *
        ‖shortCutoffCommutatorLocalResidualL cov A i hS hST‖ := by
  unfold shortSupportedPairResidualTransportL shortPairResidualTransportL
  calc
    ‖(ParabolicC0AlphaBanach.mulCoeffL
        (ContinuousLinearMap.lsmul ℝ ℝ)
        (shortPairBufferedCutoffField cov A j i hST)).comp
      (A.radius (j : M) ^ 2 •
        ((ParabolicC0AlphaBanach.mulCoeffL
          (operatorEvaluation W₂ W₂)
          (shortPairFrameCoefficientField cov A j i hST)).comp
            (shortPairResidualPullbackL cov A j i hS hST)))‖ ≤
        ‖ParabolicC0AlphaBanach.mulCoeffL
          (ContinuousLinearMap.lsmul ℝ ℝ)
          (shortPairBufferedCutoffField cov A j i hST)‖ *
        ‖A.radius (j : M) ^ 2 •
          ((ParabolicC0AlphaBanach.mulCoeffL
            (operatorEvaluation W₂ W₂)
            (shortPairFrameCoefficientField cov A j i hST)).comp
              (shortPairResidualPullbackL cov A j i hS hST))‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖(ContinuousLinearMap.lsmul ℝ ℝ :
          ℝ →L[ℝ] W₂ →L[ℝ] W₂)‖ *
          ‖shortPairBufferedCutoffField cov A j i hST‖) *
        (‖A.radius (j : M) ^ 2‖ *
          ‖(ParabolicC0AlphaBanach.mulCoeffL
            (operatorEvaluation W₂ W₂)
            (shortPairFrameCoefficientField cov A j i hST)).comp
              (shortPairResidualPullbackL cov A j i hS hST)‖) := by
      gcongr
      · exact ParabolicC0AlphaBanach.norm_mulCoeffL_le _ _
      · rw [norm_smul]
    _ ≤ (‖(ContinuousLinearMap.lsmul ℝ ℝ :
          ℝ →L[ℝ] W₂ →L[ℝ] W₂)‖ *
          ‖shortPairBufferedCutoffField cov A j i hST‖) *
        (‖A.radius (j : M) ^ 2‖ *
          ((‖operatorEvaluation W₂ W₂‖ *
              ‖shortPairFrameCoefficientField cov A j i hST‖) *
            ‖shortPairResidualPullbackL cov A j i hS hST‖)) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _ |>.trans <|
        mul_le_mul_of_nonneg_right
          (ParabolicC0AlphaBanach.norm_mulCoeffL_le _ _) (norm_nonneg _)
    _ ≤ (‖(ContinuousLinearMap.lsmul ℝ ℝ :
          ℝ →L[ℝ] W₂ →L[ℝ] W₂)‖ *
          ‖normalizedPairBufferedCutoffField cov A j i‖) *
        (‖A.radius (j : M) ^ 2‖ *
          ((‖operatorEvaluation W₂ W₂‖ *
              ‖normalizedPairFrameCoefficientField cov A j i‖) *
            (max 1 (pairSpacetimeLipschitzBound cov A j i ^ α) *
              (3 * ‖shortCutoffCommutatorLocalResidualL
                cov A i hS hST‖)))) := by
      gcongr
      · exact norm_shortPairBufferedCutoffField_le cov A j i hST
      · exact norm_shortPairFrameCoefficientField_le cov A j i hST
      · exact norm_shortPairResidualPullbackL_le cov A j i hS hST
    _ = shortPairOuterConstant cov A j i *
        ‖shortCutoffCommutatorLocalResidualL cov A i hS hST‖ := by
      unfold shortPairOuterConstant
      ring

def shortPairGradientWeight
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) : ℝ :=
  shortPairOuterConstant cov A j i *
    (3 * ‖A.localInverse (i : M)‖) *
      (‖operatorEvaluation (E →L[ℝ] W₂) W₂‖ *
        ‖normalizedCutoffCommutatorFirstField cov A i‖)

def shortPairValueWeight
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) : ℝ :=
  shortPairOuterConstant cov A j i *
    (3 * ‖A.localInverse (i : M)‖) *
      (‖operatorEvaluation W₂ W₂‖ *
        ‖normalizedCutoffCommutatorZeroField cov A i‖)

lemma shortPairGradientWeight_nonneg
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) :
    0 ≤ shortPairGradientWeight cov A j i := by
  unfold shortPairGradientWeight
  exact mul_nonneg
    (mul_nonneg (shortPairOuterConstant_nonneg cov A j i) (by positivity))
    (by positivity)

lemma shortPairValueWeight_nonneg
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) :
    0 ≤ shortPairValueWeight cov A j i := by
  unfold shortPairValueWeight
  exact mul_nonneg
    (mul_nonneg (shortPairOuterConstant_nonneg cov A j i) (by positivity))
    (by positivity)

theorem norm_shortSupportedPairResidualTransportL_le_weights
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) (hS : t₀ < S) (hST : S ≤ T)
    (hthin : S - t₀ ≤ 1) :
    ‖shortSupportedPairResidualTransportL cov A j i hS hST‖ ≤
      shortPairGradientWeight cov A j i *
          FiniteParabolicC2AlphaBanach.gradientShortTimeFactor
            (S - t₀) α +
        shortPairValueWeight cov A j i *
          FiniteParabolicC2AlphaBanach.valueShortTimeFactor
            (S - t₀) α := by
  calc
    ‖shortSupportedPairResidualTransportL cov A j i hS hST‖ ≤
        shortPairOuterConstant cov A j i *
          ‖shortCutoffCommutatorLocalResidualL cov A i hS hST‖ :=
      norm_shortSupportedPairResidualTransportL_le cov A j i hS hST
    _ ≤ shortPairOuterConstant cov A j i *
        (FiniteParabolicC2AlphaBanach.lowerOrderShortTimeFactor
            (X := E) (W := W₂)
            ‖normalizedCutoffCommutatorFirstField cov A i‖
            ‖normalizedCutoffCommutatorZeroField cov A i‖
            (S - t₀) α *
          (3 * ‖A.localInverse (i : M)‖)) :=
      mul_le_mul_of_nonneg_left
        (norm_shortCutoffCommutatorLocalResidualL_le
          cov A i hS hST hthin)
        (shortPairOuterConstant_nonneg cov A j i)
    _ = shortPairGradientWeight cov A j i *
          FiniteParabolicC2AlphaBanach.gradientShortTimeFactor
            (S - t₀) α +
        shortPairValueWeight cov A j i *
          FiniteParabolicC2AlphaBanach.valueShortTimeFactor
            (S - t₀) α := by
      unfold FiniteParabolicC2AlphaBanach.lowerOrderShortTimeFactor
      unfold shortPairGradientWeight shortPairValueWeight
      ring

/-- Sum of all ordered-pair gradient costs.  Summing over targets rather
than taking a maximum gives a simple uniform row bound. -/
def shortAtlasGradientWeight
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α) : ℝ :=
  ∑ j : A.cover.Index, ∑ i : A.cover.Index,
    shortPairGradientWeight cov A j i

/-- Sum of all ordered-pair zeroth-order costs. -/
def shortAtlasValueWeight
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α) : ℝ :=
  ∑ j : A.cover.Index, ∑ i : A.cover.Index,
    shortPairValueWeight cov A j i

lemma shortAtlasGradientWeight_nonneg
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α) :
    0 ≤ shortAtlasGradientWeight cov A := by
  unfold shortAtlasGradientWeight
  exact Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun i _ => shortPairGradientWeight_nonneg cov A j i

lemma shortAtlasValueWeight_nonneg
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α) :
    0 ≤ shortAtlasValueWeight cov A := by
  unfold shortAtlasValueWeight
  exact Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun i _ => shortPairValueWeight_nonneg cov A j i

private lemma norm_piProjection_le_one
    {ι : Type*} [Fintype ι]
    {G : ι → Type*} [∀ i, SeminormedAddCommGroup (G i)]
    [∀ i, NormedSpace ℝ (G i)] (i : ι) :
    ‖(ContinuousLinearMap.proj i : (∀ i, G i) →L[ℝ] G i)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => ?_)
  rw [one_mul, ContinuousLinearMap.proj_apply, Pi.norm_def]
  exact_mod_cast Finset.le_sup (s := Finset.univ)
    (f := fun j => ‖f j‖₊) (Finset.mem_univ i)

private lemma norm_comp_piProjection_le
    {iota : Type*} [Fintype iota]
    {G : iota → Type*} [∀ i, SeminormedAddCommGroup (G i)]
    [∀ i, NormedSpace ℝ (G i)]
    {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (i : iota) (L : G i →L[ℝ] F) :
    ‖L.comp (ContinuousLinearMap.proj i)‖ ≤ ‖L‖ := by
  calc
    ‖L.comp (ContinuousLinearMap.proj i)‖ ≤
        ‖L‖ * ‖(ContinuousLinearMap.proj i : (∀ i, G i) →L[ℝ] G i)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖L‖ * 1 :=
      mul_le_mul_of_nonneg_left (norm_piProjection_le_one i) (norm_nonneg _)
    _ = _ := mul_one _

/-- Projecting to one source component does not enlarge a transport matrix
entry. -/
theorem norm_shortAtlasCommutatorEntryL_le
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) (hS : t₀ < S) (hST : S ≤ T) :
    ‖shortAtlasCommutatorEntryL cov A j i hS hST‖ ≤
      ‖shortSupportedPairResidualTransportL cov A j i hS hST‖ := by
  unfold shortAtlasCommutatorEntryL
  exact norm_comp_piProjection_le i _

/-- Quantitative norm estimate for one target row of the short commutator
matrix. -/
theorem norm_shortAtlasCommutatorRowL_le
    [Nonempty M]
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j : A.cover.Index)
    (hS : t₀ < S) (hST : S ≤ T) (hthin : S - t₀ ≤ 1) :
    ‖shortAtlasCommutatorRowL cov A j hS hST‖ ≤
      (∑ i : A.cover.Index, shortPairGradientWeight cov A j i) *
          FiniteParabolicC2AlphaBanach.gradientShortTimeFactor
            (S - t₀) α +
        (∑ i : A.cover.Index, shortPairValueWeight cov A j i) *
          FiniteParabolicC2AlphaBanach.valueShortTimeFactor
            (S - t₀) α := by
  let g := FiniteParabolicC2AlphaBanach.gradientShortTimeFactor
    (S - t₀) α
  let v := FiniteParabolicC2AlphaBanach.valueShortTimeFactor
    (S - t₀) α
  unfold shortAtlasCommutatorRowL
  calc
    ‖∑ i : A.cover.Index,
        shortAtlasCommutatorEntryL cov A j i hS hST‖ ≤
        ∑ i : A.cover.Index,
          ‖shortAtlasCommutatorEntryL cov A j i hS hST‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : A.cover.Index,
          ‖shortSupportedPairResidualTransportL cov A j i hS hST‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact norm_shortAtlasCommutatorEntryL_le cov A j i hS hST
    _ ≤ ∑ i : A.cover.Index,
          (shortPairGradientWeight cov A j i * g +
            shortPairValueWeight cov A j i * v) := by
      apply Finset.sum_le_sum
      intro i _
      exact norm_shortSupportedPairResidualTransportL_le_weights
        cov A j i hS hST hthin
    _ = (∑ i : A.cover.Index, shortPairGradientWeight cov A j i) * g +
        (∑ i : A.cover.Index, shortPairValueWeight cov A j i) * v := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_mul]

/-- Quantitative norm estimate for the complete finite short commutator
matrix. -/
theorem norm_shortAtlasCommutatorLiftL_le
    [Nonempty M]
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (hS : t₀ < S) (hST : S ≤ T) (hthin : S - t₀ ≤ 1) :
    ‖shortAtlasCommutatorLiftL cov A hS hST‖ ≤
      shortAtlasGradientWeight cov A *
          FiniteParabolicC2AlphaBanach.gradientShortTimeFactor
            (S - t₀) α +
        shortAtlasValueWeight cov A *
          FiniteParabolicC2AlphaBanach.valueShortTimeFactor
            (S - t₀) α := by
  let g := FiniteParabolicC2AlphaBanach.gradientShortTimeFactor (S - t₀) α
  let v := FiniteParabolicC2AlphaBanach.valueShortTimeFactor (S - t₀) α
  have hD : 0 ≤ S - t₀ := sub_nonneg.mpr hS.le
  have hg : 0 ≤ g :=
    FiniteParabolicC2AlphaBanach.gradientShortTimeFactor_nonneg hD
  have hv : 0 ≤ v :=
    FiniteParabolicC2AlphaBanach.valueShortTimeFactor_nonneg hD
  have hC : 0 ≤ shortAtlasGradientWeight cov A * g +
      shortAtlasValueWeight cov A * v :=
    add_nonneg
      (mul_nonneg (shortAtlasGradientWeight_nonneg cov A) hg)
      (mul_nonneg (shortAtlasValueWeight_nonneg cov A) hv)
  unfold shortAtlasCommutatorLiftL
  apply ContinuousLinearMap.norm_pi_le_of_le _ hC
  intro j
  calc
    ‖shortAtlasCommutatorRowL cov A j hS hST‖ ≤
        (∑ i : A.cover.Index, shortPairGradientWeight cov A j i) * g +
          (∑ i : A.cover.Index, shortPairValueWeight cov A j i) * v :=
      norm_shortAtlasCommutatorRowL_le cov A j hS hST hthin
    _ ≤ shortAtlasGradientWeight cov A * g +
        shortAtlasValueWeight cov A * v := by
      gcongr
      · unfold shortAtlasGradientWeight
        simpa using (Finset.single_le_sum
          (s := Finset.univ)
          (f := fun k : A.cover.Index =>
            ∑ i : A.cover.Index, shortPairGradientWeight cov A k i)
          (fun k _ => Finset.sum_nonneg fun i _ =>
            shortPairGradientWeight_nonneg cov A k i)
          (Finset.mem_univ j))
      · unfold shortAtlasValueWeight
        simpa using (Finset.single_le_sum
          (s := Finset.univ)
          (f := fun k : A.cover.Index =>
            ∑ i : A.cover.Index, shortPairValueWeight cov A k i)
          (fun k _ => Finset.sum_nonneg fun i _ =>
            shortPairValueWeight_nonneg cov A k i)
          (Finset.mem_univ j))

/-- A sufficiently short normalized terminal time makes the concrete
commutator matrix a strict contraction. -/
theorem exists_shortTerminal_norm_shortAtlasCommutatorLiftL_lt_one
    [Nonempty M]
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α) :
    ∃ (S : ℝ) (hS : t₀ < S) (hST : S ≤ T),
      ‖shortAtlasCommutatorLiftL cov A hS hST‖ < 1 := by
  let G := shortAtlasGradientWeight cov A
  let V := shortAtlasValueWeight cov A
  have hG : 0 ≤ G := shortAtlasGradientWeight_nonneg cov A
  have hV : 0 ≤ V := shortAtlasValueWeight_nonneg cov A
  let qG : ℝ := (4 * (G + 1))⁻¹
  let qV : ℝ := (4 * (V + 1))⁻¹
  have hqG : 0 < qG := by
    dsimp [qG]
    positivity
  have hqV : 0 < qV := by
    dsimp [qV]
    positivity
  obtain ⟨Dg, hDg, hg⟩ :=
    FiniteParabolicC2AlphaBanach.exists_thickness_gradientShortTimeFactor_le
      A.alpha_pos A.alpha_lt_one hqG
  obtain ⟨Dv, hDv, hv⟩ :=
    FiniteParabolicC2AlphaBanach.exists_thickness_valueShortTimeFactor_le
      A.alpha_pos A.alpha_lt_one hqV
  let m := min (T - t₀) (min Dg (min Dv 1))
  have hm : 0 < m := by
    dsimp [m]
    exact lt_min (sub_pos.mpr A.time_lt)
      (lt_min hDg (lt_min hDv zero_lt_one))
  let D := m / 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hDT : D ≤ T - t₀ := by
    have hmT : m ≤ T - t₀ := min_le_left _ _
    dsimp [D]
    linarith
  have hDDg : D ≤ Dg := by
    have hmm : m ≤ min Dg (min Dv 1) := min_le_right _ _
    have hmDg : m ≤ Dg := hmm.trans (min_le_left _ _)
    dsimp [D]
    linarith
  have hDDv : D ≤ Dv := by
    have hmm : m ≤ min Dg (min Dv 1) := min_le_right _ _
    have hmDv : m ≤ Dv :=
      hmm.trans ((min_le_right _ _).trans (min_le_left _ _))
    dsimp [D]
    linarith
  have hDone : D ≤ 1 := by
    have hmm : m ≤ min Dg (min Dv 1) := min_le_right _ _
    have hmone : m ≤ 1 :=
      hmm.trans ((min_le_right _ _).trans (min_le_right _ _))
    dsimp [D]
    linarith
  let S := t₀ + D
  have hS : t₀ < S := by dsimp [S]; linarith
  have hST : S ≤ T := by dsimp [S]; linarith
  have hthin : S - t₀ ≤ 1 := by dsimp [S]; linarith
  have hgS : FiniteParabolicC2AlphaBanach.gradientShortTimeFactor
      (S - t₀) α ≤ qG := by
    apply hg (S - t₀)
    · linarith
    · dsimp [S]
      linarith
  have hvS : FiniteParabolicC2AlphaBanach.valueShortTimeFactor
      (S - t₀) α ≤ qV := by
    apply hv (S - t₀)
    · linarith
    · dsimp [S]
      linarith
  have hGq : G * qG < (1 : ℝ) / 4 := by
    have hden : 0 < 4 * (G + 1) := by positivity
    change G * (4 * (G + 1))⁻¹ < (1 : ℝ) / 4
    rw [← div_eq_mul_inv, div_lt_iff₀ hden]
    nlinarith
  have hVq : V * qV < (1 : ℝ) / 4 := by
    have hden : 0 < 4 * (V + 1) := by positivity
    change V * (4 * (V + 1))⁻¹ < (1 : ℝ) / 4
    rw [← div_eq_mul_inv, div_lt_iff₀ hden]
    nlinarith
  refine ⟨S, hS, hST, ?_⟩
  calc
    ‖shortAtlasCommutatorLiftL cov A hS hST‖ ≤
        G * FiniteParabolicC2AlphaBanach.gradientShortTimeFactor
              (S - t₀) α +
          V * FiniteParabolicC2AlphaBanach.valueShortTimeFactor
              (S - t₀) α := by
      simpa [G, V] using
        norm_shortAtlasCommutatorLiftL_le cov A hS hST hthin
    _ ≤ G * qG + V * qV :=
      add_le_add
        (mul_le_mul_of_nonneg_left hgS hG)
        (mul_le_mul_of_nonneg_left hvS hV)
    _ < 1 := by nlinarith

/-- The short contraction and its exact physical realization form the
genuine commutator-lift datum used by the Neumann-corrected parametrix. -/
theorem exists_restrictedTerminalAtlas_commutatorLift
    [Nonempty M]
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α) :
    ∃ (S : ℝ) (hS : t₀ < S) (hST : S ≤ T),
      Nonempty (CommutatorLift cov (A.restrictTerminalAtlas cov hS hST)) := by
  obtain ⟨S, hS, hST, hnorm⟩ :=
    exists_shortTerminal_norm_shortAtlasCommutatorLiftL_lt_one cov A
  refine ⟨S, hS, hST, ⟨{
    toContinuousLinearMap := ?_
    realizes := ?_
    norm_lt_one := ?_ }⟩⟩
  · change ((i : A.cover.Index) →
        ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀ S)) →L[ℝ]
      ((i : A.cover.Index) →
        ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀ S))
    exact shortAtlasCommutatorLiftL cov A hS hST
  · intro q t ht x
    exact physicalAtlasSourceSlice_shortAtlasCommutatorLiftL
      cov A hS hST q ht x
  · change ‖shortAtlasCommutatorLiftL cov A hS hST‖ < 1
    exact hnorm

end FiniteTensorHeatParametrixAtlas
end AnalyticPDE
end RicciFlow
