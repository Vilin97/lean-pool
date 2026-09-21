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

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasAffineCorrection
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasLocalUniqueness

/-!
# Strong finite-atlas well-posedness for tensor heat

The spatial coefficient and transition extensions are kept from a fixed
parent atlas, while the operators here act directly on arbitrary
short-cylinder higher jets.  Composing the higher commutator with the
restricted local solution family is exactly the previously constructed
strict contraction.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Filter Set
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
  [CompactSpace M] [SigmaCompactSpace M] [I.Boundaryless]

variable {d : ℕ} {t₀ S T α : ℝ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)
local notation "W₂" => (Fin d × Fin d → ℝ)
local notation "DW₂" => (E →L[ℝ] W₂)
local notation "D2W₂" => (E →L[ℝ] E →L[ℝ] W₂)

@[reducible] local instance strongFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup DW₂ := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance strongFirstDerivativeNormedSpace :
    NormedSpace ℝ DW₂ := ContinuousLinearMap.toNormedSpace
@[reducible] local instance strongSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup D2W₂ := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance strongSecondDerivativeNormedSpace :
    NormedSpace ℝ D2W₂ := ContinuousLinearMap.toNormedSpace
@[reducible] local instance strongScalarThirdNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedAddCommGroup
@[reducible] local instance strongScalarThirdNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedSpace
@[reducible] local instance strongThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedAddCommGroup x
@[reducible] local instance strongThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedSpace x
local instance strongThreeTotalSpaceTopology :
    TopologicalSpace (TotalSpace
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance strongThreeFiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance strongThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂

/-- Fixed parent commutator coefficients acting directly on an arbitrary
short-cylinder higher jet. -/
def shortHigherCutoffCommutatorResidualL
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) (hST : S ≤ T) :
    FiniteParabolicC2AlphaBanach E W₂ t₀ S α →L[ℝ]
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ S) :=
  FiniteParabolicC2AlphaBanach.lowerOrderL
    (shortCutoffCommutatorFirstField cov A i hST)
    (shortCutoffCommutatorZeroField cov A i hST)

/-- On a partition piece, the fixed parent coefficient expression for an
arbitrary short higher jet is the intrinsic commutator of the restricted
atlas reconstruction. -/
theorem eval_shortHigherCutoffCommutatorResidualL
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
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) (hS : t₀ < S) (hST : S ≤ T)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ S α)
    (s : ℝ) (hs : s ∈ Ioc t₀ S) {x : M}
    (hx : x ∈ (A.cover.pieces i : Set M)) (p k : Fin d) :
    ParabolicC0AlphaBanach.evalCLM
        (s, normalizedTensorHeatCoordinate (I := I)
          (i : M) (A.radius (i : M)) x)
        (by simpa using hs)
        (shortHigherCutoffCommutatorResidualL cov A i hST u) (k, p) =
      connectionLaplacianCutoffCommutator cov (A.cover.partition i)
        (bufferedLocalHigherSlice cov
          (A.restrictTerminalAtlas cov hS hST) i u s) x
        ((trivializationAt E TM (i : M)).localFrame b p x)
        ((trivializationAt E TM (i : M)).localFrame b k x) := by
  let B := A.restrictTerminalAtlas cov hS hST
  let ξ : E := normalizedTensorHeatCoordinate (I := I)
    (i : M) (A.radius (i : M)) x
  let z : E := (extChartAt I (i : M)) x
  let h := bufferedLocalHigherSlice cov B i u s
  let U := FiniteParabolicC2AlphaBanach.value u (s, ξ)
  let Du := finiteAffineFirstDerivativeL (A.radius (i : M))⁻¹
    (FiniteParabolicC2AlphaBanach.spaceDeriv u (s, ξ))
  have hxB : x ∈ (B.cover.pieces i : Set M) := by
    simpa [B] using hx
  have hxPatch := B.cover.pieces_subset_domain i hxB
  have hcoord :=
    connectionLaplacianCutoffCommutator_apply_eq_secondOrderCutoff
      (I := I) cov (i : M) (trivializationAt E TM (i : M)) b
      ((B.cover.partition i).contMDiff.of_le
        (show (2 : WithTop ℕ∞) ≤ ∞ by decide))
      (contMDiff_bufferedLocalHigherSlice cov B i u hs)
      (B.patch_subset_trivialization (i : M) hxPatch) hxPatch.1 p k
  have hpart : B.cover.partition i = A.cover.partition i := rfl
  rw [hpart] at hcoord
  have hDu := (localTensorCoordinateDerivatives_bufferedHigher
    cov B i u s hs hxB).1
  have hu : localTensorCoordinates (I := I) (i : M)
      (trivializationAt E TM (i : M)) b h z = U := by
    have hev := localTensorCoordinates_bufferedHigher_eventuallyEq_normalized
      cov B i u s hs hxB
    have hv := hev.self_of_nhds
    simpa [B, h, z, U, ξ, normalizedTensorHeatCoordinate] using hv
  have hzCore : z ∈ cutoffCommutatorCoordinateCore cov A i :=
    ⟨x, A.piece_subset_bufferedCutoff_tsupport cov i hx, rfl⟩
  have hG := (cutoffCommutatorCoefficientExtensions cov A i).first
    |>.eventuallyEq_original.self_of_nhdsSet z hzCore
  have hD := (cutoffCommutatorCoefficientExtensions cov A i).zero
    |>.eventuallyEq_original.self_of_nhdsSet z hzCore
  have hraw : (extChartAt I (i : M)) (i : M) +
      A.radius (i : M) • ξ = z := by
    dsimp [ξ, z, normalizedTensorHeatCoordinate]
    rw [smul_smul,
      mul_inv_cancel₀ (ne_of_gt (A.radius_pos (i : M))),
      one_smul, add_sub_cancel]
  rw [hcoord]
  change
    _ = (cutoffCommutatorFirstCoefficient cov A i z
          (localTensorCoordinateDerivative (I := I) (i : M)
            (trivializationAt E TM (i : M)) b h z) +
      cutoffCommutatorZeroCoefficient cov A i z
          (localTensorCoordinates (I := I) (i : M)
            (trivializationAt E TM (i : M)) b h z)) (k, p)
  rw [hDu, hu]
  change _ = (cutoffCommutatorFirstCoefficient cov A i z Du +
      cutoffCommutatorZeroCoefficient cov A i z U) (k, p)
  rw [← hG, ← hD]
  rw [shortHigherCutoffCommutatorResidualL,
    FiniteParabolicC2AlphaBanach.evalCLM_lowerOrderL]
  simp only [shortCutoffCommutatorFirstField,
    shortCutoffCommutatorZeroField,
    ParabolicC0AlphaSpace.toFun_restrictL,
    toFun_normalizedCutoffCommutatorFirstField,
    toFun_normalizedCutoffCommutatorZeroField]
  rw [normalizedCutoffCommutatorFirstCoefficient,
    normalizedCutoffCommutatorZeroCoefficient, hraw]
  have hscale : Du = (A.radius (i : M))⁻¹ •
      FiniteParabolicC2AlphaBanach.spaceDeriv u (s, ξ) := by
    dsimp [Du]
    ext v out
    simp [finiteAffineFirstDerivativeL_apply]
  rw [hscale, map_smul]
  rfl

/-- On the fixed buffered support outside the partition piece, the arbitrary
short higher residual vanishes exactly. -/
theorem eval_shortHigherCutoffCommutatorResidualL_eq_zero
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) (hST : S ≤ T)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ S α)
    (s : ℝ) (hs : s ∈ Ioc t₀ S) {x : M}
    (hxBuffer : x ∈ tsupport (A.bufferedCutoff cov i).cutoff)
    (hx : x ∉ (A.cover.pieces i : Set M)) :
    ParabolicC0AlphaBanach.evalCLM
        (s, normalizedTensorHeatCoordinate (I := I)
          (i : M) (A.radius (i : M)) x)
        (by simpa using hs)
        (shortHigherCutoffCommutatorResidualL cov A i hST u) = 0 := by
  let ξ : E := normalizedTensorHeatCoordinate (I := I)
    (i : M) (A.radius (i : M)) x
  let z : E := (extChartAt I (i : M)) x
  have hxPatch : x ∈ actualLocalTensorHeatPatch (I := I)
      (i : M) (A.radius (i : M)) :=
    (A.bufferedCutoff cov i).support_subset hxBuffer
  have hraw : (extChartAt I (i : M)) (i : M) +
      A.radius (i : M) • ξ = z := by
    dsimp [ξ, z, normalizedTensorHeatCoordinate]
    rw [smul_smul,
      mul_inv_cancel₀ (ne_of_gt (A.radius_pos (i : M))),
      one_smul, add_sub_cancel]
  have hzCore : z ∈ cutoffCommutatorCoordinateCore cov A i :=
    ⟨x, hxBuffer, rfl⟩
  have hG := (cutoffCommutatorCoefficientExtensions cov A i).first
    |>.eventuallyEq_original.self_of_nhdsSet z hzCore
  have hD := (cutoffCommutatorCoefficientExtensions cov A i).zero
    |>.eventuallyEq_original.self_of_nhdsSet z hzCore
  have hzero := cutoffCommutatorCoefficients_eq_zero_of_not_mem_piece
    cov A i hxPatch hx
  rw [shortHigherCutoffCommutatorResidualL,
    FiniteParabolicC2AlphaBanach.evalCLM_lowerOrderL]
  simp only [shortCutoffCommutatorFirstField,
    shortCutoffCommutatorZeroField,
    ParabolicC0AlphaSpace.toFun_restrictL,
    toFun_normalizedCutoffCommutatorFirstField,
    toFun_normalizedCutoffCommutatorZeroField]
  change
    normalizedCutoffCommutatorFirstCoefficient cov A i ξ
          (FiniteParabolicC2AlphaBanach.spaceDeriv u (s, ξ)) +
      normalizedCutoffCommutatorZeroCoefficient cov A i ξ
          (FiniteParabolicC2AlphaBanach.value u (s, ξ)) = 0
  rw [normalizedCutoffCommutatorFirstCoefficient,
    normalizedCutoffCommutatorZeroCoefficient, hraw]
  change
    ((A.radius (i : M))⁻¹ •
        (cutoffCommutatorCoefficientExtensions cov A i).first.extension z)
          (FiniteParabolicC2AlphaBanach.spaceDeriv u (s, ξ)) +
      (cutoffCommutatorCoefficientExtensions cov A i).zero.extension z
          (FiniteParabolicC2AlphaBanach.value u (s, ξ)) = 0
  rw [hG, hD, hzero.1, hzero.2]
  simp

/-- Pull an arbitrary short higher residual through the fixed pairwise
space-time transition. -/
def shortHigherPairResidualPullbackL
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) (hS : t₀ < S) (hST : S ≤ T) :
    FiniteParabolicC2AlphaBanach E W₂ t₀ S α →L[ℝ]
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ S) :=
  (ParabolicC0AlphaBanach.precompL
    (X := E) (Y := E) (E := W₂) (α := α)
    (s := (Set.univ : Set (ℝ × E)))
    (t := parabolicFiniteCylinder E t₀ S)
    A.alpha_pos.le (pairSpacetimeLipschitzBound_nonneg cov A j i)
    (Set.mapsTo_univ _ _)
    (fun p _ q _ =>
      parabolicDistance_extendedPairSpacetimeTransition_le cov A j i p q)).comp
    ((ParabolicC0AlphaBanach.finiteSourceExtensionL
      (X := E) (E := W₂) hS A.alpha_pos).comp
      (shortHigherCutoffCommutatorResidualL cov A i hST))

/-- Change the source tensor frame and insert the physical target-radius
scale. -/
def shortHigherPairResidualTransportL
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) (hS : t₀ < S) (hST : S ≤ T) :
    FiniteParabolicC2AlphaBanach E W₂ t₀ S α →L[ℝ]
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ S) :=
  A.radius (j : M) ^ 2 •
    ((ParabolicC0AlphaBanach.mulCoeffL
      (operatorEvaluation W₂ W₂)
      (shortPairFrameCoefficientField cov A j i hST)).comp
        (shortHigherPairResidualPullbackL cov A j i hS hST))

/-- Apply the fixed buffered source mask. -/
def shortHigherSupportedPairResidualTransportL
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) (hS : t₀ < S) (hST : S ≤ T) :
    FiniteParabolicC2AlphaBanach E W₂ t₀ S α →L[ℝ]
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ S) :=
  (ParabolicC0AlphaBanach.mulCoeffL
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (shortPairBufferedCutoffField cov A j i hST)).comp
      (shortHigherPairResidualTransportL cov A j i hS hST)

theorem eval_shortHigherPairResidualTransportL
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) (hS : t₀ < S) (hST : S ≤ T)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ S α)
    (z : ℝ × E) (hz : z ∈ parabolicFiniteCylinder E t₀ S)
    (hsource : extendedPairSpacetimeTransition cov A j i z ∈
      parabolicFiniteCylinder E t₀ S) :
    ParabolicC0AlphaBanach.evalCLM z hz
        (shortHigherPairResidualTransportL cov A j i hS hST u) =
      A.radius (j : M) ^ 2 •
        extendedNormalizedTensorPairFrameChange cov A j i z.2
          (ParabolicC0AlphaBanach.evalCLM
            (extendedPairSpacetimeTransition cov A j i z) hsource
            (shortHigherCutoffCommutatorResidualL cov A i hST u)) := by
  rw [shortHigherPairResidualTransportL]
  rw [smul_apply, map_smul]
  rw [ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_mulCoeffL_apply]
  simp only [shortPairFrameCoefficientField,
    ParabolicC0AlphaSpace.toFun_restrictL,
    toFun_normalizedPairFrameCoefficientField,
    operatorEvaluation_apply]
  rw [shortHigherPairResidualPullbackL, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  rw [ParabolicC0AlphaBanach.evalCLM_precompL_apply]
  rw [ParabolicC0AlphaBanach.finiteSourceExtensionL_apply]
  rw [ParabolicC0AlphaBanach.eval_finiteSourceExtension_of_mem
    hS A.alpha_pos _ _ hsource]

theorem eval_shortHigherSupportedPairResidualTransportL
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) (hS : t₀ < S) (hST : S ≤ T)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ S α)
    (z : ℝ × E) (hz : z ∈ parabolicFiniteCylinder E t₀ S) :
    ParabolicC0AlphaBanach.evalCLM z hz
        (shortHigherSupportedPairResidualTransportL
          cov A j i hS hST u) =
      ParabolicC0AlphaSpace.toFun
          (shortPairBufferedCutoffField cov A j i hST) z •
        ParabolicC0AlphaBanach.evalCLM z hz
          (shortHigherPairResidualTransportL cov A j i hS hST u) := by
  rw [shortHigherSupportedPairResidualTransportL,
    ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_mulCoeffL_apply]
  rfl

/-- The fixed-geometry higher pair operator represents the restricted
atlas's intrinsic commutator at every point of the target partition piece. -/
theorem eval_shortHigherSupportedPairResidualTransportL_at_physical_point
    [Nonempty M]
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
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) (hS : t₀ < S) (hST : S ≤ T)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ S α)
    {t : ℝ}
    (ht : t ∈ Ioo t₀
      (A.restrictTerminalAtlas cov hS hST).commonTerminalTime)
    {x : M} (hxj : x ∈ (A.cover.pieces j : Set M)) :
    let sj := FiniteClassicalTensorHeatField.normalizedTime
      t₀ (A.radius (j : M)) t
    let yj := normalizedTensorHeatCoordinate (I := I)
      (j : M) (A.radius (j : M)) x
    ParabolicC0AlphaBanach.evalCLM (sj, yj)
        (by simpa using
          ((A.restrictTerminalAtlas cov hS hST).normalizedTime_mem_Ioc_of_mem_commonInterval
            cov j ht))
        (shortHigherSupportedPairResidualTransportL
          cov A j i hS hST u) =
      A.radius (j : M) ^ 2 •
        intrinsicTensorPairCoordinates (I := I) b (j : M) x
          (connectionLaplacianCutoffCommutator cov (A.cover.partition i)
            (bufferedLocalHigherSlice cov
              (A.restrictTerminalAtlas cov hS hST) i u
                (FiniteClassicalTensorHeatField.normalizedTime
                  t₀ (A.radius (i : M)) t)) x) := by
  dsimp only
  let B := A.restrictTerminalAtlas cov hS hST
  let sj := FiniteClassicalTensorHeatField.normalizedTime
    t₀ (A.radius (j : M)) t
  let si := FiniteClassicalTensorHeatField.normalizedTime
    t₀ (A.radius (i : M)) t
  let yj := normalizedTensorHeatCoordinate (I := I)
    (j : M) (A.radius (j : M)) x
  let yi := normalizedTensorHeatCoordinate (I := I)
    (i : M) (A.radius (i : M)) x
  have hsj : sj ∈ Ioc t₀ S := by
    simpa [B, sj] using B.normalizedTime_mem_Ioc_of_mem_commonInterval cov j ht
  have hsi : si ∈ Ioc t₀ S := by
    simpa [B, si] using B.normalizedTime_mem_Ioc_of_mem_commonInterval cov i ht
  have hzj : (sj, yj) ∈ parabolicFiniteCylinder E t₀ S := by
    simpa [sj, yj] using hsj
  rw [eval_shortHigherSupportedPairResidualTransportL
    cov A j i hS hST u (sj, yj) hzj]
  simp only [shortPairBufferedCutoffField,
    ParabolicC0AlphaSpace.toFun_restrictL]
  rw [normalizedPairBufferedCutoffField_at_normalizedCoordinate
    cov A j i sj hxj]
  by_cases hxi : x ∈ (A.cover.pieces i : Set M)
  · rw [A.bufferedCutoff_eq_one_of_mem_piece cov i hxi, one_smul]
    have hspace : extendedNormalizedSpatialTransition cov A j i yj = yi :=
      extendedNormalizedSpatialTransition_eq_on_overlap cov A j i hxj hxi
    have htime : normalizedPairTimeTransition cov A j i sj = si :=
      normalizedPairTimeTransition_normalizedTime cov A j i t
    have htransition : extendedPairSpacetimeTransition cov A j i (sj, yj) =
        (si, yi) := by
      simp [extendedPairSpacetimeTransition, htime, hspace]
    have hsource : extendedPairSpacetimeTransition cov A j i (sj, yj) ∈
        parabolicFiniteCylinder E t₀ S := by
      rw [htransition]
      simpa [si, yi] using hsi
    rw [eval_shortHigherPairResidualTransportL
      cov A j i hS hST u (sj, yj) hzj hsource]
    rw [extendedNormalizedTensorPairFrameChange_eq_on_overlap
      cov A j i hxj hxi]
    apply congrArg (fun v : W₂ => A.radius (j : M) ^ 2 • v)
    let Hx : T₂ x := connectionLaplacianCutoffCommutator cov
      (A.cover.partition i)
      (bufferedLocalHigherSlice cov B i u si) x
    apply tensorPairFrameChangeL_eq_intrinsicTensorPairCoordinates
      (I := I) b (i : M) (j : M)
      (A.patch_subset_trivialization (i : M)
        (A.cover.pieces_subset_domain i hxi))
      (A.patch_subset_trivialization (j : M)
        (A.cover.pieces_subset_domain j hxj)) Hx
    intro p k
    have heval := eval_shortHigherCutoffCommutatorResidualL
      cov A i hS hST u si hsi hxi p k
    simpa [B, htransition, si, yi, Hx] using heval
  · have hcomm : connectionLaplacianCutoffCommutator cov
        (A.cover.partition i)
        (bufferedLocalHigherSlice cov B i u si) x = 0 := by
      exact connectionLaplacianCutoffCommutator_eq_zero_of_notMem_tsupport
        (I := I) cov b
        ((A.cover.partition i).contMDiff.of_le
          (show (2 : WithTop ℕ∞) ≤ ∞ by decide))
        (contMDiff_bufferedLocalHigherSlice cov B i u hsi) hxi
    rw [show FiniteClassicalTensorHeatField.normalizedTime
        t₀ (A.radius (i : M)) t = si by rfl, hcomm]
    have hrhs : intrinsicTensorPairCoordinates (I := I) b (j : M) x
        (0 : T₂ x) = 0 := by rfl
    rw [hrhs, smul_zero]
    by_cases hcut : (A.bufferedCutoff cov i).cutoff x = 0
    · rw [hcut, zero_smul]
    · have hxBuffer : x ∈ tsupport (A.bufferedCutoff cov i).cutoff := by
        apply subset_closure
        exact hcut
      have hspace : extendedNormalizedSpatialTransition cov A j i yj = yi :=
        extendedNormalizedSpatialTransition_eq_on_buffered_overlap
          cov A j i hxj hxBuffer
      have htime : normalizedPairTimeTransition cov A j i sj = si :=
        normalizedPairTimeTransition_normalizedTime cov A j i t
      have htransition : extendedPairSpacetimeTransition cov A j i (sj, yj) =
          (si, yi) := by
        simp [extendedPairSpacetimeTransition, htime, hspace]
      have hsource : extendedPairSpacetimeTransition cov A j i (sj, yj) ∈
          parabolicFiniteCylinder E t₀ S := by
        rw [htransition]
        simpa [si, yi] using hsi
      rw [eval_shortHigherPairResidualTransportL
        cov A j i hS hST u (sj, yj) hzj hsource]
      have hres0 := eval_shortHigherCutoffCommutatorResidualL_eq_zero
        cov A i hST u si hsi hxBuffer hxi
      have hres : ParabolicC0AlphaBanach.evalCLM
          (extendedPairSpacetimeTransition cov A j i (sj, yj)) hsource
          (shortHigherCutoffCommutatorResidualL cov A i hST u) = 0 := by
        simpa only [htransition, si, yi] using hres0
      rw [hres]
      simp

/-- One ordered-pair entry of the fixed finite short higher-jet
commutator matrix. -/
def shortHigherAtlasCommutatorEntryL
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) (hS : t₀ < S) (hST : S ≤ T) :
    ((i : A.cover.Index) →
        FiniteParabolicC2AlphaBanach E W₂ t₀ S α) →L[ℝ]
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ S) :=
  (shortHigherSupportedPairResidualTransportL
    cov A j i hS hST).comp (ContinuousLinearMap.proj i)

/-- One target row of the fixed finite short higher-jet commutator
matrix. -/
def shortHigherAtlasCommutatorRowL
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j : A.cover.Index) (hS : t₀ < S) (hST : S ≤ T) :
    ((i : A.cover.Index) →
        FiniteParabolicC2AlphaBanach E W₂ t₀ S α) →L[ℝ]
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ S) :=
  ∑ i : A.cover.Index,
    shortHigherAtlasCommutatorEntryL cov A j i hS hST

/-- The fixed finite short commutator matrix acting on arbitrary higher
jets. -/
def shortHigherAtlasCommutatorLiftL
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (hS : t₀ < S) (hST : S ≤ T) :
    ((i : A.cover.Index) →
        FiniteParabolicC2AlphaBanach E W₂ t₀ S α) →L[ℝ]
      ((i : A.cover.Index) →
        ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀ S)) :=
  ContinuousLinearMap.pi fun j =>
    shortHigherAtlasCommutatorRowL cov A j hS hST

@[simp] theorem shortHigherAtlasCommutatorLiftL_apply
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (hS : t₀ < S) (hST : S ≤ T)
    (u : (i : A.cover.Index) →
      FiniteParabolicC2AlphaBanach E W₂ t₀ S α)
    (j : A.cover.Index) :
    shortHigherAtlasCommutatorLiftL cov A hS hST u j =
      ∑ i : A.cover.Index,
        shortHigherSupportedPairResidualTransportL
          cov A j i hS hST (u i) := by
  unfold shortHigherAtlasCommutatorLiftL
    shortHigherAtlasCommutatorRowL shortHigherAtlasCommutatorEntryL
  rw [ContinuousLinearMap.pi_apply, ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rfl

/-- In target chart `j`, the short higher-jet matrix represents the
complete intrinsic commutator of the restricted atlas. -/
theorem eval_shortHigherAtlasCommutatorLiftL_at_physical_point [Nonempty M]
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
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (hS : t₀ < S) (hST : S ≤ T)
    (u : HigherCoefficientSpace cov
      (A.restrictTerminalAtlas cov hS hST))
    (j : A.cover.Index) {t : ℝ}
    (ht : t ∈ Ioo t₀
      (A.restrictTerminalAtlas cov hS hST).commonTerminalTime)
    {x : M} (hxj : x ∈ (A.cover.pieces j : Set M)) :
    let sj := FiniteClassicalTensorHeatField.normalizedTime
      t₀ (A.radius (j : M)) t
    let yj := normalizedTensorHeatCoordinate (I := I)
      (j : M) (A.radius (j : M)) x
    ParabolicC0AlphaBanach.evalCLM (sj, yj)
        (by simpa using
          ((A.restrictTerminalAtlas cov hS hST).normalizedTime_mem_Ioc_of_mem_commonInterval
            cov j ht))
        (shortHigherAtlasCommutatorLiftL cov A hS hST u j) =
      A.radius (j : M) ^ 2 •
        intrinsicTensorPairCoordinates (I := I) b (j : M) x
          (higherAtlasCommutatorSlice
            cov (A.restrictTerminalAtlas cov hS hST) u t x) := by
  dsimp only
  change (∀ _ : A.cover.Index,
    FiniteParabolicC2AlphaBanach E W₂ t₀ S α) at u
  let B := A.restrictTerminalAtlas cov hS hST
  let sj := FiniteClassicalTensorHeatField.normalizedTime
    t₀ (A.radius (j : M)) t
  let yj := normalizedTensorHeatCoordinate (I := I)
    (j : M) (A.radius (j : M)) x
  have hsj : sj ∈ Ioc t₀ S := by
    simpa [B, sj] using B.normalizedTime_mem_Ioc_of_mem_commonInterval cov j ht
  have hzj : (sj, yj) ∈ parabolicFiniteCylinder E t₀ S := by
    simpa [sj, yj] using hsj
  rw [shortHigherAtlasCommutatorLiftL_apply, map_sum]
  simp_rw [eval_shortHigherSupportedPairResidualTransportL_at_physical_point
    cov A j _ hS hST _ ht hxj]
  rw [← Finset.smul_sum]
  congr 1
  unfold higherAtlasCommutatorSlice intrinsicTensorPairCoordinates
  ext out
  simp only [restrictTerminalAtlas_cover, restrictTerminalAtlas_radius,
    ContinuousLinearMap.sum_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rfl

/-- The fixed short higher-jet matrix realizes the complete intrinsic
commutator after physical reconstruction. -/
theorem physicalAtlasSourceSlice_shortHigherAtlasCommutatorLiftL
    [Nonempty M]
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
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (hS : t₀ < S) (hST : S ≤ T)
    (u : HigherCoefficientSpace cov
      (A.restrictTerminalAtlas cov hS hST))
    {t : ℝ} (ht : t ∈ Ioo t₀
      (A.restrictTerminalAtlas cov hS hST).commonTerminalTime)
    (x : M) :
    (A.restrictTerminalAtlas cov hS hST).physicalAtlasSourceSlice cov
        (shortHigherAtlasCommutatorLiftL cov A hS hST u) t x =
      higherAtlasCommutatorSlice
        cov (A.restrictTerminalAtlas cov hS hST) u t x := by
  let B := A.restrictTerminalAtlas cov hS hST
  change ∑ j : A.cover.Index,
      B.physicalLocalSourceSlice cov j
        (shortHigherAtlasCommutatorLiftL cov A hS hST u j) t x = _
  have hlocal (j : A.cover.Index) :
      B.physicalLocalSourceSlice cov j
          (shortHigherAtlasCommutatorLiftL cov A hS hST u j) t x =
        A.cover.partition j x •
          higherAtlasCommutatorSlice cov B u t x := by
    by_cases hpsi : A.cover.partition j x = 0
    · change A.cover.partition j x • _ = A.cover.partition j x • _
      rw [hpsi]
      ext v w
      simp only [smul_apply, smul_eq_mul, zero_mul]
    · have hxj : x ∈ (A.cover.pieces j : Set M) := subset_closure hpsi
      have hxPatch := A.cover.pieces_subset_domain j hxj
      have hxFrame : x ∈ (trivializationAt E TM (j : M)).baseSet :=
        A.patch_subset_trivialization (j : M) hxPatch
      apply continuousBilinearMap_ext_localFrame
        (I := I) (trivializationAt E TM (j : M)) b hxFrame
      intro p k
      rw [B.physicalLocalSourceSlice_localFrame cov j
        (shortHigherAtlasCommutatorLiftL cov A hS hST u j)
        t hxFrame p k]
      simp only [smul_apply, smul_eq_mul]
      let sj := FiniteClassicalTensorHeatField.normalizedTime
        t₀ (A.radius (j : M)) t
      let yj := normalizedTensorHeatCoordinate (I := I)
        (j : M) (A.radius (j : M)) x
      have hsj : sj ∈ Ioc t₀ S := by
        simpa [B, sj] using B.normalizedTime_mem_Ioc_of_mem_commonInterval cov j ht
      have hzj : (sj, yj) ∈ parabolicFiniteCylinder E t₀ S := by
        simpa [sj, yj] using hsj
      have heval := congrFun
        (eval_shortHigherAtlasCommutatorLiftL_at_physical_point
          cov A hS hST u j ht hxj) (k, p)
      have hrep : ParabolicC0AlphaBanach.representative
            (shortHigherAtlasCommutatorLiftL cov A hS hST u j)
              (sj, yj) (k, p) =
          A.radius (j : M) ^ 2 *
            higherAtlasCommutatorSlice cov B u t x
              ((trivializationAt E TM (j : M)).localFrame b p x)
              ((trivializationAt E TM (j : M)).localFrame b k x) := by
        rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
          (shortHigherAtlasCommutatorLiftL cov A hS hST u j)
            (sj, yj) hzj]
        simpa [sj, yj, intrinsicTensorPairCoordinates,
          smul_eq_mul, B] using heval
      change A.cover.partition j x *
          ((A.radius (j : M))⁻¹ ^ 2 *
            ParabolicC0AlphaBanach.representative
              (shortHigherAtlasCommutatorLiftL cov A hS hST u j)
                (sj, yj) (k, p)) = _
      rw [hrep]
      field_simp [ne_of_gt (A.radius_pos (j : M))]
  rw [Finset.sum_congr rfl (fun j _ => hlocal j)]
  rw [← Finset.sum_smul]
  have hpartition : ∑ j : A.cover.Index, A.cover.partition j x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using
      A.cover.partition.sum_eq_one (Set.mem_univ x)
  rw [hpartition, one_smul]

/-- Apply every restricted local inverse while retaining the fixed parent
cover as the product index. -/
def fixedShortLocalSolutionFamilyL
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (hS : t₀ < S) (hST : S ≤ T) :
    ((i : A.cover.Index) →
        ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀ S)) →L[ℝ]
      ((i : A.cover.Index) →
        FiniteParabolicC2AlphaBanach E W₂ t₀ S α) :=
  ContinuousLinearMap.pi fun i =>
    (shortLocalInverse cov A (i : M) hS hST).comp
      (ContinuousLinearMap.proj i)

@[simp] theorem fixedShortLocalSolutionFamilyL_apply
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (hS : t₀ < S) (hST : S ≤ T)
    (q : (i : A.cover.Index) →
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ S))
    (i : A.cover.Index) :
    fixedShortLocalSolutionFamilyL cov A hS hST q i =
      shortLocalInverse cov A (i : M) hS hST (q i) := rfl

/-- Composing the arbitrary-higher commutator matrix with the restricted
local solution family is exactly the already constructed source-space
commutator matrix. -/
theorem shortHigherAtlasCommutatorLiftL_comp_localSolutionFamilyL
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (hS : t₀ < S) (hST : S ≤ T) :
    (shortHigherAtlasCommutatorLiftL cov A hS hST).comp
        (fixedShortLocalSolutionFamilyL cov A hS hST) =
      shortAtlasCommutatorLiftL cov A hS hST := by
  apply ContinuousLinearMap.ext
  intro q
  funext j
  rw [ContinuousLinearMap.comp_apply,
    shortHigherAtlasCommutatorLiftL_apply]
  unfold shortAtlasCommutatorLiftL shortAtlasCommutatorRowL
    shortAtlasCommutatorEntryL
  rw [ContinuousLinearMap.pi_apply, ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rfl

/-- A commutator lift strong enough for well-posedness: it acts on every
higher atlas jet, realizes that jet's intrinsic cutoff commutator, and
intertwines the local solution family with the strict source contraction. -/
structure StrongCommutatorLift [Nonempty M]
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α) where
  higherMap : HigherCoefficientSpace cov A →L[ℝ] SourceSpace cov A
  sourceLift : CommutatorLift cov A
  realizesHigher : ∀ u : HigherCoefficientSpace cov A,
    ∀ t : ℝ, t ∈ Ioo t₀ A.commonTerminalTime → ∀ x : M,
      A.physicalAtlasSourceSlice cov (higherMap u) t x =
        higherAtlasCommutatorSlice cov A u t x
  intertwines : higherMap.comp (localSolutionFamilyL cov A) =
    sourceLift.toContinuousLinearMap

/-- Equality of every local normalized initial trace. -/
def HasSameAtlasInitialTrace
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u h : HigherCoefficientSpace cov A) : Prop :=
  ∀ i : A.cover.Index,
    FiniteParabolicC2AlphaBanach.initialTraceL
        A.time_lt A.alpha_pos (u i) =
      FiniteParabolicC2AlphaBanach.initialTraceL
        A.time_lt A.alpha_pos (h i)

/-- The intrinsic atlas equation in higher-jet coordinates. -/
def StrongAtlasSolutionEquation [Nonempty M]
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (Hlift : StrongCommutatorLift cov A)
    (h : HigherCoefficientSpace cov A) (f : SourceSpace cov A)
    (u : HigherCoefficientSpace cov A) : Prop :=
  HasSameAtlasInitialTrace cov A u h ∧
    localCoordinateCauchyFamilyL cov A u - Hlift.higherMap u = f

/-- The corrected source for the strong atlas equation. -/
def strongCorrectedSource [Nonempty M]
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (Hlift : StrongCommutatorLift cov A)
    (h : HigherCoefficientSpace cov A) (f : SourceSpace cov A) :
    SourceSpace cov A :=
  CommutatorLift.correctedSource cov Hlift.sourceLift
    (f - localCoordinateCauchyFamilyL cov A h + Hlift.higherMap h)

/-- The higher atlas family obtained from the strong correction. -/
def strongSolutionFamily [Nonempty M]
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (Hlift : StrongCommutatorLift cov A)
    (h : HigherCoefficientSpace cov A) (f : SourceSpace cov A) :
    HigherCoefficientSpace cov A :=
  h + localSolutionFamilyL cov A (strongCorrectedSource cov Hlift h f)

/-- The strong corrected family satisfies the prescribed trace and the
exact atlas equation. -/
theorem strongSolutionFamily_solves
    [Nonempty M]
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (Hlift : StrongCommutatorLift cov A)
    (h : HigherCoefficientSpace cov A) (f : SourceSpace cov A) :
    StrongAtlasSolutionEquation cov Hlift h f
      (strongSolutionFamily cov Hlift h f) := by
  let g := strongCorrectedSource cov Hlift h f
  constructor
  · intro i
    simp only [strongSolutionFamily, Pi.add_apply, map_add]
    rw [A.initialTrace_localSolutionFamilyL_apply cov g i, add_zero]
  · have hg := CommutatorLift.correctedSource_sub_commutator
      cov Hlift.sourceLift
        (f - localCoordinateCauchyFamilyL cov A h + Hlift.higherMap h)
    have hinter := congrArg (fun L => L g) Hlift.intertwines
    change localCoordinateCauchyFamilyL cov A
          (h + localSolutionFamilyL cov A g) -
        Hlift.higherMap (h + localSolutionFamilyL cov A g) = f
    rw [map_add, map_add]
    have hright : localCoordinateCauchyFamilyL cov A
        (localSolutionFamilyL cov A g) = g := by
      ext i
      exact A.localCoordinateCauchyL_localInverse cov i (g i)
    rw [hright]
    change Hlift.higherMap (localSolutionFamilyL cov A g) =
      Hlift.sourceLift.toContinuousLinearMap g at hinter
    rw [hinter]
    have hg' : g - Hlift.sourceLift.toContinuousLinearMap g =
        f - localCoordinateCauchyFamilyL cov A h + Hlift.higherMap h := by
      simpa [g, strongCorrectedSource] using hg
    calc
      localCoordinateCauchyFamilyL cov A h + g -
          (Hlift.higherMap h +
            Hlift.sourceLift.toContinuousLinearMap g) =
          localCoordinateCauchyFamilyL cov A h +
            (g - Hlift.sourceLift.toContinuousLinearMap g) -
              Hlift.higherMap h := by abel
      _ = localCoordinateCauchyFamilyL cov A h +
            (f - localCoordinateCauchyFamilyL cov A h +
              Hlift.higherMap h) - Hlift.higherMap h := by rw [hg']
      _ = f := by abel

/-- A strict continuous-linear contraction has no nonzero fixed point. -/
theorem eq_zero_of_strictContraction_fixedPoint
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : X →L[ℝ] X) (hK : ‖K‖ < 1) (x : X) (hx : K x = x) :
    x = 0 := by
  by_contra hne
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hne
  have hle : ‖x‖ ≤ ‖K‖ * ‖x‖ := by
    have h := K.le_opNorm x
    rw [hx] at h
    exact h
  nlinarith [norm_nonneg K]

/-- Local zero-trace uniqueness turns any zero-trace atlas family into the
local solution family applied to its coordinate Cauchy source. -/
theorem eq_localSolutionFamily_of_zero_trace
    [Nonempty M]
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (hunique : HasLocalZeroTraceUniqueness cov A)
    (u : HigherCoefficientSpace cov A)
    (hu0 : ∀ i : A.cover.Index,
      FiniteParabolicC2AlphaBanach.initialTraceL
        A.time_lt A.alpha_pos (u i) = 0) :
    u = localSolutionFamilyL cov A
      (localCoordinateCauchyFamilyL cov A u) := by
  funext i
  let w := u i - A.localInverse (i : M)
    (localCoordinateCauchyFamilyL cov A u i)
  have hwC : localCoordinateCauchyL cov A i w = 0 := by
    dsimp [w]
    rw [map_sub, A.localCoordinateCauchyL_localInverse cov]
    exact sub_self _
  have hw0 : FiniteParabolicC2AlphaBanach.initialTraceL
      A.time_lt A.alpha_pos w = 0 := by
    change FiniteParabolicC2AlphaBanach.initialTraceL
      A.time_lt A.alpha_pos
        (u i - A.localInverse (i : M)
          (localCoordinateCauchyFamilyL cov A u i)) = 0
    rw [map_sub, hu0 i]
    have hz := A.initialTrace_localSolutionFamilyL_apply cov
      (localCoordinateCauchyFamilyL cov A u) i
    simp only [localSolutionFamilyL_apply] at hz
    rw [hz, sub_zero]
  have hw : w = 0 := hunique (i : M) w hwC hw0
  change u i = A.localInverse (i : M)
    (localCoordinateCauchyFamilyL cov A u i)
  exact sub_eq_zero.mp hw

/-- The strong atlas equation has at most one higher-regularity solution. -/
theorem strongAtlasSolutionEquation_unique
    [Nonempty M]
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (hunique : HasLocalZeroTraceUniqueness cov A)
    (Hlift : StrongCommutatorLift cov A)
    (h : HigherCoefficientSpace cov A) (f : SourceSpace cov A)
    {u v : HigherCoefficientSpace cov A}
    (hu : StrongAtlasSolutionEquation cov Hlift h f u)
    (hv : StrongAtlasSolutionEquation cov Hlift h f v) :
    u = v := by
  let w := u - v
  have hw0 : ∀ i : A.cover.Index,
      FiniteParabolicC2AlphaBanach.initialTraceL
        A.time_lt A.alpha_pos (w i) = 0 := by
    intro i
    change FiniteParabolicC2AlphaBanach.initialTraceL
      A.time_lt A.alpha_pos (u i - v i) = 0
    rw [map_sub, hu.1 i, hv.1 i, sub_self]
  have hwEq : localCoordinateCauchyFamilyL cov A w -
      Hlift.higherMap w = 0 := by
    calc
      localCoordinateCauchyFamilyL cov A w - Hlift.higherMap w =
          (localCoordinateCauchyFamilyL cov A u - Hlift.higherMap u) -
            (localCoordinateCauchyFamilyL cov A v - Hlift.higherMap v) := by
        dsimp [w]
        rw [map_sub, map_sub]
        abel
      _ = 0 := by rw [hu.2, hv.2, sub_self]
  have hrep := eq_localSolutionFamily_of_zero_trace cov A hunique w hw0
  let q := localCoordinateCauchyFamilyL cov A w
  have hinter := congrArg (fun L => L q) Hlift.intertwines
  have hH : Hlift.higherMap w =
      Hlift.sourceLift.toContinuousLinearMap q := by
    rw [hrep]
    change Hlift.higherMap (localSolutionFamilyL cov A q) = _
    simpa only [ContinuousLinearMap.comp_apply] using hinter
  have hCeq : localCoordinateCauchyFamilyL cov A w =
      Hlift.higherMap w := sub_eq_zero.mp hwEq
  have hfixed : Hlift.sourceLift.toContinuousLinearMap q = q := by
    calc
      Hlift.sourceLift.toContinuousLinearMap q = Hlift.higherMap w := hH.symm
      _ = localCoordinateCauchyFamilyL cov A w := hCeq.symm
      _ = q := rfl
  have hq0 : q = 0 := eq_zero_of_strictContraction_fixedPoint
    Hlift.sourceLift.toContinuousLinearMap
      Hlift.sourceLift.norm_lt_one q hfixed
  have hw : w = 0 := by
    rw [hrep]
    change localSolutionFamilyL cov A q = 0
    rw [hq0, map_zero]
  exact sub_eq_zero.mp hw

/-- Existence and uniqueness for the strong atlas equation. -/
theorem existsUnique_strongAtlasSolutionEquation
    [Nonempty M]
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (hunique : HasLocalZeroTraceUniqueness cov A)
    (Hlift : StrongCommutatorLift cov A)
    (h : HigherCoefficientSpace cov A) (f : SourceSpace cov A) :
    ∃! u : HigherCoefficientSpace cov A,
      StrongAtlasSolutionEquation cov Hlift h f u := by
  refine ⟨strongSolutionFamily cov Hlift h f,
    strongSolutionFamily_solves cov Hlift h f, ?_⟩
  intro u hu
  exact strongAtlasSolutionEquation_unique
    cov hunique Hlift h f hu (strongSolutionFamily_solves cov Hlift h f)

/-- Equality of all local coefficient traces gives equality of the actual
tensor reconstructed from those traces. -/
theorem atlasInitialTrace_eq_of_hasSameAtlasInitialTrace
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    {u h : HigherCoefficientSpace cov A}
    (htrace : HasSameAtlasInitialTrace cov A u h) :
    atlasInitialTrace cov A u = atlasInitialTrace cov A h := by
  funext x
  unfold atlasInitialTrace
  apply Finset.sum_congr rfl
  intro i _hi
  unfold localInitialTrace
  apply congrFun
  apply congrArg (cutoffLocalTensorOfMatrix (I := I)
    (trivializationAt E TM (i : M)) b (A.cover.partition i))
  funext y
  apply congrArg (tensorCoordinateReconstructionEquiv d)
  exact congrArg
    (fun F : BoundedContinuousFunction E W₂ =>
      F (normalizedTensorHeatCoordinate (I := I)
        (i : M) (A.radius (i : M)) y))
    (htrace i)

/-- Every solution of the strong atlas equation has the prescribed genuine
geometric initial tensor. -/
theorem hasInitialTrace_atlasFieldOfHigher_of_strongAtlasSolutionEquation
    [Nonempty M]
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (Hlift : StrongCommutatorLift cov A)
    (h : HigherCoefficientSpace cov A) (f : SourceSpace cov A)
    (u : HigherCoefficientSpace cov A)
    (hu : StrongAtlasSolutionEquation cov Hlift h f u) :
    FiniteClassicalTensorHeatField.HasInitialTrace cov
      (atlasFieldOfHigher cov A u) (atlasInitialTrace cov A h) := by
  have hu0 := A.hasInitialTrace_atlasFieldOfHigher cov u
  rw [A.atlasInitialTrace_eq_of_hasSameAtlasInitialTrace cov hu.1] at hu0
  exact hu0

/-- Every solution of the strong atlas equation solves the actual intrinsic
connection heat equation with the physical source reconstructed from `f`. -/
theorem atlasFieldOfHigher_tensorHeatOperator_eq_of_strongAtlasSolutionEquation
    [Nonempty M]
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
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (Hlift : StrongCommutatorLift cov A)
    (h : HigherCoefficientSpace cov A) (f : SourceSpace cov A)
    (u : HigherCoefficientSpace cov A)
    (hu : StrongAtlasSolutionEquation cov Hlift h f u)
    (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime) (x : M) :
    (atlasFieldOfHigher cov A u).tensorHeatOperator cov t ht x =
      A.physicalAtlasSourceSlice cov f t x := by
  have hC : localCoordinateCauchyFamilyL cov A u =
      f + Hlift.higherMap u := (sub_eq_iff_eq_add).mp hu.2
  rw [atlasFieldOfHigher_tensorHeatOperator_eq_source_sub_commutator
    cov A u t ht x, hC, A.physicalAtlasSourceSlice_add cov,
    Hlift.realizesHigher u t ht x]
  abel

/-- A higher atlas family is a classical solution when it satisfies the
strong coordinate equation and its reconstructed tensor has the prescribed
geometric trace and intrinsic source equation. -/
def StrongAtlasClassicalSolution
    [Nonempty M]
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
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (Hlift : StrongCommutatorLift cov A)
    (h : HigherCoefficientSpace cov A) (f : SourceSpace cov A)
    (u : HigherCoefficientSpace cov A) : Prop :=
  StrongAtlasSolutionEquation cov Hlift h f u ∧
    FiniteClassicalTensorHeatField.HasInitialTrace cov
      (atlasFieldOfHigher cov A u) (atlasInitialTrace cov A h) ∧
    ∀ (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime) (x : M),
      (atlasFieldOfHigher cov A u).tensorHeatOperator cov t ht x =
        A.physicalAtlasSourceSlice cov f t x

/-- The canonical corrected family is a genuine classical solution. -/
theorem strongSolutionFamily_isClassicalSolution
    [Nonempty M]
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
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (Hlift : StrongCommutatorLift cov A)
    (h : HigherCoefficientSpace cov A) (f : SourceSpace cov A) :
    StrongAtlasClassicalSolution cov Hlift h f
      (strongSolutionFamily cov Hlift h f) := by
  have hsolves := strongSolutionFamily_solves cov Hlift h f
  refine ⟨hsolves,
    hasInitialTrace_atlasFieldOfHigher_of_strongAtlasSolutionEquation
      cov Hlift h f _ hsolves, ?_⟩
  intro t ht x
  exact atlasFieldOfHigher_tensorHeatOperator_eq_of_strongAtlasSolutionEquation
    cov Hlift h f _ hsolves t ht x

/-- Existence and uniqueness in the genuine classical finite-atlas
`C^{2+α,1+α/2}` solution class. -/
theorem existsUnique_strongAtlasClassicalSolution
    [Nonempty M]
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
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (hunique : HasLocalZeroTraceUniqueness cov A)
    (Hlift : StrongCommutatorLift cov A)
    (h : HigherCoefficientSpace cov A) (f : SourceSpace cov A) :
    ∃! u : HigherCoefficientSpace cov A,
      StrongAtlasClassicalSolution cov Hlift h f u := by
  refine ⟨strongSolutionFamily cov Hlift h f,
    strongSolutionFamily_isClassicalSolution cov Hlift h f, ?_⟩
  intro u hu
  exact strongAtlasSolutionEquation_unique cov hunique Hlift h f
    hu.1 (strongSolutionFamily_solves cov Hlift h f)

/-- Quantitative finite-atlas Schauder estimate for the canonical strong
solution. -/
theorem norm_strongSolutionFamily_le
    [Nonempty M]
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (Hlift : StrongCommutatorLift cov A)
    (h : HigherCoefficientSpace cov A) (f : SourceSpace cov A) :
    ‖strongSolutionFamily cov Hlift h f‖ ≤
      ‖h‖ + ‖localSolutionFamilyL cov A‖ *
        (1 - ‖Hlift.sourceLift.toContinuousLinearMap‖)⁻¹ *
          ‖f - localCoordinateCauchyFamilyL cov A h +
            Hlift.higherMap h‖ := by
  let g : SourceSpace cov A := strongCorrectedSource cov Hlift h f
  have hbase : ‖h + localSolutionFamilyL cov A g‖ ≤
      ‖h‖ + ‖localSolutionFamilyL cov A‖ * ‖g‖ := by
    calc
      ‖h + localSolutionFamilyL cov A g‖ ≤
          ‖h‖ + ‖localSolutionFamilyL cov A g‖ := norm_add_le _ _
      _ ≤ ‖h‖ + ‖localSolutionFamilyL cov A‖ * ‖g‖ :=
        add_le_add_right ((localSolutionFamilyL cov A).le_opNorm g) _
  have hg : ‖g‖ ≤
      (1 - ‖Hlift.sourceLift.toContinuousLinearMap‖)⁻¹ *
        ‖f - localCoordinateCauchyFamilyL cov A h +
          Hlift.higherMap h‖ := by
    simpa [g, strongCorrectedSource] using
      (CommutatorLift.norm_correctedSource_apply_le cov Hlift.sourceLift
        (f - localCoordinateCauchyFamilyL cov A h + Hlift.higherMap h))
  change ‖h + localSolutionFamilyL cov A g‖ ≤ _
  calc
    ‖h + localSolutionFamilyL cov A g‖ ≤
        ‖h‖ + ‖localSolutionFamilyL cov A‖ * ‖g‖ := hbase
    _ ≤ ‖h‖ + ‖localSolutionFamilyL cov A‖ *
        ((1 - ‖Hlift.sourceLift.toContinuousLinearMap‖)⁻¹ *
          ‖f - localCoordinateCauchyFamilyL cov A h +
            Hlift.higherMap h‖) := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left hg
          (norm_nonneg (localSolutionFamilyL cov A))) _
    _ = ‖h‖ + ‖localSolutionFamilyL cov A‖ *
        (1 - ‖Hlift.sourceLift.toContinuousLinearMap‖)⁻¹ *
          ‖f - localCoordinateCauchyFamilyL cov A h +
            Hlift.higherMap h‖ := by ring

/-- A single sufficiently short restriction carries the arbitrary-higher
commutator realization and the same strict contraction used by the
parametrix. -/
theorem exists_restrictedTerminalAtlas_strongCommutatorLift
    [Nonempty M]
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
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α) :
    ∃ (S : ℝ) (hS : t₀ < S) (hST : S ≤ T),
      Nonempty (StrongCommutatorLift cov
        (A.restrictTerminalAtlas cov hS hST)) := by
  obtain ⟨S, hS, hST, hnorm⟩ :=
    exists_shortTerminal_norm_shortAtlasCommutatorLiftL_lt_one cov A
  let B := A.restrictTerminalAtlas cov hS hST
  let K : CommutatorLift cov B := {
    toContinuousLinearMap := by
      change ((i : A.cover.Index) →
          ParabolicC0AlphaBanach E W₂ α
            (parabolicFiniteCylinder E t₀ S)) →L[ℝ]
        ((i : A.cover.Index) →
          ParabolicC0AlphaBanach E W₂ α
            (parabolicFiniteCylinder E t₀ S))
      exact shortAtlasCommutatorLiftL cov A hS hST
    realizes := by
      intro q t ht x
      exact physicalAtlasSourceSlice_shortAtlasCommutatorLiftL
        cov A hS hST q ht x
    norm_lt_one := by
      change ‖shortAtlasCommutatorLiftL cov A hS hST‖ < 1
      exact hnorm }
  refine ⟨S, hS, hST, ⟨{
    higherMap := ?_
    sourceLift := K
    realizesHigher := ?_
    intertwines := ?_ }⟩⟩
  · change ((i : A.cover.Index) →
        FiniteParabolicC2AlphaBanach E W₂ t₀ S α) →L[ℝ]
      ((i : A.cover.Index) →
        ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀ S))
    exact shortHigherAtlasCommutatorLiftL cov A hS hST
  · intro u t ht x
    exact physicalAtlasSourceSlice_shortHigherAtlasCommutatorLiftL
      cov A hS hST u ht x
  · change (shortHigherAtlasCommutatorLiftL cov A hS hST).comp
        (fixedShortLocalSolutionFamilyL cov A hS hST) =
      shortAtlasCommutatorLiftL cov A hS hST
    exact shortHigherAtlasCommutatorLiftL_comp_localSolutionFamilyL
      cov A hS hST

end FiniteTensorHeatParametrixAtlas
end AnalyticPDE
end RicciFlow
