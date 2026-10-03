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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasCommutatorLift
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasRestriction

/-!
# Short-cylinder tensor-heat commutator lift

The spatial extensions and transition fields are fixed once on a parent
atlas.  Only their time domains and the local inverses are restricted.  This
keeps every geometric multiplier uniformly fixed while the lower-order
zero-trace factor tends to zero with the cylinder thickness.
-/

@[expose] public section

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

@[reducible] local instance shortLiftFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup DW₂ := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance shortLiftFirstDerivativeNormedSpace :
    NormedSpace ℝ DW₂ := ContinuousLinearMap.toNormedSpace
@[reducible] local instance shortLiftSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup D2W₂ := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance shortLiftSecondDerivativeNormedSpace :
    NormedSpace ℝ D2W₂ := ContinuousLinearMap.toNormedSpace
@[reducible] local instance shortLiftScalarThirdNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedAddCommGroup
@[reducible] local instance shortLiftScalarThirdNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedSpace
@[reducible] local instance shortLiftThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedAddCommGroup x
@[reducible] local instance shortLiftThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedSpace x
local instance shortLiftThreeTotalSpaceTopology :
    TopologicalSpace (TotalSpace
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance shortLiftThreeFiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance shortLiftThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂

/-- The parent first-order commutator coefficient restricted to the short
cylinder. -/
def shortCutoffCommutatorFirstField
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
    FiniteFirstCoefficientSpace (X := E) (W := W₂)
      (t₀ := t₀) (T := S) (α := α) :=
  ParabolicC0AlphaSpace.restrictL
    (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST)
    (normalizedCutoffCommutatorFirstField cov A i)

/-- The parent zeroth-order commutator coefficient restricted to the short
cylinder. -/
def shortCutoffCommutatorZeroField
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
    FiniteZeroCoefficientSpace (X := E) (W := W₂)
      (t₀ := t₀) (T := S) (α := α) :=
  ParabolicC0AlphaSpace.restrictL
    (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST)
    (normalizedCutoffCommutatorZeroField cov A i)

/-- The genuine lower-order cutoff residual using the shortened local
inverse but the fixed parent geometric coefficients. -/
def shortCutoffCommutatorLocalResidualL
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
    (i : A.cover.Index) (hS : t₀ < S) (hST : S ≤ T) :
    ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ S) →L[ℝ]
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ S) :=
  (FiniteParabolicC2AlphaBanach.lowerOrderL
    (shortCutoffCommutatorFirstField cov A i hST)
    (shortCutoffCommutatorZeroField cov A i hST)).comp
      (shortLocalInverse cov A (i : M) hS hST)

/-- Restriction of the fixed target-frame multiplier. -/
def shortPairFrameCoefficientField
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) (hST : S ≤ T) :
    ParabolicC0AlphaSpace E (W₂ →L[ℝ] W₂) α
      (parabolicFiniteCylinder E t₀ S) :=
  ParabolicC0AlphaSpace.restrictL
    (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST)
    (normalizedPairFrameCoefficientField cov A j i)

/-- Restriction of the fixed source-support mask. -/
def shortPairBufferedCutoffField
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (j i : A.cover.Index) (hST : S ≤ T) :
    ParabolicC0AlphaSpace E ℝ α
      (parabolicFiniteCylinder E t₀ S) :=
  ParabolicC0AlphaSpace.restrictL
    (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST)
    (normalizedPairBufferedCutoffField cov A j i)

/-- Pull a short-cylinder local residual through the fixed global pairwise
space-time transition. -/
def shortPairResidualPullbackL
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
    ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ S) →L[ℝ]
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
      (shortCutoffCommutatorLocalResidualL cov A i hS hST))

/-- Fixed-frame pairwise transport on the short cylinder, before applying
the source support mask. -/
def shortPairResidualTransportL
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
    ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ S) →L[ℝ]
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ S) :=
  (A.radius (j : M) ^ 2 •
    ((ParabolicC0AlphaBanach.mulCoeffL
      (operatorEvaluation W₂ W₂)
      (shortPairFrameCoefficientField cov A j i hST)).comp
        (shortPairResidualPullbackL cov A j i hS hST)))

/-- Fixed-geometry pairwise transport on the short cylinder. -/
def shortSupportedPairResidualTransportL
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
    ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ S) →L[ℝ]
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ S) :=
  (ParabolicC0AlphaBanach.mulCoeffL
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (shortPairBufferedCutoffField cov A j i hST)).comp
      (shortPairResidualTransportL cov A j i hS hST)

/-- One ordered-pair entry of the fixed finite short commutator matrix. -/
def shortAtlasCommutatorEntryL
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
        ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀ S)) →L[ℝ]
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ S) :=
  (shortSupportedPairResidualTransportL cov A j i hS hST).comp
    (ContinuousLinearMap.proj i)

/-- One target row of the fixed finite short commutator matrix. -/
def shortAtlasCommutatorRowL
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
        ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀ S)) →L[ℝ]
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ S) :=
  ∑ i : A.cover.Index, shortAtlasCommutatorEntryL cov A j i hS hST

/-- The fixed finite matrix on the short product source space. -/
def shortAtlasCommutatorLiftL
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
        ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀ S)) →L[ℝ]
      ((i : A.cover.Index) →
        ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀ S)) :=
  ContinuousLinearMap.pi fun j => shortAtlasCommutatorRowL cov A j hS hST

/-- The restricted atlas solution has the same point value as the fixed
parent solution fed by the canonical short-to-long extension. -/
theorem value_normalizedLocalSolution_restrictTerminalAtlas
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) (hS : t₀ < S) (hST : S ≤ T)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ S))
    (z : ℝ × E) (hz : z ∈ parabolicFiniteCylinder E t₀ S) :
    FiniteParabolicC2AlphaBanach.value
        ((A.restrictTerminalAtlas cov hS hST).normalizedLocalSolution cov i q) z =
      FiniteParabolicC2AlphaBanach.value
        (A.normalizedLocalSolution cov i
          (ParabolicC0AlphaBanach.extendTerminalL hS hST A.alpha_pos q)) z := by
  unfold normalizedLocalSolution
  rw [FiniteParabolicC2AlphaBanach.value_fiberPostcompL _ _ z hz,
    FiniteParabolicC2AlphaBanach.value_fiberPostcompL _ _ z
      (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST hz)]
  change
    (tensorCoordinateReconstructionEquiv d).toContinuousLinearMap
        (FiniteParabolicC2AlphaBanach.value
          (FiniteParabolicC2AlphaBanach.restrictTerminal hST
            (A.localInverse (i : M)
              (ParabolicC0AlphaBanach.extendTerminalL hS hST A.alpha_pos q))) z) = _
  rw [FiniteParabolicC2AlphaBanach.value_restrictTerminal hST _ hz]

/-- On a partition piece, the buffered short-atlas reconstruction and the
fixed parent reconstruction agree on a whole neighborhood.  Thus changing
the noncanonical buffer chosen by `Classical.choice` does not change any
germ-local differential expression used by the commutator. -/
theorem bufferedLocalSolutionSlice_restrict_eventuallyEq
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) (hS : t₀ < S) (hST : S ≤ T)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ S))
    {s : ℝ} (hs : s ∈ Ioc t₀ S) {x : M}
    (hx : x ∈ (A.cover.pieces i : Set M)) :
    ∀ᶠ y in nhds x,
      (A.restrictTerminalAtlas cov hS hST).bufferedLocalSolutionSlice
          cov i q s y =
        A.bufferedLocalSolutionSlice cov i
          (ParabolicC0AlphaBanach.extendTerminalL hS hST A.alpha_pos q) s y := by
  let B := A.restrictTerminalAtlas cov hS hST
  have hχB : ∀ᶠ y in nhds x, (B.bufferedCutoff cov i).cutoff y = 1 :=
    (B.bufferedCutoff cov i).one_nhds.filter_mono
      (nhds_le_nhdsSet hx)
  have hχA : ∀ᶠ y in nhds x, (A.bufferedCutoff cov i).cutoff y = 1 :=
    (A.bufferedCutoff cov i).one_nhds.filter_mono
      (nhds_le_nhdsSet hx)
  filter_upwards [hχB, hχA] with y hyB hyA
  unfold bufferedLocalSolutionSlice cutoffLocalTensorOfMatrix
  rw [hyB, hyA, one_smul, one_smul]
  unfold localTensorOfMatrix
  split_ifs
  · congr 1
    apply congrArg (matrixBilinearCLM b)
    simpa [normalizedTensorHeatCoefficientSlice] using
      A.value_normalizedLocalSolution_restrictTerminalAtlas
        cov i hS hST q
          (s, normalizedTensorHeatCoordinate (I := I)
            (i : M) (A.radius (i : M)) y) (by simpa using hs)
  · rfl

/-- Evaluation of the fixed-coefficient short residual agrees with the
parent residual applied to the canonical terminal extension. -/
theorem eval_shortCutoffCommutatorLocalResidualL_eq_parent
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
    (i : A.cover.Index) (hS : t₀ < S) (hST : S ≤ T)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ S))
    (z : ℝ × E) (hz : z ∈ parabolicFiniteCylinder E t₀ S) :
    ParabolicC0AlphaBanach.evalCLM z hz
        (shortCutoffCommutatorLocalResidualL cov A i hS hST q) =
      ParabolicC0AlphaBanach.evalCLM z
        (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST hz)
        (normalizedCutoffCommutatorLocalResidualL cov A i
          (ParabolicC0AlphaBanach.extendTerminalL
            hS hST A.alpha_pos q)) := by
  rw [shortCutoffCommutatorLocalResidualL,
    normalizedCutoffCommutatorLocalResidualL,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,
    FiniteParabolicC2AlphaBanach.evalCLM_lowerOrderL,
    FiniteParabolicC2AlphaBanach.evalCLM_lowerOrderL]
  simp only [shortCutoffCommutatorFirstField,
    shortCutoffCommutatorZeroField,
    ParabolicC0AlphaSpace.toFun_restrictL,
    shortLocalInverse,
    ContinuousLinearMap.comp_apply]
  change
    (ParabolicC0AlphaSpace.toFun
        (normalizedCutoffCommutatorFirstField cov A i) z)
          (FiniteParabolicC2AlphaBanach.spaceDeriv
            (FiniteParabolicC2AlphaBanach.restrictTerminal hST
              (A.localInverse (i : M)
                (ParabolicC0AlphaBanach.extendTerminalL
                  hS hST A.alpha_pos q))) z) +
      (ParabolicC0AlphaSpace.toFun
        (normalizedCutoffCommutatorZeroField cov A i) z)
          (FiniteParabolicC2AlphaBanach.value
            (FiniteParabolicC2AlphaBanach.restrictTerminal hST
              (A.localInverse (i : M)
                (ParabolicC0AlphaBanach.extendTerminalL
                  hS hST A.alpha_pos q))) z) = _
  rw [FiniteParabolicC2AlphaBanach.spaceDeriv_restrictTerminal hST _ hz,
    FiniteParabolicC2AlphaBanach.value_restrictTerminal hST _ hz]

/-- Evaluation formula for the fixed-geometry pair transport on a short
cylinder. -/
theorem eval_shortPairResidualTransportL
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
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ S))
    (z : ℝ × E) (hz : z ∈ parabolicFiniteCylinder E t₀ S)
    (hsource : extendedPairSpacetimeTransition cov A j i z ∈
      parabolicFiniteCylinder E t₀ S) :
    ParabolicC0AlphaBanach.evalCLM z hz
        (shortPairResidualTransportL cov A j i hS hST q) =
      A.radius (j : M) ^ 2 •
        extendedNormalizedTensorPairFrameChange cov A j i z.2
          (ParabolicC0AlphaBanach.evalCLM
            (extendedPairSpacetimeTransition cov A j i z) hsource
            (shortCutoffCommutatorLocalResidualL cov A i hS hST q)) := by
  rw [shortPairResidualTransportL]
  rw [ContinuousLinearMap.smul_apply, map_smul]
  rw [ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_mulCoeffL_apply]
  simp only [shortPairFrameCoefficientField,
    ParabolicC0AlphaSpace.toFun_restrictL,
    toFun_normalizedPairFrameCoefficientField,
    operatorEvaluation_apply]
  rw [shortPairResidualPullbackL, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  rw [ParabolicC0AlphaBanach.evalCLM_precompL_apply]
  rw [ParabolicC0AlphaBanach.finiteSourceExtensionL_apply]
  rw [ParabolicC0AlphaBanach.eval_finiteSourceExtension_of_mem
    hS A.alpha_pos _ _ hsource]

/-- Evaluation formula after applying the fixed source-support mask. -/
theorem eval_shortSupportedPairResidualTransportL
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
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ S))
    (z : ℝ × E) (hz : z ∈ parabolicFiniteCylinder E t₀ S) :
    ParabolicC0AlphaBanach.evalCLM z hz
        (shortSupportedPairResidualTransportL cov A j i hS hST q) =
      ParabolicC0AlphaSpace.toFun
          (shortPairBufferedCutoffField cov A j i hST) z •
        ParabolicC0AlphaBanach.evalCLM z hz
          (shortPairResidualTransportL cov A j i hS hST q) := by
  rw [shortSupportedPairResidualTransportL,
    ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_mulCoeffL_apply]
  rfl

/-- The intrinsic cutoff commutator depends only on the germ of the tensor
field. -/
theorem connectionLaplacianCutoffCommutator_congr_of_eventuallyEq
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
    (b : Module.Basis (Fin d) ℝ E) {g : M → ℝ}
    {h h' : ∀ x : M, T₂ x}
    (hg : ContMDiff I 𝓘(ℝ) 2 g)
    (hh : ContMDiff I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun x => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) x (h x)))
    (hh' : ContMDiff I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun x => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) x (h' x)))
    {x : M} (heq : ∀ᶠ y in nhds x, h y = h' y) :
    connectionLaplacianCutoffCommutator cov g h x =
      connectionLaplacianCutoffCommutator cov g h' x := by
  let e := trivializationAt E TM x
  let z := (extChartAt I x) x
  have hxFrame : x ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hxChart : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  have hzTarget : z ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxChart
  have hzRange : z ∈ Set.range I :=
    extChartAt_target_subset_range x hzTarget
  have hsymm : Tendsto (extChartAt I x).symm (nhds z) (nhds x) := by
    have ht := continuousAt_extChartAt_symm' hxChart
    change Tendsto (extChartAt I x).symm
      (nhds ((extChartAt I x) x))
      (nhds ((extChartAt I x).symm ((extChartAt I x) x))) at ht
    rw [(extChartAt I x).left_inv hxChart] at ht
    exact ht
  have heqPull : ∀ᶠ w in nhds z,
      h ((extChartAt I x).symm w) = h' ((extChartAt I x).symm w) :=
    hsymm.eventually heq
  have heqx : h x = h' x := heq.self_of_nhds
  have heqCoord : localTensorCoordinates (I := I) x e b h =ᶠ[nhds z]
      localTensorCoordinates (I := I) x e b h' := by
    filter_upwards [heqPull] with w hw
    funext out
    unfold localTensorCoordinates localTwoTensorComponentInChart
      writtenInExtChartAt
    simp only [Function.comp_apply]
    unfold localTwoTensorComponent
    rw [heqx, hw]
  have hvalue : localTensorCoordinates (I := I) x e b h z =
      localTensorCoordinates (I := I) x e b h' z :=
    heqCoord.self_of_nhds
  have hderiv : localTensorCoordinateDerivative (I := I) x e b h z =
      localTensorCoordinateDerivative (I := I) x e b h' z := by
    exact (heqCoord.filter_mono inf_le_left).fderivWithin_eq_of_mem hzRange
  apply continuousBilinearMap_ext_localFrame (I := I) e b hxFrame
  intro p q
  rw [connectionLaplacianCutoffCommutator_apply_eq_secondOrderCutoff
      cov x e b hg hh hxFrame hxChart p q,
    connectionLaplacianCutoffCommutator_apply_eq_secondOrderCutoff
      cov x e b hg hh' hxFrame hxChart p q]
  rw [hderiv, hvalue]

/-- On a partition piece, the fixed-coefficient short residual is exactly
the intrinsic commutator of the restricted atlas. -/
theorem eval_shortCutoffCommutatorLocalResidualL
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
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ S))
    (s : ℝ) (hs : s ∈ Ioc t₀ S) {x : M}
    (hx : x ∈ (A.cover.pieces i : Set M)) (p k : Fin d) :
    ParabolicC0AlphaBanach.evalCLM
        (s, normalizedTensorHeatCoordinate (I := I)
          (i : M) (A.radius (i : M)) x)
        (by simpa using hs)
        (shortCutoffCommutatorLocalResidualL cov A i hS hST q) (k, p) =
      connectionLaplacianCutoffCommutator cov (A.cover.partition i)
        ((A.restrictTerminalAtlas cov hS hST).bufferedLocalSolutionSlice
          cov i q s) x
        ((trivializationAt E TM (i : M)).localFrame b p x)
        ((trivializationAt E TM (i : M)).localFrame b k x) := by
  let z := (s, normalizedTensorHeatCoordinate (I := I)
    (i : M) (A.radius (i : M)) x)
  have hzs : z ∈ parabolicFiniteCylinder E t₀ S := by
    simpa [z] using hs
  have hsT : s ∈ Ioc t₀ T := ⟨hs.1, hs.2.trans hST⟩
  have hBA := A.bufferedLocalSolutionSlice_restrict_eventuallyEq
    cov i hS hST q hs hx
  have hAB : ∀ᶠ y in nhds x,
      A.bufferedLocalSolutionSlice cov i
          (ParabolicC0AlphaBanach.extendTerminalL hS hST A.alpha_pos q) s y =
        (A.restrictTerminalAtlas cov hS hST).bufferedLocalSolutionSlice
          cov i q s y := hBA.mono (fun _ hy => hy.symm)
  have hcomm := connectionLaplacianCutoffCommutator_congr_of_eventuallyEq
    (I := I) (x := x) cov b
    ((A.cover.partition i).contMDiff.of_le
      (show (2 : WithTop ℕ∞) ≤ ∞ by decide))
    (A.contMDiff_bufferedLocalSolutionSlice cov i
      (ParabolicC0AlphaBanach.extendTerminalL hS hST A.alpha_pos q) hsT)
    ((A.restrictTerminalAtlas cov hS hST).contMDiff_bufferedLocalSolutionSlice
      cov i q hs) hAB
  calc
    ParabolicC0AlphaBanach.evalCLM z hzs
        (shortCutoffCommutatorLocalResidualL cov A i hS hST q) (k, p) =
        connectionLaplacianCutoffCommutator cov (A.cover.partition i)
          (A.bufferedLocalSolutionSlice cov i
            (ParabolicC0AlphaBanach.extendTerminalL
              hS hST A.alpha_pos q) s) x
          ((trivializationAt E TM (i : M)).localFrame b p x)
          ((trivializationAt E TM (i : M)).localFrame b k x) := by
      rw [A.eval_shortCutoffCommutatorLocalResidualL_eq_parent
        cov i hS hST q z hzs]
      exact A.eval_normalizedCutoffCommutatorLocalResidualL
        cov i (ParabolicC0AlphaBanach.extendTerminalL
          hS hST A.alpha_pos q) s hsT hx p k
    _ = _ := congrArg (fun Hx : T₂ x =>
      Hx ((trivializationAt E TM (i : M)).localFrame b p x)
        ((trivializationAt E TM (i : M)).localFrame b k x)) hcomm

/-- The supported short pair operator represents the restricted atlas's
intrinsic commutator at every point of the target partition piece. -/
theorem eval_shortSupportedPairResidualTransportL_at_physical_point
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
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ S))
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
        (shortSupportedPairResidualTransportL cov A j i hS hST q) =
      A.radius (j : M) ^ 2 •
        intrinsicTensorPairCoordinates (I := I) b (j : M) x
          (connectionLaplacianCutoffCommutator cov (A.cover.partition i)
            ((A.restrictTerminalAtlas cov hS hST).bufferedLocalSolutionSlice
              cov i q
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
  rw [eval_shortSupportedPairResidualTransportL
    cov A j i hS hST q (sj, yj) hzj]
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
    rw [eval_shortPairResidualTransportL
      cov A j i hS hST q (sj, yj) hzj hsource]
    rw [extendedNormalizedTensorPairFrameChange_eq_on_overlap
      cov A j i hxj hxi]
    apply congrArg (fun v : W₂ => A.radius (j : M) ^ 2 • v)
    let Hx : T₂ x := connectionLaplacianCutoffCommutator cov
      (A.cover.partition i)
      ((A.restrictTerminalAtlas cov hS hST).bufferedLocalSolutionSlice
        cov i q si) x
    apply tensorPairFrameChangeL_eq_intrinsicTensorPairCoordinates
      (I := I) b (i : M) (j : M)
      (A.patch_subset_trivialization (i : M)
        (A.cover.pieces_subset_domain i hxi))
      (A.patch_subset_trivialization (j : M)
        (A.cover.pieces_subset_domain j hxj)) Hx
    intro p k
    have heval := A.eval_shortCutoffCommutatorLocalResidualL
      cov i hS hST q si hsi hxi p k
    simpa [htransition, si, yi, Hx] using heval
  · have hcomm : connectionLaplacianCutoffCommutator cov
        (A.cover.partition i)
        ((A.restrictTerminalAtlas cov hS hST).bufferedLocalSolutionSlice
          cov i q si) x = 0 :=
      connectionLaplacianCutoffCommutator_eq_zero_of_notMem_tsupport
        (I := I) cov b
        ((A.cover.partition i).contMDiff.of_le
          (show (2 : WithTop ℕ∞) ≤ ∞ by decide))
        ((A.restrictTerminalAtlas cov hS hST).contMDiff_bufferedLocalSolutionSlice
          cov i q hsi) hxi
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
      rw [eval_shortPairResidualTransportL
        cov A j i hS hST q (sj, yj) hzj hsource]
      have hresParent := A.eval_normalizedCutoffCommutatorLocalResidualL_eq_zero
        cov i (ParabolicC0AlphaBanach.extendTerminalL hS hST A.alpha_pos q)
          si ⟨hsi.1, hsi.2.trans hST⟩ hxBuffer hxi
      have hresEq := A.eval_shortCutoffCommutatorLocalResidualL_eq_parent
        cov i hS hST q (si, yi) (by simpa [si, yi] using hsi)
      have hres : ParabolicC0AlphaBanach.evalCLM
          (extendedPairSpacetimeTransition cov A j i (sj, yj)) hsource
          (shortCutoffCommutatorLocalResidualL cov A i hS hST q) = 0 := by
        simpa only [htransition] using hresEq.trans hresParent
      rw [hres]
      simp

@[simp] theorem shortAtlasCommutatorLiftL_apply
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
    (q : SourceSpace cov (A.restrictTerminalAtlas cov hS hST))
    (j : A.cover.Index) :
    shortAtlasCommutatorLiftL cov A hS hST q j =
      ∑ i : A.cover.Index,
        shortSupportedPairResidualTransportL cov A j i hS hST (q i) := by
  change (∀ _ : A.cover.Index,
    ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ S)) at q
  unfold shortAtlasCommutatorLiftL shortAtlasCommutatorRowL
    shortAtlasCommutatorEntryL
  rw [ContinuousLinearMap.pi_apply, ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

/-- In target chart `j`, the short finite matrix represents the complete
intrinsic commutator of the restricted atlas. -/
theorem eval_shortAtlasCommutatorLiftL_at_physical_point [Nonempty M]
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
    (q : SourceSpace cov (A.restrictTerminalAtlas cov hS hST))
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
        (shortAtlasCommutatorLiftL cov A hS hST q j) =
      A.radius (j : M) ^ 2 •
        intrinsicTensorPairCoordinates (I := I) b (j : M) x
          ((A.restrictTerminalAtlas cov hS hST).atlasCommutatorSlice
            cov q t x) := by
  dsimp only
  let B := A.restrictTerminalAtlas cov hS hST
  let sj := FiniteClassicalTensorHeatField.normalizedTime
    t₀ (A.radius (j : M)) t
  let yj := normalizedTensorHeatCoordinate (I := I)
    (j : M) (A.radius (j : M)) x
  have hsj : sj ∈ Ioc t₀ S := by
    simpa [B, sj] using B.normalizedTime_mem_Ioc_of_mem_commonInterval cov j ht
  have hzj : (sj, yj) ∈ parabolicFiniteCylinder E t₀ S := by
    simpa [sj, yj] using hsj
  rw [shortAtlasCommutatorLiftL_apply]
  rw [map_sum]
  simp_rw [eval_shortSupportedPairResidualTransportL_at_physical_point
    cov A j _ hS hST _ ht hxj]
  rw [← Finset.smul_sum]
  congr 1
  unfold atlasCommutatorSlice intrinsicTensorPairCoordinates
  ext out
  simp only [restrictTerminalAtlas_cover, restrictTerminalAtlas_radius,
    ContinuousLinearMap.sum_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

/-- One short target chart reconstructs its partition function times the
complete intrinsic commutator. -/
theorem physicalLocalSourceSlice_shortAtlasCommutatorLiftL [Nonempty M]
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
    (q : SourceSpace cov (A.restrictTerminalAtlas cov hS hST))
    (j : A.cover.Index) {t : ℝ}
    (ht : t ∈ Ioo t₀
      (A.restrictTerminalAtlas cov hS hST).commonTerminalTime)
    (x : M) :
    (A.restrictTerminalAtlas cov hS hST).physicalLocalSourceSlice cov j
        (shortAtlasCommutatorLiftL cov A hS hST q j) t x =
      A.cover.partition j x •
        (A.restrictTerminalAtlas cov hS hST).atlasCommutatorSlice
          cov q t x := by
  let B := A.restrictTerminalAtlas cov hS hST
  by_cases hψ : A.cover.partition j x = 0
  · change A.cover.partition j x • _ = A.cover.partition j x • _
    rw [hψ]
    ext v w
    simp only [smul_apply, smul_eq_mul, zero_mul]
  · have hxSupport : x ∈ Function.support (A.cover.partition j) := hψ
    have hxj : x ∈ (A.cover.pieces j : Set M) := subset_closure hxSupport
    have hxPatch := A.cover.pieces_subset_domain j hxj
    have hxFrame : x ∈ (trivializationAt E TM (j : M)).baseSet :=
      A.patch_subset_trivialization (j : M) hxPatch
    apply continuousBilinearMap_ext_localFrame
      (I := I) (trivializationAt E TM (j : M)) b hxFrame
    intro p k
    rw [B.physicalLocalSourceSlice_localFrame cov j
      (shortAtlasCommutatorLiftL cov A hS hST q j) t hxFrame p k]
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
      (eval_shortAtlasCommutatorLiftL_at_physical_point
        cov A hS hST q j ht hxj) (k, p)
    have hrep : ParabolicC0AlphaBanach.representative
          (shortAtlasCommutatorLiftL cov A hS hST q j) (sj, yj) (k, p) =
        A.radius (j : M) ^ 2 *
          B.atlasCommutatorSlice cov q t x
            ((trivializationAt E TM (j : M)).localFrame b p x)
            ((trivializationAt E TM (j : M)).localFrame b k x) := by
      rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
        (shortAtlasCommutatorLiftL cov A hS hST q j) (sj, yj) hzj]
      simpa [sj, yj, intrinsicTensorPairCoordinates, smul_eq_mul, B] using heval
    change A.cover.partition j x *
        ((A.radius (j : M))⁻¹ ^ 2 *
          ParabolicC0AlphaBanach.representative
            (shortAtlasCommutatorLiftL cov A hS hST q j) (sj, yj) (k, p)) = _
    rw [hrep]
    field_simp [ne_of_gt (A.radius_pos (j : M))]
    simp only [B]

/-- The short finite matrix realizes the intrinsic commutator exactly. -/
theorem physicalAtlasSourceSlice_shortAtlasCommutatorLiftL [Nonempty M]
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
    (q : SourceSpace cov (A.restrictTerminalAtlas cov hS hST))
    {t : ℝ} (ht : t ∈ Ioo t₀
      (A.restrictTerminalAtlas cov hS hST).commonTerminalTime)
    (x : M) :
    (A.restrictTerminalAtlas cov hS hST).physicalAtlasSourceSlice cov
        (shortAtlasCommutatorLiftL cov A hS hST q) t x =
      (A.restrictTerminalAtlas cov hS hST).atlasCommutatorSlice cov q t x := by
  change ∑ j : A.cover.Index,
      (A.restrictTerminalAtlas cov hS hST).physicalLocalSourceSlice cov j
        (shortAtlasCommutatorLiftL cov A hS hST q j) t x = _
  rw [Finset.sum_congr rfl (fun j _ =>
    physicalLocalSourceSlice_shortAtlasCommutatorLiftL
      cov A hS hST q j ht x)]
  rw [← Finset.sum_smul]
  have hpartition : ∑ j : A.cover.Index, A.cover.partition j x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using
      A.cover.partition.sum_eq_one (Set.mem_univ x)
  rw [hpartition, one_smul]

end FiniteTensorHeatParametrixAtlas
end AnalyticPDE
end RicciFlow
