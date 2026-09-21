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

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasCorrection

/-!
# Initial data in the finite tensor-heat atlas

This file upgrades the zero-trace local inverse to the affine Cauchy solver
needed for arbitrary initial data.  An initial tensor is represented by its
finite family of local `C^{2+α}` extensions.  The local equation defect of
that family is corrected by the already constructed zero-trace inverses, so
the resulting family has exactly the requested coordinate forcing and exactly
the same canonical initial trace.
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
  [CompactSpace M] [SigmaCompactSpace M] [I.Boundaryless] [Nonempty M]

variable {d : ℕ} {t₀ T α : ℝ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "W₂" => (Fin d × Fin d → ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)

private theorem norm_add_clm_apply_le
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (y : Y) (L : X →L[ℝ] Y) (x : X) :
    ‖y + L x‖ ≤ ‖y‖ + ‖L‖ * ‖x‖ := by
  exact (norm_add_le _ _).trans (add_le_add_right (L.le_opNorm x) _)

@[reducible] local instance atlasInitialTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedAddCommGroup x
@[reducible] local instance atlasInitialTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedSpace x

/-- The normalized coordinate Cauchy operator in one selected atlas chart. -/
def localCoordinateCauchyL
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) :
    FiniteParabolicC2AlphaBanach E W₂ t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ T) :=
  FiniteParabolicC2AlphaBanach.coordinateCauchyL
    ((A.coefficients (i : M)).principalField A.alpha_pos
      A.alpha_lt_one (A.radius (i : M)))
    ((A.coefficients (i : M)).firstField A.alpha_pos
      A.alpha_lt_one (A.radius (i : M)))
    ((A.coefficients (i : M)).zeroField A.alpha_pos
      A.alpha_lt_one (A.radius (i : M)))

/-- Apply the normalized coordinate Cauchy operator in every atlas chart. -/
def localCoordinateCauchyFamilyL
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α) :
    HigherCoefficientSpace cov A →L[ℝ] SourceSpace cov A :=
  ContinuousLinearMap.pi fun i =>
    (localCoordinateCauchyL cov A i).comp (ContinuousLinearMap.proj i)

@[simp]
theorem localCoordinateCauchyFamilyL_apply
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A) (i : A.cover.Index) :
    localCoordinateCauchyFamilyL cov A u i =
      localCoordinateCauchyL cov A i (u i) := rfl

/-- The chosen zero-trace local inverse is a right inverse in each chart. -/
theorem localCoordinateCauchyL_localInverse
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T)) :
    localCoordinateCauchyL cov A i (A.localInverse (i : M) q) = q := by
  have h := congrArg
    (fun L : ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀ T) →L[ℝ]
        ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀ T) => L q)
    (A.right_inverse (i : M))
  simpa [localCoordinateCauchyL, ContinuousLinearMap.comp_apply] using h

/-- Affine correction of an arbitrary local higher-regularity extension.
The correction has zero trace, so it changes the equation but not the initial
value. -/
def affineLocalSolutionFamily
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (h : HigherCoefficientSpace cov A)
    (q : SourceSpace cov A) : HigherCoefficientSpace cov A :=
  h + localSolutionFamilyL cov A
    (q - localCoordinateCauchyFamilyL cov A h)

/-- The affine atlas family solves every selected coordinate equation. -/
theorem localCoordinateCauchyFamilyL_affineLocalSolutionFamily
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (h : HigherCoefficientSpace cov A)
    (q : SourceSpace cov A) :
    localCoordinateCauchyFamilyL cov A
      (affineLocalSolutionFamily cov A h q) = q := by
  ext i
  simp only [affineLocalSolutionFamily,
    localCoordinateCauchyFamilyL_apply, Pi.add_apply, Pi.sub_apply,
    localSolutionFamilyL_apply, map_add, map_sub]
  rw [A.localCoordinateCauchyL_localInverse cov,
    A.localCoordinateCauchyL_localInverse cov]
  abel

/-- The affine atlas family has exactly the initial trace of the supplied
higher-regularity extension. -/
theorem initialTrace_affineLocalSolutionFamily_apply
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (h : HigherCoefficientSpace cov A)
    (q : SourceSpace cov A) (i : A.cover.Index) :
    FiniteParabolicC2AlphaBanach.initialTraceL
        (X := E) (E := W₂) A.time_lt A.alpha_pos
        (affineLocalSolutionFamily cov A h q i) =
      FiniteParabolicC2AlphaBanach.initialTraceL
        A.time_lt A.alpha_pos (h i) := by
  simp only [affineLocalSolutionFamily, Pi.add_apply, map_add,
    localSolutionFamilyL_apply]
  have hz := A.initialTrace_localSolutionFamilyL_apply cov
    (q - localCoordinateCauchyFamilyL cov A h) i
  change FiniteParabolicC2AlphaBanach.initialTraceL
      A.time_lt A.alpha_pos
      (A.localInverse (i : M)
        ((q - localCoordinateCauchyFamilyL cov A h) i)) = 0 at hz
  rw [hz]
  exact add_zero _

/-- Reconstruct the canonical initial trace of one local higher-coefficient
field as an actual cutoff covariant two-tensor. -/
def localInitialTrace
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α) : ∀ x : M, T₂ x :=
  cutoffLocalTensorOfMatrix (I := I)
    (trivializationAt E TM (i : M)) b (A.cover.partition i)
    (fun y => tensorCoordinateReconstructionEquiv d
      (FiniteParabolicC2AlphaBanach.initialTraceL
        A.time_lt A.alpha_pos u
        (normalizedTensorHeatCoordinate (I := I)
          (i : M) (A.radius (i : M)) y)))

/-- Reconstruct the canonical initial trace of a local higher-coefficient
family as an actual global covariant two-tensor. -/
def atlasInitialTrace
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A) : ∀ x : M, T₂ x :=
  fun x => ∑ i : A.cover.Index, localInitialTrace cov A i (u i) x

/-- Affine correction preserves the reconstructed geometric initial tensor,
not only the separate chart traces. -/
theorem atlasInitialTrace_affineLocalSolutionFamily
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (h : HigherCoefficientSpace cov A)
    (q : SourceSpace cov A) :
    atlasInitialTrace cov A (affineLocalSolutionFamily cov A h q) =
      atlasInitialTrace cov A h := by
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
    (A.initialTrace_affineLocalSolutionFamily_apply cov h q i)

/-- The atlas reconstruction of every zero-trace local solution family has
zero geometric initial tensor. -/
theorem atlasInitialTrace_localSolutionFamilyL
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (q : SourceSpace cov A) :
    atlasInitialTrace cov A (localSolutionFamilyL cov A q) = 0 := by
  funext x
  change (∑ i : A.cover.Index,
    localInitialTrace cov A i (localSolutionFamilyL cov A q i) x) =
      (0 : T₂ x)
  rw [Finset.sum_eq_zero]
  intro i _hi
  unfold localInitialTrace
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simp only [cutoffLocalTensorOfMatrix, smul_apply, smul_eq_mul]
  rw [A.initialTrace_localSolutionFamilyL_apply cov q i]
  change (A.cover.partition i) x *
    localTensorOfMatrix (I := I) (trivializationAt E TM (i : M)) b
      (fun _ => (0 : Fin d → Fin d → ℝ)) x v w = 0
  have hlocal : localTensorOfMatrix (I := I)
      (trivializationAt E TM (i : M)) b
      (fun _ => (0 : Fin d → Fin d → ℝ)) x v w = 0 := by
    simp [localTensorOfMatrix, matrixBilinearCLM]
    by_cases hx : x ∈ (chartAt H (i : M)).source <;> simp [hx]
  rw [hlocal, mul_zero]

/-- Curry one pair-indexed higher coefficient field into the matrix convention
used by tensor reconstruction. -/
def normalizedHigherSolution
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α) :
    FiniteParabolicC2AlphaBanach E (Fin d → Fin d → ℝ) t₀ T α :=
  FiniteParabolicC2AlphaBanach.fiberPostcompL
    (tensorCoordinateReconstructionEquiv d).toContinuousLinearMap u

/-- Normalized cutoff reconstruction converges to the canonical coefficient
trace.  This connects the finite-cylinder Banach trace to the actual tensor
field's `HasInitialTrace` predicate. -/
theorem hasInitialTrace_normalizedHigherSolution
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α) :
    FiniteClassicalTensorHeatField.HasInitialTrace cov
      (normalizedFiniteClassicalTensorHeatField
        (I := I) cov (i : M) (A.radius (i : M)) b
        (A.cover.partition i)
        ((A.cover.partition i).contMDiff.of_le
          (show (2 : WithTop ℕ∞) ≤ ∞ by decide))
        (A.cover.pieces_subset_domain i)
        (A.patch_subset_trivialization (i : M))
        (normalizedHigherSolution u) A.alpha_pos)
      (localInitialTrace cov A i u) := by
  intro x
  let ξ : E := normalizedTensorHeatCoordinate (I := I)
    (i : M) (A.radius (i : M)) x
  let q := FiniteParabolicC2AlphaBanach.valueComponentL u
  let B := (tensorCoordinateReconstructionEquiv d).toContinuousLinearMap
  let S := cutoffLocalTensorSynthesisAt (I := I)
    (trivializationAt E TM (i : M)) b (A.cover.partition i) x
  let g : ℝ → T₂ x := fun t => S (B
    (ParabolicC0AlphaBanach.globalTimeSlice A.alpha_pos
      (ParabolicC0AlphaBanach.finiteSourceExtension
        A.time_lt A.alpha_pos q) t ξ))
  have hg : Continuous g := by
    apply S.continuous.comp
    apply B.continuous.comp
    apply (BoundedContinuousFunction.evalCLM ℝ ξ).continuous.comp
    exact ParabolicC0AlphaBanach.continuous_globalTimeSlice A.alpha_pos
      (ParabolicC0AlphaBanach.finiteSourceExtension
        A.time_lt A.alpha_pos q)
  have hlim : Tendsto g (nhdsWithin t₀ (Ioc t₀ T)) (nhds (g t₀)) :=
    hg.continuousAt.mono_left inf_le_left
  have heq :
      (fun t =>
        (normalizedFiniteClassicalTensorHeatField
          (I := I) cov (i : M) (A.radius (i : M)) b
          (A.cover.partition i)
          ((A.cover.partition i).contMDiff.of_le
            (show (2 : WithTop ℕ∞) ≤ ∞ by decide))
          (A.cover.pieces_subset_domain i)
          (A.patch_subset_trivialization (i : M))
          (normalizedHigherSolution u) A.alpha_pos).toFun t x) =ᶠ[
        nhdsWithin t₀ (Ioc t₀ T)] g := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hz : (t, ξ) ∈ parabolicFiniteCylinder E t₀ T := by
      exact ⟨ht, Set.mem_univ ξ⟩
    change S (FiniteParabolicC2AlphaBanach.value
      (normalizedHigherSolution u) (t, ξ)) = g t
    rw [show FiniteParabolicC2AlphaBanach.value
          (normalizedHigherSolution u) (t, ξ) =
        B (FiniteParabolicC2AlphaBanach.value u (t, ξ)) by
      unfold normalizedHigherSolution
      simpa [B] using
        (FiniteParabolicC2AlphaBanach.value_fiberPostcompL
          (tensorCoordinateReconstructionEquiv d).toContinuousLinearMap
          u (t, ξ) hz)]
    unfold g
    rw [ParabolicC0AlphaBanach.globalTimeSlice_apply,
      ParabolicC0AlphaBanach.eval_finiteSourceExtension_of_mem
        A.time_lt A.alpha_pos q (t, ξ) hz,
      FiniteParabolicC2AlphaBanach.evalCLM_valueComponentL]
  have hg0 : g t₀ = localInitialTrace cov A i u x := by
    unfold g
    rw [ParabolicC0AlphaBanach.globalTimeSlice_apply,
      ParabolicC0AlphaBanach.eval_finiteSourceExtension]
    simp only [ParabolicC0AlphaBanach.finiteSourceExtensionFun,
      Set.projIcc_of_mem A.time_lt.le
        (show t₀ ∈ Icc t₀ T from ⟨le_rfl, A.time_lt.le⟩)]
    change S (B
      (ParabolicC0AlphaBanach.finiteInitialTrace
        A.time_lt A.alpha_pos q ξ)) = localInitialTrace cov A i u x
    rfl
  rw [← hg0]
  exact hlim.congr' heq.symm

/-- Parabolic time rescaling preserves a genuine tensor initial trace. -/
theorem hasInitialTrace_timePushforward
    (cov : CovariantDerivative I E TM)
    {u : FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ T}
    {u₀ : ∀ x : M, T₂ x}
    (r : ℝ) (hr : r ≠ 0)
    (hu : FiniteClassicalTensorHeatField.HasInitialTrace cov u u₀) :
    FiniteClassicalTensorHeatField.HasInitialTrace cov
      (FiniteClassicalTensorHeatField.timePushforward cov u r hr) u₀ := by
  intro x
  apply (hu x).comp
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt
        (FiniteClassicalTensorHeatField.normalizedTime t₀ r) t₀ := by
      unfold FiniteClassicalTensorHeatField.normalizedTime
      fun_prop
    have hc' : Tendsto
        (FiniteClassicalTensorHeatField.normalizedTime t₀ r)
        (nhdsWithin t₀ (Ioc t₀
          (FiniteClassicalTensorHeatField.physicalTerminalTime t₀ T r)))
        (nhds (FiniteClassicalTensorHeatField.normalizedTime t₀ r t₀)) :=
      hc.mono_left inf_le_left
    simpa only [FiniteClassicalTensorHeatField.normalizedTime,
      sub_self, mul_zero, add_zero] using hc'
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact FiniteClassicalTensorHeatField.normalizedTime_mem_Ioc hr ht

/-- Reconstruct any one local higher-coefficient field on physical time and
restrict it to the finite atlas's common horizon. -/
def localFieldOfHigher
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α) :
    FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ A.commonTerminalTime :=
  FiniteClassicalTensorHeatField.restrictTerminal cov
    (physicalFiniteClassicalTensorHeatField
      (I := I) cov (i : M) (A.radius (i : M))
      (ne_of_gt (A.radius_pos (i : M))) b (A.cover.partition i)
      ((A.cover.partition i).contMDiff.of_le
        (show (2 : WithTop ℕ∞) ≤ ∞ by decide))
      (A.cover.pieces_subset_domain i)
      (A.patch_subset_trivialization (i : M))
      (normalizedHigherSolution u) A.alpha_pos)
    A.commonTerminalTime (A.commonTerminalTime_le cov i)

/-- Every physically rescaled local reconstruction has the tensor initial
trace reconstructed from its canonical finite-cylinder coefficient trace. -/
theorem hasInitialTrace_localFieldOfHigher
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α) :
    FiniteClassicalTensorHeatField.HasInitialTrace cov
      (localFieldOfHigher cov A i u) (localInitialTrace cov A i u) := by
  apply FiniteClassicalTensorHeatField.hasInitialTrace_restrictTerminal
  apply hasInitialTrace_timePushforward cov
  exact A.hasInitialTrace_normalizedHigherSolution cov i u

/-- Reconstruct a finite family of arbitrary local higher-coefficient fields
as a genuine global tensor field. -/
def atlasFieldOfHigher
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A) :
    FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ A.commonTerminalTime :=
  FiniteClassicalTensorHeatField.finsetSum cov Finset.univ
    (fun i => localFieldOfHigher cov A i (u i))

@[simp]
theorem atlasFieldOfHigher_toFun
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A) (t : ℝ) (x : M) :
    (atlasFieldOfHigher cov A u).toFun t x =
      ∑ i : A.cover.Index, (localFieldOfHigher cov A i (u i)).toFun t x := rfl

/-- The finite reconstructed field converges to its actual atlas initial
tensor. -/
theorem hasInitialTrace_atlasFieldOfHigher
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A) :
    FiniteClassicalTensorHeatField.HasInitialTrace cov
      (atlasFieldOfHigher cov A u) (atlasInitialTrace cov A u) := by
  have hs := FiniteClassicalTensorHeatField.hasInitialTrace_finsetSum cov
    Finset.univ
    (fun i => localFieldOfHigher cov A i (u i))
    (fun i => localInitialTrace cov A i (u i))
    (fun i _hi => A.hasInitialTrace_localFieldOfHigher cov i (u i))
  change FiniteClassicalTensorHeatField.HasInitialTrace cov
    (FiniteClassicalTensorHeatField.finsetSum cov Finset.univ
      (fun i => localFieldOfHigher cov A i (u i)))
    (fun x => ∑ i : A.cover.Index, localInitialTrace cov A i (u i) x)
  exact hs

/-- The original zero-trace parametrix is the reconstruction of the local
solution family. -/
theorem atlasFieldOfHigher_localSolutionFamilyL
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (q : SourceSpace cov A) :
    atlasFieldOfHigher cov A (localSolutionFamilyL cov A q) =
      A.parametrixField cov q := by
  rfl

/-- The uncorrected atlas parametrix has the genuine zero tensor initial
trace. -/
theorem hasInitialTrace_parametrixField_zero
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (q : SourceSpace cov A) :
    FiniteClassicalTensorHeatField.HasInitialTrace cov
      (A.parametrixField cov q) 0 := by
  rw [← A.atlasFieldOfHigher_localSolutionFamilyL cov q]
  have h := A.hasInitialTrace_atlasFieldOfHigher cov
    (localSolutionFamilyL cov A q)
  rw [A.atlasInitialTrace_localSolutionFamilyL cov q] at h
  exact h

/-- Neumann correction changes only the source and therefore retains the
genuine zero tensor initial trace. -/
theorem hasInitialTrace_correctedParametrixField_zero
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (K : CommutatorLift cov A) (f : SourceSpace cov A) :
    FiniteClassicalTensorHeatField.HasInitialTrace cov
      (A.correctedParametrixField cov K f) 0 :=
  A.hasInitialTrace_parametrixField_zero cov
    (CommutatorLift.correctedSource cov K f)

/-- The affine local Cauchy correction preserves the prescribed actual
geometric initial tensor after finite-atlas reconstruction. -/
theorem hasInitialTrace_affineAtlasField
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (h : HigherCoefficientSpace cov A) (q : SourceSpace cov A) :
    FiniteClassicalTensorHeatField.HasInitialTrace cov
      (atlasFieldOfHigher cov A (affineLocalSolutionFamily cov A h q))
      (atlasInitialTrace cov A h) := by
  have hu := A.hasInitialTrace_atlasFieldOfHigher cov
    (affineLocalSolutionFamily cov A h q)
  rwa [A.atlasInitialTrace_affineLocalSolutionFamily cov h q] at hu

/-- Atlas Schauder estimate for arbitrary initial extensions and forcing. -/
theorem norm_affineLocalSolutionFamily_le
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (h : HigherCoefficientSpace cov A)
    (q : SourceSpace cov A) :
    ‖affineLocalSolutionFamily cov A h q‖ ≤
      ‖h‖ + ‖localSolutionFamilyL cov A‖ *
        ‖q - localCoordinateCauchyFamilyL cov A h‖ := by
  exact norm_add_clm_apply_le h (localSolutionFamilyL cov A)
    (q - localCoordinateCauchyFamilyL cov A h)

end FiniteTensorHeatParametrixAtlas
end AnalyticPDE
end RicciFlow
