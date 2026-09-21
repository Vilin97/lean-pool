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

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasResidual
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasShortTime

/-!
# Neumann correction of the geometric tensor-heat atlas

This file isolates the final forcing-space correction in the finite-atlas
construction. A commutator lift represents the genuine geometric cutoff
residual back in the finite product of coordinate Holder spaces. Once that
lift has norm below one, its Neumann inverse produces an exact solution of
the actual connection heat equation.

The existence and short-time bound for the lift are kept separate: this
module proves the exact algebraic and geometric consequence of that concrete
atlas estimate without replacing the connection Laplacian by a coordinate
surrogate.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology

namespace RicciFlow
namespace AnalyticPDE
namespace FiniteTensorHeatParametrixAtlas

open CovariantDerivative
open LinearParabolicParametrix

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
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

@[reducible] local instance atlasCorrectionTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedAddCommGroup x
@[reducible] local instance atlasCorrectionTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedSpace x
@[reducible] local instance atlasCorrectionThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedAddCommGroup
@[reducible] local instance atlasCorrectionThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedSpace
@[reducible] local instance atlasCorrectionThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedAddCommGroup x
@[reducible] local instance atlasCorrectionThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedSpace x
local instance atlasCorrectionThreeTotalSpaceTopology :
    TopologicalSpace (TotalSpace
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance atlasCorrectionThreeFiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance atlasCorrectionThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂

/-- The finite product of normalized coordinate forcing spaces attached to
an atlas. Its norm is the ordinary finite-product supremum norm. -/
abbrev SourceSpace
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α) :=
  A.cover.Index →
    ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T)

/-- The finite product of local `C^{2+α,1+α/2}` coefficient spaces produced
by the normalized chart inverses.  This is the atlas-level higher norm that
is available before the local fields are reconstructed as a global tensor. -/
abbrev HigherCoefficientSpace
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α) :=
  A.cover.Index → FiniteParabolicC2AlphaBanach E W₂ t₀ T α

/-- Apply every local normalized inverse at once. -/
def localSolutionFamilyL
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α) :
    SourceSpace cov A →L[ℝ] HigherCoefficientSpace cov A :=
  ContinuousLinearMap.pi fun i =>
    (A.localInverse (i : M)).comp (ContinuousLinearMap.proj i)

@[simp]
theorem localSolutionFamilyL_apply
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (q : SourceSpace cov A) (i : A.cover.Index) :
    localSolutionFamilyL cov A q i = A.localInverse (i : M) (q i) := rfl

/-- Every member of the atlas solution family has the canonical zero initial
trace supplied by the local finite-cylinder inverse. -/
theorem initialTrace_localSolutionFamilyL_apply
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (q : SourceSpace cov A) (i : A.cover.Index) :
    FiniteParabolicC2AlphaBanach.initialTraceL
        (X := E) (E := W₂) A.time_lt A.alpha_pos
        (localSolutionFamilyL cov A q i) = 0 := by
  have h := congrArg
    (fun L : ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀ T) →L[ℝ]
        BoundedContinuousFunction E W₂ => L (q i))
    (A.zero_trace (i : M))
  simpa using h

/-- Physical reconstruction is additive in one chart's normalized source. -/
theorem physicalLocalSourceSlice_add
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (q r : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    (t : ℝ) :
    A.physicalLocalSourceSlice cov i (q + r) t =
      A.physicalLocalSourceSlice cov i q t +
        A.physicalLocalSourceSlice cov i r t := by
  unfold physicalLocalSourceSlice
  rw [show
      (fun x p k =>
        (A.radius (i : M))⁻¹ ^ 2 *
          ParabolicC0AlphaBanach.representative (q + r)
            (FiniteClassicalTensorHeatField.normalizedTime
                t₀ (A.radius (i : M)) t,
              normalizedTensorHeatCoordinate
                (I := I) (i : M) (A.radius (i : M)) x) (k, p)) =
        (fun x p k =>
          (A.radius (i : M))⁻¹ ^ 2 *
            ParabolicC0AlphaBanach.representative q
              (FiniteClassicalTensorHeatField.normalizedTime
                  t₀ (A.radius (i : M)) t,
                normalizedTensorHeatCoordinate
                  (I := I) (i : M) (A.radius (i : M)) x) (k, p)) +
          (fun x p k =>
            (A.radius (i : M))⁻¹ ^ 2 *
              ParabolicC0AlphaBanach.representative r
                (FiniteClassicalTensorHeatField.normalizedTime
                    t₀ (A.radius (i : M)) t,
                  normalizedTensorHeatCoordinate
                    (I := I) (i : M) (A.radius (i : M)) x) (k, p)) by
        funext x p k
        simp only [ParabolicC0AlphaBanach.representative_add, Pi.add_apply]
        ring]
  exact cutoffLocalTensorOfMatrix_add
    (I := I) (trivializationAt E TM (i : M)) b
      (A.cover.partition i) _ _

/-- The global physical source reconstruction is linear under addition. -/
theorem physicalAtlasSourceSlice_add
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (q r : SourceSpace cov A) (t : ℝ) (x : M) :
    A.physicalAtlasSourceSlice cov (q + r) t x =
      A.physicalAtlasSourceSlice cov q t x +
        A.physicalAtlasSourceSlice cov r t x := by
  unfold physicalAtlasSourceSlice
  simp_rw [Pi.add_apply, A.physicalLocalSourceSlice_add cov]
  exact Finset.sum_add_distrib

/-- Concrete datum required to feed the geometric cutoff commutator back
into the normalized coordinate forcing space. `realizes` is an equality of
actual covariant two-tensors, not merely an equality of chart coefficients. -/
structure CommutatorLift
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α) where
  toContinuousLinearMap : SourceSpace cov A →L[ℝ] SourceSpace cov A
  realizes : ∀ q : SourceSpace cov A,
    ∀ t : ℝ, t ∈ Ioo t₀ A.commonTerminalTime → ∀ x : M,
      A.physicalAtlasSourceSlice cov (toContinuousLinearMap q) t x =
        A.atlasCommutatorSlice cov q t x
  norm_lt_one : ‖toContinuousLinearMap‖ < 1

namespace CommutatorLift

/-- The forcing corrected by the convergent geometric commutator series. -/
def correctedSource
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (K : CommutatorLift cov A) :
    SourceSpace cov A →L[ℝ] SourceSpace cov A :=
  neumannInverse K.toContinuousLinearMap K.norm_lt_one

/-- The corrected source satisfies `(1-K)g=f`. -/
theorem correctedSource_sub_commutator
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (K : CommutatorLift cov A) (f : SourceSpace cov A) :
    correctedSource cov K f -
        K.toContinuousLinearMap (correctedSource cov K f) = f := by
  have h := congrArg (fun L => L f)
    (oneSub_comp_neumannInverse K.toContinuousLinearMap K.norm_lt_one)
  simpa [correctedSource, mul_apply_eq_comp] using h

/-- The geometric-series bound for the corrected normalized forcing. -/
theorem norm_correctedSource_apply_le
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (K : CommutatorLift cov A) (f : SourceSpace cov A) :
    ‖correctedSource cov K f‖ ≤
      (1 - ‖K.toContinuousLinearMap‖)⁻¹ * ‖f‖ := by
  exact ((correctedSource cov K).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right
      (norm_neumannInverse_le K.toContinuousLinearMap K.norm_lt_one)
      (norm_nonneg f))

end CommutatorLift

/-- The atlas `C^{2+α,1+α/2}` norm of the local normalized solutions used
to reconstruct a tensor field. -/
def atlasSchauderNorm
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (q : SourceSpace cov A) : ℝ :=
  ‖localSolutionFamilyL cov A q‖

/-- The corrected local solution family obeys the Neumann-series Schauder
bound.  The first factor records the finite-atlas local inverse constant. -/
theorem atlasSchauderNorm_correctedSource_le
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (K : CommutatorLift cov A) (f : SourceSpace cov A) :
    atlasSchauderNorm cov A (CommutatorLift.correctedSource cov K f) ≤
      ‖localSolutionFamilyL cov A‖ *
        (1 - ‖K.toContinuousLinearMap‖)⁻¹ * ‖f‖ := by
  calc
    atlasSchauderNorm cov A (CommutatorLift.correctedSource cov K f) ≤
        ‖localSolutionFamilyL cov A‖ *
          ‖CommutatorLift.correctedSource cov K f‖ :=
      (localSolutionFamilyL cov A).le_opNorm
        (CommutatorLift.correctedSource cov K f)
    _ ≤ ‖localSolutionFamilyL cov A‖ *
          ((1 - ‖K.toContinuousLinearMap‖)⁻¹ * ‖f‖) :=
      mul_le_mul_of_nonneg_left
        (CommutatorLift.norm_correctedSource_apply_le cov K f)
        (norm_nonneg (localSolutionFamilyL cov A))
    _ = ‖localSolutionFamilyL cov A‖ *
          (1 - ‖K.toContinuousLinearMap‖)⁻¹ * ‖f‖ := by ring

/-- The finite atlas parametrix evaluated at the Neumann-corrected source. -/
def correctedParametrixField
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (K : CommutatorLift cov A) (f : SourceSpace cov A) :
    FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ A.commonTerminalTime :=
  A.parametrixField cov (CommutatorLift.correctedSource cov K f)

/-- Exact positive-time equation for the corrected geometric parametrix.
The right-hand side is the actual global tensor forcing reconstructed from
the arbitrary atlas Holder datum `f`. -/
theorem correctedParametrixField_tensorHeatOperator
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
    (K : CommutatorLift cov A) (f : SourceSpace cov A)
    (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime) (x : M) :
    (A.correctedParametrixField cov K f).tensorHeatOperator cov t ht x =
      A.physicalAtlasSourceSlice cov f t x := by
  let g : SourceSpace cov A := CommutatorLift.correctedSource cov K f
  have hg : g - K.toContinuousLinearMap g = f :=
    CommutatorLift.correctedSource_sub_commutator cov K f
  have hg' : g = f + K.toContinuousLinearMap g := by
    calc
      g = (g - K.toContinuousLinearMap g) + K.toContinuousLinearMap g := by
        abel
      _ = f + K.toContinuousLinearMap g := by rw [hg]
  calc
    (A.correctedParametrixField cov K f).tensorHeatOperator cov t ht x =
        A.physicalAtlasSourceSlice cov g t x -
          A.atlasCommutatorSlice cov g t x := by
      exact A.parametrixField_tensorHeatOperator_eq_source_sub_commutator
        cov g t ht x
    _ = A.physicalAtlasSourceSlice cov g t x -
          A.physicalAtlasSourceSlice cov (K.toContinuousLinearMap g) t x := by
      rw [K.realizes g t ht x]
    _ = A.physicalAtlasSourceSlice cov
          (f + K.toContinuousLinearMap g) t x -
            A.physicalAtlasSourceSlice cov (K.toContinuousLinearMap g) t x := by
      exact congrArg
        (fun z : T₂ x =>
          z - A.physicalAtlasSourceSlice cov
            (K.toContinuousLinearMap g) t x)
        (congrArg (fun q : SourceSpace cov A =>
          A.physicalAtlasSourceSlice cov q t x) hg')
    _ = A.physicalAtlasSourceSlice cov f t x := by
      rw [A.physicalAtlasSourceSlice_add cov]
      abel

end FiniteTensorHeatParametrixAtlas
end AnalyticPDE
end RicciFlow
