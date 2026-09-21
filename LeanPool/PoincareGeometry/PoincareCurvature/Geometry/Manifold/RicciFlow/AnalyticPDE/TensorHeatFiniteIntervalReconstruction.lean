/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatLocalReconstruction
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatCoefficientLocalization
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatFiniteInterval

/-!
# Finite-cylinder tensor-heat reconstruction on manifold patches

This file connects the finite-cylinder coordinate Banach solution to genuine
covariant two-tensors.  A normalized coordinate slice is proved `C²` on its
radius-adapted manifold patch.  Multiplication by a subordinate smooth cutoff
then produces a global tensor section in the actual connection-Laplacian
domain.

Time rescaling and the finite parametrix sum are kept separate: the results
here concern one normalized positive-time slice and make no false claim of
regularity at the missing initial face.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff

namespace RicciFlow
namespace AnalyticPDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)

variable {d : ℕ} {t₀ T α : ℝ}

/-- Normalized radius-`r` coordinate of a manifold point relative to `p`. -/
def normalizedTensorHeatCoordinate (p : M) (r : ℝ) (x : M) : E :=
  r⁻¹ • ((extChartAt I p) x - (extChartAt I p) p)

/-- Pull one fixed normalized-time slice of a finite-cylinder matrix solution
back along the radius-adapted manifold chart. -/
def normalizedTensorHeatCoefficientSlice
    (p : M) (r : ℝ)
    (u : FiniteParabolicC2AlphaBanach E (Fin d → Fin d → ℝ) t₀ T α)
    (t : ℝ) (x : M) : Fin d → Fin d → ℝ :=
  FiniteParabolicC2AlphaBanach.value u
    (t, normalizedTensorHeatCoordinate (I := I) p r x)

/-- Every positive-time normalized coefficient slice is genuinely `C²` on
the corresponding radius-adapted manifold patch. -/
theorem contMDiffOn_normalizedTensorHeatCoefficientSlice
    (p : M) (r : ℝ)
    (u : FiniteParabolicC2AlphaBanach E (Fin d → Fin d → ℝ) t₀ T α)
    (hα : 0 < α) {t : ℝ} (ht : t ∈ Set.Ioc t₀ T) :
    ContMDiffOn I 𝓘(ℝ, Fin d → Fin d → ℝ) 2
      (normalizedTensorHeatCoefficientSlice (I := I) p r u t)
      (actualLocalTensorHeatPatch (I := I) p r) := by
  have hslice := FiniteParabolicC2AlphaBanach.contDiff_two_space hα u ht
  have haff : ContDiff ℝ 2
      (fun z : E => r⁻¹ • (z - (extChartAt I p) p)) :=
    (contDiff_id.sub contDiff_const).const_smul r⁻¹
  have hmodel : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin d → Fin d → ℝ) 2
      (fun z => FiniteParabolicC2AlphaBanach.value u
        (t, r⁻¹ • (z - (extChartAt I p) p))) :=
    contMDiff_iff_contDiff.mpr (hslice.comp haff)
  apply (hmodel.contMDiffOn (s := Set.univ)).comp
    ((contMDiffOn_extChartAt (I := I) (H := H) (n := 2) (x := p)).mono
      (by
        intro x hx
        simpa [extChartAt] using hx.1))
  intro x hx
  exact Set.mem_univ _

/-- A subordinate cutoff turns a normalized finite-cylinder solution slice
into a genuine global covariant two-tensor in the connection-Laplacian
domain. -/
theorem normalizedTensorHeatSlice_mem_connectionLaplacianDomain
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (p : M) (r : ℝ)
    (b : Module.Basis (Fin d) ℝ E)
    (ψ : M → ℝ)
    (hψ : ContMDiff I 𝓘(ℝ) 2 ψ)
    (hψsupp : tsupport ψ ⊆ actualLocalTensorHeatPatch (I := I) p r)
    (hpatch : actualLocalTensorHeatPatch (I := I) p r ⊆
      (trivializationAt E TM p).baseSet)
    (u : FiniteParabolicC2AlphaBanach E (Fin d → Fin d → ℝ) t₀ T α)
    (hα : 0 < α) {t : ℝ} (ht : t ∈ Set.Ioc t₀ T) :
    cutoffLocalTensorOfMatrix (I := I) (trivializationAt E TM p) b ψ
        (normalizedTensorHeatCoefficientSlice (I := I) p r u t) ∈
      CovariantDerivative.ConnectionLaplacianDomain cov := by
  apply cutoffLocalTensorOfMatrix_mem_connectionLaplacianDomain_of_isOpen
    (I := I) cov p (trivializationAt E TM p) b ψ
    (normalizedTensorHeatCoefficientSlice (I := I) p r u t)
  · exact isOpen_actualLocalTensorHeatPatch (I := I) p r
  · exact hpatch
  · exact hψ
  · exact hψsupp
  · exact contMDiffOn_normalizedTensorHeatCoefficientSlice
      (I := I) p r u hα ht

/-- The time-derivative coefficients of a normalized local solution,
reconstructed as a genuine covariant two-tensor. -/
def normalizedTensorHeatTimeDerivative
    (p : M) (r : ℝ)
    (b : Module.Basis (Fin d) ℝ E) (ψ : M → ℝ)
    (u : FiniteParabolicC2AlphaBanach E (Fin d → Fin d → ℝ) t₀ T α)
    (t : ℝ) : ∀ x : M, T₂ x :=
  cutoffLocalTensorOfMatrix (I := I) (trivializationAt E TM p) b ψ
    (fun x => FiniteParabolicC2AlphaBanach.timeDeriv u
      (t, normalizedTensorHeatCoordinate (I := I) p r x))

/-- Cutoff reconstruction of one normalized finite-cylinder solution is an
honest finite-interval classical tensor field. Its spatial slices use the
actual connection Laplacian, and its temporal witness is obtained by applying
the continuous linear fibre reconstruction to the stored coordinate time
derivative. -/
def normalizedFiniteClassicalTensorHeatField
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (p : M) (r : ℝ)
    (b : Module.Basis (Fin d) ℝ E)
    (ψ : M → ℝ)
    (hψ : ContMDiff I (modelWithCornersSelf ℝ ℝ) 2 ψ)
    (hψsupp : tsupport ψ ⊆ actualLocalTensorHeatPatch (I := I) p r)
    (hpatch : actualLocalTensorHeatPatch (I := I) p r ⊆
      (trivializationAt E TM p).baseSet)
    (u : FiniteParabolicC2AlphaBanach E (Fin d → Fin d → ℝ) t₀ T α)
    (hα : 0 < α) :
    CovariantDerivative.FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ T where
  toFun t := cutoffLocalTensorOfMatrix (I := I)
    (trivializationAt E TM p) b ψ
      (normalizedTensorHeatCoefficientSlice (I := I) p r u t)
  slice_mem t ht := normalizedTensorHeatSlice_mem_connectionLaplacianDomain
    (I := I) cov p r b ψ hψ hψsupp hpatch u hα ht
  timeDerivative := normalizedTensorHeatTimeDerivative (I := I) p r b ψ u
  hasTimeDerivative := by
    intro t ht x v w
    have hu := FiniteParabolicC2AlphaBanach.hasDerivAt_time u ht
      (normalizedTensorHeatCoordinate (I := I) p r x)
    have h := (cutoffLocalTensorEvaluationSynthesisAt
      (I := I) (trivializationAt E TM p) b ψ x v w).hasFDerivAt.comp_hasDerivAt t hu
    simpa [normalizedTensorHeatCoefficientSlice,
      normalizedTensorHeatTimeDerivative, Function.comp_def,
      cutoffLocalTensorEvaluationSynthesisAt_apply,
      cutoffLocalTensorOfMatrix, localTensorOfMatrix] using h

/-- The same reconstructed local field on physical time. Spatial
normalization by r is paired with the inverse-time substitution, so the
physical interval ends at t₀ + r²(T-t₀). -/
def physicalFiniteClassicalTensorHeatField
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (p : M) (r : ℝ) (hr : r ≠ 0)
    (b : Module.Basis (Fin d) ℝ E)
    (ψ : M → ℝ)
    (hψ : ContMDiff I (modelWithCornersSelf ℝ ℝ) 2 ψ)
    (hψsupp : tsupport ψ ⊆ actualLocalTensorHeatPatch (I := I) p r)
    (hpatch : actualLocalTensorHeatPatch (I := I) p r ⊆
      (trivializationAt E TM p).baseSet)
    (u : FiniteParabolicC2AlphaBanach E (Fin d → Fin d → ℝ) t₀ T α)
    (hα : 0 < α) :
    CovariantDerivative.FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀
      (CovariantDerivative.FiniteClassicalTensorHeatField.physicalTerminalTime
        t₀ T r) :=
  CovariantDerivative.FiniteClassicalTensorHeatField.timePushforward cov
    (normalizedFiniteClassicalTensorHeatField
      (I := I) cov p r b ψ hψ hψsupp hpatch u hα) r hr

@[simp] theorem physicalFiniteClassicalTensorHeatField_toFun
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (p : M) (r : ℝ) (hr : r ≠ 0)
    (b : Module.Basis (Fin d) ℝ E)
    (ψ : M → ℝ)
    (hψ : ContMDiff I (modelWithCornersSelf ℝ ℝ) 2 ψ)
    (hψsupp : tsupport ψ ⊆ actualLocalTensorHeatPatch (I := I) p r)
    (hpatch : actualLocalTensorHeatPatch (I := I) p r ⊆
      (trivializationAt E TM p).baseSet)
    (u : FiniteParabolicC2AlphaBanach E (Fin d → Fin d → ℝ) t₀ T α)
    (hα : 0 < α) (t : ℝ) :
    (physicalFiniteClassicalTensorHeatField
      (I := I) cov p r hr b ψ hψ hψsupp hpatch u hα).toFun t =
      cutoffLocalTensorOfMatrix (I := I) (trivializationAt E TM p) b ψ
        (normalizedTensorHeatCoefficientSlice (I := I) p r u
          (CovariantDerivative.FiniteClassicalTensorHeatField.normalizedTime
            t₀ r t)) :=
  rfl

end AnalyticPDE
end RicciFlow
