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

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatLocalInverse
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteInitialTrace
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.AffineCauchyCorrection
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.SpatialInitialExtension

/-!
# Canonical zero trace of the corrected local tensor-heat solver

The corrected local parametrix was already accompanied by an explicit
closed-time value path.  Uniqueness of the endpoint completion identifies
that path with the canonical bounded initial trace of the higher parabolic
Banach element.  Consequently the Neumann-corrected local right inverse lands
in the closed zero-trace subspace.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff Topology

namespace RicciFlow
namespace AnalyticPDE

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

section LocalTrace

variable (p : M)
  (e : Trivialization E
    (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
  [MemTrivializationAtlas e]
  (b : Module.Basis (Fin d) ℝ E) {x : M}
  (hxFrame : x ∈ e.baseSet)
  (hxChart : x ∈ (extChartAt I p).source)
  {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
  (P : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α →L[ℝ]
    ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (parabolicFiniteCylinder E t₀ T))
  (hsmall : ‖frozenTensorHeatPerturbationL
    (I := I) p e b x hxChart hT hα hα1 P‖ < 1)

/-- Every value produced by the corrected local solver has zero canonical
initial trace. -/
@[simp]
theorem initialTraceL_localTensorHeatSolutionL_apply
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (parabolicFiniteCylinder E t₀ T)) :
    FiniteParabolicC2AlphaBanach.initialTraceL hT hα
      (localTensorHeatSolutionL
        (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall q) = 0 := by
  change ParabolicC0AlphaBanach.finiteInitialTrace hT hα
    (FiniteParabolicC2AlphaBanach.valueComponentL
      (localTensorHeatSolutionL
        (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall q)) = 0
  rw [ParabolicC0AlphaBanach.finiteInitialTrace_eq_of_continuous
    hT hα _
    (localTensorHeatSolutionValuePathIcc
      (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall q)
    (localTensorHeatSolutionValuePathIcc
      (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall q).continuous]
  · exact localTensorHeatSolutionValuePathIcc_initial
      (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall q
  · intro t
    ext y ij
    let τ : ↥(Set.Ioc t₀ T) := ⟨(t : ℝ), t.2, t.1.2.2⟩
    calc
      localTensorHeatSolutionValuePathIcc
          (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall q
          (t : ↥(Set.Icc t₀ T)) y ij =
        FiniteParabolicC2AlphaBanach.value
          (frozenTensorHeatFiniteZeroInitialInverseL
            (I := I) p x hxChart d hT hα hα1
            (localTensorHeatCorrectedSourceL
              (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall q))
          (t, y) ij := by
            exact congrFun
              (localTensorHeatSolutionValuePathIcc_eq_frozenInverse
                (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall q τ y) ij
      _ = FiniteParabolicC2AlphaBanach.value
          (localTensorHeatSolutionL
            (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall q)
          (t, y) ij := by
            rw [localTensorHeatSolutionL_eq_frozen_comp_correctedSourceL
              (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall]
            rfl
      _ = ParabolicC0AlphaBanach.evalCLM ((t : ℝ), y)
          (ParabolicC0AlphaBanach.positiveTimeInIcc_mem_parabolicFiniteCylinder t y)
          (FiniteParabolicC2AlphaBanach.valueComponentL
            (localTensorHeatSolutionL
              (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall q)) ij := by
            rw [FiniteParabolicC2AlphaBanach.evalCLM_valueComponentL]
      _ = ParabolicC0AlphaBanach.finiteTimeSlice hα
          (FiniteParabolicC2AlphaBanach.valueComponentL
            (localTensorHeatSolutionL
              (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall q)) t y ij := rfl

/-- Operator form: initial trace annihilates the corrected local right
inverse. -/
theorem initialTraceL_comp_localTensorHeatSolutionL :
    (FiniteParabolicC2AlphaBanach.initialTraceL
      (X := E) (E := Fin d × Fin d → ℝ) hT hα).comp
        (localTensorHeatSolutionL
          (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall) = 0 := by
  apply ContinuousLinearMap.ext
  intro q
  exact initialTraceL_localTensorHeatSolutionL_apply
    (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall q

/-- The corrected local right inverse with codomain restricted to the closed
zero-initial subspace. -/
def localTensorHeatSolutionToKernelL :
    ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      FiniteParabolicC2AlphaBanach.zeroInitialSubmodule
        (X := E) (E := Fin d × Fin d → ℝ) hT hα :=
  (localTensorHeatSolutionL
    (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall).codRestrict
      (FiniteParabolicC2AlphaBanach.zeroInitialSubmodule hT hα)
      (fun q => (FiniteParabolicC2AlphaBanach.mem_zeroInitialSubmodule_iff
        hT hα _).2 (initialTraceL_localTensorHeatSolutionL_apply
          (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall q))

@[simp]
theorem localTensorHeatSolutionToKernelL_apply
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (parabolicFiniteCylinder E t₀ T)) :
    (localTensorHeatSolutionToKernelL
      (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall q :
        FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α) =
      localTensorHeatSolutionL
        (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall q :=
  rfl

/-! ## Nonzero initial data by affine correction -/

/-- Starting from any higher-parabolic extension `h` of the desired initial
datum, correct its equation defect with the zero-trace local inverse. -/
def localTensorHeatAffineSolution
    (h : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α)
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (parabolicFiniteCylinder E t₀ T)) :
    FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α :=
  LinearParabolicParametrix.affineCauchyCorrection P
    (localTensorHeatSolutionL
      (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall) h q

/-- The affine local solution has the prescribed forcing. -/
theorem localTensorHeatAffineSolution_solves
    (h : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α)
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (parabolicFiniteCylinder E t₀ T)) :
    P (localTensorHeatAffineSolution
      (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall h q) = q := by
  apply LinearParabolicParametrix.apply_affineCauchyCorrection
  exact comp_localTensorHeatSolutionL
    (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall

/-- The affine local solution has exactly the canonical initial trace of the
chosen extension. -/
theorem initialTraceL_localTensorHeatAffineSolution
    (h : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α)
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (parabolicFiniteCylinder E t₀ T)) :
    FiniteParabolicC2AlphaBanach.initialTraceL hT hα
        (localTensorHeatAffineSolution
          (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall h q) =
      FiniteParabolicC2AlphaBanach.initialTraceL hT hα h := by
  apply LinearParabolicParametrix.trace_affineCauchyCorrection
  exact initialTraceL_comp_localTensorHeatSolutionL
    (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall

/-- Quantitative affine local Schauder estimate. -/
theorem norm_localTensorHeatAffineSolution_le
    (h : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α)
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (parabolicFiniteCylinder E t₀ T)) :
    ‖localTensorHeatAffineSolution
        (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall h q‖ ≤
      ‖h‖ +
        ‖localTensorHeatSolutionL
          (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall‖ *
          ‖q - P h‖ := by
  exact LinearParabolicParametrix.norm_affineCauchyCorrection_le P
    (localTensorHeatSolutionL
      (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall) h q

/-- Every forcing and every initial datum represented by a higher-parabolic
extension admit a local solution with an explicit Schauder bound. -/
theorem exists_localTensorHeatSolution_with_initialTrace
    (h : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α)
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (parabolicFiniteCylinder E t₀ T)) :
    ∃ u : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α,
      P u = q ∧
      FiniteParabolicC2AlphaBanach.initialTraceL hT hα u =
        FiniteParabolicC2AlphaBanach.initialTraceL hT hα h ∧
      ‖u‖ ≤ ‖h‖ +
        ‖localTensorHeatSolutionL
          (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall‖ *
          ‖q - P h‖ := by
  exact LinearParabolicParametrix.exists_solution_with_trace_of_rightInverse_zeroTrace
    (FiniteParabolicC2AlphaBanach.initialTraceL
      (X := E) (E := Fin d × Fin d → ℝ) (t₀ := t₀) (T := T) (α := α) hT hα) P
    (localTensorHeatSolutionL
      (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall)
    (comp_localTensorHeatSolutionL
      (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall)
    (initialTraceL_comp_localTensorHeatSolutionL
      (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall) h q

/-- Every bounded spatial `C^{2,α}` initial datum and parabolic Hölder forcing
admit a corrected local solution with exactly that canonical trace. -/
theorem exists_localTensorHeatSolution_with_spatialInitialData
    (D : BoundedSpatialC2AlphaData E (Fin d × Fin d → ℝ) α)
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (parabolicFiniteCylinder E t₀ T)) :
    ∃ u : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α,
      P u = q ∧
      FiniteParabolicC2AlphaBanach.initialTraceL hT hα u = D.value ∧
      ‖u‖ ≤
        ‖D.timeIndependentExtension (t₀ := t₀) (T := T) hα‖ +
        ‖localTensorHeatSolutionL
          (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall‖ *
          ‖q - P (D.timeIndependentExtension
            (t₀ := t₀) (T := T) hα)‖ := by
  obtain ⟨u, hPu, htrace, hnorm⟩ :=
    exists_localTensorHeatSolution_with_initialTrace
      (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall
      (D.timeIndependentExtension (t₀ := t₀) (T := T) hα) q
  refine ⟨u, hPu, ?_, hnorm⟩
  rw [htrace, D.initialTraceL_timeIndependentExtension hT hα]

end LocalTrace

end AnalyticPDE
end RicciFlow
