/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatFrozenInverse
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.Parametrix

/-!
# Local inversion by perturbing the frozen tensor-heat operator

This file performs the functional-analytic correction needed after freezing
the genuine tensor-heat operator at a chart point.  The exact finite-cylinder
frozen inverse is used as a right parametrix for any nearby bounded operator.
If the resulting perturbation has norm below one, a Neumann series produces
an exact bounded right inverse, together with its quantitative Schauder
estimate.

The hypothesis is intentionally the single concrete estimate which remains
for the geometric localization argument: the variable-coefficient operator,
including lower-order connection terms and cutoff commutators, must be close
to its frozen principal part after composition with the frozen inverse.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff

namespace RicciFlow
namespace AnalyticPDE

open CovariantDerivative
open LinearParabolicParametrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

/-! ## The frozen-relative perturbation -/

/-- The error of a finite-cylinder operator relative to the genuine frozen
tensor-heat operator, measured after applying the exact frozen inverse. -/
def frozenTensorHeatPerturbationL
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) (x : M)
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (P : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
        (parabolicFiniteCylinder E t₀ T)) :
    ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
        (parabolicFiniteCylinder E t₀ T) :=
  (P - frozenTensorHeatCauchyL (I := I) p e b x t₀ T α).comp
    (frozenTensorHeatFiniteZeroInitialInverseL
      (I := I) p x hxChart d hT hα hα1)

/-- Because the frozen inverse is exact, the right-parametrix defect for `P`
is exactly the negative frozen-relative perturbation. -/
theorem rightError_frozenTensorHeatFiniteZeroInitialInverseL
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (P : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
        (parabolicFiniteCylinder E t₀ T)) :
    rightError P
        (frozenTensorHeatFiniteZeroInitialInverseL
          (I := I) p x hxChart d hT hα hα1) =
      -frozenTensorHeatPerturbationL
        (I := I) p e b x hxChart hT hα hα1 P := by
  rw [rightError, frozenTensorHeatPerturbationL]
  rw [ContinuousLinearMap.sub_comp]
  rw [frozenTensorHeatCauchyL_comp_finiteZeroInitialInverseL
    (I := I) p e b hxFrame hxChart hT hα hα1]
  ext q
  simp

/-- A strict frozen-relative perturbation supplies the one-sided Neumann
parametrix datum for the variable operator. -/
def frozenTensorHeatRightData
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (P : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
        (parabolicFiniteCylinder E t₀ T))
    (hsmall : ‖frozenTensorHeatPerturbationL
      (I := I) p e b x hxChart hT hα hα1 P‖ < 1) :
    LinearParabolicParametrix.RightData P where
  approxRightInverse := frozenTensorHeatFiniteZeroInitialInverseL
    (I := I) p x hxChart d hT hα hα1
  rightError_lt_one := by
    rw [rightError_frozenTensorHeatFiniteZeroInitialInverseL
      (I := I) p e b hxFrame hxChart hT hα hα1 P, norm_neg]
    exact hsmall

/-! ## Corrected local solution operator -/

/-- The exact zero-initial solution operator obtained by Neumann-correcting
the genuine frozen tensor-heat inverse. -/
def localTensorHeatSolutionL
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (P : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
        (parabolicFiniteCylinder E t₀ T))
    (hsmall : ‖frozenTensorHeatPerturbationL
      (I := I) p e b x hxChart hT hα hα1 P‖ < 1) :
    ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α :=
  rightSolutionOperator P
    (frozenTensorHeatRightData
      (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall)

/-- The corrected local solution operator is an exact right inverse of the
variable finite-cylinder operator. -/
theorem comp_localTensorHeatSolutionL
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (P : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
        (parabolicFiniteCylinder E t₀ T))
    (hsmall : ‖frozenTensorHeatPerturbationL
      (I := I) p e b x hxChart hT hα hα1 P‖ < 1) :
    P.comp (localTensorHeatSolutionL
      (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall) =
      ContinuousLinearMap.id ℝ
        (ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
          (parabolicFiniteCylinder E t₀ T)) :=
  comp_rightSolutionOperator P
    (frozenTensorHeatRightData
      (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall)

/-- Every finite-cylinder source is solved by the corrected local operator. -/
theorem localTensorHeatSolutionL_solves
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
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
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (parabolicFiniteCylinder E t₀ T)) :
    P (localTensorHeatSolutionL
      (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall q) = q :=
  rightSolutionOperator_solves P
    (frozenTensorHeatRightData
      (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall) q

/-- Explicit local Schauder estimate.  The denominator is precisely the
distance of the frozen-relative perturbation norm from one. -/
theorem norm_localTensorHeatSolutionL_le
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (P : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
        (parabolicFiniteCylinder E t₀ T))
    (hsmall : ‖frozenTensorHeatPerturbationL
      (I := I) p e b x hxChart hT hα hα1 P‖ < 1) :
    ‖localTensorHeatSolutionL
      (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall‖ ≤
      ‖frozenTensorHeatFiniteZeroInitialInverseL
          (I := I) p x hxChart d hT hα hα1‖ *
        (1 - ‖frozenTensorHeatPerturbationL
          (I := I) p e b x hxChart hT hα hα1 P‖)⁻¹ := by
  unfold localTensorHeatSolutionL
  have h := norm_rightSolutionOperator_le P
    (frozenTensorHeatRightData
      (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall)
  change
    ‖rightSolutionOperator P
        (frozenTensorHeatRightData
          (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall)‖ ≤
      ‖frozenTensorHeatFiniteZeroInitialInverseL
          (I := I) p x hxChart d hT hα hα1‖ *
        (1 - ‖rightError P
          (frozenTensorHeatFiniteZeroInitialInverseL
            (I := I) p x hxChart d hT hα hα1)‖)⁻¹ at h
  rw [rightError_frozenTensorHeatFiniteZeroInitialInverseL
    (I := I) p e b hxFrame hxChart hT hα hα1 P, norm_neg] at h
  exact h

/-- Pointwise form of the local Schauder estimate. -/
theorem norm_localTensorHeatSolutionL_apply_le
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
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
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (parabolicFiniteCylinder E t₀ T)) :
    ‖localTensorHeatSolutionL
      (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall q‖ ≤
      ‖frozenTensorHeatFiniteZeroInitialInverseL
          (I := I) p x hxChart d hT hα hα1‖ *
        (1 - ‖frozenTensorHeatPerturbationL
          (I := I) p e b x hxChart hT hα hα1 P‖)⁻¹ * ‖q‖ := by
  exact (localTensorHeatSolutionL
    (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall).le_opNorm q |>.trans
      (mul_le_mul_of_nonneg_right
        (norm_localTensorHeatSolutionL_le
          (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall)
        (norm_nonneg q))

/-! ## Closed-time zero trace of the corrected solution -/

section ClosedTimeTrace

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

/-- The forcing-space Neumann correction applied before the genuine frozen
zero-initial inverse. -/
def localTensorHeatCorrectedSourceL :
    ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
        (parabolicFiniteCylinder E t₀ T) :=
  LinearParabolicParametrix.neumannInverse
    (LinearParabolicParametrix.rightError P
      (frozenTensorHeatFiniteZeroInitialInverseL
        (I := I) p x hxChart d hT hα hα1))
    (by
      rw [rightError_frozenTensorHeatFiniteZeroInitialInverseL
        (I := I) p e b hxFrame hxChart hT hα hα1 P, norm_neg]
      exact hsmall)

/-- The selected local solution is the frozen zero-initial solver applied
to the Neumann-corrected source. -/
theorem localTensorHeatSolutionL_eq_frozen_comp_correctedSourceL :
    localTensorHeatSolutionL
        (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall =
      (frozenTensorHeatFiniteZeroInitialInverseL
        (I := I) p x hxChart d hT hα hα1).comp
        (localTensorHeatCorrectedSourceL
          (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall) := by
  rfl

/-- Closed-time value path belonging to the selected corrected local
solution. -/
def localTensorHeatSolutionValuePathIcc
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (parabolicFiniteCylinder E t₀ T)) :
    BoundedContinuousFunction (↥(Set.Icc t₀ T))
      (BoundedContinuousFunction E (Fin d × Fin d → ℝ)) :=
  frozenTensorHeatFiniteZeroInitialValuePathIcc
    (I := I) p x hxChart d hT hα
    (localTensorHeatCorrectedSourceL
      (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall q)

/-- The corrected local solution has genuine zero initial trace in the
spatial uniform norm. -/
@[simp] theorem localTensorHeatSolutionValuePathIcc_initial
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (parabolicFiniteCylinder E t₀ T)) :
    localTensorHeatSolutionValuePathIcc
        (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall q
        ⟨t₀, le_rfl, hT.le⟩ = 0 := by
  exact frozenTensorHeatFiniteZeroInitialValuePathIcc_initial
    (I := I) p x hxChart d hT hα _

/-- At positive times the closed path agrees with the frozen inverse applied
to the corrected source; the preceding operator identity identifies this
with the corrected local Schauder solution. -/
theorem localTensorHeatSolutionValuePathIcc_eq_frozenInverse
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (parabolicFiniteCylinder E t₀ T))
    (t : ↥(Set.Ioc t₀ T)) (y : E) :
    localTensorHeatSolutionValuePathIcc
        (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall q
        ⟨t, (Set.mem_Ioc.mp t.2).1.le, (Set.mem_Ioc.mp t.2).2⟩ y =
      FiniteParabolicC2AlphaBanach.value
        (frozenTensorHeatFiniteZeroInitialInverseL
          (I := I) p x hxChart d hT hα hα1
          (localTensorHeatCorrectedSourceL
            (I := I) p e b hxFrame hxChart hT hα hα1 P hsmall q)) (t, y) := by
  rw [localTensorHeatSolutionValuePathIcc,
    frozenTensorHeatFiniteZeroInitialValuePathIcc_eq_inverse]

end ClosedTimeTrace

end AnalyticPDE
end RicciFlow
