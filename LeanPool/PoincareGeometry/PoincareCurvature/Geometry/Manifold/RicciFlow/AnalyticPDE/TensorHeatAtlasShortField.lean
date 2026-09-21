/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasCutoff
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasShortTime

/-!
# Tensor-heat atlas fields on a genuinely short physical interval

A common physical terminal time does not correspond to the same normalized
terminal time in charts of different radii.  This file records the correct
chart-dependent normalized cylinders and reconstructs their local solutions
on one common physical interval.  No long-cylinder solution is evaluated
outside the portion controlled by the short-time estimates.
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

variable {d : ℕ} {t₀ T α τ : ℝ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "W₂" => (Fin d × Fin d → ℝ)

/-- Normalized terminal time in chart `i` corresponding to the common
physical terminal time `τ`. -/
def shortNormalizedTerminal
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (τ : ℝ) (i : A.cover.Index) : ℝ :=
  FiniteClassicalTensorHeatField.normalizedTime
    t₀ (A.radius (i : M)) τ

/-- A physical time in the atlas common interval maps into every chart's
original normalized cylinder. -/
theorem shortNormalizedTerminal_mem_Ioc
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) (hτ : t₀ < τ) (hτA : τ ≤ A.commonTerminalTime) :
    A.shortNormalizedTerminal cov τ i ∈ Ioc t₀ T := by
  apply FiniteClassicalTensorHeatField.normalizedTime_mem_Ioc
    (ne_of_gt (A.radius_pos (i : M)))
  exact ⟨hτ, hτA.trans (A.commonTerminalTime_le cov i)⟩

theorem time_lt_shortNormalizedTerminal
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) (hτ : t₀ < τ) (hτA : τ ≤ A.commonTerminalTime) :
    t₀ < A.shortNormalizedTerminal cov τ i :=
  (A.shortNormalizedTerminal_mem_Ioc cov i hτ hτA).1

theorem shortNormalizedTerminal_le
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) (hτ : t₀ < τ) (hτA : τ ≤ A.commonTerminalTime) :
    A.shortNormalizedTerminal cov τ i ≤ T :=
  (A.shortNormalizedTerminal_mem_Ioc cov i hτ hτA).2

/-- Rescaling the chart-dependent normalized terminal time returns exactly
the chosen common physical terminal time. -/
theorem physicalTerminalTime_shortNormalizedTerminal
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (τ : ℝ) (i : A.cover.Index) :
    FiniteClassicalTensorHeatField.physicalTerminalTime t₀
        (A.shortNormalizedTerminal cov τ i) (A.radius (i : M)) = τ := by
  have hr : A.radius (i : M) ≠ 0 := ne_of_gt (A.radius_pos (i : M))
  unfold shortNormalizedTerminal
  rw [FiniteClassicalTensorHeatField.physicalTerminalTime,
    FiniteClassicalTensorHeatField.normalizedTime]
  field_simp [hr]
  ring

/-- Product of the chart-dependent normalized source spaces for a common
short physical interval. -/
abbrev ShortSourceSpace
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (τ : ℝ) :=
  (i : A.cover.Index) →
    ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀
        (A.shortNormalizedTerminal cov τ i))

/-- The shortened normalized solution in the matrix convention used for
intrinsic tensor reconstruction. -/
def shortNormalizedLocalSolution
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) (hτ : t₀ < τ) (hτA : τ ≤ A.commonTerminalTime)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀
        (A.shortNormalizedTerminal cov τ i))) :
    FiniteParabolicC2AlphaBanach E (Fin d → Fin d → ℝ) t₀
      (A.shortNormalizedTerminal cov τ i) α :=
  FiniteParabolicC2AlphaBanach.fiberPostcompL
    (tensorCoordinateReconstructionEquiv d).toContinuousLinearMap
    (shortLocalInverse cov A i
      (A.time_lt_shortNormalizedTerminal cov i hτ hτA)
      (A.shortNormalizedTerminal_le cov i hτ hτA) q)

/-- Pointwise application of the shortened coordinate right inverse. -/
theorem shortLocalCauchy_shortLocalInverse
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) (hτ : t₀ < τ) (hτA : τ ≤ A.commonTerminalTime)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀
        (A.shortNormalizedTerminal cov τ i))) :
    shortLocalCauchyL cov A i
        (A.shortNormalizedTerminal_le cov i hτ hτA)
        (shortLocalInverse cov A i
          (A.time_lt_shortNormalizedTerminal cov i hτ hτA)
          (A.shortNormalizedTerminal_le cov i hτ hτA) q) = q := by
  have h := congrArg
    (fun L : ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀
            (A.shortNormalizedTerminal cov τ i)) →L[ℝ]
        ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀
            (A.shortNormalizedTerminal cov τ i)) => L q)
    (shortLocalCauchyL_comp_shortLocalInverse cov A i
      (A.time_lt_shortNormalizedTerminal cov i hτ hτA)
      (A.shortNormalizedTerminal_le cov i hτ hτA))
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using h

/-- On the unit ball, the shortened inverse satisfies the coordinate
equation of the actual connection Laplacian, with the chart-dependent
normalized terminal time. -/
theorem shortNormalizedLocalEquation_on_unitBall
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) (hτ : t₀ < τ) (hτA : τ ≤ A.commonTerminalTime)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀
        (A.shortNormalizedTerminal cov τ i)))
    (z : ℝ × E)
    (hz : z ∈ parabolicFiniteCylinder E t₀
      (A.shortNormalizedTerminal cov τ i))
    (hzBall : z.2 ∈ Metric.closedBall (0 : E) 1) :
    let u := shortLocalInverse cov A i
      (A.time_lt_shortNormalizedTerminal cov i hτ hτA)
      (A.shortNormalizedTerminal_le cov i hτ hτA) q
    FiniteParabolicC2AlphaBanach.timeDeriv u z -
        (localTensorHeatPrincipalCoefficient (I := I) (i : M)
            (trivializationAt E TM (i : M)) b
            ((extChartAt I (i : M)) (i : M) +
              A.radius (i : M) • z.2)
            (FiniteParabolicC2AlphaBanach.spaceSecondDeriv u z) +
          A.radius (i : M) •
            localTensorHeatFirstCoefficient (I := I) cov (i : M)
              (trivializationAt E TM (i : M)) b
              ((extChartAt I (i : M)) (i : M) +
                A.radius (i : M) • z.2)
              (FiniteParabolicC2AlphaBanach.spaceDeriv u z) +
          A.radius (i : M) ^ 2 •
            localTensorHeatZeroCoefficient (I := I) cov (i : M)
              (trivializationAt E TM (i : M)) b
              ((extChartAt I (i : M)) (i : M) +
                A.radius (i : M) • z.2)
              (FiniteParabolicC2AlphaBanach.value u z)) =
      ParabolicC0AlphaBanach.evalCLM z hz q := by
  dsimp only
  let hST := A.shortNormalizedTerminal_le cov i hτ hτA
  let hS := A.time_lt_shortNormalizedTerminal cov i hτ hτA
  let u := shortLocalInverse cov A i hS hST q
  have heq : shortLocalCauchyL cov A i hST u = q :=
    A.shortLocalCauchy_shortLocalInverse cov i hτ hτA q
  have heval := congrArg
    (ParabolicC0AlphaBanach.evalCLM z hz) heq
  change ParabolicC0AlphaBanach.evalCLM z hz
      (FiniteParabolicC2AlphaBanach.coordinateCauchyL _ _ _ u) = _ at heval
  rw [FiniteParabolicC2AlphaBanach.evalCLM_coordinateCauchyL] at heval
  obtain ⟨_hzDomain, hA, hB, hC⟩ := A.fields_agree (i : M) z hzBall
  change _ = _ at heval
  simp only [ParabolicC0AlphaSpace.toFun_restrictL] at heval
  rw [hA, hB, hC] at heval
  simpa only [smul_apply, u, hS, hST] using heval

@[simp] theorem shortNormalizedLocalSolution_value
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) (hτ : t₀ < τ) (hτA : τ ≤ A.commonTerminalTime)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀
        (A.shortNormalizedTerminal cov τ i)))
    (z : ℝ × E)
    (hz : z ∈ parabolicFiniteCylinder E t₀
      (A.shortNormalizedTerminal cov τ i))
    (a c : Fin d) :
    FiniteParabolicC2AlphaBanach.value
        (A.shortNormalizedLocalSolution cov i hτ hτA q) z a c =
      FiniteParabolicC2AlphaBanach.value
        (shortLocalInverse cov A i
          (A.time_lt_shortNormalizedTerminal cov i hτ hτA)
          (A.shortNormalizedTerminal_le cov i hτ hτA) q) z (c, a) := by
  rw [shortNormalizedLocalSolution,
    FiniteParabolicC2AlphaBanach.value_fiberPostcompL _ _ z hz]
  rfl

/-- One shortened local inverse reconstructed and parabolically rescaled on
the common physical interval `(t₀,τ]`. -/
def shortLocalField
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index) (hτ : t₀ < τ) (hτA : τ ≤ A.commonTerminalTime)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀
        (A.shortNormalizedTerminal cov τ i))) :
    FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ τ :=
  FiniteClassicalTensorHeatField.restrictTerminal cov
    (physicalFiniteClassicalTensorHeatField
      (I := I) cov (i : M) (A.radius (i : M))
      (ne_of_gt (A.radius_pos (i : M))) b (A.cover.partition i)
      ((A.cover.partition i).contMDiff.of_le
        (show (2 : WithTop ℕ∞) ≤ ∞ by decide))
      (A.cover.pieces_subset_domain i)
      (A.patch_subset_trivialization (i : M))
      (A.shortNormalizedLocalSolution cov i hτ hτA q) A.alpha_pos)
    τ (le_of_eq (A.physicalTerminalTime_shortNormalizedTerminal cov τ i).symm)

/-- The shortened finite-atlas parametrix on one honest common physical
interval. -/
def shortParametrixField
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (hτ : t₀ < τ) (hτA : τ ≤ A.commonTerminalTime)
    (q : ShortSourceSpace cov A τ) :
    FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ τ :=
  FiniteClassicalTensorHeatField.finsetSum cov Finset.univ
    (fun i => A.shortLocalField cov i hτ hτA (q i))

end FiniteTensorHeatParametrixAtlas
end AnalyticPDE
end RicciFlow
