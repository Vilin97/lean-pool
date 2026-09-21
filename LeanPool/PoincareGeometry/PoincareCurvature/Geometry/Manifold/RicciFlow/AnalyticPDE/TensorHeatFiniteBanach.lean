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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatC2Alpha
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteCylinderBanach
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.HigherFunctionSpace

/-!
# Finite-cylinder Banach solution for Euclidean tensor heat flow

The scalar heat-kernel construction is assembled into one matrix-valued
`C^{2+α,1+α/2}` Banach element.  Unlike an entrywise predicate, this is a
single complete-space inhabitant on which bounded coordinate differential
operators act.
-/

@[expose] public noncomputable section
open Real Set MeasureTheory Metric Filter
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- All analytic data required by the finite-cylinder matrix heat problem. -/
structure MatrixHeatFiniteData (n d : ℕ) (t₀ T r : ℝ) where
  hT : t₀ ≤ T
  hr0 : 0 < r
  hr1 : r < 1
  initial : Matrix (Fin d) (Fin d) (EuclideanBoundedC2Data n)
  initialHessianHolderConstant : ℝ
  initialHessianHolderConstant_nonneg : 0 ≤ initialHessianHolderConstant
  initialHessianHolder : ∀ i j a b x y,
    |(initial i j).second a b x - (initial i j).second a b y| ≤
      initialHessianHolderConstant * ∑ ell : Fin n, |(x - y) ell| ^ r
  source : ℝ → Matrix (Fin d) (Fin d)
    (BoundedContinuousFunction (Fin n → ℝ) ℝ)
  source_continuous : ∀ i j, Continuous (fun s ↦ source s i j)
  sourceBound : ℝ
  sourceSpatialHolderConstant : ℝ
  sourceParabolicHolderConstant : ℝ
  sourceBound_nonneg : 0 ≤ sourceBound
  sourceSpatialHolderConstant_nonneg : 0 ≤ sourceSpatialHolderConstant
  sourceParabolicHolderConstant_nonneg : 0 ≤ sourceParabolicHolderConstant
  source_bounded : ∀ s y i j, ‖source s i j y‖ ≤ sourceBound
  source_spatialHolder : ∀ s x y i j, |source s i j y - source s i j x| ≤
    sourceSpatialHolderConstant * ∑ ell : Fin n, |(x - y) ell| ^ r
  source_parabolicHolder : ∀ i j, ParabolicHolderWith sourceParabolicHolderConstant r
    (fun z : ℝ × (Fin n → ℝ) ↦ source z.1 i j z.2)
    (euclideanMildFiniteCylinderND n t₀ T)

namespace MatrixHeatFiniteData

variable {n d : ℕ} {t₀ T r : ℝ}

/-- The matrix-valued mild solution represented by the data. -/
def solutionFunction (P : MatrixHeatFiniteData n d t₀ T r) :
    ℝ × (Fin n → ℝ) → Fin d → Fin d → ℝ :=
  matrixHeatMildSpaceTimeND n d t₀
    (matrixEuclideanBoundedC2ValueND P.initial) P.source

/-- The assembled matrix `C^{2+α,1+α/2}` radius. -/
def schauderRadius (P : MatrixHeatFiniteData n d t₀ T r) : ℝ :=
  ∑ i : Fin d,
    ParabolicC2AlphaNormLe.continuousLinearMapRadius
      (X := Fin n → ℝ) (E := Fin d → ℝ)
      (ContinuousLinearMap.single ℝ (fun _ : Fin d => Fin d → ℝ) i) *
      (∑ j : Fin d,
        ParabolicC2AlphaNormLe.continuousLinearMapRadius
          (X := Fin n → ℝ) (E := ℝ)
          (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) j) *
        heatMildC2AlphaNormConstantND n t₀ T r
          P.initialHessianHolderConstant P.sourceSpatialHolderConstant
          P.sourceBound P.sourceParabolicHolderConstant (P.initial i j))

/-- The matrix mild solution has one matrix-valued higher parabolic norm
bound, obtained by finite assembly of the scalar bounds. -/
theorem solutionFunction_c2AlphaNormLe (P : MatrixHeatFiniteData n d t₀ T r) :
    ParabolicC2AlphaNormLe P.schauderRadius r P.solutionFunction
      (parabolicFiniteCylinder (Fin n → ℝ) t₀ T) := by
  classical
  have hentries : ∀ i j, ParabolicC2AlphaNormLe
      (heatMildC2AlphaNormConstantND n t₀ T r
        P.initialHessianHolderConstant P.sourceSpatialHolderConstant
        P.sourceBound P.sourceParabolicHolderConstant (P.initial i j)) r
      (fun z ↦ P.solutionFunction z i j)
      (parabolicFiniteCylinder (Fin n → ℝ) t₀ T) := by
    intro i j
    change ParabolicC2AlphaNormLe _ r
      (heatMildSpaceTimeND t₀ (P.initial i j).value (fun s ↦ P.source s i j)) _
    simpa only [parabolicFiniteCylinder, euclideanMildFiniteCylinderND] using
      (parabolicC2AlphaNormLe_heatMildSpaceTimeND_Ioc
        P.hT P.hr0 P.hr1 (P.initial i j)
        P.initialHessianHolderConstant_nonneg (P.initialHessianHolder i j)
        (P.source_continuous i j) P.sourceBound_nonneg
        P.sourceSpatialHolderConstant_nonneg P.sourceParabolicHolderConstant_nonneg
        (fun s y ↦ P.source_bounded s y i j)
        (fun s x y ↦ P.source_spatialHolder s x y i j)
        (P.source_parabolicHolder i j))
  have hrows : ∀ i, ParabolicC2AlphaNormLe
      (∑ j : Fin d,
        ParabolicC2AlphaNormLe.continuousLinearMapRadius
          (X := Fin n → ℝ) (E := ℝ)
          (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) j) *
        heatMildC2AlphaNormConstantND n t₀ T r
          P.initialHessianHolderConstant P.sourceSpatialHolderConstant
          P.sourceBound P.sourceParabolicHolderConstant (P.initial i j)) r
      (fun z ↦ P.solutionFunction z i)
      (parabolicFiniteCylinder (Fin n → ℝ) t₀ T) := by
    intro i
    exact ParabolicC2AlphaNormLe.pi
      (X := Fin n → ℝ) (s := parabolicFiniteCylinder (Fin n → ℝ) t₀ T)
      (fun j ↦ hentries i j)
  simpa only [schauderRadius] using
    (ParabolicC2AlphaNormLe.pi
      (X := Fin n → ℝ) (s := parabolicFiniteCylinder (Fin n → ℝ) t₀ T)
      hrows)

/-- A canonical genuine matrix-valued second jet selected from the proved
higher estimate. -/
def chosenSecondJet (P : MatrixHeatFiniteData n d t₀ T r) :
    ParabolicSecondJet P.solutionFunction
      (parabolicFiniteCylinder (Fin n → ℝ) t₀ T) :=
  Classical.choose P.solutionFunction_c2AlphaNormLe.exists_secondJet_c0AlphaNormLe_self

/-- All four components of the canonical jet obey the assembled radius. -/
theorem chosenSecondJet_componentBounds (P : MatrixHeatFiniteData n d t₀ T r) :
    ParabolicC0AlphaNormLe P.schauderRadius r P.solutionFunction
        (parabolicFiniteCylinder (Fin n → ℝ) t₀ T) ∧
      ParabolicC0AlphaNormLe P.schauderRadius r P.chosenSecondJet.spaceDeriv
        (parabolicFiniteCylinder (Fin n → ℝ) t₀ T) ∧
      ParabolicC0AlphaNormLe P.schauderRadius r P.chosenSecondJet.spaceSecondDeriv
        (parabolicFiniteCylinder (Fin n → ℝ) t₀ T) ∧
      ParabolicC0AlphaNormLe P.schauderRadius r P.chosenSecondJet.timeDeriv
        (parabolicFiniteCylinder (Fin n → ℝ) t₀ T) :=
  Classical.choose_spec P.solutionFunction_c2AlphaNormLe.exists_secondJet_c0AlphaNormLe_self

/-- The matrix mild solution as one element of the complete finite-cylinder
parabolic Banach space. -/
def solution (P : MatrixHeatFiniteData n d t₀ T r) :
    FiniteParabolicC2AlphaBanach (Fin n → ℝ) (Fin d → Fin d → ℝ)
      t₀ T r :=
  FiniteParabolicC2AlphaBanach.ofSecondJet P.solutionFunction P.chosenSecondJet
    P.chosenSecondJet_componentBounds.1.c0AlphaOn
    P.chosenSecondJet_componentBounds.2.1.c0AlphaOn
    P.chosenSecondJet_componentBounds.2.2.1.c0AlphaOn
    P.chosenSecondJet_componentBounds.2.2.2.c0AlphaOn

@[simp] theorem solution_value (P : MatrixHeatFiniteData n d t₀ T r)
    {z : ℝ × (Fin n → ℝ)}
    (hz : z ∈ parabolicFiniteCylinder (Fin n → ℝ) t₀ T) :
    FiniteParabolicC2AlphaBanach.value P.solution z = P.solutionFunction z := by
  exact FiniteParabolicC2AlphaBanach.value_ofSecondJet _ _ _ _ _ _ hz

theorem norm_solution_le (P : MatrixHeatFiniteData n d t₀ T r) :
    ‖P.solution‖ ≤ P.schauderRadius := by
  exact FiniteParabolicC2AlphaBanach.norm_ofSecondJet_le
    P.solutionFunction P.chosenSecondJet
    P.chosenSecondJet_componentBounds.1
    P.chosenSecondJet_componentBounds.2.1
    P.chosenSecondJet_componentBounds.2.2.1
    P.chosenSecondJet_componentBounds.2.2.2

/-- The explicit scalar jet in one matrix entry, restricted to the finite
cylinder. -/
def entrySecondJet (P : MatrixHeatFiniteData n d t₀ T r) (i j : Fin d) :
    ParabolicSecondJet (fun z ↦ P.solutionFunction z i j)
      (parabolicFiniteCylinder (Fin n → ℝ) t₀ T) := by
  change ParabolicSecondJet
    (heatMildSpaceTimeND t₀ (P.initial i j).value (fun s ↦ P.source s i j))
    (euclideanMildFiniteCylinderND n t₀ T)
  exact heatMildFiniteParabolicSecondJetND (t₀ := t₀) (T := T) P.hr0
    (P.initial i j).value (P.source_continuous i j)
    P.sourceSpatialHolderConstant_nonneg
    (fun s y ↦ P.source_bounded s y i j)
    (fun s x y ↦ P.source_spatialHolder s x y i j)

/-- Evaluating the time derivative of the selected matrix jet in an entry
recovers the time derivative of the explicit scalar entry jet. -/
theorem chosenSecondJet_timeDeriv_apply (P : MatrixHeatFiniteData n d t₀ T r)
    {z : ℝ × (Fin n → ℝ)}
    (hz : z ∈ parabolicFiniteCylinder (Fin n → ℝ) t₀ T) (i j : Fin d) :
    P.chosenSecondJet.timeDeriv z i j = (P.entrySecondJet i j).timeDeriv z := by
  let L : (Fin d → Fin d → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : (Fin d → Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
  let K : ParabolicSecondJet (fun z ↦ P.solutionFunction z i j)
      (parabolicFiniteCylinder (Fin n → ℝ) t₀ T) := by
    simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using
      (P.chosenSecondJet.continuousLinearMap L)
  have heq := K.timeDeriv_eq_of_unique (P.entrySecondJet i j) hz
    (uniqueDiffWithinAt_timeSlice_parabolicFiniteCylinder hz)
  simpa only [K, L, ParabolicSecondJet.continuousLinearMap,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using heq

/-- Evaluating the spatial Hessian of the selected matrix jet in an entry
recovers the Hessian of the explicit scalar entry jet. -/
theorem chosenSecondJet_spaceSecondDeriv_apply
    (P : MatrixHeatFiniteData n d t₀ T r)
    {z : ℝ × (Fin n → ℝ)}
    (hz : z ∈ parabolicFiniteCylinder (Fin n → ℝ) t₀ T)
    (v w : Fin n → ℝ) (i j : Fin d) :
    P.chosenSecondJet.spaceSecondDeriv z v w i j =
      (P.entrySecondJet i j).spaceSecondDeriv z v w := by
  let L : (Fin d → Fin d → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : (Fin d → Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
  let K : ParabolicSecondJet (fun z ↦ P.solutionFunction z i j)
      (parabolicFiniteCylinder (Fin n → ℝ) t₀ T) := by
    simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using
      (P.chosenSecondJet.continuousLinearMap L)
  have heq := K.spaceSecondDeriv_eq_of_unique (P.entrySecondJet i j) hz
    (fun {_x} hx ↦ uniqueDiffWithinAt_spaceSlice_parabolicFiniteCylinder hx)
  have happ := congrArg (fun A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ ↦
    A v w) heq
  simpa only [K, L, ParabolicSecondJet.continuousLinearMap,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.compL_apply] using happ

@[simp] theorem solution_timeDeriv (P : MatrixHeatFiniteData n d t₀ T r)
    {z : ℝ × (Fin n → ℝ)}
    (hz : z ∈ parabolicFiniteCylinder (Fin n → ℝ) t₀ T) :
    FiniteParabolicC2AlphaBanach.timeDeriv P.solution z =
      P.chosenSecondJet.timeDeriv z := by
  exact FiniteParabolicC2AlphaBanach.timeDeriv_ofSecondJet _ _ _ _ _ _ hz

@[simp] theorem solution_spaceSecondDeriv
    (P : MatrixHeatFiniteData n d t₀ T r)
    {z : ℝ × (Fin n → ℝ)}
    (hz : z ∈ parabolicFiniteCylinder (Fin n → ℝ) t₀ T) :
    FiniteParabolicC2AlphaBanach.spaceSecondDeriv P.solution z =
      P.chosenSecondJet.spaceSecondDeriv z := by
  exact FiniteParabolicC2AlphaBanach.spaceSecondDeriv_ofSecondJet _ _ _ _ _ _ hz

/-- Each explicit entry jet satisfies the scalar inhomogeneous heat equation. -/
theorem entrySecondJet_heatEquation (P : MatrixHeatFiniteData n d t₀ T r)
    {t : ℝ} (ht : t ∈ Set.Ioc t₀ T) (x : Fin n → ℝ) (i j : Fin d) :
    (P.entrySecondJet i j).timeDeriv (t, x) =
      (∑ k : Fin n, (P.entrySecondJet i j).spaceSecondDeriv (t, x)
        (Pi.single k 1) (Pi.single k 1)) + P.source t i j x := by
  change heatMildTimeDerivND t₀ (P.initial i j).value (fun s ↦ P.source s i j) (t, x) =
    (∑ k : Fin n,
      heatMildSpaceHessianND t₀ P.hr0 (P.initial i j).value
        (P.source_continuous i j) P.sourceSpatialHolderConstant_nonneg
        (fun s y ↦ P.source_bounded s y i j)
        (fun s y z ↦ P.source_spatialHolder s y z i j) (t, x)
        (Pi.single k 1) (Pi.single k 1)) + P.source t i j x
  simp only [heatMildTimeDerivND, if_pos ht.1, heatMildSpaceHessianND,
    dif_pos ht.1]
  rw [sum_heatMildSpatialHessianCLM_diag_eq_laplacian
    ht.1 P.hr0 (P.initial i j).value (P.source_continuous i j)
    P.sourceSpatialHolderConstant_nonneg
    (fun s y ↦ P.source_bounded s y i j)
    (fun s y z ↦ P.source_spatialHolder s y z i j) x]

/-- The single matrix-valued Banach inhabitant satisfies the inhomogeneous
tensor heat equation, coefficientwise, at every positive cylinder time. -/
theorem solution_heatEquation (P : MatrixHeatFiniteData n d t₀ T r)
    {t : ℝ} (ht : t ∈ Set.Ioc t₀ T) (x : Fin n → ℝ) :
    FiniteParabolicC2AlphaBanach.timeDeriv P.solution (t, x) =
      (∑ k : Fin n, FiniteParabolicC2AlphaBanach.spaceSecondDeriv
        P.solution (t, x) (Pi.single k 1) (Pi.single k 1)) +
      (fun i j ↦ P.source t i j x) := by
  have hz : (t, x) ∈ parabolicFiniteCylinder (Fin n → ℝ) t₀ T := by
    simpa [parabolicFiniteCylinder] using ht
  rw [P.solution_timeDeriv hz, P.solution_spaceSecondDeriv hz]
  funext i j
  rw [P.chosenSecondJet_timeDeriv_apply hz i j]
  simp only [Finset.sum_apply, Pi.add_apply]
  rw [P.entrySecondJet_heatEquation ht x i j]
  congr 1
  apply Finset.sum_congr rfl
  intro k _hk
  exact (P.chosenSecondJet_spaceSecondDeriv_apply hz
    (Pi.single k 1) (Pi.single k 1) i j).symm

/-- Symmetric initial coefficients and forcing give a symmetric packaged
solution at every point of the cylinder. -/
theorem solution_isSymm (P : MatrixHeatFiniteData n d t₀ T r)
    (hinitial : ∀ i j, (P.initial i j).value = (P.initial j i).value)
    (hsource : ∀ s i j, P.source s i j = P.source s j i)
    {z : ℝ × (Fin n → ℝ)}
    (hz : z ∈ parabolicFiniteCylinder (Fin n → ℝ) t₀ T) :
    ∀ i j, FiniteParabolicC2AlphaBanach.value P.solution z i j =
      FiniteParabolicC2AlphaBanach.value P.solution z j i := by
  rw [P.solution_value hz]
  intro i j
  exact (matrixHeatMildSpaceTimeND_isSymm_of_boundedC2 t₀ P.initial P.source
    hinitial hsource z).apply j i

end MatrixHeatFiniteData

end AnalyticPDE
end RicciFlow
