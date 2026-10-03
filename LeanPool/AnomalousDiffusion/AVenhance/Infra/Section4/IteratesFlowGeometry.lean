/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.DirectionalCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFlowSupport
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowGlobalJointSmoothness
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowSpatialPeriodicity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2FlowRegularityCore
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2FlowHigherDerivative
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2FlowInverseBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2FlowBoundsAtScale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.AppB2Smoothness

/-! # Iterates Flow Geometry

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance Infra.Construction

/-- Joint smoothness of the actual matrix, assembled from its proved entries. -/
theorem iterate_flowGrad_joint_smooth {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2) := by
  exact contDiff_pi.mpr fun i => contDiff_pi.mpr fun j =>
    amnr_flowGrad_joint_contDiff_infty I hΦ m l i j

/-- Periodicity holds at every time, including the initial time. -/
theorem iterate_flowGrad_periodic {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) :
    IsZ2Periodic (I.flowGrad hΦ m l t) := by
  intro k x
  ext i j
  exact amnr_flowGrad_spatial_periodic I hΦ m l t i j k x

/-- Respect the transposed row/column convention when crossing to
Section 2's continuous-linear-map Jacobian. -/
theorem iterate_flowGrad_entry_eq_composed {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (l : ℤ) (t : ℝ) (x : Vec 2) (i j : Fin 2) :
    (I.flowGrad hΦ m l t x - 1) i j =
      (constructionComposedFlowJacobian hΦ (m - 1)
        ((l : ℝ) * tauPP β I.Λ m) (t - (l : ℝ) * tauPP β I.Λ m) x -
          ContinuousLinearMap.id ℝ (Vec 2)) (basisVec i) j := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (I.xFlow hΦ m l t) :=
    (amnr_xFlow_joint_contDiff_infty I hΦ m l).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
  have hentry : I.flowGrad hΦ m l t x i j =
      (fderiv ℝ (I.xFlow hΦ m l t) (I.xFlowInv hΦ m l t x) (basisVec i)) j := by
    unfold Ingredients.flowGrad gradMatrix spaceGrad
    change fderiv ℝ (fun y => I.xFlow hΦ m l t y j) (I.xFlowInv hΦ m l t x)
      (basisVec i) = _
    rw [fderiv_apply (hs.differentiable (by simp) _) j]
    rfl
  rw [show (I.flowGrad hΦ m l t x - 1) i j =
    I.flowGrad hΦ m l t x i j - (if i = j then 1 else 0) by rfl, hentry]
  unfold constructionComposedFlowJacobian constructionFlowJacobian
    constructionFlowInv constructionFlow Ingredients.xFlow Ingredients.xFlowInv
  simp [Homogenization.basisVec, Pi.single_apply, eq_comm]

/-- The actual active flow entries inherit the all-order composed seminorm. -/
theorem iterate_flowGrad_barNorm {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 2 ≤ m) {l : ℤ} {t : ℝ} (hne : I.hatXiML m l t ≠ 0)
    (n : ℕ) (i j : Fin 2) :
    barNorm n (2 ^ 10 * (epsilon β I.Λ (m - 1))⁻¹)
      (fun x => (I.flowGrad hΦ m l t x - 1) i j) ≤ ENNReal.ofReal 40 := by
  let scales := section2Scales_canonical I
  let data := appB2InverseFlowData_of_smoothPeriodicFlow hΦ scales
  have hind := section2_stream_induction scales data
  have hb := section2_flow_jacobian_composed_from_previous scales data
    (m - 1) (by omega) n (hind ((m - 1) - 1))
    ((l : ℝ) * tauPP β I.Λ m) (t - (l : ℝ) * tauPP β I.Λ m)
    (iterate_hatXi_section2_window I (by omega) hne)
  have he := (le_iSup_of_le j (le_iSup_of_le i le_rfl)).trans hb
  simpa only [flowJacobianBarNorm, ← iterate_flowGrad_entry_eq_composed] using he

end AVenhance.Infra.Section4
