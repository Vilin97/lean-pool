/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.VelocitySpatialRates
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowJacobianC1
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.PulledGradientTransport
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MatrixTransport
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowInvRightInverse

/-! Actual Eulerian material differentiation of the pulled-back flow gradient. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow

/-- The actual pulled-back Jacobian entry is jointly C¹ in Eulerian variables.
This supplies its material differentiability rather than assuming it. -/
theorem amnr_flowGrad_contDiff_one {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (l : ℤ) (k p : Fin 2) :
    ContDiff ℝ 1 (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2 k p) := by
  let b := AVenhance.streamVel (Φ (m - 1))
  let X := AVenhance.flow b (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz
  let s := (l : ℝ) * AVenhance.tauPP β I.Λ m
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)
  have hX : AVenhance.IsFlow b X := AVenhance.flow_isFlow b _ _
  have hJ := amnrFlowJacobianEntry_contDiff_one hb hX s k p
  have hInv := AVenhance.Infra.Section5.xFlowInv_joint_contDiff_one I hΦ m l
  have hembed : ContDiff ℝ 1
      (fun z : AmnrSpace => (z.1, I.xFlowInv hΦ m l z.1 z.2)) := contDiff_fst.prodMk hInv
  have hf := hJ.comp hembed
  have heq : (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2 k p) =
      amnrFlowJacobianEntry X s k p ∘ (fun z => (z.1, I.xFlowInv hΦ m l z.1 z.2)) := by
    funext z
    exact AVenhance.Infra.Section5.gradMatrix_entry_eq_fderiv
      ((AVenhance.Infra.Section5.xFlow_spatial_contDiff_two I hΦ m l z.1).differentiable
        (by norm_num) _) k p
  rw [heq]
  exact hf

/-- Eulerian material differentiation of the actual flow gradient follows
its variational equation, with the exact source row convention. -/
theorem amnr_flowGrad_material_equation {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (l : ℤ) (k p : Fin 2) (z : AmnrSpace) :
    amnrOp (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) none
      (fun y => I.flowGrad hΦ m l y.1 y.2 k p) z =
      ∑ q : Fin 2, I.flowGrad hΦ m l z.1 z.2 k q *
        amnrVelocityGradient (fun y => AVenhance.streamVel (Φ (m - 1)) y.1 y.2) p q z := by
  let b := AVenhance.streamVel (Φ (m - 1))
  let X := AVenhance.flow b (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz
  let s := (l : ℝ) * AVenhance.tauPP β I.Λ m
  let y := I.xFlowInv hΦ m l z.1 z.2
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)
  have hX : AVenhance.IsFlow b X := AVenhance.flow_isFlow b _ _
  have hxy : I.xFlow hΦ m l z.1 y = z.2 :=
    AVenhance.flowInv_rightInverse b _ _ z.1 s z.2
  have hc : HasDerivAt (fun r => I.xFlow hΦ m l r y) (b z.1 z.2) z.1 := by
    have hh := hX.2 y s z.1
    change HasDerivAt (fun r => I.xFlow hΦ m l r y)
      (b z.1 (I.xFlow hΦ m l z.1 y)) z.1 at hh
    rwa [hxy] at hh
  have hpair := (hasDerivAt_id z.1).prodMk hc
  have hf := (amnr_flowGrad_contDiff_one I hΦ m l k p).differentiable (by norm_num) z
  have heval : z = (z.1, I.xFlow hΦ m l z.1 y) := by rw [hxy]
  have hchain := hf.hasFDerivAt.comp_hasDerivAt_of_eq z.1 hpair heval
  have hvar := AVenhance.Infra.Section5.flowGrad_material_deriv_component I hΦ m l z.1 y k p
  rw [hxy] at hvar
  have he : amnrOp (fun y => b y.1 y.2) none
      (fun y => I.flowGrad hΦ m l y.1 y.2 k p) z =
      jointSpatialFDeriv b z.1 z.2 (fderiv ℝ (I.xFlow hΦ m l z.1) y (basisVec k)) p := by
    exact hchain.deriv.symm.trans hvar.deriv
  rw [he, jointSpatialFDeriv_eq_slice hb]
  have hbs : ContDiff ℝ (⊤ : ℕ∞) (b z.1) :=
    hb.smooth.comp (contDiff_const.prodMk contDiff_id)
  rw [AVenhance.Infra.Section5.fderiv_vector_component_eq_sum_gradMatrix
    (hbs.differentiable (by simp) z.2) p]
  apply Finset.sum_congr rfl
  intro q _
  have hentry : fderiv ℝ (I.xFlow hΦ m l z.1) y (basisVec k) q =
      I.flowGrad hΦ m l z.1 z.2 k q :=
    (AVenhance.Infra.Section5.gradMatrix_entry_eq_fderiv
      ((AVenhance.Infra.Section5.xFlow_spatial_contDiff_two I hΦ m l z.1).differentiable
        (by norm_num) y) k q).symm
  rw [hentry]
  rfl

end AVenhance.Infra.Section4
