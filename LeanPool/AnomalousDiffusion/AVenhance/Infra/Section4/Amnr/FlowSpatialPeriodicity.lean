/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureFluxEvolution
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.Laws

/-! Spatial periodicity of the actual pulled flow Jacobian. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4

/-- Differentiating lattice equivariance makes the derivative periodic. -/
theorem amnr_fderiv_periodic_of_equivariant {X : Vec 2 → Vec 2}
    (hX : Differentiable ℝ X)
    (he : ∀ k x, X (x + AVenhance.latticeShift k) = X x + AVenhance.latticeShift k) :
    AVenhance.IsZ2Periodic (fderiv ℝ X) := by
  intro k x
  have hid : HasFDerivAt (fun y : Vec 2 => y + AVenhance.latticeShift k)
      (ContinuousLinearMap.id ℝ (Vec 2)) x := (hasFDerivAt_id x).add_const _
  have hc := (hX (x + AVenhance.latticeShift k)).hasFDerivAt.comp x hid
  have heq : (fun y => X (y + AVenhance.latticeShift k)) =
      (fun y => X y + AVenhance.latticeShift k) := funext (he k)
  rw [Function.comp_def, heq] at hc
  have hd := hc.fderiv
  simpa only [fderiv_add_const, ContinuousLinearMap.comp_id] using hd.symm

/-- Both actual flow maps are lattice equivariant by uniqueness of their
integral curves; the inverse uses the reversed time arguments. -/
theorem amnr_xFlow_lattice_equivariant {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (l : ℤ) (t : ℝ) (k : Fin 2 → ℤ) (x : Vec 2) :
    I.xFlow hΦ m l t (x + AVenhance.latticeShift k) =
      I.xFlow hΦ m l t x + AVenhance.latticeShift k := by
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)
  exact AVenhance.Infra.Flow.flow_lattice_equivariant _ (hΦ.adm_pred m).vel_lipschitz
    (fun s n y => by simpa using hb.periodic 0 n s y)
    (AVenhance.flow_isFlow _ (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz) x _ t k

theorem amnr_xFlowInv_lattice_equivariant {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (l : ℤ) (t : ℝ) (k : Fin 2 → ℤ) (x : Vec 2) :
    I.xFlowInv hΦ m l t (x + AVenhance.latticeShift k) =
      I.xFlowInv hΦ m l t x + AVenhance.latticeShift k := by
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)
  exact AVenhance.Infra.Flow.flow_lattice_equivariant _ (hΦ.adm_pred m).vel_lipschitz
    (fun s n y => by simpa using hb.periodic 0 n s y)
    (AVenhance.flow_isFlow _ (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz) x t _ k

/-- Pulling the periodic derivative through the equivariant inverse preserves
periodicity, with the row/column convention. -/
theorem amnr_flowGrad_spatial_periodic {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (l : ℤ) (t : ℝ) (i j : Fin 2) :
    AVenhance.IsZ2Periodic (fun x => I.flowGrad hΦ m l t x i j) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (I.xFlow hΦ m l t) :=
    (amnr_xFlow_joint_contDiff_infty I hΦ m l).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
  have hp := amnr_fderiv_periodic_of_equivariant (hs.differentiable (by simp))
    (fun k x => amnr_xFlow_lattice_equivariant I hΦ m l t k x)
  intro k x
  change fderiv ℝ (fun y => I.xFlow hΦ m l t y j)
      (I.xFlowInv hΦ m l t (x + AVenhance.latticeShift k)) (basisVec i) =
    fderiv ℝ (fun y => I.xFlow hΦ m l t y j)
      (I.xFlowInv hΦ m l t x) (basisVec i)
  rw [amnr_xFlowInv_lattice_equivariant I hΦ m l t k x]
  rw [fderiv_apply (hs.differentiable (by simp) _) j,
    fderiv_apply (hs.differentiable (by simp) _) j, hp k _]

end AVenhance.Infra.Section4
