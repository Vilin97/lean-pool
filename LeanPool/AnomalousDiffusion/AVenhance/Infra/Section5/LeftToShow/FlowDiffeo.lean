/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.XFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.XFlowInv
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowIsFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowInvLeftInverse
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowInvRightInverse
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.StreamAdmissible
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2FlowIdentities
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointSmoothFromFixedStart
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.Laws
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.MeasurePreservation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.Flow

/-! # The §4 flow slices as periodic volume-preserving diffeomorphisms

The flow slice `X_{m-1,l}(t,·)` (`Ingredients.xFlow`) with inverse `Ingredients.xFlowInv`
is packaged as an `Infra.Ergodic.PeriodicVolumePreservingDiffeomorphism 2`, the input of the
App C ergodic lemmas. -/

@[expose] public section

open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.LeftToShow

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem FlowDiffeo.streamFlowSmooth (hΦ : IsStreamSeq I Φ) (m : ℕ) :
    Infra.Flow.SmoothPeriodicField (streamVel (Φ (m - 1))) :=
  Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)

theorem FlowDiffeo.streamFlowIsFlow (hΦ : IsStreamSeq I Φ) (m : ℕ) :
    IsFlow (streamVel (Φ (m - 1)))
      (flow (streamVel (Φ (m - 1)))
        (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz) :=
  flow_isFlow _ _ _

theorem FlowDiffeo.streamFlowPeriodic (hΦ : IsStreamSeq I Φ) (m : ℕ) (t : ℝ) :
    IsZ2Periodic (streamVel (Φ (m - 1)) t) := by
  intro k x
  have h := (FlowDiffeo.streamFlowSmooth I hΦ m).periodic 0 k t x
  simpa using h

/-- Spatial slices `x ↦ X t x s` of the construction flow are `C^∞`. -/
theorem FlowDiffeo.streamFlow_slice_contDiff (hΦ : IsStreamSeq I Φ) (m : ℕ) (t s : ℝ) :
    ContDiff ℝ ∞ (fun x : Vec 2 =>
      flow (streamVel (Φ (m - 1))) (hΦ.adm_pred m).vel_continuous
        (hΦ.adm_pred m).vel_lipschitz t x s) := by
  have hmain := Infra.Flow.flow_joint_contDiff_infty
    (FlowDiffeo.streamFlowSmooth I hΦ m) (FlowDiffeo.streamFlowIsFlow I hΦ m)
  have hembed : ContDiff ℝ ∞ (fun x : Vec 2 => (t, x, s)) := by fun_prop
  exact hmain.comp hembed

/-- `X_{m-1,l}(t,·)` (`xFlow`) packaged for the App C ergodic lemmas. -/
noncomputable def xFlowDiffeo (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) :
    AVenhance.Infra.Ergodic.PeriodicVolumePreservingDiffeomorphism 2 where
  toFun := I.xFlow hΦ m l t
  invFun := I.xFlowInv hΦ m l t
  contDiff_toFun := FlowDiffeo.streamFlow_slice_contDiff I hΦ m t _
  contDiff_invFun := by
    have hmain := Infra.Flow.flow_joint_contDiff_infty
      (FlowDiffeo.streamFlowSmooth I hΦ m) (FlowDiffeo.streamFlowIsFlow I hΦ m)
    have hembed : ContDiff ℝ ∞ (fun x : Vec 2 => (((l : ℝ) * tauPP β I.Λ m), x, t)) := by
      fun_prop
    exact hmain.comp hembed
  left_inv := flowInv_leftInverse _ _ _ t _
  right_inv := flowInv_rightInverse _ _ _ t _
  lattice_equivariant := fun x k =>
    Infra.Flow.flow_lattice_equivariant _ (hΦ.adm_pred m).vel_lipschitz
      (FlowDiffeo.streamFlowPeriodic I hΦ m) (FlowDiffeo.streamFlowIsFlow I hΦ m) x _ t k
  measurePreserving :=
    Infra.Flow.flow_measurePreserving_of_divergence_free (FlowDiffeo.streamFlowSmooth I hΦ m)
      (FlowDiffeo.streamFlowIsFlow I hΦ m)
      (fun t' x => Infra.Construction.streamVel_spatialDivergence_eq_zero (hΦ.adm_pred m) t' x)
      _ t

@[simp] theorem xFlowDiffeo_toFun (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) :
    (xFlowDiffeo I hΦ m l t).toFun = I.xFlow hΦ m l t := rfl

@[simp] theorem xFlowDiffeo_invFun (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) :
    (xFlowDiffeo I hΦ m l t).invFun = I.xFlowInv hΦ m l t := rfl

theorem xFlowInv_lattice_equivariant (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ)
    (x : Vec 2) (k : Fin 2 → ℤ) :
    I.xFlowInv hΦ m l t (x + AVenhance.Infra.Ergodic.latticeVector k) =
      I.xFlowInv hΦ m l t x + AVenhance.Infra.Ergodic.latticeVector k :=
  Infra.Flow.flow_lattice_equivariant _ (hΦ.adm_pred m).vel_lipschitz
    (FlowDiffeo.streamFlowPeriodic I hΦ m) (FlowDiffeo.streamFlowIsFlow I hΦ m) x t _ k

end AVenhance.Infra.Section5.LeftToShow
