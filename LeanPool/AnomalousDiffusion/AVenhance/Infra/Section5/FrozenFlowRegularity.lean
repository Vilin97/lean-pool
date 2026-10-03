/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.StreamAdmissible
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointC1
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.InverseC1
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SpatialC2
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SpatialC3
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.XFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.XFlowInv
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowIsFlow

/-! Joint first-order regularity for the §4 flow slices. -/

@[expose] public section

open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem FrozenFlowRegularity.streamFlowSmooth
    (hΦ : IsStreamSeq I Φ) (m : ℕ) :
    Infra.Flow.SmoothPeriodicField (streamVel (Φ (m - 1))) :=
  Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)

theorem FrozenFlowRegularity.streamFlowIsFlow
    (hΦ : IsStreamSeq I Φ) (m : ℕ) :
    IsFlow (streamVel (Φ (m - 1)))
      (flow (streamVel (Φ (m - 1)))
        (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz) :=
  flow_isFlow _ _ _

/-- The inverse flow slice is jointly C¹ in target time and position. -/
theorem xFlowInv_joint_contDiff_one
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) :
    ContDiff ℝ 1 (fun p : ℝ × Vec 2 =>
      I.xFlowInv hΦ m l p.1 p.2) := by
  let b := streamVel (Φ (m - 1))
  let X := flow b (hΦ.adm_pred m).vel_continuous
    (hΦ.adm_pred m).vel_lipschitz
  let s := (l : ℝ) * tauPP β I.Λ m
  let embed : ℝ × Vec 2 → ℝ × Vec 2 × ℝ := fun p => (p.1, p.2, s)
  have hembed : ContDiff ℝ 1 embed := by fun_prop
  have hmain := Infra.Flow.flow_inverse_joint_contDiff_one
    (FrozenFlowRegularity.streamFlowSmooth I hΦ m) (FrozenFlowRegularity.streamFlowIsFlow I hΦ m)
  have hcomp := hmain.comp hembed
  simpa [Ingredients.xFlowInv, AVenhance.flowInv, b, X, s, embed,
    Function.comp_def] using hcomp

/-- The joint Fréchet derivative needed by the inverse-flow transport rule is
provided by the flow definitions and the smoothness of the preceding
admissible stream. -/
theorem xFlowInv_hasFDerivAt
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) (x : Vec 2) :
    HasFDerivAt (Function.uncurry fun s y => I.xFlowInv hΦ m l s y)
      (fderiv ℝ (Function.uncurry fun s y => I.xFlowInv hΦ m l s y) (t, x))
      (t, x) := by
  exact ((xFlowInv_joint_contDiff_one I hΦ m l).differentiable
    (by norm_num) (t, x)).hasFDerivAt

/-- Every forward flow slice is C² in the initial spatial point. -/
theorem xFlow_spatial_contDiff_two
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) :
    ContDiff ℝ 2 (I.xFlow hΦ m l t) := by
  let b := streamVel (Φ (m - 1))
  let X := flow b (hΦ.adm_pred m).vel_continuous
    (hΦ.adm_pred m).vel_lipschitz
  let s := (l : ℝ) * tauPP β I.Λ m
  change ContDiff ℝ 2 (fun x => X t x s)
  exact Infra.Flow.flow_spatial_contDiff_two
    (FrozenFlowRegularity.streamFlowSmooth I hΦ m) (FrozenFlowRegularity.streamFlowIsFlow I hΦ m)
        s t

/-- Every inverse flow slice is C² in the spatial point. -/
theorem xFlowInv_spatial_contDiff_two
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) :
    ContDiff ℝ 2 (I.xFlowInv hΦ m l t) := by
  let b := streamVel (Φ (m - 1))
  let X := flow b (hΦ.adm_pred m).vel_continuous
    (hΦ.adm_pred m).vel_lipschitz
  let s := (l : ℝ) * tauPP β I.Λ m
  change ContDiff ℝ 2 (fun x => X s x t)
  exact Infra.Flow.flow_spatial_contDiff_two
    (FrozenFlowRegularity.streamFlowSmooth I hΦ m) (FrozenFlowRegularity.streamFlowIsFlow I hΦ m)
        t s

/-- Every forward flow slice is C³ in its initial spatial point. -/
theorem xFlow_spatial_contDiff_three
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) :
    ContDiff ℝ 3 (I.xFlow hΦ m l t) := by
  let b := streamVel (Φ (m - 1))
  let X := flow b (hΦ.adm_pred m).vel_continuous
    (hΦ.adm_pred m).vel_lipschitz
  let s := (l : ℝ) * tauPP β I.Λ m
  change ContDiff ℝ 3 (fun x => X t x s)
  exact Infra.Flow.flow_spatial_contDiff_three
    (FrozenFlowRegularity.streamFlowSmooth I hΦ m) (FrozenFlowRegularity.streamFlowIsFlow I hΦ m)
        s t

/-- Every inverse flow slice is C³ in its spatial point. -/
theorem xFlowInv_spatial_contDiff_three
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) :
    ContDiff ℝ 3 (I.xFlowInv hΦ m l t) := by
  let b := streamVel (Φ (m - 1))
  let X := flow b (hΦ.adm_pred m).vel_continuous
    (hΦ.adm_pred m).vel_lipschitz
  let s := (l : ℝ) * tauPP β I.Λ m
  change ContDiff ℝ 3 (fun x => X s x t)
  exact Infra.Flow.flow_spatial_contDiff_three
    (FrozenFlowRegularity.streamFlowSmooth I hΦ m) (FrozenFlowRegularity.streamFlowIsFlow I hΦ m)
        t s

end AVenhance.Infra.Section5
