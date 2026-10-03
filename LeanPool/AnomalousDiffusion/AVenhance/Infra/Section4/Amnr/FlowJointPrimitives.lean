/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SmoothInverse

/-! Actual jointly smooth spatial Jacobians and inverse-flow compositions. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow

/-- Spatial restriction of the actual joint derivative equals the actual
fixed-time spatial derivative, whenever the joint function is differentiable. -/
theorem amnrStateDerivative_eq_slice {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × E → F} {t : ℝ} {x : E} (hf : DifferentiableAt ℝ f (t, x)) :
    amnrStateDerivative f (t, x) = fderiv ℝ (fun y => f (t, y)) x := by
  exact (hf.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv.symm

/-- The actual pulled spatial flow Jacobian is jointly smooth on the same
short interval as the actual forward and inverse flow. -/
theorem amnr_pulledFlowJacobian_contDiffAt_of_short {b : ℝ → Vec 2 → Vec 2}
    (hb : SmoothPeriodicField b) {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {M : ℝ} (hM : 0 ≤ M) (hstate : ∀ t x, ‖jointSpatialFDeriv b t x‖ ≤ M)
    (s t : ℝ) (x : Vec 2) (hshort : |t - s| * M ≤ 1 / 4) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : ℝ × Vec 2 => fderiv ℝ (fun y => X z.1 y s) (X s z.2 z.1)) (t, x) := by
  let F := fun z : ℝ × Vec 2 => X z.1 z.2 s
  let R := fun z : ℝ × Vec 2 => (z.1, X s z.2 z.1)
  have hF : ContDiffAt ℝ (⊤ : ℕ∞) F (R (t, x)) :=
    amnr_flow_contDiffAt_joint_of_short hb hX hM hstate s t (X s x t) hshort
  have hR : ContDiffAt ℝ (⊤ : ℕ∞) R (t, x) :=
    contDiffAt_fst.prodMk (amnr_flow_inverse_contDiffAt_joint_of_short hb hX hM hstate s t x hshort)
  have hd := (amnrRestrictState (E := Vec 2) (F := Vec 2)).contDiff.contDiffAt.comp _
    ((hF.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).comp (t, x) hR)
  have hFc : ContDiff ℝ 1 F := (flow_joint_contDiff_one hb hX).comp
    (by fun_prop : ContDiff ℝ 1 (fun z : ℝ × Vec 2 => (z.1, z.2, s)))
  have he : amnrRestrictState ∘ (fderiv ℝ F ∘ R) =
      fun z : ℝ × Vec 2 => fderiv ℝ (fun y => X z.1 y s) (X s z.2 z.1) := by
    funext z
    exact amnrStateDerivative_eq_slice (hFc.differentiable (by norm_num) (R z))
  rwa [he] at hd

/-- Each actual source matrix entry inherits the actual pulled-Jacobian
joint smoothness, in the row convention. -/
theorem amnr_pulledFlowGradientEntry_contDiffAt_of_short {b : ℝ → Vec 2 → Vec 2}
    (hb : SmoothPeriodicField b) {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {M : ℝ} (hM : 0 ≤ M) (hstate : ∀ t x, ‖jointSpatialFDeriv b t x‖ ≤ M)
    (s t : ℝ) (x : Vec 2) (hshort : |t - s| * M ≤ 1 / 4) (i j : Fin 2) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : ℝ × Vec 2 => AVenhance.gradMatrix (fun y => X z.1 y s) (X s z.2 z.1) i j) (t, x) :=
          by
  have hJ := amnr_pulledFlowJacobian_contDiffAt_of_short hb hX hM hstate s t x hshort
  let P := amnrJacobianEntryProjection i j
  have hh := P.contDiff.contDiffAt.comp (t, x) hJ
  have he : P ∘ (fun z : ℝ × Vec 2 => fderiv ℝ (fun y => X z.1 y s) (X s z.2 z.1)) =
      fun z : ℝ × Vec 2 => AVenhance.gradMatrix (fun y => X z.1 y s) (X s z.2 z.1) i j := by
    funext z
    change (fderiv ℝ (fun y => X z.1 y s) (X s z.2 z.1) (basisVec i)) j =
      AVenhance.spaceGrad (fun y => X z.1 y s j) (X s z.2 z.1) i
    unfold AVenhance.spaceGrad
    rw [fderiv_apply ((flow_spatial_contDiff_one hb hX s z.1).differentiable (by norm_num) _) j]
    rfl
  rwa [he] at hh

end AVenhance.Infra.Section4
