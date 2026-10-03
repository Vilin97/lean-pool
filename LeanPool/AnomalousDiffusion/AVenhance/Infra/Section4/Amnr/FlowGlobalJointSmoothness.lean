/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowGlobalSpatialSmoothness

/-! Actual globally smooth inverse maps and source flow primitives. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow

/-- Actual inverse identities extend the global forward joint smoothness
to the actual inverse flow, at every target time and point. -/
theorem amnr_flow_inverse_joint_contDiff_infty_global {b : ℝ → Vec 2 → Vec 2}
    (hb : SmoothPeriodicField b) {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {M : ℝ} (hM : 0 ≤ M) (hstate : ∀ t x, ‖jointSpatialFDeriv b t x‖ ≤ M)
    (s : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Vec 2 => X s z.2 z.1) := by
  let P := fun z : ℝ × Vec 2 => (z.1, X z.1 z.2 s)
  let Q := fun z : ℝ × Vec 2 => (z.1, X s z.2 z.1)
  have hP : ContDiff ℝ (⊤ : ℕ∞) P :=
    contDiff_fst.prodMk (amnr_flow_joint_contDiff_infty_global hb hX hM hstate s)
  have hQi : ContDiff ℝ 1 (fun z : ℝ × Vec 2 => X s z.2 z.1) :=
    (flow_joint_contDiff_one hb hX).comp
      (by fun_prop : ContDiff ℝ 1 (fun z : ℝ × Vec 2 => (s, z.2, z.1)))
  have hQ : Differentiable ℝ Q := (contDiff_fst.prodMk hQi).differentiable (by norm_num)
  have hl : ∀ z, Q (P z) = z := fun z => Prod.ext rfl
    ((flow_fixed_time_maps_are_C1_inverses hb hX s z.1).2.2.1 z.2)
  have hr : ∀ z, P (Q z) = z := fun z => Prod.ext rfl
    ((flow_fixed_time_maps_are_C1_inverses hb hX s z.1).2.2.2 z.2)
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact contDiffAt_snd.comp z
    (amnr_contDiffAt_inverse_of_differentiable_inverses hP.contDiffAt (hQ z) hl hr)

/-- Every smooth periodic primitive field has a proved global Jacobian
bound, sufficient for the finite subdivision argument. -/
theorem amnr_smoothPeriodic_global_stateJacobian_bound {b : ℝ → Vec 2 → Vec 2}
    (hb : SmoothPeriodicField b) : ∃ M : ℝ, 0 ≤ M ∧ ∀ t x, ‖jointSpatialFDeriv b t x‖ ≤ M := by
  obtain ⟨M, hM, hMb⟩ := exists_global_iteratedFDeriv_bound hb 1
  refine ⟨M, hM, fun t x => ?_⟩
  simpa only [norm_iteratedFDeriv_zero, amnrStateDerivative_uncurry_eq] using
    amnrStateDerivative_iteratedFDeriv_norm_le hb.smooth 0 hMb (t, x)

/-- Qualitative joint smoothness of the actual source forward flow requires
only its proved admissible stream smoothness, without any quantitative stream-regularity input. -/
theorem amnr_xFlow_joint_contDiff_infty {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ) (m : ℕ) (l : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => I.xFlow hΦ m l z.1 z.2) := by
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)
  obtain ⟨M, hM, hMb⟩ := amnr_smoothPeriodic_global_stateJacobian_bound hb
  exact amnr_flow_joint_contDiff_infty_global hb
    (AVenhance.flow_isFlow _ (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz)
    hM hMb _

/-- The actual source inverse flow is jointly smooth at every time. -/
theorem amnr_xFlowInv_joint_contDiff_infty {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ) (m : ℕ) (l : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => I.xFlowInv hΦ m l z.1 z.2) := by
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)
  obtain ⟨M, hM, hMb⟩ := amnr_smoothPeriodic_global_stateJacobian_bound hb
  exact amnr_flow_inverse_joint_contDiff_infty_global hb
    (AVenhance.flow_isFlow _ (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz)
    hM hMb _

/-- The actual pulled source Jacobian is jointly smooth globally. Its
quantitative cutoff estimates are proved in separate declarations. -/
theorem amnr_flowGrad_joint_contDiff_infty {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ) (m : ℕ) (l : ℤ)
    (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2 i j) := by
  let F := fun z : AmnrSpace => I.xFlow hΦ m l z.1 z.2
  let R := fun z : AmnrSpace => (z.1, I.xFlowInv hΦ m l z.1 z.2)
  have hF := amnr_xFlow_joint_contDiff_infty I hΦ m l
  have hR : ContDiff ℝ (⊤ : ℕ∞) R := contDiff_fst.prodMk (amnr_xFlowInv_joint_contDiff_infty I hΦ
      m l)
  let P := amnrJacobianEntryProjection i j
  have hd := P.contDiff.comp ((amnrRestrictState (E := Vec 2) (F := Vec 2)).contDiff.comp
    ((hF.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).comp hR))
  have he : P ∘ (amnrRestrictState ∘ (fderiv ℝ F ∘ R)) =
      fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2 i j := by
    funext z
    have hslice := amnrStateDerivative_eq_slice (hF.differentiable (by simp) (R z))
    change P (amnrStateDerivative F (R z)) = _
    rw [hslice]
    change (fderiv ℝ (I.xFlow hΦ m l z.1) (I.xFlowInv hΦ m l z.1 z.2) (basisVec i)) j =
      AVenhance.spaceGrad (fun y => I.xFlow hΦ m l z.1 y j) (I.xFlowInv hΦ m l z.1 z.2) i
    unfold AVenhance.spaceGrad
    have hs : ContDiff ℝ (⊤ : ℕ∞) (I.xFlow hΦ m l z.1) := hF.comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (z.1, y)))
    rw [fderiv_apply (hs.differentiable (by simp) _) j]
    rfl
  rwa [he] at hd

end AVenhance.Infra.Section4
