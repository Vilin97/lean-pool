/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.Drift
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FlowPiolaDivergence

/-! The stream velocity is classically divergence-free, so its
inverse-flow cofactor Piola identity follows from the source sequence alone. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section5

open AVenhance

/-- The flow's trace divergence agrees with the classical divergence. -/
theorem spatialDivergence_eq_vecDiv
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    (t : ℝ) (x : Vec 2) :
    Infra.Flow.spatialDivergence b t x = vecDiv (b t) x := by
  rw [Infra.Flow.spatialDivergence,
    Infra.Flow.jointSpatialFDeriv_eq_slice hb]
  unfold vecDiv spaceGrad
  simp only [Fin.sum_univ_two]
  change (fderiv ℝ (fun y => b t y) x) (basisVec 0) 0 +
      (fderiv ℝ (fun y => b t y) x) (basisVec 1) 1 = _
  have hslice : DifferentiableAt ℝ (fun y => b t y) x := by
    have hcont : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => b t y) := by
      exact hb.smooth.comp (contDiff_const.prodMk contDiff_id)
    exact hcont.differentiable (by norm_num) x
  rw [fderiv_apply hslice 0, fderiv_apply hslice 1]
  simp [ContinuousLinearMap.comp_apply]

/-- Every predecessor stream has zero classical spatial divergence. -/
theorem streamVel_spatialDivergence_eq_zero
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) :
    ∀ t x, Infra.Flow.spatialDivergence (streamVel (Φ (m - 1))) t x = 0 := by
  let φ := Φ (m - 1)
  have hφ : IsAdmissibleStream φ := hΦ.adm_pred m
  have hb : Infra.Flow.SmoothPeriodicField (streamVel φ) :=
    Infra.Classical.streamVel_smoothPeriodic φ hφ
  intro t x
  rw [spatialDivergence_eq_vecDiv hb]
  exact Infra.Classical.streamVel_vecDiv_eq_zero φ hφ t x

/-- Full inverse-flow cofactor transport for the source flow. The
cofactor-divergence identity follows from the C² flow slice; determinant one
follows from Liouville and the divergence identity derived above. -/
theorem xFlowInv_cofactorPiola_of_streamSeq
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) (x : Vec 2)
    {g : Vec 2 → Vec 2} {Lg : Vec 2 →L[ℝ] Vec 2}
    (hg : HasFDerivAt g Lg (I.xFlowInv hΦ m l t x)) :
    vecDiv (fun y => (rowCofactor
        (gradMatrix (I.xFlowInv hΦ m l t) y)).mulVec
          (g (I.xFlowInv hΦ m l t y))) x =
      vecDiv g (I.xFlowInv hΦ m l t x) := by
  have hM : HasFDerivAt (I.xFlowInv hΦ m l t)
      (fderiv ℝ (I.xFlowInv hΦ m l t) x) x :=
    ((xFlowInv_spatial_contDiff_two I hΦ m l t).differentiable
      (by norm_num) x).hasFDerivAt
  rcases xFlowInv_cofactor_piolaInputs I hΦ m l t x with
    ⟨hQ, hPiolaDiv⟩
  exact xFlowInv_cofactorPiola I hΦ m l t x hM hg hQ hPiolaDiv
    (streamVel_spatialDivergence_eq_zero I hΦ m)

end AVenhance.Infra.Section5
