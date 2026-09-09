/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketPhysicalCoefficients
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketIntervalData
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section

/-! The actual scalar pressure gives a symmetric curvature operator.
Symmetry of the source history Hessian is consequently a theorem about
the constructed parent data, rather than an independent hypothesis. -/

noncomputable section

namespace EulerParentPacketFrames

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransverseFrameCoordinates EulerTimeIntervalRestriction
open scoped ContDiff

theorem hessian_isSymmetric (p : Space → ℝ) (hp : ContDiff ℝ 2 p) (x : Space) :
    (fderiv ℝ (gradient p) x).IsSymmetric := by
  have hd : DifferentiableAt ℝ (fderiv ℝ p) x :=
    ((hp.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero).differentiableAt
  have hg : fderiv ℝ (gradient p) x =
      (toDual ℝ Space).symm.toContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ p) x) :=
    ((toDual ℝ Space).symm.toContinuousLinearMap.hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  intro v w
  change ⟪fderiv ℝ (gradient p) x v,w⟫_ℝ = ⟪v,fderiv ℝ (gradient p) x w⟫_ℝ
  rw [hg]
  change ⟪(toDual ℝ Space).symm (fderiv ℝ (fderiv ℝ p) x v),w⟫_ℝ =
    ⟪v,(toDual ℝ Space).symm (fderiv ℝ (fderiv ℝ p) x w)⟫_ℝ
  calc
    _ = fderiv ℝ (fderiv ℝ p) x v w := toDual_symm_apply
    _ = fderiv ℝ (fderiv ℝ p) x w v := (hp.contDiffAt.isSymmSndFDerivAt (by simp)).eq v w
    _ = ⟪(toDual ℝ Space).symm (fderiv ℝ (fderiv ℝ p) x w),v⟫_ℝ := toDual_symm_apply.symm
    _ = _ := real_inner_comm _ _

namespace Parent

variable (G : Parent) (p : Icc (0 : ℝ) G.T → Space → ℝ)
  (hp : ∀ t, ContDiff ℝ ∞ (p t))
  (hacceleration : ∀ t x, G.acceleration.field t x = -(gradient (p t) (G.position t x)))

include hp hacceleration

theorem curvature_symmetric (t : Icc (0 : ℝ) G.T) (x : Space) :
    (G.curvature.field t x).IsSymmetric := by
  rw [G.curvature_physical (fun t => gradient (p t))
    (fun t x => ((EulerMeanSolenoidal.contDiff_gradient (hp t)).differentiable (by simp) x))
    hacceleration]
  exact hessian_isSymmetric (p t) ((hp t).of_le (by simp)) _

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖=1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (S : Set Space) (hS : IsCompact S) (H : LowBounds G)

theorem history_symmetric (t : Icc (0 : ℝ) G.T) (x : Space) :
    ((G.historyData m hm R S hS H).H.field t x).IsSymmetric :=
  G.curvature_symmetric p hp hacceleration t x

theorem initial_history_symmetric (τ : ℝ) (hτ : 0 < τ) (hτT : τ ≤ G.T)
    (t : Icc (0 : ℝ) τ) (x : Space) :
    (((G.historyData m hm R S hS H).initial τ hτ hτT).H.field t x).IsSymmetric :=
  G.curvature_symmetric p hp hacceleration (initialInclusion G.T τ hτT t) x

end Parent
end EulerParentPacketFrames
