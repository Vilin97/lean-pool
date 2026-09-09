/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketChildFieldMatch
public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerState

@[expose] public section

/-! Sharp whole-horizon low-order propagation for the actual child
fields. On good times only the negative part of f' can increase the
upper pressure bound; history and early times use the exponentially
small target ratio. No child low bound is assumed. -/

noncomputable section

namespace EulerPacketPhysicalLowBounds

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketPrimaryFactorization

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (H : HistoryData (D.initial τ hτ hτT.le)) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (a slope : ℝ)

theorem pressureTerm_eq_coefficient (t : Icc (0 : ℝ) D.T) (x : Space) :
    pressureTerm a slope (D.M.field t x) (D.normal.field t x)
      (canonicalVelocity τ hτ hτT H ξ hs t x) =
    (EulerPacketPrimaryPressure.coefficient τ hτ hτT H ξ hs a t x*slope) •
      rankOne ℝ (D.normal.field t x) (D.normal.field t x) := by
  unfold pressureTerm EulerPacketPrimaryPressure.coefficient
  congr 1
  ring

end EulerPacketPhysicalLowBounds

namespace EulerParentPacketFrames.Evolution

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerPacketSourceGeometry EulerPacketMovingFrame EulerPacketGeometryLowBounds
  EulerPacketPhysicalLowBounds EulerPacketPrimaryFactorization EulerPeriodicProfile
  EulerSpatialCutoffs EulerPacketTerminalDatum
open scoped ContDiff

variable {A : Parent} (E : Evolution A)

theorem strain_at_normalized_inverse (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.strain.field t (E.inverse.normalized t (A.ell⁻¹ • x)) =
      fderiv ℝ (fun y => E.velocity (t,y)) x := by
  rw [E.strain_eq]
  have hi : A.ell • E.inverse.normalized t (A.ell⁻¹ • x)=E.inverse.field t x := by
    simp only [ParticleInverse.normalized,Parent.packetInverse,
      projIcc_of_mem A.T_pos.le t.property,smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul]
  rw [hi,E.inverse.right_inverse]


theorem pressure_hessian_eq_force (t : Icc (0 : ℝ) A.T) (x : Space) :
    fderiv ℝ (gradient (fun y => E.pressure (t,y))) x=fderiv ℝ (E.force t) x := by
  rw [show gradient (fun y => E.pressure (t,y))=E.force t from funext (E.pressure_gradient t)]

theorem force_quadratic_upper_of_lowBounds (L : LowBounds A)
    (t : Icc (0 : ℝ) A.T) (x z : Space) :
    ⟪fderiv ℝ (E.force t) x z,z⟫_ℝ ≤ L.K*‖z‖^2 := by
  have hh := L.curvature_upper t (A.ell⁻¹ • E.inverse.field t x) z
  rw [E.curvature_eq] at hh
  simpa only [smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul,E.inverse.right_inverse] using hh

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖=1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {κ : ℝ} {hκ : |κ| ≤ 1} {Z R : FieldTower period A.T}
  (B : Budget period A.T_pos (correctionData (A.transverseData m hm J support hSupport) period κ hκ
    Z R))
  (residual : ApproximationResidual period A.T_pos
    (correctionData (A.transverseData m hm J support hSupport) period κ hκ Z R))
  (k : ℝ) (hk : k*κ=1)

include hk in
omit [CompleteSpace U] in
theorem exactPacket_derivative_split (t : Icc (0 : ℝ) A.T) (x : Space) :
    fderiv ℝ (fun y => A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field
      E.velocity (t,y)) x =
      fderiv ℝ (fun y => E.velocity (t,y)) x+
        fderiv ℝ (A.normalizedPacketVelocity m hm J support hSupport B residual k E.inverse t)
          (A.ell⁻¹ • x) ∧
    fderiv ℝ (gradient (fun y => A.exactPacketPressure m hm J support hSupport B residual k
      E.inverse.field E.pressure (t,y))) x =
      fderiv ℝ (E.force t) x+
        fderiv ℝ (gradient (A.normalizedPacketPressure m hm J support hSupport B residual k
          E.inverse t)) (A.ell⁻¹ • x) := by
  refine ⟨A.exactPacketVelocity_fderiv m hm J support hSupport B residual k E.inverse E.velocity t x
    ((E.velocity_smooth t).differentiable (by simp) x),?_⟩
  have hp1 : DifferentiableAt ℝ (gradient (fun y => E.pressure (t,y))) x := by
    rw [show gradient (fun y => E.pressure (t,y))=E.force t from funext (E.pressure_gradient t)]
    exact (E.force_smooth t).differentiable (by simp) x
  rw [A.exactPacketPressure_hessian m hm J support hSupport B residual k E.inverse hk E.pressure t x
    (E.pressure_differentiable t) hp1,E.pressure_hessian_eq_force]

variable {τ : ℝ} {hτ : 0 < τ} {hτT : τ < A.T}
  {F : ParentFrame (A.transverseData m hm J support hSupport) τ}
  {H : HistoryData ((A.transverseData m hm J support hSupport).initial τ hτ hτT.le)}
  (G : Guards hτ hτT F H) (hball : (1/2 : ℝ) ≤ G.radius)
  (hs : tsupport innerCutoff ⊆ support) (hδ : 0 < G.δ) (hδ1 : G.δ ≤ 1)

/-- The exact source (20) errors, expressed on the same normalized
packet that defines the physical child. These are precisely the two
errors supplied by the same-Q packet choice. -/
def SourceErrors (ev ep : ℝ) : Prop :=
  ∀ (t : Icc (0 : ℝ) A.T) (x : Space),
    ‖fderiv ℝ (A.normalizedPacketVelocity m hm J support hSupport B residual k E.inverse t) x-
      shearTerm (G.primaryAmplitude hball) (deriv (profile G.δ) (k*⟪m,E.inverse.normalized t x⟫_ℝ))
        ((A.transverseData m hm J support hSupport).normal.field t (E.inverse.normalized t x))
        (canonicalVelocity τ hτ hτT H G.terminal hs t (E.inverse.normalized t x))‖ ≤ ev ∧
    ‖fderiv ℝ (gradient (A.normalizedPacketPressure m hm J support hSupport B residual k E.inverse
      t)) x-
      pressureTerm (G.primaryAmplitude hball) (deriv (profile G.δ) (k*⟪m,E.inverse.normalized t
        x⟫_ℝ))
        ((A.transverseData m hm J support hSupport).M.field t (E.inverse.normalized t x))
        ((A.transverseData m hm J support hSupport).normal.field t (E.inverse.normalized t x))
        (canonicalVelocity τ hτ hτT H G.terminal hs t (E.inverse.normalized t x))‖ ≤ ep

/-- The literal strict errors returned by the global same-Q packet
theorem imply the error record without any additional analytic bound. -/
theorem sourceErrors_of_global (ev ep : ℝ)
    (herr : ∀ (t : Icc (0 : ℝ) A.T) (x : Space),
      ‖fderiv ℝ (A.normalizedPacketVelocity m hm J support hSupport B residual k E.inverse t) x-
        (G.primaryAmplitude hball*deriv (profile G.δ) (k*⟪m,E.inverse.normalized t x⟫_ℝ)) •
          rankOne ℝ (canonicalVelocity τ hτ hτT H G.terminal hs t (E.inverse.normalized t x))
            ((A.transverseData m hm J support hSupport).normal.field t (E.inverse.normalized t x))‖
              < ev ∧
      ‖fderiv ℝ (gradient (A.normalizedPacketPressure m hm J support hSupport B residual k
        E.inverse t)) x-
        (EulerPacketPrimaryPressure.coefficient τ hτ hτT H G.terminal hs (G.primaryAmplitude hball)
          t
            (E.inverse.normalized t x)*deriv (profile G.δ) (k*⟪m,E.inverse.normalized t x⟫_ℝ)) •
          rankOne ℝ ((A.transverseData m hm J support hSupport).normal.field t
            (E.inverse.normalized t x))
            ((A.transverseData m hm J support hSupport).normal.field t (E.inverse.normalized t x))‖
              < ep) :
    E.SourceErrors m hm J support hSupport B residual k G hball hs ev ep := by
  intro t x
  refine ⟨(herr t x).1.le,?_⟩
  erw [pressureTerm_eq_coefficient]
  exact (herr t x).2.le

include hk hδ hδ1 in
theorem exactPacket_good_low_bounds
    (ev ep CM CH Kupper : ℝ)
    (herr : E.SourceErrors m hm J support hSupport B residual k G hball hs ev ep)
    (t : Icc (0 : ℝ) A.T) (ht : 1 ≤ scaledTime τ F.a F.epsilon t) (x : Space)
    (hCM : ‖fderiv ℝ (fun y => E.velocity (t,y)) x‖ ≤ CM)
    (hCH : ‖fderiv ℝ (E.force t) x‖ ≤ CH)
    (hupper : ∀ z, ⟪fderiv ℝ (E.force t) x z,z⟫_ℝ ≤ Kupper*‖z‖^2) :
    ‖fderiv ℝ (fun y => A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field
      E.velocity (t,y)) x‖ ≤
      CM+G.hchild*goodRatio+ev ∧
    ‖fderiv ℝ (gradient (fun y => A.exactPacketPressure m hm J support hSupport B residual k
      E.inverse.field E.pressure (t,y))) x‖ ≤
      CH+2*CM*(G.hchild*goodRatio)+ep ∧
    ∀ z, ⟪fderiv ℝ (gradient (fun y => A.exactPacketPressure m hm J support hSupport B residual k
      E.inverse.field E.pressure (t,y))) x z,z⟫_ℝ ≤
      (Kupper+2*CM*G.δ*(G.hchild*goodRatio)+ep)*‖z‖^2 := by
  let y := E.inverse.normalized t (A.ell⁻¹ • x)
  have herr' := herr t (A.ell⁻¹ • x)
  have he := E.exactPacket_derivative_split m hm J support hSupport B residual k hk t x
  have hm' : (A.transverseData m hm J support hSupport).M.field t y=
      fderiv ℝ (fun y => E.velocity (t,y)) x := E.strain_at_normalized_inverse t x
  apply good_step_bounds _ _ _ _ ((A.transverseData m hm J support hSupport).M.field t y)
    ((A.transverseData m hm J support hSupport).normal.field t y)
    (canonicalVelocity τ hτ hτT H G.terminal hs t y)
    (G.primaryAmplitude hball) G.δ (k*⟪m,y⟫_ℝ) ev ep CM CM CH (G.hchild*goodRatio)
    (G.primaryAmplitude_nonneg hball) hδ hδ1
  · simpa only [mul_assoc] using G.good_primary_size hball t ht y hs
  · rw [hm']; exact hCM
  · exact hCM
  · exact hCH
  · rw [he.1,add_sub_cancel_left]
    exact herr'.1
  · rw [he.2,add_sub_cancel_left]
    exact herr'.2
  · exact G.good_primary_flux hball t ht y hs
  · exact hupper

include hk hδ hδ1 in
theorem exactPacket_bad_low_bounds
    (ev ep CM CH Kupper : ℝ)
    (herr : E.SourceErrors m hm J support hSupport B residual k G hball hs ev ep)
    (t : Icc (0 : ℝ) A.T) (ht : scaledTime τ F.a F.epsilon t ≤ 1) (x : Space)
    (hCM : ‖fderiv ℝ (fun y => E.velocity (t,y)) x‖ ≤ CM)
    (hCH : ‖fderiv ℝ (E.force t) x‖ ≤ CH)
    (hupper : ∀ z, ⟪fderiv ℝ (E.force t) x z,z⟫_ℝ ≤ Kupper*‖z‖^2) :
    ‖fderiv ℝ (fun y => A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field
      E.velocity (t,y)) x‖ ≤
      CM+G.hchild*G.badRatio+ev ∧
    ‖fderiv ℝ (gradient (fun y => A.exactPacketPressure m hm J support hSupport B residual k
      E.inverse.field E.pressure (t,y))) x‖ ≤
      CH+2*CM*(G.hchild*G.badRatio)+ep ∧
    ∀ z, ⟪fderiv ℝ (gradient (fun y => A.exactPacketPressure m hm J support hSupport B residual k
      E.inverse.field E.pressure (t,y))) x z,z⟫_ℝ ≤
      (Kupper+2*CM*(G.hchild*G.badRatio)+ep)*‖z‖^2 := by
  let y := E.inverse.normalized t (A.ell⁻¹ • x)
  have herr' := herr t (A.ell⁻¹ • x)
  have he := E.exactPacket_derivative_split m hm J support hSupport B residual k hk t x
  have hm' : (A.transverseData m hm J support hSupport).M.field t y=
      fderiv ℝ (fun y => E.velocity (t,y)) x := E.strain_at_normalized_inverse t x
  apply absolute_step_bounds _ _ _ _ ((A.transverseData m hm J support hSupport).M.field t y)
    ((A.transverseData m hm J support hSupport).normal.field t y)
    (canonicalVelocity τ hτ hτT H G.terminal hs t y)
    (G.primaryAmplitude hball) G.δ (k*⟪m,y⟫_ℝ) ev ep CM CM CH (G.hchild*G.badRatio)
    (G.primaryAmplitude_nonneg hball) hδ hδ1
  · simpa only [mul_assoc] using G.bad_primary_size hball t ht y hs
  · rw [hm']; exact hCM
  · exact hCM
  · exact hCH
  · rw [he.1,add_sub_cancel_left]
    exact herr'.1
  · rw [he.2,add_sub_cancel_left]
    exact herr'.2
  · exact hupper

include hk hδ hδ1 in
/-- The full horizon has one fixed absolute-size cost, while the upper
pressure cost retains delta on good times and the exponentially small
bad-time ratio. The parent constants remain the actual sharp CM and CH. -/
theorem exactPacket_whole_horizon_low_bounds
    (ev ep CM CH Kupper : ℝ)
    (herr : E.SourceErrors m hm J support hSupport B residual k G hball hs ev ep)
    (hCM : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (fun y => E.velocity (t,y)) x‖ ≤ CM)
    (hCH : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (E.force t) x‖ ≤ CH)
    (hupper : ∀ (t : Icc (0 : ℝ) A.T) x z, ⟪fderiv ℝ (E.force t) x z,z⟫_ℝ ≤ Kupper*‖z‖^2)
    (t : Icc (0 : ℝ) A.T) (x : Space) :
    ‖fderiv ℝ (fun y => A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field
      E.velocity (t,y)) x‖ ≤
      CM+G.hchild*(goodRatio+G.badRatio)+ev ∧
    ‖fderiv ℝ (gradient (fun y => A.exactPacketPressure m hm J support hSupport B residual k
      E.inverse.field E.pressure (t,y))) x‖ ≤
      CH+2*CM*G.hchild*(goodRatio+G.badRatio)+ep ∧
    ∀ z, ⟪fderiv ℝ (gradient (fun y => A.exactPacketPressure m hm J support hSupport B residual k
      E.inverse.field E.pressure (t,y))) x z,z⟫_ℝ ≤
      (Kupper+2*CM*G.hchild*(G.δ*goodRatio+G.badRatio)+ep)*‖z‖^2 := by
  have hCM0 : 0 ≤ CM := (norm_nonneg _).trans (hCM t x)
  have hchild := G.child_nonneg
  have hbad := G.badRatio_nonneg
  have hgood := goodRatio_pos.le
  by_cases ht : 1 ≤ scaledTime τ F.a F.epsilon t
  · obtain ⟨hv,hp,hq⟩ := E.exactPacket_good_low_bounds m hm J support hSupport B residual k hk
      G hball hs hδ hδ1 ev ep CM CH Kupper herr t ht x (hCM t x) (hCH t x) (hupper t x)
    refine ⟨hv.trans ?_,hp.trans ?_,fun z => (hq z).trans ?_⟩
    · nlinarith only [mul_nonneg hchild hbad]
    · nlinarith only [mul_nonneg (mul_nonneg hCM0 hchild) hbad]
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      nlinarith only [mul_nonneg (mul_nonneg hCM0 hchild) hbad]
  · obtain ⟨hv,hp,hq⟩ := E.exactPacket_bad_low_bounds m hm J support hSupport B residual k hk
      G hball hs hδ hδ1 ev ep CM CH Kupper herr t (le_of_not_ge ht) x (hCM t x) (hCH t x) (hupper t
        x)
    refine ⟨hv.trans ?_,hp.trans ?_,fun z => (hq z).trans ?_⟩
    · nlinarith only [mul_nonneg hchild hgood]
    · nlinarith only [mul_nonneg (mul_nonneg hCM0 hchild) hgood]
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      nlinarith only [mul_nonneg (mul_nonneg (mul_nonneg hCM0 hchild) G.delta_nonneg) hgood]

end EulerParentPacketFrames.Evolution
