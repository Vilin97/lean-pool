/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentGeometryChoiceCenter
public import LeanPool.NavierStokesAndEuler.Euler.ParentTargetRenewal

@[expose] public section

/-! Actual frame renewal for the very correction and flow chosen by
the geometric packet factories. Center source matching is derived. -/

noncomputable section

namespace EulerParentPacketFrames.Evolution

open Set EulerSmoothLimit EulerVolterraConvolution

variable {A : Parent} (E : Evolution A)

theorem centerStrain_bound (CM : ℝ)
    (hCM : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (fun y => E.velocity (t,y)) x‖ ≤ CM)
    (t : ℝ) : ‖A.centerStrain t‖ ≤ CM := by
  change ‖A.strain.field (projIcc 0 A.T A.T_pos.le t) 0‖ ≤ CM
  rw [E.strain_eq]
  exact hCM _ _

theorem centerCurvature_bound (CH : ℝ)
    (hCH : ∀ (t : Icc (0 : ℝ) A.T) x, ‖fderiv ℝ (E.force t) x‖ ≤ CH)
    (t : ℝ) : ‖A.centerCurvature t‖ ≤ CH := by
  change ‖A.curvature.field (projIcc 0 A.T A.T_pos.le t) 0‖ ≤ CH
  rw [E.curvature_eq]
  exact hCH _ _

end EulerParentPacketFrames.Evolution

namespace EulerParentPacketFrames.GeometryForwardChoice

open Set Real InnerProductSpace EulerSmoothLimit EulerTransverseFrameCoordinates
  EulerPacketSourceGeometry EulerPacketTerminalDatum EulerPacketSourceFrequency
  EulerPacketMovingFrame EulerPacketNormalizedPrimary

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {I : GeometryForwardInput U} {S : SmoothState I.parent}
  {k : ℝ} {hk : UniversalFrequency k}
  {nextEll : ℝ} {hnext : 0 < nextEll} {hnext1 : nextEll ≤ 1}
  (F : GeometryForwardChoice I S k hk nextEll hnext hnext1)
  (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support)
  (CM CH K : ℝ) (hCM0 : 0 ≤ CM) (hK : 1 ≤ K) (hMK : CM ≤ K) (hHK : CM^2+CH ≤ K^2)
  (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t,y)) x‖ ≤ CM)
  (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (m : Space) (hm : ‖m‖=1) (R : V ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)

def renewal : ParentFrame (F.parent.transverseData m hm R support hSupport)
    (I.geometry.lowGeometry I.halfBall).targetTime :=
  S.forwardTargetRenewal (state I S k hk nextEll hnext hnext1 F hSym) rfl
    I.normal I.normal_unit I.coordinates I.support I.support_compact
    m hm R support hSupport I.geometry I.halfBall CM CH K (k^(-(1/4 : ℝ)))
    hCM0 hK (rpow_nonneg hk.pos.le _) hMK hHK
    (fun t _ => S.evolution.centerStrain_bound CM hCM t)
    (fun t _ => S.evolution.centerCurvature_bound CH hCH t)
    I.delta_pos k (fun t _ => center_error I S k hk nextEll hnext hnext1 F hSym t)

local notation "Pnew" => F.renewal hSym CM CH K hCM0 hK hMK hHK hCM hCH m hm R support hSupport

theorem renewal_matches : RenewalAtTarget (I.geometry.lowGeometry I.halfBall) Pnew := by
  unfold renewal
  apply SmoothState.forwardTargetRenewal_matches

theorem renewal_costs : (Pnew).G=K ∧ (Pnew).error=k^(-(1/4 : ℝ)) := ⟨rfl,rfl⟩

theorem renewal_parameters (hTilt : (I.geometry.lowGeometry I.halfBall).tiltError ≤ 1/2) :
    (Pnew).shear=I.geometry.hchild ∧ 0 < (Pnew).a ∧
    |(Pnew).a/I.frame.a-1| ≤ (I.geometry.lowGeometry I.halfBall).couplingError ∧
    0 < (Pnew).sigma ∧
    |(I.geometry.y⁻¹)^2*(Pnew).sigma^2-1| ≤ (I.geometry.lowGeometry I.halfBall).tiltError := by
  have H := F.renewal_matches hSym CM CH K hCM0 hK hMK hHK hCM hCH m hm R support hSupport
  exact ⟨H.shear_eq I.delta_pos,H.coupling_pos,H.coupling_error,H.sigma_pos hTilt,H.tilt_error
    hTilt⟩

theorem renewal_compression (e : ℝ) (he : e ≤ 1) :
    ⟪(Pnew).B (I.geometry.lowGeometry I.halfBall).targetTime
      (unit ((Pnew).m (I.geometry.lowGeometry I.halfBall).targetTime)),
      unit ((Pnew).m (I.geometry.lowGeometry I.halfBall).targetTime)⟫_ℝ+e < 0 := by
  have H := F.renewal_matches hSym CM CH K hCM0 hK hMK hHK hCM hCH m hm R support hSupport
  rw [H.background_compression_eq]
  have hm := (I.geometry.lowGeometry I.halfBall).compression_margin he
  have hc := (I.geometry.lowGeometry I.halfBall).nextCompression_le
  linarith only [hm,hc]

end EulerParentPacketFrames.GeometryForwardChoice

namespace EulerParentPacketFrames.GeometryJoinedChoice

open Set Real InnerProductSpace EulerSmoothLimit EulerTransverseFrameCoordinates
  EulerPacketSourceGeometry EulerPacketTerminalDatum EulerPacketSourceFrequency
  EulerPacketMovingFrame EulerPacketNormalizedPrimary

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {I : EulerPacketInitial.Input U} {S : SmoothState I.parent}
  {k : ℝ} {hk : UniversalFrequency k}
  {nextEll : ℝ} {hnext : 0 < nextEll} {hnext1 : nextEll ≤ 1}
  (F : GeometryJoinedChoice I S k hk nextEll hnext hnext1)
  (hSym : ∀ x, -x ∈ I.support ↔ x ∈ I.support)
  (CM CH K : ℝ) (hCM0 : 0 ≤ CM) (hK : 1 ≤ K) (hMK : CM ≤ K) (hHK : CM^2+CH ≤ K^2)
  (hCM : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (fun y => S.evolution.velocity (t,y)) x‖ ≤ CM)
  (hCH : ∀ (t : Icc (0 : ℝ) I.parent.T) x, ‖fderiv ℝ (S.evolution.force t) x‖ ≤ CH)
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (m : Space) (hm : ‖m‖=1) (R : V ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)

def renewal : ParentFrame (F.parent.transverseData m hm R support hSupport)
    (I.geometry.lowGeometry I.halfBall).targetTime :=
  S.joinedTargetRenewal (state I S k hk nextEll hnext hnext1 F hSym) rfl
    I.normal I.normal_unit I.coordinates I.support I.support_compact
    m hm R support hSupport I.historyTime I.history_pos I.history_lt I.history I.geometry I.halfBall
    I.cutoff_support CM CH K (k^(-(1/4 : ℝ)))
    hCM0 hK (rpow_nonneg hk.pos.le _) hMK hHK
    (fun t _ => S.evolution.centerStrain_bound CM hCM t)
    (fun t _ => S.evolution.centerCurvature_bound CH hCH t)
    I.delta_pos k (fun t _ => center_error I S k hk nextEll hnext hnext1 F hSym t)

local notation "Pnew" => F.renewal hSym CM CH K hCM0 hK hMK hHK hCM hCH m hm R support hSupport

theorem renewal_matches : RenewalAtTarget (I.geometry.lowGeometry I.halfBall) Pnew := by
  unfold renewal
  apply SmoothState.joinedTargetRenewal_matches

theorem renewal_costs : (Pnew).G=K ∧ (Pnew).error=k^(-(1/4 : ℝ)) := ⟨rfl,rfl⟩

theorem renewal_parameters (hTilt : (I.geometry.lowGeometry I.halfBall).tiltError ≤ 1/2) :
    (Pnew).shear=I.geometry.hchild ∧ 0 < (Pnew).a ∧
    |(Pnew).a/I.frame.a-1| ≤ (I.geometry.lowGeometry I.halfBall).couplingError ∧
    0 < (Pnew).sigma ∧
    |(I.geometry.y⁻¹)^2*(Pnew).sigma^2-1| ≤ (I.geometry.lowGeometry I.halfBall).tiltError := by
  have H := F.renewal_matches hSym CM CH K hCM0 hK hMK hHK hCM hCH m hm R support hSupport
  exact ⟨H.shear_eq I.delta_pos,H.coupling_pos,H.coupling_error,H.sigma_pos hTilt,H.tilt_error
    hTilt⟩

theorem renewal_compression (e : ℝ) (he : e ≤ 1) :
    ⟪(Pnew).B (I.geometry.lowGeometry I.halfBall).targetTime
      (unit ((Pnew).m (I.geometry.lowGeometry I.halfBall).targetTime)),
      unit ((Pnew).m (I.geometry.lowGeometry I.halfBall).targetTime)⟫_ℝ+e < 0 := by
  have H := F.renewal_matches hSym CM CH K hCM0 hK hMK hHK hCM hCH m hm R support hSupport
  rw [H.background_compression_eq]
  have hm := (I.geometry.lowGeometry I.halfBall).compression_margin he
  have hc := (I.geometry.lowGeometry I.halfBall).nextCompression_le
  linarith only [hm,hc]

end EulerParentPacketFrames.GeometryJoinedChoice
