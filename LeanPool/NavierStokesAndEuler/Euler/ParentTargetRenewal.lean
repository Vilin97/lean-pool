/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentRenewalParameters
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardGeometryLowBounds

@[expose] public section

/-! The geometric target of the actual forward or joined primary is the
activation time of the next parent frame. These factories are the checked
`SmoothState` renewals with the source-selected amplitude and primary;
all target matching is proved from their definitions. -/

noncomputable section

namespace EulerParentPacketFrames.SmoothState

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerSpatialCutoffs EulerPeriodicProfile
  EulerPacketMovingFrame EulerPacketNormalizedPrimary

variable {A N : Parent} (S : SmoothState A) (T : SmoothState N) (hTime : N.T=A.T)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖=1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (mNext : Space) (hmNext : ‖mNext‖=1) (JNext : V ≃ₗᵢ[ℝ] referencePlane mNext)
  (supportNext : Set Space) (hSupportNext : IsCompact supportNext)

local notation "D" => A.transverseData m hm J support hSupport
local notation "DNext" => N.transverseData mNext hmNext JNext supportNext hSupportNext

section Forward

variable {P : ParentFrame (A.transverseData m hm J support hSupport) 0} (G : ForwardGuards P)
  (hball : (1/2 : ℝ) ≤ G.radius)

local notation "Geo" => ForwardGuards.lowGeometry G hball
local notation "tNext" => PhysicalGeometryData.targetTime (ForwardGuards.lowGeometry G hball)

variable (CM CH K error : ℝ) (hCM : 0 ≤ CM) (hK : 1 ≤ K) (he : 0 ≤ error)
  (hMK : CM ≤ K) (hHK : CM^2+CH ≤ K^2)
  (hM : ∀ t ∈ Icc (G.lowGeometry hball).targetTime N.T, ‖A.centerStrain t‖ ≤ CM)
  (hH : ∀ t ∈ Icc (G.lowGeometry hball).targetTime N.T, ‖A.centerCurvature t‖ ≤ CH)
  (hδ : 0 < G.δ) (k : ℝ)
  (hsource : ∀ t : Icc (0 : ℝ) A.T, (G.lowGeometry hball).targetTime ≤ (t : ℝ) →
    ‖fderiv ℝ (S.velocityIncrement T t) 0-
      (G.primaryAmplitude hball*deriv (profile G.δ)
        (k*⟪m,S.evolution.inverse.normalized t 0⟫_ℝ)) •
        rankOne ℝ (EulerPacketForwardFactorization.canonicalVelocity
          (A.transverseData m hm J support hSupport) G.initialCoordinate t
            (S.evolution.inverse.normalized t 0))
          ((A.transverseData m hm J support hSupport).normal.field t
            (S.evolution.inverse.normalized t 0))‖ ≤ error)

/-- The next actual frame, using exactly the forward source primary and
its target-normalized amplitude. -/
def forwardTargetRenewal : ParentFrame DNext tNext :=
  S.forwardRenewal T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext
    tNext ((G.lowGeometry hball).target_time_mem).1 CM CH K error
    hCM hK he hMK hHK hM hH G.δ hδ (G.primaryAmplitude hball) k
    G.initialCoordinate G.initialCoordinate_ne_zero hsource

local notation "Q" => forwardTargetRenewal S T hTime m hm J support hSupport
  mNext hmNext JNext supportNext hSupportNext G hball CM CH K error
  hCM hK he hMK hHK hM hH hδ k hsource

/-- In particular, the new ray and primary are the old source's actual
physical ray and primary at the target, not freely chosen frame vectors. -/
theorem forwardTargetRenewal_matches : RenewalAtTarget Geo Q := by
  let t : Icc (0 : ℝ) A.T := ⟨tNext,(G.lowGeometry hball).target_time_mem⟩
  constructor
  · change A.centerStrain t = (D).M.field ((D).clamp (t : ℝ)) 0
    rw [Data.clamp_coe D t]
    exact (A.source_strain_eq m hm J support hSupport t).symm
  · change A.sourceNormal m t = (D).normal.field ((D).clamp (t : ℝ)) 0
    rw [Data.clamp_coe D t]
    exact (A.source_normal_eq m hm J support hSupport t).symm
  · rfl
  · rfl

theorem forwardTargetRenewal_shear : (Q).shear=G.hchild :=
  (forwardTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext G hball CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource).shear_eq hδ

theorem forwardTargetRenewal_constants : (Q).G=K ∧ (Q).error=error := ⟨rfl,rfl⟩

include hTime hCM hK he hMK hHK hM hH hδ hsource in
theorem forwardTargetRenewal_remainder (hT : tNext ≤ N.T) :
    ‖(DNext).M.field ((DNext).clamp tNext) 0-(Geo).M (Geo).center tNext-
      G.hchild • rankOne ℝ (unit ((Geo).w (Geo).center tNext))
        (unit ((Geo).r (Geo).center tNext))‖ ≤ error := by
  have H := forwardTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext G hball CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact H.target_remainder hδ hT

theorem forwardTargetRenewal_parameters (hTilt : (Geo).tiltError ≤ 1/2) :
    (Q).shear=G.hchild ∧ 0 < (Q).a ∧
    |(Q).a/P.a-1| ≤ (Geo).couplingError ∧
    0 < (Q).sigma ∧
    |(G.y⁻¹)^2*(Q).sigma^2-1| ≤ (Geo).tiltError ∧
    1/2 ≤ (G.y⁻¹)^2*(Q).sigma^2 ∧ (G.y⁻¹)^2*(Q).sigma^2 ≤ 3/2 := by
  have H := forwardTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext G hball CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact ⟨H.shear_eq hδ,H.coupling_pos,H.coupling_error,H.sigma_pos hTilt,
    H.tilt_error hTilt,H.tilt_interval hTilt⟩

theorem forwardTargetRenewal_compression
    (ht : 0 < tNext) (hT : tNext < N.T)
    (hmargin : 3*((Geo).G+(Geo).d)+error < (Geo).compressionScale) :
    ⟪(DNext).M.field ⟨tNext,ht.le,hT.le⟩ 0 (unit ((Q).m tNext)),
      unit ((Q).m tNext)⟫_ℝ < 0 := by
  have H := forwardTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext G hball CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact H.activation_compression ht hT hmargin

theorem forwardTargetRenewal_compression_of_error_le_one
    (hT : tNext < N.T) (herror : error ≤ 1) :
    ⟪(DNext).M.field ⟨tNext,(Geo).targetTime_pos le_rfl |>.le,hT.le⟩ 0
      (unit ((Q).m tNext)),unit ((Q).m tNext)⟫_ℝ < 0 := by
  have H := forwardTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext G hball CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact H.activation_compression_of_error_le_one ((Geo).targetTime_pos le_rfl) hT herror

end Forward

section Joined

variable (s : ℝ) (hs : 0 < s) (hsT : s < A.T)
  (H : HistoryData ((A.transverseData m hm J support hSupport).initial s hs hsT.le))
  {P : ParentFrame (A.transverseData m hm J support hSupport) s}
  (G : Guards hs hsT P H) (hball : (1/2 : ℝ) ≤ G.radius)
  (hcut : tsupport innerCutoff ⊆ support)

local notation "Geo" => Guards.lowGeometry G hball
local notation "tNext" => PhysicalGeometryData.targetTime (Guards.lowGeometry G hball)

variable (CM CH K error : ℝ) (hCM : 0 ≤ CM) (hK : 1 ≤ K) (he : 0 ≤ error)
  (hMK : CM ≤ K) (hHK : CM^2+CH ≤ K^2)
  (hM : ∀ t ∈ Icc (G.lowGeometry hball).targetTime N.T, ‖A.centerStrain t‖ ≤ CM)
  (hH : ∀ t ∈ Icc (G.lowGeometry hball).targetTime N.T, ‖A.centerCurvature t‖ ≤ CH)
  (hδ : 0 < G.δ) (k : ℝ)
  (hsource : ∀ t : Icc (0 : ℝ) A.T, (G.lowGeometry hball).targetTime ≤ (t : ℝ) →
    ‖fderiv ℝ (S.velocityIncrement T t) 0-
      (G.primaryAmplitude hball*deriv (profile G.δ)
        (k*⟪m,S.evolution.inverse.normalized t 0⟫_ℝ)) •
        rankOne ℝ (EulerPacketPrimaryFactorization.canonicalVelocity
          s hs hsT H G.terminal hcut t (S.evolution.inverse.normalized t 0))
          ((A.transverseData m hm J support hSupport).normal.field t
            (S.evolution.inverse.normalized t 0))‖ ≤ error)

/-- The joined renewal retains the activation-selected endpoint and
its actual stationary-history initial trace. -/
def joinedTargetRenewal : ParentFrame DNext tNext :=
  S.joinedRenewal T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext
    tNext (hs.le.trans ((G.lowGeometry hball).target_time_mem).1) CM CH K error
    hCM hK he hMK hHK hM hH G.δ hδ (G.primaryAmplitude hball) k
    s hs hsT H G.terminal G.terminal_properties.1 hcut hsource

local notation "Q" => joinedTargetRenewal S T hTime m hm J support hSupport
  mNext hmNext JNext supportNext hSupportNext s hs hsT H G hball hcut CM CH K error
  hCM hK he hMK hHK hM hH hδ k hsource

theorem joinedTargetRenewal_matches : RenewalAtTarget Geo Q := by
  let t : Icc (0 : ℝ) A.T :=
    ⟨tNext,hs.le.trans ((G.lowGeometry hball).target_time_mem).1,
      ((G.lowGeometry hball).target_time_mem).2⟩
  constructor
  · change A.centerStrain t = (D).M.field ((D).clamp (t : ℝ)) 0
    rw [Data.clamp_coe D t]
    exact (A.source_strain_eq m hm J support hSupport t).symm
  · change A.sourceNormal m t = (D).normal.field ((D).clamp (t : ℝ)) 0
    rw [Data.clamp_coe D t]
    exact (A.source_normal_eq m hm J support hSupport t).symm
  · rfl
  · rfl

theorem joinedTargetRenewal_shear : (Q).shear=G.hchild :=
  (joinedTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext s hs hsT H G hball hcut CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource).shear_eq hδ

theorem joinedTargetRenewal_constants : (Q).G=K ∧ (Q).error=error := ⟨rfl,rfl⟩

include hTime hCM hK he hMK hHK hM hH hδ hsource in
theorem joinedTargetRenewal_remainder (hT : tNext ≤ N.T) :
    ‖(DNext).M.field ((DNext).clamp tNext) 0-(Geo).M (Geo).center tNext-
      G.hchild • rankOne ℝ (unit ((Geo).w (Geo).center tNext))
        (unit ((Geo).r (Geo).center tNext))‖ ≤ error := by
  have E := joinedTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext s hs hsT H G hball hcut CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact E.target_remainder hδ hT

theorem joinedTargetRenewal_parameters (hTilt : (Geo).tiltError ≤ 1/2) :
    (Q).shear=G.hchild ∧ 0 < (Q).a ∧
    |(Q).a/P.a-1| ≤ (Geo).couplingError ∧
    0 < (Q).sigma ∧
    |(G.y⁻¹)^2*(Q).sigma^2-1| ≤ (Geo).tiltError ∧
    1/2 ≤ (G.y⁻¹)^2*(Q).sigma^2 ∧ (G.y⁻¹)^2*(Q).sigma^2 ≤ 3/2 := by
  have E := joinedTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext s hs hsT H G hball hcut CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact ⟨E.shear_eq hδ,E.coupling_pos,E.coupling_error,E.sigma_pos hTilt,
    E.tilt_error hTilt,E.tilt_interval hTilt⟩

theorem joinedTargetRenewal_compression
    (ht : 0 < tNext) (hT : tNext < N.T)
    (hmargin : 3*((Geo).G+(Geo).d)+error < (Geo).compressionScale) :
    ⟪(DNext).M.field ⟨tNext,ht.le,hT.le⟩ 0 (unit ((Q).m tNext)),
      unit ((Q).m tNext)⟫_ℝ < 0 := by
  have E := joinedTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext s hs hsT H G hball hcut CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact E.activation_compression ht hT hmargin

theorem joinedTargetRenewal_compression_of_error_le_one
    (hT : tNext < N.T) (herror : error ≤ 1) :
    ⟪(DNext).M.field ⟨tNext,(Geo).targetTime_pos hs.le |>.le,hT.le⟩ 0
      (unit ((Q).m tNext)),unit ((Q).m tNext)⟫_ℝ < 0 := by
  have E := joinedTargetRenewal_matches S T hTime m hm J support hSupport
    mNext hmNext JNext supportNext hSupportNext s hs hsT H G hball hcut CM CH K error
    hCM hK he hMK hHK hM hH hδ k hsource
  exact E.activation_compression_of_error_le_one ((Geo).targetTime_pos hs.le) hT herror

end Joined
end EulerParentPacketFrames.SmoothState
