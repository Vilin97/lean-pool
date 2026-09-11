/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInductionStage
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketScaleGeometry
import LeanPool.NavierStokesAndEuler.Euler.PacketInductionScaleBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketRestriction
public import LeanPool.NavierStokesAndEuler.Euler.PacketNestedHorizons
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceGeometryData
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleGuards

/-! The next literal activation and horizon are constructed from the
current actual frame. Restriction preserves the actual Euler state,
low bounds and frame before the next packet is added. -/

section

/-! Restricting the actual parent frame to the next packet horizon,
and identifying its physical and scaled times with the literal scales. -/

@[expose] public section

noncomputable section

namespace EulerPacketSourceGeometry.ParentFrame

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerParentPacketFrames EulerTransversePacketProvider EulerTransverseFrameCoordinates
  EulerPacketMovingFrame EulerTimeIntervalRestriction

variable {A : Parent} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {m : Space} {hm : ‖m‖ = 1} {R : U ≃ₗᵢ[ℝ] referencePlane m}
  {support : Set Space} {hSupport : IsCompact support} {τ : ℝ}
  (P : ParentFrame (A.transverseData m hm R support hSupport) τ)
  (S : ℝ) (hS : 0 < S) (hST : S ≤ A.T) (hτ : 0 ≤ τ)

/-- Restrict time, bundling `B`, `B₁`, `m`, `v` and the required compatibility proofs. -/
def restrictTime : ParentFrame ((A.restrictTime S hS hST).transverseData m hm R support hSupport) τ
    where
  B := P.B
  B₁ := P.B₁
  m := P.m
  v := P.v
  c := P.c
  G := P.G
  error := P.error
  G_lower := P.G_lower
  error_nonneg := P.error_nonneg
  B_derivative t ht := (P.B_derivative t ⟨ht.1,ht.2.trans hST⟩).mono (Icc_subset_Icc le_rfl hST)
  ray_equation t ht := (P.ray_equation t ⟨ht.1,ht.2.trans hST⟩).mono (Icc_subset_Icc le_rfl hST)
  velocity_equation t ht := (P.velocity_equation t ⟨ht.1,ht.2.trans hST⟩).mono (Icc_subset_Icc
      le_rfl hST)
  ray_nonzero t ht := P.ray_nonzero t ⟨ht.1,ht.2.trans hST⟩
  velocity_nonzero t ht := P.velocity_nonzero t ⟨ht.1,ht.2.trans hST⟩
  tangent t ht := P.tangent t ⟨ht.1,ht.2.trans hST⟩
  B_bound t ht := P.B_bound t ⟨ht.1,ht.2.trans hST⟩
  B₁_bound t ht := P.B₁_bound t ⟨ht.1,ht.2.trans hST⟩
  remainder_bound t ht := by
    let ts : Icc (0 : ℝ) S := ⟨t,hτ.trans ht.1,ht.2⟩
    let ta : Icc (0 : ℝ) A.T := ⟨t,hτ.trans ht.1,ht.2.trans hST⟩
    have h := P.remainder_bound t ⟨ht.1,ht.2.trans hST⟩
    rw [Data.clamp_coe (A.transverseData m hm R support hSupport) ta] at h
    change ‖(A.restrictTime S hS hST).strain.field
      (((A.restrictTime S hS hST).transverseData m hm R support hSupport).clamp t) 0 -
      P.B t-primaryShear P.c P.m P.v t •
        rankOne ℝ (EulerPacketNormalizedPrimary.unit (P.v t))
          (EulerPacketNormalizedPrimary.unit (P.m t))‖ ≤ P.error
    rw [Data.clamp_coe ((A.restrictTime S hS hST).transverseData m hm R support hSupport) ts,
      A.restrictTime_strain S hS hST ts 0]
    exact h

@[simp] theorem restrictTime_a : (P.restrictTime S hS hST hτ).a=P.a := rfl
@[simp] theorem restrictTime_sigma : (P.restrictTime S hS hST hτ).sigma=P.sigma := rfl
@[simp] theorem restrictTime_shear : (P.restrictTime S hS hST hτ).shear=P.shear := rfl
@[simp] theorem restrictTime_epsilon : (P.restrictTime S hS hST hτ).epsilon=P.epsilon := rfl
@[simp] theorem restrictTime_G : (P.restrictTime S hS hST hτ).G=P.G := rfl
@[simp] theorem restrictTime_error : (P.restrictTime S hS hST hτ).error=P.error := rfl
@[simp] theorem restrictTime_horizon :
    (P.restrictTime S hS hST hτ).horizon=P.a*(S-τ)/P.epsilon := rfl

end EulerPacketSourceGeometry.ParentFrame

namespace EulerParentStageHorizon

open Real EulerPacketMovingFrame EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketNestedHorizons

theorem scaled_rate {a h : ℝ} (ha : 0 ≤ a) : a/sqrt (a/h)=sqrt (a*h) := by
  rw [sqrt_div ha,div_div_eq_mul_div,sqrt_mul ha]
  calc
    a*sqrt h/sqrt a = (a/sqrt a)*sqrt h := by ring
    _ = sqrt a*sqrt h := by rw [div_sqrt]

theorem physical_rate {a h : ℝ} (ha : 0 ≤ a) : sqrt (a/h)/a=1/sqrt (a*h) := by
  rw [one_div,← scaled_rate ha,inv_div]

theorem physical_target_identity {a h β : ℝ} (ha : 0 ≤ a) (hβ : 0 ≤ β) (τ x : ℝ) :
    physicalTime τ a (sqrt (a/h)) (x/sqrt β)=τ+x/sqrt (β*a*h) := by
  have hd : sqrt β*sqrt (a*h)=sqrt (β*a*h) := by
    rw [← sqrt_mul hβ]
    congr 1
    ring
  unfold physicalTime
  rw [physical_rate ha]
  have he : (1/sqrt (a*h))*(x/sqrt β)=x/(sqrt β*sqrt (a*h)) := by ring
  rw [he,hd]

theorem scaled_horizon_identity {a h β : ℝ} (ha : 0 < a) (hh : 0 < h) (hβ : 0 < β)
    (τ x W : ℝ) :
    a*(τ+x/sqrt (β*a*h)+2*W-τ)/sqrt (a/h)=x/sqrt β+2*sqrt (a*h)*W := by
  have hd : sqrt (β*a*h)=sqrt β*sqrt (a*h) := by
    rw [← sqrt_mul hβ.le]
    congr 1
    ring
  calc
    _ = (a/sqrt (a/h))*(x/(sqrt β*sqrt (a*h))+2*W) := by rw [hd]; ring
    _ = sqrt (a*h)*(x/(sqrt β*sqrt (a*h))+2*W) := by rw [scaled_rate ha.le]
    _ = _ := by
      field_simp [(sqrt_pos.mpr hβ).ne',(sqrt_pos.mpr (mul_pos ha hh)).ne']

end EulerParentStageHorizon

namespace EulerPacketSourceGeometry.ParentFrame

open Set EulerSmoothLimit EulerParentPacketFrames EulerTransversePacketProvider
  EulerTransverseFrameCoordinates EulerPacketMovingFrame EulerParentStageHorizon
  EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence EulerPacketNestedHorizons

variable {A : Parent} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {m : Space} {hm : ‖m‖ = 1} {R : U ≃ₗᵢ[ℝ] referencePlane m}
  {support : Set Space} {hSupport : IsCompact support} {τ : ℝ}
  (P : ParentFrame (A.transverseData m hm R support hSupport) τ)

theorem target_on_scales (J : ℕ) (X : ℝ) (a β : ℕ → ℝ) (n : ℕ)
    (ha : 0 ≤ a n) (hβ : 0 ≤ β n) (haMatch : P.a = a n)
    (hShear : P.shear = previousShear J X n) (hSigma : P.sigma = Real.sqrt (β n)) :
    physicalTime τ P.a P.epsilon (scaleSequence J X (n+1)/P.sigma) =
      τ+stepLength J X a β n := by
  simp only [ParentFrame.epsilon,haMatch,hShear,hSigma,stepLength]
  exact physical_target_identity ha hβ τ _

theorem restricted_horizon_on_scales (J : ℕ) (X : ℝ) (hX : 0 < X) (a β : ℕ → ℝ) (n : ℕ)
    (ha : 0 < a n) (hβ : 0 < β n) (haMatch : P.a = a n)
    (hShear : P.shear = previousShear J X n)
    (S : ℝ) (hS : 0 < S) (hST : S ≤ A.T) (hτ : 0 ≤ τ)
    (hSMatch : S = τ + stepLength J X a β n + 2 * timeWidth J X (n + 1)) :
    (P.restrictTime S hS hST hτ).horizon =
      EulerPacketSourceScaleGuards.horizon J X (a n) (β n) n := by
  rw [P.restrictTime_horizon,ParentFrame.epsilon,haMatch,hShear,hSMatch]
  exact scaled_horizon_identity ha (previousShear_pos J hX n) hβ τ
    (scaleSequence J X (n+1)) (timeWidth J X (n+1))

end EulerPacketSourceGeometry.ParentFrame

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketInduction.Stage

open Set Real EulerSmoothLimit EulerParentPacketFrames EulerPacketSourceGeometry
  EulerPacketInductionScales EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence
  EulerPacketNestedHorizons EulerPacketBaseGuardScales EulerPacketScaleGeometry
  EulerPacketMovingFrame EulerTimeIntervalRestriction

variable {c B : ℝ} {S : Scales c B} {n : ℕ} (P : Stage S n)

/-- Step, given by `stepLength S.J S.X (fun _ => P.frame.a) (fun _ => P.frame.sigma^2) n`. -/
def step : ℝ :=
  stepLength S.J S.X (fun _ => P.frame.a) (fun _ => P.frame.sigma^2) n

/-- Next time, given by `P.time+P.step`. -/
def nextTime : ℝ := P.time+P.step

/-- Next horizon, given by `P.nextTime+2*timeWidth S.J S.X (n+1)`. -/
def nextHorizon : ℝ := P.nextTime+2*timeWidth S.J S.X (n+1)

theorem step_bounds : timeWidth S.J S.X n/6 ≤ P.step ∧
    P.step ≤ 2*timeWidth S.J S.X n/3 :=
  activation_time_bounds P.coupling_bounds.1 P.coupling_bounds.2
    (previousShear_pos S.J S.x_pos n) (zero_lt_one.trans_le (S.sequence_one n))
    (zero_le_one.trans (S.sequence_one (n+1))) P.tilt_lower P.tilt_upper

theorem step_pos : 0 < P.step :=
  (div_pos (timeWidth_pos S.J S.j_one S.x_pos n) (by norm_num)).trans_le P.step_bounds.1

theorem time_lt_nextTime : P.time < P.nextTime := lt_add_of_pos_right _ P.step_pos

theorem nextTime_pos : 0 < P.nextTime := P.time_nonneg.trans_lt P.time_lt_nextTime

theorem nextTime_lt_nextHorizon : P.nextTime < P.nextHorizon :=
  lt_add_of_pos_right _ (mul_pos (by norm_num) (timeWidth_pos S.J S.j_one S.x_pos (n+1)))

theorem time_lt_nextHorizon : P.time < P.nextHorizon :=
  P.time_lt_nextTime.trans P.nextTime_lt_nextHorizon

theorem nextHorizon_pos : 0 < P.nextHorizon :=
  P.nextTime_pos.trans P.nextTime_lt_nextHorizon

theorem nextHorizon_lt : P.nextHorizon < P.parent.T := by
  have hstep := P.step_bounds.2
  have hwidth := P.source_stage.next_width
  have hpos := timeWidth_pos S.J S.j_one S.x_pos n
  rw [P.horizon_eq]
  dsimp only [nextHorizon,nextTime]
  linarith only [hstep,hwidth,hpos]

theorem nextHorizon_le : P.nextHorizon ≤ P.parent.T := P.nextHorizon_lt.le

theorem nextHorizon_le_base : P.nextHorizon ≤ baseHorizon S.J S.X :=
  P.nextHorizon_le.trans P.horizon_le

theorem nextHorizon_one : P.nextHorizon ≤ 1 := P.nextHorizon_le_base.trans S.time_small

theorem nextTime_lower : baseHorizon S.J S.X/12 ≤ P.nextTime := by
  by_cases hn : n=0
  · subst n
    have ht := P.time_zero rfl
    have hs := P.step_bounds.1
    rw [baseHorizon_eq_timeWidth S.J S.x_pos]
    dsimp only [nextTime]
    linarith only [ht,hs]
  · exact (P.time_lower hn).trans P.time_lt_nextTime.le

theorem nextHorizon_common : baseHorizon S.J S.X/12 < P.nextHorizon :=
  P.nextTime_lower.trans_lt P.nextTime_lt_nextHorizon

theorem physical_target_eq_nextTime :
    physicalTime P.time P.frame.a P.frame.epsilon
      (scaleSequence S.J S.X (n+1)/P.frame.sigma)=P.nextTime := by
  exact P.frame.target_on_scales S.J S.X (fun _ => P.frame.a) (fun _ => P.frame.sigma^2) n
    P.coupling_pos.le (sq_nonneg _) rfl P.frame_shear
    (sqrt_sq P.sigma_nonneg).symm

/-- Restricted parent, given by `P.parent.restrictTime P.nextHorizon P.nextHorizon_pos
P.nextHorizon_le`. -/
def restrictedParent : Parent :=
  P.parent.restrictTime P.nextHorizon P.nextHorizon_pos P.nextHorizon_le

/-- Restricted state, given by `P.state.restrictTime P.nextHorizon P.nextHorizon_pos
P.nextHorizon_le`. -/
def restrictedState : SmoothState P.restrictedParent :=
  P.state.restrictTime P.nextHorizon P.nextHorizon_pos P.nextHorizon_le

/-- Restricted low, given by `P.low.restrictTime P.nextHorizon P.nextHorizon_pos
P.nextHorizon_le`. -/
def restrictedLow : LowBounds P.restrictedParent :=
  P.low.restrictTime P.nextHorizon P.nextHorizon_pos P.nextHorizon_le

/-- Restricted frame, given by `P.frame.restrictTime P.nextHorizon P.nextHorizon_pos
P.nextHorizon_le P.time_nonneg`. -/
def restrictedFrame : ParentFrame (frameData P.restrictedParent) P.time :=
  P.frame.restrictTime P.nextHorizon P.nextHorizon_pos P.nextHorizon_le P.time_nonneg

@[simp] theorem restrictedParent_time : P.restrictedParent.T=P.nextHorizon := rfl
@[simp] theorem restrictedParent_scale : P.restrictedParent.ell=P.parent.ell := rfl
@[simp] theorem restrictedState_label : P.restrictedState.labels.K=P.state.labels.K := rfl
@[simp] theorem restrictedLow_exterior : P.restrictedLow.Be=P.low.Be := rfl
@[simp] theorem restrictedLow_core : P.restrictedLow.Bc=P.low.Bc := rfl
@[simp] theorem restrictedLow_pressure : P.restrictedLow.K=P.low.K := rfl
@[simp] theorem restrictedLow_boundary : P.restrictedLow.L=P.low.L := rfl
@[simp] theorem restrictedLow_radius : P.restrictedLow.r=P.low.r := rfl
@[simp] theorem restrictedFrame_a : P.restrictedFrame.a=P.frame.a := rfl
@[simp] theorem restrictedFrame_sigma : P.restrictedFrame.sigma=P.frame.sigma := rfl
@[simp] theorem restrictedFrame_shear : P.restrictedFrame.shear=P.frame.shear := rfl
@[simp] theorem restrictedFrame_G : P.restrictedFrame.G=P.frame.G := rfl
@[simp] theorem restrictedFrame_error : P.restrictedFrame.error=P.frame.error := rfl
@[simp] theorem restrictedFrame_B : P.restrictedFrame.B=P.frame.B := rfl
@[simp] theorem restrictedFrame_m : P.restrictedFrame.m=P.frame.m := rfl
@[simp] theorem restrictedFrame_v : P.restrictedFrame.v=P.frame.v := rfl

theorem restrictedFrame_horizon :
    P.restrictedFrame.horizon=EulerPacketSourceScaleGuards.horizon S.J S.X
      P.frame.a (P.frame.sigma^2) n :=
  P.frame.restricted_horizon_on_scales S.J S.X S.x_pos
    (fun _ => P.frame.a) (fun _ => P.frame.sigma^2) n P.coupling_pos
    (sq_pos_of_pos P.sigma_pos) rfl P.frame_shear
    P.nextHorizon P.nextHorizon_pos P.nextHorizon_le P.time_nonneg rfl

theorem restricted_strain_bound (t : Icc (0 : ℝ) P.restrictedParent.T) (x : Space) :
    ‖P.restrictedParent.strain.field t x‖ ≤
      EulerPacketLowConstants.gradientConstant*previousShear S.J S.X n := by
  rw [show P.restrictedParent.strain.field t x=P.parent.strain.field
    (initialInclusion P.parent.T P.nextHorizon P.nextHorizon_le t) x from
      P.parent.restrictTime_strain P.nextHorizon P.nextHorizon_pos P.nextHorizon_le t x]
  exact P.strain_bound _ _

theorem restricted_curvature_bound (t : Icc (0 : ℝ) P.restrictedParent.T) (x : Space) :
    ‖P.restrictedParent.curvature.field t x‖ ≤
      EulerPacketLowConstants.hessianConstant*previousShear S.J S.X n*olderShear S.J S.X n := by
  rw [show P.restrictedParent.curvature.field t x=P.parent.curvature.field
    (initialInclusion P.parent.T P.nextHorizon P.nextHorizon_le t) x from
      P.parent.restrictTime_curvature P.nextHorizon P.nextHorizon_pos P.nextHorizon_le t x]
  exact P.curvature_bound _ _

end EulerPacketInduction.Stage
