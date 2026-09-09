/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketRestriction
public import LeanPool.NavierStokesAndEuler.Euler.PacketNestedHorizons
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceGeometryData
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleGuards

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
