/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryFactorization
import LeanPool.NavierStokesAndEuler.Euler.FixedEndpointClassical
import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryScaling
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistory
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketTimeData

/-! Tangency, the physical tangent ODE, and nonvanishing of the actual
canonical primary. Nonvanishing follows from the prescribed nonzero
terminal displacement, rather than from an assumption on the solved velocity. -/

@[expose] public section


noncomputable section

namespace EulerLinearDuhamel.Evolution

open Set ContinuousLinearMap EulerVolterraConvolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {T : ℝ} {hT : 0 ≤ T} {G : C(Icc (0 : ℝ) T, E →L[ℝ] E)}

/-- A zero of a genuine homogeneous solution propagates in either time direction. -/
theorem homogeneous_zero_at (U : Evolution T hT G) (f : ℝ → E)
    (hf : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt f (G t (f t)) (Icc (0 : ℝ) T) t)
    (s t : Icc (0 : ℝ) T) (hs : f s = 0) : f t = 0 := by
  let q : ℝ → E := fun r => extendPath T hT U.backward r (f r)
  have hq : ∀ r ∈ Icc (0 : ℝ) T, HasDerivWithinAt q 0 (Icc (0 : ℝ) T) r := by
    intro r hr
    have hd := (U.backward_derivative ⟨r,hr⟩).clm_apply (hf ⟨r,hr⟩)
    convert! hd using 1
    · simp only [neg_apply,comp_apply,extendPath,projIcc_of_mem hT hr]
      abel
  have he : q t = q s := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hq
      (fun r hr => by simp) (convex_Icc (0 : ℝ) T) s.property t.property
    simpa only [zero_mul,norm_le_zero_iff,sub_eq_zero] using h
  have hqs : q s = 0 := by simp only [q,hs,map_zero]
  have ht : U.backward t (f t) = 0 := by
    simpa only [q,extendPath,projIcc_of_mem hT t.property] using he.trans hqs
  have h := congrArg (U.forward t) ht
  change ((U.forward t).comp (U.backward t)) (f t) = U.forward t 0 at h
  simpa only [U.forward_backward,id_apply,map_zero] using h

end EulerLinearDuhamel.Evolution

namespace EulerCylinderDirichlet.Coefficients

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerVolterraConvolution
  EulerTransverseEndpointCoordinates EulerFixedEndpointClassical

variable {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)

/-- A nonzero terminal coordinate forces the actual physical history
velocity to be nonzero at some time. -/
theorem labelVelocity_exists_ne_zero (x : Space) (ξ : U) (hξ : ξ ≠ 0) :
    ∃ t : Icc (0 : ℝ) T, D.labelVelocity x ξ t ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  have hv : ∀ t : Icc (0 : ℝ) T, D.labelCoordinate x ξ t = 0 := by
    intro t
    have h := D.labelFrame_lower x t (D.labelCoordinate x ξ t)
    change D.lower*‖D.labelCoordinate x ξ t‖^2 ≤ ‖D.labelVelocity x ξ t‖^2 at h
    rw [hn t,norm_zero,zero_pow (by decide : 2 ≠ 0)] at h
    have hs : ‖D.labelCoordinate x ξ t‖^2 ≤ 0 := nonpos_of_mul_nonpos_right h D.lower_pos
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (D.labelCoordinate x ξ t)])
  let z := EulerFixedEndpointClassical.displacement T D.time_pos.le (D.labelFrame x)
      (D.labelFrameDerivative x)
    (D.labelHessian x) D.lower D.lower_pos (D.labelFrame_lower x) (D.labelFrame_derivative x)
    D.potential D.potential_nonneg (D.labelHessian_upper x) D.small ξ
  have hd : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T D.time_pos.le z) 0 (Icc (0 : ℝ) T) t := by
    intro t ht
    have h := EulerFixedEndpointClassical.displacement_hasDerivWithinAt T D.time_pos.le
        (D.labelFrame x)
      (D.labelFrameDerivative x) (D.labelHessian x) D.lower D.lower_pos (D.labelFrame_lower x)
      (D.labelFrame_derivative x) D.potential D.potential_nonneg (D.labelHessian_upper x) D.small
      (D.labelFrameSecond x) D.time_pos (D.labelFrame_second_derivative x) (D.labelFrame_equation x)
      ξ ⟨t,ht⟩
    change HasDerivWithinAt (extendPath T D.time_pos.le z) (D.labelCoordinate x ξ ⟨t,ht⟩)
      (Icc (0 : ℝ) T) t at h
    rwa [hv] at h
  have he : extendPath T D.time_pos.le z T = extendPath T D.time_pos.le z 0 := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hd
      (fun r hr => by simp) (convex_Icc (0 : ℝ) T)
      (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,D.time_pos.le⟩)
      (show T ∈ Icc (0 : ℝ) T from ⟨D.time_pos.le,le_rfl⟩)
    simpa only [zero_mul,norm_le_zero_iff,sub_eq_zero] using h
  have hz0 : extendPath T D.time_pos.le z 0 = 0 := by
    rw [extendPath,projIcc_of_mem D.time_pos.le (show (0 : ℝ) ∈ Icc 0 T from
        ⟨le_rfl,D.time_pos.le⟩)]
    exact EulerFixedEndpointClassical.displacement_initial T D.time_pos.le (D.labelFrame x)
        (D.labelFrameDerivative x)
      (D.labelHessian x) D.lower D.lower_pos (D.labelFrame_lower x) (D.labelFrame_derivative x)
      D.potential D.potential_nonneg (D.labelHessian_upper x) D.small ξ
  have hzT : extendPath T D.time_pos.le z T = ξ := by
    rw [extendPath,projIcc_of_mem D.time_pos.le (show T ∈ Icc (0 : ℝ) T from
        ⟨D.time_pos.le,le_rfl⟩)]
    exact EulerFixedEndpointClassical.displacement_terminal T D.time_pos.le (D.labelFrame x)
        (D.labelFrameDerivative x)
      (D.labelHessian x) D.lower D.lower_pos (D.labelFrame_lower x) (D.labelFrame_derivative x)
      D.potential D.potential_nonneg (D.labelHessian_upper x) D.small D.time_pos ξ
  exact hξ (hzT.symm.trans (he.trans hz0))

end EulerCylinderDirichlet.Coefficients

namespace EulerPacketPrimaryFactorization

open Set InnerProductSpace EulerSmoothLimit EulerTransversePacketProvider
  EulerPacketTerminalDatum EulerTransversePacketPrimary EulerSpatialCutoffs
  EulerLinearDuhamel EulerVolterraConvolution

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (ξ : U) (hs : tsupport innerCutoff ⊆ D.support)

omit [CompleteSpace U] in
theorem canonicalNormal_equation (t : Icc (0 : ℝ) D.T) (x : Space) :
    HasDerivWithinAt (fun s => D.normal.field (D.clamp s) x)
      (-(D.M.field t x).adjoint (D.normal.field t x)) (Icc (0 : ℝ) D.T) t := by
  simpa only [extendPath,Data.clamp,projIcc_of_mem D.T_pos.le t.property,
    Data.normalDerivative_apply] using D.normal_hasDerivWithinAt t t.property x

theorem canonicalVelocity_tangent (t : Icc (0 : ℝ) D.T) (x : Space) :
    ⟪D.normal.field t x,canonicalVelocity τ hτ hτT B ξ hs t x⟫_ℝ = 0 := by
  have h : ⟪D.normal.field t x,
      vector τ hτ hτT B (initialData D 1 zero_lt_one ξ hs) (t,(x,Real.pi/2))⟫_ℝ = 0 := by
    simpa only [Data.normalField,Data.clamp_coe] using
      vector_tangent τ hτ hτT B (initialData D 1 zero_lt_one ξ hs) t x (Real.pi/2)
  simp only [canonicalVelocity,envelopedVelocity,inner_smul_right,h,mul_zero]

theorem canonicalVelocity_equation (t : Icc (0 : ℝ) D.T) (x : Space) :
    HasDerivWithinAt (fun s => canonicalVelocity τ hτ hτT B ξ hs s x)
      (-D.M.field t x (canonicalVelocity τ hτ hτT B ξ hs t x) +
        (2*⟪D.normal.field t x,D.M.field t x (canonicalVelocity τ hτ hτT B ξ hs t x)⟫_ℝ/
          ‖D.normal.field t x‖^2) • D.normal.field t x) (Icc (0 : ℝ) D.T) t := by
  simpa only [physicalGenerator_apply] using canonicalVelocity_homogeneous_time τ hτ hτT B ξ hs t x

theorem canonicalVelocity_ne_zero (hξ : ξ ≠ 0) (t : Icc (0 : ℝ) D.T)
    (x : Space) (hx : innerCutoff x ≠ 0) : canonicalVelocity τ hτ hτT B ξ hs t x ≠ 0 := by
  intro ht
  obtain ⟨s,hs0⟩ := B.coefficients.labelVelocity_exists_ne_zero x ξ hξ
  let sd : Icc (0 : ℝ) D.T := ⟨s,s.property.1,s.property.2.trans hτT.le⟩
  have hz := (constructedEvolution D.T D.T_pos.le (physicalGenerator D x)).homogeneous_zero_at
    (fun r => canonicalVelocity τ hτ hτT B ξ hs r x)
    (fun r => canonicalVelocity_homogeneous_time τ hτ hτT B ξ hs r x) t sd ht
  change canonicalVelocity τ hτ hτT B ξ hs s x = 0 at hz
  rw [canonicalVelocity_history τ hτ hτT B ξ hs s x] at hz
  exact hs0 ((smul_eq_zero.mp hz).resolve_left hx)

theorem canonicalVelocity_center_ne_zero (hξ : ξ ≠ 0) (t : Icc (0 : ℝ) D.T) :
    canonicalVelocity τ hτ hτT B ξ hs t 0 ≠ 0 :=
  canonicalVelocity_ne_zero τ hτ hτT B ξ hs hξ t 0 (by rw [innerCutoff_zero]; exact one_ne_zero)

theorem canonical_size_pos (hξ : ξ ≠ 0) (t : Icc (0 : ℝ) D.T) :
    0 < ‖D.normal.field t 0‖*‖canonicalVelocity τ hτ hτT B ξ hs t 0‖ :=
  mul_pos (norm_pos_iff.mpr (HistoryData.normal_ne_zero t 0))
    (norm_pos_iff.mpr (canonicalVelocity_center_ne_zero τ hτ hτT B ξ hs hξ t))

/-- Canonical velocity path, bundling `toFun`, `continuous_toFun`. -/
def canonicalVelocityPath (x : Space) : C(Icc (0 : ℝ) D.T,Space) where
  toFun t := canonicalVelocity τ hτ hτT B ξ hs t x
  continuous_toFun := (show ContinuousOn (fun t => canonicalVelocity τ hτ hτT B ξ hs t x)
      (Icc (0 : ℝ) D.T) from fun t ht =>
    (canonicalVelocity_homogeneous_time τ hτ hτT B ξ hs ⟨t,ht⟩ x).continuousWithinAt).domRestrict

theorem canonical_amplitude_pos (hξ : ξ ≠ 0) (t : Icc (0 : ℝ) D.T)
    (δ h : ℝ) (hδ : 0 < δ) (hh : 0 < h) :
    0 < δ*h/(‖D.normal.field t 0‖*‖canonicalVelocity τ hτ hτT B ξ hs t 0‖) :=
  div_pos (mul_pos hδ hh) (canonical_size_pos τ hτ hτT B ξ hs hξ t)

/-- The actual scaled terminal datum achieves the requested primary
gradient norm; nonvanishing is proved from its nonzero terminal direction. -/
theorem scaled_terminal_target_shear (hξ : ξ ≠ 0) (δ : ℝ) (hδ : 0 < δ)
    (h k : ℝ) (hh : 0 ≤ h) (hk : k ≠ 0) (t : Icc (0 : ℝ) D.T)
    (X Y : Space → Space) (hX : HasFDerivAt X (D.F.field t 0) 0)
    (hY : DifferentiableAt ℝ Y (X 0)) (hleft : ∀ y, Y (X y) = y) :
    let α := δ*h/(‖D.normal.field t 0‖*‖canonicalVelocity τ hτ hτT B ξ hs t 0‖)
    ‖fderiv ℝ (fun x => k⁻¹ • vector τ hτ hτT B (initialData D δ hδ (α • ξ) hs)
      (t,(Y x,k*inner ℝ D.m₀ (Y x)))) (X 0)‖ = h := by
  dsimp only
  have he := EulerPacketPrimaryShear.scaled_terminal_wave_eq τ hτ hτT B δ hδ ξ hs
    (δ*h/(‖D.normal.field t 0‖*‖canonicalVelocity τ hτ hτT B ξ hs t 0‖)) k t
  change ‖fderiv ℝ ((fun x : Space => k⁻¹ • vector τ hτ hτT B
    (initialData D δ hδ ((δ*h/(‖D.normal.field t 0‖*
      ‖canonicalVelocity τ hτ hτT B ξ hs t 0‖)) • ξ) hs)
      (t,(x,k*inner ℝ D.m₀ x))) ∘ Y) (X 0)‖ = h
  rw [he]
  exact EulerPacketPrimaryShear.fullWave_target_shear τ hτ hτT B δ hδ ξ hs h k hh hk t X Y
    hX hY hleft (canonicalVelocity_center_ne_zero τ hτ hτT B ξ hs hξ t)

end EulerPacketPrimaryFactorization
