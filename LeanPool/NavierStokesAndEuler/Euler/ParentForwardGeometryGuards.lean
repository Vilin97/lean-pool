/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardGeometryData
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketNeighborBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleGuards

@[expose] public section

/-! The literal numerical scale guards also initialize the zero-history
amplification stage. Its new ray and velocity start exactly in the old
frame, so only the actual strain's spatial variation enters the error. -/

noncomputable section

namespace EulerParentPacketFrames.LabelData

open Set InnerProductSpace EulerSmoothLimit EulerPacketSourceGeometry
  EulerPacketMovingFrame EulerPacketNormalizedPrimary EulerPacketCrossProduct
  EulerPacketSourceScaleSequence EulerPacketSourceScaleChoice EulerPacketSourceScaleActual
  EulerPacketSourceScaleGuards EulerPacketSourceScales

variable {A : Parent} (L : LabelData A)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖=1)
  (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  (P : ParentFrame (A.transverseData m hm R support hSupport) 0)

theorem forwardError_bound (ρ E N : ℝ) (hρ : 0 ≤ ρ) (hE : P.error ≤ E)
    (hN : L.strainDifferenceCost*A.ell*ρ ≤ N) : P.forwardError ρ ≤ E+N := by
  unfold ParentFrame.forwardError
  exact add_le_add hE
    ((mul_le_mul_of_nonneg_right (L.source_strain_derivative_norm m hm R support hSupport)
      hρ).trans hN)

def forwardGeometryGuardsOfStage
    (J D : ℕ) (C c X : ℝ) (a β : ℕ → ℝ) (n : ℕ)
    (CF : ℝ) (hCF : 1 ≤ CF)
    (stage : StageGuards J D C c X (neighborStabilityConstant*CF^2) a β n)
    (ha : 1/2 ≤ a n) (ha_match : P.a=a n)
    (hshear : P.shear=previousShear J X n)
    (hsigma : P.sigma=Real.sqrt (β n))
    (htime : P.horizon=EulerPacketSourceScaleGuards.horizon J X (a n) (β n) n)
    (hG : P.G ≤ CF*(1+olderShear J X n))
    (herr : P.error ≤ priorError J D X n)
    (ρ δ hchild : ℝ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) (hhchild : 0 ≤ hchild)
    (hneighbor : L.strainDifferenceCost*A.ell*ρ ≤ neighborError J D X c n)
    (hnormal : m=cross (unit (P.m 0)) (unit (P.v 0))) : ForwardGuards P := by
  have hepsilon : P.epsilon=epsilon J X (a n) n := by
    simp only [ParentFrame.epsilon,epsilon,ha_match,hshear]
  have heps : 0 < P.epsilon := by simpa only [hepsilon] using stage.epsilon_pos
  have htarget : ((scaleSequence J X (n+1))⁻¹)⁻¹/P.sigma=targetTime J X (β n) n := by
    simp only [inv_inv,hsigma,targetTime]
  have htarget1 : 1 ≤ targetTime J X (β n) n := by
    have hh : 1 ≤ 1/Real.sqrt (β n) :=
      (le_div_iff₀ stage.sigma_pos).2 (by nlinarith only [stage.sigma_small])
    exact hh.trans stage.target_from_sigma
  have htH : targetTime J X (β n) n ≤ P.horizon := by
    rw [htime]
    exact stage.target_le_horizon
  have hH : 1 ≤ P.horizon := htarget1.trans htH
  have hHθ : P.horizon ≤ sourceTheta J C (scaleSequence J X) n := by
    rw [htime]
    exact stage.horizon_le_Theta
  have hθ : 1 ≤ sourceTheta J C (scaleSequence J X) n := hH.trans hHθ
  have hshort : P.horizon-targetTime J X (β n) n ≤ 1 := by
    rw [htime]
    apply stage.extra_time.trans
    exact (div_le_iff₀ (pow_pos (zero_lt_one.trans_le hθ) 60)).2
      (by simpa only [one_mul] using one_le_pow₀ hθ (n := 60))
  have herror := L.forwardError_bound m hm R support hSupport P ρ
    (priorError J D X n) (neighborError J D X c n) hρ herr hneighbor
  have herror0 : 0 ≤ P.forwardError ρ :=
    add_nonneg P.error_nonneg (mul_nonneg (norm_nonneg _) hρ)
  have hcoef : 16*(P.epsilon*P.horizon*(4*P.G)^2+P.forwardError ρ) ≤
      CF^2*geometryError J D C c X a n := by
    have hmain : P.epsilon*P.horizon*(4*P.G)^2 ≤
        CF^2*(epsilon J X (a n) n*sourceTheta J C (scaleSequence J X) n*
          (4*(1+olderShear J X n))^2) := by
      rw [hepsilon]
      calc
        _ ≤ epsilon J X (a n) n*sourceTheta J C (scaleSequence J X) n*
            (4*(CF*(1+olderShear J X n)))^2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hHθ stage.epsilon_pos.le)
            (pow_le_pow_left₀ (by positivity [P.G_lower])
              (mul_le_mul_of_nonneg_left hG (by norm_num : (0 : ℝ) ≤ 4)) 2)
            (sq_nonneg _) (mul_nonneg stage.epsilon_pos.le (zero_le_one.trans hθ))
        _ = _ := by ring
    have hE := herror.trans (le_mul_of_one_le_left (herror0.trans herror)
      (one_le_pow₀ hCF : 1 ≤ CF^2))
    calc
      _ ≤ 16*(CF^2*(epsilon J X (a n) n*sourceTheta J C (scaleSequence J X) n*
          (4*(1+olderShear J X n))^2)+CF^2*(priorError J D X n+neighborError J D X c n)) :=
        mul_le_mul_of_nonneg_left (add_le_add hmain hE) (by norm_num)
      _ = _ := by unfold geometryError; ring
  have hcoef0 : 0 ≤ 16*(P.epsilon*P.horizon*(4*P.G)^2+P.forwardError ρ) := by
    positivity
  have hN1 : 1 ≤ 1000000*neighborStabilityConstant := by
    nlinarith only [neighborStabilityConstant_ge]
  have hN : 0 ≤ 1000000*neighborStabilityConstant := zero_le_one.trans hN1
  have hsmall : 1000000*neighborStabilityConstant*
      (16*(P.epsilon*P.horizon*(4*P.G)^2+P.forwardError ρ))*P.horizon^40 ≤ 1 := by
    calc
      _ ≤ 1000000*neighborStabilityConstant*(CF^2*geometryError J D C c X a n)*
          sourceTheta J C (scaleSequence J X) n^40 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcoef hN)
          (pow_le_pow_left₀ (zero_le_one.trans hH) hHθ 40)
          (pow_nonneg (zero_le_one.trans hH) 40) (mul_nonneg hN (hcoef0.trans hcoef))
      _ = 1000000*(neighborStabilityConstant*CF^2)*geometryError J D C c X a n*
          sourceTheta J C (scaleSequence J X) n^40 := by ring
      _ ≤ 1 := stage.geometry_small
  have hplain : 16*(P.epsilon*P.horizon*(4*P.G)^2+P.forwardError ρ) ≤ 1 := by
    have hh : 1 ≤ 1000000*neighborStabilityConstant*P.horizon^40 :=
      one_le_mul_of_one_le_of_one_le hN1 (one_le_pow₀ hH)
    have hh' := mul_le_mul_of_nonneg_right hh hcoef0
    nlinarith only [hh',hsmall]
  refine {
    radius := ρ, y := (scaleSequence J X (n+1))⁻¹, δ := δ, hchild := hchild,
    radius_nonneg := hρ, delta_nonneg := hδ, child_nonneg := hhchild,
    coupling_lower := by simpa only [ha_match] using ha,
    shear_pos := ?_, sigma_pos := by simpa only [hsigma] using stage.sigma_pos,
    sigma_small := by simpa only [hsigma] using stage.sigma_small,
    y_pos := stage.reciprocal_pos, y_small := stage.reciprocal_small,
    target_le_horizon := by simpa only [htarget] using htH,
    horizon_lower := hH, short_extension := by simpa only [htarget] using hshort,
    small := hsmall, compression_guard := ?_, initial_frame := A.frame_initial,
    normal_choice := hnormal }
  · have haP : 0 < P.a := by rw [ha_match]; linarith only [ha]
    have hdiv : 0 < P.a/P.shear := Real.sqrt_pos.mp heps
    exact (div_pos_iff.mp hdiv).resolve_right (by intro h; exact (not_lt_of_ge haP.le) h.1) |>.2
  · rw [htarget]
    exact compression_of_error_small (by simpa only [ha_match] using ha) heps.le
      (zero_le_one.trans hH) htH P.G_lower herror0 hplain

end EulerParentPacketFrames.LabelData
