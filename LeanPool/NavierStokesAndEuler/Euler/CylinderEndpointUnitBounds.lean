/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointBudget
public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointForcing
import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletRegularity
import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletTimeBounds
import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointRegularity
import LeanPool.NavierStokesAndEuler.Euler.CylinderTerminalAmplitude
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangularRegularity
import LeanPool.NavierStokesAndEuler.Euler.PacketMajorantShift
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevOperations

/-!
Actual fixed-Hq mixed-word estimates for unit terminal data. The spatial
radius is unchanged; the coordinate/velocity use two shifts and the true
time derivative uses three. Every inverse guard is source-only.
-/

@[expose] public section


noncomputable section

namespace EulerCylinderDirichlet.Coefficients.EndpointBudget

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderRectangular
  EulerTimeLp EulerGevrey EulerParameterWordGevrey EulerFixedEvolutionSobolev
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {D : Coefficients T U E} {ι : Type*} [Fintype ι] {q : ℕ}
  (L : EndpointBudget D ι q) (directions : ι → LiftTangent)
  (hdir : ∀ i, ‖directions i‖ ≤ 1)
  (Y : CylinderL2 P U) (hY : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a Y))
  (d : ℕ) (hYb : ∀ n, block directions q (fun a : LiftTangent => translate P a Y) n 0 ≤ majorant
      L.R d n)

include hY hYb in
omit [CompleteSpace U] [CompleteSpace E] in
theorem constant_unit_bound (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate P a
      (ContinuousMap.const (Icc (0 : ℝ) T) (T⁻¹ • Y))) n 0 ≤ T⁻¹*majorant L.R d n := by
  have hs := block_smul_le directions q T⁻¹
    (fun a : LiftTangent => pathTranslate P a (ContinuousMap.const (Icc (0 : ℝ) T) Y))
    (constantPath_orbit_contDiff P Y hY) n 0
  rw [abs_of_nonneg (inv_nonneg.mpr D.time_pos.le)] at hs
  have hb := (constantPath_block_le (K := Icc (0 : ℝ) T) P directions q Y hY n 0).trans (hYb n)
  have he : ContinuousMap.const (Icc (0 : ℝ) T) (T⁻¹ • Y) =
      T⁻¹ • ContinuousMap.const (Icc (0 : ℝ) T) Y := rfl
  rw [he]
  simp only [map_smul]
  exact hs.trans (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr D.time_pos.le))

include hdir hY hYb

omit [CompleteSpace U] [CompleteSpace E] in
theorem forcing_unit_bound (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate P a (D.endpointForcing P Y)) n 0 ≤
      endpointForcingCost ι q T L.Rc L.C₁*majorant L.R d n := by
  let Z := ContinuousMap.const (Icc (0 : ℝ) T) (T⁻¹ • Y)
  have hz : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a Z) :=
    endpointConstant_orbit_contDiff P Y hY
  have hp := product_orbit_block_bound P D.Q₁ L.frameDerivative_smooth directions hdir q Z hz
    L.Rc L.C₁ L.R T⁻¹ L.Rc_nonneg L.C₁_nonneg (inv_nonneg.mpr D.time_pos.le)
    L.radius_bounds.2 L.frameDerivative_bound d (L.constant_unit_bound P directions Y hY d hYb) n
  have hs := block_smul_le directions q (2 : ℝ)
    (fun a : LiftTangent => pathTranslate P a (fullMultiplierMap P D.Q₁ Z))
    (product_orbit_contDiff P D.Q₁ L.frameDerivative_smooth Z hz) n 0
  have he : D.endpointForcing P Y = (2 : ℝ) • fullMultiplierMap P D.Q₁ Z := rfl
  rw [he]
  simp only [map_smul]
  apply (hs.trans (mul_le_mul_of_nonneg_left hp (abs_nonneg (2 : ℝ)))).trans_eq
  unfold endpointForcingCost
  norm_num
  ring

theorem coordinate_unit_bound (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate P a (D.endpointCoordinate P Y)) n 0 ≤
      L.coordinateCost*majorant L.R (d+2) n := by
  have hf := D.endpointForcing_orbit_contDiff P L.frameDerivative_smooth Y hY
  have hv := D.velocityPath_orbit_contDiff P L.frame_smooth L.frameDerivative_smooth
      L.hessian_smooth
    (D.endpointForcing P Y) hf
  have hb := D.continuousVelocity_block_bound P directions hdir q
    L.frame_smooth L.frameDerivative_smooth L.hessian_smooth L.Rc L.C₀ L.C₁ L.CH
    (endpointForcingCost ι q T L.Rc L.C₁) L.R L.Rc_nonneg L.C₀_nonneg L.C₁_nonneg
    L.CH_nonneg L.forcingCost_nonneg L.frame_bound L.frameDerivative_bound L.hessian_bound
    L.weak_radius L.strong_radius L.time_le_one (D.endpointForcing P Y) hf d
    (L.forcing_unit_bound P directions hdir Y hY d hYb) n 0
  have hc := (L.constant_unit_bound P directions Y hY d hYb n).trans
    (mul_le_mul_of_nonneg_left (majorant_mono_shift L.R L.radius_bounds.1 d (d+2) n (by omega))
      (inv_nonneg.mpr D.time_pos.le))
  rw [D.endpointCoordinate_eq_forced P Y]
  simp only [map_sub]
  exact (block_sub_le directions q _ _ (endpointConstant_orbit_contDiff P Y hY) hv n 0).trans
    (by simpa only [coordinateCost,add_mul] using add_le_add hc hb)

theorem acceleration_unit_bound (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate P a (D.endpointAcceleration P Y)) n 0 ≤
      majorant L.R (d+3) n := by
  have hf := D.endpointForcing_orbit_contDiff P L.frameDerivative_smooth Y hY
  have ha := D.accelerationPath_orbit_contDiff P L.frame_smooth L.frameDerivative_smooth
      L.hessian_smooth
    (D.endpointForcing P Y) hf
  have hb := D.accelerationPath_block_bound P directions hdir q
    L.frame_smooth L.frameDerivative_smooth L.hessian_smooth L.Rc L.C₀ L.C₁ L.CH
    (endpointForcingCost ι q T L.Rc L.C₁) L.R L.Rc_nonneg L.C₀_nonneg L.C₁_nonneg
    L.CH_nonneg L.forcingCost_nonneg L.frame_bound L.frameDerivative_bound L.hessian_bound
    L.weak_radius L.strong_radius L.time_le_one L.uniform_radius (D.endpointForcing P Y) hf d
    (L.forcing_unit_bound P directions hdir Y hY d hYb) n 0
  have hs := block_smul_le directions q (-1 : ℝ)
    (fun a : LiftTangent => pathTranslate P a (D.accelerationPath P (D.endpointForcing P Y))) ha n 0
  rw [D.endpointAcceleration_eq_forced P Y]
  simp only [map_neg]
  have hn : block directions q
      (fun a : LiftTangent => -pathTranslate P a (D.accelerationPath P (D.endpointForcing P Y))) n
          0 ≤
      block directions q
        (fun a : LiftTangent => pathTranslate P a (D.accelerationPath P (D.endpointForcing P Y))) n
            0 := by
    simpa only [neg_one_smul,abs_neg,abs_one,one_mul] using hs
  exact hn.trans hb

theorem velocity_unit_bound (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate P a (D.endpointVelocity P Y)) n 0 ≤
      L.velocityCost*majorant L.R (d+2) n := by
  change block directions q (fun a : LiftTangent => pathTranslate P a
    (fullMultiplierMap P D.Q (D.endpointCoordinate P Y))) n 0 ≤ _
  exact product_orbit_block_bound P D.Q L.frame_smooth directions hdir q (D.endpointCoordinate P Y)
    (D.endpointCoordinate_orbit_contDiff P L.frame_smooth L.frameDerivative_smooth L.hessian_smooth
        Y hY)
    L.Rc L.C₀ L.R L.coordinateCost L.Rc_nonneg L.C₀_nonneg L.coordinateCost_nonneg
    L.radius_bounds.2 L.frame_bound (d+2) (L.coordinate_unit_bound P directions hdir Y hY d hYb) n

theorem derivative_unit_bound (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate P a (D.endpointDerivative P Y)) n 0 ≤
      L.derivativeCost*majorant L.R (d+3) n := by
  have hv := D.endpointCoordinate_orbit_contDiff P L.frame_smooth L.frameDerivative_smooth
      L.hessian_smooth Y hY
  have ha := D.endpointAcceleration_orbit_contDiff P L.frame_smooth L.frameDerivative_smooth
      L.hessian_smooth Y hY
  have hbv (k) : block directions q (fun a : LiftTangent => pathTranslate P a (D.endpointCoordinate
      P Y)) k 0 ≤
      L.coordinateCost*majorant L.R (d+3) k :=
    (L.coordinate_unit_bound P directions hdir Y hY d hYb k).trans
      (mul_le_mul_of_nonneg_left (majorant_mono_shift L.R L.radius_bounds.1 (d+2) (d+3) k (by
          omega))
        L.coordinateCost_nonneg)
  have hba (k) : block directions q (fun a : LiftTangent => pathTranslate P a
      (D.endpointAcceleration P Y)) k 0 ≤
      1*majorant L.R (d+3) k := by
    simpa only [one_mul] using L.acceleration_unit_bound P directions hdir Y hY d hYb k
  have h₁ := product_orbit_block_bound P D.Q₁ L.frameDerivative_smooth directions hdir q
    (D.endpointCoordinate P Y) hv L.Rc L.C₁ L.R L.coordinateCost L.Rc_nonneg L.C₁_nonneg
    L.coordinateCost_nonneg L.radius_bounds.2 L.frameDerivative_bound (d+3) hbv n
  have h₂ := product_orbit_block_bound P D.Q L.frame_smooth directions hdir q
    (D.endpointAcceleration P Y) ha L.Rc L.C₀ L.R 1 L.Rc_nonneg L.C₀_nonneg
    zero_le_one L.radius_bounds.2 L.frame_bound (d+3) hba n
  have he : D.endpointDerivative P Y = fullMultiplierMap P D.Q₁ (D.endpointCoordinate P Y) +
      fullMultiplierMap P D.Q (D.endpointAcceleration P Y) := rfl
  rw [he]
  simp only [map_add]
  exact (block_add_le directions q _ _
    (product_orbit_contDiff P D.Q₁ L.frameDerivative_smooth _ hv)
    (product_orbit_contDiff P D.Q L.frame_smooth _ ha) n 0).trans
    (by simpa only [derivativeCost,mul_one,add_mul] using add_le_add h₁ h₂)

end EulerCylinderDirichlet.Coefficients.EndpointBudget
