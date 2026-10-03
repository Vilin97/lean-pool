/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.Pointwise

/-! # The energy rate identity for `w = u - v`

For `t > 0`,
`d/dt ∫ w² = ∫ 2 w ∂ₜ w = -2κ ∫ |∇w|² - 2 ∫ f w`
(Laplacian integration by parts and cancellation of the divergence-free transport term). -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Homogenization
open AVenhance.Infra.Torus AVenhance.Infra.Classical
open scoped Topology

namespace AVenhance.Infra.Section5.Integration.Energy

open AVenhance

theorem continuous_spaceGrad_component {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) :
    Continuous (fun x => spaceGrad f x i) := by
  change Continuous (fun x => fderiv ℝ f x (basisVec i))
  exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const

theorem continuous_spaceLap {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (spaceLap f) := by
  unfold spaceLap
  apply continuous_finsetSum
  intro i _
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (fun x => spaceGrad f x i) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ f x (basisVec i))
    exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
  exact continuous_spaceGrad_component hgrad i

theorem continuous_vecDot_of {f g : Vec 2 → Vec 2} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => vecDot (f x) (g x)) := by
  change Continuous (fun x => ∑ i : Fin 2, f x i * g x i)
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i).comp hf).mul ((continuous_apply i).comp hg)

variable {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {θ₀ : Vec 2 → ℝ} {u v : ℝ → Vec 2 → ℝ}

namespace ForcedSetup

/-- The slice of the forcing is continuous at positive times. -/
theorem forcing_slice_continuous (S : ForcedSetup φ κ θ₀ u v) {t : ℝ} (ht : 0 < t) :
    Continuous (fun x => advDiffOp (streamVel φ) κ v t x) := by
  have hline : Continuous fun x : Vec 2 => (t, x) := continuous_const.prodMk continuous_id
  have hmaps : MapsTo (fun x : Vec 2 => (t, x)) Set.univ classicalPositiveTimeDomain := by
    intro x _
    simp [classicalPositiveTimeDomain, ht]
  exact continuousOn_univ.mp (S.forcing_continuousOn.comp hline.continuousOn hmaps)

/-- Energy rate identity for the error `w = u - v` at positive times. -/
theorem energy_rate (S : ForcedSetup φ κ θ₀ u v) {t : ℝ} (ht : 0 < t) :
    (∫ x in unitCell 2, 2 * (u t x - v t x) * deriv (fun s => u s x - v s x) t) =
      -(2 * κ) * (∫ x in unitCell 2,
        vecDot (spaceGrad (fun y => u t y - v t y) x) (spaceGrad (fun y => u t y - v t y) x)) -
      2 * ∫ x in unitCell 2, advDiffOp (streamVel φ) κ v t x * (u t x - v t x) := by
  set w : Vec 2 → ℝ := fun y => u t y - v t y with hw
  have hws : ContDiff ℝ (⊤ : ℕ∞) w := S.wSlice ht.le
  have hwp : IsZ2Periodic w := S.wPeriodic ht.le
  have hwc : Continuous w := hws.continuous
  have hbJoint := streamVel_smoothPeriodic φ S.hφ
  have hbc : Continuous (streamVel φ t) :=
    (hbJoint.smooth.continuous).comp (continuous_const.prodMk continuous_id)
  have hgradc : Continuous (spaceGrad w) :=
    continuous_pi fun i => continuous_spaceGrad_component hws i
  have hfc := S.forcing_slice_continuous ht
  have hlInt : IntegrableOn (fun x => w x * spaceLap w x) (unitCell 2) :=
    continuous_integrableOn_unitCell (hwc.mul (continuous_spaceLap hws))
  have hqInt : IntegrableOn (fun x => vecDot (streamVel φ t x) (spaceGrad w x) * w x)
      (unitCell 2) :=
    continuous_integrableOn_unitCell ((continuous_vecDot_of hbc hgradc).mul hwc)
  have hfInt : IntegrableOn (fun x => advDiffOp (streamVel φ) κ v t x * w x) (unitCell 2) :=
    continuous_integrableOn_unitCell (hfc.mul hwc)
  have hpoint : ∀ x, 2 * w x * deriv (fun s => u s x - v s x) t =
      (2 * κ) * (w x * spaceLap w x) - 2 * (vecDot (streamVel φ t x) (spaceGrad w x) * w x) -
        2 * (advDiffOp (streamVel φ) κ v t x * w x) := by
    intro x
    rw [S.deriv_w_eq ht x]
    ring
  have hsplit : (∫ x in unitCell 2, 2 * w x * deriv (fun s => u s x - v s x) t) =
      (2 * κ) * (∫ x in unitCell 2, w x * spaceLap w x) -
        2 * (∫ x in unitCell 2, vecDot (streamVel φ t x) (spaceGrad w x) * w x) -
        2 * (∫ x in unitCell 2, advDiffOp (streamVel φ) κ v t x * w x) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    rw [integral_sub ((hlInt.const_mul (2 * κ)).sub' (hqInt.const_mul 2)) (hfInt.const_mul 2),
      integral_sub (hlInt.const_mul (2 * κ)) (hqInt.const_mul 2),
      integral_const_mul, integral_const_mul, integral_const_mul]
  have hlap := integral_unitCell_lap_energy hws hwp
  have htransport := streamVel_unitCell_transport_energy_zero φ S.hφ t w
    (hws.of_le (by norm_num)) hwp
  rw [hsplit, hlap, htransport]
  ring

end ForcedSetup

end AVenhance.Infra.Section5.Integration.Energy

end
