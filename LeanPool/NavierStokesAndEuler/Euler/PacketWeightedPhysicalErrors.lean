/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalCorrectionPotential
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftCorrection
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalFrequencyBounds
import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftGraph
import LeanPool.NavierStokesAndEuler.Euler.FieldTowerPointwiseGevrey
import LeanPool.NavierStokesAndEuler.Euler.PacketContinuousInverse
import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalPressureGevrey
import Mathlib.Algebra.Order.Star.Real

/-! Actual weighted correction and pressure norms bound the physical
velocity gradient and the Hessian of the constructed scalar potential
for that same correction. -/

@[expose] public section


noncomputable section


namespace EulerAllOrderDriftCorrection

open Set EulerSmoothLimit EulerAllOrderCorrectionData EulerLiftedGradientSpace
  EulerCylinderSobolev EulerCylinderSobolevSpace EulerSobolevGevreyOperators
  EulerPacketPhysicalGevrey EulerPacketInverseFlowGevrey EulerGraphPressurePotential
  EulerCylinderPhysicalTensor EulerGevrey
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (P : ℝ) [Fact (0 < P)]

/-- Weighted physical gradient cost, given by `((1+9*CF)*physicalFixedCost D R CF ρ⁻¹
1)*(sobolevEmbeddingConstant P 3*Cw)`. -/
def weightedPhysicalGradientCost (R CF ρ Cw : ℝ) : ℝ :=
  ((1+9*CF)*physicalFixedCost D R CF ρ⁻¹ 1)*(sobolevEmbeddingConstant P 3*Cw)

theorem weightedPhysicalGradientCost_nonneg (R CF ρ Cw : ℝ)
    (hR : 0 ≤ R) (hCF : 0 ≤ CF) (hρ : 0 < ρ) (hCw : 0 ≤ Cw) :
    0 ≤ weightedPhysicalGradientCost D P R CF ρ Cw := by
  have h := physicalFixedCost_nonneg D R CF ρ⁻¹ 1 hR hCF (inv_nonneg.mpr hρ.le)
  have hs := sobolevEmbeddingConstant_nonneg P 3
  unfold weightedPhysicalGradientCost
  positivity

variable {A : Data P D.T} (Q : Budget P D.T_pos A)
  (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hXY : ∀ t x, X t (Y t x) = x) (hY : Continuous (Function.uncurry Y))
  (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det = 1)
  (R CF : ℝ) (hR : 0 ≤ R) (hCF : 0 ≤ CF)
  (hFb : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F.field t : Space → (Space →L[ℝ] Space)) x‖ ≤ CF * majorant R 0 n)

include hX hXY hY hdet hR hCF hFb in
theorem Budget.physical_gradient_hessian_of_weighted (k ρ Cw d : ℝ)
    (hk : 1 ≤ k) (hκ : A.κ = k⁻¹) (hm : A.direction = D.m₀)
    (hρ : 0 < ρ) (hCw : 0 ≤ Cw) (hd : 0 ≤ d)
    (he : ∀ n (t : Icc (0 : ℝ) D.T), weightedNorm P 6 n ρ
      ((Q.fieldTower P).realization (n + 6) t) ≤ Cw * d)
    (hp : ∀ n (t : Icc (0 : ℝ) D.T), weightedNorm P 6 n ρ
      ((Q.pressureTower P).realization (n + 6) t) ≤ Cw * d)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖fderiv ℝ (fun y => k⁻¹ • D.F.field t (Y t y)
      (Q.pointField P t (cylinderGraph P k D.m₀ (Y t y)))) x‖ ≤
        weightedPhysicalGradientCost D P R CF ρ Cw*k*d ∧
    ‖fderiv ℝ (gradient (Q.physicalPotential D P k Y t)) x‖ ≤
        weightedPhysicalGradientCost D P R CF ρ Cw*k*d := by
  let Cpt := sobolevEmbeddingConstant P 3*Cw
  have hCpt : 0 ≤ Cpt := mul_nonneg (sobolevEmbeddingConstant_nonneg P 3) hCw
  have hword (F : FieldTower P D.T)
      (hF : ∀ n (s : Icc (0 : ℝ) D.T), weightedNorm P 6 n ρ
        (F.realization (n+6) s) ≤ Cw*d) (n : ℕ) (s : Icc (0 : ℝ) D.T) (y : LiftDomain P) :
      (∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w (F.pointField s) y‖) ≤
        (Cpt*d)*(ρ⁻¹)^n*(n.factorial : ℝ)^2 := by
    have h := F.pointField_wordSum_gevrey (n+6) 6 n n (by omega) (by omega) le_rfl
      ρ (Cw*d) hρ s (hF n s) y
    simpa only [Cpt,mul_assoc] using h
  have heword (n : ℕ) (s : Icc (0 : ℝ) D.T) (y : LiftDomain P) :
      (∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w (Q.pointField P s) y‖) ≤
        (Cpt*d)*(ρ⁻¹)^n*(n.factorial : ℝ)^2 := by
    simpa only [Q.correctionTower_pointField P s] using hword (Q.fieldTower P) he n s y
  have hpword (n : ℕ) (s : Icc (0 : ℝ) D.T) (y : LiftDomain P) :
      (∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w (Q.pointPressure P s) y‖) ≤
        (Cpt*d)*(ρ⁻¹)^n*(n.factorial : ℝ)^2 := by
    simpa only [Q.pressureTower_pointField P s] using hword (Q.pressureTower P) hp n s y
  have hYd := continuousInverse_differentiable D X Y hX hXY hY
  have hk0 : 0 < k := by linarith
  have hki : |k⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.mpr hk0)]
    exact inv_le_one_of_one_le₀ hk
  have hv := physicalReconstruction_power_bound D P k⁻¹ k (Q.pointField P)
    (Q.pointField_smooth P) R CF (Cpt*d) ρ⁻¹ hR hCF (mul_nonneg hCpt hd)
    (inv_nonneg.mpr hρ.le) hFb heword X Y hX hYd hXY hdet hk hki 1 t x
  have hpr := physicalPressureForce_power_bound D P k⁻¹ k (Q.pointPressure P)
    (Q.pointPressure_smooth P) R CF (Cpt*d) ρ⁻¹ hR hCF (mul_nonneg hCpt hd)
    (inv_nonneg.mpr hρ.le) hdet hFb hpword X Y hX hYd hXY hk hki 1 t x
  let H := (1+9*CF)*physicalFixedCost D R CF ρ⁻¹ 1
  have hc := physicalFixedCost_nonneg D R CF ρ⁻¹ 1 hR hCF (inv_nonneg.mpr hρ.le)
  have hcv : physicalFixedCost D R CF ρ⁻¹ 1 ≤ H := by dsimp [H]; nlinarith
  have hcp : 9*CF*physicalFixedCost D R CF ρ⁻¹ 1 ≤ H := by dsimp [H]; nlinarith
  have absorb (v c : ℝ) (hvc : v ≤ c*(Cpt*d)*k) (hcH : c ≤ H) :
      v ≤ weightedPhysicalGradientCost D P R CF ρ Cw*k*d := by
    apply hvc.trans
    apply (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcH (mul_nonneg hCpt hd)) hk0.le).trans_eq
    dsimp [weightedPhysicalGradientCost,H,Cpt]
    ring
  constructor
  · apply absorb _ _ _ hcv
    change ‖iteratedFDeriv ℝ 1 (fun y => k⁻¹ • D.F.field t (Y t y)
      (Q.pointField P t (cylinderGraph P k D.m₀ (Y t y)))) x‖ ≤ _ at hv
    simpa only [norm_iteratedFDeriv_one,pow_one] using hv
  · have hscale : k*A.κ=1 := by rw [hκ]; exact mul_inv_cancel₀ hk0.ne'
    rw [Q.physicalPotential_hessian_norm D P X Y hX hXY hY k hscale t x,hκ,hm]
    apply absorb _ _ _ hcp
    change ‖iteratedFDeriv ℝ 1 (fun y => k⁻¹ • (D.FInv.field t (Y t y)).adjoint
      (Q.pointPressure P t (cylinderGraph P k D.m₀ (Y t y)))) x‖ ≤ _ at hpr
    simpa only [pow_one] using hpr

end EulerAllOrderDriftCorrection
