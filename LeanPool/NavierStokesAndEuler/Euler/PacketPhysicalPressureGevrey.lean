/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalFrequencyBounds

@[expose] public section

/-! The physical pressure force κF⁻ᵀp has the same fixed polynomial
frequency losses as the velocity correction. The inverse-transpose
coefficient bounds follow from the actual determinant-one deformation. -/

noncomputable section

namespace EulerPacketPhysicalGevrey

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerMetricTransport EulerCylinderSobolev
  EulerCylinderPhysicalTensor EulerPacketInverseFlowGevrey EulerPacketPiola
  EulerOperatorGevreyCalculus EulerGevrey EulerTransverseGramInverse EulerPacketCofactor
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (P κ k : ℝ)
  (e : Icc (0 : ℝ) D.T → LiftDomain P → Space)
  (he : ∀ t x, ContDiff ℝ ∞ (localFieldLift P (e t) x))

def graphPressureForce (t : Icc (0 : ℝ) D.T) (x : Space) : Space :=
  κ • (D.FInv.field t x).adjoint (physicalField P k D.m₀ (e t) x)

include he in
theorem graphPressureForce_contDiff (t : Icc (0 : ℝ) D.T) :
    ContDiff ℝ ∞ (graphPressureForce D P κ k e t) :=
  ((((realAdjoint (U := Space) (E := Space)).contDiff.comp (D.FInv.smooth t))).clm_apply
    (physicalField_contDiff P k D.m₀ (e t) (he t))).const_smul κ

variable (R C A S : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hA : 0 ≤ A) (hS : 0 ≤ S)
  (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det=1)
  (hF : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F.field t : Space → (Space →L[ℝ] Space)) x‖ ≤ C*majorant R 0 n)
  (hb : ∀ n t x, (∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w (e t) x‖) ≤
    A*S^n*(n.factorial : ℝ)^2)

include hR hC hdet hF in
theorem inverseTranspose_gevrey (n : ℕ) (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (fun y => (D.FInv.field t y).adjoint) x‖ ≤
      (9*C^2)*majorant R 0 n :=
  adjoint_bound (D.FInv.field t) (D.FInv.smooth t) R (9*C^2) hR (by positivity) 0
    (fun j y => coefficientInverse_bound D.F D.FInv.field hdet D.inverse_left R C hR hC hF j t y) n
      x

include he hR hC hA hS hdet hF hb in
theorem graphPressureForce_gevrey (n : ℕ) (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (graphPressureForce D P κ k e t) x‖ ≤
      (|κ| *27*C^2*A)*majorant (R+frequencyFactor k D.m₀*S) 0 n := by
  let Rg := R+frequencyFactor k D.m₀*S
  have hRg : 0 ≤ Rg := add_nonneg hR (mul_nonneg (frequencyFactor_nonneg k D.m₀) hS)
  have hFR : ∀ n x, ‖iteratedFDeriv ℝ n (fun y => (D.FInv.field t y).adjoint) x‖ ≤
      (9*C^2)*majorant Rg 0 n := fun n x => (inverseTranspose_gevrey D R C hR hC hdet hF n t
        x).trans
    (mul_le_mul_of_nonneg_left (majorant_radius_mono R Rg hR
      (le_add_of_nonneg_right (mul_nonneg (frequencyFactor_nonneg k D.m₀) hS)) 0 n) (by positivity))
  have heR : ∀ n x, ‖iteratedFDeriv ℝ n (physicalField P k D.m₀ (e t)) x‖ ≤
      A*majorant Rg 0 n := fun n x =>
    (physicalField_gevrey P k D.m₀ (e t) (he t) A S (fun n x => hb n t x) n x).trans
      (mul_le_mul_of_nonneg_left (majorant_radius_mono (frequencyFactor k D.m₀*S) Rg
        (mul_nonneg (frequencyFactor_nonneg k D.m₀) hS) (le_add_of_nonneg_left hR) 0 n) hA)
  have hI : ContDiff ℝ ∞ (fun y => (D.FInv.field t y).adjoint) :=
    (realAdjoint (U := Space) (E := Space)).contDiff.comp (D.FInv.smooth t)
  have hprod := clm_apply_bound (fun y => (D.FInv.field t y).adjoint) (physicalField P k D.m₀ (e t))
    hI (physicalField_contDiff P k D.m₀ (e t) (he t)) Rg (9*C^2) A hRg (by positivity) hA 0 0 hFR
      heR n x
  change ‖iteratedFDeriv ℝ n (fun y => κ • ((D.FInv.field t y).adjoint
    (physicalField P k D.m₀ (e t) y))) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply'
    ((hI.clm_apply (physicalField_contDiff P k D.m₀ (e t) (he t))).contDiffAt.of_le
      (by simp : (n : ℕ∞ω) ≤ ∞)),norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left hprod (abs_nonneg κ)).trans_eq (by simp only [Nat.zero_add];
    ring)

variable (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hY : ∀ t, Differentiable ℝ (Y t))
  (hXY : ∀ t x, X t (Y t x)=x)

def physicalPressureForce (t : Icc (0 : ℝ) D.T) (x : Space) : Space :=
  graphPressureForce D P κ k e t (Y t x)

include he hR hC hA hS hF hb hX hY hXY hdet in
theorem physicalPressureForce_gevrey (n : ℕ) (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (physicalPressureForce D P κ k e Y t) x‖ ≤
      (|κ| *27*C^2*A)*(physicalRadius D k R C S)^n*(n.factorial : ℝ)^2 := by
  apply pullback_gevrey D X Y hX hY hXY R C hR hC hdet hF
    (graphPressureForce D P κ k e) (graphPressureForce_contDiff D P κ k e he)
    (|κ| *27*C^2*A) (R+frequencyFactor k D.m₀*S) (by positivity)
    (add_nonneg hR (mul_nonneg (frequencyFactor_nonneg k D.m₀) hS)) _ n t x
  intro j s y
  simpa only [majorant,Nat.add_zero,mul_assoc] using
    graphPressureForce_gevrey D P κ k e he R C A S hR hC hA hS hdet hF hb j s y

include he hR hC hA hS hF hb hX hY hXY hdet in
theorem physicalPressureForce_power_bound (hk : 1 ≤ k) (hκ : |κ| ≤ 1)
    (n : ℕ) (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (physicalPressureForce D P κ k e Y t) x‖ ≤
      (9*C*physicalFixedCost D R C S n)*A*k^n := by
  have h := physicalPressureForce_gevrey D P κ k e he R C A S hR hC hA hS hdet hF hb
    X Y hX hY hXY n t x
  have hL := (sourceInverseRadius_pos C R hR).le
  have hr : 0 ≤ physicalRadius D k R C S := by
    unfold physicalRadius
    have hf := frequencyFactor_nonneg k D.m₀
    positivity
  have ha : |κ| *27*C^2*A ≤ 27*C^2*A := by
    simpa only [one_mul,mul_assoc] using
      mul_le_mul_of_nonneg_right hκ (by positivity : 0 ≤ 27*C^2*A)
  have hbnd := mul_le_mul ha
    (pow_le_pow_left₀ hr (physicalRadius_le_linear D k R C S hk hR hS) n)
    (pow_nonneg hr n) (by positivity)
  exact h.trans ((mul_le_mul_of_nonneg_right hbnd (sq_nonneg (n.factorial : ℝ))).trans_eq
    (by unfold physicalFixedCost; rw [mul_pow]; ring))

end EulerPacketPhysicalGevrey
