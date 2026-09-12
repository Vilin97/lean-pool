/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCofactorOperator
public import LeanPool.NavierStokesAndEuler.Euler.GevreyInverseMap
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketData
import LeanPool.NavierStokesAndEuler.Euler.PacketParentCoefficientBounds

/-!
# The actual inverse parent flow preserves source Gevrey regularity

The inverse derivative bounds are derived from the prescribed deformation
and its determinant-one cofactor identity.  Neither inverse-flow jets nor
inverse-deformation jets are independent assumptions.
-/

@[expose] public section


noncomputable section

open scoped ContDiff BoundedContinuousFunction

namespace EulerPacketInverseFlowGevrey

open Set EulerSmoothLimit EulerGevrey EulerGevreyComposition EulerPacketCofactor
  EulerPacketPiola

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)
  (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hY : ∀ t, Differentiable ℝ (Y t))
  (hXY : ∀ t x, X t (Y t x) = x)

include hX hY hXY in
theorem inverseFlow_fderiv (t : Icc (0 : ℝ) D.T) (x : Space) :
    fderiv ℝ (Y t) x = D.FInv.field t (Y t x) := by
  apply fderiv_eq_inverse_field (X t) (Y t) (D.FInv.field t)
    (fun y => (hX t y).differentiableAt) (hY t) (hXY t)
  intro y v
  rw [(hX t y).fderiv]
  exact D.inverse_left t y v

include hX hY hXY in
theorem inverseFlow_contDiff (t : Icc (0 : ℝ) D.T) : ContDiff ℝ ∞ (Y t) :=
  contDiff_of_fderiv_eq_comp (Y t) (D.FInv.field t) (hY t) (D.FInv.smooth t)
    (inverseFlow_fderiv D X Y hX hY hXY t)

/-- Source inverse radius, given by `1 + 18*C^2*R`. -/
def sourceInverseRadius (C R : ℝ) : ℝ := 1 + 18*C^2*R

lemma sourceInverseRadius_eq (C R : ℝ) :
    sourceInverseRadius C R = inverseMapRadius (9*C^2) R := by
  unfold sourceInverseRadius inverseMapRadius
  ring

lemma sourceInverseRadius_pos (C R : ℝ) (hR : 0 ≤ R) :
    0 < sourceInverseRadius C R := by
  rw [sourceInverseRadius_eq]
  exact inverseMapRadius_pos _ R (by positivity) hR

variable (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
  (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
  (hF : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F.field t : Space → EndSpace) x‖ ≤ C * majorant R 0 n)

include hX hY hXY hR hC hdet hF in
theorem inverseFlow_gevrey (n : ℕ) (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖iteratedFDeriv ℝ (n+1) (Y t) x‖ ≤
      (9*C^2) * (sourceInverseRadius C R)^n * (n.factorial : ℝ)^2 := by
  rw [sourceInverseRadius_eq]
  apply norm_iteratedFDeriv_of_fderiv_eq_comp (Y t) (D.FInv.field t)
    (inverseFlow_contDiff D X Y hX hY hXY t) (D.FInv.smooth t)
    (inverseFlow_fderiv D X Y hX hY hXY t) (9*C^2) R (by positivity) hR
  intro j y
  simpa only [majorant, Nat.add_zero, mul_assoc] using
    coefficientInverse_bound D.F D.FInv.field hdet D.inverse_left R C hR hC hF j t y

include hX hY hXY hR hC hdet hF in
/-- The coordinate change in the physical packet only changes the fixed
Gevrey radius; the small correction amplitude is retained exactly. -/
theorem pullback_gevrey {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : Icc (0 : ℝ) D.T → Space → V) (hg : ∀ t, ContDiff ℝ ∞ (g t))
    (A S : ℝ) (hA : 0 ≤ A) (hS : 0 ≤ S)
    (hgjet : ∀ n t x, ‖iteratedFDeriv ℝ n (g t) x‖ ≤ A * S ^ n * (n.factorial : ℝ) ^ 2)
    (n : ℕ) (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (fun y => g t (Y t y)) x‖ ≤
      A * (sourceInverseRadius C R * (9*C^2*S+2))^n * (n.factorial : ℝ)^2 := by
  rw [sourceInverseRadius_eq]
  apply norm_iteratedFDeriv_comp_of_fderiv_eq_comp (Y t) (D.FInv.field t) (g t)
    (hY t) (D.FInv.smooth t) (hg t) (inverseFlow_fderiv D X Y hX hY hXY t)
    (9*C^2) R A S (by positivity) hR hA hS
  · intro j y
    simpa only [majorant, Nat.add_zero, mul_assoc] using
      coefficientInverse_bound D.F D.FInv.field hdet D.inverse_left R C hR hC hF j t y
  · exact fun j y => hgjet j t y

end EulerPacketInverseFlowGevrey
