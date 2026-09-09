/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInverseFlowGevrey

@[expose] public section

/-! A finite-order Sobolev composition constant obtained from the actual
parent deformation. No inverse-flow derivative budget is assumed. -/

noncomputable section

namespace EulerPacketInverseFlowGevrey

open Set EulerSmoothLimit EulerGevrey EulerPacketPiola
open scoped ContDiff BoundedContinuousFunction

def finiteOrderConstant (C R : ℝ) (n : ℕ) : ℝ :=
  1+9*C^2*(sourceInverseRadius C R)^n*(n.factorial : ℝ)^2

theorem sourceInverseRadius_one_le (C R : ℝ) (hR : 0 ≤ R) :
    1 ≤ sourceInverseRadius C R := by
  unfold sourceInverseRadius
  have h : 0 ≤ 18*C^2*R := by positivity
  linarith

theorem finiteOrderConstant_one_le (C R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    1 ≤ finiteOrderConstant C R n := by
  have hL := (sourceInverseRadius_pos C R hR).le
  unfold finiteOrderConstant
  have h : 0 ≤ 9*C^2*(sourceInverseRadius C R)^n*(n.factorial : ℝ)^2 := by positivity
  linarith

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)
  (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hY : ∀ t, Differentiable ℝ (Y t))
  (hXY : ∀ t x, X t (Y t x) = x)
  (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
  (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
  (hF : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F.field t : Space → (Space →L[ℝ] Space)) x‖ ≤ C*majorant R 0 n)

include hX hY hXY hR hC hdet hF in
theorem inverseFlow_finiteOrderBound (n i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖iteratedFDeriv ℝ i (Y t) x‖ ≤ (finiteOrderConstant C R n)^i := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  have hjn : j ≤ n := by omega
  have hL := sourceInverseRadius_one_le C R hR
  have hD := finiteOrderConstant_one_le C R hR n
  have hfac : (j.factorial : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hjn
  have hbound : 9*C^2*(sourceInverseRadius C R)^j*(j.factorial : ℝ)^2 ≤
      9*C^2*(sourceInverseRadius C R)^n*(n.factorial : ℝ)^2 := by
    gcongr
  calc
    _ ≤ 9*C^2*(sourceInverseRadius C R)^j*(j.factorial : ℝ)^2 :=
      inverseFlow_gevrey D X Y hX hY hXY R C hR hC hdet hF j t x
    _ ≤ finiteOrderConstant C R n := by
      exact hbound.trans (by unfold finiteOrderConstant; linarith)
    _ = (finiteOrderConstant C R n)^1 := (pow_one _).symm
    _ ≤ _ := pow_le_pow_right₀ hD hi

end EulerPacketInverseFlowGevrey
