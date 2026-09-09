/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
public import LeanPool.NavierStokesAndEuler.Euler.SmoothBanachFlow
import LeanPool.NavierStokesAndEuler.Euler.GevreyComposition
import LeanPool.NavierStokesAndEuler.Euler.GevreyFixedShift
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowGevrey
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Polynomial-radius bounds for the velocity and material acceleration
of the constructed flow.  The second expression is literally
`(A₁ + D A · A) ∘ Φ`; identifying A₁ as the time derivative is a separate
qualitative chain rule, not an assumption about its size. -/

@[expose] public section


noncomputable section

open Set
open scoped ContDiff BoundedContinuousFunction

namespace EulerSmoothFlowGevrey

open EulerSmoothBanachFlow EulerGevreyGeneratingDerivatives
  EulerGevreyComposition EulerGevrey EulerOperatorGevreyCalculus

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (T : ℝ) (hT : 0 ≤ T) (A : SmoothTimeField (Icc (0 : ℝ) T) E E)

/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] E)` instance to shorten typeclass
synthesis. -/
local instance instSmoothFlowTimeGevrey1 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instSmoothFlowTimeGevrey2 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instSmoothFlowTimeGevrey3 (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] E)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instSmoothFlowTimeGevrey4 (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] E)) :=
    inferInstance

/-- Flow radius, given by `(4*R+1)*((1+B*T)*S+2)`. -/
def flowRadius (B R T S : ℝ) : ℝ := (4*R+1)*((1+B*T)*S+2)

omit [FiniteDimensional ℝ E] in
theorem field_jet_bound (B R : ℝ)
    (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
    (n : ℕ) (t : Icc (0 : ℝ) T) (x : E) :
    ‖iteratedFDeriv ℝ n (A.field t : E → E) x‖ ≤ B*R^n*(n.factorial : ℝ)^2 := by
  rw [← A.jet_eq]
  exact ((A.jet n t).norm_coe_le_norm x).trans
    (((A.jet n).norm_coe_le_norm t).trans (hb n))

theorem forward_positive_bound (B R : ℝ)
    (hB : 0 ≤ B) (hR : 0 < R) (hsmall : B * R * T ≤ 1 / 8)
    (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
    (n : ℕ) (hn : 0 < n) (t : Icc (0 : ℝ) T) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => (flowData T hT A).forward t y) x‖ ≤
      (1+B*T)*(4*R+1)^n*(n.factorial : ℝ)^2 := by
  have he : (fun y => (flowData T hT A).forward t y) = id+displacement T hT A t := by
    funext y
    change (flowData T hT A).forward t y = y+displacement T hT A t y
    rw [displacement_eq]
    abel
  rw [he, iteratedFDeriv_add_apply contDiffAt_id
    ((displacement_contDiff T hT A t).contDiffAt.of_le (by simp))]
  have hi : ‖iteratedFDeriv ℝ n (id : E → E) x‖ ≤ 1 := by
    have h := norm_iteratedFDeriv_id_le n hn x
    split_ifs at h <;> linarith
  let W := (4*R+1)^n*(n.factorial : ℝ)^2
  have hfact : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
  have hW : 1 ≤ W := by
    have hp : (1 : ℝ) ≤ (4*R+1)^n := one_le_pow₀ (by linarith)
    have hf : (1 : ℝ) ≤ (n.factorial : ℝ)^2 := by nlinarith
    calc
      (1 : ℝ) = 1*1 := by ring
      _ ≤ W := mul_le_mul hp hf (by norm_num) (by positivity)
  have hdisp : ‖iteratedFDeriv ℝ n (displacement T hT A t) x‖ ≤ B*T*W := by
    have htB : B*(t : ℝ) ≤ B*T := mul_le_mul_of_nonneg_left t.property.2 hB
    have hp : (4*R)^n ≤ (4*R+1)^n := pow_le_pow_left₀ (by positivity) (by linarith) n
    have hm := mul_le_mul htB hp (pow_nonneg (show 0 ≤ 4*R by positivity) n) (mul_nonneg hB hT)
    have hs := mul_le_mul_of_nonneg_right hm (sq_nonneg (n.factorial : ℝ))
    exact (displacement_positive_bound T hT A B R hB hR hsmall hb n hn t t.property x).trans
      (hs.trans_eq (by dsimp [W]; ring))
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (id : E → E) x‖+
        ‖iteratedFDeriv ℝ n (displacement T hT A t) x‖ := norm_add_le _ _
    _ ≤ 1+B*T*W := add_le_add hi hdisp
    _ ≤ W+B*T*W := add_le_add hW le_rfl
    _ = _ := by dsimp [W]; ring

/-- Material velocity, given by `A.field t ((flowData T hT A).forward t x)`. -/
def materialVelocity (t : Icc (0 : ℝ) T) (x : E) : E :=
  A.field t ((flowData T hT A).forward t x)

theorem materialVelocity_bound (B R : ℝ)
    (hB : 0 ≤ B) (hR : 0 < R) (hsmall : B * R * T ≤ 1 / 8)
    (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
    (n : ℕ) (t : Icc (0 : ℝ) T) (x : E) :
    ‖iteratedFDeriv ℝ n (materialVelocity T hT A t) x‖ ≤
      B*(flowRadius B R T R)^n*(n.factorial : ℝ)^2 := by
  apply norm_iteratedFDeriv_comp_gevrey
    (fun y => (flowData T hT A).forward t y) (A.field t : E → E)
    (forward_contDiff T hT A t) (A.smooth t)
    B (1+B*T) (4*R+1) R hB (by positivity) (by positivity) hR.le
  · intro j y
    exact field_jet_bound T A B R hb j t y
  · intro j hj y
    exact forward_positive_bound T hT A B R hB hR hsmall hb j hj t y

/-- Acceleration field, given by `A₁.field t x + fderiv ℝ (A.field t : E → E) x (A.field t x)`. -/
def accelerationField (A₁ : SmoothTimeField (Icc (0 : ℝ) T) E E)
    (t : Icc (0 : ℝ) T) (x : E) : E :=
  A₁.field t x + fderiv ℝ (A.field t : E → E) x (A.field t x)

omit [FiniteDimensional ℝ E] in
theorem accelerationField_contDiff (A₁ : SmoothTimeField (Icc (0 : ℝ) T) E E)
    (t : Icc (0 : ℝ) T) : ContDiff ℝ ∞ (accelerationField T A A₁ t) :=
  (A₁.smooth t).add (((A.smooth t).fderiv_right (m := ∞) (by simp)).clm_apply (A.smooth t))

omit [FiniteDimensional ℝ E] in
theorem accelerationField_bound (A₁ : SmoothTimeField (Icc (0 : ℝ) T) E E)
    (B R B₁ R₁ : ℝ) (hB : 0 ≤ B) (hR : 0 < R) (hB₁ : 0 ≤ B₁) (hR₁ : 0 ≤ R₁)
    (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
    (hb₁ : ∀ n, ‖A₁.jet n‖ ≤ B₁ * R₁ ^ n * (n.factorial : ℝ) ^ 2)
    (n : ℕ) (t : Icc (0 : ℝ) T) (x : E) :
    ‖iteratedFDeriv ℝ n (accelerationField T A A₁ t) x‖ ≤
      (B₁+3*B^2*R)*majorant (4*R+R₁) 0 n := by
  have hS : 0 ≤ 4*R+R₁ := by positivity
  have hA (j : ℕ) (y : E) : ‖iteratedFDeriv ℝ j (A.field t : E → E) y‖ ≤
      B*majorant (4*R+R₁) 0 j := by
    have hh := field_jet_bound T A B R hb j t y
    apply hh.trans
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (majorant_radius_mono R (4*R+R₁) hR.le (by linarith) 0 j) hB
  have hA₁ (j : ℕ) (y : E) : ‖iteratedFDeriv ℝ j (A₁.field t : E → E) y‖ ≤
      B₁*majorant (4*R+R₁) 0 j := by
    have hh := field_jet_bound T A₁ B₁ R₁ hb₁ j t y
    apply hh.trans
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (majorant_radius_mono R₁ (4*R+R₁) hR₁ (by linarith) 0 j) hB₁
  have hDA (j : ℕ) (y : E) : ‖iteratedFDeriv ℝ j (fderiv ℝ (A.field t : E → E)) y‖ ≤
      (B*R)*majorant (4*R+R₁) 0 j := by
    rw [norm_iteratedFDeriv_fderiv]
    have hh := field_jet_bound T A B R hb (j+1) t y
    calc
      _ ≤ B*majorant R 1 j := by simpa only [majorant, mul_assoc] using hh
      _ ≤ B*(R*majorant (4*R) 0 j) :=
        mul_le_mul_of_nonneg_left (majorant_one_le_radius_four R hR.le j) hB
      _ ≤ (B*R)*majorant (4*R+R₁) 0 j := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (majorant_radius_mono (4*R) (4*R+R₁) (by positivity) (by linarith) 0 j)
          (mul_nonneg hB hR.le)
  have hprod := clm_apply_bound (fderiv ℝ (A.field t : E → E)) (A.field t)
    ((A.smooth t).fderiv_right (m := ∞) (by simp)) (A.smooth t)
    (4*R+R₁) (B*R) B hS (mul_nonneg hB hR.le) hB 0 0 hDA hA
  have he := add_bound (A₁.field t : E → E)
    (fun y => fderiv ℝ (A.field t : E → E) y (A.field t y))
    (A₁.smooth t) (((A.smooth t).fderiv_right (m := ∞) (by simp)).clm_apply (A.smooth t))
    (4*R+R₁) B₁ (3*(B*R)*B) 0 hA₁ hprod n x
  have hconst : B₁+3*(B*R)*B = B₁+3*B^2*R := by ring
  change ‖iteratedFDeriv ℝ n (fun y => A₁.field t y +
    fderiv ℝ (A.field t : E → E) y (A.field t y)) x‖ ≤ _
  simpa only [hconst] using he

/-- Material acceleration, given by `accelerationField T A A₁ t ((flowData T hT A).forward t
x)`. -/
def materialAcceleration (A₁ : SmoothTimeField (Icc (0 : ℝ) T) E E)
    (t : Icc (0 : ℝ) T) (x : E) : E :=
  accelerationField T A A₁ t ((flowData T hT A).forward t x)

theorem materialAcceleration_bound (A₁ : SmoothTimeField (Icc (0 : ℝ) T) E E)
    (B R B₁ R₁ : ℝ) (hB : 0 ≤ B) (hR : 0 < R) (hB₁ : 0 ≤ B₁) (hR₁ : 0 ≤ R₁)
    (hsmall : B * R * T ≤ 1 / 8)
    (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
    (hb₁ : ∀ n, ‖A₁.jet n‖ ≤ B₁ * R₁ ^ n * (n.factorial : ℝ) ^ 2)
    (n : ℕ) (t : Icc (0 : ℝ) T) (x : E) :
    ‖iteratedFDeriv ℝ n (materialAcceleration T hT A A₁ t) x‖ ≤
      (B₁+3*B^2*R)*(flowRadius B R T (4*R+R₁))^n*(n.factorial : ℝ)^2 := by
  apply norm_iteratedFDeriv_comp_gevrey
    (fun y => (flowData T hT A).forward t y) (accelerationField T A A₁ t)
    (forward_contDiff T hT A t) (accelerationField_contDiff T A A₁ t)
    (B₁+3*B^2*R) (1+B*T) (4*R+1) (4*R+R₁)
    (by positivity) (by positivity) (by positivity) (by positivity)
  · intro j y
    simpa only [majorant, Nat.add_zero, mul_assoc] using
      accelerationField_bound T A A₁ B R B₁ R₁ hB hR hB₁ hR₁ hb hb₁ j t y
  · intro j hj y
    exact forward_positive_bound T hT A B R hB hR hsmall hb j hj t y

end EulerSmoothFlowGevrey
