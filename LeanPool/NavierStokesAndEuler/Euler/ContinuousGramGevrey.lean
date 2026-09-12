/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ContinuousGramPath
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpGramGevrey
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathCalculus
import LeanPool.NavierStokesAndEuler.Euler.BoundedInverseGevrey
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.TransverseStrongEstimates
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Uniform-time factorial bounds for the actual Gram inverse

The inverse is a genuinely smooth continuous operator path. Applying the
frozen-coefficient recurrence in the uniform norm gives actual inverse-path
and solution estimates, without a Hilbert structure on the path space.
-/

@[expose] public section


noncomputable section

namespace EulerContinuousGramGevrey

open Set ContinuousLinearMap EulerContinuousTimeIntegral EulerContinuousPathCalculus
  EulerContinuousPathComposition EulerContinuousGramPath EulerTransverseGramInverse
  EulerTransverseGramPath EulerTransverseStrongEstimates EulerOperatorGevreyCalculus
  EulerTimeLpGramGevrey EulerGevrey
open scoped ContDiff

private theorem cost_bounds (c C D : ℝ) (hc : 0 < c) (hD : 0 ≤ D) :
    1 ≤ gramCost c C D ∧ c⁻¹*(3*C^2) ≤ gramCost c C D ∧ c⁻¹*D ≤ gramCost c C D := by
  have hi : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  unfold gramCost
  constructor
  · have h : 0 ≤ c⁻¹*(3*C^2+D+1) := by positivity
    linarith
  constructor <;> nlinarith [sq_nonneg C]

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instContinuousGramGevrey1 : NormedAddCommGroup (U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instContinuousGramGevrey2 : NormedSpace ℝ (U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,U →L[ℝ] U)` instance to shorten
typeclass synthesis. -/
local instance instContinuousGramGevrey3 (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,U →L[ℝ] U) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,U →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instContinuousGramGevrey4 (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,U →L[ℝ] U) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (C(Icc (0 : ℝ) T,U →L[ℝ] U) →L[ℝ] C(Icc (0 : ℝ) T,U
→L[ℝ] U))` instance to shorten typeclass synthesis. -/
local instance instContinuousGramGevrey5 (T : ℝ) : NormedAddCommGroup
    (C(Icc (0 : ℝ) T,U →L[ℝ] U) →L[ℝ] C(Icc (0 : ℝ) T,U →L[ℝ] U)) := inferInstance
/-- Cache the standard `NormedSpace ℝ (C(Icc (0 : ℝ) T,U →L[ℝ] U) →L[ℝ] C(Icc (0 : ℝ) T,U →L[ℝ]
U))` instance to shorten typeclass synthesis. -/
local instance instContinuousGramGevrey6 (T : ℝ) : NormedSpace ℝ
    (C(Icc (0 : ℝ) T,U →L[ℝ] U) →L[ℝ] C(Icc (0 : ℝ) T,U →L[ℝ] U)) := inferInstance

/-- Bounded left multiplication on continuous endomorphism paths, as a
bounded linear function of the actual coefficient path. -/
def leftMultiplicationMap (T : ℝ) :
    C(Icc (0 : ℝ) T,U →L[ℝ] U) →L[ℝ]
      C(Icc (0 : ℝ) T,U →L[ℝ] U) →L[ℝ] C(Icc (0 : ℝ) T,U →L[ℝ] U) :=
  (coefficientMap (K := Icc (0 : ℝ) T) (E := U →L[ℝ] U) (F := U →L[ℝ] U)).comp
    (compositionLift (K := Icc (0 : ℝ) T) (U := U) (E := U) (F := U))

omit [CompleteSpace U] in
theorem leftMultiplicationMap_norm (T : ℝ) : ‖leftMultiplicationMap (U := U) T‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  simp only [one_mul]
  apply opNorm_le_bound _ (norm_nonneg A)
  intro B
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg B))).2
  intro t
  exact (opNorm_comp_le (A t) (B t)).trans
    (mul_le_mul (A.norm_coe_le_norm t) (B.norm_coe_le_norm t) (norm_nonneg (B t)) (norm_nonneg A))

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  (T : ℝ) (Q : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hLower : ∀ x t v, c * ‖v‖ ^ 2 ≤ ‖Q x t v‖ ^ 2)
  (hQ : ContDiff ℝ ∞ Q)
  (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
  (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C * majorant Rc 0 n)

include hQ hRc hC hbQ

/-- The actual continuous inverse path has one factorial shift, uniformly in time. -/
theorem inversePath_gevrey (R : ℝ) (hR : 2 * gramCost c C 1 * (Rc + 1) ≤ R) (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => gramInversePath T (Q y) c hc (hLower y)) x‖ ≤
      majorant R 1 n := by
  let B := fun y => gramPath T (Q y)
  let V := fun y => gramInversePath T (Q y) c hc (hLower y)
  let A := fun y => leftMultiplicationMap (U := U) T (B y)
  let I := fun y => leftMultiplicationMap (U := U) T (V y)
  let onePath : C(Icc (0 : ℝ) T,U →L[ℝ] U) := ⟨fun _ => ContinuousLinearMap.id ℝ U,
      continuous_const⟩
  have hB : ContDiff ℝ ∞ B := gramPath_contDiff T Q hQ
  have hV : ContDiff ℝ ∞ V := gramInversePath_contDiff T c hc Q hLower hQ
  have hA : ContDiff ℝ ∞ A :=
    ContDiff.comp (g := leftMultiplicationMap (U := U) T) (f := B)
      (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
        (E := C(Icc (0 : ℝ) T,U →L[ℝ] U))
        (F := C(Icc (0 : ℝ) T,U →L[ℝ] U) →L[ℝ] C(Icc (0 : ℝ) T,U →L[ℝ] U))
        (leftMultiplicationMap (U := U) T)) hB
  have hsolve (y : P) : A y (V y) = onePath := by
    apply ContinuousMap.ext
    intro t
    apply ContinuousLinearMap.ext
    intro v
    exact gram_inverse_apply (Q y t) c hc (hLower y t) v
  have hleft (y : P) (p : C(Icc (0 : ℝ) T,U →L[ℝ] U)) : I y (A y p) = p := by
    apply ContinuousMap.ext
    intro t
    apply ContinuousLinearMap.ext
    intro v
    exact inverse_gram_apply (Q y t) c hc (hLower y t) (p t v)
  have hI (y : P) : ‖I y‖ ≤ c⁻¹ := by
    have h := ((leftMultiplicationMap (U := U) T).le_opNorm (V y)).trans
      (mul_le_mul_of_nonneg_right (leftMultiplicationMap_norm T) (norm_nonneg (V y)))
    exact (h.trans_eq (one_mul _)).trans (gramInversePath_norm T (Q y) c hc (hLower y))
  have hAall := contraction_bound (leftMultiplicationMap (U := U) T) (leftMultiplicationMap_norm T)
    B hB Rc (3*C^2) hRc (by positivity) 0 (gramPath_bound T Q hQ Rc C hRc hC hbQ)
  have hApos (j : ℕ) (y : P) : ‖iteratedFDeriv ℝ (j+1) A y‖ ≤
      (3*C^2)*(Rc^(j+1)*((j+1).factorial : ℝ)^2) := by
    simpa only [majorant, Nat.add_zero] using hAall (j+1) y
  obtain ⟨hM, hMC, hMD⟩ := cost_bounds c C 1 hc zero_le_one
  have hR0 : 0 ≤ R := by nlinarith
  have hone : ‖onePath‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ zero_le_one).2
    intro t
    exact norm_id_le
  exact EulerBoundedInverseGevrey.solution_gevrey A V (fun _ : P => onePath)
    hA hV contDiff_const hsolve I hleft c⁻¹ (3*C^2) 1 (gramCost c C 1) Rc R
    (by positivity) zero_le_one hM hMC hMD hRc hR hI hApos 0
    (const_bound onePath R 1 hR0 hone) n x

/-- The actual continuous solution has the same one-shift inverse estimate. -/
theorem solution_gevrey (f : P → C(Icc (0 : ℝ) T, U)) (hf : ContDiff ℝ ∞ f)
    (D R : ℝ) (hD : 0 ≤ D) (hR : 2 * gramCost c C D * (Rc + 1) ≤ R)
    (d : ℕ) (hbf : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ D * majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => solve T (Q y) c hc (hLower y) (f y)) x‖ ≤
      majorant R (d+1) n := by
  let A := fun y => multiplier (gramPath T (Q y))
  let V := fun y => solve T (Q y) c hc (hLower y) (f y)
  let I := fun y => solve T (Q y) c hc (hLower y)
  have hB := gramPath_contDiff T Q hQ
  have hA : ContDiff ℝ ∞ A := contDiff_multiplier (fun y => gramPath T (Q y)) hB
  have hV : ContDiff ℝ ∞ V := solve_contDiff T c hc Q hLower f hQ hf
  have hAall := multiplier_bound (fun y => gramPath T (Q y)) hB Rc (3*C^2) hRc
    (by positivity) 0 (gramPath_bound T Q hQ Rc C hRc hC hbQ)
  have hApos (j : ℕ) (y : P) : ‖iteratedFDeriv ℝ (j+1) A y‖ ≤
      (3*C^2)*(Rc^(j+1)*((j+1).factorial : ℝ)^2) := by
    simpa only [majorant, Nat.add_zero] using hAall (j+1) y
  obtain ⟨hM, hMC, hMD⟩ := cost_bounds c C D hc hD
  exact EulerBoundedInverseGevrey.solution_gevrey A V f hA hV hf
    (fun y => solve_equation T (Q y) c hc (hLower y) (f y)) I
    (fun y => solve_left_inverse T (Q y) c hc (hLower y))
    c⁻¹ (3*C^2) D (gramCost c C D) Rc R (by positivity) hD hM hMC hMD hRc hR
    (fun y => solve_norm T (Q y) c hc (hLower y)) hApos d hbf n x

end EulerContinuousGramGevrey
