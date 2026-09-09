/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
public import LeanPool.NavierStokesAndEuler.Euler.TransverseFixedSpaceInverse
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.TimeLpCoefficientGevrey
import LeanPool.NavierStokesAndEuler.Euler.TransverseParameterRegularity
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Factorial coefficient estimates for the actual transverse form

The coefficient constants below are polynomial in the frame bounds and the
interval length. They control genuine Fréchet derivatives of the concrete
fixed-space operator and forcing, without a packaged jet or recurrence input.
-/

@[expose] public section


noncomputable section

open scoped ContDiff

namespace EulerTransverseCoefficientGevrey

open Set ContinuousLinearMap InnerProductSpace EulerTimeLp
  EulerTerminalTimePrimitive EulerVolterraConvolution EulerTimeH1OperatorProduct
  EulerTimeH1FrameTransport EulerTimeLpCoefficientMap EulerTimeLpCoefficientGevrey
  EulerOperatorGevreyCalculus EulerGevrey EulerTransverseVariationalInverse
  EulerTransverseGramInverse EulerTransverseFixedSpaceInverse
  EulerTransverseParameterRegularity

variable {P U E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The polynomial coefficient cost of taking a physical derivative. -/
def derivativeCost (T C₀ C₁ : ℝ) : ℝ := T*C₁+C₀

/-- The polynomial coefficient cost of the transported variational form. -/
def formCost (T C₀ C₁ CH : ℝ) : ℝ :=
  9 * (derivativeCost T C₀ C₁)^2 * (1 + T^2*CH)

/-- The polynomial cost of the actual weak forcing term. -/
def forcingCost (T C₀ C₁ : ℝ) : ℝ := 3 * (T * derivativeCost T C₀ C₁)

omit [CompleteSpace U] [CompleteSpace E] in
/-- Every actual derivative of the fixed kinetic map has the same factorial bound. -/
theorem fixedFrameDerivative_bound (T : ℝ) (hT : 0 ≤ T)
    (Q Q₁ : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (hQ : ContDiff ℝ ∞ Q) (hQ₁ : ContDiff ℝ ∞ Q₁)
    (R C₀ C₁ : ℝ) (hR : 0 ≤ R) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C₀ * majorant R 0 n)
    (hbQ₁ : ∀ n x, ‖iteratedFDeriv ℝ n Q₁ x‖ ≤ C₁ * majorant R 0 n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => fixedFrameDerivative T hT (Q y) (Q₁ y)) x‖ ≤
      derivativeCost T C₀ C₁ * majorant R 0 n := by
  have hb := clm_comp_const_right_bound
    (fun y => productDerivative T hT (Q y) (Q₁ y))
    (zeroTraceDerivatives (U := U) T hT).subtypeL
    (contDiff_productDerivative T hT Q Q₁ hQ hQ₁)
    R (derivativeCost T C₀ C₁) hR (by unfold derivativeCost; positivity) 0
    (productDerivative_bound T hT Q Q₁ hQ hQ₁ R C₀ C₁ hR hC₀ hC₁ 0 hbQ hbQ₁) n x
  apply hb.trans
  have hN : ‖(zeroTraceDerivatives (U := U) T hT).subtypeL‖ * derivativeCost T C₀ C₁ ≤
      derivativeCost T C₀ C₁ := by
    simpa only [one_mul] using (mul_le_mul_of_nonneg_right
      (zeroTraceDerivatives (U := U) T hT).norm_subtypeL_le
      (show 0 ≤ derivativeCost T C₀ C₁ by unfold derivativeCost; positivity))
  exact mul_le_mul_of_nonneg_right
    hN (majorant_nonneg R hR 0 n)

omit [CompleteSpace U] [CompleteSpace E] in
/-- Terminal integration adds only the interval-length factor. -/
theorem fixedFramePrimitive_bound (T : ℝ) (hT : 0 ≤ T)
    (Q Q₁ : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (hQ : ContDiff ℝ ∞ Q) (hQ₁ : ContDiff ℝ ∞ Q₁)
    (R C₀ C₁ : ℝ) (hR : 0 ≤ R) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C₀ * majorant R 0 n)
    (hbQ₁ : ∀ n x, ‖iteratedFDeriv ℝ n Q₁ x‖ ≤ C₁ * majorant R 0 n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => fixedFramePrimitive T hT (Q y) (Q₁ y)) x‖ ≤
      (T * derivativeCost T C₀ C₁) * majorant R 0 n := by
  have hb := clm_comp_const_left_bound (primitiveTimeLp (E := E) T hT)
    (fun y => fixedFrameDerivative T hT (Q y) (Q₁ y))
    (contDiff_fixedFrameDerivative T hT Q Q₁ hQ hQ₁)
    R (derivativeCost T C₀ C₁) hR (by unfold derivativeCost; positivity) 0
    (fixedFrameDerivative_bound T hT Q Q₁ hQ hQ₁ R C₀ C₁ hR hC₀ hC₁ hbQ hbQ₁) n x
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (primitive_norm_le_time (E := E) T hT)
      (by unfold derivativeCost; positivity)) (majorant_nonneg R hR 0 n))

/-- The physical Dirichlet form has the coefficient-only factorial bound. -/
theorem dirichletOperator_bound (T : ℝ) (hT : 0 ≤ T)
    (H : P → C(Icc (0 : ℝ) T, E →L[ℝ] E)) (hH : ContDiff ℝ ∞ H)
    (R CH : ℝ) (hR : 0 ≤ R) (hCH : 0 ≤ CH)
    (hbH : ∀ n x, ‖iteratedFDeriv ℝ n H x‖ ≤ CH * majorant R 0 n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => dirichletOperator (primitiveTimeLp T hT)
      (timeMultiplier T hT (H y))) x‖ ≤ (1+T^2*CH) * majorant R 0 n := by
  let J : TimeLp T E →L[ℝ] TimeLp T E := primitiveTimeLp T hT
  have hJ : ‖J‖ ≤ T := primitive_norm_le_time (E := E) T hT
  have hright (k : ℕ) (y : P) :
      ‖iteratedFDeriv ℝ k (fun z => (timeMultiplier T hT (H z)).comp J) y‖ ≤
      (T*CH) * majorant R 0 k := by
    exact (clm_comp_const_right_bound _ J (contDiff_timeMultiplier T hT H hH)
      R CH hR hCH 0 (timeMultiplier_bound T hT H hH R CH hR hCH 0 hbH) k y).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hJ hCH) (majorant_nonneg R hR 0 k))
  have hpotential (k : ℕ) (y : P) :
      ‖iteratedFDeriv ℝ k (fun z => J.adjoint.comp ((timeMultiplier T hT (H z)).comp J)) y‖ ≤
      (T^2*CH) * majorant R 0 k := by
    have hp := clm_comp_const_left_bound J.adjoint _
      ((contDiff_timeMultiplier T hT H hH).clm_comp contDiff_const)
      R (T*CH) hR (mul_nonneg hT hCH) 0 hright k y
    rw [LinearIsometryEquiv.norm_map] at hp
    apply hp.trans
    have h := mul_le_mul_of_nonneg_right hJ (mul_nonneg hT hCH)
    convert mul_le_mul_of_nonneg_right h (majorant_nonneg R hR 0 k) using 1
    ring
  exact sub_bound (fun _ : P => ContinuousLinearMap.id ℝ (TimeLp T E))
    (fun y => J.adjoint.comp ((timeMultiplier T hT (H y)).comp J))
    contDiff_const (contDiff_const.clm_comp ((contDiff_timeMultiplier T hT H hH).clm_comp
        contDiff_const))
    R 1 (T^2*CH) 0 (const_bound _ R 1 hR norm_id_le) hpotential n x

/-- Factorial control of the concrete fixed-space operator follows from the prescribed paths. -/
theorem fixedFrameOperator_bound (T : ℝ) (hT : 0 ≤ T)
    (Q Q₁ : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (H : P → C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (hQ : ContDiff ℝ ∞ Q) (hQ₁ : ContDiff ℝ ∞ Q₁) (hH : ContDiff ℝ ∞ H)
    (R C₀ C₁ CH : ℝ) (hR : 0 ≤ R) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hCH : 0 ≤ CH)
    (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C₀ * majorant R 0 n)
    (hbQ₁ : ∀ n x, ‖iteratedFDeriv ℝ n Q₁ x‖ ≤ C₁ * majorant R 0 n)
    (hbH : ∀ n x, ‖iteratedFDeriv ℝ n H x‖ ≤ CH * majorant R 0 n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => fixedFrameOperator T hT (Q y) (Q₁ y) (H y)) x‖ ≤
      formCost T C₀ C₁ CH * majorant R 0 n := by
  let D := fun y => fixedFrameDerivative T hT (Q y) (Q₁ y)
  let A := fun y => dirichletOperator (primitiveTimeLp T hT) (timeMultiplier T hT (H y))
  have hD : ContDiff ℝ ∞ D := contDiff_fixedFrameDerivative T hT Q Q₁ hQ hQ₁
  have hA : ContDiff ℝ ∞ A := contDiff_const.sub
    (contDiff_const.clm_comp ((contDiff_timeMultiplier T hT H hH).clm_comp contDiff_const))
  have hd0 : 0 ≤ derivativeCost T C₀ C₁ := by unfold derivativeCost; positivity
  have ha0 : 0 ≤ 1+T^2*CH := by positivity
  have hbD := fixedFrameDerivative_bound T hT Q Q₁ hQ hQ₁ R C₀ C₁ hR hC₀ hC₁ hbQ hbQ₁
  have hbA := dirichletOperator_bound T hT H hH R CH hR hCH hbH
  have hAD := clm_comp_bound A D hA hD R (1+T^2*CH) (derivativeCost T C₀ C₁)
    hR ha0 hd0 0 0 hbA hbD
  have h := clm_comp_bound (fun y => (D y).adjoint) (fun y => (A y).comp (D y))
    (contDiff_adjoint hD)
    (hA.clm_comp hD) R (derivativeCost T C₀ C₁) (3*(1+T^2*CH)*derivativeCost T C₀ C₁)
    hR hd0 (by positivity) 0 0 (adjoint_bound D hD R _ hR hd0 0 hbD) hAD n x
  have he : 3 * derivativeCost T C₀ C₁ * (3*(1+T^2*CH)*derivativeCost T C₀ C₁) =
      formCost T C₀ C₁ CH := by unfold formCost; ring
  simp only [Nat.add_zero, he] at h
  convert h using 1
  rfl

/-- The genuine weak right side has the input shift with a fixed polynomial cost. -/
theorem fixedForcing_bound (T : ℝ) (hT : 0 ≤ T)
    (Q Q₁ : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (hQ : ContDiff ℝ ∞ Q) (hQ₁ : ContDiff ℝ ∞ Q₁)
    (R C₀ C₁ : ℝ) (hR : 0 ≤ R) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C₀ * majorant R 0 n)
    (hbQ₁ : ∀ n x, ‖iteratedFDeriv ℝ n Q₁ x‖ ≤ C₁ * majorant R 0 n)
    (f : P → TimeLp T E) (hf : ContDiff ℝ ∞ f) (d : ℕ)
    (hbf : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n
      (fun y => (-(fixedFramePrimitive T hT (Q y) (Q₁ y)).adjoint) (f y)) x‖ ≤
      forcingCost T C₀ C₁ * majorant R d n := by
  let Z := fun y => fixedFramePrimitive T hT (Q y) (Q₁ y)
  have hZ : ContDiff ℝ ∞ Z := contDiff_fixedFramePrimitive T hT Q Q₁ hQ hQ₁
  have hZT : ContDiff ℝ ∞ (fun y => (Z y).adjoint) :=
    contDiff_adjoint hZ
  have hC : 0 ≤ T * derivativeCost T C₀ C₁ := by unfold derivativeCost; positivity
  have hbound := adjoint_bound Z hZ R (T * derivativeCost T C₀ C₁) hR hC 0
    (fixedFramePrimitive_bound T hT Q Q₁ hQ hQ₁ R C₀ C₁ hR hC₀ hC₁ hbQ hbQ₁)
  have hp (k : ℕ) (y : P) := clm_apply_bound (fun z => -(Z z).adjoint) f
    hZT.neg hf R (T * derivativeCost T C₀ C₁) 1 hR hC zero_le_one 0 d
    (neg_bound (fun z => (Z z).adjoint) R _ 0 hbound)
    (by simpa only [one_mul] using hbf) k y
  simpa only [forcingCost, mul_one, Nat.zero_add] using hp n x

end EulerTransverseCoefficientGevrey
