/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevTensorInverse
public import LeanPool.NavierStokesAndEuler.Euler.TransverseFixedEvolution
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevProductGevrey
import LeanPool.NavierStokesAndEuler.Euler.TransverseParameterRegularity
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import LeanPool.NavierStokesAndEuler.Euler.HilbertCoerciveGevrey
import LeanPool.NavierStokesAndEuler.Euler.TimeLpCoefficientGevrey
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
public import LeanPool.NavierStokesAndEuler.Euler.TransverseFixedSpaceInverse

/-!
# Same-radius fixed-Sobolev estimates for the actual transverse history

The finite base order stays inside each external word. Only coefficient
tensor bounds are converted to word sums; forcing and solution use the same
external radius and base order. The recurrence is applied to the actual
coercive inverse, with its proved polynomial norm bound.
-/

section

/-!
# Uniform factorial estimates for the constructed transverse inverse

Every constant is an explicit polynomial in the interval length, frame
bounds, potential bound, and reciprocal frame lower bound. The same radius
works at every derivative order and input shift. The recurrence is derived
from the actual inverse equation, not assumed for an abstract jet.
-/

section

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

end
end

end

@[expose] public section

noncomputable section

open scoped ContDiff

namespace EulerTransverseGevreyInverse

open Set InnerProductSpace ContinuousLinearMap EulerTimeLp EulerTerminalTimePrimitive
  EulerTimeH1FrameTransport EulerTransverseFixedSpaceInverse
  EulerTransverseParameterRegularity EulerTransverseCoefficientGevrey
  EulerHilbertCoerciveGevrey EulerOperatorGevreyCalculus EulerGevrey
  EulerCoerciveProjection EulerTransverseGramInverse EulerTransverseCoordinateRegularity
  EulerTransverseVariationalInverse EulerVolterraConvolution EulerTimeLpCoefficientMap
  EulerTimeLpCoefficientGevrey

/-- Uniform polynomial bound for the inverse frame transport. -/
def transportCeiling (T C₀ C₁ c : ℝ) : ℝ :=
  1 + ((2*(c⁻¹)^2*C₀^2*C₁ + c⁻¹*C₁)*T + c⁻¹*C₀)

/-- Uniform polynomial bound for the inverse of the transported form. -/
def inverseCost (T C₀ C₁ c : ℝ) : ℝ := 2 * (transportCeiling T C₀ C₁ c)^2

/-- One polynomial top constant handles both coefficient and forcing amplitudes. -/
def solveCost (T C₀ C₁ CH c : ℝ) : ℝ :=
  1 + inverseCost T C₀ C₁ c * (formCost T C₀ C₁ CH + forcingCost T C₀ C₁ + 1)

variable {P U E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace U] [CompleteSpace E] in
/-- The explicit fixed-space coercivity gives the promised polynomial inverse bound. -/
theorem fixedCoercivity_inv_le (T : ℝ) (hT : 0 ≤ T)
    (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (c : ℝ) (hc : 0 < c) (C₀ C₁ : ℝ)
    (hQ : ‖Q‖ ≤ C₀) (hQ₁ : ‖Q₁‖ ≤ C₁) :
    (fixedCoercivity T Q Q₁ c)⁻¹ ≤ inverseCost T C₀ C₁ c := by
  have ht : transportCost T Q Q₁ c ≤ transportCeiling T C₀ C₁ c := by
    unfold transportCost transportCeiling
    gcongr
  have ht0 := (transportCost_pos T hT Q Q₁ c hc).le
  have he : (fixedCoercivity T Q Q₁ c)⁻¹ = 2*(transportCost T Q Q₁ c)^2 := by
    simp only [fixedCoercivity, div_eq_mul_inv, mul_inv_rev, inv_pow, inv_inv]
  rw [he]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 ht 2) (by norm_num)

/-- The top constant is at least one for all nonnegative coefficient bounds. -/
theorem solveCost_one_le (T C₀ C₁ CH c : ℝ)
    (hT : 0 ≤ T) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hCH : 0 ≤ CH) :
    1 ≤ solveCost T C₀ C₁ CH c := by
  unfold solveCost
  have h : 0 ≤ inverseCost T C₀ C₁ c *
      (formCost T C₀ C₁ CH + forcingCost T C₀ C₁ + 1) := by
    unfold inverseCost formCost forcingCost derivativeCost
    positivity
  linarith

variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (H : P → C(Icc (0 : ℝ) T, E →L[ℝ] E))
  (c : ℝ) (hc : 0 < c)
  (hLower : ∀ x t v, c * ‖v‖ ^ 2 ≤ ‖Q x t v‖ ^ 2)
  (hd : ∀ x (t : Icc (0 : ℝ) T),
    HasDerivWithinAt (EulerVolterraConvolution.extendPath T hT (Q x)) (Q₁ x t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K)
  (hPotential : ∀ x t v, ⟪H x t v, v⟫_ℝ ≤ K * ‖v‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)
  (hQ : ContDiff ℝ ∞ Q) (hQ₁ : ContDiff ℝ ∞ Q₁) (hH : ContDiff ℝ ∞ H)
  (Rc C₀ C₁ CH : ℝ) (hRc : 0 ≤ Rc)
  (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hCH : 0 ≤ CH)
  (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C₀ * majorant Rc 0 n)
  (hbQ₁ : ∀ n x, ‖iteratedFDeriv ℝ n Q₁ x‖ ≤ C₁ * majorant Rc 0 n)
  (hbH : ∀ n x, ‖iteratedFDeriv ℝ n H x‖ ≤ CH * majorant Rc 0 n)

include hQ hQ₁ hH hRc hC₀ hC₁ hCH hbQ hbQ₁ hbH in
/-- The actual zero-endpoint coordinate solve has a single-shift factorial
bound with a radius uniform in the derivative order and input shift. -/
theorem fixedFrameSolution_gevrey
    (R : ℝ) (hR : 2 * solveCost T C₀ C₁ CH c * (Rc + 1) ≤ R)
    (f : P → TimeLp T E) (hf : ContDiff ℝ ∞ f) (d : ℕ)
    (hbf : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y =>
      fixedFrameSolver T hT (Q y) (Q₁ y) (H y) c hc (hLower y) (hd y)
        K hK (hPotential y) hsmall (f y)) x‖ ≤ majorant R (d+1) n := by
  let A := fun y => fixedFrameOperator T hT (Q y) (Q₁ y) (H y)
  let δ := fun y => fixedCoercivity T (Q y) (Q₁ y) c
  let rhs := fun y => (-(fixedFramePrimitive T hT (Q y) (Q₁ y)).adjoint) (f y)
  have hδ : ∀ y, 0 < δ y := fun y => fixedCoercivity_pos T hT (Q y) (Q₁ y) c hc
  have hAco : ∀ y v, δ y * ‖v‖^2 ≤ ⟪A y v, v⟫_ℝ := fun y =>
    fixedFrameOperator_coercive T hT (Q y) (Q₁ y) (H y) c hc (hLower y) (hd y)
      K hK (hPotential y) hsmall
  have hAreg : ContDiff ℝ ∞ A := contDiff_fixedFrameOperator T hT Q Q₁ H hQ hQ₁ hH
  have hrhs : ContDiff ℝ ∞ rhs :=
    (contDiff_adjoint (contDiff_fixedFramePrimitive T hT Q Q₁ hQ hQ₁)).neg.clm_apply hf
  have hM := solveCost_one_le T C₀ C₁ CH c hT hC₀ hC₁ hCH
  have hRcR : Rc ≤ R := (radius_bounds hRc hM hR).2
  have hR0 : 0 ≤ R := hRc.trans hRcR
  have hCR : 0 ≤ formCost T C₀ C₁ CH := by unfold formCost; positivity
  have hFR : 0 ≤ forcingCost T C₀ C₁ := by unfold forcingCost derivativeCost; positivity
  have hI : 0 ≤ inverseCost T C₀ C₁ c := by unfold inverseCost; positivity
  have hMC : inverseCost T C₀ C₁ c * formCost T C₀ C₁ CH ≤ solveCost T C₀ C₁ CH c := by
    unfold solveCost
    nlinarith
  have hMF : inverseCost T C₀ C₁ c * forcingCost T C₀ C₁ ≤ solveCost T C₀ C₁ CH c := by
    unfold solveCost
    nlinarith
  have hinv (y : P) : (δ y)⁻¹ ≤ inverseCost T C₀ C₁ c := by
    apply fixedCoercivity_inv_le T hT (Q y) (Q₁ y) c hc C₀ C₁
    · simpa only [norm_iteratedFDeriv_zero, majorant, Nat.add_zero, pow_zero,
        Nat.factorial_zero, Nat.cast_one, one_pow, mul_one] using hbQ 0 y
    · simpa only [norm_iteratedFDeriv_zero, majorant, Nat.add_zero, pow_zero,
        Nat.factorial_zero, Nat.cast_one, one_pow, mul_one] using hbQ₁ 0 y
  have hbA (j : ℕ) (y : P) : ‖iteratedFDeriv ℝ (j+1) A y‖ ≤
      formCost T C₀ C₁ CH * (Rc^(j+1) * ((j+1).factorial : ℝ)^2) := by
    simpa only [majorant, Nat.add_zero] using
      fixedFrameOperator_bound T hT Q Q₁ H hQ hQ₁ hH Rc C₀ C₁ CH hRc hC₀ hC₁ hCH
        hbQ hbQ₁ hbH (j+1) y
  have hbQR (j : ℕ) (y : P) : ‖iteratedFDeriv ℝ j Q y‖ ≤ C₀*majorant R 0 j :=
    (hbQ j y).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc R hRc hRcR 0 j) hC₀)
  have hbQ₁R (j : ℕ) (y : P) : ‖iteratedFDeriv ℝ j Q₁ y‖ ≤ C₁*majorant R 0 j :=
    (hbQ₁ j y).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc R hRc hRcR 0 j) hC₁)
  have hbrhs := fixedForcing_bound T hT Q Q₁ hQ hQ₁ R C₀ C₁ hR0 hC₀ hC₁ hbQR hbQ₁R
    f hf d hbf
  exact coerciveSolution_gevrey_amplitudes A δ hδ hAco rhs hAreg hrhs
    (inverseCost T C₀ C₁ c) (formCost T C₀ C₁ CH) (forcingCost T C₀ C₁)
    (solveCost T C₀ C₁ CH c) Rc R hCR hFR hM hMC hMF hRc hR hinv hbA d hbrhs n x

include hd hQ hQ₁ hH hRc hC₀ hC₁ hCH hbQ hbQ₁ hbH in
/-- The factorial estimate applies to the recovered coordinate derivative of
the original physical transverse solver. -/
theorem transverseCoordinates_gevrey
    (m : P → Icc (0 : ℝ) T → E)
    (hTangent : ∀ y t v, ⟪m y t, Q y t v⟫_ℝ = 0)
    (hRange : ∀ y t η, ⟪m y t, η⟫_ℝ = 0 → ∃ v : U, Q y t v = η)
    (R : ℝ) (hR : 2 * solveCost T C₀ C₁ CH c * (Rc + 1) ≤ R)
    (f : P → TimeLp T E) (hf : ContDiff ℝ ∞ f) (d : ℕ)
    (hbf : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => coordinateDerivative T hT (Q y) (Q₁ y) c hc (hLower y)
      (transverseSolver T hT (m y) (H y) K hK (hPotential y) hsmall (f y) : TimeLp T E)) x‖ ≤
      majorant R (d+1) n := by
  let v := fun y => fixedFrameSolver T hT (Q y) (Q₁ y) (H y) c hc (hLower y) (hd y)
    K hK (hPotential y) hsmall (f y)
  have hv : ContDiff ℝ ∞ v :=
    contDiff_fixedFrameSolution T hT Q Q₁ H c hc hLower hd K hK hPotential hsmall hQ hQ₁ hH f hf
  have hb (j : ℕ) (y : P) : ‖iteratedFDeriv ℝ j v y‖ ≤ majorant R (d+1) j :=
    fixedFrameSolution_gevrey T hT Q Q₁ H c hc hLower hd K hK hPotential hsmall
      hQ hQ₁ hH Rc C₀ C₁ CH hRc hC₀ hC₁ hCH hbQ hbQ₁ hbH R hR f hf d hbf j y
  have heq : (fun y => coordinateDerivative T hT (Q y) (Q₁ y) c hc (hLower y)
      (transverseSolver T hT (m y) (H y) K hK (hPotential y) hsmall (f y) : TimeLp T E)) =
      fun y => (v y : TimeLp T U) := by
    funext y
    have he := fixedFrameSolver_eq_transverse T hT (Q y) (Q₁ y) (H y) c hc (hLower y) (hd y)
      K hK (hPotential y) hsmall (m y) (hTangent y) (hRange y) (f y)
    exact (congrArg (fun z : zeroTraceDerivatives (U := U) T hT => (z : TimeLp T U)) he).symm
  rw [heq]
  have hM := solveCost_one_le T C₀ C₁ CH c hT hC₀ hC₁ hCH
  have hR0 : 0 ≤ R := by nlinarith
  have hout := contraction_bound (zeroTraceDerivatives (U := U) T hT).subtypeL
    (zeroTraceDerivatives (U := U) T hT).norm_subtypeL_le v hv R 1 hR0 zero_le_one (d+1)
    (by simpa only [one_mul] using hb) n x
  simp only [one_mul] at hout
  convert hout using 1
  rfl

include hd hQ hQ₁ hH hRc hC₀ hC₁ hCH hbQ hbQ₁ hbH in
/-- The actual physical transverse velocity has the same factorial shift,
with only the fixed coefficient multiplication constant. -/
theorem transverseVelocity_gevrey
    (m : P → Icc (0 : ℝ) T → E)
    (hTangent : ∀ y t v, ⟪m y t, Q y t v⟫_ℝ = 0)
    (hRange : ∀ y t η, ⟪m y t, η⟫_ℝ = 0 → ∃ v : U, Q y t v = η)
    (R : ℝ) (hR : 2 * solveCost T C₀ C₁ CH c * (Rc + 1) ≤ R)
    (f : P → TimeLp T E) (hf : ContDiff ℝ ∞ f) (d : ℕ)
    (hbf : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => timeMultiplier T hT (Q y)
      (coordinateDerivative T hT (Q y) (Q₁ y) c hc (hLower y)
        (transverseSolver T hT (m y) (H y) K hK (hPotential y) hsmall (f y) : TimeLp T E))) x‖ ≤
      (3*C₀) * majorant R (d+1) n := by
  let v := fun y => coordinateDerivative T hT (Q y) (Q₁ y) c hc (hLower y)
    (transverseSolver T hT (m y) (H y) K hK (hPotential y) hsmall (f y) : TimeLp T E)
  have hv : ContDiff ℝ ∞ v := contDiff_transverse_coordinates T hT Q Q₁ H c hc hLower hd
    K hK hPotential hsmall m hTangent hRange hQ hQ₁ hH f hf
  have hb := transverseCoordinates_gevrey T hT Q Q₁ H c hc hLower hd K hK hPotential hsmall
    hQ hQ₁ hH Rc C₀ C₁ CH hRc hC₀ hC₁ hCH hbQ hbQ₁ hbH m hTangent hRange R hR f hf d hbf
  have hM := solveCost_one_le T C₀ C₁ CH c hT hC₀ hC₁ hCH
  have hRcR : Rc ≤ R := (radius_bounds hRc hM hR).2
  have hR0 : 0 ≤ R := hRc.trans hRcR
  have hbQR (j : ℕ) (y : P) : ‖iteratedFDeriv ℝ j Q y‖ ≤ C₀*majorant R 0 j :=
    (hbQ j y).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc R hRc hRcR 0 j) hC₀)
  have h := clm_apply_bound (fun y => timeMultiplier T hT (Q y)) v
    (contDiff_timeMultiplier T hT Q hQ) hv R C₀ 1 hR0 hC₀ zero_le_one 0 (d+1)
    (timeMultiplier_bound T hT Q hQ R C₀ hR0 hC₀ 0 hbQR)
    (by simpa only [one_mul] using hb) n x
  simpa only [mul_one, Nat.zero_add] using h

end EulerTransverseGevreyInverse

end
end

end

@[expose] public section

noncomputable section

namespace EulerTransverseFixedSobolev

open Set ContinuousLinearMap InnerProductSpace EulerTimeLp EulerVolterraConvolution
  EulerTimeH1FrameTransport EulerTransverseFixedSpaceInverse EulerTransverseParameterRegularity
  EulerTransverseCoefficientGevrey EulerTransverseGevreyInverse EulerCoerciveProjection
  EulerTransverseGramInverse EulerOperatorGevreyCalculus EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

/-- Forcing block amplitude, given by `3*sobolevCoefficientAmplitude ι q Rc (T*derivativeCost T
C₀ C₁)*Cf`. -/
def forcingBlockAmplitude (ι : Type*) [Fintype ι] (q : ℕ) (T Rc C₀ C₁ Cf : ℝ) : ℝ :=
  3*sobolevCoefficientAmplitude ι q Rc (T*derivativeCost T C₀ C₁)*Cf

/-- Block cost, given by `inverseBlockCost ι q (inverseCost T C₀ C₁ c) Rc (formCost T C₀ C₁ CH)
(forcingBlockAmplitude ι q T Rc C₀ C₁ Cf)`. -/
def blockCost (ι : Type*) [Fintype ι] (q : ℕ) (T Rc C₀ C₁ CH c Cf : ℝ) : ℝ :=
  inverseBlockCost ι q (inverseCost T C₀ C₁ c) Rc (formCost T C₀ C₁ CH)
    (forcingBlockAmplitude ι q T Rc C₀ C₁ Cf)

theorem forcingBlockAmplitude_nonneg (ι : Type*) [Fintype ι] (q : ℕ) (T Rc C₀ C₁ Cf : ℝ)
    (hT : 0 ≤ T) (hRc : 0 ≤ Rc) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hCf : 0 ≤ Cf) :
    0 ≤ forcingBlockAmplitude ι q T Rc C₀ C₁ Cf := by
  have hb := sobolevCoefficientAmplitude_nonneg (ι := ι) q Rc (T*derivativeCost T C₀ C₁)
    hRc (by unfold derivativeCost; positivity)
  unfold forcingBlockAmplitude
  positivity

theorem blockCost_one_le (ι : Type*) [Fintype ι] (q : ℕ) (T Rc C₀ C₁ CH c Cf : ℝ)
    (hT : 0 ≤ T) (hRc : 0 ≤ Rc) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hCH : 0 ≤ CH) (hCf : 0 ≤ Cf) : 1 ≤ blockCost ι q T Rc C₀ C₁ CH c Cf := by
  have hI : 0 ≤ inverseCost T C₀ C₁ c := by unfold inverseCost; positivity
  have hC : 0 ≤ formCost T C₀ C₁ CH := by unfold formCost; positivity
  have hA := sobolevCoefficientAmplitude_nonneg (ι := ι) q Rc _ hRc hC
  have hB := forcingBlockAmplitude_nonneg ι q T Rc C₀ C₁ Cf hT hRc hC₀ hC₁ hCf
  have hS := sobolevInverseCost_nonneg (inverseCost T C₀ C₁ c)
    (sobolevCoefficientAmplitude ι q Rc (formCost T C₀ C₁ CH)) hI hA q
  unfold blockCost inverseBlockCost
  linarith [mul_nonneg hS (add_nonneg hA hB)]

variable {X U E ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype ι]

/-- The actual weak forcing pullback has coefficient-only tensor bounds. -/
theorem forcingOperator_bound (T : ℝ) (hT : 0 ≤ T)
    (Q Q₁ : X → C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (hQ : ContDiff ℝ ∞ Q) (hQ₁ : ContDiff ℝ ∞ Q₁)
    (Rc C₀ C₁ : ℝ) (hRc : 0 ≤ Rc) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C₀ * majorant Rc 0 n)
    (hbQ₁ : ∀ n x, ‖iteratedFDeriv ℝ n Q₁ x‖ ≤ C₁ * majorant Rc 0 n)
    (n : ℕ) (x : X) :
    ‖iteratedFDeriv ℝ n (fun y => -(fixedFramePrimitive T hT (Q y) (Q₁ y)).adjoint) x‖ ≤
      (T*derivativeCost T C₀ C₁)*majorant Rc 0 n :=
  neg_bound (fun y => (fixedFramePrimitive T hT (Q y) (Q₁ y)).adjoint)
    Rc (T*derivativeCost T C₀ C₁) 0
    (adjoint_bound (fun y => fixedFramePrimitive T hT (Q y) (Q₁ y))
      (contDiff_fixedFramePrimitive T hT Q Q₁ hQ hQ₁)
      Rc (T*derivativeCost T C₀ C₁) hRc (by unfold derivativeCost; positivity) 0
      (fixedFramePrimitive_bound T hT Q Q₁ hQ hQ₁ Rc C₀ C₁ hRc hC₀ hC₁ hbQ hbQ₁)) n x

variable (directions : ι → X) (hdir : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : X → C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (H : X → C(Icc (0 : ℝ) T, E →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hLower : ∀ x t v, c * ‖v‖ ^ 2 ≤ ‖Q x t v‖ ^ 2)
  (hd : ∀ x (t : Icc (0 : ℝ) T),
    HasDerivWithinAt (extendPath T hT (Q x)) (Q₁ x t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K) (hPotential : ∀ x t v, ⟪H x t v, v⟫_ℝ ≤ K * ‖v‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)
  (hQ : ContDiff ℝ ∞ Q) (hQ₁ : ContDiff ℝ ∞ Q₁) (hH : ContDiff ℝ ∞ H)
  (Rc C₀ C₁ CH Cf R : ℝ) (hRc : 0 ≤ Rc)
  (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hCH : 0 ≤ CH) (hCf : 0 ≤ Cf)
  (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C₀ * majorant Rc 0 n)
  (hbQ₁ : ∀ n x, ‖iteratedFDeriv ℝ n Q₁ x‖ ≤ C₁ * majorant Rc 0 n)
  (hbH : ∀ n x, ‖iteratedFDeriv ℝ n H x‖ ≤ CH * majorant Rc 0 n)
  (hR : 2 * blockCost ι q T Rc C₀ C₁ CH c Cf * (sobolevCoefficientRadius ι Rc + 1) ≤ R)

include hdir hQ hQ₁ hH hRc hC₀ hC₁ hCH hCf hbQ hbQ₁ hbH hR

/-- The genuine zero-trace coordinate solver gains one factorial shift at
the identical external radius and fixed base Sobolev order. -/
theorem solver_block_gevrey (f : X → TimeLp T E) (hf : ContDiff ℝ ∞ f) (d : ℕ)
    (hfb : ∀ n x, block directions q f n x ≤ Cf * majorant R d n) (n : ℕ) (x : X) :
    block directions q (fun y => fixedFrameSolver T hT (Q y) (Q₁ y) (H y)
      c hc (hLower y) (hd y) K hK (hPotential y) hsmall (f y)) n x ≤ majorant R (d+1) n := by
  let A := fun y => fixedFrameOperator T hT (Q y) (Q₁ y) (H y)
  let δ := fun y => fixedCoercivity T (Q y) (Q₁ y) c
  let J := fun y => -(fixedFramePrimitive T hT (Q y) (Q₁ y)).adjoint
  let v := fun y => fixedFrameSolver T hT (Q y) (Q₁ y) (H y)
    c hc (hLower y) (hd y) K hK (hPotential y) hsmall (f y)
  let rhs := fun y => J y (f y)
  have hδ (y : X) : 0 < δ y := fixedCoercivity_pos T hT (Q y) (Q₁ y) c hc
  have hco (y : X) (u : zeroTraceDerivatives (U := U) T hT) :
      δ y*‖u‖^2 ≤ ⟪A y u,u⟫_ℝ :=
    fixedFrameOperator_coercive T hT (Q y) (Q₁ y) (H y) c hc (hLower y) (hd y)
      K hK (hPotential y) hsmall u
  let inv := fun y => coerciveInverse (A y) (δ y) (hδ y) (hco y)
  have hA : ContDiff ℝ ∞ A := contDiff_fixedFrameOperator T hT Q Q₁ H hQ hQ₁ hH
  have hJ : ContDiff ℝ ∞ J :=
    (contDiff_adjoint (contDiff_fixedFramePrimitive T hT Q Q₁ hQ hQ₁)).neg
  have hv : ContDiff ℝ ∞ v := contDiff_fixedFrameSolution T hT Q Q₁ H c hc hLower hd
    K hK hPotential hsmall hQ hQ₁ hH f hf
  have hrhs : ContDiff ℝ ∞ rhs := hJ.clm_apply hf
  have heq (y : X) : A y (v y) = rhs y :=
    operator_inverse_apply (A y) (δ y) (hδ y) (hco y) (rhs y)
  have hinv (y : X) : ‖inv y‖ ≤ inverseCost T C₀ C₁ c := by
    apply (coerciveInverse_norm_le (A y) (δ y) (hδ y) (hco y)).trans
    apply fixedCoercivity_inv_le T hT (Q y) (Q₁ y) c hc C₀ C₁
    · simpa only [norm_iteratedFDeriv_zero,majorant,Nat.add_zero,pow_zero,
        Nat.factorial_zero,Nat.cast_one,one_pow,mul_one] using hbQ 0 y
    · simpa only [norm_iteratedFDeriv_zero,majorant,Nat.add_zero,pow_zero,
        Nat.factorial_zero,Nat.cast_one,one_pow,mul_one] using hbQ₁ 0 y
  have hCA : 0 ≤ formCost T C₀ C₁ CH := by unfold formCost; positivity
  have hCJ : 0 ≤ T*derivativeCost T C₀ C₁ := by unfold derivativeCost; positivity
  have hJA : 0 ≤ sobolevCoefficientAmplitude ι q Rc (T*derivativeCost T C₀ C₁) :=
    sobolevCoefficientAmplitude_nonneg q Rc _ hRc hCJ
  have hM := blockCost_one_le ι q T Rc C₀ C₁ CH c Cf hT hRc hC₀ hC₁ hCH hCf
  have hr0 := sobolevCoefficientRadius_nonneg (ι := ι) Rc hRc
  have hrR : sobolevCoefficientRadius ι Rc ≤ R := (radius_bounds hr0 hM hR).2
  have hAb (k y) : ‖iteratedFDeriv ℝ k A y‖ ≤ formCost T C₀ C₁ CH*majorant Rc 0 k :=
    fixedFrameOperator_bound T hT Q Q₁ H hQ hQ₁ hH Rc C₀ C₁ CH hRc hC₀ hC₁ hCH hbQ hbQ₁ hbH k y
  have hJb (k y) : ‖iteratedFDeriv ℝ k J y‖ ≤ (T*derivativeCost T C₀ C₁)*majorant Rc 0 k :=
    forcingOperator_bound T hT Q Q₁ hQ hQ₁ Rc C₀ C₁ hRc hC₀ hC₁ hbQ hbQ₁ k y
  have hJB (k y) : coefficientBlock directions q J k y ≤
      sobolevCoefficientAmplitude ι q Rc (T*derivativeCost T C₀ C₁) *
        majorant (sobolevCoefficientRadius ι Rc) 0 k :=
    coefficientBlock_of_tensor_bound directions hdir q J hJ Rc _ hRc hCJ hJb k y
  have hrhsb (k y) : block directions q rhs k y ≤
      forcingBlockAmplitude ι q T Rc C₀ C₁ Cf*majorant R d k :=
    block_clm_apply_gevrey directions q J f hJ hf (sobolevCoefficientRadius ι Rc) R
      (sobolevCoefficientAmplitude ι q Rc (T*derivativeCost T C₀ C₁)) Cf
      hr0 hrR hJA hCf hJB d hfb k y
  exact inverse_block_gevrey_of_tensor directions hdir q A v rhs hA hv hrhs heq inv
    (fun y u => inverse_operator_apply (A y) (δ y) (hδ y) (hco y) u)
    (inverseCost T C₀ C₁ c) Rc (formCost T C₀ C₁ CH) (forcingBlockAmplitude ι q T Rc C₀ C₁ Cf) R
    hRc hCA (forcingBlockAmplitude_nonneg ι q T Rc C₀ C₁ Cf hT hRc hC₀ hC₁ hCf)
    hinv hAb hR d hrhsb n x

/-- Forgetting the zero-trace subtype is a contraction, so the actual
coordinate L² velocity has the identical word estimate. -/
theorem velocityLp_block_gevrey (f : X → TimeLp T E) (hf : ContDiff ℝ ∞ f) (d : ℕ)
    (hfb : ∀ n x, block directions q f n x ≤ Cf * majorant R d n) (n : ℕ) (x : X) :
    block directions q (fun y => EulerTransverseFixedEvolution.velocityLp T hT (Q y) (Q₁ y) (H y)
      c hc (hLower y) (hd y) K hK (hPotential y) hsmall (f y)) n x ≤ majorant R (d+1) n := by
  let v := fun y => fixedFrameSolver T hT (Q y) (Q₁ y) (H y)
    c hc (hLower y) (hd y) K hK (hPotential y) hsmall (f y)
  have hv : ContDiff ℝ ∞ v := contDiff_fixedFrameSolution T hT Q Q₁ H c hc hLower hd
    K hK hPotential hsmall hQ hQ₁ hH f hf
  have hb := solver_block_gevrey directions hdir q T hT Q Q₁ H c hc hLower hd K hK hPotential hsmall
    hQ hQ₁ hH Rc C₀ C₁ CH Cf R hRc hC₀ hC₁ hCH hCf hbQ hbQ₁ hbH hR f hf d hfb n x
  have h := block_comp_clm_le directions q (zeroTraceDerivatives (U := U) T hT).subtypeL v hv n x
  apply h.trans
  exact (mul_le_mul_of_nonneg_right (zeroTraceDerivatives (U := U) T hT).norm_subtypeL_le
    (block_nonneg directions q v n x)).trans (by simpa only [one_mul] using hb)

end EulerTransverseFixedSobolev
