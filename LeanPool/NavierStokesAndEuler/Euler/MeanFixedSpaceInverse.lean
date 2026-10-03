/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanFixedFrameTransport
public import LeanPool.NavierStokesAndEuler.Euler.HilbertCoerciveTransport

/-!
# The actual mean variational inverse on a fixed Hilbert space

The fixed space is ordinary solenoidal Bochner L² time. The transported operator
contains the original kinetic, potential, and nonlocal initial-trace terms. Its
coercive inverse is constructed and identified with the original mean solve,
so coefficient comparisons can use a common domain without assuming an inverse.
-/

@[expose] public section

-- Numeric exponents elaborate as natural numbers at once: left to the default instance,
-- every `x ^ 2` of a long statement stays pending and is retried after each later binder.
local macro_rules | `($x ^ $n:num) => `($x ^ ($n : ℕ))


noncomputable section


namespace EulerMeanFixedSpaceInverse

open Set InnerProductSpace ContinuousLinearMap EulerTimeLp EulerTerminalTimePrimitive
  EulerMeanSolenoidal EulerVolterraConvolution EulerTimeH1OperatorProduct
  EulerMeanVariationalInverse EulerMeanVariationalOperator EulerHilbertCoerciveTransport
  EulerCoerciveProjection EulerTransverseVariationalInverse

-- Cache the nested Hilbert-space instances used throughout the operator identities.
/-- Cache the standard `NormedAddCommGroup solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanFixedSpaceInverse1 : NormedAddCommGroup solenoidalSpace := inferInstance
/-- Cache the standard `InnerProductSpace ℝ solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanFixedSpaceInverse2 : InnerProductSpace ℝ solenoidalSpace := inferInstance
/-- Cache the standard `NormedAddCommGroup (TimeLp T L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanFixedSpaceInverse3 (T : ℝ) : NormedAddCommGroup (TimeLp T L2) :=
    inferInstance
/-- Cache the standard `InnerProductSpace ℝ (TimeLp T L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanFixedSpaceInverse4 (T : ℝ) : InnerProductSpace ℝ (TimeLp T L2) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (TimeLp T solenoidalSpace)` instance to shorten
typeclass synthesis. -/
local instance instMeanFixedSpaceInverse5 (T : ℝ) : NormedAddCommGroup (TimeLp T solenoidalSpace)
    := inferInstance
/-- Cache the standard `InnerProductSpace ℝ (TimeLp T solenoidalSpace)` instance to shorten
typeclass synthesis. -/
local instance instMeanFixedSpaceInverse6 (T : ℝ) : InnerProductSpace ℝ (TimeLp T solenoidalSpace)
    := inferInstance

private theorem coercive_forcing_inner {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (O : V →L[ℝ] V) (J : V →L[ℝ] W) (c : ℝ) (hc : 0 < c)
    (hO : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪O v, v⟫_ℝ) (f : W) (v : V) :
    ⟪O (coerciveInverse O c hc hO (-adjoint (𝕜 := ℝ) (E := V) (F := W) J f)), v⟫_ℝ =
      -⟪f,J v⟫_ℝ := by
  rw [operator_inverse_apply, inner_neg_left, adjoint_inner_left]

private theorem coercive_forcing_unique {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (O : V →L[ℝ] V) (J : V →L[ℝ] W) (c : ℝ) (hc : 0 < c)
    (hO : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪O v, v⟫_ℝ) (f : W) (u : V)
    (hu : ∀ v, ⟪O u, v⟫_ℝ = -⟪f, J v⟫_ℝ) :
    u = coerciveInverse O c hc hO (-adjoint (𝕜 := ℝ) (E := V) (F := W) J f) := by
  apply (coerciveEquiv O c hc hO).injective
  simp only [coerciveEquiv_apply]
  apply ext_inner_right ℝ
  intro v
  exact (hu v).trans (coercive_forcing_inner O J c hc hO f v).symm

variable (T : ℝ) (hT : 0 ≤ T)
  (F F₁ H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (M0 A : L2 →L[ℝ] L2) (L : ℝ)

/-- Actual physical derivative on the fixed solenoidal coordinate space. -/
def fixedMeanDerivative : TimeLp T solenoidalSpace →L[ℝ] TimeLp T L2 :=
  productDerivative T hT (solenoidalFrame T F) (solenoidalFrame T F₁)

/-- Actual physical displacement on the fixed coordinate space. -/
def fixedMeanPrimitive : TimeLp T solenoidalSpace →L[ℝ] TimeLp T L2 :=
  (primitiveTimeLp (E := L2) T hT).comp (fixedMeanDerivative T hT F F₁)

/-- Actual physical initial trace on the fixed coordinate space. -/
def fixedMeanTrace : TimeLp T solenoidalSpace →L[ℝ] L2 :=
  (initialTrace (E := L2) T hT).comp (fixedMeanDerivative T hT F F₁)

/-- The full original mean form as an operator on one fixed Hilbert space. -/
def fixedMeanOperator : TimeLp T solenoidalSpace →L[ℝ] TimeLp T solenoidalSpace :=
  transportedOperator (fixedMeanDerivative T hT F F₁)
    (meanOperator (primitiveTimeLp T hT) (initialTrace T hT) (timeMultiplier T hT H) (M0+L • A))

/-- The transported operator has precisely the original mean bilinear form. -/
theorem fixedMeanOperator_inner (u v : TimeLp T solenoidalSpace) :
    ⟪fixedMeanOperator T hT F F₁ H M0 A L u, v⟫_ℝ =
      ⟪fixedMeanDerivative T hT F F₁ u, fixedMeanDerivative T hT F F₁ v⟫_ℝ -
      ⟪timeMultiplier T hT H (fixedMeanPrimitive T hT F F₁ u),
        fixedMeanPrimitive T hT F F₁ v⟫_ℝ +
      ⟪(M0+L • A) (fixedMeanTrace T hT F F₁ u), fixedMeanTrace T hT F F₁ v⟫_ℝ := by
  exact (transportedOperator_inner _ _ u v).trans (meanOperator_inner _ _ _ _ _ _)

variable (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (F t x) = x)
  (hF : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)

/-- An explicit positive coercivity constant from the proved mean transport bound. -/
def fixedMeanCoercivity : ℝ := (meanTransportCost T FInv F F₁)⁻¹^2 / 2

include hT in
/-- The fixed-space coercivity constant is positive. -/
theorem fixedMeanCoercivity_pos : 0 < fixedMeanCoercivity T F F₁ FInv := by
  unfold fixedMeanCoercivity
  exact div_pos (pow_pos (inv_pos.mpr (meanTransportCost_pos T hT FInv F F₁)) 2) (by norm_num)

variable (K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B)
  (hFInv₀ : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
  (hH : ∀ t z, ⟪H t z, z⟫_ℝ ≤ K * ‖z‖ ^ 2)
  (hboundary : ∀ z : L2, z ∈ solenoidalSpace →
    -B * ‖z‖ ^ 2 ≤ ⟪M0 z, z⟫_ℝ + L * ⟪A z, z⟫_ℝ)
  (hsmall : K * (T ^ 2 / 2) + B * T ≤ 1 / 2)

include hInv hF K B hK hB hFInv₀ hH hboundary hsmall in
/-- The source smallness and actual transport bounds prove fixed-space coercivity. -/
theorem fixedMeanOperator_coercive (v : TimeLp T solenoidalSpace) :
    fixedMeanCoercivity T F F₁ FInv*‖v‖^2 ≤ ⟪fixedMeanOperator T hT F F₁ H M0 A L v, v⟫_ℝ := by
  let u := meanTestMap T hT FInv F F₁ hF hInv v
  have hbase := meanOperator_coercive _ _ _ _ _ _ _ _ hK hB
    (meanPrimitive_norm_sq T hT FInv) (meanTrace_norm_sq T hT FInv)
    (timeMultiplier_quadratic_upper T hT H K hH)
    (meanTrace_boundary T hT FInv M0 A L B hFInv₀ hboundary) hsmall u
  calc
    fixedMeanCoercivity T F F₁ FInv*‖v‖^2 =
        (1/2 : ℝ)*((meanTransportCost T FInv F F₁)⁻¹^2*‖v‖^2) := by
      unfold fixedMeanCoercivity
      ring
    _ ≤ (1/2 : ℝ)*‖u‖^2 :=
      mul_le_mul_of_nonneg_left (meanForward_norm_sq_lower T hT FInv F F₁ hInv hF v)
        (by norm_num)
    _ ≤ _ := hbase
    _ = ⟪fixedMeanOperator T hT F F₁ H M0 A L v, v⟫_ℝ :=
      (meanOperator_inner _ _ _ _ u u).trans (fixedMeanOperator_inner T hT F F₁ H M0 A L v v).symm

/-- The actual fixed-space inverse operator. -/
def fixedMeanInverse : TimeLp T solenoidalSpace →L[ℝ] TimeLp T solenoidalSpace :=
  coerciveInverse (fixedMeanOperator T hT F F₁ H M0 A L) (fixedMeanCoercivity T F F₁ FInv)
    (fixedMeanCoercivity_pos T hT F F₁ FInv)
    (fixedMeanOperator_coercive T hT F F₁ H M0 A L FInv hInv hF K B hK hB hFInv₀ hH hboundary
        hsmall)

/-- The actual forcing-to-coordinate-derivative map on the fixed space. -/
def fixedMeanSolver : TimeLp T L2 →L[ℝ] TimeLp T solenoidalSpace :=
  (fixedMeanInverse T hT F F₁ H M0 A L FInv hInv hF K B hK hB hFInv₀ hH hboundary hsmall).comp
    (-(adjoint (𝕜 := ℝ) (E := TimeLp T solenoidalSpace) (F := TimeLp T L2)
      (fixedMeanPrimitive T hT F F₁)))

/-- The fixed inverse has its actual quantitative coercive norm bound. -/
theorem fixedMeanInverse_norm :
    ‖fixedMeanInverse T hT F F₁ H M0 A L FInv hInv hF K B hK hB hFInv₀ hH hboundary hsmall‖ ≤
      (fixedMeanCoercivity T F F₁ FInv)⁻¹ :=
  coerciveInverse_norm_le (fixedMeanOperator T hT F F₁ H M0 A L) (fixedMeanCoercivity T F F₁ FInv)
    (fixedMeanCoercivity_pos T hT F F₁ FInv)
    (fixedMeanOperator_coercive T hT F F₁ H M0 A L FInv hInv hF K B hK hB hFInv₀ hH hboundary
        hsmall)

/-- The constructed fixed-space solution satisfies the full original form. -/
theorem fixedMeanSolver_weak (f : TimeLp T L2) (v : TimeLp T solenoidalSpace) :
    let u := fixedMeanSolver T hT F F₁ H M0 A L FInv hInv hF K B hK hB hFInv₀ hH hboundary hsmall f
    ⟪fixedMeanDerivative T hT F F₁ u, fixedMeanDerivative T hT F F₁ v⟫_ℝ -
      ⟪timeMultiplier T hT H (fixedMeanPrimitive T hT F F₁ u), fixedMeanPrimitive T hT F F₁ v⟫_ℝ +
      ⟪(M0+L • A) (fixedMeanTrace T hT F F₁ u), fixedMeanTrace T hT F F₁ v⟫_ℝ =
      -⟪f, fixedMeanPrimitive T hT F F₁ v⟫_ℝ := by
  intro u
  refine (fixedMeanOperator_inner T hT F F₁ H M0 A L u v).symm.trans ?_
  apply coercive_forcing_inner (fixedMeanOperator T hT F F₁ H M0 A L)
    (fixedMeanPrimitive T hT F F₁) (fixedMeanCoercivity T F F₁ FInv)
    (fixedMeanCoercivity_pos T hT F F₁ FInv)
    (fixedMeanOperator_coercive T hT F F₁ H M0 A L FInv hInv hF K B hK hB hFInv₀ hH hboundary
        hsmall) f v

/-- Uniqueness is on the same fixed Hilbert space. -/
theorem fixedMeanSolver_unique (f : TimeLp T L2) (u : TimeLp T solenoidalSpace)
    (hu : ∀ v : TimeLp T solenoidalSpace,
      ⟪fixedMeanDerivative T hT F F₁ u, fixedMeanDerivative T hT F F₁ v⟫_ℝ -
        ⟪timeMultiplier T hT H (fixedMeanPrimitive T hT F F₁ u), fixedMeanPrimitive T hT F F₁ v⟫_ℝ +
        ⟪(M0+L • A) (fixedMeanTrace T hT F F₁ u), fixedMeanTrace T hT F F₁ v⟫_ℝ =
        -⟪f, fixedMeanPrimitive T hT F F₁ v⟫_ℝ) :
    u = fixedMeanSolver T hT F F₁ H M0 A L FInv hInv hF K B hK hB hFInv₀ hH hboundary hsmall f := by
  exact coercive_forcing_unique (fixedMeanOperator T hT F F₁ H M0 A L)
    (fixedMeanPrimitive T hT F F₁) (fixedMeanCoercivity T F F₁ FInv)
    (fixedMeanCoercivity_pos T hT F F₁ FInv)
    (fixedMeanOperator_coercive T hT F F₁ H M0 A L FInv hInv hF K B hK hB hFInv₀ hH hboundary
        hsmall) f u
    (fun v => (fixedMeanOperator_inner T hT F F₁ H M0 A L u v).trans (hu v))

/-- The fixed inverse is precisely the coordinate transport of the original actual solve. -/
theorem fixedMeanSolver_eq_mean
    (hRight : ∀ (t : Icc (0 : ℝ) T) (x : L2), F t (FInv t x) = x) (f : TimeLp T L2) :
    fixedMeanSolver T hT F F₁ H M0 A L FInv hInv hF K B hK hB hFInv₀ hH hboundary hsmall f =
      meanBackward T hT FInv F F₁ hInv
        (EulerMeanVariationalInverse.meanSolver T hT FInv H M0 A L K B hK hB hFInv₀ hH hboundary
            hsmall f) := by
  symm
  apply fixedMeanSolver_unique T hT F F₁ H M0 A L FInv hInv hF K B hK hB hFInv₀ hH hboundary hsmall
  intro v
  let u := EulerMeanVariationalInverse.meanSolver T hT FInv H M0 A L K B hK hB hFInv₀ hH hboundary
      hsmall f
  have h := EulerMeanVariationalInverse.meanSolver_weak T hT FInv H M0 A L K B hK hB hFInv₀ hH
      hboundary hsmall f
    (meanTestMap T hT FInv F F₁ hF hInv v)
  have hu := congrArg (fun w : meanDerivatives T hT FInv => (w : TimeLp T L2))
    (meanForward_backward T hT FInv F F₁ hInv hF hRight u)
  change fixedMeanDerivative T hT F F₁ (meanBackward T hT FInv F F₁ hInv u) = (u : TimeLp T L2)
      at hu
  change ⟪fixedMeanDerivative T hT F F₁ (meanBackward T hT FInv F F₁ hInv u),
      fixedMeanDerivative T hT F F₁ v⟫_ℝ -
    ⟪timeMultiplier T hT H (primitiveTimeLp (E := L2) T hT
      (fixedMeanDerivative T hT F F₁ (meanBackward T hT FInv F F₁ hInv u))), fixedMeanPrimitive T
          hT F F₁ v⟫_ℝ +
    ⟪(M0+L • A) (initialTrace (E := L2) T hT
      (fixedMeanDerivative T hT F F₁ (meanBackward T hT FInv F F₁ hInv u))), fixedMeanTrace T hT F
          F₁ v⟫_ℝ = _
  have heq := congrArg (fun w : TimeLp T L2 =>
    ⟪w, fixedMeanDerivative T hT F F₁ v⟫_ℝ -
      ⟪timeMultiplier T hT H (primitiveTimeLp (E := L2) T hT w),
        fixedMeanPrimitive T hT F F₁ v⟫_ℝ +
      ⟪(M0+L • A) (initialTrace (E := L2) T hT w), fixedMeanTrace T hT F F₁ v⟫_ℝ) hu
  apply heq.trans
  simpa only [u, fixedMeanDerivative, fixedMeanPrimitive, fixedMeanTrace, meanPrimitive,
    meanTrace, comp_apply, Submodule.subtypeL_apply, meanTestMap_coe,
    add_apply, smul_apply, inner_add_left, real_inner_smul_left, add_assoc] using h

end EulerMeanFixedSpaceInverse
