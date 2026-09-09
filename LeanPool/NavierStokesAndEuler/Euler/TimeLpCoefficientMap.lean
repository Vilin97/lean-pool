/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseVariationalOperator
public import LeanPool.NavierStokesAndEuler.Euler.TimeH1OperatorProduct

@[expose] public section

/-!
# Dependence of the actual Bochner multiplier on its coefficient

The coefficient-to-operator map is constructed as a bounded linear map. Thus
parameter derivatives of time-dependent coefficients give actual operator-norm
derivatives, rather than an assumed regular family of solution operators.
-/

noncomputable section

open scoped ContDiff


namespace EulerTimeLpCoefficientMap

open Set MeasureTheory ContinuousLinearMap EulerTimeLp EulerTerminalTimePrimitive
  EulerVolterraConvolution EulerTimeH1OperatorProduct

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (T : ℝ) (hT : 0 ≤ T)

/-- The genuine multiplier is additive in the coefficient. -/
theorem timeMultiplier_add (A B : C(Icc (0 : ℝ) T, E →L[ℝ] F)) :
    timeMultiplier T hT (A+B) = timeMultiplier T hT A + timeMultiplier T hT B := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [timeMultiplier_ae T hT (A+B) u,
    timeMultiplier_ae T hT A u, timeMultiplier_ae T hT B u,
    Lp.coeFn_add (timeMultiplier T hT A u) (timeMultiplier T hT B u)] with t hAB hA hB hs
  change (timeMultiplier T hT (A+B) u) t = (timeMultiplier T hT A u + timeMultiplier T hT B u) t
  rw [hAB, hs]
  simp only [Pi.add_apply, hA, hB]
  rfl

/-- The genuine multiplier is homogeneous in the coefficient. -/
theorem timeMultiplier_smul (r : ℝ) (A : C(Icc (0 : ℝ) T, E →L[ℝ] F)) :
    timeMultiplier T hT (r • A) = r • timeMultiplier T hT A := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [timeMultiplier_ae T hT (r • A) u,
    timeMultiplier_ae T hT A u, Lp.coeFn_smul r (timeMultiplier T hT A u)] with t hr hA hs
  change (timeMultiplier T hT (r • A) u) t = (r • timeMultiplier T hT A u) t
  rw [hr, hs]
  simp only [Pi.smul_apply, hA]
  rfl

/-- The operator norm is bounded by the actual uniform coefficient norm. -/
theorem timeMultiplier_norm (A : C(Icc (0 : ℝ) T, E →L[ℝ] F)) :
    ‖timeMultiplier T hT A‖ ≤ ‖A‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) (timeApply_bound T hT A)

/-- The actual bounded linear coefficient-to-Bochner-multiplier map. -/
def coefficientLinear : C(Icc (0 : ℝ) T, E →L[ℝ] F) →ₗ[ℝ] (TimeLp T E →L[ℝ] TimeLp T F) where
  toFun := timeMultiplier T hT
  map_add' := timeMultiplier_add T hT
  map_smul' := timeMultiplier_smul T hT

/-- The coefficient map is bounded for the actual uniform and operator norms. -/
def coefficientMap : C(Icc (0 : ℝ) T, E →L[ℝ] F) →L[ℝ] (TimeLp T E →L[ℝ] TimeLp T F) where
  toLinearMap := coefficientLinear T hT
  cont := AddMonoidHomClass.continuous_of_bound (coefficientLinear T hT) 1 (fun A => by
    change ‖timeMultiplier T hT A‖ ≤ (1 : ℝ) * ‖A‖
    simpa only [one_mul] using timeMultiplier_norm (E := E) (F := F) T hT A)

/-- Coefficient derivatives give genuine operator-norm derivatives of the time multiplier. -/
theorem hasDerivAt_timeMultiplier
    (A : ℝ → C(Icc (0 : ℝ) T, E →L[ℝ] F))
    (A₁ : C(Icc (0 : ℝ) T, E →L[ℝ] F)) (x : ℝ)
    (hA : HasDerivAt A A₁ x) :
    HasDerivAt (fun r => timeMultiplier T hT (A r)) (timeMultiplier T hT A₁) x := by
  change HasDerivAt ((coefficientMap T hT) ∘ A) (coefficientMap T hT A₁) x
  exact HasFDerivAt.comp_hasDerivAt
    (F := C(Icc (0 : ℝ) T, E →L[ℝ] F)) (E := TimeLp T E →L[ℝ] TimeLp T F) x
    (coefficientMap (E := E) (F := F) T hT).hasFDerivAt hA

/-- Every order of actual coefficient regularity passes to operator norm regularity. -/
theorem contDiff_timeMultiplier {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P → C(Icc (0 : ℝ) T, E →L[ℝ] F)) {n : ℕ∞ω} (hA : ContDiff ℝ n A) :
    ContDiff ℝ n (fun x => timeMultiplier T hT (A x)) := by
  change ContDiff ℝ n ((coefficientMap T hT) ∘ A)
  exact ContDiff.comp
    (g := coefficientMap (E := E) (F := F) T hT) (f := A)
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n)
      (E := C(Icc (0 : ℝ) T, E →L[ℝ] F)) (F := TimeLp T E →L[ℝ] TimeLp T F)
      (coefficientMap (E := E) (F := F) T hT)) hA

/-- Differentiating the actual frame H¹ transport with respect to an external parameter. -/
theorem hasDerivAt_productDerivative
    (A B : ℝ → C(Icc (0 : ℝ) T, E →L[ℝ] F))
    (A₁ B₁ : C(Icc (0 : ℝ) T, E →L[ℝ] F)) (x : ℝ)
    (hA : HasDerivAt A A₁ x) (hB : HasDerivAt B B₁ x) :
    HasDerivAt (fun r => productDerivative T hT (A r) (B r))
      ((timeMultiplier T hT B₁).comp (primitiveTimeLp T hT) + timeMultiplier T hT A₁) x := by
  have h := ((hasDerivAt_timeMultiplier T hT B B₁ x hB).clm_comp
    (hasDerivAt_const x (primitiveTimeLp (E := E) T hT))).add
      (hasDerivAt_timeMultiplier T hT A A₁ x hA)
  convert h using 1 <;> first | rfl | simp only [comp_zero, add_zero]

/-- Arbitrary-order parameter regularity of the genuine H¹ frame transport. -/
theorem contDiff_productDerivative {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A B : P → C(Icc (0 : ℝ) T, E →L[ℝ] F)) {n : ℕ∞ω}
    (hA : ContDiff ℝ n A) (hB : ContDiff ℝ n B) :
    ContDiff ℝ n (fun x => productDerivative T hT (A x) (B x)) := by
  exact ((contDiff_timeMultiplier T hT B hB).clm_comp contDiff_const).add
    (contDiff_timeMultiplier T hT A hA)

end EulerTimeLpCoefficientMap
