/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.VolterraAnalyticBounds
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Regular Volterra inverses and the sparse parameter-derivative system

The radial inverse is an actual interval integral. Its regularity at the axis
is proved directly, without interpreting the singular differential expression
by division by zero. The analytic word estimates are supplied separately by
`VolterraAnalyticBounds`.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.NilpotentVolterra

open Set Filter MeasureTheory
open scoped Topology ContDiff

section RadialInverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The normalized integral in the regular inverse of `d/dξ+c/ξ`. -/
def weightedMean (c : ℕ) (f : ℝ → E) (ξ : ℝ) : E :=
  ∫ t in (0 : ℝ)..1, (t ^ c) • f (t * ξ)

/-- The genuine zero-axis Volterra inverse. -/
def regularPrimitive (c : ℕ) (f : ℝ → E) (ξ : ℝ) : E :=
  ξ • weightedMean c f ξ

theorem weightedMean_continuous (c : ℕ) {f : ℝ → E} (hf : Continuous f) :
    Continuous (weightedMean c f) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    ((continuous_snd.pow c).smul (hf.comp (continuous_snd.mul continuous_fst))) 0 1

theorem regularPrimitive_continuous (c : ℕ) {f : ℝ → E} (hf : Continuous f) :
    Continuous (regularPrimitive c f) :=
  continuous_id.smul (weightedMean_continuous c hf)

@[simp] theorem regularPrimitive_zero (c : ℕ) (f : ℝ → E) :
    regularPrimitive c f 0 = 0 := by simp [regularPrimitive]

theorem weightedMean_zero [CompleteSpace E] (c : ℕ) (f : ℝ → E) :
    weightedMean c f 0 = (1 / ((c : ℝ) + 1)) • f 0 := by
  simp only [weightedMean, mul_zero, intervalIntegral.integral_smul_const,
    integral_pow, one_pow, zero_pow (Nat.succ_ne_zero c), sub_zero]

/-- Multiplication by the integrating factor gives the ordinary primitive. -/
theorem regularPrimitive_integratingFactor (c : ℕ) (f : ℝ → E) (ξ : ℝ) :
    ξ ^ c • regularPrimitive c f ξ = ∫ s in (0 : ℝ)..ξ, s ^ c • f s := by
  calc
    ξ ^ c • regularPrimitive c f ξ =
        ξ • ∫ t in (0 : ℝ)..1, (t * ξ) ^ c • f (t * ξ) := by
      unfold regularPrimitive weightedMean
      rw [smul_comm, ← intervalIntegral.integral_smul]
      congr 1
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [mul_pow, smul_smul]
      rw [mul_comm]
    _ = _ := by
      simpa only [zero_mul, one_mul] using
        intervalIntegral.smul_integral_comp_mul_right (a := 0) (b := 1)
          (fun s => s ^ c • f s) ξ

theorem regularPrimitive_eq_div (c : ℕ) (f : ℝ → E) {ξ : ℝ} (hξ : ξ ≠ 0) :
    regularPrimitive c f ξ = (ξ ^ c)⁻¹ • ∫ s in (0 : ℝ)..ξ, s ^ c • f s := by
  rw [← regularPrimitive_integratingFactor]
  simp only [inv_smul_smul₀ (pow_ne_zero c hξ)]

/-- The axis derivative is the normalized average at zero. -/
theorem regularPrimitive_hasDerivAt_zero (c : ℕ) {f : ℝ → E} (hf : Continuous f) :
    HasDerivAt (regularPrimitive c f) (weightedMean c f 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  apply ((weightedMean_continuous c hf).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hne : t ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using ht
  simp only [zero_add, regularPrimitive, zero_smul, sub_zero, inv_smul_smul₀ hne]

theorem weightedMean_norm_le (c : ℕ) (f : ℝ → E) (ξ M : ℝ)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (t * ξ)‖ ≤ M) :
    ‖weightedMean c f ξ‖ ≤ M := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := M) (f := fun t => (t ^ c) • f (t * ξ)) ?_
  · simpa only [weightedMean, sub_zero, abs_one, mul_one] using h
  intro t ht
  have ht0 : t ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht0.1.le, ht0.2⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht'.1 c)]
  exact (mul_le_mul (pow_le_one₀ ht'.1 ht'.2) (hf t ht') (norm_nonneg _) zero_le_one).trans_eq
    (one_mul M)

theorem regularPrimitive_norm_le (c : ℕ) (f : ℝ → E) (ξ M : ℝ)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (t * ξ)‖ ≤ M) :
    ‖regularPrimitive c f ξ‖ ≤ |ξ| * M := by
  rw [regularPrimitive, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (weightedMean_norm_le c f ξ M hf) (abs_nonneg ξ)

/-- Differentiating the integrating-factor formula gives a nonsingular
formula for the radial derivative away from the axis. -/
theorem regularPrimitive_hasDerivAt_ne_zero [CompleteSpace E] (c : ℕ)
    {f : ℝ → E} (hf : Continuous f) {ξ : ℝ} (hξ : ξ ≠ 0) :
    HasDerivAt (regularPrimitive c f)
      (f ξ - (c : ℝ) • weightedMean c f ξ) ξ := by
  have hg : Continuous (fun s : ℝ => s ^ c • f s) := (continuous_id.pow c).smul hf
  have hi := (hasDerivAt_pow c ξ).fun_inv (pow_ne_zero c hξ)
  have hd := hi.fun_smul (hg.integral_hasStrictDerivAt 0 ξ).hasDerivAt
  have he : regularPrimitive c f =ᶠ[𝓝 ξ]
      (fun x : ℝ => (x ^ c)⁻¹ • ∫ s in (0 : ℝ)..x, s ^ c • f s) := by
    filter_upwards [eventually_ne_nhds hξ] with x hx
    exact regularPrimitive_eq_div c f hx
  have hfactor : (-(c : ℝ) * ξ ^ (c - 1) / (ξ ^ c) ^ 2) * (ξ ^ c * ξ) = -(c : ℝ) := by
    cases c with
    | zero => simp
    | succ n =>
        simp only [Nat.add_sub_cancel, pow_succ]
        field_simp
  convert! hd.congr_of_eventuallyEq he using 1
  rw [inv_smul_smul₀ (pow_ne_zero c hξ), ← regularPrimitive_integratingFactor c f ξ,
    regularPrimitive, smul_smul, smul_smul]
  rw [neg_mul] at hfactor
  rw [← mul_assoc] at hfactor
  rw [hfactor, neg_smul]
  simp only [sub_eq_add_neg]

/-- The same derivative formula is valid at zero; no singular division
is used to define or differentiate the solution there. -/
theorem regularPrimitive_hasDerivAt [CompleteSpace E] (c : ℕ)
    {f : ℝ → E} (hf : Continuous f) (ξ : ℝ) :
    HasDerivAt (regularPrimitive c f)
      (f ξ - (c : ℝ) • weightedMean c f ξ) ξ := by
  by_cases hξ : ξ = 0
  · subst ξ
    have hd := regularPrimitive_hasDerivAt_zero c hf
    convert! hd using 1
    rw [weightedMean_zero]
    calc
      _ = ((1 : ℝ) - (c : ℝ) * (1 / ((c : ℝ) + 1))) • f 0 := by
        rw [sub_smul, one_smul, mul_smul]
      _ = _ := by
        congr 1
        field_simp; ring
  · exact regularPrimitive_hasDerivAt_ne_zero c hf hξ

theorem regularPrimitive_equation [CompleteSpace E] (c : ℕ)
    {f : ℝ → E} (hf : Continuous f) {ξ : ℝ} (hξ : ξ ≠ 0) :
    deriv (regularPrimitive c f) ξ + ((c : ℝ) / ξ) • regularPrimitive c f ξ = f ξ := by
  rw [(regularPrimitive_hasDerivAt c hf ξ).deriv, regularPrimitive, smul_smul,
    div_mul_cancel₀ _ hξ, sub_add_cancel]

theorem regularPrimitive_derivative_continuous [CompleteSpace E] (c : ℕ)
    {f : ℝ → E} (hf : Continuous f) : Continuous (deriv (regularPrimitive c f)) := by
  have he : deriv (regularPrimitive c f) = fun ξ => f ξ - (c : ℝ) • weightedMean c f ξ :=
    funext fun ξ => (regularPrimitive_hasDerivAt c hf ξ).deriv
  rw [he]
  exact hf.sub (continuous_const.smul (weightedMean_continuous c hf))

end RadialInverse

/-- The six actual components of the first-order radial system. -/
abbrev Vec := Fin 6 → ℂ

/-- Continuous paths on the full fixed radial interval. -/
abbrev Path (R : ℝ) := C(Icc (0 : ℝ) R, Vec)

/-- Coefficient path: an abbreviation for `C(Icc (0 : ℝ) R, Vec →L[ℂ] Vec)`. -/
abbrev CoefficientPath (R : ℝ) := C(Icc (0 : ℝ) R, Vec →L[ℂ] Vec)

/-- Extend path, given by `f (projIcc 0 R hR ξ)`. -/
def extendPath {R : ℝ} (hR : 0 ≤ R) (f : Path R) (ξ : ℝ) : Vec :=
  f (projIcc 0 R hR ξ)

theorem extendPath_continuous {R : ℝ} (hR : 0 ≤ R) (f : Path R) :
    Continuous (extendPath hR f) :=
  f.continuous.comp continuous_projIcc

theorem extendPath_apply {R : ℝ} (hR : 0 ≤ R) (f : Path R) (ξ : Icc (0 : ℝ) R) :
    extendPath hR f ξ = f ξ := by simp only [extendPath, projIcc_val]

/-- Path inverse value as an element of `Path R`. -/
def pathInverseValue {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ) (f : Path R) : Path R :=
  ⟨fun ξ i => regularPrimitive (c i) (fun s => extendPath hR f s i) ξ,
    continuous_pi fun i =>
      (regularPrimitive_continuous (c i)
        ((continuous_apply i).comp (extendPath_continuous hR f))).comp continuous_subtype_val⟩

theorem norm_pathInverseValue_le {R : ℝ} (hR : 0 ≤ R)
    (c : Fin 6 → ℕ) (f : Path R) : ‖pathInverseValue hR c f‖ ≤ R * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hR (norm_nonneg f))).mpr
  intro ξ
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hR (norm_nonneg f))).mpr
  intro i
  change ‖regularPrimitive (c i) (fun s => extendPath hR f s i) ξ‖ ≤ R * ‖f‖
  refine (regularPrimitive_norm_le (c i) _ ξ ‖f‖ ?_).trans ?_
  · intro t ht
    exact (norm_le_pi_norm (extendPath hR f (t * ξ)) i).trans (f.norm_coe_le_norm _)
  · exact mul_le_mul_of_nonneg_right
      ((abs_of_nonneg ξ.2.1).le.trans ξ.2.2) (norm_nonneg f)

/-- The diagonal integral operator is bounded and complex linear on actual paths. -/
def pathInverse {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ) : Path R →L[ℂ] Path R :=
  LinearMap.mkContinuous {
    toFun := pathInverseValue hR c
    map_add' := by
      intro f g
      ext ξ i
      change (ξ : ℝ) • (∫ t in (0 : ℝ)..1,
          (t ^ c i) • (extendPath hR f (t * ξ) i + extendPath hR g (t * ξ) i)) = _
      simp only [smul_add]
      rw [intervalIntegral.integral_add, smul_add]
      · rfl
      · exact ((continuous_id.pow (c i)).smul
          (((continuous_apply i).comp (extendPath_continuous hR f)).comp
            (continuous_id.mul continuous_const))).intervalIntegrable _ _
      · exact ((continuous_id.pow (c i)).smul
          (((continuous_apply i).comp (extendPath_continuous hR g)).comp
            (continuous_id.mul continuous_const))).intervalIntegrable _ _
    map_smul' := by
      intro a f
      ext ξ i
      change (ξ : ℝ) • (∫ t in (0 : ℝ)..1,
          (t ^ c i) • (a • extendPath hR f (t * ξ) i)) =
        a • ((ξ : ℝ) • ∫ t in (0 : ℝ)..1, (t ^ c i) • extendPath hR f (t * ξ) i)
      conv_lhs => arg 2; arg 1; ext t; rw [smul_comm (t ^ c i) a]
      rw [intervalIntegral.integral_smul, smul_comm]
  } R (norm_pathInverseValue_le hR c)

theorem pathInverse_apply {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ)
    (f : Path R) (ξ : Icc (0 : ℝ) R) (i : Fin 6) :
    pathInverse hR c f ξ i =
      (ξ : ℝ) • ∫ t in (0 : ℝ)..1, (t ^ c i) • extendPath hR f (t * ξ) i := rfl

/-- Coefficient action value, given by `⟨fun ξ => A ξ (f ξ), A.continuous.clm_apply
f.continuous⟩`. -/
noncomputable def coefficientActionValue {R : ℝ} (A : CoefficientPath R) (f : Path R) : Path R :=
  ⟨fun ξ => A ξ (f ξ), A.continuous.clm_apply f.continuous⟩

theorem norm_coefficientActionValue_le {R : ℝ} (A : CoefficientPath R) (f : Path R) :
    ‖coefficientActionValue A f‖ ≤ ‖A‖ * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg f))).mpr
  intro ξ
  exact ((A ξ).le_opNorm (f ξ)).trans
    (mul_le_mul (A.norm_coe_le_norm ξ) (f.norm_coe_le_norm ξ)
      (norm_nonneg _) (norm_nonneg _))

/-- Coefficient action linear, bundling `toFun`, `toFun`, `map_add`, `map_smul` and the required
compatibility proofs. -/
def coefficientActionLinear {R : ℝ} : CoefficientPath R →ₗ[ℂ] Path R →ₗ[ℂ] Path R where
  toFun A := {
    toFun := coefficientActionValue A
    map_add' := by intro f g; ext ξ i; exact congrFun (map_add (A ξ) (f ξ) (g ξ)) i
    map_smul' := by intro a f; ext ξ i; exact congrFun (map_smul (A ξ) a (f ξ)) i }
  map_add' := by intro A B; ext f ξ i; rfl
  map_smul' := by intro a A; ext f ξ i; rfl

/-- Pointwise matrix action is a genuine bounded bilinear map of path spaces. -/
def coefficientAction {R : ℝ} : CoefficientPath R →L[ℂ] Path R →L[ℂ] Path R :=
  (coefficientActionLinear (R := R)).mkContinuous₂
    (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜₃ := ℂ)
    (E := CoefficientPath R) (F := Path R) (G := Path R) 1
    (fun A f => by
      change ‖coefficientActionValue A f‖ ≤ 1 * ‖A‖ * ‖f‖
      simpa only [one_mul] using norm_coefficientActionValue_le A f)

theorem coefficientAction_apply {R : ℝ} (A : CoefficientPath R) (f : Path R)
    (ξ : Icc (0 : ℝ) R) : coefficientAction A f ξ = A ξ (f ξ) := rfl

/-- Path letter, defined pointwise by `pathInverse hR c (if b then coefficientAction (A₁ z)
(deriv F z) else coefficientAction (A₀ z) (F z))`. -/
def pathLetter {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ)
    (A₀ A₁ : ℂ → CoefficientPath R) (b : Bool) (F : ℂ → Path R) : ℂ → Path R :=
  fun z => pathInverse hR c
    (if b then coefficientAction (A₁ z) (deriv F z) else coefficientAction (A₀ z) (F z))

/-- Path word as an element of `w, F => pathLetter hR c A₀ A₁ b (pathWord hR c A₀ A₁ w F)`. -/
def pathWord {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ)
    (A₀ A₁ : ℂ → CoefficientPath R) : List Bool → (ℂ → Path R) → ℂ → Path R
  | [], F => F
  | b :: w, F => pathLetter hR c A₀ A₁ b (pathWord hR c A₀ A₁ w F)

theorem pathLetter_holomorphic {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ)
    {A₀ A₁ : ℂ → CoefficientPath R} {F : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hF : DifferentiableOn ℂ F U) (b : Bool) :
    DifferentiableOn ℂ (pathLetter hR c A₀ A₁ b F) U := by
  have hAction : Differentiable ℂ (coefficientAction (R := R)) :=
    ContinuousLinearMap.differentiable (𝕜 := ℂ)
      (E := CoefficientPath R) (F := Path R →L[ℂ] Path R) coefficientAction
  cases b
  · exact (pathInverse hR c).differentiable.comp_differentiableOn
      ((hAction.comp_differentiableOn hA₀).clm_apply hF)
  · exact (pathInverse hR c).differentiable.comp_differentiableOn
      ((hAction.comp_differentiableOn hA₁).clm_apply (hF.deriv hU))

/-- Every finite word is holomorphic before any convergence is asserted. -/
theorem pathWord_holomorphic {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ)
    {A₀ A₁ : ℂ → CoefficientPath R} {F : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hF : DifferentiableOn ℂ F U) (w : List Bool) :
    DifferentiableOn ℂ (pathWord hR c A₀ A₁ w F) U := by
  induction w with
  | nil => exact hF
  | cons b w ih => exact pathLetter_holomorphic hR c hU hA₀ hA₁ ih b

/-- Path evaluation, given by `(ContinuousLinearMap.proj i).comp (ContinuousMap.evalCLM ℂ ξ)`. -/
def pathEvaluation {R : ℝ} (ξ : Icc (0 : ℝ) R) (i : Fin 6) : Path R →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj i).comp (ContinuousMap.evalCLM ℂ ξ)

theorem pathEvaluation_apply {R : ℝ} (ξ : Icc (0 : ℝ) R) (i : Fin 6) (f : Path R) :
    pathEvaluation ξ i f = f ξ i := rfl

/-- Coordinate evaluation commutes with the genuine complex derivative. -/
theorem pathEvaluation_deriv {R : ℝ} {F : ℂ → Path R} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (ξ : Icc (0 : ℝ) R) (i : Fin 6) :
    deriv (fun w => F w ξ i) z = deriv F z ξ i := by
  exact ((pathEvaluation ξ i).hasFDerivAt.comp_hasDerivAt z hF.hasDerivAt).deriv

/-- Raw field, defined pointwise by `extendPath hR (F z) r`. -/
def rawField {R : ℝ} (hR : 0 ≤ R) (F : ℂ → Path R) : VolterraAnalyticBounds.Field :=
  fun r z => extendPath hR (F z) r

/-- Raw coefficient, defined pointwise by `LinearMap.toMatrix' (A z (projIcc 0 R hR
r)).toLinearMap`. -/
def rawCoefficient {R : ℝ} (hR : 0 ≤ R) (A : ℂ → CoefficientPath R) :
    VolterraAnalyticBounds.Coeff :=
  fun r z => LinearMap.toMatrix' (A z (projIcc 0 R hR r)).toLinearMap

theorem rawCoefficient_mulVec {R : ℝ} (hR : 0 ≤ R) (A : ℂ → CoefficientPath R)
    (r : ℝ) (z : ℂ) (v : Vec) :
    (rawCoefficient hR A r z).mulVec v = A z (projIcc 0 R hR r) v := by
  rw [rawCoefficient, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

theorem rawField_deriv {R : ℝ} (hR : 0 ≤ R) {F : ℂ → Path R} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (r : ℝ) :
    VolterraAnalyticBounds.parameterDeriv (rawField hR F) r z =
      rawField hR (deriv F) r z := by
  funext i
  exact pathEvaluation_deriv hF (projIcc 0 R hR r) i

theorem scaled_radius_mem {R r t : ℝ} (hr : r ∈ Icc (0 : ℝ) R)
    (ht : t ∈ Icc (0 : ℝ) 1) : t * r ∈ Icc (0 : ℝ) R :=
  ⟨mul_nonneg ht.1 hr.1, (mul_le_of_le_one_left hr.1 ht.2).trans hr.2⟩

/-- Every path letter is the actual integral/derivative letter on its radial interval. -/
theorem rawField_pathLetter {R : ℝ} (hR : 0 ≤ R)
    (A₀ A₁ : ℂ → CoefficientPath R) {F : ℂ → Path R} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (b : Bool) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) R) :
    rawField hR (pathLetter hR VolterraAnalyticBounds.exponent A₀ A₁ b F) r z =
      VolterraAnalyticBounds.letter (rawCoefficient hR A₀) (rawCoefficient hR A₁) b
        (rawField hR F) r z := by
  change pathLetter hR VolterraAnalyticBounds.exponent A₀ A₁ b F z (projIcc 0 R hR r) = _
  rw [projIcc_of_mem hR hr]
  cases b <;> funext i <;>
    simp only [pathLetter, Bool.false_eq_true, ite_false, ite_true, pathInverse_apply,
      VolterraAnalyticBounds.letter, VolterraAnalyticBounds.radialInverse]
  · congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [VolterraAnalyticBounds.matrixAction, rawCoefficient_mulVec,
      rawField, extendPath, coefficientAction_apply]
  · congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [VolterraAnalyticBounds.matrixAction, rawCoefficient_mulVec, rawField_deriv hR hF,
      rawField, extendPath, coefficientAction_apply]

theorem letter_congrOn {R : ℝ} {U : Set ℂ} (hU : IsOpen U)
    (A₀ A₁ : VolterraAnalyticBounds.Coeff) (b : Bool)
    {F G : VolterraAnalyticBounds.Field}
    (hFG : ∀ r ∈ Icc (0 : ℝ) R, ∀ z ∈ U, F r z = G r z)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) R) {z : ℂ} (hz : z ∈ U) :
    VolterraAnalyticBounds.letter A₀ A₁ b F r z =
      VolterraAnalyticBounds.letter A₀ A₁ b G r z := by
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) R) :
      VolterraAnalyticBounds.parameterDeriv F s z =
        VolterraAnalyticBounds.parameterDeriv G s z := by
    funext i
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hU.mem_nhds hz] with w hw
    exact congrFun (hFG s hs w hw) i
  cases b <;> funext i <;>
    simp only [VolterraAnalyticBounds.letter, Bool.false_eq_true, ite_false, ite_true,
      VolterraAnalyticBounds.radialInverse]
  · congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    simp only [VolterraAnalyticBounds.matrixAction, hFG (t * r) (scaled_radius_mem hr ht') z hz]
  · congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    simp only [VolterraAnalyticBounds.matrixAction, hd (t * r) (scaled_radius_mem hr ht')]

/-- The finite path construction represents precisely the raw Volterra words. -/
theorem rawField_pathWord {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {F : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hF : DifferentiableOn ℂ F U) (w : List Bool)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) R) {z : ℂ} (hz : z ∈ U) :
    VolterraAnalyticBounds.word (rawCoefficient hR A₀) (rawCoefficient hR A₁) w
        (rawField hR F) r z =
      rawField hR (pathWord hR VolterraAnalyticBounds.exponent A₀ A₁ w F) r z := by
  induction w generalizing r z with
  | nil => rfl
  | cons b w ih =>
      rw [pathWord, rawField_pathLetter hR A₀ A₁
        ((pathWord_holomorphic hR _ hU hA₀ hA₁ hF w).differentiableAt (hU.mem_nhds hz)) b hr]
      exact letter_congrOn hU _ _ b (fun r hr z hz => ih hr hz) hr hz

theorem raw_word_analytic {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {F : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hF : DifferentiableOn ℂ F U) {center : ℂ} {ρ : ℝ}
    (hDisk : Metric.closedBall center ρ ⊆ U) (w : List Bool) :
    VolterraAnalyticBounds.AnalyticField
      (VolterraAnalyticBounds.word (rawCoefficient hR A₀) (rawCoefficient hR A₁) w
        (rawField hR F)) R center ρ := by
  intro r hr i
  have hp := pathWord_holomorphic hR VolterraAnalyticBounds.exponent hU hA₀ hA₁ hF w
  have he := (pathEvaluation (projIcc 0 R hR r) i).differentiable.comp_differentiableOn hp
  have hraw : DifferentiableOn ℂ
      (fun z => VolterraAnalyticBounds.word (rawCoefficient hR A₀) (rawCoefficient hR A₁) w
        (rawField hR F) r z i) U := by
    apply he.congr
    intro z hz
    exact congrFun (rawField_pathWord hR hU hA₀ hA₁ hF w hr hz) i
  exact (hraw.analyticOnNhd hU).mono hDisk

/-- Binary words as an element of `ℕ → List (List Bool) | 0 => [[]] | k + 1 => (binaryWords
k).map (List.cons false) ++ (binaryWords k).map (List.cons true)`. -/
def binaryWords : ℕ → List (List Bool)
  | 0 => [[]]
  | k + 1 => (binaryWords k).map (List.cons false) ++ (binaryWords k).map (List.cons true)

theorem binaryWords_length (k : ℕ) : (binaryWords k).length = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [binaryWords, ih, pow_succ, Nat.mul_two]

theorem length_of_mem_binaryWords {k : ℕ} {w : List Bool} (hw : w ∈ binaryWords k) :
    w.length = k := by
  induction k generalizing w with
  | zero => simpa [binaryWords] using hw
  | succ k ih =>
      simp only [binaryWords, List.mem_append, List.mem_map] at hw
      rcases hw with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ <;>
        simpa only [List.length_cons] using congrArg Nat.succ (ih hv)

theorem list_sum_eval {X E : Type*} [AddCommMonoid E] (l : List (X → E)) (x : X) :
    l.sum x = (l.map (fun f => f x)).sum := by
  induction l with
  | nil => rfl
  | cons f l ih =>
      simpa only [List.sum_cons, List.map_cons, Pi.add_apply] using congrArg (f x + ·) ih

theorem norm_list_sum_le {E : Type*} [SeminormedAddCommGroup E]
    (l : List E) (M : ℝ) (h : ∀ x ∈ l, ‖x‖ ≤ M) :
    ‖l.sum‖ ≤ (l.length : ℝ) * M := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      calc
        ‖x + l.sum‖ ≤ ‖x‖ + ‖l.sum‖ := norm_add_le _ _
        _ ≤ M + (l.length : ℝ) * M :=
          add_le_add (h x (List.mem_cons_self ..)) (ih (fun y hy => h y (List.mem_cons_of_mem _
              hy)))
        _ = _ := by ring

theorem holomorphic_list_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (l : List (ℂ → E)) {U : Set ℂ} (h : ∀ f ∈ l, DifferentiableOn ℂ f U) :
    DifferentiableOn ℂ l.sum U := by
  induction l with
  | nil => exact differentiableOn_const _
  | cons f l ih =>
      exact (h f (List.mem_cons_self ..)).add (ih (fun g hg => h g (List.mem_cons_of_mem _ hg)))

/-- Layer, given by `((binaryWords k).map (fun w => pathWord hR c A₀ A₁ w F)).sum`. -/
def layer {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ)
    (A₀ A₁ : ℂ → CoefficientPath R) (F : ℂ → Path R) (k : ℕ) : ℂ → Path R :=
  ((binaryWords k).map (fun w => pathWord hR c A₀ A₁ w F)).sum

theorem layer_holomorphic {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ)
    {A₀ A₁ : ℂ → CoefficientPath R} {F : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hF : DifferentiableOn ℂ F U) (k : ℕ) :
    DifferentiableOn ℂ (layer hR c A₀ A₁ F k) U := by
  apply holomorphic_list_sum
  intro g hg
  rcases List.mem_map.mp hg with ⟨w, hw, rfl⟩
  exact pathWord_holomorphic hR c hU hA₀ hA₁ hF w

@[simp] theorem layer_zero {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ)
    (A₀ A₁ : ℂ → CoefficientPath R) (F : ℂ → Path R) :
    layer hR c A₀ A₁ F 0 = F := by simp [layer, binaryWords, pathWord]

theorem pathLetter_add {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ)
    (A₀ A₁ : ℂ → CoefficientPath R) (b : Bool) {F G : ℂ → Path R} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (hG : DifferentiableAt ℂ G z) :
    pathLetter hR c A₀ A₁ b (F + G) z =
      pathLetter hR c A₀ A₁ b F z + pathLetter hR c A₀ A₁ b G z := by
  cases b <;> simp only [pathLetter, Bool.false_eq_true, ite_false, ite_true, Pi.add_apply]
  · simp only [map_add]
  · change pathInverse hR c (coefficientAction (A₁ z) (deriv (fun w => F w + G w) z)) = _
    rw [deriv_fun_add hF hG]
    simp only [map_add]

theorem pathLetter_list_sum {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ)
    (A₀ A₁ : ℂ → CoefficientPath R) (b : Bool) (l : List (ℂ → Path R))
    {U : Set ℂ} (hU : IsOpen U) (h : ∀ F ∈ l, DifferentiableOn ℂ F U)
    {z : ℂ} (hz : z ∈ U) :
    (l.map (pathLetter hR c A₀ A₁ b)).sum z = pathLetter hR c A₀ A₁ b l.sum z := by
  induction l with
  | nil => cases b <;> simp [pathLetter]
  | cons F l ih =>
      rw [List.map_cons, List.sum_cons, Pi.add_apply, List.sum_cons,
        pathLetter_add hR c A₀ A₁ b
          ((h F (List.mem_cons_self ..)).differentiableAt (hU.mem_nhds hz))
          ((holomorphic_list_sum l (fun G hG => h G (List.mem_cons_of_mem _ hG))).differentiableAt
            (hU.mem_nhds hz)), ih (fun G hG => h G (List.mem_cons_of_mem _ hG))]

theorem layer_succ {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ)
    {A₀ A₁ : ℂ → CoefficientPath R} {F : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hF : DifferentiableOn ℂ F U) (k : ℕ) {z : ℂ} (hz : z ∈ U) :
    layer hR c A₀ A₁ F (k + 1) z =
      pathLetter hR c A₀ A₁ false (layer hR c A₀ A₁ F k) z +
        pathLetter hR c A₀ A₁ true (layer hR c A₀ A₁ F k) z := by
  have hl : ∀ G ∈ (binaryWords k).map (fun w => pathWord hR c A₀ A₁ w F),
      DifferentiableOn ℂ G U := by
    intro G hG
    rcases List.mem_map.mp hG with ⟨w, hw, rfl⟩
    exact pathWord_holomorphic hR c hU hA₀ hA₁ hF w
  have hfalse := pathLetter_list_sum hR c A₀ A₁ false _ hU hl hz
  have htrue := pathLetter_list_sum hR c A₀ A₁ true _ hU hl hz
  simpa only [layer, binaryWords, List.map_append, List.sum_append, Pi.add_apply,
    List.map_map, Function.comp_def, pathWord] using congrArg₂ (· + ·) hfalse htrue

theorem rawField_bound {R : ℝ} (hR : 0 ≤ R) (F : ℂ → Path R)
    {center : ℂ} {ρ B : ℝ} (hF : ∀ z ∈ Metric.closedBall center ρ, ‖F z‖ ≤ B) :
    VolterraAnalyticBounds.RadialBound (rawField hR F) R center ρ B 0 := by
  intro r hr z hz i
  have h := (norm_le_pi_norm (F z (projIcc 0 R hR r)) i).trans
    ((F z).norm_coe_le_norm (projIcc 0 R hR r))
  simpa only [rawField, extendPath, pow_zero, Nat.factorial_zero, Nat.cast_one,
    mul_one, div_one] using h.trans (hF z hz)

theorem rawCoefficient_bound {R : ℝ} (hR : 0 ≤ R) (A : ℂ → CoefficientPath R)
    {center : ℂ} {ρ M : ℝ} (hA : ∀ z ∈ Metric.closedBall center ρ, ‖A z‖ ≤ M) :
    VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A) R center ρ (6 * M) := by
  intro r hr z hz i
  calc
    ∑ j, ‖rawCoefficient hR A r z i j‖ ≤ ∑ _j : Fin 6, M := by
      apply Finset.sum_le_sum
      intro j hj
      change ‖A z (projIcc 0 R hR r) (Pi.single j 1) i‖ ≤ M
      calc
        _ ≤ ‖A z (projIcc 0 R hR r) (Pi.single j 1)‖ := norm_le_pi_norm _ i
        _ ≤ ‖A z (projIcc 0 R hR r)‖ * ‖(Pi.single j 1 : Vec)‖ :=
          (A z (projIcc 0 R hR r)).le_opNorm (Pi.single j 1 : Vec)
        _ = ‖A z (projIcc 0 R hR r)‖ := by rw [Pi.norm_single, norm_one, mul_one]
        _ ≤ ‖A z‖ := (A z).norm_coe_le_norm _
        _ ≤ M := hA z hz
    _ = 6 * M := by simp

theorem pathWord_bound {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {F : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hF : DifferentiableOn ℂ F U) {center : ℂ} {ρ σ B M : ℝ}
    (hDisk : Metric.closedBall center σ ⊆ U) (hgap : ρ < σ)
    (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hshape : VolterraAnalyticBounds.DerivativeShape (rawCoefficient hR A₁))
    (hbA₀ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₀) R center σ M)
    (hbA₁ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₁) R center σ M)
    (hbF : ∀ z ∈ Metric.closedBall center σ, ‖F z‖ ≤ B)
    (w : List Bool) {z : ℂ} (hz : z ∈ Metric.closedBall center ρ) :
    ‖pathWord hR VolterraAnalyticBounds.exponent A₀ A₁ w F z‖ ≤
      B * VolterraAnalyticBounds.wordMajorant (M * R) (max 1 (σ - ρ)⁻¹) w.length := by
  have hc : 0 ≤ B * VolterraAnalyticBounds.wordMajorant (M * R) (max 1 (σ - ρ)⁻¹) w.length :=
    mul_nonneg hB (VolterraAnalyticBounds.wordMajorant_nonneg (mul_nonneg hM hR)
      (le_trans zero_le_one (le_max_left _ _)) _)
  apply (ContinuousMap.norm_le _ hc).mpr
  intro ξ
  apply (pi_norm_le_iff_of_nonneg hc).mpr
  intro i
  have hb := VolterraAnalyticBounds.norm_word_le hB hM hR hgap hshape hbA₀ hbA₁
    (rawField_bound hR F hbF) (fun v => raw_word_analytic hR hU hA₀ hA₁ hF hDisk v)
    w ξ.2 hz i
  rw [rawField_pathWord hR hU hA₀ hA₁ hF w ξ.2
    (hDisk (Metric.closedBall_subset_closedBall hgap.le hz))] at hb
  simpa only [rawField, extendPath, projIcc_val] using hb

theorem layer_bound {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {F : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hF : DifferentiableOn ℂ F U) {center : ℂ} {ρ σ B M : ℝ}
    (hDisk : Metric.closedBall center σ ⊆ U) (hgap : ρ < σ)
    (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hshape : VolterraAnalyticBounds.DerivativeShape (rawCoefficient hR A₁))
    (hbA₀ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₀) R center σ M)
    (hbA₁ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₁) R center σ M)
    (hbF : ∀ z ∈ Metric.closedBall center σ, ‖F z‖ ≤ B)
    (k : ℕ) {z : ℂ} (hz : z ∈ Metric.closedBall center ρ) :
    ‖layer hR VolterraAnalyticBounds.exponent A₀ A₁ F k z‖ ≤
      B * 2 ^ k * VolterraAnalyticBounds.wordMajorant (M * R) (max 1 (σ - ρ)⁻¹) k := by
  rw [layer, list_sum_eval]
  refine (norm_list_sum_le _
    (B * VolterraAnalyticBounds.wordMajorant (M * R) (max 1 (σ - ρ)⁻¹) k) ?_).trans_eq ?_
  · intro x hx
    simp only [List.mem_map] at hx
    rcases hx with ⟨G, ⟨w, hw, rfl⟩, rfl⟩
    have hb := pathWord_bound hR hU hA₀ hA₁ hF hDisk hgap hB hM hshape hbA₀ hbA₁ hbF w hz
    simpa only [length_of_mem_binaryWords hw] using hb
  · simp only [List.length_map, binaryWords_length, Nat.cast_pow, Nat.cast_ofNat]
    ring

/-- Solution series, defined pointwise by `∑' k : ℕ, layer hR VolterraAnalyticBounds.exponent A₀
A₁ F k z`. -/
def solutionSeries {R : ℝ} (hR : 0 ≤ R)
    (A₀ A₁ : ℂ → CoefficientPath R) (F : ℂ → Path R) : ℂ → Path R :=
  fun z => ∑' k : ℕ, layer hR VolterraAnalyticBounds.exponent A₀ A₁ F k z

section Summation

variable {R : ℝ} (hR : 0 ≤ R)
  {A₀ A₁ : ℂ → CoefficientPath R} {F : ℂ → Path R} {U : Set ℂ}
  (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
  (hF : DifferentiableOn ℂ F U) {center : ℂ} {ρ σ B M : ℝ}
  (hDisk : Metric.closedBall center σ ⊆ U) (hgap : ρ < σ)
  (hB : 0 ≤ B) (hM : 0 ≤ M)
  (hshape : VolterraAnalyticBounds.DerivativeShape (rawCoefficient hR A₁))
  (hbA₀ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₀) R center σ M)
  (hbA₁ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₁) R center σ M)
  (hbF : ∀ z ∈ Metric.closedBall center σ, ‖F z‖ ≤ B)

include hR hU hA₀ hA₁ hF hDisk hgap hB hM hshape hbA₀ hbA₁ hbF

theorem solutionSeries_hasSum {z : ℂ} (hz : z ∈ Metric.closedBall center ρ) :
    HasSum (fun k => layer hR VolterraAnalyticBounds.exponent A₀ A₁ F k z)
      (solutionSeries hR A₀ A₁ F z) := by
  apply Summable.hasSum
  apply Summable.of_norm_bounded
    (VolterraAnalyticBounds.summable_wordLayers (mul_nonneg hM hR)
      (le_trans zero_le_one (le_max_left _ _)))
  · intro k
    exact layer_bound hR hU hA₀ hA₁ hF hDisk hgap hB hM hshape hbA₀ hbA₁ hbF k hz

/-- The infinite series is a holomorphic map into the space of actual
continuous radial paths, with no smallness restriction on the coefficients. -/
theorem solutionSeries_holomorphic :
    DifferentiableOn ℂ (solutionSeries hR A₀ A₁ F) (Metric.ball center ρ) := by
  apply Complex.differentiableOn_tsum_of_summable_norm
    (VolterraAnalyticBounds.summable_wordLayers (B := B) (mul_nonneg hM hR)
      (le_trans zero_le_one (le_max_left 1 (σ - ρ)⁻¹)))
  · intro k
    exact (layer_holomorphic hR _ hU hA₀ hA₁ hF k).mono
      (fun z hz => hDisk (Metric.closedBall_subset_closedBall hgap.le
        (Metric.ball_subset_closedBall hz)))
  · exact Metric.isOpen_ball
  · intro k z hz
    exact layer_bound hR hU hA₀ hA₁ hF hDisk hgap hB hM hshape hbA₀ hbA₁ hbF k
      (Metric.ball_subset_closedBall hz)

/-- Actual complex differentiation commutes with the convergent Volterra series. -/
theorem solutionSeries_deriv_hasSum {z : ℂ} (hz : z ∈ Metric.ball center ρ) :
    HasSum (fun k => deriv (layer hR VolterraAnalyticBounds.exponent A₀ A₁ F k) z)
      (deriv (solutionSeries hR A₀ A₁ F) z) := by
  apply Complex.hasSum_deriv_of_summable_norm
    (VolterraAnalyticBounds.summable_wordLayers (B := B) (mul_nonneg hM hR)
      (le_trans zero_le_one (le_max_left 1 (σ - ρ)⁻¹)))
  · intro k
    exact (layer_holomorphic hR _ hU hA₀ hA₁ hF k).mono
      (fun z hz => hDisk (Metric.closedBall_subset_closedBall hgap.le
        (Metric.ball_subset_closedBall hz)))
  · exact Metric.isOpen_ball
  · intro k z hz
    exact layer_bound hR hU hA₀ hA₁ hF hDisk hgap hB hM hshape hbA₀ hbA₁ hbF k
      (Metric.ball_subset_closedBall hz)
  · exact hz

/-- The convergent series solves the genuine integral equation. In
particular, convergence is not merely convergence of unrelated scalar bounds. -/
theorem solutionSeries_equation {z : ℂ} (hz : z ∈ Metric.ball center ρ) :
    solutionSeries hR A₀ A₁ F z = F z + pathInverse hR VolterraAnalyticBounds.exponent
      (coefficientAction (A₀ z) (solutionSeries hR A₀ A₁ F z) +
        coefficientAction (A₁ z) (deriv (solutionSeries hR A₀ A₁ F) z)) := by
  have hs := solutionSeries_hasSum hR hU hA₀ hA₁ hF hDisk hgap hB hM hshape hbA₀ hbA₁ hbF
    (Metric.ball_subset_closedBall hz)
  have hd := solutionSeries_deriv_hasSum hR hU hA₀ hA₁ hF hDisk hgap hB hM hshape hbA₀ hbA₁ hbF hz
  let L₀ := (pathInverse hR VolterraAnalyticBounds.exponent).comp (coefficientAction (A₀ z))
  let L₁ := (pathInverse hR VolterraAnalyticBounds.exponent).comp (coefficientAction (A₁ z))
  have hsum := (hs.mapL L₀).add (hd.mapL L₁)
  have hshift : HasSum (fun k => layer hR VolterraAnalyticBounds.exponent A₀ A₁ F (k + 1) z)
      (L₀ (solutionSeries hR A₀ A₁ F z) + L₁ (deriv (solutionSeries hR A₀ A₁ F) z)) := by
    convert! hsum using 1
    funext k
    exact layer_succ hR _ hU hA₀ hA₁ hF k
      (hDisk (Metric.closedBall_subset_closedBall hgap.le (Metric.ball_subset_closedBall hz)))
  calc
    _ = layer hR VolterraAnalyticBounds.exponent A₀ A₁ F 0 z +
        ∑' k, layer hR VolterraAnalyticBounds.exponent A₀ A₁ F (k + 1) z :=
      hs.summable.tsum_eq_zero_add
    _ = _ := by rw [layer_zero, hshift.tsum_eq, map_add]; rfl

end Summation

/-- Canonical series with the actual integrated forcing as its initial layer. -/
def integralSolution {R : ℝ} (hR : 0 ≤ R)
    (A₀ A₁ : ℂ → CoefficientPath R) (f : ℂ → Path R) : ℂ → Path R :=
  solutionSeries hR A₀ A₁ (fun z => pathInverse hR VolterraAnalyticBounds.exponent (f z))

/-- Compactness supplies all coefficient bounds. Thus the actual solution
theorem assumes neither a word bound nor convergence of its defining series. -/
theorem integralSolution_spec {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {f : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U) {center : ℂ} {ρ σ : ℝ}
    (hDisk : Metric.closedBall center σ ⊆ U) (hgap : ρ < σ)
    (hshape : VolterraAnalyticBounds.DerivativeShape (rawCoefficient hR A₁)) :
    DifferentiableOn ℂ (integralSolution hR A₀ A₁ f) (Metric.ball center ρ) ∧
      ∀ z ∈ Metric.ball center ρ,
        integralSolution hR A₀ A₁ f z = pathInverse hR VolterraAnalyticBounds.exponent
          (f z + (coefficientAction (A₀ z) (integralSolution hR A₀ A₁ f z) +
            coefficientAction (A₁ z) (deriv (integralSolution hR A₀ A₁ f) z))) := by
  obtain ⟨K₀, hK₀⟩ := (isCompact_closedBall center σ).exists_bound_of_continuousOn
    (f := A₀) (hA₀.continuousOn.mono hDisk)
  obtain ⟨K₁, hK₁⟩ := (isCompact_closedBall center σ).exists_bound_of_continuousOn
    (f := A₁) (hA₁.continuousOn.mono hDisk)
  obtain ⟨B₀, hB₀⟩ := (isCompact_closedBall center σ).exists_bound_of_continuousOn
    (hf.continuousOn.mono hDisk)
  let K := max 0 (max K₀ K₁)
  have hK : 0 ≤ K := le_max_left _ _
  have hbA₀ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₀) R center σ (6 * K) :=
    rawCoefficient_bound hR A₀ (fun z hz => (hK₀ z hz).trans
      ((le_max_left K₀ K₁).trans (le_max_right 0 (max K₀ K₁))))
  have hbA₁ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₁) R center σ (6 * K) :=
    rawCoefficient_bound hR A₁ (fun z hz => (hK₁ z hz).trans
      ((le_max_right K₀ K₁).trans (le_max_right 0 (max K₀ K₁))))
  let F : ℂ → Path R := fun z => pathInverse hR VolterraAnalyticBounds.exponent (f z)
  have hF : DifferentiableOn ℂ F U :=
    (pathInverse hR VolterraAnalyticBounds.exponent).differentiable.comp_differentiableOn hf
  have hBF : 0 ≤ R * max 0 B₀ := mul_nonneg hR (le_max_left _ _)
  have hbF : ∀ z ∈ Metric.closedBall center σ, ‖F z‖ ≤ R * max 0 B₀ := by
    intro z hz
    exact (norm_pathInverseValue_le hR VolterraAnalyticBounds.exponent (f z)).trans
      (mul_le_mul_of_nonneg_left ((hB₀ z hz).trans (le_max_right _ _)) hR)
  have hM : 0 ≤ 6 * K := mul_nonneg (by norm_num) hK
  refine ⟨solutionSeries_holomorphic hR hU hA₀ hA₁ hF hDisk hgap hBF hM hshape hbA₀ hbA₁ hbF, ?_⟩
  intro z hz
  have he := solutionSeries_equation hR hU hA₀ hA₁ hF hDisk hgap hBF hM hshape hbA₀ hbA₁ hbF hz
  simp only [map_add] at he ⊢
  exact he

/-- Rhs path, given by `f z + (coefficientAction (A₀ z) (W z) + coefficientAction (A₁ z) (deriv
W z))`. -/
def rhsPath {R : ℝ} (A₀ A₁ : ℂ → CoefficientPath R) (f W : ℂ → Path R) (z : ℂ) : Path R :=
  f z + (coefficientAction (A₀ z) (W z) + coefficientAction (A₁ z) (deriv W z))

/-- An actual radial function extending the solved path. Its definition
uses the regular integral even at the axis and beyond the path interval. -/
def liftedField {R : ℝ} (hR : 0 ≤ R) (A₀ A₁ : ℂ → CoefficientPath R)
    (f W : ℂ → Path R) : VolterraAnalyticBounds.Field :=
  fun r z i => regularPrimitive (VolterraAnalyticBounds.exponent i)
    (fun s => extendPath hR (rhsPath A₀ A₁ f W z) s i) r

theorem liftedField_hasDerivAt {R : ℝ} (hR : 0 ≤ R) (A₀ A₁ : ℂ → CoefficientPath R)
    (f W : ℂ → Path R) (r : ℝ) (z : ℂ) (i : Fin 6) :
    HasDerivAt (fun s => liftedField hR A₀ A₁ f W s z i)
      (extendPath hR (rhsPath A₀ A₁ f W z) r i -
        (VolterraAnalyticBounds.exponent i : ℝ) • weightedMean (VolterraAnalyticBounds.exponent i)
          (fun s => extendPath hR (rhsPath A₀ A₁ f W z) s i) r) r :=
  regularPrimitive_hasDerivAt _ ((continuous_apply i).comp (extendPath_continuous hR _)) r

theorem liftedField_derivative_continuous {R : ℝ} (hR : 0 ≤ R)
    (A₀ A₁ : ℂ → CoefficientPath R) (f W : ℂ → Path R) (z : ℂ) (i : Fin 6) :
    Continuous (deriv (fun r => liftedField hR A₀ A₁ f W r z i)) :=
  regularPrimitive_derivative_continuous _ ((continuous_apply i).comp (extendPath_continuous hR _))

theorem liftedField_axis_zero {R : ℝ} (hR : 0 ≤ R)
    (A₀ A₁ : ℂ → CoefficientPath R) (f W : ℂ → Path R) (z : ℂ) :
    liftedField hR A₀ A₁ f W 0 z = 0 := by
  funext i
  exact regularPrimitive_zero _ _

theorem liftedField_eq_trace {R : ℝ} (hR : 0 ≤ R)
    (A₀ A₁ : ℂ → CoefficientPath R) (f W : ℂ → Path R) {z : ℂ}
    (hW : W z = pathInverse hR VolterraAnalyticBounds.exponent (rhsPath A₀ A₁ f W z))
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) R) :
    liftedField hR A₀ A₁ f W r z = rawField hR W r z := by
  funext i
  change regularPrimitive _ _ r = W z (projIcc 0 R hR r) i
  rw [hW, projIcc_of_mem hR hr]
  rfl

/-- Equation RHS as an element of `VolterraAnalyticBounds.Field`. -/
def equationRHS (A₀ A₁ : VolterraAnalyticBounds.Coeff)
    (f W : VolterraAnalyticBounds.Field) : VolterraAnalyticBounds.Field :=
  fun r z => f r z + (VolterraAnalyticBounds.matrixAction A₀ W r z +
    VolterraAnalyticBounds.matrixAction A₁ (VolterraAnalyticBounds.parameterDeriv W) r z)

/-- Radial derivative, defined pointwise by `deriv (fun s : ℝ => W s z i) r`. -/
def radialDeriv (W : VolterraAnalyticBounds.Field) : VolterraAnalyticBounds.Field :=
  fun r z i => deriv (fun s : ℝ => W s z i) r

/-- A genuine regular solution of the singular first-order system. Radial
regularity here is C¹, stated through ordinary derivatives and their continuity. -/
structure IsRegularSolution (R : ℝ) (U : Set ℂ)
    (A₀ A₁ : VolterraAnalyticBounds.Coeff) (f W : VolterraAnalyticBounds.Field) : Prop where
  jointly_continuous : ContinuousOn (fun p : ℝ × ℂ => W p.1 p.2) (Icc (0 : ℝ) R ×ˢ U)
  parameter_holomorphic : ∀ r ∈ Icc (0 : ℝ) R, ∀ i,
    DifferentiableOn ℂ (fun z => W r z i) U
  radial_differentiable : ∀ z ∈ U, ∀ i, Differentiable ℝ (fun r => W r z i)
  radial_derivative_continuous : ∀ z ∈ U, ∀ i, Continuous (fun r => radialDeriv W r z i)
  axis_zero : ∀ z ∈ U, W 0 z = 0
  equation : ∀ r ∈ Icc (0 : ℝ) R, r ≠ 0 → ∀ z ∈ U, ∀ i,
    radialDeriv W r z i + ((VolterraAnalyticBounds.exponent i : ℝ) / r) • W r z i =
      equationRHS A₀ A₁ f W r z i
  axis_derivative : ∀ z ∈ U, ∀ i,
    radialDeriv W 0 z i =
      (1 / ((VolterraAnalyticBounds.exponent i : ℝ) + 1)) • equationRHS A₀ A₁ f W 0 z i

section LiftSolution

variable {R : ℝ} (hR : 0 ≤ R)
  (A₀ A₁ : ℂ → CoefficientPath R) (f W : ℂ → Path R) {U : Set ℂ}
  (hU : IsOpen U) (hWholo : DifferentiableOn ℂ W U)
  (hW : ∀ z ∈ U, W z = pathInverse hR VolterraAnalyticBounds.exponent (rhsPath A₀ A₁ f W z))

include hU hWholo hW

theorem liftedField_parameterDeriv {r : ℝ} (hr : r ∈ Icc (0 : ℝ) R)
    {z : ℂ} (hz : z ∈ U) :
    VolterraAnalyticBounds.parameterDeriv (liftedField hR A₀ A₁ f W) r z =
      rawField hR (deriv W) r z := by
  rw [← rawField_deriv hR (hWholo.differentiableAt (hU.mem_nhds hz)) r]
  funext i
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hU.mem_nhds hz] with w hw
  exact congrFun (liftedField_eq_trace hR A₀ A₁ f W (hW w hw) hr) i

omit hU in
theorem liftedField_holomorphic {r : ℝ} (hr : r ∈ Icc (0 : ℝ) R) (i : Fin 6) :
    DifferentiableOn ℂ (fun z => liftedField hR A₀ A₁ f W r z i) U := by
  have hh := (pathEvaluation (projIcc 0 R hR r) i).differentiable.comp_differentiableOn hWholo
  apply hh.congr
  intro z hz
  exact congrFun (liftedField_eq_trace hR A₀ A₁ f W (hW z hz) hr) i

theorem liftedField_rhs {r : ℝ} (hr : r ∈ Icc (0 : ℝ) R) {z : ℂ} (hz : z ∈ U) :
    extendPath hR (rhsPath A₀ A₁ f W z) r =
      equationRHS (rawCoefficient hR A₀) (rawCoefficient hR A₁) (rawField hR f)
        (liftedField hR A₀ A₁ f W) r z := by
  simp only [equationRHS, VolterraAnalyticBounds.matrixAction, rawCoefficient_mulVec]
  rw [liftedField_parameterDeriv hR A₀ A₁ f W hU hWholo hW hr hz]
  simp only [
    liftedField_eq_trace hR A₀ A₁ f W (hW z hz) hr]
  rfl

omit hU in
theorem liftedField_jointly_continuous :
    ContinuousOn (fun p : ℝ × ℂ => liftedField hR A₀ A₁ f W p.1 p.2)
      (Icc (0 : ℝ) R ×ˢ U) := by
  have hw : ContinuousOn (fun p : ℝ × ℂ => W p.2) (Icc (0 : ℝ) R ×ˢ U) :=
    hWholo.continuousOn.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hr : Continuous (fun p : ℝ × ℂ => projIcc 0 R hR p.1) :=
    continuous_projIcc.comp continuous_fst
  have he : ContinuousOn (fun p : ℝ × ℂ => rawField hR W p.1 p.2)
      (Icc (0 : ℝ) R ×ˢ U) :=
    continuous_eval.comp_continuousOn (hw.prodMk hr.continuousOn)
  apply he.congr
  intro p hp
  exact liftedField_eq_trace hR A₀ A₁ f W (hW p.2 hp.2) hp.1

theorem liftedField_isRegularSolution :
    IsRegularSolution R U (rawCoefficient hR A₀) (rawCoefficient hR A₁)
      (rawField hR f) (liftedField hR A₀ A₁ f W) := by
  refine {
    jointly_continuous := liftedField_jointly_continuous hR A₀ A₁ f W hWholo hW
    parameter_holomorphic := fun r hr i => liftedField_holomorphic hR A₀ A₁ f W hWholo hW hr i
    radial_differentiable := ?_
    radial_derivative_continuous := fun z hz i => liftedField_derivative_continuous hR A₀ A₁ f W z i
    axis_zero := fun z hz => liftedField_axis_zero hR A₀ A₁ f W z
    equation := ?_
    axis_derivative := ?_ }
  · intro z hz i r
    exact (liftedField_hasDerivAt hR A₀ A₁ f W r z i).differentiableAt
  · intro r hr hr0 z hz i
    have hg : Continuous (fun s => extendPath hR (rhsPath A₀ A₁ f W z) s i) :=
      (continuous_apply i).comp (extendPath_continuous hR _)
    have he := regularPrimitive_equation (VolterraAnalyticBounds.exponent i) hg hr0
    change radialDeriv (liftedField hR A₀ A₁ f W) r z i +
      ((VolterraAnalyticBounds.exponent i : ℝ) / r) • liftedField hR A₀ A₁ f W r z i =
        extendPath hR (rhsPath A₀ A₁ f W z) r i at he
    rw [liftedField_rhs hR A₀ A₁ f W hU hWholo hW hr hz] at he
    exact he
  · intro z hz i
    have hg : Continuous (fun s => extendPath hR (rhsPath A₀ A₁ f W z) s i) :=
      (continuous_apply i).comp (extendPath_continuous hR _)
    have he := (regularPrimitive_hasDerivAt_zero (VolterraAnalyticBounds.exponent i) hg).deriv
    rw [weightedMean_zero] at he
    change radialDeriv (liftedField hR A₀ A₁ f W) 0 z i =
      (1 / ((VolterraAnalyticBounds.exponent i : ℝ) + 1)) •
        extendPath hR (rhsPath A₀ A₁ f W z) 0 i at he
    rw [liftedField_rhs hR A₀ A₁ f W hU hWholo hW ⟨le_rfl, hR⟩ hz] at he
    exact he

end LiftSolution

/-- A regular solution on any prescribed finite radial interval. Only
the parameter neighborhood is reduced; coefficient size places no upper
bound on the length of the radial interval. -/
theorem exists_regular_solution {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {f : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U) {center : ℂ} {ρ σ : ℝ}
    (hDisk : Metric.closedBall center σ ⊆ U) (hgap : ρ < σ)
    (hshape : VolterraAnalyticBounds.DerivativeShape (rawCoefficient hR A₁)) :
    ∃ W : VolterraAnalyticBounds.Field,
      IsRegularSolution R (Metric.ball center ρ)
        (rawCoefficient hR A₀) (rawCoefficient hR A₁) (rawField hR f) W := by
  obtain ⟨holo, heq⟩ := integralSolution_spec hR hU hA₀ hA₁ hf hDisk hgap hshape
  exact ⟨liftedField hR A₀ A₁ f (integralSolution hR A₀ A₁ f),
    liftedField_isRegularSolution hR A₀ A₁ f (integralSolution hR A₀ A₁ f)
      Metric.isOpen_ball holo heq⟩

theorem homogeneous_layer_eq {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {V : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hV : DifferentiableOn ℂ V U)
    (heq : ∀ z ∈ U, V z = pathInverse hR VolterraAnalyticBounds.exponent
      (coefficientAction (A₀ z) (V z) + coefficientAction (A₁ z) (deriv V z)))
    (k : ℕ) {z : ℂ} (hz : z ∈ U) :
    layer hR VolterraAnalyticBounds.exponent A₀ A₁ V k z = V z := by
  induction k generalizing z with
  | zero => rw [layer_zero]
  | succ k ih =>
      have hevent : layer hR VolterraAnalyticBounds.exponent A₀ A₁ V k =ᶠ[𝓝 z] V := by
        filter_upwards [hU.mem_nhds hz] with w hw
        exact ih hw
      rw [layer_succ hR _ hU hA₀ hA₁ hV k hz]
      simp only [pathLetter, Bool.false_eq_true, ite_false, ite_true]
      rw [ih hz, hevent.deriv_eq, ← map_add]
      exact (heq z hz).symm

theorem homogeneous_zero_on_closedDisk {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {V : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hV : DifferentiableOn ℂ V U) {center : ℂ} {ρ σ B M : ℝ}
    (hDisk : Metric.closedBall center σ ⊆ U) (hgap : ρ < σ)
    (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hshape : VolterraAnalyticBounds.DerivativeShape (rawCoefficient hR A₁))
    (hbA₀ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₀) R center σ M)
    (hbA₁ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₁) R center σ M)
    (hbV : ∀ z ∈ Metric.closedBall center σ, ‖V z‖ ≤ B)
    (heq : ∀ z ∈ U, V z = pathInverse hR VolterraAnalyticBounds.exponent
      (coefficientAction (A₀ z) (V z) + coefficientAction (A₁ z) (deriv V z)))
    {z : ℂ} (hz : z ∈ Metric.closedBall center ρ) : V z = 0 := by
  have hzU := hDisk (Metric.closedBall_subset_closedBall hgap.le hz)
  have hs := VolterraAnalyticBounds.summable_wordLayers (B := B) (mul_nonneg hM hR)
    (le_trans zero_le_one (le_max_left 1 (σ - ρ)⁻¹))
  have hnorm : ‖V z‖ ≤ 0 := ge_of_tendsto' hs.tendsto_atTop_zero (fun k => by
    have hb := layer_bound hR hU hA₀ hA₁ hV hDisk hgap hB hM hshape hbA₀ hbA₁ hbV k hz
    rwa [homogeneous_layer_eq hR hU hA₀ hA₁ hV heq k hzU] at hb)
  exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))

/-- Local compact bounds and the convergent majorant force every
holomorphic homogeneous zero-axis solution to vanish. -/
theorem homogeneous_solution_zero {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {V : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hV : DifferentiableOn ℂ V U)
    (hshape : VolterraAnalyticBounds.DerivativeShape (rawCoefficient hR A₁))
    (heq : ∀ z ∈ U, V z = pathInverse hR VolterraAnalyticBounds.exponent
      (coefficientAction (A₀ z) (V z) + coefficientAction (A₁ z) (deriv V z))) :
    ∀ z ∈ U, V z = 0 := by
  intro z hz
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  have hDisk : Metric.closedBall z (δ / 2) ⊆ U := fun w hw =>
    hδU (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hw).trans_lt (by linarith)))
  obtain ⟨K₀, hK₀⟩ := (isCompact_closedBall z (δ / 2)).exists_bound_of_continuousOn
    (f := A₀) (hA₀.continuousOn.mono hDisk)
  obtain ⟨K₁, hK₁⟩ := (isCompact_closedBall z (δ / 2)).exists_bound_of_continuousOn
    (f := A₁) (hA₁.continuousOn.mono hDisk)
  obtain ⟨B₀, hB₀⟩ := (isCompact_closedBall z (δ / 2)).exists_bound_of_continuousOn
    (hV.continuousOn.mono hDisk)
  let K := max 0 (max K₀ K₁)
  have hK : 0 ≤ K := le_max_left _ _
  have hbA₀ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₀) R z (δ / 2) (6 * K) :=
    rawCoefficient_bound hR A₀ (fun w hw => (hK₀ w hw).trans
      ((le_max_left K₀ K₁).trans (le_max_right 0 (max K₀ K₁))))
  have hbA₁ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₁) R z (δ / 2) (6 * K) :=
    rawCoefficient_bound hR A₁ (fun w hw => (hK₁ w hw).trans
      ((le_max_right K₀ K₁).trans (le_max_right 0 (max K₀ K₁))))
  exact homogeneous_zero_on_closedDisk hR hU hA₀ hA₁ hV hDisk
    (show δ / 4 < δ / 2 by linarith) (le_max_left 0 B₀)
    (mul_nonneg (by norm_num) hK) hshape hbA₀ hbA₁
    (fun w hw => (hB₀ w hw).trans (le_max_right 0 B₀)) heq
    (Metric.mem_closedBall_self (show 0 ≤ δ / 4 by positivity))

/-- Uniqueness in the holomorphic continuous-path class, with all local
growth bounds derived from compactness. -/
theorem integral_solution_unique {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {f W₀ W₁ : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hW₀ : DifferentiableOn ℂ W₀ U) (hW₁ : DifferentiableOn ℂ W₁ U)
    (hshape : VolterraAnalyticBounds.DerivativeShape (rawCoefficient hR A₁))
    (heq₀ : ∀ z ∈ U, W₀ z = pathInverse hR VolterraAnalyticBounds.exponent (rhsPath A₀ A₁ f W₀ z))
    (heq₁ : ∀ z ∈ U, W₁ z = pathInverse hR VolterraAnalyticBounds.exponent (rhsPath A₀ A₁ f W₁ z)) :
    EqOn W₀ W₁ U := by
  have hd : ∀ z ∈ U, deriv (W₀ - W₁) z = deriv W₀ z - deriv W₁ z := by
    intro z hz
    exact deriv_fun_sub (hW₀.differentiableAt (hU.mem_nhds hz))
      (hW₁.differentiableAt (hU.mem_nhds hz))
  have heq : ∀ z ∈ U, (W₀ - W₁) z = pathInverse hR VolterraAnalyticBounds.exponent
      (coefficientAction (A₀ z) ((W₀ - W₁) z) +
        coefficientAction (A₁ z) (deriv (W₀ - W₁) z)) := by
    intro z hz
    have hs := congrArg₂ (fun u v : Path R => u - v) (heq₀ z hz) (heq₁ z hz)
    rw [← map_sub] at hs
    refine hs.trans ?_
    congr 1
    rw [hd z hz]
    simp only [rhsPath, map_sub, Pi.sub_apply]
    abel
  intro z hz
  have hzero := homogeneous_solution_zero hR hU hA₀ hA₁ (hW₀.sub hW₁) hshape heq z hz
  exact sub_eq_zero.mp hzero

/-- The same canonical series works locally on every disk in an arbitrary
open parameter domain. Consequently its values are holomorphic on that
domain; uniform estimates are taken on smaller compact neighborhoods. -/
theorem integralSolution_spec_open {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {f : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U)
    (hshape : VolterraAnalyticBounds.DerivativeShape (rawCoefficient hR A₁)) :
    DifferentiableOn ℂ (integralSolution hR A₀ A₁ f) U ∧
      ∀ z ∈ U, integralSolution hR A₀ A₁ f z =
        pathInverse hR VolterraAnalyticBounds.exponent
          (rhsPath A₀ A₁ f (integralSolution hR A₀ A₁ f) z) := by
  have hlocal : ∀ z ∈ U,
      DifferentiableAt ℂ (integralSolution hR A₀ A₁ f) z ∧
        integralSolution hR A₀ A₁ f z = pathInverse hR VolterraAnalyticBounds.exponent
          (rhsPath A₀ A₁ f (integralSolution hR A₀ A₁ f) z) := by
    intro z hz
    obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
    have hDisk : Metric.closedBall z (δ / 2) ⊆ U := fun w hw =>
      hδU (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hw).trans_lt (by linarith)))
    have hgap : δ / 4 < δ / 2 := by linarith
    obtain ⟨hholo, heq⟩ := integralSolution_spec hR hU hA₀ hA₁ hf hDisk hgap hshape
    have hz' : z ∈ Metric.ball z (δ / 4) := Metric.mem_ball_self (by positivity)
    exact ⟨hholo.differentiableAt (Metric.isOpen_ball.mem_nhds hz'), heq z hz'⟩
  exact ⟨fun z hz => (hlocal z hz).1.differentiableWithinAt, fun z hz => (hlocal z hz).2⟩

/-- Existence on any finite radial interval and any open parameter
neighborhood carrying the fixed holomorphic input data. -/
theorem exists_regular_solution_open {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {f : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U)
    (hshape : VolterraAnalyticBounds.DerivativeShape (rawCoefficient hR A₁)) :
    ∃ W : VolterraAnalyticBounds.Field,
      IsRegularSolution R U (rawCoefficient hR A₀) (rawCoefficient hR A₁) (rawField hR f) W := by
  obtain ⟨holo, heq⟩ := integralSolution_spec_open hR hU hA₀ hA₁ hf hshape
  exact ⟨liftedField hR A₀ A₁ f (integralSolution hR A₀ A₁ f),
    liftedField_isRegularSolution hR A₀ A₁ f (integralSolution hR A₀ A₁ f) hU holo heq⟩

/-- Zero axis data make the axis derivative depend only on the given forcing. -/
theorem IsRegularSolution.axis_derivative_eq_forcing
    {R : ℝ} {U : Set ℂ} {A₀ A₁ : VolterraAnalyticBounds.Coeff}
    {f W : VolterraAnalyticBounds.Field} (hsol : IsRegularSolution R U A₀ A₁ f W)
    (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) (i : Fin 6) :
    radialDeriv W 0 z i = (1 / ((VolterraAnalyticBounds.exponent i : ℝ) + 1)) • f 0 z i := by
  have hp : VolterraAnalyticBounds.parameterDeriv W 0 z = 0 := by
    funext j
    have he : (fun w => W 0 w j) =ᶠ[𝓝 z] (fun _ : ℂ => (0 : ℂ)) := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact congrFun (hsol.axis_zero w hw) j
    exact he.deriv_eq.trans (deriv_const z 0)
  rw [hsol.axis_derivative z hz i]
  simp only [equationRHS, VolterraAnalyticBounds.matrixAction,
    hsol.axis_zero z hz, hp, Matrix.mulVec_zero, add_zero, Pi.add_apply, Pi.zero_apply]

end NavierStokes.NilpotentVolterra
