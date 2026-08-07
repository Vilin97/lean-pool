/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.FunProp

/-!
# Mixed mass and phase derivatives

The first homological equation differentiates phase derivatives with respect to the mass
parameter.  This file packages the needed Schwarz theorem for a jointly `C²` scalar function.
-/

namespace LeanPool.PoincareThreeBody

/-- The derivative in the distinguished real parameter direction at parameter zero. -/
noncomputable def parameterCoefficient
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (G : ℝ × B → ℝ) (b : B) : ℝ :=
  fderiv ℝ G (0, b) (1, 0)

/-- A jointly `C²` function has a differentiable first parameter coefficient in the remaining
variables. -/
theorem differentiableAt_parameterCoefficient
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {G : ℝ × B → ℝ} {b : B} (hG : ContDiffAt ℝ 2 G (0, b)) :
    DifferentiableAt ℝ (parameterCoefficient G) b := by
  have hfderiv : DifferentiableAt ℝ (fderiv ℝ G) (0, b) := by
    exact (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold parameterCoefficient
  fun_prop

/-- A jointly `C²` function has a continuously differentiable first parameter coefficient. -/
theorem contDiffAt_parameterCoefficient
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {G : ℝ × B → ℝ} {b : B} (hG : ContDiffAt ℝ 2 G (0, b)) :
    ContDiffAt ℝ 1 (parameterCoefficient G) b := by
  have hfderiv : ContDiffAt ℝ 1 (fderiv ℝ G) (0, b) :=
    hG.fderiv_right (m := 1) (by norm_num)
  unfold parameterCoefficient
  fun_prop

/-- The phase derivative of a slice of a jointly differentiable function is its joint derivative
in the pure phase direction. -/
theorem fderiv_curry_right_apply
    {A B C : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    {G : A × B → C} {a : A} {b v : B} (hG : DifferentiableAt ℝ G (a, b)) :
    fderiv ℝ (fun y ↦ G (a, y)) b v = fderiv ℝ G (a, b) (0, v) := by
  have hembedding : HasFDerivAt (fun y : B ↦ (a, y))
      ((0 : B →L[ℝ] A).prod (ContinuousLinearMap.id ℝ B)) b := by
    exact (hasFDerivAt_const (x := b) (c := a)).prodMk (hasFDerivAt_id b)
  have hcomposition := hG.hasFDerivAt.comp b hembedding
  have hderivative := hcomposition.fderiv
  change fderiv ℝ (G ∘ Prod.mk a) b v = fderiv ℝ G (a, b) (0, v)
  rw [hderivative]
  rfl

/-- The mass derivative of a scalar slice is the joint derivative in the pure parameter
direction. -/
theorem deriv_curry_left
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {G : ℝ × B → ℝ} {b : B} (hG : DifferentiableAt ℝ G (0, b)) :
    deriv (fun mass ↦ G (mass, b)) 0 = parameterCoefficient G b := by
  have hembedding := hasFDerivAt_prodMk_left (𝕜 := ℝ) (0 : ℝ) b
  have hcomposition := hG.hasFDerivAt.comp 0 hembedding
  have hderivative := hcomposition.fderiv
  change fderiv ℝ (G ∘ fun mass ↦ (mass, b)) 0 1 = _
  rw [hderivative]
  rfl

/-- Along an affine line, the derivative of a first directional derivative is the corresponding
second directional derivative. -/
theorem hasDerivAt_directionalFDeriv_along_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : E → ℝ} {x v w : E} (hG : ContDiffAt ℝ 2 G x) :
    HasDerivAt
      (fun t : ℝ ↦ iteratedFDeriv ℝ 1 G (x + t • w) (fun _ ↦ v))
      (iteratedFDeriv ℝ 2 G x ![w, v]) 0 := by
  let Q : E → ℝ := fun y ↦ iteratedFDeriv ℝ 1 G y (fun _ ↦ v)
  have hiterated : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 G) x := by
    exact hG.differentiableAt_iteratedFDeriv (m := 1) (by norm_num)
  have hQ : DifferentiableAt ℝ Q x := by
    dsimp only [Q]
    fun_prop
  have hline : HasDerivAt (fun t : ℝ ↦ x + t • w) w 0 := by
    have h := (hasDerivAt_const (x := (0 : ℝ)) x).add
      ((hasDerivAt_id (0 : ℝ)).smul_const w)
    convert h using 1
    · funext t
      rfl
    · simp
  have hcomposition : HasDerivAt (fun t : ℝ ↦ Q (x + t • w))
      (fderiv ℝ Q x w) 0 := by
    have hQbase : DifferentiableAt ℝ Q (x + (0 : ℝ) • w) := by
      simpa using hQ
    change HasDerivAt (Q ∘ fun t : ℝ ↦ x + t • w) (fderiv ℝ Q x w) 0
    have hc := hQbase.hasFDerivAt.comp_hasDerivAt 0 hline
    simpa only [zero_smul, add_zero] using hc
  apply hcomposition.congr_deriv
  have hsucc := hiterated.iteratedFDeriv_succ_apply_left'
    (m := ![w, v])
  simpa [Q] using hsucc.symm

/-- The second derivative of a real `C²` function is symmetric. -/
theorem iteratedFDeriv_two_swap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : E → ℝ} {x v w : E} (hG : ContDiffAt ℝ 2 G x) :
    iteratedFDeriv ℝ 2 G x ![v, w] = iteratedFDeriv ℝ 2 G x ![w, v] := by
  exact (hG.isSymmSndFDerivAt (by simp)).iteratedFDeriv_cons

/-- The directional derivative along a line can equivalently be written with the two directions
swapped. This is the form used to commute mass and phase differentiation. -/
theorem hasDerivAt_directionalFDeriv_along_line_swap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : E → ℝ} {x v w : E} (hG : ContDiffAt ℝ 2 G x) :
    HasDerivAt
      (fun t : ℝ ↦ iteratedFDeriv ℝ 1 G (x + t • w) (fun _ ↦ v))
      (iteratedFDeriv ℝ 2 G x ![v, w]) 0 := by
  apply (hasDerivAt_directionalFDeriv_along_line hG).congr_deriv
  exact iteratedFDeriv_two_swap hG

/-- The phase derivative of the parameter coefficient is the mixed second derivative with phase
first and parameter second. -/
theorem fderiv_parameterCoefficient
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {G : ℝ × B → ℝ} {b v : B} (hG : ContDiffAt ℝ 2 G (0, b)) :
    fderiv ℝ (parameterCoefficient G) b v =
      iteratedFDeriv ℝ 2 G (0, b) ![(0, v), (1, 0)] := by
  have hiterated : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 G) (0, b) :=
    hG.differentiableAt_iteratedFDeriv (m := 1) (by norm_num)
  have hcoefficient : DifferentiableAt ℝ (parameterCoefficient G) b :=
    differentiableAt_parameterCoefficient hG
  have hline : HasDerivAt (fun t : ℝ ↦ b + t • v) v 0 := by
    have h := (hasDerivAt_const (x := (0 : ℝ)) b).add
      ((hasDerivAt_id (0 : ℝ)).smul_const v)
    convert h using 1
    · funext t
      rfl
    · simp
  have hcoefficientLine : HasDerivAt
      (fun t : ℝ ↦ parameterCoefficient G (b + t • v))
      (fderiv ℝ (parameterCoefficient G) b v) 0 := by
    have hbase : DifferentiableAt ℝ (parameterCoefficient G) (b + (0 : ℝ) • v) := by
      simpa using hcoefficient
    change HasDerivAt
      (parameterCoefficient G ∘ fun t : ℝ ↦ b + t • v)
      (fderiv ℝ (parameterCoefficient G) b v) 0
    have hc := hbase.hasFDerivAt.comp_hasDerivAt 0 hline
    simpa only [zero_smul, add_zero] using hc
  have hmixed := hasDerivAt_directionalFDeriv_along_line
    (G := G) (x := (0, b)) (v := (1, 0)) (w := (0, v)) hG
  have hmixedCoefficient : HasDerivAt
      (fun t : ℝ ↦ parameterCoefficient G (b + t • v))
      (iteratedFDeriv ℝ 2 G (0, b) ![(0, v), (1, 0)]) 0 := by
    apply hmixed.congr_of_eventuallyEq
    filter_upwards [] with t
    simp [parameterCoefficient]
  exact hcoefficientLine.unique hmixedCoefficient

/-- Joint `C²` regularity commutes the parameter derivative with every phase derivative. -/
theorem hasDerivAt_fderiv_curry_right
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {G : ℝ × B → ℝ} {b v : B} (hG : ContDiffAt ℝ 2 G (0, b)) :
    HasDerivAt (fun mass ↦ fderiv ℝ (fun y ↦ G (mass, y)) b v)
      (fderiv ℝ (parameterCoefficient G) b v) 0 := by
  have hmixed := hasDerivAt_directionalFDeriv_along_line_swap
    (G := G) (x := (0, b)) (v := (0, v)) (w := (1, 0)) hG
  have htarget : iteratedFDeriv ℝ 2 G (0, b) ![(0, v), (1, 0)] =
      fderiv ℝ (parameterCoefficient G) b v :=
    (fderiv_parameterCoefficient hG).symm
  apply (hmixed.congr_deriv htarget).congr_of_eventuallyEq
  have hjoint : ∀ᶠ mass in nhds (0 : ℝ), ContDiffAt ℝ 2 G (mass, b) := by
    exact (continuousAt_id.prodMk continuousAt_const).eventually (hG.eventually (by simp))
  filter_upwards [hjoint] with mass hmass
  rw [fderiv_curry_right_apply (hmass.differentiableAt (by norm_num))]
  simp

end LeanPool.PoincareThreeBody
