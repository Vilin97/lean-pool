/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteParabolicScaling
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteCylinderCauchyOperator

/-!
# Coordinate operators under affine parabolic scaling

The pullback `v = u ∘ Φ_r` transforms

`∂ₜu - A D²u - B Du - C u = f`

into

`∂ₜv - (A ∘ Φ_r) D²v - r (B ∘ Φ_r) Dv
       - r² (C ∘ Φ_r) v = r² (f ∘ Φ_r)`.

This file states that identity for the genuine finite-cylinder Banach
operators.  It is the exact algebraic reason the lower-order tensor-heat
coefficients become small after localization and parabolic normalization.
-/

@[expose] public noncomputable section
open Set

namespace RicciFlow
namespace AnalyticPDE

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

@[reducible] local instance scalingOperatorFirstNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance scalingOperatorFirstNormedSpace :
    NormedSpace ℝ (X →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance scalingOperatorSecondNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] X →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance scalingOperatorSecondNormedSpace :
    NormedSpace ℝ (X →L[ℝ] X →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance scalingOperatorPrincipalNormedAddCommGroup :
    NormedAddCommGroup ((X →L[ℝ] X →L[ℝ] E) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance scalingOperatorPrincipalNormedSpace :
    NormedSpace ℝ ((X →L[ℝ] X →L[ℝ] E) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance scalingOperatorFirstCoeffNormedAddCommGroup :
    NormedAddCommGroup ((X →L[ℝ] E) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance scalingOperatorFirstCoeffNormedSpace :
    NormedSpace ℝ ((X →L[ℝ] E) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace

namespace FiniteParabolicC2AlphaBanach

variable {α S : ℝ}

/-- Principal coefficient on normalized coordinates. -/
def finiteAffineScaledPrincipalCoefficient
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (A : PrincipalCoefficientSpace
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α)) :
    PrincipalCoefficientSpace
      (X := X) (E := E) (t₀ := a.1) (T := a.1 + S) (α := α) :=
  ParabolicC0AlphaSpace.finiteAffinePullbackL hα c a r hr A

/-- First-order coefficient on normalized coordinates; the chain rule
supplies one factor of `r`. -/
def finiteAffineScaledFirstCoefficient
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (B : FirstCoefficientSpace
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α)) :
    FirstCoefficientSpace
      (X := X) (E := E) (t₀ := a.1) (T := a.1 + S) (α := α) :=
  r • ParabolicC0AlphaSpace.finiteAffinePullbackL hα c a r hr B

/-- Zeroth-order coefficient on normalized coordinates; the chain rule
supplies two factors of `r`. -/
def finiteAffineScaledZeroCoefficient
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (C : ZeroCoefficientSpace
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α)) :
    ZeroCoefficientSpace
      (X := X) (E := E) (t₀ := a.1) (T := a.1 + S) (α := α) :=
  r ^ 2 • ParabolicC0AlphaSpace.finiteAffinePullbackL hα c a r hr C

@[simp] theorem toFun_finiteAffineScaledPrincipalCoefficient
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (A : PrincipalCoefficientSpace
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α))
    (z : ℝ × X) :
    ParabolicC0AlphaSpace.toFun
        (finiteAffineScaledPrincipalCoefficient hα c a r hr A) z =
      ParabolicC0AlphaSpace.toFun A (finiteParabolicAffineMap c a r z) := by
  rfl

@[simp] theorem toFun_finiteAffineScaledFirstCoefficient
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (B : FirstCoefficientSpace
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α))
    (z : ℝ × X) :
    ParabolicC0AlphaSpace.toFun
        (finiteAffineScaledFirstCoefficient hα c a r hr B) z =
      r • ParabolicC0AlphaSpace.toFun B
        (finiteParabolicAffineMap c a r z) := by
  rfl

@[simp] theorem toFun_finiteAffineScaledZeroCoefficient
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (C : ZeroCoefficientSpace
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α))
    (z : ℝ × X) :
    ParabolicC0AlphaSpace.toFun
        (finiteAffineScaledZeroCoefficient hα c a r hr C) z =
      r ^ 2 • ParabolicC0AlphaSpace.toFun C
        (finiteParabolicAffineMap c a r z) := by
  rfl

/-- Quantitative principal-coefficient pullback bound. -/
theorem norm_finiteAffineScaledPrincipalCoefficient_le
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (A : PrincipalCoefficientSpace
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α)) :
    ‖finiteAffineScaledPrincipalCoefficient hα c a r hr A‖ ≤
      max 1 (|r| ^ α) * ‖A‖ := by
  exact (ParabolicC0AlphaSpace.finiteAffinePullbackL
      (E := ((X →L[ℝ] X →L[ℝ] E) →L[ℝ] E))
      (S := S) hα c a r hr).le_opNorm A |>.trans
    (mul_le_mul_of_nonneg_right
      (ParabolicC0AlphaSpace.norm_finiteAffinePullbackL_le
        (E := ((X →L[ℝ] X →L[ℝ] E) →L[ℝ] E))
        (S := S) hα c a r hr) (norm_nonneg A))

/-- The oscillation from any comparison principal field obeys the same
pullback bound. -/
theorem norm_finiteAffineScaledPrincipalCoefficient_sub_le
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (A A₀ : PrincipalCoefficientSpace
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α)) :
    ‖finiteAffineScaledPrincipalCoefficient hα c a r hr A -
        finiteAffineScaledPrincipalCoefficient hα c a r hr A₀‖ ≤
      max 1 (|r| ^ α) * ‖A - A₀‖ := by
  change ‖(ParabolicC0AlphaSpace.finiteAffinePullbackL
      (E := ((X →L[ℝ] X →L[ℝ] E) →L[ℝ] E))
      (S := S) hα c a r hr) A -
      (ParabolicC0AlphaSpace.finiteAffinePullbackL
      (E := ((X →L[ℝ] X →L[ℝ] E) →L[ℝ] E))
      (S := S) hα c a r hr) A₀‖ ≤ _
  rw [← map_sub]
  exact norm_finiteAffineScaledPrincipalCoefficient_le hα c a r hr (A - A₀)

/-- The normalized first coefficient has the explicit factor `|r|`. -/
theorem norm_finiteAffineScaledFirstCoefficient_le
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (B : FirstCoefficientSpace
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α)) :
    ‖finiteAffineScaledFirstCoefficient hα c a r hr B‖ ≤
      |r| * max 1 (|r| ^ α) * ‖B‖ := by
  rw [finiteAffineScaledFirstCoefficient, norm_smul, Real.norm_eq_abs]
  calc
    |r| * ‖ParabolicC0AlphaSpace.finiteAffinePullbackL hα c a r hr B‖
        ≤ |r| * (max 1 (|r| ^ α) * ‖B‖) := by
          gcongr
          exact (ParabolicC0AlphaSpace.finiteAffinePullbackL
            (E := ((X →L[ℝ] E) →L[ℝ] E)) (S := S) hα c a r hr).le_opNorm B |>.trans
            (mul_le_mul_of_nonneg_right
              (ParabolicC0AlphaSpace.norm_finiteAffinePullbackL_le
                (E := ((X →L[ℝ] E) →L[ℝ] E)) (S := S) hα c a r hr)
              (norm_nonneg B))
    _ = |r| * max 1 (|r| ^ α) * ‖B‖ := by ring

/-- The normalized zeroth coefficient has the explicit factor `|r|²`. -/
theorem norm_finiteAffineScaledZeroCoefficient_le
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (C : ZeroCoefficientSpace
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α)) :
    ‖finiteAffineScaledZeroCoefficient hα c a r hr C‖ ≤
      r ^ 2 * max 1 (|r| ^ α) * ‖C‖ := by
  rw [finiteAffineScaledZeroCoefficient, norm_smul, Real.norm_eq_abs, abs_sq]
  calc
    r ^ 2 * ‖ParabolicC0AlphaSpace.finiteAffinePullbackL hα c a r hr C‖
        ≤ r ^ 2 * (max 1 (|r| ^ α) * ‖C‖) := by
          gcongr
          exact (ParabolicC0AlphaSpace.finiteAffinePullbackL
            (E := E →L[ℝ] E) (S := S) hα c a r hr).le_opNorm C |>.trans
            (mul_le_mul_of_nonneg_right
              (ParabolicC0AlphaSpace.norm_finiteAffinePullbackL_le
                (E := E →L[ℝ] E) (S := S) hα c a r hr)
              (norm_nonneg C))
    _ = r ^ 2 * max 1 (|r| ^ α) * ‖C‖ := by ring

/-- Pullback and multiply a source by the parabolic time weight `r²`. -/
def finiteAffineScaledSourcePullbackL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0) :
    ParabolicC0AlphaBanach X E α
        (parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S)) →L[ℝ]
      ParabolicC0AlphaBanach X E α
        (parabolicFiniteCylinder X a.1 (a.1 + S)) :=
  (ParabolicC0AlphaBanach.compL
      (finiteAffineTimeDerivativeL (E := E) r)).comp
    (ParabolicC0AlphaBanach.finiteAffinePullbackL hα c a r hr)

@[simp] theorem evalCLM_finiteAffineScaledSourcePullbackL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (f : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S)))
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X a.1 (a.1 + S)) :
    ParabolicC0AlphaBanach.evalCLM z hz
        (finiteAffineScaledSourcePullbackL hα c a r hr f) =
      r ^ 2 • ParabolicC0AlphaBanach.evalCLM
        (finiteParabolicAffineMap c a r z)
        (finiteParabolicAffineMap_mapsTo c a hr hz) f := by
  rw [finiteAffineScaledSourcePullbackL, ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_compL_apply,
    finiteAffineTimeDerivativeL_apply,
    ParabolicC0AlphaBanach.evalCLM_finiteAffinePullbackL]

/-- Push a normalized source back to the physical cylinder and remove the
parabolic time weight.  This is the inverse of scaled source pullback. -/
def finiteAffineScaledSourcePushforwardL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0) :
    ParabolicC0AlphaBanach X E α
        (parabolicFiniteCylinder X a.1 (a.1 + S)) →L[ℝ]
      ParabolicC0AlphaBanach X E α
        (parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S)) :=
  (ParabolicC0AlphaBanach.compL
      (finiteAffineTimeDerivativeL (E := E) r⁻¹)).comp
    (ParabolicC0AlphaBanach.finiteAffinePushforwardL hα c a r hr)

@[simp] theorem evalCLM_finiteAffineScaledSourcePushforwardL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (f : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X a.1 (a.1 + S)))
    (z : ℝ × X)
    (hz : z ∈ parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S)) :
    ParabolicC0AlphaBanach.evalCLM z hz
        (finiteAffineScaledSourcePushforwardL hα c a r hr f) =
      r⁻¹ ^ 2 • ParabolicC0AlphaBanach.evalCLM
        (finiteParabolicAffineInvMap c a r z)
        (finiteParabolicAffineInvMap_mapsTo c a hr hz) f := by
  rw [finiteAffineScaledSourcePushforwardL, ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_compL_apply,
    finiteAffineTimeDerivativeL_apply,
    ParabolicC0AlphaBanach.evalCLM_finiteAffinePushforwardL]

/-- Scaled source pullback after scaled pushforward is the identity. -/
@[simp] theorem finiteAffineScaledSourcePullbackL_pushforwardL_apply
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (f : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X a.1 (a.1 + S))) :
    finiteAffineScaledSourcePullbackL hα c a r hr
        (finiteAffineScaledSourcePushforwardL hα c a r hr f) = f := by
  apply (ParabolicC0AlphaBanach.eq_iff_forall_evalCLM _ _).2
  intro z hz
  rw [evalCLM_finiteAffineScaledSourcePullbackL,
    evalCLM_finiteAffineScaledSourcePushforwardL,
    ParabolicC0AlphaBanach.evalCLM_eq_representative,
    ParabolicC0AlphaBanach.evalCLM_eq_representative,
    finiteParabolicAffineInvMap_leftInverse c a hr z, smul_smul]
  have hscale : r ^ 2 * r⁻¹ ^ 2 = 1 := by
    field_simp
  rw [hscale, one_smul]

/-- Scaled source pushforward after scaled pullback is the identity. -/
@[simp] theorem finiteAffineScaledSourcePushforwardL_pullbackL_apply
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (f : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S))) :
    finiteAffineScaledSourcePushforwardL hα c a r hr
        (finiteAffineScaledSourcePullbackL hα c a r hr f) = f := by
  apply (ParabolicC0AlphaBanach.eq_iff_forall_evalCLM _ _).2
  intro z hz
  rw [evalCLM_finiteAffineScaledSourcePushforwardL,
    evalCLM_finiteAffineScaledSourcePullbackL,
    ParabolicC0AlphaBanach.evalCLM_eq_representative,
    ParabolicC0AlphaBanach.evalCLM_eq_representative,
    finiteParabolicAffineInvMap_rightInverse c a hr z, smul_smul]
  have hscale : r⁻¹ ^ 2 * r ^ 2 = 1 := by
    field_simp
  rw [hscale, one_smul]

@[simp] theorem finiteAffineScaledSourcePullbackL_comp_pushforwardL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0) :
    (finiteAffineScaledSourcePullbackL
      (E := E) (S := S) hα c a r hr).comp
        (finiteAffineScaledSourcePushforwardL hα c a r hr) =
      ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro f
  exact finiteAffineScaledSourcePullbackL_pushforwardL_apply hα c a r hr f

@[simp] theorem finiteAffineScaledSourcePushforwardL_comp_pullbackL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0) :
    (finiteAffineScaledSourcePushforwardL
      (E := E) (S := S) hα c a r hr).comp
        (finiteAffineScaledSourcePullbackL hα c a r hr) =
      ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro f
  exact finiteAffineScaledSourcePushforwardL_pullbackL_apply hα c a r hr f

/-- Pointwise coordinate-operator conjugacy under affine parabolic
scaling. -/
theorem evalCLM_coordinateCauchyL_finiteAffinePullbackL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (A : PrincipalCoefficientSpace
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α))
    (B : FirstCoefficientSpace
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α))
    (C : ZeroCoefficientSpace
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α))
    (u : FiniteParabolicC2AlphaBanach X E c.1 (c.1 + r ^ 2 * S) α)
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X a.1 (a.1 + S)) :
    ParabolicC0AlphaBanach.evalCLM z hz
        (coordinateCauchyL
          (finiteAffineScaledPrincipalCoefficient hα c a r hr A)
          (finiteAffineScaledFirstCoefficient hα c a r hr B)
          (finiteAffineScaledZeroCoefficient hα c a r hr C)
          (finiteAffinePullbackL hα c a r hr u)) =
      r ^ 2 • ParabolicC0AlphaBanach.evalCLM
        (finiteParabolicAffineMap c a r z)
        (finiteParabolicAffineMap_mapsTo c a hr hz)
        (coordinateCauchyL A B C u) := by
  rw [evalCLM_coordinateCauchyL, evalCLM_coordinateCauchyL,
    timeDeriv_finiteAffinePullbackL, spaceSecondDeriv_finiteAffinePullbackL,
    spaceDeriv_finiteAffinePullbackL, value_finiteAffinePullbackL]
  have hD1 : finiteAffineFirstDerivativeL r
      (spaceDeriv u (finiteParabolicAffineMap c a r z)) =
        r • spaceDeriv u (finiteParabolicAffineMap c a r z) := by
    ext v
    exact finiteAffineFirstDerivativeL_apply r _ v
  have hD2 : finiteAffineSecondDerivativeL r
      (spaceSecondDeriv u (finiteParabolicAffineMap c a r z)) =
        r ^ 2 • spaceSecondDeriv u (finiteParabolicAffineMap c a r z) := by
    ext v w
    exact finiteAffineSecondDerivativeL_apply r _ v w
  rw [hD1, hD2]
  simp only [toFun_finiteAffineScaledPrincipalCoefficient,
    toFun_finiteAffineScaledFirstCoefficient,
    toFun_finiteAffineScaledZeroCoefficient, map_smul,
    ContinuousLinearMap.smul_apply, smul_smul]
  module
  all_goals assumption

/-- Operator-level conjugacy.  Pulling back the solution and applying the
scaled operator is exactly the same as applying the original operator and
then pulling back the source with weight `r²`. -/
theorem coordinateCauchyL_comp_finiteAffinePullbackL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (A : PrincipalCoefficientSpace
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α))
    (B : FirstCoefficientSpace
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α))
    (C : ZeroCoefficientSpace
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α)) :
    (coordinateCauchyL
      (finiteAffineScaledPrincipalCoefficient hα c a r hr A)
      (finiteAffineScaledFirstCoefficient hα c a r hr B)
      (finiteAffineScaledZeroCoefficient hα c a r hr C)).comp
        (finiteAffinePullbackL hα c a r hr) =
      (finiteAffineScaledSourcePullbackL hα c a r hr).comp
        (coordinateCauchyL A B C) := by
  ext u
  apply (ParabolicC0AlphaBanach.eq_iff_forall_evalCLM _ _).2
  intro z hz
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    evalCLM_coordinateCauchyL_finiteAffinePullbackL,
    evalCLM_finiteAffineScaledSourcePullbackL]

/-- The inverse form of coordinate-operator conjugacy.  Applying the physical
operator after pushing a normalized four-jet forward is the same as applying
the normalized operator and then undoing the scaled source pullback. -/
theorem coordinateCauchyL_comp_finiteAffinePushforwardL
    (hα : 0 < α) (hS : 0 < S) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (A : PrincipalCoefficientSpace
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α))
    (B : FirstCoefficientSpace
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α))
    (C : ZeroCoefficientSpace
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α)) :
    (coordinateCauchyL A B C).comp
        (finiteAffinePushforwardL hα.le c a r hr) =
      (finiteAffineScaledSourcePushforwardL hα.le c a r hr).comp
        (coordinateCauchyL
          (finiteAffineScaledPrincipalCoefficient hα.le c a r hr A)
          (finiteAffineScaledFirstCoefficient hα.le c a r hr B)
          (finiteAffineScaledZeroCoefficient hα.le c a r hr C)) := by
  let sourcePullback := finiteAffineScaledSourcePullbackL
    (E := E) (S := S) hα.le c a r hr
  let sourcePushforward := finiteAffineScaledSourcePushforwardL
    (E := E) (S := S) hα.le c a r hr
  have hinj : Function.Injective sourcePullback := by
    intro f g hfg
    have h := congrArg sourcePushforward hfg
    simpa [sourcePullback, sourcePushforward] using h
  apply ContinuousLinearMap.ext
  intro u
  apply hinj
  change
    sourcePullback
        ((coordinateCauchyL A B C)
          (finiteAffinePushforwardL hα.le c a r hr u)) =
      sourcePullback
        (sourcePushforward
          ((coordinateCauchyL
            (finiteAffineScaledPrincipalCoefficient hα.le c a r hr A)
            (finiteAffineScaledFirstCoefficient hα.le c a r hr B)
            (finiteAffineScaledZeroCoefficient hα.le c a r hr C)) u))
  have hconj := coordinateCauchyL_comp_finiteAffinePullbackL
    hα.le c a r hr A B C
  have hleft := DFunLike.congr_fun hconj
    (finiteAffinePushforwardL hα.le c a r hr u)
  change
    (coordinateCauchyL
      (finiteAffineScaledPrincipalCoefficient hα.le c a r hr A)
      (finiteAffineScaledFirstCoefficient hα.le c a r hr B)
      (finiteAffineScaledZeroCoefficient hα.le c a r hr C))
        (finiteAffinePullbackL hα.le c a r hr
          (finiteAffinePushforwardL hα.le c a r hr u)) =
      sourcePullback
        ((coordinateCauchyL A B C)
          (finiteAffinePushforwardL hα.le c a r hr u)) at hleft
  rw [finiteAffinePullbackL_pushforwardL_apply hα hS c a r hr u] at hleft
  rw [← hleft]
  exact (finiteAffineScaledSourcePullbackL_pushforwardL_apply
    hα.le c a r hr
      ((coordinateCauchyL
        (finiteAffineScaledPrincipalCoefficient hα.le c a r hr A)
        (finiteAffineScaledFirstCoefficient hα.le c a r hr B)
        (finiteAffineScaledZeroCoefficient hα.le c a r hr C)) u)).symm

/-- Transport any normalized right-inverse candidate to the physical
cylinder by scaling the source, solving in normalized coordinates, and
pushing the four-jet back. -/
def finiteAffineTransportedRightInverseL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (R : ParabolicC0AlphaBanach X E α
          (parabolicFiniteCylinder X a.1 (a.1 + S)) →L[ℝ]
        FiniteParabolicC2AlphaBanach X E a.1 (a.1 + S) α) :
    ParabolicC0AlphaBanach X E α
        (parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S)) →L[ℝ]
      FiniteParabolicC2AlphaBanach X E c.1 (c.1 + r ^ 2 * S) α :=
  (finiteAffinePushforwardL hα c a r hr).comp
    (R.comp (finiteAffineScaledSourcePullbackL hα c a r hr))

/-- A normalized exact right inverse transports to an exact right inverse of
the physical coordinate operator. -/
theorem coordinateCauchyL_comp_finiteAffineTransportedRightInverseL
    (hα : 0 < α) (hS : 0 < S) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (A : PrincipalCoefficientSpace
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α))
    (B : FirstCoefficientSpace
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α))
    (C : ZeroCoefficientSpace
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α))
    (R : ParabolicC0AlphaBanach X E α
          (parabolicFiniteCylinder X a.1 (a.1 + S)) →L[ℝ]
        FiniteParabolicC2AlphaBanach X E a.1 (a.1 + S) α)
    (hR : (coordinateCauchyL
      (finiteAffineScaledPrincipalCoefficient hα.le c a r hr A)
      (finiteAffineScaledFirstCoefficient hα.le c a r hr B)
      (finiteAffineScaledZeroCoefficient hα.le c a r hr C)).comp R =
        ContinuousLinearMap.id ℝ
          (ParabolicC0AlphaBanach X E α
            (parabolicFiniteCylinder X a.1 (a.1 + S)))) :
    (coordinateCauchyL A B C).comp
        (finiteAffineTransportedRightInverseL hα.le c a r hr R) =
      ContinuousLinearMap.id ℝ _ := by
  have hpush := coordinateCauchyL_comp_finiteAffinePushforwardL
    hα hS c a r hr A B C
  apply ContinuousLinearMap.ext
  intro f
  have hpushApply := DFunLike.congr_fun hpush
    (R (finiteAffineScaledSourcePullbackL hα.le c a r hr f))
  have hpushPoint :
      (coordinateCauchyL A B C)
          (finiteAffinePushforwardL hα.le c a r hr
            (R (finiteAffineScaledSourcePullbackL hα.le c a r hr f))) =
        finiteAffineScaledSourcePushforwardL hα.le c a r hr
          ((coordinateCauchyL
            (finiteAffineScaledPrincipalCoefficient hα.le c a r hr A)
            (finiteAffineScaledFirstCoefficient hα.le c a r hr B)
            (finiteAffineScaledZeroCoefficient hα.le c a r hr C))
              (R (finiteAffineScaledSourcePullbackL hα.le c a r hr f))) := by
    simpa only [ContinuousLinearMap.comp_apply] using hpushApply
  have hRApply := DFunLike.congr_fun hR
    (finiteAffineScaledSourcePullbackL hα.le c a r hr f)
  change
    (coordinateCauchyL A B C)
      (finiteAffinePushforwardL hα.le c a r hr
        (R (finiteAffineScaledSourcePullbackL hα.le c a r hr f))) = f
  rw [hpushPoint]
  change finiteAffineScaledSourcePushforwardL hα.le c a r hr
      ((coordinateCauchyL
        (finiteAffineScaledPrincipalCoefficient hα.le c a r hr A)
        (finiteAffineScaledFirstCoefficient hα.le c a r hr B)
        (finiteAffineScaledZeroCoefficient hα.le c a r hr C))
          (R (finiteAffineScaledSourcePullbackL hα.le c a r hr f))) = f
  rw [show
      (coordinateCauchyL
        (finiteAffineScaledPrincipalCoefficient hα.le c a r hr A)
        (finiteAffineScaledFirstCoefficient hα.le c a r hr B)
        (finiteAffineScaledZeroCoefficient hα.le c a r hr C))
          (R (finiteAffineScaledSourcePullbackL hα.le c a r hr f)) =
        finiteAffineScaledSourcePullbackL hα.le c a r hr f by
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
        using hRApply]
  exact finiteAffineScaledSourcePushforwardL_pullbackL_apply
    hα.le c a r hr f

/-- Norm bound for the transported right inverse, exposing the three exact
operator factors used by the local Schauder estimate. -/
theorem norm_finiteAffineTransportedRightInverseL_le
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (R : ParabolicC0AlphaBanach X E α
          (parabolicFiniteCylinder X a.1 (a.1 + S)) →L[ℝ]
        FiniteParabolicC2AlphaBanach X E a.1 (a.1 + S) α) :
    ‖finiteAffineTransportedRightInverseL hα c a r hr R‖ ≤
      ‖finiteAffinePushforwardL (E := E) (S := S) hα c a r hr‖ *
        (‖R‖ * ‖finiteAffineScaledSourcePullbackL
          (E := E) (S := S) hα c a r hr‖) := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))

end FiniteParabolicC2AlphaBanach

end AnalyticPDE
end RicciFlow
