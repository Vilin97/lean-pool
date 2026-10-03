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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.SpatialLinearChange

/-!
# Affine parabolic scaling on finite-cylinder Banach spaces

This file packages the genuine parabolic change of variables

`(t,x) ↦ c + (r² (t-aₜ), r (x-aₓ))`

as bounded pullback operators on the finite-cylinder `C^{0,α}` and
`C^{2+α,1+α/2}` Banach spaces.  The four-jet pullback carries the exact
chain-rule weights: `r` on the first spatial derivative and `r²` on both
the second spatial derivative and the time derivative.
-/

@[expose] public noncomputable section
open Filter Set
open scoped Topology

namespace RicciFlow
namespace AnalyticPDE

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

@[reducible] local instance parabolicScalingFirstNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance parabolicScalingFirstNormedSpace :
    NormedSpace ℝ (X →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance parabolicScalingSecondNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] X →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance parabolicScalingSecondNormedSpace :
    NormedSpace ℝ (X →L[ℝ] X →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

/-- The affine parabolic chart from source center `a` to target center
`c`, with parabolic scale `r`. -/
def finiteParabolicAffineMap (c a : ℝ × X) (r : ℝ) : ℝ × X → ℝ × X :=
  fun z => c + (r ^ 2 * (z.1 - a.1), r • (z.2 - a.2))

/-- The inverse affine chart, written without any endpoint casts. -/
def finiteParabolicAffineInvMap (c a : ℝ × X) (r : ℝ) : ℝ × X → ℝ × X :=
  finiteParabolicAffineMap a c r⁻¹

theorem finiteParabolicAffineInvMap_leftInverse
    (c a : ℝ × X) {r : ℝ} (hr : r ≠ 0) :
    Function.LeftInverse (finiteParabolicAffineInvMap c a r)
      (finiteParabolicAffineMap c a r) :=
  affineChart_leftInverse c a hr

theorem finiteParabolicAffineInvMap_rightInverse
    (c a : ℝ × X) {r : ℝ} (hr : r ≠ 0) :
    Function.RightInverse (finiteParabolicAffineInvMap c a r)
      (finiteParabolicAffineMap c a r) :=
  affineChart_rightInverse c a hr

theorem inv_sq_mul_sq_mul (r S : ℝ) (hr : r ≠ 0) :
    r⁻¹ ^ 2 * (r ^ 2 * S) = S := by
  field_simp

@[simp] theorem finiteParabolicAffineMap_fst
    (c a : ℝ × X) (r : ℝ) (z : ℝ × X) :
    (finiteParabolicAffineMap c a r z).1 = c.1 + r ^ 2 * (z.1 - a.1) := rfl

@[simp] theorem finiteParabolicAffineMap_snd
    (c a : ℝ × X) (r : ℝ) (z : ℝ × X) :
    (finiteParabolicAffineMap c a r z).2 = c.2 + r • (z.2 - a.2) := rfl

/-- Exact distortion of parabolic distance by the affine chart. -/
theorem parabolicDistance_finiteParabolicAffineMap
    (c a : ℝ × X) (r : ℝ) (p q : ℝ × X) :
    parabolicDistance (finiteParabolicAffineMap c a r p)
        (finiteParabolicAffineMap c a r q) =
      |r| * parabolicDistance p q :=
  parabolicDistance_affineChart c a r p q

/-- A nondegenerate affine parabolic chart sends a finite cylinder of
thickness `S` to the finite cylinder of thickness `r² S`. -/
theorem finiteParabolicAffineMap_mapsTo
    (c a : ℝ × X) {r S : ℝ} (hr : r ≠ 0) :
    MapsTo (finiteParabolicAffineMap c a r)
      (parabolicFiniteCylinder X a.1 (a.1 + S))
      (parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S)) := by
  intro z hz
  rw [mem_parabolicFiniteCylinder] at hz ⊢
  simp only [finiteParabolicAffineMap_fst]
  have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  constructor <;> nlinarith

/-- The inverse affine chart sends the scaled finite cylinder back to the
unscaled one, with no endpoint casts in its statement. -/
theorem finiteParabolicAffineInvMap_mapsTo
    (c a : ℝ × X) {r S : ℝ} (hr : r ≠ 0) :
    MapsTo (finiteParabolicAffineInvMap c a r)
      (parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S))
      (parabolicFiniteCylinder X a.1 (a.1 + S)) := by
  intro z hz
  change finiteParabolicAffineMap a c r⁻¹ z ∈
    parabolicFiniteCylinder X a.1 (a.1 + S)
  have h := finiteParabolicAffineMap_mapsTo
    (X := X) a c (S := r ^ 2 * S) (inv_ne_zero hr) hz
  rw [inv_sq_mul_sq_mul r S hr] at h
  exact h

/-- Exact parabolic-distance distortion by the inverse affine chart. -/
theorem parabolicDistance_finiteParabolicAffineInvMap
    (c a : ℝ × X) (r : ℝ) (p q : ℝ × X) :
    parabolicDistance (finiteParabolicAffineInvMap c a r p)
        (finiteParabolicAffineInvMap c a r q) =
      |r⁻¹| * parabolicDistance p q :=
  parabolicDistance_finiteParabolicAffineMap a c r⁻¹ p q

/-- Pullback of a finite-cylinder `C^{0,α}` carrier representative by an
affine parabolic scaling.  This carrier-level version is used for operator
coefficients, whose pointwise representatives must remain available. -/
def ParabolicC0AlphaSpace.finiteAffinePullbackL
    {α S : ℝ} (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0) :
    ParabolicC0AlphaSpace X E α
        (parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S)) →L[ℝ]
      ParabolicC0AlphaSpace X E α
        (parabolicFiniteCylinder X a.1 (a.1 + S)) :=
  ParabolicC0AlphaSpace.precompL hα (abs_nonneg r)
    (finiteParabolicAffineMap_mapsTo c a hr)
    (fun p _hp q _hq =>
      (parabolicDistance_finiteParabolicAffineMap c a r p q).le)

/-- Operator norm of affine pullback on the Hölder carrier. -/
theorem ParabolicC0AlphaSpace.norm_finiteAffinePullbackL_le
    {α S : ℝ} (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0) :
    ‖ParabolicC0AlphaSpace.finiteAffinePullbackL
        (E := E) (S := S) hα c a r hr‖ ≤ max 1 (|r| ^ α) :=
  ParabolicC0AlphaSpace.norm_precompL_le hα (abs_nonneg r)
    (finiteParabolicAffineMap_mapsTo c a hr)
    (fun p _hp q _hq =>
      (parabolicDistance_finiteParabolicAffineMap c a r p q).le)

@[simp] theorem ParabolicC0AlphaSpace.toFun_finiteAffinePullbackL
    {α S : ℝ} (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (u : ParabolicC0AlphaSpace X E α
      (parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S))) :
    ParabolicC0AlphaSpace.toFun
        (ParabolicC0AlphaSpace.finiteAffinePullbackL hα c a r hr u) =
      fun z => ParabolicC0AlphaSpace.toFun u
        (finiteParabolicAffineMap c a r z) := by
  rfl

/-- Pullback of finite-cylinder `C^{0,α}` data by an affine parabolic
scaling. -/
def ParabolicC0AlphaBanach.finiteAffinePullbackL
    {α S : ℝ} (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0) :
    ParabolicC0AlphaBanach X E α
        (parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S)) →L[ℝ]
      ParabolicC0AlphaBanach X E α
        (parabolicFiniteCylinder X a.1 (a.1 + S)) :=
  ParabolicC0AlphaBanach.precompL hα (abs_nonneg r)
    (finiteParabolicAffineMap_mapsTo c a hr)
    (fun p _hp q _hq =>
      (parabolicDistance_finiteParabolicAffineMap c a r p q).le)

/-- Operator norm of affine pullback on the separated Hölder Banach space. -/
theorem ParabolicC0AlphaBanach.norm_finiteAffinePullbackL_le
    {α S : ℝ} (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0) :
    ‖ParabolicC0AlphaBanach.finiteAffinePullbackL
        (E := E) (S := S) hα c a r hr‖ ≤ max 1 (|r| ^ α) :=
  ParabolicC0AlphaBanach.norm_precompL_le hα (abs_nonneg r)
    (finiteParabolicAffineMap_mapsTo c a hr)
    (fun p _hp q _hq =>
      (parabolicDistance_finiteParabolicAffineMap c a r p q).le)

/-- Pushforward from normalized coordinates back to the original finite
cylinder.  It is the affine pullback for the inverse chart, with the
endpoint equality `r⁻²(r²S)=S` discharged internally. -/
def ParabolicC0AlphaBanach.finiteAffinePushforwardL
    {α S : ℝ} (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0) :
    ParabolicC0AlphaBanach X E α
        (parabolicFiniteCylinder X a.1 (a.1 + S)) →L[ℝ]
      ParabolicC0AlphaBanach X E α
        (parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S)) :=
  ParabolicC0AlphaBanach.precompL hα (abs_nonneg r⁻¹)
    (finiteParabolicAffineInvMap_mapsTo c a hr)
    (fun p _hp q _hq =>
      (parabolicDistance_finiteParabolicAffineInvMap c a r p q).le)

@[simp] theorem ParabolicC0AlphaBanach.evalCLM_finiteAffinePullbackL
    {α S : ℝ} (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (u : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S)))
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X a.1 (a.1 + S)) :
    ParabolicC0AlphaBanach.evalCLM z hz
        (ParabolicC0AlphaBanach.finiteAffinePullbackL hα c a r hr u) =
      ParabolicC0AlphaBanach.evalCLM (finiteParabolicAffineMap c a r z)
        (finiteParabolicAffineMap_mapsTo c a hr hz) u := by
  exact ParabolicC0AlphaBanach.evalCLM_precompL_apply
    hα (abs_nonneg r) (finiteParabolicAffineMap_mapsTo c a hr)
      (fun p _hp q _hq =>
        (parabolicDistance_finiteParabolicAffineMap c a r p q).le)
    z hz u

@[simp] theorem ParabolicC0AlphaBanach.evalCLM_finiteAffinePushforwardL
    {α S : ℝ} (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (u : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X a.1 (a.1 + S)))
    (z : ℝ × X)
    (hz : z ∈ parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S)) :
    ParabolicC0AlphaBanach.evalCLM z hz
        (ParabolicC0AlphaBanach.finiteAffinePushforwardL hα c a r hr u) =
      ParabolicC0AlphaBanach.evalCLM (finiteParabolicAffineInvMap c a r z)
        (by
          change finiteParabolicAffineMap a c r⁻¹ z ∈
            parabolicFiniteCylinder X a.1 (a.1 + S)
          have h := finiteParabolicAffineMap_mapsTo
            (X := X) a c (S := r ^ 2 * S) (inv_ne_zero hr) hz
          rw [inv_sq_mul_sq_mul r S hr] at h
          exact h) u := by
  exact ParabolicC0AlphaBanach.evalCLM_precompL_apply
    hα (abs_nonneg r⁻¹) (finiteParabolicAffineInvMap_mapsTo c a hr)
      (fun p _hp q _hq =>
        (parabolicDistance_finiteParabolicAffineInvMap c a r p q).le)
    z hz u

/-- Pulling back after pushing forward recovers normalized Hölder data. -/
@[simp] theorem ParabolicC0AlphaBanach.finiteAffinePullbackL_pushforwardL_apply
    {α S : ℝ} (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (u : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X a.1 (a.1 + S))) :
    ParabolicC0AlphaBanach.finiteAffinePullbackL hα c a r hr
        (ParabolicC0AlphaBanach.finiteAffinePushforwardL hα c a r hr u) = u := by
  apply (ParabolicC0AlphaBanach.eq_iff_forall_evalCLM _ _).2
  intro z hz
  rw [ParabolicC0AlphaBanach.evalCLM_finiteAffinePullbackL,
    ParabolicC0AlphaBanach.evalCLM_finiteAffinePushforwardL]
  rw [ParabolicC0AlphaBanach.evalCLM_eq_representative,
    ParabolicC0AlphaBanach.evalCLM_eq_representative,
    finiteParabolicAffineInvMap_leftInverse c a hr z]

/-- Pushing forward after pulling back recovers physical-cylinder Hölder data. -/
@[simp] theorem ParabolicC0AlphaBanach.finiteAffinePushforwardL_pullbackL_apply
    {α S : ℝ} (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (u : ParabolicC0AlphaBanach X E α
      (parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S))) :
    ParabolicC0AlphaBanach.finiteAffinePushforwardL hα c a r hr
        (ParabolicC0AlphaBanach.finiteAffinePullbackL hα c a r hr u) = u := by
  apply (ParabolicC0AlphaBanach.eq_iff_forall_evalCLM _ _).2
  intro z hz
  rw [ParabolicC0AlphaBanach.evalCLM_finiteAffinePushforwardL,
    ParabolicC0AlphaBanach.evalCLM_finiteAffinePullbackL]
  rw [ParabolicC0AlphaBanach.evalCLM_eq_representative,
    ParabolicC0AlphaBanach.evalCLM_eq_representative,
    finiteParabolicAffineInvMap_rightInverse c a hr z]

/-- The normalized-data pullback and pushforward compose to the identity CLM. -/
@[simp] theorem ParabolicC0AlphaBanach.finiteAffinePullbackL_comp_pushforwardL
    {α S : ℝ} (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0) :
    (ParabolicC0AlphaBanach.finiteAffinePullbackL
      (E := E) (S := S) hα c a r hr).comp
        (ParabolicC0AlphaBanach.finiteAffinePushforwardL hα c a r hr) =
      ContinuousLinearMap.id ℝ _ := by
  ext u
  exact ParabolicC0AlphaBanach.finiteAffinePullbackL_pushforwardL_apply
    hα c a r hr u

/-- The physical-data pushforward and pullback compose to the identity CLM. -/
@[simp] theorem ParabolicC0AlphaBanach.finiteAffinePushforwardL_comp_pullbackL
    {α S : ℝ} (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0) :
    (ParabolicC0AlphaBanach.finiteAffinePushforwardL
      (E := E) (S := S) hα c a r hr).comp
        (ParabolicC0AlphaBanach.finiteAffinePullbackL hα c a r hr) =
      ContinuousLinearMap.id ℝ _ := by
  ext u
  exact ParabolicC0AlphaBanach.finiteAffinePushforwardL_pullbackL_apply
    hα c a r hr u

/-- The spatial chain-rule map `D ↦ D ∘ (r·id)`. -/
def finiteAffineFirstDerivativeL (r : ℝ) :
    (X →L[ℝ] E) →L[ℝ] (X →L[ℝ] E) :=
  precomposeFirstDerivativeL (r • ContinuousLinearMap.id ℝ X)

@[simp] theorem finiteAffineFirstDerivativeL_apply
    (r : ℝ) (D : X →L[ℝ] E) (v : X) :
    finiteAffineFirstDerivativeL r D v = r • D v := by
  simp [finiteAffineFirstDerivativeL, precomposeFirstDerivativeL_apply]

/-- The spatial second-derivative chain-rule map, with one factor `r` in
each input. -/
def finiteAffineSecondDerivativeL (r : ℝ) :
    (X →L[ℝ] X →L[ℝ] E) →L[ℝ] (X →L[ℝ] X →L[ℝ] E) :=
  precomposeSecondDerivativeL (r • ContinuousLinearMap.id ℝ X)

@[simp] theorem finiteAffineSecondDerivativeL_apply
    (r : ℝ) (D : X →L[ℝ] X →L[ℝ] E) (v w : X) :
    finiteAffineSecondDerivativeL r D v w = r ^ 2 • D v w := by
  simp [finiteAffineSecondDerivativeL, precomposeSecondDerivativeL_apply,
    pow_two, smul_smul]

/-- The time-derivative chain-rule map `v ↦ r² v`. -/
def finiteAffineTimeDerivativeL (r : ℝ) : E →L[ℝ] E :=
  r ^ 2 • ContinuousLinearMap.id ℝ E

@[simp] theorem finiteAffineTimeDerivativeL_apply (r : ℝ) (v : E) :
    finiteAffineTimeDerivativeL r v = r ^ 2 • v := by
  simp [finiteAffineTimeDerivativeL]

namespace FiniteParabolicC2AlphaBanach

variable {t₀ T α : ℝ}
/-- Spatial differentiation of a fixed-time finite-cylinder solution after
the inverse affine map `x ↦ r⁻¹ (x - c)`. -/
theorem hasFDerivAt_spatialInvAffineValue
    (q : FiniteParabolicC2AlphaBanach X E t₀ T α)
    {t : ℝ} (ht : t ∈ Set.Ioc t₀ T) (c : X) (r : ℝ) (x : X) :
    HasFDerivAt
      (fun y : X => value q (t, r⁻¹ • (y - c)))
      ((spaceDeriv q (t, r⁻¹ • (x - c))).comp
        (r⁻¹ • ContinuousLinearMap.id ℝ X)) x := by
  let L : X →L[ℝ] X := r⁻¹ • ContinuousLinearMap.id ℝ X
  have hmap : HasFDerivAt (fun y : X => r⁻¹ • (y - c)) L x := by
    have h := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const c).const_smul r⁻¹
    convert h using 1
    funext y
    rfl
  have h := (hasFDerivAt_space q ht (r⁻¹ • (x - c))).comp x hmap
  simpa only [Function.comp_def, L] using h
/-- A second spatial differentiation of the inverse-affine fixed-time slice
produces the exact two inverse-radius factors. -/
theorem hasFDerivAt_spatialInvAffineSpaceDeriv
    (q : FiniteParabolicC2AlphaBanach X E t₀ T α)
    {t : ℝ} (ht : t ∈ Set.Ioc t₀ T) (c : X) (r : ℝ) (x : X) :
    HasFDerivAt
      (fun y : X => ((ContinuousLinearMap.compL ℝ X X E).flip
          (r⁻¹ • ContinuousLinearMap.id ℝ X))
        (spaceDeriv q (t, r⁻¹ • (y - c))))
      (((ContinuousLinearMap.compL ℝ X X E).flip
          (r⁻¹ • ContinuousLinearMap.id ℝ X)).comp
        ((spaceSecondDeriv q (t, r⁻¹ • (x - c))).comp
          (r⁻¹ • ContinuousLinearMap.id ℝ X))) x := by
  let L : X →L[ℝ] X := r⁻¹ • ContinuousLinearMap.id ℝ X
  let K := (ContinuousLinearMap.compL ℝ X X E).flip L
  have hmap : HasFDerivAt (fun y : X => r⁻¹ • (y - c)) L x := by
    have h := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const c).const_smul r⁻¹
    convert h using 1
    funext y
    rfl
  have hcomp := (hasFDerivAt_spaceDeriv q ht
    (r⁻¹ • (x - c))).comp x hmap
  have h := K.hasFDerivAt.comp x hcomp
  simpa only [Function.comp_def, K, L] using h

end FiniteParabolicC2AlphaBanach

namespace FiniteParabolicC2AlphaAmbient

variable {α S : ℝ}

/-- Pullback of an ambient finite-cylinder four-jet by affine parabolic
scaling, including all exact chain-rule weights. -/
def finiteAffinePullbackL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0) :
    FiniteParabolicC2AlphaAmbient X E c.1 (c.1 + r ^ 2 * S) α →L[ℝ]
      FiniteParabolicC2AlphaAmbient X E a.1 (a.1 + S) α := by
  let V := ParabolicC0AlphaBanach.finiteAffinePullbackL
    (X := X) (E := E) (α := α) (S := S) hα c a r hr
  let D0 := ParabolicC0AlphaBanach.finiteAffinePullbackL
    (X := X) (E := X →L[ℝ] E) (α := α) (S := S) hα c a r hr
  let D := (ParabolicC0AlphaBanach.compL
      (finiteAffineFirstDerivativeL (X := X) (E := E) r)).comp D0
  let D20 := ParabolicC0AlphaBanach.finiteAffinePullbackL
    (X := X) (E := X →L[ℝ] X →L[ℝ] E)
      (α := α) (S := S) hα c a r hr
  let D2 := (ParabolicC0AlphaBanach.compL
      (finiteAffineSecondDerivativeL (X := X) (E := E) r)).comp D20
  let Dt0 := ParabolicC0AlphaBanach.finiteAffinePullbackL
    (X := X) (E := E) (α := α) (S := S) hα c a r hr
  let Dt := (ParabolicC0AlphaBanach.compL
      (finiteAffineTimeDerivativeL (E := E) r)).comp Dt0
  exact
    (V.comp (ContinuousLinearMap.fst ℝ _ _)).prod
      ((D.comp ((ContinuousLinearMap.fst ℝ _ _).comp
          (ContinuousLinearMap.snd ℝ _ _))).prod
        ((D2.comp ((ContinuousLinearMap.fst ℝ _ _).comp
            ((ContinuousLinearMap.snd ℝ _ _).comp
              (ContinuousLinearMap.snd ℝ _ _)))).prod
          (Dt.comp ((ContinuousLinearMap.snd ℝ _ _).comp
            ((ContinuousLinearMap.snd ℝ _ _).comp
              (ContinuousLinearMap.snd ℝ _ _))))))

/-- Pushforward of an ambient finite-cylinder four-jet by the inverse affine
chart.  This is defined directly, so its source and target endpoints are
definitionally the physical cylinders rather than transports across an
arithmetic equality. -/
def finiteAffinePushforwardL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0) :
    FiniteParabolicC2AlphaAmbient X E a.1 (a.1 + S) α →L[ℝ]
      FiniteParabolicC2AlphaAmbient X E c.1 (c.1 + r ^ 2 * S) α := by
  let V := ParabolicC0AlphaBanach.finiteAffinePushforwardL
    (X := X) (E := E) (α := α) (S := S) hα c a r hr
  let D0 := ParabolicC0AlphaBanach.finiteAffinePushforwardL
    (X := X) (E := X →L[ℝ] E) (α := α) (S := S) hα c a r hr
  let D := (ParabolicC0AlphaBanach.compL
      (finiteAffineFirstDerivativeL (X := X) (E := E) r⁻¹)).comp D0
  let D20 := ParabolicC0AlphaBanach.finiteAffinePushforwardL
    (X := X) (E := X →L[ℝ] X →L[ℝ] E)
      (α := α) (S := S) hα c a r hr
  let D2 := (ParabolicC0AlphaBanach.compL
      (finiteAffineSecondDerivativeL (X := X) (E := E) r⁻¹)).comp D20
  let Dt0 := ParabolicC0AlphaBanach.finiteAffinePushforwardL
    (X := X) (E := E) (α := α) (S := S) hα c a r hr
  let Dt := (ParabolicC0AlphaBanach.compL
      (finiteAffineTimeDerivativeL (E := E) r⁻¹)).comp Dt0
  exact
    (V.comp (ContinuousLinearMap.fst ℝ _ _)).prod
      ((D.comp ((ContinuousLinearMap.fst ℝ _ _).comp
          (ContinuousLinearMap.snd ℝ _ _))).prod
        ((D2.comp ((ContinuousLinearMap.fst ℝ _ _).comp
            ((ContinuousLinearMap.snd ℝ _ _).comp
              (ContinuousLinearMap.snd ℝ _ _)))).prod
          (Dt.comp ((ContinuousLinearMap.snd ℝ _ _).comp
            ((ContinuousLinearMap.snd ℝ _ _).comp
              (ContinuousLinearMap.snd ℝ _ _))))))

@[simp] theorem value_finiteAffinePullbackL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (q : FiniteParabolicC2AlphaAmbient X E c.1 (c.1 + r ^ 2 * S) α)
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X a.1 (a.1 + S)) :
    value (finiteAffinePullbackL hα c a r hr q) z =
      value q (finiteParabolicAffineMap c a r z) := by
  unfold value
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
    ((finiteAffinePullbackL hα c a r hr q).1) z hz]
  change ParabolicC0AlphaBanach.evalCLM z hz
      (ParabolicC0AlphaBanach.finiteAffinePullbackL hα c a r hr q.1) = _
  rw [ParabolicC0AlphaBanach.evalCLM_finiteAffinePullbackL,
    ParabolicC0AlphaBanach.evalCLM_eq_representative]

@[simp] theorem spaceDeriv_finiteAffinePullbackL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (q : FiniteParabolicC2AlphaAmbient X E c.1 (c.1 + r ^ 2 * S) α)
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X a.1 (a.1 + S)) :
    spaceDeriv (finiteAffinePullbackL hα c a r hr q) z =
      finiteAffineFirstDerivativeL r
        (spaceDeriv q (finiteParabolicAffineMap c a r z)) := by
  unfold spaceDeriv
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
    ((finiteAffinePullbackL hα c a r hr q).2.1) z hz]
  change ParabolicC0AlphaBanach.evalCLM z hz
      ((ParabolicC0AlphaBanach.compL (finiteAffineFirstDerivativeL r)).comp
        (ParabolicC0AlphaBanach.finiteAffinePullbackL hα c a r hr) q.2.1) = _
  rw [ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_compL_apply,
    ParabolicC0AlphaBanach.evalCLM_finiteAffinePullbackL,
    ParabolicC0AlphaBanach.evalCLM_eq_representative]

@[simp] theorem spaceSecondDeriv_finiteAffinePullbackL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (q : FiniteParabolicC2AlphaAmbient X E c.1 (c.1 + r ^ 2 * S) α)
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X a.1 (a.1 + S)) :
    spaceSecondDeriv (finiteAffinePullbackL hα c a r hr q) z =
      finiteAffineSecondDerivativeL r
        (spaceSecondDeriv q (finiteParabolicAffineMap c a r z)) := by
  unfold spaceSecondDeriv
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
    ((finiteAffinePullbackL hα c a r hr q).2.2.1) z hz]
  change ParabolicC0AlphaBanach.evalCLM z hz
      ((ParabolicC0AlphaBanach.compL (finiteAffineSecondDerivativeL r)).comp
        (ParabolicC0AlphaBanach.finiteAffinePullbackL hα c a r hr) q.2.2.1) = _
  rw [ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_compL_apply,
    ParabolicC0AlphaBanach.evalCLM_finiteAffinePullbackL,
    ParabolicC0AlphaBanach.evalCLM_eq_representative]

@[simp] theorem timeDeriv_finiteAffinePullbackL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (q : FiniteParabolicC2AlphaAmbient X E c.1 (c.1 + r ^ 2 * S) α)
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X a.1 (a.1 + S)) :
    timeDeriv (finiteAffinePullbackL hα c a r hr q) z =
      r ^ 2 • timeDeriv q (finiteParabolicAffineMap c a r z) := by
  unfold timeDeriv
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
    ((finiteAffinePullbackL hα c a r hr q).2.2.2) z hz]
  change ParabolicC0AlphaBanach.evalCLM z hz
      ((ParabolicC0AlphaBanach.compL (finiteAffineTimeDerivativeL r)).comp
        (ParabolicC0AlphaBanach.finiteAffinePullbackL hα c a r hr) q.2.2.2) = _
  rw [ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_compL_apply,
    ParabolicC0AlphaBanach.evalCLM_finiteAffinePullbackL,
    ParabolicC0AlphaBanach.evalCLM_eq_representative,
    finiteAffineTimeDerivativeL_apply]

@[simp] theorem value_finiteAffinePushforwardL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (q : FiniteParabolicC2AlphaAmbient X E a.1 (a.1 + S) α)
    (z : ℝ × X)
    (hz : z ∈ parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S)) :
    value (finiteAffinePushforwardL hα c a r hr q) z =
      value q (finiteParabolicAffineInvMap c a r z) := by
  unfold value
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
    ((finiteAffinePushforwardL hα c a r hr q).1) z hz]
  change ParabolicC0AlphaBanach.evalCLM z hz
      (ParabolicC0AlphaBanach.finiteAffinePushforwardL hα c a r hr q.1) = _
  rw [ParabolicC0AlphaBanach.evalCLM_finiteAffinePushforwardL,
    ParabolicC0AlphaBanach.evalCLM_eq_representative]

@[simp] theorem spaceDeriv_finiteAffinePushforwardL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (q : FiniteParabolicC2AlphaAmbient X E a.1 (a.1 + S) α)
    (z : ℝ × X)
    (hz : z ∈ parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S)) :
    spaceDeriv (finiteAffinePushforwardL hα c a r hr q) z =
      finiteAffineFirstDerivativeL r⁻¹
        (spaceDeriv q (finiteParabolicAffineInvMap c a r z)) := by
  unfold spaceDeriv
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
    ((finiteAffinePushforwardL hα c a r hr q).2.1) z hz]
  change ParabolicC0AlphaBanach.evalCLM z hz
      ((ParabolicC0AlphaBanach.compL (finiteAffineFirstDerivativeL r⁻¹)).comp
        (ParabolicC0AlphaBanach.finiteAffinePushforwardL hα c a r hr) q.2.1) = _
  rw [ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_compL_apply,
    ParabolicC0AlphaBanach.evalCLM_finiteAffinePushforwardL,
    ParabolicC0AlphaBanach.evalCLM_eq_representative]

@[simp] theorem spaceSecondDeriv_finiteAffinePushforwardL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (q : FiniteParabolicC2AlphaAmbient X E a.1 (a.1 + S) α)
    (z : ℝ × X)
    (hz : z ∈ parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S)) :
    spaceSecondDeriv (finiteAffinePushforwardL hα c a r hr q) z =
      finiteAffineSecondDerivativeL r⁻¹
        (spaceSecondDeriv q (finiteParabolicAffineInvMap c a r z)) := by
  unfold spaceSecondDeriv
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
    ((finiteAffinePushforwardL hα c a r hr q).2.2.1) z hz]
  change ParabolicC0AlphaBanach.evalCLM z hz
      ((ParabolicC0AlphaBanach.compL (finiteAffineSecondDerivativeL r⁻¹)).comp
        (ParabolicC0AlphaBanach.finiteAffinePushforwardL hα c a r hr) q.2.2.1) = _
  rw [ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_compL_apply,
    ParabolicC0AlphaBanach.evalCLM_finiteAffinePushforwardL,
    ParabolicC0AlphaBanach.evalCLM_eq_representative]

@[simp] theorem timeDeriv_finiteAffinePushforwardL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (q : FiniteParabolicC2AlphaAmbient X E a.1 (a.1 + S) α)
    (z : ℝ × X)
    (hz : z ∈ parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S)) :
    timeDeriv (finiteAffinePushforwardL hα c a r hr q) z =
      r⁻¹ ^ 2 • timeDeriv q (finiteParabolicAffineInvMap c a r z) := by
  unfold timeDeriv
  rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative
    ((finiteAffinePushforwardL hα c a r hr q).2.2.2) z hz]
  change ParabolicC0AlphaBanach.evalCLM z hz
      ((ParabolicC0AlphaBanach.compL (finiteAffineTimeDerivativeL r⁻¹)).comp
        (ParabolicC0AlphaBanach.finiteAffinePushforwardL hα c a r hr) q.2.2.2) = _
  rw [ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_compL_apply,
    ParabolicC0AlphaBanach.evalCLM_finiteAffinePushforwardL,
    ParabolicC0AlphaBanach.evalCLM_eq_representative,
    finiteAffineTimeDerivativeL_apply]

/-- The affine four-jet pullback preserves derivative-graph compatibility. -/
theorem finiteAffinePullbackL_mem_compatibleSubmodule
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (q : FiniteParabolicC2AlphaAmbient X E c.1 (c.1 + r ^ 2 * S) α)
    (hq : q ∈ compatibleSubmodule
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α)) :
    finiteAffinePullbackL hα c a r hr q ∈ compatibleSubmodule
      (X := X) (E := E) (t₀ := a.1) (T := a.1 + S) (α := α) := by
  constructor
  · intro t ht x
    let L : X →L[ℝ] X := r • ContinuousLinearMap.id ℝ X
    have htime : c.1 < c.1 + r ^ 2 * (t - a.1) ∧
        c.1 + r ^ 2 * (t - a.1) ≤ c.1 + r ^ 2 * S := by
      have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
      constructor <;> nlinarith [ht.1, ht.2]
    have hmap : HasFDerivAt (fun y : X => c.2 + r • (y - a.2)) L x := by
      have h := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const a.2).const_smul r
      convert (hasFDerivAt_const (𝕜 := ℝ) c.2 x).add h using 1
      · ext y
        rfl
      · simp [L]
    have h := (hq.hasSpaceDeriv _ htime (c.2 + r • (x - a.2))).comp x hmap
    convert h using 1
    · funext y
      rw [value_finiteAffinePullbackL hα c a r hr q (t, y)
        (by simpa [parabolicFiniteCylinder] using ht)]
      rfl
    · rw [spaceDeriv_finiteAffinePullbackL hα c a r hr q (t, x)
        (by simpa [parabolicFiniteCylinder] using ht)]
      rfl
  · intro t ht x
    let L : X →L[ℝ] X := r • ContinuousLinearMap.id ℝ X
    have htime : c.1 < c.1 + r ^ 2 * (t - a.1) ∧
        c.1 + r ^ 2 * (t - a.1) ≤ c.1 + r ^ 2 * S := by
      have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
      constructor <;> nlinarith [ht.1, ht.2]
    have hmap : HasFDerivAt (fun y : X => c.2 + r • (y - a.2)) L x := by
      have h := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const a.2).const_smul r
      convert (hasFDerivAt_const (𝕜 := ℝ) c.2 x).add h using 1
      · ext y
        rfl
      · simp [L]
    let K := finiteAffineFirstDerivativeL (X := X) (E := E) r
    have hcomp := (hq.hasSpaceSecondDeriv _ htime
      (c.2 + r • (x - a.2))).comp x hmap
    have h := K.hasFDerivAt.comp x hcomp
    convert h using 1
    · funext y
      rw [spaceDeriv_finiteAffinePullbackL hα c a r hr q (t, y)
        (by simpa [parabolicFiniteCylinder] using ht)]
      rfl
    · rw [spaceSecondDeriv_finiteAffinePullbackL hα c a r hr q (t, x)
        (by simpa [parabolicFiniteCylinder] using ht)]
      rfl
  · intro t ht x
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    have htime : c.1 < c.1 + r ^ 2 * (t - a.1) ∧
        c.1 + r ^ 2 * (t - a.1) < c.1 + r ^ 2 * S := by
      constructor <;> nlinarith [ht.1, ht.2]
    have hmap : HasDerivAt (fun s : ℝ => c.1 + r ^ 2 * (s - a.1)) (r ^ 2) t := by
      have hsub : HasDerivAt (fun s : ℝ => s - a.1) 1 t :=
        (hasDerivAt_id t).sub_const a.1
      have hmul : HasDerivAt (fun s : ℝ => r ^ 2 * (s - a.1)) (r ^ 2) t := by
        simpa [mul_comm] using hsub.const_mul (r ^ 2)
      exact hmul.const_add c.1
    have houter : HasDerivAt
        (fun s : ℝ => value q (s, c.2 + r • (x - a.2)))
        (timeDeriv q
          (c.1 + r ^ 2 * (t - a.1), c.2 + r • (x - a.2)))
        (c.1 + r ^ 2 * (t - a.1)) :=
      hq.hasTimeDeriv _ htime (c.2 + r • (x - a.2))
    have h := houter.scomp t hmap
    have hnhds : Set.Ioc a.1 (a.1 + S) ∈ 𝓝 t :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Set.Ioo_subset_Ioc_self
    have hev :
        (fun s : ℝ => value (finiteAffinePullbackL hα c a r hr q) (s, x))
          =ᶠ[𝓝 t]
        fun s : ℝ => value q
          (c.1 + r ^ 2 * (s - a.1), c.2 + r • (x - a.2)) := by
      filter_upwards [hnhds] with s hs
      rw [value_finiteAffinePullbackL hα c a r hr q (s, x)
        (by simpa [parabolicFiniteCylinder] using hs)]
      rfl
    have hz : (t, x) ∈ parabolicFiniteCylinder X a.1 (a.1 + S) := by
      simp [parabolicFiniteCylinder, ht.1, ht.2.le]
    rw [timeDeriv_finiteAffinePullbackL hα c a r hr q (t, x) hz]
    exact h.congr_of_eventuallyEq hev

/-- The direct inverse-chart four-jet pushforward also preserves the three
derivative-graph compatibility conditions. -/
theorem finiteAffinePushforwardL_mem_compatibleSubmodule
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (q : FiniteParabolicC2AlphaAmbient X E a.1 (a.1 + S) α)
    (hq : q ∈ compatibleSubmodule
      (X := X) (E := E) (t₀ := a.1) (T := a.1 + S) (α := α)) :
    finiteAffinePushforwardL hα c a r hr q ∈ compatibleSubmodule
      (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α) := by
  have hrinv2 : 0 < r⁻¹ ^ 2 := sq_pos_of_ne_zero (inv_ne_zero hr)
  have hscale : r⁻¹ ^ 2 * (r ^ 2 * S) = S :=
    inv_sq_mul_sq_mul r S hr
  constructor
  · intro t ht x
    let L : X →L[ℝ] X := r⁻¹ • ContinuousLinearMap.id ℝ X
    have hdelta : 0 < t - c.1 ∧ t - c.1 ≤ r ^ 2 * S := by
      constructor <;> linarith [ht.1, ht.2]
    have hscaledLower : 0 < r⁻¹ ^ 2 * (t - c.1) :=
      mul_pos hrinv2 hdelta.1
    have hscaledUpper : r⁻¹ ^ 2 * (t - c.1) ≤ S := by
      have h := mul_le_mul_of_nonneg_left hdelta.2 hrinv2.le
      rw [hscale] at h
      exact h
    have htime : a.1 < a.1 + r⁻¹ ^ 2 * (t - c.1) ∧
        a.1 + r⁻¹ ^ 2 * (t - c.1) ≤ a.1 + S := by
      constructor <;> linarith
    have hmap : HasFDerivAt (fun y : X => a.2 + r⁻¹ • (y - c.2)) L x := by
      have h := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const c.2).const_smul r⁻¹
      convert (hasFDerivAt_const (𝕜 := ℝ) a.2 x).add h using 1
      · ext y
        rfl
      · simp [L]
    have h := (hq.hasSpaceDeriv _ htime
      (a.2 + r⁻¹ • (x - c.2))).comp x hmap
    convert h using 1
    · funext y
      rw [value_finiteAffinePushforwardL hα c a r hr q (t, y)
        (by simpa [parabolicFiniteCylinder] using ht)]
      rfl
    · rw [spaceDeriv_finiteAffinePushforwardL hα c a r hr q (t, x)
        (by simpa [parabolicFiniteCylinder] using ht)]
      rfl
  · intro t ht x
    let L : X →L[ℝ] X := r⁻¹ • ContinuousLinearMap.id ℝ X
    have hdelta : 0 < t - c.1 ∧ t - c.1 ≤ r ^ 2 * S := by
      constructor <;> linarith [ht.1, ht.2]
    have hscaledLower : 0 < r⁻¹ ^ 2 * (t - c.1) :=
      mul_pos hrinv2 hdelta.1
    have hscaledUpper : r⁻¹ ^ 2 * (t - c.1) ≤ S := by
      have h := mul_le_mul_of_nonneg_left hdelta.2 hrinv2.le
      rw [hscale] at h
      exact h
    have htime : a.1 < a.1 + r⁻¹ ^ 2 * (t - c.1) ∧
        a.1 + r⁻¹ ^ 2 * (t - c.1) ≤ a.1 + S := by
      constructor <;> linarith
    have hmap : HasFDerivAt (fun y : X => a.2 + r⁻¹ • (y - c.2)) L x := by
      have h := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const c.2).const_smul r⁻¹
      convert (hasFDerivAt_const (𝕜 := ℝ) a.2 x).add h using 1
      · ext y
        rfl
      · simp [L]
    let K := finiteAffineFirstDerivativeL (X := X) (E := E) r⁻¹
    have hcomp := (hq.hasSpaceSecondDeriv _ htime
      (a.2 + r⁻¹ • (x - c.2))).comp x hmap
    have h := K.hasFDerivAt.comp x hcomp
    convert h using 1
    · funext y
      rw [spaceDeriv_finiteAffinePushforwardL hα c a r hr q (t, y)
        (by simpa [parabolicFiniteCylinder] using ht)]
      rfl
    · rw [spaceSecondDeriv_finiteAffinePushforwardL hα c a r hr q (t, x)
        (by simpa [parabolicFiniteCylinder] using ht)]
      rfl
  · intro t ht x
    have hdelta : 0 < t - c.1 ∧ t - c.1 < r ^ 2 * S := by
      constructor <;> linarith [ht.1, ht.2]
    have hscaledLower : 0 < r⁻¹ ^ 2 * (t - c.1) :=
      mul_pos hrinv2 hdelta.1
    have hscaledUpper : r⁻¹ ^ 2 * (t - c.1) < S := by
      have h := mul_lt_mul_of_pos_left hdelta.2 hrinv2
      rw [hscale] at h
      exact h
    have htime : a.1 < a.1 + r⁻¹ ^ 2 * (t - c.1) ∧
        a.1 + r⁻¹ ^ 2 * (t - c.1) < a.1 + S := by
      constructor <;> linarith
    have hmap : HasDerivAt
        (fun s : ℝ => a.1 + r⁻¹ ^ 2 * (s - c.1)) (r⁻¹ ^ 2) t := by
      have hsub : HasDerivAt (fun s : ℝ => s - c.1) 1 t :=
        (hasDerivAt_id t).sub_const c.1
      have hmul : HasDerivAt
          (fun s : ℝ => r⁻¹ ^ 2 * (s - c.1)) (r⁻¹ ^ 2) t := by
        simpa only [mul_comm, mul_one] using hsub.const_mul (r⁻¹ ^ 2)
      exact hmul.const_add a.1
    have houter : HasDerivAt
        (fun s : ℝ => value q (s, a.2 + r⁻¹ • (x - c.2)))
        (timeDeriv q
          (a.1 + r⁻¹ ^ 2 * (t - c.1), a.2 + r⁻¹ • (x - c.2)))
        (a.1 + r⁻¹ ^ 2 * (t - c.1)) :=
      hq.hasTimeDeriv _ htime (a.2 + r⁻¹ • (x - c.2))
    have h := houter.scomp t hmap
    have hnhds : Set.Ioc c.1 (c.1 + r ^ 2 * S) ∈ 𝓝 t :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Set.Ioo_subset_Ioc_self
    have hev :
        (fun s : ℝ => value (finiteAffinePushforwardL hα c a r hr q) (s, x))
          =ᶠ[𝓝 t]
        fun s : ℝ => value q
          (a.1 + r⁻¹ ^ 2 * (s - c.1), a.2 + r⁻¹ • (x - c.2)) := by
      filter_upwards [hnhds] with s hs
      rw [value_finiteAffinePushforwardL hα c a r hr q (s, x)
        (by simpa [parabolicFiniteCylinder] using hs)]
      rfl
    have hz : (t, x) ∈ parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S) := by
      simp [parabolicFiniteCylinder, ht.1, ht.2.le]
    rw [timeDeriv_finiteAffinePushforwardL hα c a r hr q (t, x) hz]
    exact h.congr_of_eventuallyEq hev

end FiniteParabolicC2AlphaAmbient

namespace FiniteParabolicC2AlphaBanach

variable {α S : ℝ}

/-- Bounded affine parabolic pullback on the genuine compatible four-jet
Banach space. -/
def finiteAffinePullbackL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0) :
    FiniteParabolicC2AlphaBanach X E c.1 (c.1 + r ^ 2 * S) α →L[ℝ]
      FiniteParabolicC2AlphaBanach X E a.1 (a.1 + S) α :=
  (FiniteParabolicC2AlphaAmbient.finiteAffinePullbackL
      (X := X) (E := E) (α := α) (S := S) hα c a r hr).comp
      (FiniteParabolicC2AlphaAmbient.compatibleSubmodule
        (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S)
        (α := α)).subtypeL |>.codRestrict
    (FiniteParabolicC2AlphaAmbient.compatibleSubmodule
      (X := X) (E := E) (t₀ := a.1) (T := a.1 + S) (α := α))
    (fun u => FiniteParabolicC2AlphaAmbient.finiteAffinePullbackL_mem_compatibleSubmodule
      hα c a r hr u.1 u.2)

/-- Pushforward of compatible four-jets from normalized coordinates back
to the original finite cylinder. -/
def finiteAffinePushforwardL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0) :
    FiniteParabolicC2AlphaBanach X E a.1 (a.1 + S) α →L[ℝ]
      FiniteParabolicC2AlphaBanach X E c.1 (c.1 + r ^ 2 * S) α :=
  (FiniteParabolicC2AlphaAmbient.finiteAffinePushforwardL
      (X := X) (E := E) (α := α) (S := S) hα c a r hr).comp
      (FiniteParabolicC2AlphaAmbient.compatibleSubmodule
        (X := X) (E := E) (t₀ := a.1) (T := a.1 + S) (α := α)).subtypeL
    |>.codRestrict
      (FiniteParabolicC2AlphaAmbient.compatibleSubmodule
        (X := X) (E := E) (t₀ := c.1) (T := c.1 + r ^ 2 * S) (α := α))
      (fun u =>
        FiniteParabolicC2AlphaAmbient.finiteAffinePushforwardL_mem_compatibleSubmodule
          hα c a r hr u.1 u.2)

@[simp] theorem value_finiteAffinePullbackL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (u : FiniteParabolicC2AlphaBanach X E c.1 (c.1 + r ^ 2 * S) α)
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X a.1 (a.1 + S)) :
    value (finiteAffinePullbackL hα c a r hr u) z =
      value u (finiteParabolicAffineMap c a r z) :=
  FiniteParabolicC2AlphaAmbient.value_finiteAffinePullbackL hα c a r hr u.1 z hz

@[simp] theorem spaceDeriv_finiteAffinePullbackL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (u : FiniteParabolicC2AlphaBanach X E c.1 (c.1 + r ^ 2 * S) α)
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X a.1 (a.1 + S)) :
    spaceDeriv (finiteAffinePullbackL hα c a r hr u) z =
      finiteAffineFirstDerivativeL r
        (spaceDeriv u (finiteParabolicAffineMap c a r z)) :=
  FiniteParabolicC2AlphaAmbient.spaceDeriv_finiteAffinePullbackL
    hα c a r hr u.1 z hz

@[simp] theorem spaceSecondDeriv_finiteAffinePullbackL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (u : FiniteParabolicC2AlphaBanach X E c.1 (c.1 + r ^ 2 * S) α)
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X a.1 (a.1 + S)) :
    spaceSecondDeriv (finiteAffinePullbackL hα c a r hr u) z =
      finiteAffineSecondDerivativeL r
        (spaceSecondDeriv u (finiteParabolicAffineMap c a r z)) :=
  FiniteParabolicC2AlphaAmbient.spaceSecondDeriv_finiteAffinePullbackL
    hα c a r hr u.1 z hz

@[simp] theorem timeDeriv_finiteAffinePullbackL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (u : FiniteParabolicC2AlphaBanach X E c.1 (c.1 + r ^ 2 * S) α)
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X a.1 (a.1 + S)) :
    timeDeriv (finiteAffinePullbackL hα c a r hr u) z =
      r ^ 2 • timeDeriv u (finiteParabolicAffineMap c a r z) :=
  FiniteParabolicC2AlphaAmbient.timeDeriv_finiteAffinePullbackL
    hα c a r hr u.1 z hz

@[simp] theorem value_finiteAffinePushforwardL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (u : FiniteParabolicC2AlphaBanach X E a.1 (a.1 + S) α)
    (z : ℝ × X)
    (hz : z ∈ parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S)) :
    value (finiteAffinePushforwardL hα c a r hr u) z =
      value u (finiteParabolicAffineInvMap c a r z) := by
  exact FiniteParabolicC2AlphaAmbient.value_finiteAffinePushforwardL
    hα c a r hr u.1 z hz

@[simp] theorem spaceDeriv_finiteAffinePushforwardL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (u : FiniteParabolicC2AlphaBanach X E a.1 (a.1 + S) α)
    (z : ℝ × X)
    (hz : z ∈ parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S)) :
    spaceDeriv (finiteAffinePushforwardL hα c a r hr u) z =
      finiteAffineFirstDerivativeL r⁻¹
        (spaceDeriv u (finiteParabolicAffineInvMap c a r z)) := by
  exact FiniteParabolicC2AlphaAmbient.spaceDeriv_finiteAffinePushforwardL
    hα c a r hr u.1 z hz

@[simp] theorem spaceSecondDeriv_finiteAffinePushforwardL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (u : FiniteParabolicC2AlphaBanach X E a.1 (a.1 + S) α)
    (z : ℝ × X)
    (hz : z ∈ parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S)) :
    spaceSecondDeriv (finiteAffinePushforwardL hα c a r hr u) z =
      finiteAffineSecondDerivativeL r⁻¹
        (spaceSecondDeriv u (finiteParabolicAffineInvMap c a r z)) := by
  exact FiniteParabolicC2AlphaAmbient.spaceSecondDeriv_finiteAffinePushforwardL
    hα c a r hr u.1 z hz

@[simp] theorem timeDeriv_finiteAffinePushforwardL
    (hα : 0 ≤ α) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (u : FiniteParabolicC2AlphaBanach X E a.1 (a.1 + S) α)
    (z : ℝ × X)
    (hz : z ∈ parabolicFiniteCylinder X c.1 (c.1 + r ^ 2 * S)) :
    timeDeriv (finiteAffinePushforwardL hα c a r hr u) z =
      r⁻¹ ^ 2 • timeDeriv u (finiteParabolicAffineInvMap c a r z) := by
  exact FiniteParabolicC2AlphaAmbient.timeDeriv_finiteAffinePushforwardL
    hα c a r hr u.1 z hz

/-- Pullback after pushforward is the identity on compatible normalized
four-jets. -/
@[simp] theorem finiteAffinePullbackL_pushforwardL_apply
    (hα : 0 < α) (hS : 0 < S) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (u : FiniteParabolicC2AlphaBanach X E a.1 (a.1 + S) α) :
    finiteAffinePullbackL hα.le c a r hr
        (finiteAffinePushforwardL hα.le c a r hr u) = u := by
  apply ext_value hα (by linarith)
  intro z hz
  rw [value_finiteAffinePullbackL hα.le c a r hr _ z hz]
  rw [value_finiteAffinePushforwardL hα.le c a r hr u
    (finiteParabolicAffineMap c a r z)
    (finiteParabolicAffineMap_mapsTo c a hr hz)]
  rw [finiteParabolicAffineInvMap_leftInverse c a hr z]

/-- Pushforward after pullback is the identity on compatible physical-cylinder
four-jets. -/
@[simp] theorem finiteAffinePushforwardL_pullbackL_apply
    (hα : 0 < α) (hS : 0 < S) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0)
    (u : FiniteParabolicC2AlphaBanach X E c.1 (c.1 + r ^ 2 * S) α) :
    finiteAffinePushforwardL hα.le c a r hr
        (finiteAffinePullbackL hα.le c a r hr u) = u := by
  have hthick : 0 < r ^ 2 * S := mul_pos (sq_pos_of_ne_zero hr) hS
  apply ext_value hα (by linarith)
  intro z hz
  rw [value_finiteAffinePushforwardL hα.le c a r hr _ z hz]
  rw [value_finiteAffinePullbackL hα.le c a r hr u
    (finiteParabolicAffineInvMap c a r z)
    (finiteParabolicAffineInvMap_mapsTo c a hr hz)]
  rw [finiteParabolicAffineInvMap_rightInverse c a hr z]

/-- Pullback and pushforward compose to the identity on the normalized
compatible Banach space. -/
@[simp] theorem finiteAffinePullbackL_comp_pushforwardL
    (hα : 0 < α) (hS : 0 < S) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0) :
    (finiteAffinePullbackL (E := E) (S := S) hα.le c a r hr).comp
        (finiteAffinePushforwardL hα.le c a r hr) =
      ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro u
  exact finiteAffinePullbackL_pushforwardL_apply hα hS c a r hr u

/-- Pushforward and pullback compose to the identity on the physical-cylinder
compatible Banach space. -/
@[simp] theorem finiteAffinePushforwardL_comp_pullbackL
    (hα : 0 < α) (hS : 0 < S) (c a : ℝ × X) (r : ℝ) (hr : r ≠ 0) :
    (finiteAffinePushforwardL (E := E) (S := S) hα.le c a r hr).comp
        (finiteAffinePullbackL hα.le c a r hr) =
      ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro u
  exact finiteAffinePushforwardL_pullbackL_apply hα hS c a r hr u

end FiniteParabolicC2AlphaBanach

end AnalyticPDE
end RicciFlow
