/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The double-angle Gram identity for principal angles

`sin 2θ = 2 sin θ cos θ` at the level of operators, in the *rectangular*
geometry where the two subspaces need not have the same dimension.

Let `T` be a contraction and `C` a second operator tied to it by the
"Pythagorean" relation `C⋆C = 1 - T T⋆`.  Then

`(C ∘ T)⋆ (C ∘ T) = M - M²`,  `M := T⋆T`,

so the Gram operator of `2 (C ∘ T)` is `4 (M - M²)`: if `s` is a singular value
of `T`, the matching singular value of `2 (C ∘ T)` is
`2 s √(1 - s²) = sin (2 arcsin s)`.

This is the geometric content behind the unequal-dimension `sin 2θ` theorem of
Davis--Kahan 1970 (the extension announced at the end of Section 8).  With
`E₀, F₀, F₁` the isometry blocks of that paper, `P = E₀E₀⋆`, `Q = F₀F₀⋆` and
`X = 2P - 1`, the cross block between the reflected subspace `Q₋ = XQX` and
`Q^⊥` is

`(X F₀)⋆ F₁ = 2 (F₀⋆E₀)(E₀⋆F₁)`,

which is `2 (C ∘ T)` for `C = F₀⋆E₀` and `T = E₀⋆F₁`; and `C⋆C = 1 - T T⋆`
holds because `F₀F₀⋆ + F₁F₁⋆ = 1` and `E₀` is an isometry.  Nothing here
compares `dim (range E₀)` with `dim (range F₀)`, and no direct rotation is
used: the identity is rectangular, which is exactly why the `sin 2θ` estimate
survives a dimension mismatch while the `tan 2θ` estimate does not (see the
section below on the missing `tan 2θ` analogue).

## Main results

* `TauCeti.gram_comp_of_gram_eq_id_sub`: the abstract identity
  `(C ∘ T)⋆(C ∘ T) = M - M²` from `C⋆C = 1 - T T⋆`.
* `TauCeti.gram_two_smul_comp`: the Gram operator of `2 (C ∘ T)` is `4(M - M²)`.
* `TauCeti.gram_two_smul_comp_apply_of_eigenvector`: on an eigenvector of `M`
  for `s²` the Gram operator of `2 (C ∘ T)` acts by `sin (2 arcsin s) ^ 2`.
* `TauCeti.sin_two_mul_arcsin`: `sin (2 arcsin s) = 2 s √(1 - s²)`.
* `TauCeti.gram_isometryBlock_eq_id_sub`: the Davis--Kahan isometry blocks
  satisfy that hypothesis, `(F₀⋆E₀)⋆(F₀⋆E₀) = 1 - (E₀⋆F₁)(E₀⋆F₁)⋆`.
* `TauCeti.adjoint_comp_isometryBlock_eq_zero`: `F₀⋆F₁ = 0`.
* `TauCeti.adjoint_reflection_comp_isometryBlock`: the Section 7 cross-block
  identity `(X F₀)⋆F₁ = 2 (F₀⋆E₀)(E₀⋆F₁)` for `X = 2 E₀E₀⋆ - 1`.
* `TauCeti.gram_adjoint_reflection_comp_isometryBlock`: the two combined — the
  reflected cross block has `sin 2Θ₀` singular data.
* `TauCeti.gram_sinTwoAngleOperator`: the same statement in ambient projector
  form, for `sinTwoAngleOperator U V = 2 P_{Uᗮ} P_V P_U`.

## Why there is no `tan 2θ` analogue

Davis and Kahan record that no extension of the `tan 2θ` theorem to
`dim 𝔛(E₀) < dim 𝔛(F₀)` is known, and this file explains the structural
asymmetry rather than contradicting it.  The `sin 2θ` proof reduces to an
*ordinary* sine theorem for the pair `(Q₋, Q)`, and because `X` is unitary that
pair automatically has matching dimensions however `P` and `Q` differ; the only
step that mentions `Θ₀` is the cross block above, which this file shows is
rectangular.  The `tan 2θ` proof instead imitates the single-angle tangent
argument: its load-bearing identity is a `2 × 2` rotation-block system in
matched `C₀, C₁, S₀` blocks of the *direct rotation* `P → Q`, and when the
dimensions differ there is no direct rotation, hence no such block system.  The
rectangular repair that rescues Theorem 6.3 supplies only `C₁⋆C₁ = 1 - S₀S₀⋆` —
enough for a `cos θ` denominator, not enough to reproduce the coupled `C₀/C₁`
identity that produces the signed `cos 2θ`.  So the obstruction is to the proof
method; nothing here asserts that the `tan 2θ` extension is false.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: Theorems 6.1 and 6.3 for the
  rectangular single-angle geometry, Section 7 for the reflection `X = 2P - 1`,
  and the final paragraph of Section 8 for the extension this file supports.
-/

@[expose] public section

namespace TauCeti

open scoped InnerProductSpace

/-! ### The scalar double-angle transfer -/

/-- `sin (2 arcsin s) = 2 s √(1 - s²)`: the sine of the doubled angle whose sine
is `s`.  This is the scalar content of the double-angle theorems — a singular
value `s = sin θ` of a directed cross projection is carried to `sin 2θ`. -/
theorem sin_two_mul_arcsin {s : ℝ} (h₀ : -1 ≤ s) (h₁ : s ≤ 1) :
    Real.sin (2 * Real.arcsin s) = 2 * s * √(1 - s ^ 2) := by
  rw [Real.sin_two_mul, Real.sin_arcsin h₀ h₁, Real.cos_arcsin]

/-- The squared double-angle sine of an angle with sine `s`, as a polynomial:
`sin (2 arcsin s) ^ 2 = 4 s² (1 - s²)`. -/
theorem sin_two_mul_arcsin_sq {s : ℝ} (h₀ : -1 ≤ s) (h₁ : s ≤ 1) :
    Real.sin (2 * Real.arcsin s) ^ 2 = 4 * s ^ 2 * (1 - s ^ 2) := by
  have hnn : (0 : ℝ) ≤ 1 - s ^ 2 := by nlinarith
  rw [sin_two_mul_arcsin h₀ h₁, mul_pow, mul_pow, Real.sq_sqrt hnn]
  ring

/-! ### The rectangular double-angle Gram identity -/

section Rectangular

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K₀ K₁ L : Type*}
  [NormedAddCommGroup K₀] [InnerProductSpace 𝕜 K₀] [FiniteDimensional 𝕜 K₀]
  [NormedAddCommGroup K₁] [InnerProductSpace 𝕜 K₁] [FiniteDimensional 𝕜 K₁]
  [NormedAddCommGroup L] [InnerProductSpace 𝕜 L] [FiniteDimensional 𝕜 L]

/-- **The rectangular double-angle Gram identity.**  If `C⋆C = 1 - T T⋆` then
the Gram operator of the composite `C ∘ T` is `M - M²` for `M = T⋆T`.

The three spaces are independent: `T : K₁ →ₗ K₀` and `C : K₀ →ₗ L` need not have
equal-dimensional domains and codomains, and no direct rotation between them is
assumed.  This is what makes the `sin 2θ` estimate survive the dimension
mismatch `dim 𝔛(E₀) < dim 𝔛(F₀)` of Davis--Kahan 1970. -/
theorem gram_comp_of_gram_eq_id_sub {C : K₀ →ₗ[𝕜] L} {T : K₁ →ₗ[𝕜] K₀}
    (hC : LinearMap.adjoint C ∘ₗ C = LinearMap.id - T ∘ₗ LinearMap.adjoint T) :
    LinearMap.adjoint (C ∘ₗ T) ∘ₗ (C ∘ₗ T) =
      (LinearMap.adjoint T ∘ₗ T) -
        (LinearMap.adjoint T ∘ₗ T) ∘ₗ (LinearMap.adjoint T ∘ₗ T) := by
  ext x
  have hx := LinearMap.congr_fun hC (T x)
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at hx
  rw [LinearMap.adjoint_comp]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, hx, map_sub]

/-- The Gram operator of `2 (C ∘ T)` is `4 (M - M²)`, `M = T⋆T`: the operator
form of `sin 2θ = 2 sin θ cos θ`, squared. -/
theorem gram_two_smul_comp {C : K₀ →ₗ[𝕜] L} {T : K₁ →ₗ[𝕜] K₀}
    (hC : LinearMap.adjoint C ∘ₗ C = LinearMap.id - T ∘ₗ LinearMap.adjoint T) :
    LinearMap.adjoint ((2 : 𝕜) • (C ∘ₗ T)) ∘ₗ ((2 : 𝕜) • (C ∘ₗ T)) =
      (4 : 𝕜) • ((LinearMap.adjoint T ∘ₗ T) -
        (LinearMap.adjoint T ∘ₗ T) ∘ₗ (LinearMap.adjoint T ∘ₗ T)) := by
  have hadj : LinearMap.adjoint ((2 : 𝕜) • (C ∘ₗ T)) =
      (2 : 𝕜) • LinearMap.adjoint (C ∘ₗ T) := by
    rw [map_smulₛₗ, map_ofNat]
  rw [hadj, LinearMap.smul_comp, LinearMap.comp_smul, gram_comp_of_gram_eq_id_sub hC,
    smul_smul]
  norm_num

/-- **The `sin 2θ` singular value.**  If `x` is an eigenvector of `M = T⋆T` for
`s²` — that is, `s` is a singular value of `T`, hence `s = sin θ` for a
principal angle `θ` — then the Gram operator of `2 (C ∘ T)` acts on `x` by
`sin (2 θ) ^ 2`.

So the singular value of `2 (C ∘ T)` attached to that eigendirection is
`sin 2θ = 2 s √(1 - s²)`, which is the identification of `2 (F₀⋆E₀)(E₀⋆F₁)`
with `sin 2Θ₀` in Davis--Kahan 1970. -/
theorem gram_two_smul_comp_apply_of_eigenvector {C : K₀ →ₗ[𝕜] L} {T : K₁ →ₗ[𝕜] K₀}
    (hC : LinearMap.adjoint C ∘ₗ C = LinearMap.id - T ∘ₗ LinearMap.adjoint T)
    {s : ℝ} (h₀ : -1 ≤ s) (h₁ : s ≤ 1) {x : K₁}
    (hx : (LinearMap.adjoint T ∘ₗ T) x = ((s ^ 2 : ℝ) : 𝕜) • x) :
    (LinearMap.adjoint ((2 : 𝕜) • (C ∘ₗ T)) ∘ₗ ((2 : 𝕜) • (C ∘ₗ T))) x =
      ((Real.sin (2 * Real.arcsin s) ^ 2 : ℝ) : 𝕜) • x := by
  rw [gram_two_smul_comp hC]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, hx,
    map_smul, smul_smul]
  rw [sin_two_mul_arcsin_sq h₀ h₁]
  push_cast
  module

end Rectangular

/-! ### The Davis--Kahan isometry blocks -/

section IsometryBlocks

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {K₀ K₁ L : Type*}
  [NormedAddCommGroup K₀] [InnerProductSpace 𝕜 K₀] [FiniteDimensional 𝕜 K₀]
  [NormedAddCommGroup K₁] [InnerProductSpace 𝕜 K₁] [FiniteDimensional 𝕜 K₁]
  [NormedAddCommGroup L] [InnerProductSpace 𝕜 L] [FiniteDimensional 𝕜 L]

/-- **The Pythagorean relation between the Davis--Kahan isometry blocks.**  If
`F₀F₀⋆ + F₁F₁⋆ = 1` and `E₀` is an isometry, then `C = F₀⋆E₀` and `T = E₀⋆F₁`
satisfy `C⋆C = 1 - T T⋆`.

This is `E₀⋆(F₀F₀⋆)E₀ = E₀⋆E₀ - E₀⋆(F₁F₁⋆)E₀` — no comparison between
`dim (range E₀)` and `dim (range F₀)` enters. -/
theorem gram_isometryBlock_eq_id_sub (E₀ : K₀ →ₗᵢ[𝕜] E) (F₀ : L →ₗᵢ[𝕜] E)
    (F₁ : K₁ →ₗᵢ[𝕜] E)
    (hF : F₀.toLinearMap ∘ₗ LinearMap.adjoint F₀.toLinearMap +
        F₁.toLinearMap ∘ₗ LinearMap.adjoint F₁.toLinearMap = LinearMap.id) :
    LinearMap.adjoint (LinearMap.adjoint F₀.toLinearMap ∘ₗ E₀.toLinearMap) ∘ₗ
        (LinearMap.adjoint F₀.toLinearMap ∘ₗ E₀.toLinearMap) =
      LinearMap.id -
        (LinearMap.adjoint E₀.toLinearMap ∘ₗ F₁.toLinearMap) ∘ₗ
          LinearMap.adjoint
            (LinearMap.adjoint E₀.toLinearMap ∘ₗ F₁.toLinearMap) := by
  ext x
  have hx := LinearMap.congr_fun hF (E₀ x)
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearIsometry.coe_toLinearMap] at hx
  rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint,
    LinearMap.adjoint_adjoint]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearIsometry.coe_toLinearMap]
  rw [eq_sub_iff_add_eq, ← map_add, hx, LinearIsometry.adjoint_apply_apply]

/-- Complementary isometry blocks have orthogonal ranges: `F₀⋆F₁ = 0`.  This is
forced by `F₀F₀⋆ + F₁F₁⋆ = 1` alone. -/
theorem adjoint_comp_isometryBlock_eq_zero (F₀ : L →ₗᵢ[𝕜] E) (F₁ : K₁ →ₗᵢ[𝕜] E)
    (hF : F₀.toLinearMap ∘ₗ LinearMap.adjoint F₀.toLinearMap +
        F₁.toLinearMap ∘ₗ LinearMap.adjoint F₁.toLinearMap = LinearMap.id) :
    LinearMap.adjoint F₀.toLinearMap ∘ₗ F₁.toLinearMap = 0 := by
  ext y
  have hy := LinearMap.congr_fun hF (F₁ y)
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearIsometry.coe_toLinearMap] at hy
  rw [LinearIsometry.adjoint_apply_apply] at hy
  have h0 : F₀ (LinearMap.adjoint F₀.toLinearMap (F₁ y)) = 0 := by
    have := hy
    rwa [add_eq_right] at this
  have := congrArg (LinearMap.adjoint F₀.toLinearMap) h0
  rw [map_zero, LinearIsometry.adjoint_apply_apply] at this
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply,
    LinearIsometry.coe_toLinearMap] using this

/-- **The Section 7 reflected cross block.**  With `X = 2 E₀E₀⋆ - 1` the
reflection in the range of `E₀`, the cross block between the reflected subspace
`X(range F₀)` and `range F₁` is

`(X F₀)⋆ F₁ = 2 (F₀⋆E₀)(E₀⋆F₁)`.

This is the displayed identity `(XF₀)⋆F₁ = 2(F₀⋆E₀)(E₀⋆F₁)` in the proof of the
`sin 2θ` theorem of Davis--Kahan 1970, Section 7.  It is pure block algebra and
uses no comparison of dimensions. -/
theorem adjoint_reflection_comp_isometryBlock (E₀ : K₀ →ₗᵢ[𝕜] E) (F₀ : L →ₗᵢ[𝕜] E)
    (F₁ : K₁ →ₗᵢ[𝕜] E)
    (hF : F₀.toLinearMap ∘ₗ LinearMap.adjoint F₀.toLinearMap +
        F₁.toLinearMap ∘ₗ LinearMap.adjoint F₁.toLinearMap = LinearMap.id) :
    LinearMap.adjoint
        (((2 : 𝕜) • (E₀.toLinearMap ∘ₗ LinearMap.adjoint E₀.toLinearMap) -
          LinearMap.id) ∘ₗ F₀.toLinearMap) ∘ₗ F₁.toLinearMap =
      (2 : 𝕜) • ((LinearMap.adjoint F₀.toLinearMap ∘ₗ E₀.toLinearMap) ∘ₗ
        (LinearMap.adjoint E₀.toLinearMap ∘ₗ F₁.toLinearMap)) := by
  have hzero := adjoint_comp_isometryBlock_eq_zero F₀ F₁ hF
  have hX : LinearMap.adjoint
      ((2 : 𝕜) • (E₀.toLinearMap ∘ₗ LinearMap.adjoint E₀.toLinearMap) -
        LinearMap.id) =
      (2 : 𝕜) • (E₀.toLinearMap ∘ₗ LinearMap.adjoint E₀.toLinearMap) -
        LinearMap.id := by
    rw [map_sub, map_smulₛₗ, map_ofNat, LinearMap.adjoint_comp,
      LinearMap.adjoint_adjoint, LinearMap.adjoint_id]
  rw [LinearMap.adjoint_comp, hX]
  ext y
  have hy := LinearMap.congr_fun hzero y
  simp only [LinearMap.comp_apply, LinearMap.zero_apply,
    LinearIsometry.coe_toLinearMap] at hy
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.id_apply, map_sub, map_smul, hy, sub_zero,
    LinearIsometry.coe_toLinearMap]

/-- **The reflected cross block carries `sin 2Θ₀`.**  Under the Davis--Kahan
block hypotheses the Gram operator of `(X F₀)⋆ F₁` is `4 (M - M²)` for
`M = T⋆T`, `T = E₀⋆F₁`.

So its singular values are `2 s √(1 - s²) = sin 2θ` for `s = sin θ` a singular
value of `E₀⋆F₁` — exactly the identification of the reflected cross block with
a `sin 2Θ₀` representative in Davis--Kahan 1970, Section 7.  **No hypothesis
relating `dim (range E₀)` to `dim (range F₀)` is used**, and no direct rotation
appears; the singular data of `E₀⋆F₁` is the same rectangular one-sided sine
data that Theorems 6.1 and 6.3 use.  This is what makes the announced extension
of the `sin 2θ` theorem to `dim 𝔛(E₀) < dim 𝔛(F₀)` possible. -/
theorem gram_adjoint_reflection_comp_isometryBlock (E₀ : K₀ →ₗᵢ[𝕜] E)
    (F₀ : L →ₗᵢ[𝕜] E) (F₁ : K₁ →ₗᵢ[𝕜] E)
    (hF : F₀.toLinearMap ∘ₗ LinearMap.adjoint F₀.toLinearMap +
        F₁.toLinearMap ∘ₗ LinearMap.adjoint F₁.toLinearMap = LinearMap.id) :
    LinearMap.adjoint (LinearMap.adjoint
          (((2 : 𝕜) • (E₀.toLinearMap ∘ₗ LinearMap.adjoint E₀.toLinearMap) -
            LinearMap.id) ∘ₗ F₀.toLinearMap) ∘ₗ F₁.toLinearMap) ∘ₗ
        (LinearMap.adjoint
          (((2 : 𝕜) • (E₀.toLinearMap ∘ₗ LinearMap.adjoint E₀.toLinearMap) -
            LinearMap.id) ∘ₗ F₀.toLinearMap) ∘ₗ F₁.toLinearMap) =
      (4 : 𝕜) • ((LinearMap.adjoint (LinearMap.adjoint E₀.toLinearMap ∘ₗ
            F₁.toLinearMap) ∘ₗ (LinearMap.adjoint E₀.toLinearMap ∘ₗ F₁.toLinearMap)) -
        (LinearMap.adjoint (LinearMap.adjoint E₀.toLinearMap ∘ₗ F₁.toLinearMap) ∘ₗ
            (LinearMap.adjoint E₀.toLinearMap ∘ₗ F₁.toLinearMap)) ∘ₗ
          (LinearMap.adjoint (LinearMap.adjoint E₀.toLinearMap ∘ₗ F₁.toLinearMap) ∘ₗ
            (LinearMap.adjoint E₀.toLinearMap ∘ₗ F₁.toLinearMap))) := by
  rw [adjoint_reflection_comp_isometryBlock E₀ F₀ F₁ hF]
  exact gram_two_smul_comp (gram_isometryBlock_eq_id_sub E₀ F₀ F₁ hF)

end IsometryBlocks

/-! ### The ambient projector form -/

section Projectors

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- **`sin 2Θ = 2 sin Θ cos Θ` for a pair of subspaces, at the Gram level.**
The Gram operator of the one-sided double-angle map `2 P_{Uᗮ} P_V P_U` is
`4 (M - M²)`, where `M` is the Gram operator of the cosine cross projection
`P_V P_U`.

Since the eigenvalues of `M` are the squared principal cosines `c²`, the squared
singular values of `sinTwoAngleOperator U V` are `4 c² (1 - c²) = sin² 2θ`.

**There is no equal-dimension hypothesis**, and none is available: `U` and `V`
are arbitrary.  This is the projector-side statement of the same fact that
`TauCeti.gram_adjoint_reflection_comp_isometryBlock` records in isometry-block
coordinates. -/
theorem gram_sinTwoAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    LinearMap.adjoint (sinTwoAngleOperator U V) ∘ₗ sinTwoAngleOperator U V =
      (4 : 𝕜) • ((LinearMap.adjoint (cosThetaMap U V) ∘ₗ cosThetaMap U V) -
        (LinearMap.adjoint (cosThetaMap U V) ∘ₗ cosThetaMap U V) ∘ₗ
          (LinearMap.adjoint (cosThetaMap U V) ∘ₗ cosThetaMap U V)) := by
  have hidem : ∀ (W : Submodule 𝕜 E) [W.HasOrthogonalProjection] (x : E),
      projection W (projection W x) = projection W x := by
    intro W _ x
    exact Submodule.starProjection_eq_self_iff.mpr (W.starProjection_apply_mem x)
  have hcomp : ∀ (W : Submodule 𝕜 E) [W.HasOrthogonalProjection] (x : E),
      complementaryProjection W x = x - projection W x := by
    intro W _ x
    rw [complementaryProjection, projection, projection,
      Submodule.starProjection_orthogonal]
    simp
  have hadjCos : LinearMap.adjoint (cosThetaMap U V) =
      projection U ∘ₗ projection V := by
    rw [cosThetaMap, LinearMap.adjoint_comp, projection_adjoint, projection_adjoint]
  have hadjSin : LinearMap.adjoint (sinTwoAngleOperator U V) =
      (2 : 𝕜) • (projection U ∘ₗ projection V ∘ₗ complementaryProjection U) := by
    rw [sinTwoAngleOperator_eq_two_smul_cross, map_smulₛₗ, map_ofNat,
      LinearMap.adjoint_comp, LinearMap.adjoint_comp, complementaryProjection,
      projection_adjoint, projection_adjoint, projection_adjoint]
    rfl
  rw [hadjSin, hadjCos, sinTwoAngleOperator_eq_two_smul_cross]
  ext x
  simp only [cosThetaMap, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, map_smul, hcomp, map_sub, hidem]
  module

end Projectors

end TauCeti
