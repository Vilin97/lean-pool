/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.AngleTransport
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.DirectedAngleRealTransport
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedKyFan
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTwoThetaReflectionAmbient
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.RealAngleIdentification
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.ComplexificationGauge
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedGramReal
import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotationReal

/-! # Tangent Transport -/

open TauCeti.DavisKahan.Angle


/-!
# The unbounded `tan 2Θ` block, and its transport to the paper's tangent

`unboundedReflectionTangent U Z = S · (C²)⁻¹ · C`, with `C = U.diagonalPart Z`
and `S = U.offDiagonalPart Z` the blocks of a self-adjoint involution `Z`
relative to `U ⊕ Uᗮ`.  Like the `sin 2Θ` block it is a proof vehicle, and the
question is what a symmetric ideal sees in it.

## The answer

For the reflection in `V` the block **is** the paper's block representative, up
to a reflection:

`unboundedReflectionTangent U (J_V) = Ξ · J_U`,

where `Ξ = tanTwoBlockRepresentative U V`.  `J_U` is a self-adjoint unitary,
so the two have the same approximation numbers, and
`absTanTwoAngleOperatorC_eq_modulus_blockRepresentative` says `|Ξ|` is the
paper's ambient `|tan 2Θ|`.  Hence

`N(unboundedReflectionTangent U J_V) = N(|tan 2Θ|)`

for every source unitarily invariant norm, with membership transferring both
ways.  The proof block can therefore disappear from the unbounded conclusion, as
it did for `sin 2Θ` in `AngleTransport`.

The cancellation is exact rather than approximate: the tangent's `(C²)⁻¹ C`
factor carries the signed doubled cosine `1 - 2(P_V - P_U)²`, which is precisely
what the block representative's secant inverts, and `J_U` is what is left.

## The block algebra underneath

Two identities, both `Z⋆ = Z` and `Z² = 1` read on and off the diagonal:

`C² + S² = 1`  and  `C S + S C = 0`.

The anticommutation makes `S²` commute with `C`, hence with `(C²)⁻¹`, and
`gram_unboundedReflectionTangent` collapses to `T⋆T = S² (1 - S²)⁻¹`: the tangent
is a function of `S` alone, `S/√(1-S²)`.
`starProjection_offDiagonal_sq_reflection` identifies the `U` block of `S²` as
`(sin 2Θ)²`, so on `U` the tangent is `sin 2Θ / cos 2Θ`.

Both routes are kept.  The Gram route says what the object *is* without any
invertibility hypothesis on the diagonal block; the transport route needs
`cos 2θ ≠ 0` on the spectrum, which is the hypothesis that makes `tan 2Θ` a
bounded operator at all.
-/

namespace TauCeti
namespace DavisKahan

open TauCeti.DavisKahanExt

open TauCeti.DavisKahan1970 TauCeti.DavisKahanExt

universe v

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

section BlockAlgebra

variable {p p' z : E →L[𝕜] E}

omit [CompleteSpace E] in
private theorem block_sq_add
    (hp : p * p = p) (hp' : p' * p' = p') (hpp' : p * p' = 0) (hp'p : p' * p = 0)
    (hsum : p + p' = 1) (hz : z * z = 1) :
    (p * z * p + p' * z * p') * (p * z * p + p' * z * p')
      + (p * z * p' + p' * z * p) * (p * z * p' + p' * z * p) = 1 := by
  have a1 : ∀ x : E →L[𝕜] E, p * (p * x) = p * x := fun x => by rw [← mul_assoc, hp]
  have a2 : ∀ x : E →L[𝕜] E, p' * (p' * x) = p' * x := fun x => by rw [← mul_assoc, hp']
  have a3 : ∀ x : E →L[𝕜] E, p * (p' * x) = 0 := fun x => by
    rw [← mul_assoc, hpp', zero_mul]
  have a4 : ∀ x : E →L[𝕜] E, p' * (p * x) = 0 := fun x => by
    rw [← mul_assoc, hp'p, zero_mul]
  have hzz : ∀ x : E →L[𝕜] E, z * (z * x) = x := fun x => by rw [← mul_assoc, hz, one_mul]
  simp only [add_mul, mul_add, mul_assoc, a1, a2, a3, a4, mul_zero, add_zero, zero_add]
  calc p * (z * (p * (z * p))) + p' * (z * (p' * (z * p')))
        + (p' * (z * (p * (z * p'))) + p * (z * (p' * (z * p))))
      = p * (z * ((p + p') * (z * p))) + p' * (z * ((p' + p) * (z * p'))) := by
        simp only [add_mul, mul_add]; abel
    _ = p * (z * (z * p)) + p' * (z * (z * p')) := by
        rw [hsum, add_comm p' p, hsum]; simp
    _ = 1 := by rw [hzz, hzz, hp, hp', hsum]

omit [CompleteSpace E] in
private theorem block_anticomm
    (hp : p * p = p) (hp' : p' * p' = p') (hpp' : p * p' = 0) (hp'p : p' * p = 0)
    (hsum : p + p' = 1) (hz : z * z = 1) :
    (p * z * p + p' * z * p') * (p * z * p' + p' * z * p)
      + (p * z * p' + p' * z * p) * (p * z * p + p' * z * p') = 0 := by
  have a1 : ∀ x : E →L[𝕜] E, p * (p * x) = p * x := fun x => by rw [← mul_assoc, hp]
  have a2 : ∀ x : E →L[𝕜] E, p' * (p' * x) = p' * x := fun x => by rw [← mul_assoc, hp']
  have a3 : ∀ x : E →L[𝕜] E, p * (p' * x) = 0 := fun x => by
    rw [← mul_assoc, hpp', zero_mul]
  have a4 : ∀ x : E →L[𝕜] E, p' * (p * x) = 0 := fun x => by
    rw [← mul_assoc, hp'p, zero_mul]
  have hzz : ∀ x : E →L[𝕜] E, z * (z * x) = x := fun x => by rw [← mul_assoc, hz, one_mul]
  simp only [add_mul, mul_add, mul_assoc, a1, a2, a3, a4, mul_zero, add_zero, zero_add]
  calc p * (z * (p * (z * p'))) + p' * (z * (p' * (z * p)))
        + (p' * (z * (p * (z * p))) + p * (z * (p' * (z * p'))))
      = p * (z * ((p + p') * (z * p'))) + p' * (z * ((p' + p) * (z * p))) := by
        simp only [add_mul, mul_add]; abel
    _ = p * (z * (z * p')) + p' * (z * (z * p)) := by
        rw [hsum, add_comm p' p, hsum]; simp
    _ = 0 := by rw [hzz, hzz, hpp', hp'p]; abel

end BlockAlgebra


section Blocks

variable (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (Z : E →L[𝕜] E)

omit [CompleteSpace E] in
private theorem orthogonal_eq :
    Uᗮ.starProjection = (1 : E →L[𝕜] E) - U.starProjection := by
  ext x
  simp

omit [CompleteSpace E] in
private theorem proj_sq : U.starProjection * U.starProjection = U.starProjection := by
  ext x
  change U.starProjection (U.starProjection x) = U.starProjection x
  rw [Submodule.starProjection_eq_self_iff]
  exact U.starProjection_apply_mem x

omit [CompleteSpace E] in
private theorem proj_mul_orthogonal :
    U.starProjection * Uᗮ.starProjection = 0 := by
  rw [orthogonal_eq, mul_sub, mul_one, proj_sq, sub_self]

omit [CompleteSpace E] in
private theorem orthogonal_mul_proj :
    Uᗮ.starProjection * U.starProjection = 0 := by
  rw [orthogonal_eq, sub_mul, one_mul, proj_sq, sub_self]

omit [CompleteSpace E] in
private theorem orthogonal_sq :
    Uᗮ.starProjection * Uᗮ.starProjection = Uᗮ.starProjection := by
  rw [orthogonal_eq]
  have h := proj_sq (𝕜 := 𝕜) U
  noncomm_ring [h]

omit [CompleteSpace E] in
private theorem proj_add_orthogonal :
    U.starProjection + Uᗮ.starProjection = (1 : E →L[𝕜] E) := by
  rw [orthogonal_eq]; abel

omit [CompleteSpace E] in
/-- The diagonal part written as the two corner products. -/
theorem diagonalPart_eq_corners :
    U.diagonalPart Z
      = U.starProjection * Z * U.starProjection
        + Uᗮ.starProjection * Z * Uᗮ.starProjection := by
  rw [Submodule.diagonalPart_eq]
  rfl

omit [CompleteSpace E] in
/-- The off-diagonal part written as the two corner products. -/
theorem offDiagonalPart_eq_corners :
    U.offDiagonalPart Z
      = U.starProjection * Z * Uᗮ.starProjection
        + Uᗮ.starProjection * Z * U.starProjection := by
  have hsum := proj_add_orthogonal (𝕜 := 𝕜) U
  have hZ : Z = (U.starProjection + Uᗮ.starProjection) * Z
      * (U.starProjection + Uᗮ.starProjection) := by
    rw [hsum, one_mul, mul_one]
  rw [Submodule.offDiagonalPart_eq, diagonalPart_eq_corners]
  nth_rewrite 1 [hZ]
  noncomm_ring

end Blocks


section Identities

variable (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] {Z : E →L[𝕜] E}

omit [CompleteSpace E] in
/-- **`C² + S² = 1`.**  The blocks of a self-adjoint involution relative to
`U ⊕ Uᗮ` satisfy the Pythagorean identity: this is `Z² = 1` read on the diagonal. -/
theorem diagonalPart_sq_add_offDiagonalPart_sq (hZ : Z * Z = 1) :
    U.diagonalPart Z * U.diagonalPart Z
        + U.offDiagonalPart Z * U.offDiagonalPart Z = 1 := by
  rw [diagonalPart_eq_corners, offDiagonalPart_eq_corners]
  exact block_sq_add (proj_sq U) (orthogonal_sq U) (proj_mul_orthogonal U)
    (orthogonal_mul_proj U) (proj_add_orthogonal U) hZ

omit [CompleteSpace E] in
/-- **`C S + S C = 0`.**  The same identity read off the diagonal: the two blocks
of a self-adjoint involution anticommute. -/
theorem diagonalPart_anticommute_offDiagonalPart (hZ : Z * Z = 1) :
    U.diagonalPart Z * U.offDiagonalPart Z
        + U.offDiagonalPart Z * U.diagonalPart Z = 0 := by
  rw [diagonalPart_eq_corners, offDiagonalPart_eq_corners]
  exact block_anticomm (proj_sq U) (orthogonal_sq U) (proj_mul_orthogonal U)
    (orthogonal_mul_proj U) (proj_add_orthogonal U) hZ

omit [CompleteSpace E] in
/-- Anticommuting with `C` makes `S²` *commute* with `C`. -/
theorem offDiagonalPart_sq_commute_diagonalPart (hZ : Z * Z = 1) :
    U.offDiagonalPart Z * U.offDiagonalPart Z * U.diagonalPart Z
      = U.diagonalPart Z * (U.offDiagonalPart Z * U.offDiagonalPart Z) := by
  have h := diagonalPart_anticommute_offDiagonalPart U hZ
  have h1 : U.offDiagonalPart Z * U.diagonalPart Z
      = -(U.diagonalPart Z * U.offDiagonalPart Z) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
  calc U.offDiagonalPart Z * U.offDiagonalPart Z * U.diagonalPart Z
      = U.offDiagonalPart Z * (U.offDiagonalPart Z * U.diagonalPart Z) := by
        rw [mul_assoc]
    _ = U.offDiagonalPart Z * -(U.diagonalPart Z * U.offDiagonalPart Z) := by rw [h1]
    _ = -((U.offDiagonalPart Z * U.diagonalPart Z) * U.offDiagonalPart Z) := by
        noncomm_ring
    _ = -(-(U.diagonalPart Z * U.offDiagonalPart Z) * U.offDiagonalPart Z) := by rw [h1]
    _ = U.diagonalPart Z * (U.offDiagonalPart Z * U.offDiagonalPart Z) := by
        noncomm_ring


omit [CompleteSpace E] in
/-- The `U` corner of `S²`: only the `(1,2)(2,1)` product survives. -/
theorem corner_offDiagonalPart_sq (Z : E →L[𝕜] E) :
    U.starProjection * (U.offDiagonalPart Z * U.offDiagonalPart Z) * U.starProjection
      = U.starProjection * Z * Uᗮ.starProjection * Z * U.starProjection := by
  have a1 : ∀ x : E →L[𝕜] E, U.starProjection * (U.starProjection * x)
      = U.starProjection * x := fun x => by rw [← mul_assoc, proj_sq U]
  have a2 : ∀ x : E →L[𝕜] E, Uᗮ.starProjection * (Uᗮ.starProjection * x)
      = Uᗮ.starProjection * x := fun x => by rw [← mul_assoc, orthogonal_sq U]
  have a3 : ∀ x : E →L[𝕜] E, U.starProjection * (Uᗮ.starProjection * x) = 0 :=
    fun x => by rw [← mul_assoc, proj_mul_orthogonal U, zero_mul]
  have a4 : ∀ x : E →L[𝕜] E, Uᗮ.starProjection * (U.starProjection * x) = 0 :=
    fun x => by rw [← mul_assoc, orthogonal_mul_proj U, zero_mul]
  rw [offDiagonalPart_eq_corners]
  simp only [add_mul, mul_add, mul_assoc, a1, a2, a3, a4, mul_zero,
    add_zero, zero_add, proj_sq U]

private theorem commute_ring_inverse {A : Type*} [Ring A] {u x : A}
    (hu : IsUnit u) (h : x * u = u * x) :
    x * Ring.inverse u = Ring.inverse u * x := by
  have h1 : u * Ring.inverse u = 1 := Ring.mul_inverse_cancel u hu
  have h2 : Ring.inverse u * u = 1 := Ring.inverse_mul_cancel u hu
  calc x * Ring.inverse u
      = Ring.inverse u * u * (x * Ring.inverse u) := by rw [h2, one_mul]
    _ = Ring.inverse u * (u * x) * Ring.inverse u := by noncomm_ring
    _ = Ring.inverse u * (x * u) * Ring.inverse u := by rw [h]
    _ = Ring.inverse u * x * (u * Ring.inverse u) := by noncomm_ring
    _ = Ring.inverse u * x := by rw [h1, mul_one]

/-- **The Gram operator of the unbounded reflection tangent.**

`T⋆T = S² (1 - S²)⁻¹`, where `S` is the off-diagonal block.  So the tangent is a
function of `S` alone -- `S/√(1-S²)`, the tangent of the angle whose sine is `S`
-- and the diagonal block has cancelled out entirely.

Everything a unitarily invariant norm sees in `unboundedReflectionTangent` is
therefore determined by `S`. -/
theorem gram_unboundedReflectionTangent
    (hZsa : IsSelfAdjoint Z) (hZ : Z * Z = 1)
    (hCC : IsUnit (U.diagonalPart Z * U.diagonalPart Z)) :
    (unboundedReflectionTangent U Z).adjoint * unboundedReflectionTangent U Z
      = U.offDiagonalPart Z * U.offDiagonalPart Z *
          Ring.inverse (U.diagonalPart Z * U.diagonalPart Z) := by
  set C := U.diagonalPart Z with hCdef
  set S := U.offDiagonalPart Z with hSdef
  have hCsa : IsSelfAdjoint C := TauCeti.isSelfAdjoint_diagonalPart hZsa
  have hSsa : IsSelfAdjoint S := TauCeti.isSelfAdjoint_offDiagonalPart hZsa
  have hCCsa : star (C * C) = C * C := by
    rw [star_mul, hCsa.star_eq]
  have hJC : Ring.inverse (C * C) * (C * C) = 1 := Ring.inverse_mul_cancel _ hCC
  have hCJ : C * C * Ring.inverse (C * C) = 1 := Ring.mul_inverse_cancel _ hCC
  have hInvsa : star (Ring.inverse (C * C)) = Ring.inverse (C * C) := by
    have h2 := congrArg star hCJ
    rw [star_mul, hCCsa, star_one] at h2
    calc star (Ring.inverse (C * C))
        = star (Ring.inverse (C * C)) * (C * C * Ring.inverse (C * C)) := by
          rw [hCJ, mul_one]
      _ = star (Ring.inverse (C * C)) * (C * C) * Ring.inverse (C * C) :=
          (mul_assoc _ _ _).symm
      _ = Ring.inverse (C * C) := by rw [h2, one_mul]
  have hcomm : S * S * C = C * (S * S) :=
    offDiagonalPart_sq_commute_diagonalPart U hZ
  have hcommCC : S * S * (C * C) = C * C * (S * S) := by
    calc S * S * (C * C) = S * S * C * C := (mul_assoc _ _ _).symm
      _ = C * (S * S) * C := by rw [hcomm]
      _ = C * (S * S * C) := mul_assoc _ _ _
      _ = C * (C * (S * S)) := by rw [hcomm]
      _ = C * C * (S * S) := (mul_assoc _ _ _).symm
  have hcommInv : S * S * Ring.inverse (C * C)
      = Ring.inverse (C * C) * (S * S) := commute_ring_inverse hCC hcommCC
  have hCinv : C * Ring.inverse (C * C) = Ring.inverse (C * C) * C := by
    refine commute_ring_inverse hCC ?_
    rw [← mul_assoc]
  -- `C J J C = J`: the diagonal block cancels against the inverse of its square.
  have hCJJC : C * Ring.inverse (C * C) * (Ring.inverse (C * C) * C)
      = Ring.inverse (C * C) := by
    calc C * Ring.inverse (C * C) * (Ring.inverse (C * C) * C)
        = Ring.inverse (C * C) * C * (Ring.inverse (C * C) * C) := by rw [hCinv]
      _ = Ring.inverse (C * C) * (C * Ring.inverse (C * C)) * C := by
          simp only [mul_assoc]
      _ = Ring.inverse (C * C) * (Ring.inverse (C * C) * C) * C := by rw [hCinv]
      _ = Ring.inverse (C * C) * (Ring.inverse (C * C) * (C * C)) := by
          simp only [mul_assoc]
      _ = Ring.inverse (C * C) := by rw [hJC, mul_one]
  have hadj : (unboundedReflectionTangent U Z).adjoint
      = C * Ring.inverse (C * C) * S := by
    rw [unboundedReflectionTangent, ← ContinuousLinearMap.star_eq_adjoint,
      star_mul, star_mul, hCsa.star_eq, hSsa.star_eq, hInvsa, ← mul_assoc]
  rw [hadj, unboundedReflectionTangent]
  calc C * Ring.inverse (C * C) * S * (S * Ring.inverse (C * C) * C)
      = C * Ring.inverse (C * C) * (S * S * Ring.inverse (C * C) * C) := by
        simp only [mul_assoc]
    _ = C * Ring.inverse (C * C) * (Ring.inverse (C * C) * (S * S) * C) := by
        rw [hcommInv]
    _ = C * Ring.inverse (C * C) * (Ring.inverse (C * C) * (S * S * C)) := by
        simp only [mul_assoc]
    _ = C * Ring.inverse (C * C) * (Ring.inverse (C * C) * (C * (S * S))) := by
        rw [hcomm]
    _ = C * Ring.inverse (C * C) * (Ring.inverse (C * C) * C) * (S * S) := by
        simp only [mul_assoc]
    _ = Ring.inverse (C * C) * (S * S) := by rw [hCJJC]
    _ = S * S * Ring.inverse (C * C) := hcommInv.symm

/-- **The tangent's Gram operator, with the diagonal block eliminated.**

`T⋆T = S² (1 - S²)⁻¹`.  Combined with
`starProjection_offDiagonal_sq_reflection`, which identifies the `U` block of
`S²` as `(sin 2Θ)²`, this is the statement that the unbounded reflection tangent
is `sin 2Θ / cos 2Θ` there. -/
theorem gram_unboundedReflectionTangent_eq_offDiagonal
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] {Z : E →L[𝕜] E}
    (hZsa : IsSelfAdjoint Z) (hZ : Z * Z = 1)
    (hCC : IsUnit (U.diagonalPart Z * U.diagonalPart Z)) :
    (unboundedReflectionTangent U Z).adjoint * unboundedReflectionTangent U Z
      = U.offDiagonalPart Z * U.offDiagonalPart Z *
          Ring.inverse ((1 : E →L[𝕜] E)
            - U.offDiagonalPart Z * U.offDiagonalPart Z) := by
  have hpy : U.diagonalPart Z * U.diagonalPart Z
      = (1 : E →L[𝕜] E) - U.offDiagonalPart Z * U.offDiagonalPart Z := by
    rw [eq_sub_iff_add_eq]
    exact diagonalPart_sq_add_offDiagonalPart_sq U hZ
  rw [gram_unboundedReflectionTangent U hZsa hZ hCC, hpy]

end Identities

section Reflection


variable {Ec : Type v} [NormedAddCommGroup Ec] [InnerProductSpace ℂ Ec]
  [CompleteSpace Ec]

/-- **The `U` block of `S²` is `(sin 2Θ)²`.**

For the reflection in `V`, the off-diagonal block `S` of the reflection relative
to `U ⊕ Uᗮ` squares, on `U`, to the square of the paper's double-angle sine.
Together with `gram_unboundedReflectionTangent` this says the tangent is
`sin 2Θ / cos 2Θ` there: the `U` block of `T⋆T` is `sin²2Θ · (1 - sin²2Θ)⁻¹`. -/
theorem starProjection_offDiagonal_sq_reflection
    (U V : Submodule ℂ Ec) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.starProjection *
        (U.offDiagonalPart V.reflectionOperator *
          U.offDiagonalPart V.reflectionOperator) * U.starProjection
      = directedSinTwoAngleOperatorC U V * directedSinTwoAngleOperatorC U V := by
  rw [corner_offDiagonalPart_sq]
  have hRR : V.reflectionOperator * V.reflectionOperator = 1 :=
    V.reflectionOperator_involutive
  have hcompl : Uᗮ.starProjection = (1 : Ec →L[ℂ] Ec) - U.starProjection :=
    orthogonal_eq U
  have hangle : directedSinTwoAngleOperatorC U V * directedSinTwoAngleOperatorC U V
      = U.starProjection * ((reflectedU U V)ᗮ.starProjection) * U.starProjection := by
    rw [← directedSinAngleOperatorC_reflected_eq_directedSinTwoAngleOperatorC U V,
      directedSinAngleOperatorC_mul_self]
  rw [hangle, starProjection_orthogonal_eq (reflectedU U V), starProjection_reflectedU,
    hcompl]
  have hRform : (2 : Ec →L[ℂ] Ec) * V.starProjection - 1 = V.reflectionOperator := by
    rw [V.reflectionOperator_eq_two_smul_sub_id]
    ext x
    simp [two_smul]
  rw [hRform]
  have hpp : U.starProjection * U.starProjection = U.starProjection := proj_sq U
  calc U.starProjection * V.reflectionOperator *
        ((1 : Ec →L[ℂ] Ec) - U.starProjection) * V.reflectionOperator *
          U.starProjection
      = U.starProjection * (V.reflectionOperator * V.reflectionOperator) *
            U.starProjection
        - U.starProjection * V.reflectionOperator * U.starProjection *
            V.reflectionOperator * U.starProjection := by noncomm_ring
    _ = U.starProjection * ((1 : Ec →L[ℂ] Ec) -
            V.reflectionOperator * U.starProjection * V.reflectionOperator) *
          U.starProjection := by
        rw [hRR]; noncomm_ring

end Reflection

section PaperTangent

open TauCeti.DavisKahan1970 TauCeti.DavisKahanExt

variable {Ec : Type v} [NormedAddCommGroup Ec] [InnerProductSpace ℂ Ec]
  [CompleteSpace Ec]
variable (U V : Submodule ℂ Ec) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

omit [CompleteSpace Ec] in
/-- The off-diagonal block of the reflection in `V`, in corner form. -/
theorem offDiagonalPart_reflection_eq :
    U.offDiagonalPart V.reflectionOperator
      = 2 * (((1 : Ec →L[ℂ] Ec) - U.starProjection) *
            projectorDifference U V * U.starProjection
          + U.starProjection * projectorDifference U V *
            ((1 : Ec →L[ℂ] Ec) - U.starProjection)) := by
  have hp : U.starProjection * U.starProjection = U.starProjection := proj_sq U
  have hQ : projectorDifference U V = V.starProjection - U.starProjection := rfl
  rw [Submodule.offDiagonalPart_eq, Submodule.diagonalPart_eq,
    Submodule.reflectionOperator_eq_two_smul_sub_id V]
  simp only [two_smul, Submodule.starProjection_orthogonal',
    show ∀ f g : Ec →L[ℂ] Ec, f ∘L g = f * g from fun _ _ => rfl]
  rw [hQ, ← ContinuousLinearMap.one_def]
  noncomm_ring [hp]

omit [CompleteSpace Ec] in
/-- **`Ξ · (1 - 2(P_V - P_U)²) = S`.**

The paper's block representative, multiplied on the right by the signed doubled
cosine, is exactly the off-diagonal block of the reflection.  The secant in the
representative cancels against the cosine; no commutation is needed because the
cancellation happens on the same side. -/
theorem tanTwoBlockRepresentative_mul_signedCosTwo
    (hinv : IsUnit ((1 : Ec →L[ℂ] Ec) - 2 * (projectorDifference U V *
      projectorDifference U V))) :
    tanTwoBlockRepresentative U V * signedCosTwo U V
      = U.offDiagonalPart V.reflectionOperator := by
  have hsec : doubleSecant U V * signedCosTwo U V = 1 :=
    Ring.inverse_mul_cancel _ hinv
  rw [tanTwoBlockRepresentative_eq hinv, offDiagonalPart_reflection_eq]
  calc 2 * ((((1 : Ec →L[ℂ] Ec) - U.starProjection) *
          projectorDifference U V * U.starProjection
        + U.starProjection * projectorDifference U V *
          ((1 : Ec →L[ℂ] Ec) - U.starProjection)) * doubleSecant U V)
        * signedCosTwo U V
      = 2 * ((((1 : Ec →L[ℂ] Ec) - U.starProjection) *
            projectorDifference U V * U.starProjection
          + U.starProjection * projectorDifference U V *
            ((1 : Ec →L[ℂ] Ec) - U.starProjection)) *
              (doubleSecant U V * signedCosTwo U V)) := by noncomm_ring
    _ = _ := by rw [hsec, mul_one]

omit [CompleteSpace Ec] in
/-- **The unbounded reflection tangent is the paper's block representative, times
a reflection.**

`T = Ξ · J_U`.  The signed cosine that the tangent's `(C²)⁻¹ C` factor carries is
exactly the one the block representative's secant inverts, and what is left over
is the reflection in `U` -- a self-adjoint unitary, so it changes nothing a
unitarily invariant norm can see. -/
theorem unboundedReflectionTangent_reflection_eq
    (hinv : IsUnit ((1 : Ec →L[ℂ] Ec) - 2 * (projectorDifference U V *
      projectorDifference U V))) :
    unboundedReflectionTangent U V.reflectionOperator
      = tanTwoBlockRepresentative U V * U.reflectionOperator := by
  have hRU : U.reflectionOperator * U.reflectionOperator = 1 :=
    U.reflectionOperator_involutive
  have hK : signedCosTwo U V = (1 : Ec →L[ℂ] Ec) - 2 * (projectorDifference U V *
      projectorDifference U V) := rfl
  have hKunit : IsUnit (signedCosTwo U V) := by rw [hK]; exact hinv
  have hdiag : U.diagonalPart V.reflectionOperator
      = U.reflectionOperator * signedCosTwo U V :=
    diagonalPart_reflection_eq_reflection_mul_signedCosTwo
  have hoff : U.offDiagonalPart V.reflectionOperator
      = tanTwoBlockRepresentative U V * signedCosTwo U V :=
    (tanTwoBlockRepresentative_mul_signedCosTwo U V hinv).symm
  -- the signed cosine commutes with the reflection in `U`
  have hKP : signedCosTwo U V * U.starProjection
      = U.starProjection * signedCosTwo U V := signedCosTwo_comm_starProjection
  have hKR : signedCosTwo U V * U.reflectionOperator
      = U.reflectionOperator * signedCosTwo U V := by
    rw [Submodule.reflectionOperator_eq_two_smul_sub_id U]
    have h2 : ((2 : ℂ) • U.starProjection - ContinuousLinearMap.id ℂ Ec)
        = 2 * U.starProjection - 1 := by ext x; simp [two_smul]
    rw [h2, mul_sub, sub_mul, mul_one, one_mul]
    have h2c : signedCosTwo U V * (2 * U.starProjection)
        = 2 * (signedCosTwo U V * U.starProjection) := by noncomm_ring
    rw [h2c, hKP]
    noncomm_ring
  -- the diagonal block squares to the signed cosine squared
  have hCC : U.diagonalPart V.reflectionOperator * U.diagonalPart V.reflectionOperator
      = signedCosTwo U V * signedCosTwo U V := by
    rw [hdiag]
    calc U.reflectionOperator * signedCosTwo U V *
          (U.reflectionOperator * signedCosTwo U V)
        = U.reflectionOperator * (signedCosTwo U V * U.reflectionOperator) *
            signedCosTwo U V := by noncomm_ring
      _ = U.reflectionOperator * (U.reflectionOperator * signedCosTwo U V) *
            signedCosTwo U V := by rw [hKR]
      _ = U.reflectionOperator * U.reflectionOperator *
            (signedCosTwo U V * signedCosTwo U V) := by noncomm_ring
      _ = signedCosTwo U V * signedCosTwo U V := by rw [hRU, one_mul]
  have hKKunit : IsUnit (signedCosTwo U V * signedCosTwo U V) := hKunit.mul hKunit
  have hKinv : signedCosTwo U V *
      Ring.inverse (signedCosTwo U V * signedCosTwo U V) *
        signedCosTwo U V = 1 := by
    have hcomm : signedCosTwo U V * (signedCosTwo U V * signedCosTwo U V)
        = signedCosTwo U V * signedCosTwo U V * signedCosTwo U V := by noncomm_ring
    have h := commute_ring_inverse hKKunit hcomm
    calc signedCosTwo U V * Ring.inverse (signedCosTwo U V * signedCosTwo U V) *
          signedCosTwo U V
        = Ring.inverse (signedCosTwo U V * signedCosTwo U V) * signedCosTwo U V *
            signedCosTwo U V := by rw [h]
      _ = Ring.inverse (signedCosTwo U V * signedCosTwo U V) *
            (signedCosTwo U V * signedCosTwo U V) := by noncomm_ring
      _ = 1 := Ring.inverse_mul_cancel _ hKKunit
  rw [unboundedReflectionTangent, hCC, hoff, hdiag]
  calc tanTwoBlockRepresentative U V * signedCosTwo U V *
        Ring.inverse (signedCosTwo U V * signedCosTwo U V) *
          (U.reflectionOperator * signedCosTwo U V)
      = tanTwoBlockRepresentative U V * (signedCosTwo U V *
          Ring.inverse (signedCosTwo U V * signedCosTwo U V) *
            (signedCosTwo U V * U.reflectionOperator)) := by
        rw [← hKR]; noncomm_ring
    _ = tanTwoBlockRepresentative U V * ((signedCosTwo U V *
          Ring.inverse (signedCosTwo U V * signedCosTwo U V) *
            signedCosTwo U V) * U.reflectionOperator) := by noncomm_ring
    _ = tanTwoBlockRepresentative U V * U.reflectionOperator := by
        rw [hKinv, one_mul]

/-! ### The pole hypothesis is a consequence, not an assumption

The unbounded `tan 2Θ` theorem's ordered-gap hypotheses already force the
diagonal block `C = U.diagonalPart J_V` to be invertible; that is the first
component of its conclusion.  And `C = J_U · (1 - 2(P_V - P_U)²)`, so a unit
diagonal block *is* a unit signed doubled cosine, which is exactly what excludes
the quarter-turn poles of `tan 2Θ`.  A caller therefore never has to certify
`cos 2θ ≠ 0` separately. -/

omit [CompleteSpace Ec] in
/-- **A unit diagonal block is a unit signed doubled cosine.**

`U.diagonalPart J_V = J_U · (1 - 2(P_V - P_U)²)` with `J_U` a self-adjoint
involution, hence a unit; and `IsUnit (C · C)` gives `IsUnit C` in any monoid. -/
theorem isUnit_signedCosTwo_of_isUnit_diagonalPart_sq
    (h : IsUnit (U.diagonalPart V.reflectionOperator *
      U.diagonalPart V.reflectionOperator)) :
    IsUnit ((1 : Ec →L[ℂ] Ec) - 2 * (projectorDifference U V *
      projectorDifference U V)) := by
  have hC : IsUnit (U.diagonalPart V.reflectionOperator) := by
    rw [← pow_two] at h
    exact (isUnit_pow_iff two_ne_zero).mp h
  have hJJ := TauCeti.DavisKahan.reflectionOperator_mul_self_complex U
  have hJU : IsUnit U.reflectionOperator :=
    ⟨⟨U.reflectionOperator, U.reflectionOperator, hJJ, hJJ⟩, rfl⟩
  have hK : signedCosTwo U V
      = U.reflectionOperator * U.diagonalPart V.reflectionOperator := by
    rw [diagonalPart_reflection_eq_reflection_mul_signedCosTwo, ← mul_assoc, hJJ,
      one_mul]
  have hunit : IsUnit (signedCosTwo U V) := by rw [hK]; exact hJU.mul hC
  simpa only [signedCosTwo] using hunit

/-- **The unbounded theorem's own conclusion excludes every quarter-turn pole.**

Composition of `isUnit_signedCosTwo_of_isUnit_diagonalPart_sq` with
`cos_two_ne_zero_of_isUnit_one_sub_two_mul_projectorDifference_sq`.  This is
what lets the source-facing `tan 2Θ` theorem state the paper's `|tan 2Θ|` without
asking its caller for an independent pole certificate. -/
theorem cos_two_ne_zero_of_isUnit_diagonalPart_reflection_sq
    (h : IsUnit (U.diagonalPart V.reflectionOperator *
      U.diagonalPart V.reflectionOperator)) :
    ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0 :=
  cos_two_ne_zero_of_isUnit_one_sub_two_mul_projectorDifference_sq
    (isUnit_signedCosTwo_of_isUnit_diagonalPart_sq U V h)

/-- **The reflection tangent and the paper's `|tan 2Θ|` have the same
approximation numbers.**

`T = Ξ · J_U` with `J_U` a self-adjoint unitary, so `T` and `Ξ` have the same
singular data; `|Ξ| = |tan 2Θ|` is
`absTanTwoAngleOperatorC_eq_modulus_blockRepresentative`, and a modulus has
the same approximation numbers as its operator.  Chaining the three gives the
transport. -/
theorem sameApproximationSingularValues_unboundedReflectionTangent
    (hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0) :
    ExactSinTheta.SameApproximationSingularValues
      (unboundedReflectionTangent U V.reflectionOperator)
      (absTanTwoAngleOperatorC U V) := by
  have hinv := isUnit_one_sub_two_mul_projectorDifference_sq_of_cos_two_ne_zero hcos
  have hrefl : U.reflectionOperator
      = U.reflection.toContinuousLinearEquiv.toContinuousLinearMap := by
    ext x; rfl
  have hcomp :
      (LinearIsometryEquiv.refl ℂ Ec).toContinuousLinearEquiv.toContinuousLinearMap ∘L
          tanTwoBlockRepresentative U V ∘L
            U.reflection.toContinuousLinearEquiv.toContinuousLinearMap
        = unboundedReflectionTangent U V.reflectionOperator := by
    rw [unboundedReflectionTangent_reflection_eq U V hinv, hrefl]
    ext x; rfl
  have h1 : ExactSinTheta.SameApproximationSingularValues
      (unboundedReflectionTangent U V.reflectionOperator)
      (tanTwoBlockRepresentative U V) := by
    rw [← hcomp]
    exact ExactSinTheta.SameApproximationSingularValues.comp_isometricEquiv
      (LinearIsometryEquiv.refl ℂ Ec) U.reflection
  intro n
  rw [h1 n, absTanTwoAngleOperatorC_eq_modulus_blockRepresentative hcos]
  exact (ContinuousLinearMap.modulus_hasSameApproximationNumbers
    (tanTwoBlockRepresentative U V) n).symm

/-- **The reflection tangent and the paper's `|tan 2Θ|` have the same gauge in
every source unitarily invariant norm**, and one lies in the norm's ideal exactly
when the other does. -/
theorem extendedGauge_unboundedReflectionTangent_complex
    (N : ExactSinTheta.SymmetricNormingFunction)
    (hcos : ∀ t ∈ spectrum ℝ (angleOperatorC U V), Real.cos (2 * t) ≠ 0) :
    N.extendedGauge (unboundedReflectionTangent U V.reflectionOperator)
      = N.extendedGauge (absTanTwoAngleOperatorC U V) :=
  N.gauge_eq_of_sameApproximationSingularValues
    (sameApproximationSingularValues_unboundedReflectionTangent U V hcos)

end PaperTangent


section RealAngle

open TauCeti.DavisKahanExt TauCeti.ApproximationNumber TauCeti.RealComplexification
  TauCeti.DavisKahan.Foundation.RealComplexification

variable {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er]
  [CompleteSpace Er]


/-- **The real reflection tangent and the real `|tan 2Θ|` have the same gauge in
every source unitarily invariant norm.**

The real counterpart of `extendedGauge_unboundedReflectionTangent_complex`, and, like it,
it asks for no independent pole certificate: the hypothesis is invertibility of
the reflection's diagonal block, which is what the unbounded `tan 2Θ` theorem
already delivers.

Everything descends through the complexification: the reflection in `V`
complexifies to the reflection in the complexified `V`, the reflection tangent
complexifies to the complex one, `absTanTwoAngleOperatorR` complexifies to
`absTanTwoAngleOperatorC`, and a source gauge is unchanged by
complexification.  No second analytic proof is involved. -/
theorem extendedGauge_unboundedReflectionTangent_real
    (U V : Submodule ℝ Er) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (N : ExactSinTheta.SymmetricNormingFunction)
    (hCC : IsUnit (U.diagonalPart V.reflectionOperator *
      U.diagonalPart V.reflectionOperator)) :
    N.extendedGauge (unboundedReflectionTangent U V.reflectionOperator)
      = N.extendedGauge (absTanTwoAngleOperatorR U V) := by
  have hZ : complexify V.reflectionOperator
      = (complexifySubmodule V).reflectionOperator :=
    complexify_reflectionOperator V
  have hCCc : IsUnit ((complexifySubmodule U).diagonalPart
        ((complexifySubmodule V).reflectionOperator) *
      (complexifySubmodule U).diagonalPart
        ((complexifySubmodule V).reflectionOperator)) := by
    rw [← hZ, diagonalPart_complexifySubmodule, ← complexify_mul,
      isUnit_complexify_iff]
    exact hCC
  have hcos := cos_two_ne_zero_of_isUnit_diagonalPart_reflection_sq
    (complexifySubmodule U) (complexifySubmodule V) hCCc
  have htrans := extendedGauge_unboundedReflectionTangent_complex
    (complexifySubmodule U) (complexifySubmodule V) N hcos
  rw [← ExactSinTheta.SymmetricNormingFunction.extendedGauge_complexify N
      (unboundedReflectionTangent U V.reflectionOperator),
    ← ExactSinTheta.SymmetricNormingFunction.extendedGauge_complexify N
      (absTanTwoAngleOperatorR U V),
    complexify_absTanTwoAngleOperatorR,
    ← unboundedReflectionTangent_complexifySubmodule U V.reflectionOperator hCC,
    hZ]
  exact htrans

end RealAngle

end DavisKahan
end TauCeti
