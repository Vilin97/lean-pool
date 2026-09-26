/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The two blocks of a self-adjoint involution

Let `Z` be a self-adjoint unitary — equivalently `Z⋆ = Z` and `Z² = 1` — and let
`U` be an orthogonally complemented subspace.  Read `Z` as a `2 × 2` matrix
against `U ⊕ Uᗮ`:

`Z = [[D₀, G⋆], [G, -D₁]]`.

This module records what `Z² = 1` says about the four blocks, in the
representation-free form

* `D := U.diagonalPart Z` — the block-diagonal part `diag (D₀, -D₁)`;
* `S := U.offDiagonalPart Z` — the block-off-diagonal part, carrying `G`.

Then `D` and `S` are self-adjoint, `D + S = Z`, and

`D² + S² = 1`,   `D S + S D = 0`.

Blockwise these are exactly `D₀² + G⋆G = 1`, `D₁² + G G⋆ = 1` and
`D₁ G = G D₀`, so the single pair of operator identities encodes the whole
double-angle geometry of the reflected pair.  For the Davis--Kahan reading
`D₀ = cos 2Θ₀`, `D₁ = cos 2Θ₁`, `|G| = sin 2Θ₀`, and `D² + S² = 1` is
`cos² 2Θ + sin² 2Θ = 1`.

The kinship to
`ForTauCeti/Analysis/InnerProductSpace/DoubleAngle/Gram.lean` is deliberate:
there the same doubled-angle geometry appears as `G⋆G = 4 M (1 - M)` for `M`
the principal-sine Gram operator of a *rectangular* cross block, here as
`G⋆G = 1 - D₀²` for the cross block of a reflection.  Both say that the Gram
operator of a doubled-angle cross block is a scalar functional expression in
the single-angle Gram operator.

## Main results

* `TauCeti.isSelfAdjoint_diagonalPart`, `TauCeti.isSelfAdjoint_offDiagonalPart`.
* `TauCeti.diagonalPart_sq_add_offDiagonalPart_sq`: `D² + S² = 1`.
* `TauCeti.diagonalPart_mul_offDiagonalPart_add_offDiagonalPart_mul_diagonalPart`:
  `D S + S D = 0`.
* `TauCeti.norm_sq_diagonalPart_add_norm_sq_offDiagonalPart_of_mem`: the vector
  form `‖D x‖² + ‖S x‖² = ‖x‖²` on `U` and on `Uᗮ`, proved from unitarity of
  `Z` alone.
* `TauCeti.diagonalPart_mem_of_mem`, `TauCeti.offDiagonalPart_mem_orthogonal_of_mem`
  and their mirrors: `D` is even and `S` is odd for the splitting `U ⊕ Uᗮ`.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46, Section 7 and the Appendix to
  Section 6: the reflection `Z = 2Q - 1` through a reducing subspace, and the
  block system its commutation with the operator produces.
-/

@[expose] public section

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]

section Parity

variable {U}

omit [U.HasOrthogonalProjection] in
/-- The complementary projection kills a vector of `U`. -/
theorem starProjection_orthogonal_eq_zero_of_mem [Uᗮ.HasOrthogonalProjection]
    {x : E} (hx : x ∈ U) : Uᗮ.starProjection x = 0 :=
  (Uᗮ.starProjection_apply_eq_zero_iff).mpr (U.le_orthogonal_orthogonal hx)

variable (U) in
/-- On `U` the diagonal part of `Z` is the `U`-component of `Z x`. -/
theorem diagonalPart_apply_of_mem (Z : E →L[𝕜] E) {x : E} (hx : x ∈ U) :
    U.diagonalPart Z x = U.starProjection (Z x) := by
  rw [Submodule.diagonalPart_apply, Submodule.starProjection_eq_self_iff.mpr hx,
    starProjection_orthogonal_eq_zero_of_mem hx, map_zero, map_zero, add_zero]

variable (U) in
/-- On `Uᗮ` the diagonal part of `Z` is the `Uᗮ`-component of `Z x`. -/
theorem diagonalPart_apply_of_mem_orthogonal (Z : E →L[𝕜] E) {x : E}
    (hx : x ∈ Uᗮ) : U.diagonalPart Z x = Uᗮ.starProjection (Z x) := by
  have h0 : U.starProjection x = 0 := (U.starProjection_apply_eq_zero_iff).mpr hx
  rw [Submodule.diagonalPart_apply, h0, map_zero, map_zero, zero_add,
    Submodule.starProjection_eq_self_iff.mpr hx]

variable (U) in
/-- On `U` the off-diagonal part of `Z` is the `Uᗮ`-component of `Z x`. -/
theorem offDiagonalPart_apply_of_mem (Z : E →L[𝕜] E) {x : E} (hx : x ∈ U) :
    U.offDiagonalPart Z x = Uᗮ.starProjection (Z x) := by
  rw [Submodule.offDiagonalPart_apply, diagonalPart_apply_of_mem U Z hx,
    Submodule.starProjection_orthogonal_apply]

variable (U) in
/-- On `Uᗮ` the off-diagonal part of `Z` is the `U`-component of `Z x`. -/
theorem offDiagonalPart_apply_of_mem_orthogonal (Z : E →L[𝕜] E) {x : E}
    (hx : x ∈ Uᗮ) : U.offDiagonalPart Z x = U.starProjection (Z x) := by
  rw [Submodule.offDiagonalPart_apply, diagonalPart_apply_of_mem_orthogonal U Z hx,
    Submodule.starProjection_orthogonal_apply]
  abel

variable (U) in
/-- The diagonal part preserves `U`. -/
theorem diagonalPart_mem_of_mem (Z : E →L[𝕜] E) {x : E} (hx : x ∈ U) :
    U.diagonalPart Z x ∈ U := by
  rw [diagonalPart_apply_of_mem U Z hx]
  exact U.starProjection_apply_mem _

variable (U) in
/-- The diagonal part preserves `Uᗮ`. -/
theorem diagonalPart_mem_orthogonal_of_mem_orthogonal (Z : E →L[𝕜] E) {x : E}
    (hx : x ∈ Uᗮ) : U.diagonalPart Z x ∈ Uᗮ := by
  rw [diagonalPart_apply_of_mem_orthogonal U Z hx]
  exact Uᗮ.starProjection_apply_mem _

variable (U) in
/-- The off-diagonal part carries `U` into `Uᗮ`. -/
theorem offDiagonalPart_mem_orthogonal_of_mem (Z : E →L[𝕜] E) {x : E}
    (hx : x ∈ U) : U.offDiagonalPart Z x ∈ Uᗮ := by
  rw [offDiagonalPart_apply_of_mem U Z hx]
  exact Uᗮ.starProjection_apply_mem _

variable (U) in
/-- The off-diagonal part carries `Uᗮ` into `U`. -/
theorem offDiagonalPart_mem_of_mem_orthogonal (Z : E →L[𝕜] E) {x : E}
    (hx : x ∈ Uᗮ) : U.offDiagonalPart Z x ∈ U := by
  rw [offDiagonalPart_apply_of_mem_orthogonal U Z hx]
  exact U.starProjection_apply_mem _

end Parity

/-- The two parts recompose the operator. -/
theorem diagonalPart_add_offDiagonalPart (Z : E →L[𝕜] E) :
    U.diagonalPart Z + U.offDiagonalPart Z = Z := by
  rw [Submodule.offDiagonalPart_eq]
  abel

section Involution

variable {U}

/-- The reflection through `U`, as a unit of the operator ring. -/
private theorem reflectionOperator_mul_self :
    U.reflectionOperator * U.reflectionOperator = 1 := by
  rw [ContinuousLinearMap.mul_def, Submodule.reflectionOperator_involutive,
    ← ContinuousLinearMap.one_def]

/-- Conjugating an involution by the reflection gives an involution. -/
private theorem reflectionConjugate_mul_self {Z : E →L[𝕜] E} (hZ : Z * Z = 1) :
    (U.reflectionOperator ∘L Z ∘L U.reflectionOperator) *
      (U.reflectionOperator ∘L Z ∘L U.reflectionOperator) = 1 := by
  set J : E →L[𝕜] E := U.reflectionOperator with hJdef
  have hJJ : J * J = 1 := reflectionOperator_mul_self
  have hcomp : J ∘L Z ∘L J = J * (Z * J) := by
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def]
  rw [hcomp]
  calc J * (Z * J) * (J * (Z * J)) = J * (Z * ((J * J) * (Z * J))) := by noncomm_ring
    _ = J * ((Z * Z) * J) := by rw [hJJ, one_mul, ← mul_assoc Z Z J]
    _ = 1 := by rw [hZ, one_mul, hJJ]

variable (U) in
/-- **The double-angle Pythagorean identity, in operator form.**  If `Z² = 1`
then `D² + S² = 1` for the two blocks of `Z` relative to `U`.  Blockwise this is
the pair `D₀² + G⋆G = 1`, `D₁² + G G⋆ = 1`. -/
theorem diagonalPart_sq_add_offDiagonalPart_sq {Z : E →L[𝕜] E} (hZ : Z * Z = 1) :
    U.diagonalPart Z * U.diagonalPart Z +
      U.offDiagonalPart Z * U.offDiagonalPart Z = 1 := by
  set W : E →L[𝕜] E :=
    U.reflectionOperator ∘L Z ∘L U.reflectionOperator with hWdef
  have hWW : W * W = 1 := reflectionConjugate_mul_self hZ
  have hD : (2 : 𝕜) • U.diagonalPart Z = Z + W :=
    Submodule.two_smul_diagonalPart_eq_add_reflectionConjugate U Z
  have hS : (2 : 𝕜) • U.offDiagonalPart Z = Z - W :=
    Submodule.two_smul_offDiagonalPart_eq_sub_reflectionConjugate U Z
  have hkey : (4 : 𝕜) • (U.diagonalPart Z * U.diagonalPart Z +
      U.offDiagonalPart Z * U.offDiagonalPart Z) = (4 : 𝕜) • (1 : E →L[𝕜] E) := by
    have hexp : (4 : 𝕜) • (U.diagonalPart Z * U.diagonalPart Z +
        U.offDiagonalPart Z * U.offDiagonalPart Z) =
        ((2 : 𝕜) • U.diagonalPart Z) * ((2 : 𝕜) • U.diagonalPart Z) +
          ((2 : 𝕜) • U.offDiagonalPart Z) * ((2 : 𝕜) • U.offDiagonalPart Z) := by
      rw [smul_mul_smul_comm, smul_mul_smul_comm, ← smul_add]
      norm_num
    rw [hexp, hD, hS]
    have hsum : (Z + W) * (Z + W) + (Z - W) * (Z - W) =
        Z * Z + Z * Z + (W * W + W * W) := by noncomm_ring
    rw [hsum, hZ, hWW]
    module
  exact smul_right_injective _ (by norm_num : (4 : 𝕜) ≠ 0) hkey

variable (U) in
/-- **The blocks of an involution anticommute.**  If `Z² = 1` then `D S + S D = 0`;
blockwise this is the intertwining relation `D₁ G = G D₀`, which is the
double-angle content of the reflected pair. -/
theorem diagonalPart_mul_offDiagonalPart_add_offDiagonalPart_mul_diagonalPart
    {Z : E →L[𝕜] E} (hZ : Z * Z = 1) :
    U.diagonalPart Z * U.offDiagonalPart Z +
      U.offDiagonalPart Z * U.diagonalPart Z = 0 := by
  set W : E →L[𝕜] E :=
    U.reflectionOperator ∘L Z ∘L U.reflectionOperator with hWdef
  have hWW : W * W = 1 := reflectionConjugate_mul_self hZ
  have hD : (2 : 𝕜) • U.diagonalPart Z = Z + W :=
    Submodule.two_smul_diagonalPart_eq_add_reflectionConjugate U Z
  have hS : (2 : 𝕜) • U.offDiagonalPart Z = Z - W :=
    Submodule.two_smul_offDiagonalPart_eq_sub_reflectionConjugate U Z
  have hkey : (4 : 𝕜) • (U.diagonalPart Z * U.offDiagonalPart Z +
      U.offDiagonalPart Z * U.diagonalPart Z) = (4 : 𝕜) • (0 : E →L[𝕜] E) := by
    have hexp : (4 : 𝕜) • (U.diagonalPart Z * U.offDiagonalPart Z +
        U.offDiagonalPart Z * U.diagonalPart Z) =
        ((2 : 𝕜) • U.diagonalPart Z) * ((2 : 𝕜) • U.offDiagonalPart Z) +
          ((2 : 𝕜) • U.offDiagonalPart Z) * ((2 : 𝕜) • U.diagonalPart Z) := by
      rw [smul_mul_smul_comm, smul_mul_smul_comm, ← smul_add]
      norm_num
    rw [hexp, hD, hS]
    have hsum : (Z + W) * (Z - W) + (Z - W) * (Z + W) =
        Z * Z + Z * Z - (W * W + W * W) := by noncomm_ring
    rw [hsum, hZ, hWW]
    module
  exact smul_right_injective _ (by norm_num : (4 : 𝕜) ≠ 0) hkey

end Involution

section Pythagoras

variable {U}

/-- **The vector double-angle Pythagoras identity on `U`.**  If `Z` preserves
norms then `‖D x‖² + ‖S x‖² = ‖x‖²` for `x ∈ U`: the two blocks of `Z x` are
orthogonal.  Blockwise this is `D₀² + G⋆G = 1` tested at `x`. -/
theorem norm_sq_diagonalPart_add_norm_sq_offDiagonalPart_of_mem
    {Z : E →L[𝕜] E} (hZ : ∀ v : E, ‖Z v‖ = ‖v‖) {x : E} (hx : x ∈ U) :
    ‖U.diagonalPart Z x‖ ^ 2 + ‖U.offDiagonalPart Z x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [diagonalPart_apply_of_mem U Z hx, offDiagonalPart_apply_of_mem U Z hx,
    ← Submodule.norm_sq_eq_add_norm_sq_starProjection (Z x) U, hZ]

/-- The mirror of `norm_sq_diagonalPart_add_norm_sq_offDiagonalPart_of_mem` on
`Uᗮ`: blockwise `D₁² + G G⋆ = 1`. -/
theorem norm_sq_diagonalPart_add_norm_sq_offDiagonalPart_of_mem_orthogonal
    {Z : E →L[𝕜] E} (hZ : ∀ v : E, ‖Z v‖ = ‖v‖) {x : E} (hx : x ∈ Uᗮ) :
    ‖U.diagonalPart Z x‖ ^ 2 + ‖U.offDiagonalPart Z x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [diagonalPart_apply_of_mem_orthogonal U Z hx,
    offDiagonalPart_apply_of_mem_orthogonal U Z hx, add_comm,
    ← Submodule.norm_sq_eq_add_norm_sq_starProjection (Z x) U, hZ]

end Pythagoras

section Operator

variable [CompleteSpace E] {U}

/-- The diagonal part of a self-adjoint operator is self-adjoint. -/
theorem isSelfAdjoint_diagonalPart {Z : E →L[𝕜] E} (hZ : IsSelfAdjoint Z) :
    IsSelfAdjoint (U.diagonalPart Z) := by
  have hcomp : ∀ V : Submodule 𝕜 E, ∀ _ : V.HasOrthogonalProjection,
      IsSelfAdjoint (V.starProjection ∘L Z ∘L V.starProjection) := by
    intro V _
    exact hZ.conjugate_self (isSelfAdjoint_starProjection V)
  rw [Submodule.diagonalPart_eq]
  exact (hcomp U inferInstance).add (hcomp Uᗮ inferInstance)

/-- The off-diagonal part of a self-adjoint operator is self-adjoint. -/
theorem isSelfAdjoint_offDiagonalPart {Z : E →L[𝕜] E} (hZ : IsSelfAdjoint Z) :
    IsSelfAdjoint (U.offDiagonalPart Z) := by
  rw [Submodule.offDiagonalPart_eq]
  exact hZ.sub (isSelfAdjoint_diagonalPart hZ)

end Operator

end TauCeti
