/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotationBlocks
-- supplies the block estimates these three statements run on: diagonal-block self-adjointness,
-- the `√2/2` norm bound on the source subspace, the half-angle inequality for the Halmos cosine
-- square, and `reflectionOperator_reflectedSubspace`.
import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.Section3Nonacute

/-! # Section3Proposition34Presentation -/
-- supplies the completed nonacute direct-rotation construction the acute forms specialise.

/-!
# Davis--Kahan 1970, Proposition 3.4, at the printed scope

Proposition 3.4 says that the square of a direct rotation is again a direct rotation, for the
reflected pair, under the printed half-angle hypothesis `C₀² ≥ ½` on the source subspace.

This module owns the three source-facing statements: the full nonacute form, the acute
specialisation that is the printed sentence, and the identification of the acute form with the
canonical direct rotation.  The reusable block estimates beneath them live in
`DavisKahan/Geometry/Polar/DirectRotationBlocks.lean`.

## Why this is its own module

The statements are written against `open scoped InnerProductSpace` alone.  The neighbouring
`Section3Proposition34.lean` additionally opens `ComplexOrder`, under which the operator order
`0 ≤ P W P` elaborates through a different coercion, so folding these three declarations into
that file would have changed how they elaborate.  Keeping the scope they were proved under is
what makes this a move rather than a restatement.

## Main results

* `proposition3_4_isDirectRotation_complex`: the full nonacute source scope.
* `proposition3_4`: the printed sentence, at `IsUniformlyAcute`.
* `proposition3_4_eq_directRotation`: the acute form is the canonical direct rotation.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahan
open TauCeti.DavisKahanExt (reflectedSubspace starProjection_reflectedSubspace)

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

/-- **Davis--Kahan 1970, Proposition 3.4 at the full nonacute source scope.**

The operator `W` is an arbitrary direct rotation in the sense of Definition 3.1: the two
operator inequalities are the printed `C₀ ≥ 0` and `C₁ ≥ 0` conditions, while the remaining
three hypotheses are unitarity, intertwining, and the skew-adjoint crossed-block relation.
The hypotheses are exactly the direct-rotation data used in the paper's nonacute Section 3
scope.

The additional hypothesis `hcos` is exactly the printed `C₀² ≥ 1/2`, read through equation
(3.7).  The conclusion says that `W²` satisfies Definition 3.1 for the ordered pair
`(Q₋ℋ,Qℋ)`. -/
theorem proposition3_4_isDirectRotation_complex
    (W : H →L[ℂ] H)
    (hunitary : W ∈ unitary (H →L[ℂ] H))
    (hintertwines : W * U.starProjection = V.starProjection * W)
    (hcrossed : (Uᗮ).starProjection * W * U.starProjection =
      -star (U.starProjection * W * (Uᗮ).starProjection))
    (hsource_pos : (0 : H →L[ℂ] H) ≤ U.starProjection * W * U.starProjection)
    (hcomplement_pos :
      (0 : H →L[ℂ] H) ≤ (Uᗮ).starProjection * W * (Uᗮ).starProjection)
    (hcos : ∀ x ∈ U, ‖x‖ ^ 2 / 2 ≤ ‖V.starProjection x‖ ^ 2) :
    IsDirectRotation (reflectedSubspace U V) V (W * W) := by
  have hsp := (ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mp hsource_pos
  have hcp := (ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mp hcomplement_pos
  have hW : IsDirectRotation U V W :=
    { unitary_mem := hunitary
      intertwines := hintertwines
      source_compression_nonnegative := fun x => by
        rw [inner_re_symm (𝕜 := ℂ)]
        exact hsp.re_inner_nonneg_left x
      complement_compression_nonnegative := fun x => by
        rw [inner_re_symm (𝕜 := ℂ)]
        exact hcp.re_inner_nonneg_left x
      crossed_blocks := hcrossed }
  have hWsq : W * W = spectraReflectionProduct U V :=
    sq_eq_spectraReflectionProduct U V W hunitary hintertwines
      hsp.isSelfAdjoint hcp.isSelfAdjoint hcrossed
  have hW2unit : W * W ∈ unitary (H →L[ℂ] H) := mul_mem hunitary hunitary
  have hrefl : Submodule.reflectionOperator (reflectedSubspace U V) =
      U.reflectionOperator * V.reflectionOperator * U.reflectionOperator :=
    reflectionOperator_reflectedSubspace V U
  have hRU : U.reflectionOperator * U.reflectionOperator = 1 :=
    reflectionOperator_mul_self_complex U
  have hsq : (W * W) * (W * W) =
      spectraReflectionProduct (reflectedSubspace U V) V := by
    show (W * W) * (W * W) =
      V.reflectionOperator * Submodule.reflectionOperator (reflectedSubspace U V)
    rw [hrefl, hWsq]
    noncomm_ring
  have hint : (W * W) * Submodule.starProjection (reflectedSubspace U V) =
      V.starProjection * (W * W) := by
    have hPref : Submodule.starProjection (reflectedSubspace U V) =
        U.reflectionOperator * V.starProjection * U.reflectionOperator :=
      starProjection_reflectedSubspace U V
    rw [hPref, hWsq]
    calc
      V.reflectionOperator * U.reflectionOperator *
          (U.reflectionOperator * V.starProjection * U.reflectionOperator) =
        V.reflectionOperator * (U.reflectionOperator * U.reflectionOperator) *
          (V.starProjection * U.reflectionOperator) := by noncomm_ring
      _ = V.reflectionOperator * V.starProjection * U.reflectionOperator := by
        rw [hRU, mul_one, mul_assoc]
      _ = V.starProjection * U.reflectionOperator := by
        rw [reflectionOperator_mul_projection_self V]
      _ = (V.starProjection * V.reflectionOperator) * U.reflectionOperator := by
        rw [projection_mul_reflectionOperator_self V]
      _ = V.starProjection * (V.reflectionOperator * U.reflectionOperator) := by
        rw [mul_assoc]
  have hhalf : ∀ x : H,
      0 ≤ RCLike.re ⟪x, halmosCosineSq U V x⟫_ℂ - ‖x‖ ^ 2 / 2 :=
    re_inner_halmosCosineSq_sub_half_nonneg_of_directRotation U V W hW
      hsp.isSelfAdjoint hcp.isSelfAdjoint hcos
  have hre : ∀ x : H, 0 ≤ RCLike.re ⟪(W * W) x, x⟫_ℂ := by
    intro x
    rw [hWsq]
    exact re_inner_reflectionProduct_nonneg U V hhalf x
  have hspec := spectrum_re_nonneg_of_nonneg_add_star (W * W) hW2unit
    (nonneg_add_star_of_re_inner_nonneg (W * W) hre)
  exact proposition3_3_principalSquareRoot_converse (reflectedSubspace U V) V (W * W)
    ⟨hW2unit, hsq, hspec⟩
    (crossedDefect_image_of_unitary_sq (reflectedSubspace U V) V (W * W)
      hW2unit hsq hint)

/-- **Acute-constructor specialization of Davis--Kahan 1970, Proposition 3.4.**

> If `C₀² ≥ ½`, then `U²` is the direct rotation of `Q₋ℋ` to `Qℋ`.

Every clause is the printed one.  `Q₋ = XQX` is the mirror image of the target in the source
(`reflectedSubspace U V`, whose projection is `R_U P_V R_U`); the conclusion is Definition 3.1
for the ordered pair `(Q₋ℋ, Qℋ)` -- the paper's own proof verifies exactly its clauses (i) and
(ii) plus the intertwining `U²Q₋ = QU²`; and `hcos` is `C₀² ≥ ½` read through equation (3.7),
`C₀² = E₀⋆ Q E₀`, so its quadratic form at `x ∈ Pℋ` is `‖Qx‖²`.

Three narrowings of `TauCeti.DavisKahan1970.proposition3_4_square_is_reflected_directRotation` are removed.  That
statement exhibits an existential pair rather than the printed `(Q₋ℋ, Qℋ)`; assumes the
symmetrized whole-space form bound rather than the printed `Pℋ` one; and carries an extra
`IsUniformlyAcute U (reflectedSubspace V U)`.  The extra acuteness is genuinely not available
here -- at the boundary `C₀² = ½` the reflected pair has gap one -- and is not needed: the
crossed-intersection mapping condition of Proposition 3.3 holds for every unitary square root
of the reflection product that intertwines the projections
(`crossedDefect_image_of_unitary_sq`), so the nonacute converse applies unchanged.  Acuteness
of the *original* pair is retained because it is what `spectraDirectRotation U V` is indexed
by, and because the companion bound `C₁² ≥ ½` is false without an intertwiner.

Grounded by `:=` on `proposition3_3_principalSquareRoot_converse`, so no square-root branch
argument is duplicated. -/
theorem proposition3_4 (hacute : IsUniformlyAcute U V)
    (hcos : ∀ x ∈ U, ‖x‖ ^ 2 / 2 ≤ ‖V.starProjection x‖ ^ 2) :
    IsDirectRotation (reflectedSubspace U V) V
      (spectraDirectRotation U V hacute * spectraDirectRotation U V hacute) := by
  set W := spectraDirectRotation U V hacute with hWdef
  have hWunit : W ∈ unitary (H →L[ℂ] H) := spectraDirectRotation_mem_unitary U V hacute
  have hTunit : W * W ∈ unitary (H →L[ℂ] H) := mul_mem hWunit hWunit
  have hWsq : W * W = V.reflectionOperator * U.reflectionOperator :=
    spectraDirectRotation_sq U V hacute
  have hrefl : Submodule.reflectionOperator (reflectedSubspace U V)
      = U.reflectionOperator * V.reflectionOperator * U.reflectionOperator :=
    reflectionOperator_reflectedSubspace V U
  have hRU : U.reflectionOperator * U.reflectionOperator = 1 :=
    reflectionOperator_mul_self_complex U
  have hsq : (W * W) * (W * W) = spectraReflectionProduct (reflectedSubspace U V) V := by
    show (W * W) * (W * W)
      = V.reflectionOperator * Submodule.reflectionOperator (reflectedSubspace U V)
    rw [hrefl, hWsq]
    noncomm_ring
  -- the printed `U²Q₋ = QU²`
  have hint : (W * W) * Submodule.starProjection (reflectedSubspace U V)
      = V.starProjection * (W * W) := by
    have hPref : Submodule.starProjection (reflectedSubspace U V)
        = U.reflectionOperator * V.starProjection * U.reflectionOperator :=
      starProjection_reflectedSubspace U V
    rw [hPref, hWsq]
    calc V.reflectionOperator * U.reflectionOperator *
          (U.reflectionOperator * V.starProjection * U.reflectionOperator)
        = V.reflectionOperator * (U.reflectionOperator * U.reflectionOperator) *
            (V.starProjection * U.reflectionOperator) := by noncomm_ring
      _ = V.reflectionOperator * V.starProjection * U.reflectionOperator := by
            rw [hRU, mul_one, mul_assoc]
      _ = V.starProjection * U.reflectionOperator := by
            rw [reflectionOperator_mul_projection_self V]
      _ = (V.starProjection * V.reflectionOperator) * U.reflectionOperator := by
            rw [projection_mul_reflectionOperator_self V]
      _ = V.starProjection * (V.reflectionOperator * U.reflectionOperator) := by
            rw [mul_assoc]
  have hre : ∀ x : H, 0 ≤ RCLike.re ⟪(W * W) x, x⟫_ℂ := by
    intro x
    rw [hWsq]
    exact re_inner_reflectionProduct_nonneg U V
      (re_inner_halmosCosineSq_sub_half_nonneg_of_source U V hacute hcos) x
  have hspec := spectrum_re_nonneg_of_nonneg_add_star (W * W) hTunit
    (nonneg_add_star_of_re_inner_nonneg (W * W) hre)
  exact proposition3_3_principalSquareRoot_converse (reflectedSubspace U V) V (W * W)
    ⟨hTunit, hsq, hspec⟩
    (crossedDefect_image_of_unitary_sq (reflectedSubspace U V) V (W * W) hTunit hsq hint)

/-- **Proposition 3.4 with the printed definite article.**

"*the* direct rotation" presupposes uniqueness, which Proposition 3.1 supplies exactly when
the reflected pair is acute.  Under that additional hypothesis the square is the canonical
direct rotation of `(Q₋ℋ, Qℋ)` on the nose.  Without it `proposition3_4` still holds:
the square satisfies Definition 3.1, and by Proposition 3.2 it is then one of possibly
several direct rotations. -/
theorem proposition3_4_eq_directRotation (hacute : IsUniformlyAcute U V)
    (hcos : ∀ x ∈ U, ‖x‖ ^ 2 / 2 ≤ ‖V.starProjection x‖ ^ 2)
    (hacuteRef : IsUniformlyAcute (reflectedSubspace U V) V) :
    spectraDirectRotation U V hacute * spectraDirectRotation U V hacute
      = spectraDirectRotation (reflectedSubspace U V) V hacuteRef := by
  set W := spectraDirectRotation U V hacute with hWdef
  have hWunit : W ∈ unitary (H →L[ℂ] H) := spectraDirectRotation_mem_unitary U V hacute
  have hTunit : W * W ∈ unitary (H →L[ℂ] H) := mul_mem hWunit hWunit
  have hWsq : W * W = V.reflectionOperator * U.reflectionOperator :=
    spectraDirectRotation_sq U V hacute
  have hrefl : Submodule.reflectionOperator (reflectedSubspace U V)
      = U.reflectionOperator * V.reflectionOperator * U.reflectionOperator :=
    reflectionOperator_reflectedSubspace V U
  have hsq : (W * W) * (W * W) = spectraReflectionProduct (reflectedSubspace U V) V := by
    show (W * W) * (W * W)
      = V.reflectionOperator * Submodule.reflectionOperator (reflectedSubspace U V)
    rw [hrefl, hWsq]
    noncomm_ring
  refine spectraDirectRotation_unique_of_sq (reflectedSubspace U V) V hacuteRef
    (W * W) hTunit hsq ?_
  intro x
  rw [hWsq]
  exact re_inner_reflectionProduct_nonneg U V
    (re_inner_halmosCosineSq_sub_half_nonneg_of_source U V hacute hcos) x

end DavisKahan1970
end TauCeti
