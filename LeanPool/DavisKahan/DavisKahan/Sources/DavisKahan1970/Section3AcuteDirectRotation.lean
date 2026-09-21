/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotationAcute
import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotationReal
import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotationSquare
import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.PrincipalSquareRoot
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.RealContinuousFunctionalCalculus
import LeanPool.DavisKahan.ForTauCeti.Analysis.RCLike.ScalarTransportFunctionalCalculus

/-! # Section3Acute Direct Rotation -/

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Proposition 3.1, at the paper's own acuteness hypothesis

Printed Proposition 3.1 reads "in the acute case the direct rotation exists, is
unique, and is characterized by property (i) alone", where the acute case is
printed Definition 3.2: the crossed intersections `U ⊓ Vᗮ` and `Uᗮ ⊓ V` vanish.
That predicate is `TauCeti.IsAcute`.

Every previously compiled endpoint carried `TauCeti.DavisKahan.IsUniformlyAcute`
instead, i.e. `‖P_U - P_V‖ < 1`.  The two agree only in finite dimension:
`TauCeti.isAcute_of_projectionGap_lt_one` holds always, and its converse
`TauCeti.projectionGap_lt_one_of_isAcute` needs `FiniteDimensional`.  Section 3
of the paper is explicitly infinite-dimensional, so the narrowing was real.
The theorems below remove it, over a real *or* complex Hilbert space of
arbitrary dimension, and the last two sections re-derive the old
`IsUniformlyAcute` statements from the new ones, so nothing is lost.

Standing assumption (1.5) — equality of the two pairs of dimensions — is *not*
needed here.  The paper uses it only to produce some unitary `V` with
`V P = Q V` before polarising; the construction below is the polar factor of
`S = P_V P_U + P_Vᗮ P_Uᗮ`, which acuteness alone makes unitary.  So these
statements are stronger than printed in that respect too.

The mathematics is in `DavisKahan/Geometry/Polar/DirectRotationAcute.lean`.
-/

open scoped InnerProductSpace ComplexOrder

namespace TauCeti
namespace DavisKahan1970


open DavisKahan

/-! ## Definition 3.1's direct rotation, over any `RCLike` field -/

/-- **The direct rotation of an acute pair**: the polar factor of the canonical
intertwiner `S = P_V P_U + P_Vᗮ P_Uᗮ`.  The object carries no hypothesis; the
theorems below say what acuteness makes of it. -/
alias acute_directRotation := DavisKahan.spectraCanonicalPolarFactor

section Generic

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
/-! The real functional calculus on `H →L[𝕜] H`, and the two scalar-action facts Mathlib
pairs it with, are theorems at every `RCLike` field
(`ContinuousLinearMap.continuousFunctionalCalculusReal`), so they are activated here rather
than quantified over.  Until 2026-09-04 they were section `variable`s, and every theorem in
this section therefore asked its caller for three instances that instance search finds.  They
are `local instance 100` rather than global because a global `Algebra ℝ (E →L[𝕜] E)` makes
Lean's `•` elaborator drop an author-written `((r : ℝ) : 𝕜) •` coercion. -/
attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal

variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

/-- **Proposition 3.1(a) at the printed hypothesis**: the direct rotation of an
acute pair is unitary. -/
theorem acute_directRotation_mem_unitary (hacute : TauCeti.IsAcute U V) :
    acute_directRotation U V ∈ unitary (H →L[𝕜] H) :=
  spectraCanonicalPolarFactor_mem_unitary U V
    (TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mp hacute).1
    (TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mp hacute).2

/-- The direct rotation intertwines the two orthogonal projections.  No
acuteness of any kind is needed for this clause. -/
theorem acute_directRotation_intertwines :
    acute_directRotation U V * U.starProjection =
      V.starProjection * acute_directRotation U V :=
  canonicalPolarFactor_intertwines_general U V

/-- The direct rotation of an acute pair carries `U` onto `V`; membership is
concluded, not assumed. -/
theorem acute_directRotation_maps_subspace (hacute : TauCeti.IsAcute U V) :
    U.map (acute_directRotation U V).toLinearMap = V :=
  spectraCanonicalPolarFactor_maps_subspace U V
    (TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mp hacute).1
    (TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mp hacute).2

/-- The source diagonal block of the direct rotation of an acute pair is the
positive Halmos cosine `|S| P_U`. -/
theorem acute_directRotation_diagonalBlock (hacute : TauCeti.IsAcute U V) :
    U.starProjection * acute_directRotation U V * U.starProjection =
      ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) * U.starProjection :=
  projection_mul_spectraCanonicalPolarFactor_mul_projection U V
    (TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mp hacute).1
    (TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mp hacute).2

/-- The complementary diagonal block of the direct rotation of an acute pair. -/
theorem acute_directRotation_complementaryDiagonalBlock (hacute : TauCeti.IsAcute U V) :
    Uᗮ.starProjection * acute_directRotation U V * Uᗮ.starProjection =
      ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) * Uᗮ.starProjection :=
  complementaryProjection_mul_spectraCanonicalPolarFactor_mul_complementaryProjection U V
    (TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mp hacute).1
    (TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mp hacute).2

/-- **Definition 3.1, property (i), for the source block**: the compression of
the direct rotation of an acute pair to `U` is a positive operator. -/
theorem acute_directRotation_positiveDiagonalBlock (hacute : TauCeti.IsAcute U V) :
    (U.starProjection * acute_directRotation U V * U.starProjection).IsPositive :=
  isPositive_projection_mul_spectraCanonicalPolarFactor_mul_projection U V
    (TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mp hacute).1
    (TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mp hacute).2

/-- **Definition 3.1, property (i), for the complementary block.** -/
theorem acute_directRotation_positiveComplementaryDiagonalBlock
    (hacute : TauCeti.IsAcute U V) :
    (Uᗮ.starProjection * acute_directRotation U V * Uᗮ.starProjection).IsPositive :=
  isPositive_complementaryProjection_mul_spectraCanonicalPolarFactor U V
    (TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mp hacute).1
    (TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mp hacute).2

/-- **Proposition 3.1(c) at the printed hypothesis**: among the unitaries
intertwining the two projections, positivity of the two diagonal blocks — the
paper's property (i) — singles out the direct rotation.  Equation (3.8) is
neither assumed nor listed. -/
theorem acute_directRotation_of_positiveDiagonalBlocks (hacute : TauCeti.IsAcute U V)
    (W : H →L[𝕜] H) (hWunit : W ∈ unitary (H →L[𝕜] H))
    (hint : W * U.starProjection = V.starProjection * W)
    (hblockU : (U.starProjection * W * U.starProjection).IsPositive)
    (hblockUperp : (Uᗮ.starProjection * W * Uᗮ.starProjection).IsPositive) :
    W = acute_directRotation U V :=
  eq_spectraCanonicalPolarFactor_of_diagonalBlocks_isPositive U V
    (TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mp hacute).1
    (TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mp hacute).2 W hWunit hint hblockU hblockUperp

/-- **Proposition 3.1(c) at the printed hypothesis, as a biconditional.** -/
theorem acute_directRotation_iff_positiveDiagonalBlocks (hacute : TauCeti.IsAcute U V)
    (W : H →L[𝕜] H) :
    W = acute_directRotation U V ↔
      W ∈ unitary (H →L[𝕜] H) ∧
        W * U.starProjection = V.starProjection * W ∧
        (U.starProjection * W * U.starProjection).IsPositive ∧
        (Uᗮ.starProjection * W * Uᗮ.starProjection).IsPositive :=
  eq_spectraCanonicalPolarFactor_iff_diagonalBlocks_isPositive U V
    (TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mp hacute).1
    (TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mp hacute).2 W

/-- **Davis--Kahan 1970, Proposition 3.1, in one statement and at the paper's
own hypothesis.**  In the acute case a unitary intertwining the two projections
with both diagonal compressions positive exists and is unique.

Over a real or complex Hilbert space of arbitrary dimension, with no projection
gap bound and without standing assumption (1.5). -/
theorem acute_directRotation_existsUnique (hacute : TauCeti.IsAcute U V) :
    ∃! W : H →L[𝕜] H,
      W ∈ unitary (H →L[𝕜] H) ∧
        W * U.starProjection = V.starProjection * W ∧
        (U.starProjection * W * U.starProjection).IsPositive ∧
        (Uᗮ.starProjection * W * Uᗮ.starProjection).IsPositive :=
  existsUnique_spectraCanonicalPolarFactor U V
    (TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mp hacute).1
    (TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mp hacute).2

/-- **Davis--Kahan 1970, Proposition 3.1, exact source-facing wrapper.**

At the paper's printed acute-case hypothesis, the canonical polar factor is a
unitary intertwiner, its two diagonal blocks are positive, it satisfies the
direct-rotation crossed-block identity from Definition 3.1(ii), and property
(i) alone characterizes it among unitary intertwiners.  Thus no projection-gap
hypothesis, equation (3.8), standing dimension assumption (1.5), finite-
dimensional hypothesis, or scalar-field specialization is present in the
statement. -/
theorem proposition3_1 (hacute : TauCeti.IsAcute U V) :
    acute_directRotation U V ∈ unitary (H →L[𝕜] H) ∧
      acute_directRotation U V * U.starProjection =
        V.starProjection * acute_directRotation U V ∧
      (U.starProjection * acute_directRotation U V * U.starProjection).IsPositive ∧
      (Uᗮ.starProjection * acute_directRotation U V * Uᗮ.starProjection).IsPositive ∧
      Uᗮ.starProjection * acute_directRotation U V * U.starProjection =
        -star (U.starProjection * acute_directRotation U V * Uᗮ.starProjection) ∧
      ∀ W : H →L[𝕜] H,
        W ∈ unitary (H →L[𝕜] H) →
        W * U.starProjection = V.starProjection * W →
        (U.starProjection * W * U.starProjection).IsPositive →
        (Uᗮ.starProjection * W * Uᗮ.starProjection).IsPositive →
        W = acute_directRotation U V := by
  refine ⟨acute_directRotation_mem_unitary U V hacute,
    acute_directRotation_intertwines U V,
    acute_directRotation_positiveDiagonalBlock U V hacute,
    acute_directRotation_positiveComplementaryDiagonalBlock U V hacute,
    canonicalPolarFactor_crossed_blocks_general U V, ?_⟩
  intro W hWunit hint hblockU hblockUperp
  exact acute_directRotation_of_positiveDiagonalBlocks U V hacute W
    hWunit hint hblockU hblockUperp


end Generic

/-! ## The complex endpoints, and the `IsUniformlyAcute` ones as a special case -/

section Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

omit [CompleteSpace H] in
/-- Over a complex space, positivity of a compression is exactly the pointwise
sign condition on the subspace, in the order on `ℂ`.  Over `ℝ` it is not: the
`ℝ⁴` rotation by `π/3` has a nonnegative but non-symmetric diagonal block. -/
theorem isPositive_compression_iff_forall_mem (W : H →L[ℂ] H) (K : Submodule ℂ H)
    [K.HasOrthogonalProjection] :
    (K.starProjection * W * K.starProjection).IsPositive ↔ ∀ x ∈ K, 0 ≤ ⟪W x, x⟫_ℂ := by
  constructor
  · intro hpos x hx
    have hK : K.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
    have hval : ⟪(K.starProjection * W * K.starProjection) x, x⟫_ℂ = ⟪W x, x⟫_ℂ := by
      change ⟪K.starProjection (W (K.starProjection x)), x⟫_ℂ = ⟪W x, x⟫_ℂ
      rw [hK, Submodule.inner_starProjection_left_eq_right K, hK]
    rw [← hval]
    exact hpos.inner_nonneg_left x
  · intro h
    rw [ContinuousLinearMap.isPositive_iff_complex]
    intro x
    have hmem : K.starProjection x ∈ K := K.starProjection_apply_mem x
    have hval : ⟪(K.starProjection * W * K.starProjection) x, x⟫_ℂ =
        ⟪W (K.starProjection x), K.starProjection x⟫_ℂ :=
      Submodule.inner_starProjection_left_eq_right K _ _
    rw [hval]
    obtain ⟨hre, him⟩ := RCLike.nonneg_iff.mp (h _ hmem)
    exact ⟨RCLike.conj_eq_iff_re.mp (RCLike.conj_eq_iff_im.mpr him), hre⟩

/-- **Proposition 3.1(c) over `ℂ`, at the printed hypothesis and in the pointwise
shape the previously compiled complex endpoint used.** -/
theorem complex_acute_directRotation_iff_positiveDiagonalBlocks
    (hacute : TauCeti.IsAcute U V) (W : H →L[ℂ] H) :
    W = acute_directRotation U V ↔
      W ∈ unitary (H →L[ℂ] H) ∧
        W * U.starProjection = V.starProjection * W ∧
        (∀ x ∈ U, 0 ≤ ⟪W x, x⟫_ℂ) ∧
        (∀ x ∈ Uᗮ, 0 ≤ ⟪W x, x⟫_ℂ) := by
  rw [acute_directRotation_iff_positiveDiagonalBlocks U V hacute W,
    isPositive_compression_iff_forall_mem W U, isPositive_compression_iff_forall_mem W Uᗮ]

/-- **The previously compiled complex endpoint is a special case.**

Statement copied from
`TauCeti.DavisKahan.eq_spectraDirectRotation_iff_diagonalBlocks_pos`,
proof obtained from the printed-hypothesis biconditional through
`TauCeti.isAcute_of_projectionGap_lt_one`.  Nothing that was compiled at
`IsUniformlyAcute` is lost. -/
theorem eq_spectraDirectRotation_iff_diagonalBlocks_pos_of_isAcute
    (hacute : DavisKahan.IsUniformlyAcute U V) (W : H →L[ℂ] H) :
    W = spectraDirectRotation U V hacute ↔
      W ∈ unitary (H →L[ℂ] H) ∧
        W * U.starProjection = V.starProjection * W ∧
        (∀ x ∈ U, 0 ≤ ⟪W x, x⟫_ℂ) ∧
        (∀ x ∈ Uᗮ, 0 ≤ ⟪W x, x⟫_ℂ) :=
  complex_acute_directRotation_iff_positiveDiagonalBlocks U V
    (TauCeti.isAcute_of_projectionGap_lt_one hacute) W

/-- **Davis--Kahan 1970, Proposition 3.1, the positivity characterization of the
canonical direct rotation.**

In the acute case the direct rotation is the unique unitary intertwiner whose
diagonal `U`-compressions are positive.

The predicate `IsDirectRotation` records the diagonal compressions only
through their numerical range (`0 ≤ re ⟪x, (P T P) x⟫`), which is strictly
weaker than operator positivity and does not pin the phase on the common part:
on `U = V` every scalar `exp (I * θ)` with `|θ| < π / 2` satisfies all five
fields yet differs from the identity direct rotation.  Uniqueness therefore
needs the diagonal compressions to be self-adjoint (equivalently genuinely
positive operators, which the canonical direct rotation satisfies because its
diagonal blocks are the positive Halmos cosine).  These two self-adjointness
hypotheses are the minimal strengthening; with them the operator squares to the
reflection product and the square-root branch is fixed by accretivity.

The printed proposition at its own hypothesis, `TauCeti.IsAcute` rather than the
strictly stronger uniform gap, is `proposition3_1` above; this is the
`IsUniformlyAcute` form stated against `spectraDirectRotation`. -/
theorem proposition3_1_positivity_characterization
    (hacute : DavisKahan.IsUniformlyAcute U V) (T : H →L[ℂ] H)
    (hunitary : T ∈ unitary (H →L[ℂ] H))
    (hintertwines : T * U.starProjection = V.starProjection * T)
    (hsource_sa : IsSelfAdjoint
      (U.starProjection * T * U.starProjection))
    (hcomplement_sa : IsSelfAdjoint
      ((Uᗮ).starProjection * T *
        (Uᗮ).starProjection)) :
    DavisKahan.IsDirectRotation U V T ↔
      T = DavisKahan.spectraDirectRotation U V hacute := by
  constructor
  · intro hT
    have hsq : T * T = DavisKahan.spectraReflectionProduct U V :=
      DavisKahan.sq_eq_spectraReflectionProduct U V T hunitary hintertwines hsource_sa
        hcomplement_sa hT.crossed_blocks
    -- Accretivity fixes the square-root branch.
    have hre : ∀ x, 0 ≤ Complex.re ⟪T x, x⟫_ℂ := by
      intro x
      have h := DavisKahan.re_inner_directRotation_nonneg U V T hT x
      rwa [← inner_re_symm (𝕜 := ℂ) (T x) x, RCLike.re_eq_complex_re] at h
    exact DavisKahan.spectraDirectRotation_unique_of_sq U V hacute T hunitary hsq hre
  · rintro rfl
    exact DavisKahan.spectraDirectRotation_isDirectRotation U V hacute

end Complex

/-! ## The real endpoints, and the `IsUniformlyAcute` ones as a special case -/

section Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (U V : Submodule ℝ E) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

/-- **The real direct rotation built by complexification descent is the real
polar factor.**

`directRotationR` is defined as the real part of the complex direct rotation of
the complexified pair; the polar factor `acute_directRotation` is built directly
over `ℝ`.  They agree, and the proof is the printed-hypothesis uniqueness clause
applied to `directRotationR`, using only its *existence*-side properties. -/
theorem real_directRotation_eq_acute_directRotation
    (hacute : DavisKahan.IsUniformlyAcute U V) :
    directRotationR U V hacute = acute_directRotation U V :=
  acute_directRotation_of_positiveDiagonalBlocks U V
    (TauCeti.isAcute_of_projectionGap_lt_one hacute) _
    (directRotationR_mem_unitary U V hacute) (directRotationR_intertwines U V hacute)
    (isPositive_projection_mul_directRotationR_mul_projection U V hacute)
    (isPositive_complementaryProjection_mul_directRotationR_mul_complementaryProjection
      U V hacute)

/-- **The previously compiled real endpoint is a special case.**

Statement copied from
`TauCeti.DavisKahan.eq_directRotationR_iff_diagonalBlocks_pos`,
proof obtained from the printed-hypothesis biconditional. -/
theorem eq_directRotationR_iff_diagonalBlocks_pos_of_isAcute
    (hacute : DavisKahan.IsUniformlyAcute U V) (W : E →L[ℝ] E) :
    W = directRotationR U V hacute ↔
      W ∈ unitary (E →L[ℝ] E) ∧
        W * U.starProjection = V.starProjection * W ∧
        (U.starProjection * W * U.starProjection).IsPositive ∧
        (Uᗮ.starProjection * W * Uᗮ.starProjection).IsPositive := by
  rw [real_directRotation_eq_acute_directRotation U V hacute]
  exact acute_directRotation_iff_positiveDiagonalBlocks U V
    (TauCeti.isAcute_of_projectionGap_lt_one hacute) W

end Real

end DavisKahan1970
end TauCeti
