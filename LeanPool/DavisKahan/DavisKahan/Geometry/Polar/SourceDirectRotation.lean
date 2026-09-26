/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.PrincipalSquareRoot
public import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.Section3Nonacute
public import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.Proposition35Infinite
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.OperatorRealAlgebra
public import LeanPool.DavisKahan.ForTauCeti.Analysis.RCLike.ScalarTransportFunctionalCalculus

/-!
# Davis--Kahan's Definition 3.1, and why every direct rotation displaces alike

`IsDirectRotation` records the two diagonal compressions only through their
numerical range, `0 ≤ re ⟪x, (P T P) x⟫`.  That is **strictly weaker** than
Davis and Kahan's Definition 3.1, which asks for `C₀ ≥ 0` and `C₁ ≥ 0` as
operators: on `U = V` every scalar `exp (i θ)` with `|θ| < π/2` satisfies all
five fields of `IsDirectRotation` and is not a direct rotation in the paper's
sense.  Section 4's extremality statements are false for that weaker predicate —
`1 - exp (i θ)` has displacement `2 sin (θ/2) > 0` where the direct rotation `1`
has none — so the source object has to be the stronger one.

`IsSourceDirectRotation` is that object: `IsDirectRotation` plus
self-adjointness of the two diagonal compressions, which upgrades their
numerical-range signs to genuine operator positivity.

The main theorem is that **the Hermitian part of a Definition 3.1 direct
rotation does not depend on which one it is**:

```
D + D⋆ = 2 |C|,      C = P_V P_U + P_{Vᗮ} P_{Uᗮ}.
```

Davis and Kahan's Proposition 3.2 says the direct rotation is not unique — the
freedom is a unitary between the two crossed defect spaces — so a Section 4
statement about "the" direct rotation is only meaningful because this quantity,
and hence the whole displacement `1 - D`, is the same for all of them.

The proof is a square-root uniqueness argument and needs no case analysis.  For
a unitary `D`, `(D + D⋆)² = D² + D⋆² + 2`, and Proposition 3.3's square identity
gives `D² = J_V J_U` for every Definition 3.1 rotation.  So `(D + D⋆)²` is the
same nonnegative operator `J_V J_U + J_U J_V + 2` for all of them, and a
nonnegative operator has one nonnegative square root.
-/

@[expose] public section

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-! The real functional calculus on `H →L[𝕜] H` and the two scalar-action facts
Mathlib pairs it with are theorems at every `RCLike` field, so they are activated
here rather than quantified over.  They are `local instance 100` rather than
global because a global `Algebra ℝ (E →L[𝕜] E)` makes Lean's `•` elaborator drop
an author-written `((r : ℝ) : 𝕜) •` coercion. -/
attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

/-- **Davis--Kahan 1970, Definition 3.1.**

A unitary intertwining the two projections, whose two diagonal `U`-compressions
are *positive operators* and whose crossed blocks are skew-paired.  The
positivity is recorded as `IsDirectRotation`'s numerical-range signs together
with self-adjointness, which is equivalent and composes with the existing API.

The weaker `IsDirectRotation` is the right predicate for the Halmos geometry and
the wrong one for the paper's Sections 3 and 4; see the module docstring. -/
structure IsSourceDirectRotation (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (D : H →L[𝕜] H) : Prop
    extends IsDirectRotation U V D where
  /-- The source diagonal compression `C₀` is self-adjoint; with the inherited
  numerical-range sign this is `C₀ ≥ 0`. -/
  source_compression_isSelfAdjoint :
    IsSelfAdjoint (U.starProjection * D * U.starProjection)
  /-- The complementary diagonal compression `C₁` is self-adjoint; with the
  inherited numerical-range sign this is `C₁ ≥ 0`. -/
  complement_compression_isSelfAdjoint :
    IsSelfAdjoint ((Uᗮ).starProjection * D * (Uᗮ).starProjection)

namespace IsSourceDirectRotation

variable {U V : Submodule 𝕜 H} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
variable {D : H →L[𝕜] H}

/-- The source diagonal compression is a positive operator: Definition 3.1's
`C₀ ≥ 0`. -/
theorem source_compression_isPositive (h : IsSourceDirectRotation U V D) :
    (U.starProjection * D * U.starProjection).IsPositive :=
  ContinuousLinearMap.isPositive_def'.mpr
    ⟨h.source_compression_isSelfAdjoint, fun x => by
      have := h.source_compression_nonnegative x
      rwa [ContinuousLinearMap.reApplyInnerSelf_apply,
        ← inner_re_symm (𝕜 := 𝕜) x _]⟩

/-- Definition 3.1's `C₁ ≥ 0`. -/
theorem complement_compression_isPositive (h : IsSourceDirectRotation U V D) :
    ((Uᗮ).starProjection * D * (Uᗮ).starProjection).IsPositive :=
  ContinuousLinearMap.isPositive_def'.mpr
    ⟨h.complement_compression_isSelfAdjoint, fun x => by
      have := h.complement_compression_nonnegative x
      rwa [ContinuousLinearMap.reApplyInnerSelf_apply,
        ← inner_re_symm (𝕜 := 𝕜) x _]⟩

/-- **Proposition 3.3's square identity**, for the source predicate. -/
theorem sq_eq (h : IsSourceDirectRotation U V D) :
    D * D = V.reflectionOperator * U.reflectionOperator :=
  sq_eq_reflectionProduct U V D h.unitary_mem h.intertwines
    h.source_compression_isSelfAdjoint h.complement_compression_isSelfAdjoint
    h.crossed_blocks

/-- A direct rotation is accretive, so its Hermitian part is nonnegative. -/
theorem add_star_nonneg (h : IsSourceDirectRotation U V D) : 0 ≤ D + star D := by
  refine (ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mpr
    (ContinuousLinearMap.isPositive_def'.mpr ⟨?_, fun x => ?_⟩)
  · exact IsSelfAdjoint.add_star_self D
  · have hre := re_inner_directRotation_nonneg U V D h.toIsDirectRotation x
    have hstar : RCLike.re ⟪(star D) x, x⟫_𝕜 = RCLike.re ⟪x, D x⟫_𝕜 := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    have hD : RCLike.re ⟪D x, x⟫_𝕜 = RCLike.re ⟪x, D x⟫_𝕜 :=
      inner_re_symm (𝕜 := 𝕜) (D x) x
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, add_apply,
      inner_add_left, map_add, hstar, hD]
    linarith

end IsSourceDirectRotation

section HermitianPart

variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

omit [CompleteSpace H] in
/-- **The Halmos cosine square in projection coordinates.**  `P_U P_V P_U`
together with the complementary block is `1 − P_U − P_V + P_V P_U + P_U P_V`. -/
theorem halmosCosineSq_eq_projection_expansion :
    halmosCosineSq U V = 1 - U.starProjection - V.starProjection
      + V.starProjection * U.starProjection + U.starProjection * V.starProjection := by
  have hP : U.starProjection * U.starProjection = U.starProjection :=
    U.isIdempotentElem_starProjection
  have hPc : (Uᗮ).starProjection = 1 - U.starProjection :=
    Submodule.starProjection_orthogonal' U
  have hQc : (Vᗮ).starProjection = 1 - V.starProjection :=
    Submodule.starProjection_orthogonal' V
  have hexp : (1 - U.starProjection) * (1 - V.starProjection) * (1 - U.starProjection)
      = 1 - U.starProjection - V.starProjection + V.starProjection * U.starProjection
        + U.starProjection * V.starProjection - U.starProjection * V.starProjection *
          U.starProjection
        - U.starProjection + U.starProjection * U.starProjection := by noncomm_ring
  rw [halmosCosineSq, hPc, hQc, hexp, hP]
  abel

/-- `4 |C|² = J_V J_U + J_U J_V + 2`: the square of twice the canonical modulus,
computed from the projection algebra alone. -/
theorem absoluteValue_double_mul_self :
    (ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) +
        ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)) *
      (ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) +
        ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)) =
      V.reflectionOperator * U.reflectionOperator +
        U.reflectionOperator * V.reflectionOperator + 1 + 1 := by
  have hAA := Proposition35.section3CanonicalAbsoluteValue_mul_self_eq_halmosCosineSq U V
  have hRU : U.reflectionOperator = U.starProjection + U.starProjection - 1 :=
    reflectionOperator_eq_projection_add_projection_sub_one U
  have hRV : V.reflectionOperator = V.starProjection + V.starProjection - 1 :=
    reflectionOperator_eq_projection_add_projection_sub_one V
  have hexpand : (ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) +
        ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)) *
      (ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) +
        ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)) =
      halmosCosineSq U V + halmosCosineSq U V + halmosCosineSq U V
        + halmosCosineSq U V := by
    rw [← hAA]; noncomm_ring
  rw [hexpand, halmosCosineSq_eq_projection_expansion, hRU, hRV]
  noncomm_ring

/-- **The Hermitian part of a Definition 3.1 direct rotation is `2 |C|`.**

Both sides are nonnegative and have the same square, and a nonnegative operator
has a unique nonnegative square root. -/
theorem IsSourceDirectRotation.add_star_eq_two_absoluteValue {D : H →L[𝕜] H}
    (h : IsSourceDirectRotation U V D) :
    D + star D =
      ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) +
        ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) := by
  have hDs : D * star D = 1 := Unitary.mul_star_self_of_mem h.unitary_mem
  have hsD : star D * D = 1 := Unitary.star_mul_self_of_mem h.unitary_mem
  have hstarsq : star D * star D = U.reflectionOperator * V.reflectionOperator := by
    have hst := congrArg star h.sq_eq
    rw [star_mul, star_mul, star_reflectionOperator_complex U,
      star_reflectionOperator_complex V] at hst
    exact hst
  have hsq : (D + star D) * (D + star D) =
      V.reflectionOperator * U.reflectionOperator +
        U.reflectionOperator * V.reflectionOperator + 1 + 1 := by
    have hstep : (D + star D) * (D + star D) =
        D * D + D * star D + (star D * D + star D * star D) := by noncomm_ring
    rw [hstep, h.sq_eq, hstarsq, hDs, hsD]
    abel
  have h1 := CFC.sqrt_unique hsq h.add_star_nonneg
  have h2 := CFC.sqrt_unique (absoluteValue_double_mul_self U V)
    (add_nonneg (ContinuousLinearMap.modulus_nonneg _)
      (ContinuousLinearMap.modulus_nonneg _))
  exact h1.symm.trans h2

/-- **Every two Definition 3.1 direct rotations of the same pair have the same
Hermitian part**, hence the same displacement modulus. -/
theorem IsSourceDirectRotation.add_star_eq {D₁ D₂ : H →L[𝕜] H}
    (h₁ : IsSourceDirectRotation U V D₁) (h₂ : IsSourceDirectRotation U V D₂) :
    D₁ + star D₁ = D₂ + star D₂ :=
  (h₁.add_star_eq_two_absoluteValue U V).trans
    (h₂.add_star_eq_two_absoluteValue U V).symm

/-- The nonacute construction realizes the same Hermitian part, so it may be used
as the comparison rotation for any Definition 3.1 direct rotation. -/
theorem IsSourceDirectRotation.add_star_eq_nonacuteDirectRotation {D : H →L[𝕜] H}
    (h : IsSourceDirectRotation U V D)
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    D + star D = nonacuteDirectRotation U V J + star (nonacuteDirectRotation U V J) :=
  (h.add_star_eq_two_absoluteValue U V).trans
    (nonacuteDirectRotation_add_star_eq_two_absoluteValue U V J).symm

/-- For a unitary `T`, the Gram operator of the displacement is `2 − (T + T⋆)`. -/
theorem star_one_sub_mul_one_sub_of_unitary {T : H →L[𝕜] H}
    (hT : T ∈ unitary (H →L[𝕜] H)) :
    star (1 - T) * (1 - T) = 1 + 1 - (T + star T) := by
  have hsT : star T * T = 1 := Unitary.star_mul_self_of_mem hT
  have hexp : (1 - star T) * (1 - T) = 1 - T - star T + star T * T := by noncomm_ring
  rw [star_sub, star_one, hexp, hsT]
  abel

/-- **The displacement is pointwise the same for every Definition 3.1 direct
rotation.**  Its Gram operator is `2 − (D + D⋆)`, and the Hermitian part does not
depend on which direct rotation is taken. -/
theorem norm_one_sub_apply_eq_of_isSourceDirectRotation {D : H →L[𝕜] H}
    (h : IsSourceDirectRotation U V D)
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) (x : H) :
    ‖(1 - D) x‖ = ‖(1 - nonacuteDirectRotation U V J) x‖ := by
  have hgram : star (1 - D) * (1 - D) =
      star (1 - nonacuteDirectRotation U V J) * (1 - nonacuteDirectRotation U V J) := by
    rw [star_one_sub_mul_one_sub_of_unitary h.unitary_mem,
      star_one_sub_mul_one_sub_of_unitary (nonacuteDirectRotation_mem_unitary U V J),
      IsSourceDirectRotation.add_star_eq_nonacuteDirectRotation U V h J]
  have hmod : (1 - D).modulus = (1 - nonacuteDirectRotation U V J).modulus := by
    rw [ContinuousLinearMap.modulus_def, ContinuousLinearMap.modulus_def]
    exact congrArg CFC.sqrt hgram
  rw [← ContinuousLinearMap.norm_modulus_apply (1 - D) x,
    ← ContinuousLinearMap.norm_modulus_apply (1 - nonacuteDirectRotation U V J) x, hmod]

end HermitianPart

end DavisKahan
end TauCeti
