/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


public import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.GenericRotationPredicates
public import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotationSquare

/-! # Section3Elementary -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Elementary Section 3 bridge

This file contains the Section 3 results that can be completed directly from
the production Halmos and acute direct-rotation developments without first
building spectral multiplicity theory.

-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan



universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Restrict a bounded operator to a closed invariant subspace. -/
noncomputable def restrictToInvariantSubspace
    (A : H →L[ℂ] H) (M : Submodule ℂ H)
    (hA : ∀ x : H, x ∈ M → A x ∈ M) :
    M →L[ℂ] M :=
  (A ∘L M.subtypeL).codRestrict M fun x =>
    hA (x : H) x.property

omit [CompleteSpace H] in
/-- The restriction to an invariant subspace acts as the original operator on the underlying
vector. -/
@[simp]
theorem coe_restrictToInvariantSubspace_apply
    (A : H →L[ℂ] H) (M : Submodule ℂ H)
    (hA : ∀ x : H, x ∈ M → A x ∈ M) (x : M) :
    ((restrictToInvariantSubspace A M hA x : M) : H) = A (x : H) :=
  rfl

omit [CompleteSpace H] in
/-- The complementary source projection preserves the generic Halmos part. -/
theorem complementaryProjection_mem_halmosGenericPart_left
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {x : H}
    (hx : x ∈ halmosGenericPart U V) :
    (Uᗮ).starProjection x ∈ halmosGenericPart U V := by
  rw [U.starProjection_orthogonal_apply]
  exact (halmosGenericPart U V).sub_mem hx
    (projection_mem_halmosGenericPart_left U V hx)

omit [CompleteSpace H] in
/-- The complementary target projection preserves the generic Halmos part. -/
theorem complementaryProjection_mem_halmosGenericPart_right
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {x : H}
    (hx : x ∈ halmosGenericPart U V) :
    (Vᗮ).starProjection x ∈ halmosGenericPart U V := by
  rw [V.starProjection_orthogonal_apply]
  exact (halmosGenericPart U V).sub_mem hx
    (projection_mem_halmosGenericPart_right U V hx)

omit [CompleteSpace H] in
/-- The Halmos cosine square preserves the generic summand. -/
theorem halmosCosineSq_mem_generic
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {x : H}
    (hx : x ∈ halmosGenericPart U V) :
    halmosCosineSq U V x ∈ halmosGenericPart U V := by
  unfold halmosCosineSq
  simp only [add_apply, mul_apply_eq_comp]
  apply (halmosGenericPart U V).add_mem
  · exact projection_mem_halmosGenericPart_left U V
      (projection_mem_halmosGenericPart_right U V
        (projection_mem_halmosGenericPart_left U V hx))
  · exact complementaryProjection_mem_halmosGenericPart_left U V
      (complementaryProjection_mem_halmosGenericPart_right U V
        (complementaryProjection_mem_halmosGenericPart_left U V hx))

omit [CompleteSpace H] in
/-- The Halmos sine square preserves the generic summand. -/
theorem halmosSineSq_mem_generic
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {x : H}
    (hx : x ∈ halmosGenericPart U V) :
    halmosSineSq U V x ∈ halmosGenericPart U V := by
  unfold halmosSineSq
  simp only [add_apply, mul_apply_eq_comp]
  apply (halmosGenericPart U V).add_mem
  · exact projection_mem_halmosGenericPart_left U V
      (complementaryProjection_mem_halmosGenericPart_right U V
        (projection_mem_halmosGenericPart_left U V hx))
  · exact complementaryProjection_mem_halmosGenericPart_left U V
      (projection_mem_halmosGenericPart_right U V
        (complementaryProjection_mem_halmosGenericPart_left U V hx))

/-- Concrete restriction of the Halmos cosine square to the generic part. -/
noncomputable def genericHalmosCosineSqCompleted
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    halmosGenericPart U V →L[ℂ] halmosGenericPart U V :=
  restrictToInvariantSubspace (halmosCosineSq U V)
    (halmosGenericPart U V) fun _ hx =>
      halmosCosineSq_mem_generic U V hx

/-- Concrete restriction of the Halmos sine square to the generic part. -/
noncomputable def genericHalmosSineSqCompleted
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    halmosGenericPart U V →L[ℂ] halmosGenericPart U V :=
  restrictToInvariantSubspace (halmosSineSq U V)
    (halmosGenericPart U V) fun _ hx =>
      halmosSineSq_mem_generic U V hx

omit [CompleteSpace H] in
/-- The restricted generic cosine and sine squares resolve the identity. -/
theorem genericHalmosCosineSqCompleted_add_sineSq
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    genericHalmosCosineSqCompleted U V +
      genericHalmosSineSqCompleted U V = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  have h := congrArg
    (fun T : H →L[ℂ] H => T (x : H))
    (halmosCosineSq_add_sineSq U V)
  simpa only [genericHalmosCosineSqCompleted,
    genericHalmosSineSqCompleted, add_apply, Submodule.coe_add,
    coe_restrictToInvariantSubspace_apply, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_apply] using h

omit [CompleteSpace H] in
/-- The paper's two crossed intersections are definitionally the two Halmos
defect subspaces. -/
theorem crossed_intersections_are_halmos_defects_completed
    (U V : Submodule ℂ H) :
    halmosSourceDefect U V = U ⊓ Vᗮ ∧
      halmosTargetDefect U V = Uᗮ ⊓ V :=
  ⟨rfl, rfl⟩

section GenericCompression

/-! This one compression identity is pure projection algebra: no functional
calculus, no acuteness, and no complex structure.  It is therefore stated over
an arbitrary `RCLike` field, which is what
`DavisKahan/Geometry/Polar/Section3Nonacute.lean` -- the only consumer outside
this file -- needs in order to be scalar-generic itself. -/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Real part of the quadratic form of a compression by an orthogonal
projection. -/
theorem re_inner_projection_compression
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →L[𝕜] E) (x : E) :
    RCLike.re
        ⟪x, (U.starProjection * A * U.starProjection) x⟫_𝕜 =
      RCLike.re ⟪A (U.starProjection x), U.starProjection x⟫_𝕜 := by
  have hsymm := U.starProjection_isSymmetric
  have h1 :
      ⟪U.starProjection (A (U.starProjection x)), x⟫_𝕜 =
        ⟪A (U.starProjection x), U.starProjection x⟫_𝕜 :=
    hsymm (A (U.starProjection x)) x
  calc
    RCLike.re
        ⟪x, (U.starProjection * A * U.starProjection) x⟫_𝕜 =
      RCLike.re
        ⟪U.starProjection (A (U.starProjection x)), x⟫_𝕜 := by
          simp only [mul_apply_eq_comp]
          exact inner_re_symm x _
    _ = RCLike.re ⟪A (U.starProjection x), U.starProjection x⟫_𝕜 :=
      congrArg RCLike.re h1

end GenericCompression

/-- The acute canonical direct rotation has nonnegative source compression. -/
theorem spectraDirectRotation_sourceCompression_nonnegative
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsUniformlyAcute U V) (x : H) :
    0 ≤ RCLike.re
      ⟪x, (U.starProjection * spectraDirectRotation U V hacute *
        U.starProjection) x⟫_ℂ := by
  let C := ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)
  have hdiag :=
    projection_mul_spectraDirectRotation_mul_projection U V hacute
  have hform :
      RCLike.re
          ⟪x, (U.starProjection * spectraDirectRotation U V hacute *
            U.starProjection) x⟫_ℂ =
        RCLike.re ⟪C (U.starProjection x), U.starProjection x⟫_ℂ := by
    rw [hdiag]
    have hcomm : Commute C (U.starProjection) :=
      spectraCanonicalAbsoluteValue_commute_projection U V
    calc
      RCLike.re ⟪x, (C * U.starProjection) x⟫_ℂ =
          RCLike.re
            ⟪x, (U.starProjection * C * U.starProjection) x⟫_ℂ := by
              simp only [mul_apply_eq_comp]
              have hfix :
                  U.starProjection (C (U.starProjection x)) =
                    C (U.starProjection x) := by
                calc
                  U.starProjection (C (U.starProjection x)) =
                      C (U.starProjection (U.starProjection x)) := by
                        simpa only [mul_apply_eq_comp, Function.comp_apply]
                          using congrArg
                            (fun T : H →L[ℂ] H => T (U.starProjection x))
                            hcomm.eq.symm
                  _ = C (U.starProjection x) := by
                    have hidem : U.starProjection (U.starProjection x) = U.starProjection x :=
                      U.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)
                    rw [hidem]
              rw [hfix]
      _ = RCLike.re ⟪C (U.starProjection x), U.starProjection x⟫_ℂ :=
        re_inner_projection_compression U C x
  rw [hform]
  have hnonneg : (0 : H →L[ℂ] H) ≤ C :=
    ContinuousLinearMap.modulus_nonneg _
  have hpositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive (f := C)).mp hnonneg
  exact hpositive.re_inner_nonneg_left (U.starProjection x)

/-- The acute canonical direct rotation has nonnegative complementary
compression. -/
theorem spectraDirectRotation_complementCompression_nonnegative
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsUniformlyAcute U V) (x : H) :
    0 ≤ RCLike.re
      ⟪x, ((Uᗮ).starProjection *
        spectraDirectRotation U V hacute *
        (Uᗮ).starProjection) x⟫_ℂ := by
  let C := ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)
  have hdiag :=
    complementaryProjection_mul_spectraDirectRotation_mul_complementaryProjection
      U V hacute
  have hform :
      RCLike.re
          ⟪x, ((Uᗮ).starProjection *
            spectraDirectRotation U V hacute *
            (Uᗮ).starProjection) x⟫_ℂ =
        RCLike.re
          ⟪C ((Uᗮ).starProjection x),
            (Uᗮ).starProjection x⟫_ℂ := by
    rw [hdiag]
    have hcomm : Commute C ((Uᗮ).starProjection) := by
      have hcomp : (Uᗮ).starProjection = 1 - U.starProjection :=
        Submodule.starProjection_orthogonal' U
      -- Left as a `rw` chain on purpose: `simp only` with this same list leaves the goal unsolved:
      -- at least one lemma here has to fire at one occurrence, in order, and simp's normal form
      -- loses the intermediate shape.
      rw [commute_iff_eq, hcomp, mul_sub, mul_one, sub_mul, one_mul,
        (spectraCanonicalAbsoluteValue_commute_projection U V).eq]
    calc
      RCLike.re ⟪x, (C * (Uᗮ).starProjection) x⟫_ℂ =
          RCLike.re
            ⟪x, ((Uᗮ).starProjection * C *
              (Uᗮ).starProjection) x⟫_ℂ := by
              simp only [mul_apply_eq_comp]
              have hfix :
                  (Uᗮ).starProjection
                      (C ((Uᗮ).starProjection x)) =
                    C ((Uᗮ).starProjection x) := by
                calc
                  (Uᗮ).starProjection
                      (C ((Uᗮ).starProjection x)) =
                    C ((Uᗮ).starProjection
                      ((Uᗮ).starProjection x)) := by
                        simpa only [mul_apply_eq_comp, Function.comp_apply]
                          using congrArg
                            (fun T : H →L[ℂ] H =>
                              T ((Uᗮ).starProjection x))
                            hcomm.eq.symm
                  _ = C ((Uᗮ).starProjection x) := by
                    have hidem :
                        (Uᗮ).starProjection
                            ((Uᗮ).starProjection x) =
                          (Uᗮ).starProjection x :=
                      Uᗮ.starProjection_eq_self_iff.mpr
                        (Uᗮ.starProjection_apply_mem x)
                    rw [hidem]
              rw [hfix]
      _ = RCLike.re
          ⟪C ((Uᗮ).starProjection x),
            (Uᗮ).starProjection x⟫_ℂ :=
        re_inner_projection_compression Uᗮ C x
  rw [hform]
  have hnonneg : (0 : H →L[ℂ] H) ≤ C :=
    ContinuousLinearMap.modulus_nonneg _
  have hpositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive (f := C)).mp hnonneg
  exact hpositive.re_inner_nonneg_left ((Uᗮ).starProjection x)

/-- The crossed source blocks of the acute canonical direct rotation are
skew-adjoint. -/
theorem spectraDirectRotation_crossed_blocks
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsUniformlyAcute U V) :
    (Uᗮ).starProjection * spectraDirectRotation U V hacute *
        U.starProjection =
      -star (U.starProjection * spectraDirectRotation U V hacute *
        (Uᗮ).starProjection) := by
  let D := spectraDirectRotation U V hacute
  let C := ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)
  let P := U.starProjection
  let Pc := (Uᗮ).starProjection
  have hsum : D + star D = C + C := by
    simpa only [D, C, two_smul] using
      spectraDirectRotation_add_star_eq_two_smul_absoluteValue U V hacute
  have hCP : Commute C P :=
    spectraCanonicalAbsoluteValue_commute_projection U V
  have hPcCP : Pc * C * P = 0 := by
    calc
      Pc * C * P = Pc * P * C := by
        rw [mul_assoc, hCP.eq, ← mul_assoc]
      _ = 0 := by rw [complementaryProjection_mul_projection, zero_mul]
  have hcompressed := congrArg (fun T : H →L[ℂ] H => Pc * T * P) hsum
  have hzero : Pc * D * P + Pc * star D * P = 0 := by
    simpa only [mul_add, add_mul, hPcCP, add_zero] using hcompressed
  have hP : star P = P := (isSelfAdjoint_starProjection U).star_eq
  have hPc : star Pc = Pc := (isSelfAdjoint_starProjection Uᗮ).star_eq
  have hstar :
      star (P * D * Pc) = Pc * star D * P := by
    rw [star_mul, star_mul, hP, hPc, mul_assoc]
  calc
    Pc * D * P = -(Pc * star D * P) := eq_neg_of_add_eq_zero_left hzero
    _ = -star (P * D * Pc) := by rw [hstar]

/-- The acute Spectra direct rotation satisfies the paper's block definition. -/
theorem spectraDirectRotation_isDirectRotation
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsUniformlyAcute U V) :
    IsDirectRotation U V (spectraDirectRotation U V hacute) where
  unitary_mem := spectraDirectRotation_mem_unitary U V hacute
  intertwines := spectraDirectRotation_intertwines U V hacute
  source_compression_nonnegative :=
    spectraDirectRotation_sourceCompression_nonnegative U V hacute
  complement_compression_nonnegative :=
    spectraDirectRotation_complementCompression_nonnegative U V hacute
  crossed_blocks := spectraDirectRotation_crossed_blocks U V hacute

/-- Davis--Kahan 1970, Corollary 3.2: reversing the ordered pair takes the
adjoint of the canonical direct rotation. -/
theorem corollary3_2_reversal_completed
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsUniformlyAcute U V) :
    spectraDirectRotation V U hacute.symm =
      star (spectraDirectRotation U V hacute) :=
  spectraDirectRotation_reversal U V hacute

end DavisKahan
end TauCeti
