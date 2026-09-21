/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotationSquare
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.FormTransport
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.ModulusTransport

/-!
# The direct rotation of two **real** closed subspaces

Standing assumption 1 of Davis--Kahan 1970 is that the Hilbert space is "real or
complex", and Section 3 is written at that generality.  The repository's original Section 3
construction was developed over `ℂ` and then descended through real complexification.  The
canonical bounded modulus and polar decomposition are now available directly over arbitrary
`RCLike` fields; this module retains the real-complexification identities needed by the
source-facing real development.

## The descent, and why it is available

`spectraDirectRotation U V` is the polar factor of the canonical intertwiner
`S = P_V P_U + P_Vᗮ P_Uᗮ`.  When `U` and `V` are complexifications of real
subspaces, `S` is the complexification of the corresponding real operator, hence
fixed by the canonical conjugation.  In the acute case `|S|` is invertible, and

  `W |S| = S`,  `conj |S| = |conj S| = |S|`,  `conj S = S`

force `conj W = W` by cancelling the unit `|S|`.  So the direct rotation itself
lies in the fixed-point algebra of the conjugation and therefore **is** the
complexification of a bounded operator on the real space
(`TauCeti.RealComplexification.complexify_realPartOperator`).

The one input that was missing before 2026-08-09 is
`TauCeti.RealComplexification.conjugateOperator_modulus`: the canonical
conjugation commutes with the operator modulus, with no continuity side
condition.

## What is proved here

`directRotationR U V hacute` is a bounded operator on the real space, and every
clause of Propositions 3.1 and 3.3 and of Corollary 3.2 is proved *about it*, as
a statement over `ℝ`: it is orthogonal, it intertwines the two projections, it
carries `U` onto `V` and `Uᗮ` onto `Vᗮ`, its square is the ordered reflection
product, its two diagonal blocks are the positive Halmos cosine, its numerical
range is nonnegative, positivity of the two diagonal blocks characterises it,
and reversing the pair takes its transpose.

Membership statements are *concluded*, not assumed: `directRotationR_maps_subspace`
concludes `U.map W = V` rather than taking it as a hypothesis.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: Definition 3.1, Propositions 3.1
  and 3.3, Corollary 3.2, and standing assumption 1.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

variable (U V : Submodule ℝ E)
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-! ## Acuteness of a real pair -/

omit [CompleteSpace E] in
/-- Acuteness of a real pair is symmetric.  The complex statement of this fact
lives in a `ℂ`-only section, so the real case is proved here from the same
scalar-generic ingredient. -/
theorem IsUniformlyAcuteReal.symm {U V : Submodule ℝ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : IsUniformlyAcute U V) : IsUniformlyAcute V U :=
  (Submodule.projectionGap_comm V U).trans_lt h

omit [CompleteSpace E] in
/-- Acuteness of a real pair passes to the complexified pair. -/
theorem isUniformlyAcute_complexifySubmodule (h : IsUniformlyAcute U V) :
    IsUniformlyAcute (complexifySubmodule U) (complexifySubmodule V) :=
  (isUniformlyAcute_complexifySubmodule_iff U V).2 h

/-! ## The real canonical intertwiner -/

/-- The canonical pre-polar intertwiner `P_V P_U + P_Vᗮ P_Uᗮ` of a **real**
pair. -/
def canonicalIntertwinerR : E →L[ℝ] E :=
  V.starProjection * U.starProjection +
    (Vᗮ).starProjection * (Uᗮ).starProjection

omit [CompleteSpace E] in
/-- The complexified real intertwiner is the intertwiner of the complexified
pair. -/
@[simp]
theorem complexify_canonicalIntertwinerR :
    complexify (canonicalIntertwinerR U V) =
      spectraCanonicalIntertwiner (complexifySubmodule U) (complexifySubmodule V) := by
  have hmul : ∀ A B : E →L[ℝ] E, complexify (A * B) = complexify A * complexify B := by
    intro A B
    simpa only [ContinuousLinearMap.mul_def] using complexify_comp A B
  change complexify (V.starProjection * U.starProjection +
      Vᗮ.starProjection * Uᗮ.starProjection) =
    (complexifySubmodule V).starProjection * (complexifySubmodule U).starProjection +
      (complexifySubmodule V)ᗮ.starProjection * (complexifySubmodule U)ᗮ.starProjection
  rw [starProjection_complexifySubmodule, starProjection_complexifySubmodule,
    starProjection_complexifySubmodule_orthogonal,
    starProjection_complexifySubmodule_orthogonal, complexify_add, hmul, hmul]

omit [CompleteSpace E] in
/-- The complexified intertwiner is fixed by the canonical conjugation. -/
theorem conjugateOperator_spectraCanonicalIntertwiner_complexifySubmodule :
    conjugateOperator
        (spectraCanonicalIntertwiner (complexifySubmodule U) (complexifySubmodule V)) =
      spectraCanonicalIntertwiner (complexifySubmodule U) (complexifySubmodule V) := by
  rw [← complexify_canonicalIntertwinerR]
  exact conjugateOperator_complexify _

/-- The modulus of the complexified intertwiner is fixed by the canonical
conjugation. -/
theorem conjugateOperator_spectraCanonicalAbsoluteValue_complexifySubmodule :
    conjugateOperator
        (ContinuousLinearMap.modulus
          (spectraCanonicalIntertwiner (complexifySubmodule U) (complexifySubmodule V))) =
      ContinuousLinearMap.modulus
        (spectraCanonicalIntertwiner (complexifySubmodule U) (complexifySubmodule V)) :=
  conjugateOperator_modulus_of_fixed
    (conjugateOperator_spectraCanonicalIntertwiner_complexifySubmodule U V)

/-- The positive Halmos cosine `|S|` of a **real** pair. -/
def canonicalAbsoluteValueR : E →L[ℝ] E :=
  realPartOperator
    (ContinuousLinearMap.modulus
      (spectraCanonicalIntertwiner (complexifySubmodule U) (complexifySubmodule V)))

/-- The complexified real Halmos cosine is the modulus of the complexified
intertwiner. -/
@[simp]
theorem complexify_canonicalAbsoluteValueR :
    complexify (canonicalAbsoluteValueR U V) =
      ContinuousLinearMap.modulus
        (spectraCanonicalIntertwiner (complexifySubmodule U) (complexifySubmodule V)) :=
  complexify_realPartOperator
    (conjugateOperator_spectraCanonicalAbsoluteValue_complexifySubmodule U V)

/-! ## The real direct rotation -/

variable {U V}

omit [CompleteSpace E] in
/-- Cancelling an invertible conjugation-fixed right factor.  If `W C = S` with
`C` invertible and both `C` and `S` conjugation-fixed, then so is `W`. -/
private theorem conjugateOperator_of_mul_unit
    {W C S : RealComplexification E →L[ℂ] RealComplexification E}
    (hCunit : IsUnit C) (hWC : W * C = S)
    (hC : conjugateOperator C = C) (hS : conjugateOperator S = S) :
    conjugateOperator W = W := by
  refine hCunit.mul_right_cancel ?_
  calc
    conjugateOperator W * C = conjugateOperator W * conjugateOperator C := by rw [hC]
    _ = conjugateOperator (W * C) := (conjugateOperator_mul _ _).symm
    _ = conjugateOperator S := by rw [hWC]
    _ = S := hS
    _ = W * C := hWC.symm

/-- The complexified direct rotation of a real acute pair is fixed by the
canonical conjugation: cancel the invertible modulus in `W |S| = S`. -/
theorem conjugateOperator_spectraDirectRotation_complexifySubmodule
    (hacute : IsUniformlyAcute U V) :
    conjugateOperator
        (spectraDirectRotation (complexifySubmodule U) (complexifySubmodule V)
          (isUniformlyAcute_complexifySubmodule U V hacute)) =
      spectraDirectRotation (complexifySubmodule U) (complexifySubmodule V)
        (isUniformlyAcute_complexifySubmodule U V hacute) := by
  refine conjugateOperator_of_mul_unit
    (isUnit_spectraCanonicalAbsoluteValue _ _
      (isUniformlyAcute_complexifySubmodule U V hacute))
    (S := spectraCanonicalIntertwiner (complexifySubmodule U) (complexifySubmodule V))
    ?_
    (conjugateOperator_spectraCanonicalAbsoluteValue_complexifySubmodule U V)
    (conjugateOperator_spectraCanonicalIntertwiner_complexifySubmodule U V)
  simpa only [ContinuousLinearMap.mul_def] using
    spectraDirectRotation_decomposition (complexifySubmodule U) (complexifySubmodule V)
      (isUniformlyAcute_complexifySubmodule U V hacute)

variable (U V)

/-- **The direct rotation of a pair of real closed subspaces**, in arbitrary
dimension: a bounded operator on the real Hilbert space.

Davis--Kahan 1970, Definition 3.1 and Proposition 3.1, over `ℝ`. -/
def directRotationR (hacute : IsUniformlyAcute U V) : E →L[ℝ] E :=
  realPartOperator
    (spectraDirectRotation (complexifySubmodule U) (complexifySubmodule V)
      (isUniformlyAcute_complexifySubmodule U V hacute))

/-- The complexified real direct rotation is the complex direct rotation of the
complexified pair.  This is the identity that makes every clause below a
statement about the real operator. -/
@[simp]
theorem complexify_directRotationR (hacute : IsUniformlyAcute U V) :
    complexify (directRotationR U V hacute) =
      spectraDirectRotation (complexifySubmodule U) (complexifySubmodule V)
        (isUniformlyAcute_complexifySubmodule U V hacute) :=
  complexify_realPartOperator
    (conjugateOperator_spectraDirectRotation_complexifySubmodule hacute)

/-! ### Transport toolkit

`complexify` is an injective unital `⋆`-algebra map from the real bounded
operators to the operators on the complexification, so every *identity* below is
proved by complexifying it and citing the complex theorem. -/

omit [CompleteSpace E] in
/-- Complexification is multiplicative for the operator product. -/
theorem complexify_mul (A B : E →L[ℝ] E) :
    complexify (A * B) = complexify A * complexify B := by
  simpa only [ContinuousLinearMap.mul_def] using complexify_comp A B

omit [CompleteSpace E] in
/-- Complexification is unital. -/
theorem complexify_one : complexify (1 : E →L[ℝ] E) = 1 := complexify_id

/-- Complexification commutes with the adjoint written as `star`. -/
theorem complexify_star (A : E →L[ℝ] E) :
    complexify (star A) = star (complexify A) := by
  simpa only [ContinuousLinearMap.star_eq_adjoint] using complexify_adjoint A

omit [CompleteSpace E] in
/-- Complexification carries the real reflection to the reflection through the
complexified subspace. -/
@[simp]
theorem complexify_reflectionOperator :
    complexify U.reflectionOperator = (complexifySubmodule U).reflectionOperator := by
  rw [Submodule.reflectionOperator_eq_two_smul_sub_id,
    Submodule.reflectionOperator_eq_two_smul_sub_id, complexify_sub,
    complexify_real_smul, complexify_id, starProjection_complexifySubmodule]
  norm_num

omit [CompleteSpace E] in
/-- Complexification carries the real orthogonal projection to the projection
onto the complexified subspace. -/

theorem complexify_projection :
    complexify (U.starProjection) = Submodule.starProjection (complexifySubmodule U) :=
  (starProjection_complexifySubmodule U).symm

omit [CompleteSpace E] in
/-- Complexification carries the real complementary projection to the
complementary projection of the complexified subspace. -/

theorem complexify_complementaryProjection :
    complexify ((Uᗮ).starProjection) =
      Submodule.starProjection ((complexifySubmodule U)ᗮ) :=
  (starProjection_complexifySubmodule_orthogonal U).symm

/-- Complexification carries an orthogonal operator to a unitary one. -/
theorem complexify_mem_unitary {W : E →L[ℝ] E} (hW : W ∈ unitary (E →L[ℝ] E)) :
    complexify W ∈
      unitary (RealComplexification E →L[ℂ] RealComplexification E) := by
  rw [Unitary.mem_iff] at hW ⊢
  refine ⟨?_, ?_⟩
  · rw [← complexify_star, ← complexify_mul, hW.1, complexify_one]
  · rw [← complexify_star, ← complexify_mul, hW.2, complexify_one]

/-- Complexification reflects orthogonality. -/
theorem mem_unitary_of_complexify {W : E →L[ℝ] E}
    (hW : complexify W ∈
      unitary (RealComplexification E →L[ℂ] RealComplexification E)) :
    W ∈ unitary (E →L[ℝ] E) := by
  rw [Unitary.mem_iff] at hW ⊢
  refine ⟨complexify_injective ?_, complexify_injective ?_⟩
  · rw [complexify_mul, complexify_star, complexify_one]; exact hW.1
  · rw [complexify_mul, complexify_star, complexify_one]; exact hW.2

omit [CompleteSpace E] in
/-- The real quadratic form is the complexified quadratic form on the real
copy. -/
theorem re_inner_complexify_ofReal (A : E →L[ℝ] E) (x : E) :
    Complex.re ⟪complexify A (ofReal x), ofReal x⟫_ℂ = ⟪A x, x⟫_ℝ := by
  have h := re_inner_complexify A (ofReal x)
  simp only [re_ofReal, im_ofReal, inner_zero_left, map_zero, add_zero] at h
  simpa only [RCLike.re_eq_complex_re] using h

omit [CompleteSpace E] in
/-- A nonnegative real quadratic form complexifies to a nonnegative one. -/
theorem re_inner_complexify_nonneg {A : E →L[ℝ] E}
    (h : ∀ x, 0 ≤ ⟪A x, x⟫_ℝ) (z : RealComplexification E) :
    0 ≤ Complex.re ⟪complexify A z, z⟫_ℂ := by
  have hz := re_inner_complexify A z
  rw [RCLike.re_eq_complex_re] at hz
  rw [hz]
  exact add_nonneg (h _) (h _)

omit [CompleteSpace E] in
/-- A quadratic form nonnegative on a real subspace complexifies to one
nonnegative on the complexified subspace. -/
theorem re_inner_complexify_nonneg_of_mem {A : E →L[ℝ] E} {W : Submodule ℝ E}
    (h : ∀ x ∈ W, 0 ≤ ⟪A x, x⟫_ℝ) {z : RealComplexification E}
    (hz : z ∈ complexifySubmodule W) :
    0 ≤ Complex.re ⟪complexify A z, z⟫_ℂ := by
  obtain ⟨hre, him⟩ := mem_complexifySubmodule.mp hz
  have hz' := re_inner_complexify A z
  rw [RCLike.re_eq_complex_re] at hz'
  rw [hz']
  exact add_nonneg (h _ hre) (h _ him)

/-! ### Proposition 3.1: the direct rotation is orthogonal and intertwines -/

/-- **The real direct rotation is orthogonal.** -/
theorem directRotationR_mem_unitary (hacute : IsUniformlyAcute U V) :
    directRotationR U V hacute ∈ unitary (E →L[ℝ] E) := by
  refine mem_unitary_of_complexify ?_
  rw [complexify_directRotationR]
  exact spectraDirectRotation_mem_unitary (complexifySubmodule U)
    (complexifySubmodule V) (isUniformlyAcute_complexifySubmodule U V hacute)

/-- The transpose is a left inverse of the real direct rotation. -/
theorem star_directRotationR_mul_self (hacute : IsUniformlyAcute U V) :
    star (directRotationR U V hacute) * directRotationR U V hacute = 1 :=
  Unitary.star_mul_self_of_mem (directRotationR_mem_unitary U V hacute)

/-- The transpose is a right inverse of the real direct rotation. -/
theorem directRotationR_mul_star_self (hacute : IsUniformlyAcute U V) :
    directRotationR U V hacute * star (directRotationR U V hacute) = 1 :=
  Unitary.mul_star_self_of_mem (directRotationR_mem_unitary U V hacute)

/-- The real direct rotation preserves norms. -/
theorem norm_directRotationR_apply (hacute : IsUniformlyAcute U V) (x : E) :
    ‖directRotationR U V hacute x‖ = ‖x‖ :=
  Unitary.norm_map
    (⟨directRotationR U V hacute, directRotationR_mem_unitary U V hacute⟩ :
      unitary (E →L[ℝ] E)) x

/-- The real direct rotation is surjective. -/
theorem directRotationR_surjective (hacute : IsUniformlyAcute U V) :
    Function.Surjective (directRotationR U V hacute) := by
  intro y
  refine ⟨star (directRotationR U V hacute) y, ?_⟩
  have h := congrArg (fun T : E →L[ℝ] E => T y) (directRotationR_mul_star_self U V hacute)
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using h

/-- The real direct rotation is injective. -/
theorem directRotationR_injective (hacute : IsUniformlyAcute U V) :
    Function.Injective (directRotationR U V hacute) := by
  intro x y hxy
  have hx := norm_directRotationR_apply U V hacute (x - y)
  rw [map_sub, hxy, sub_self, norm_zero] at hx
  exact sub_eq_zero.mp (norm_eq_zero.mp hx.symm)

/-- **The real direct rotation intertwines the two orthogonal projections.** -/
theorem directRotationR_intertwines (hacute : IsUniformlyAcute U V) :
    directRotationR U V hacute * U.starProjection =
      V.starProjection * directRotationR U V hacute := by
  refine complexify_injective ?_
  rw [complexify_mul, complexify_mul, complexify_directRotationR,
    complexify_projection, complexify_projection]
  exact spectraDirectRotation_intertwines _ _ _

/-- The real direct rotation intertwines the complementary projections. -/
theorem directRotationR_intertwines_complementary (hacute : IsUniformlyAcute U V) :
    directRotationR U V hacute * (Uᗮ).starProjection =
      (Vᗮ).starProjection * directRotationR U V hacute := by
  refine complexify_injective ?_
  rw [complexify_mul, complexify_mul, complexify_directRotationR,
    complexify_complementaryProjection, complexify_complementaryProjection]
  exact spectraDirectRotation_intertwines_complementary _ _ _

/-- Conjugating the source projection by the real direct rotation gives the
target projection. -/
theorem directRotationR_conjugates_projection (hacute : IsUniformlyAcute U V) :
    directRotationR U V hacute * U.starProjection * star (directRotationR U V hacute) =
      V.starProjection := by
  refine complexify_injective ?_
  rw [complexify_mul, complexify_mul, complexify_star, complexify_directRotationR,
    complexify_projection, complexify_projection]
  exact spectraDirectRotation_conjugates_projection _ _ _

/-- **The real direct rotation carries `U` onto `V`.**  The membership is
concluded, not assumed. -/
theorem directRotationR_maps_subspace (hacute : IsUniformlyAcute U V) :
    U.map (directRotationR U V hacute).toLinearMap = V := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    apply V.starProjection_eq_self_iff.mp
    have h := congrArg (fun T : E →L[ℝ] E => T x) (directRotationR_intertwines U V hacute)
    simp only [mul_apply_eq_comp] at h
    rw [U.starProjection_eq_self_iff.mpr hx] at h
    exact h.symm
  · intro y hy
    obtain ⟨x, rfl⟩ := directRotationR_surjective U V hacute y
    refine ⟨x, ?_, rfl⟩
    apply U.starProjection_eq_self_iff.mp
    apply directRotationR_injective U V hacute
    have h := congrArg (fun T : E →L[ℝ] E => T x) (directRotationR_intertwines U V hacute)
    simp only [mul_apply_eq_comp] at h
    rw [V.starProjection_eq_self_iff.mpr hy] at h
    exact h

/-- The real direct rotation carries `Uᗮ` onto `Vᗮ`. -/
theorem directRotationR_maps_orthogonalComplement (hacute : IsUniformlyAcute U V) :
    Uᗮ.map (directRotationR U V hacute).toLinearMap = Vᗮ := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    apply Vᗮ.starProjection_eq_self_iff.mp
    have h := congrArg (fun T : E →L[ℝ] E => T x)
      (directRotationR_intertwines_complementary U V hacute)
    simp only [mul_apply_eq_comp] at h
    rw [Uᗮ.starProjection_eq_self_iff.mpr hx] at h
    exact h.symm
  · intro y hy
    obtain ⟨x, rfl⟩ := directRotationR_surjective U V hacute y
    refine ⟨x, ?_, rfl⟩
    apply Uᗮ.starProjection_eq_self_iff.mp
    apply directRotationR_injective U V hacute
    have h := congrArg (fun T : E →L[ℝ] E => T x)
      (directRotationR_intertwines_complementary U V hacute)
    simp only [mul_apply_eq_comp] at h
    rw [Vᗮ.starProjection_eq_self_iff.mpr hy] at h
    exact h

/-! ### Proposition 3.3: the principal square root -/

/-- The real direct rotation intertwines the two reflections. -/
theorem directRotationR_intertwines_reflection (hacute : IsUniformlyAcute U V) :
    directRotationR U V hacute * U.reflectionOperator =
      V.reflectionOperator * directRotationR U V hacute := by
  refine complexify_injective ?_
  rw [complexify_mul, complexify_mul, complexify_directRotationR,
    complexify_reflectionOperator, complexify_reflectionOperator]
  exact spectraDirectRotation_intertwines_reflection _ _ _

/-- **Davis--Kahan 1970, Proposition 3.3, over `ℝ`, forward direction.**  The
square of the real direct rotation is the ordered product of the two
reflections. -/
theorem directRotationR_sq (hacute : IsUniformlyAcute U V) :
    directRotationR U V hacute * directRotationR U V hacute =
      V.reflectionOperator * U.reflectionOperator := by
  refine complexify_injective ?_
  rw [complexify_mul, complexify_mul, complexify_directRotationR,
    complexify_reflectionOperator, complexify_reflectionOperator]
  exact spectraDirectRotation_sq _ _ _

/-! ### The Hermitian part and the two diagonal blocks -/

/-- **The symmetric part of the real direct rotation is twice the positive
Halmos cosine.**  This is the "principal" clause of Proposition 3.3: the
symmetric part is nonnegative. -/
theorem directRotationR_add_star (hacute : IsUniformlyAcute U V) :
    directRotationR U V hacute + star (directRotationR U V hacute) =
      (2 : ℝ) • canonicalAbsoluteValueR U V := by
  refine complexify_injective ?_
  rw [complexify_add, complexify_star, complexify_real_smul,
    complexify_directRotationR, complexify_canonicalAbsoluteValueR]
  simpa using spectraDirectRotation_add_star_eq_two_smul_absoluteValue
    (complexifySubmodule U) (complexifySubmodule V)
    (isUniformlyAcute_complexifySubmodule U V hacute)

/-- **The source diagonal block of the real direct rotation is the positive
Halmos cosine.**  Proposition 3.1's block computation, over `ℝ`. -/
theorem projection_mul_directRotationR_mul_projection (hacute : IsUniformlyAcute U V) :
    U.starProjection * directRotationR U V hacute * U.starProjection =
      canonicalAbsoluteValueR U V * U.starProjection := by
  refine complexify_injective ?_
  rw [complexify_mul, complexify_mul, complexify_mul, complexify_directRotationR,
    complexify_canonicalAbsoluteValueR, complexify_projection]
  exact projection_mul_spectraDirectRotation_mul_projection _ _ _

/-- The complementary diagonal block of the real direct rotation is the positive
Halmos cosine. -/
theorem complementaryProjection_mul_directRotationR_mul_complementaryProjection
    (hacute : IsUniformlyAcute U V) :
    (Uᗮ).starProjection * directRotationR U V hacute * (Uᗮ).starProjection =
      canonicalAbsoluteValueR U V * (Uᗮ).starProjection := by
  refine complexify_injective ?_
  rw [complexify_mul, complexify_mul, complexify_mul, complexify_directRotationR,
    complexify_canonicalAbsoluteValueR, complexify_complementaryProjection]
  exact complementaryProjection_mul_spectraDirectRotation_mul_complementaryProjection _ _ _

/-- **The numerical range of the real direct rotation is nonnegative.** -/
theorem directRotationR_real_inner_nonneg (hacute : IsUniformlyAcute U V) (x : E) :
    0 ≤ ⟪directRotationR U V hacute x, x⟫_ℝ := by
  rw [← re_inner_complexify_ofReal (directRotationR U V hacute) x,
    complexify_directRotationR]
  exact spectraDirectRotation_real_inner_nonneg _ _ _ _

/-! ### Proposition 3.1: uniqueness and the characterisation clause -/

/-- **Davis--Kahan 1970, Proposition 3.1, uniqueness clause, over `ℝ`.**  An
orthogonal square root of the reflection product with nonnegative numerical
range is the direct rotation. -/
theorem directRotationR_unique_of_sq (hacute : IsUniformlyAcute U V)
    (W : E →L[ℝ] E) (hWunit : W ∈ unitary (E →L[ℝ] E))
    (hsq : W * W = V.reflectionOperator * U.reflectionOperator)
    (hre : ∀ x, 0 ≤ ⟪W x, x⟫_ℝ) :
    W = directRotationR U V hacute := by
  refine complexify_injective ?_
  rw [complexify_directRotationR]
  refine spectraDirectRotation_unique_of_sq _ _ _ (complexify W)
    (complexify_mem_unitary hWunit) ?_ (re_inner_complexify_nonneg hre)
  rw [← complexify_mul, hsq, complexify_mul, complexify_reflectionOperator,
    complexify_reflectionOperator]

/-- **Davis--Kahan 1970, Proposition 3.1, characterisation clause, over `ℝ`.**
Nonnegativity of the two diagonal blocks characterises the direct rotation among
orthogonal square roots of the reflection product that intertwine the two
reflections. -/
theorem directRotationR_unique_of_diagonalBlocks (hacute : IsUniformlyAcute U V)
    (W : E →L[ℝ] E) (hWunit : W ∈ unitary (E →L[ℝ] E))
    (hsq : W * W = V.reflectionOperator * U.reflectionOperator)
    (hint : W * U.reflectionOperator = V.reflectionOperator * W)
    (hblockU : ∀ x ∈ U, 0 ≤ ⟪W x, x⟫_ℝ)
    (hblockUperp : ∀ x ∈ Uᗮ, 0 ≤ ⟪W x, x⟫_ℝ) :
    W = directRotationR U V hacute := by
  refine complexify_injective ?_
  rw [complexify_directRotationR]
  refine spectraDirectRotation_unique_of_diagonalBlocks _ _ _ (complexify W)
    (complexify_mem_unitary hWunit) ?_ ?_ ?_ ?_
  · rw [← complexify_mul, hsq, complexify_mul, complexify_reflectionOperator,
      complexify_reflectionOperator]
  · rw [← complexify_reflectionOperator, ← complexify_reflectionOperator,
      ← complexify_mul, ← complexify_mul, hint]
  · exact fun z hz => re_inner_complexify_nonneg_of_mem hblockU hz
  · refine fun z hz => re_inner_complexify_nonneg_of_mem hblockUperp ?_
    rwa [complexifySubmodule_orthogonal U]

/-- **Proposition 3.1's characterisation clause as a biconditional, over `ℝ`.** -/
theorem eq_directRotationR_iff_diagonalBlocks_nonneg (hacute : IsUniformlyAcute U V)
    (W : E →L[ℝ] E) :
    W = directRotationR U V hacute ↔
      W ∈ unitary (E →L[ℝ] E) ∧
        W * W = V.reflectionOperator * U.reflectionOperator ∧
        W * U.reflectionOperator = V.reflectionOperator * W ∧
        (∀ x ∈ U, 0 ≤ ⟪W x, x⟫_ℝ) ∧
        (∀ x ∈ Uᗮ, 0 ≤ ⟪W x, x⟫_ℝ) := by
  constructor
  · rintro rfl
    exact ⟨directRotationR_mem_unitary U V hacute, directRotationR_sq U V hacute,
      directRotationR_intertwines_reflection U V hacute,
      fun x _ => directRotationR_real_inner_nonneg U V hacute x,
      fun x _ => directRotationR_real_inner_nonneg U V hacute x⟩
  · rintro ⟨hWunit, hsq, hint, hblockU, hblockUperp⟩
    exact directRotationR_unique_of_diagonalBlocks U V hacute W hWunit hsq hint
      hblockU hblockUperp

/-! ### Proposition 3.1's third clause over `ℝ`, from the printed hypotheses

The two theorems above assume the square identity (3.8), which the printed clause does not;
`spectraDirectRotation_unique_of_diagonalBlocks_pos` removes it over `ℂ` and this section
transports that.

**Property (i) is a strictly stronger condition over `ℝ` than the pointwise sign condition
used above.**  Definition 3.1(i) is `C₀ ≥ 0`, `C₁ ≥ 0` — positive *operators*, so symmetric.
Over `ℂ` an operator with nonnegative quadratic form is automatically self-adjoint, so
`∀ x ∈ U, 0 ≤ ⟪W x, x⟫_ℂ` already says it.  Over `ℝ` it does not: on `E = ℝ⁴` with
`U = V = span (e₀, e₁)`, the orthogonal `W = R ⊕ 1` with `R` a plane rotation by `π/3`
commutes with `P_U` and has `⟪W x, x⟫ = cos (π/3) ‖x‖² ≥ 0` on both blocks, yet is not the
direct rotation `1`.  So over `ℝ` the hypothesis has to be `IsPositive` of the compression,
which carries symmetry as well as the sign. -/

section PrintedThirdClause

open scoped ComplexOrder

omit [CompleteSpace E] in
/-- **A positive diagonal block complexifies to a positive one.**

The complexified quadratic form on the complexified subspace has imaginary part
`⟪A (re z), im z⟫ - ⟪A (im z), re z⟫`, and it is symmetry of the compression — the half of
`IsPositive` that a pointwise sign condition does not supply over `ℝ` — that makes it
vanish. -/
theorem inner_complexify_nonneg_of_isPositive_compression
    {A : E →L[ℝ] E} {W : Submodule ℝ E} [W.HasOrthogonalProjection]
    (h : (W.starProjection * A * W.starProjection).IsPositive)
    {z : RealComplexification E} (hz : z ∈ complexifySubmodule W) :
    0 ≤ ⟪complexify A z, z⟫_ℂ := by
  obtain ⟨hzre, hzim⟩ := mem_complexifySubmodule.mp hz
  -- On the block, `A` agrees with its compression.
  have hagree : ∀ x ∈ W, ∀ y ∈ W,
      ⟪A x, y⟫_ℝ = ⟪(W.starProjection * A * W.starProjection) x, y⟫_ℝ := by
    intro x hx y hy
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      Submodule.starProjection_eq_self_iff.mpr hx,
      Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hy]
  have hB : ⟪(W.starProjection * A * W.starProjection) (re z), im z⟫_ℝ =
      ⟪re z, (W.starProjection * A * W.starProjection) (im z)⟫_ℝ := h.isSymmetric _ _
  have hsym : ⟪A (re z), im z⟫_ℝ = ⟪A (im z), re z⟫_ℝ := by
    calc ⟪A (re z), im z⟫_ℝ
        = ⟪(W.starProjection * A * W.starProjection) (re z), im z⟫_ℝ :=
          hagree _ hzre _ hzim
      _ = ⟪re z, (W.starProjection * A * W.starProjection) (im z)⟫_ℝ := hB
      _ = ⟪(W.starProjection * A * W.starProjection) (im z), re z⟫_ℝ :=
          real_inner_comm _ _
      _ = ⟪A (im z), re z⟫_ℝ := (hagree _ hzim _ hzre).symm
  have hre : (0 : ℝ) ≤ ⟪A (re z), re z⟫_ℝ + ⟪A (im z), im z⟫_ℝ := by
    rw [hagree _ hzre _ hzre, hagree _ hzim _ hzim]
    exact add_nonneg (h.inner_nonneg_left _) (h.inner_nonneg_left _)
  refine RCLike.nonneg_iff.mpr ⟨?_, ?_⟩
  · rw [RCLike.re_to_complex]
    exact hre
  · rw [RCLike.im_to_complex]
    change ⟪A (re z), im z⟫_ℝ - ⟪A (im z), re z⟫_ℝ = 0
    rw [hsym, sub_self]

/-- **Davis--Kahan 1970, Proposition 3.1, third clause, over `ℝ`.**

Among the orthogonal `W` with `W P_U = P_V W`, the direct rotation is exactly the one whose
two diagonal blocks are positive operators.  The square identity (3.8) is not assumed. -/
theorem directRotationR_unique_of_diagonalBlocks_pos (hacute : IsUniformlyAcute U V)
    (W : E →L[ℝ] E) (hWunit : W ∈ unitary (E →L[ℝ] E))
    (hint : W * U.starProjection = V.starProjection * W)
    (hblockU : (U.starProjection * W * U.starProjection).IsPositive)
    (hblockUperp : (Uᗮ.starProjection * W * Uᗮ.starProjection).IsPositive) :
    W = directRotationR U V hacute := by
  refine complexify_injective ?_
  rw [complexify_directRotationR]
  refine spectraDirectRotation_unique_of_diagonalBlocks_pos _ _ _ (complexify W)
    (complexify_mem_unitary hWunit) ?_ ?_ ?_
  · rw [starProjection_complexifySubmodule, starProjection_complexifySubmodule,
      ← complexify_mul, ← complexify_mul, hint]
  · exact fun z hz => inner_complexify_nonneg_of_isPositive_compression hblockU hz
  · refine fun z hz => inner_complexify_nonneg_of_isPositive_compression hblockUperp ?_
    rwa [complexifySubmodule_orthogonal U]

/-! #### The converse: the real direct rotation *has* positive diagonal blocks

The complex converse `eq_spectraDirectRotation_iff_diagonalBlocks_pos` reads the sign of the
blocks off `ContinuousLinearMap.modulus_nonneg`.  Over `ℝ` the block condition is
`IsPositive` of the compression, which carries symmetry as well, so the descent is of
*operator positivity* and not of a pointwise sign: `isPositive_of_complexify` below reflects
both halves, and the compression step is then elementary. -/

/-- **Operator positivity descends through the complexification.**

Complexification reflects both halves of `IsPositive` separately: self-adjointness by
`complexify_isSelfAdjoint_iff`, and the sign by evaluating the complexified quadratic form
on the real copy.  This is the exact converse of
`inner_complexify_nonneg_of_isPositive_compression`, which pushes a *compressed* form the
other way. -/
theorem isPositive_of_complexify {A : E →L[ℝ] E}
    (h : (complexify A).IsPositive) : A.IsPositive := by
  refine (ContinuousLinearMap.isPositive_iff' A).mpr ⟨?_, fun x => ?_⟩
  · exact (complexify_isSelfAdjoint_iff A).mp h.isSelfAdjoint
  · rw [← re_inner_complexify_ofReal A x]
    simpa only [RCLike.re_eq_complex_re] using h.re_inner_nonneg_left (ofReal x)

omit [CompleteSpace E] in
/-- **The compression of a positive operator to a closed subspace is positive.**

Symmetry survives because the projection is symmetric, and the sign because the compressed
quadratic form is the original one evaluated at the projected vector. -/
private theorem isPositive_starProjection_compression {A : E →L[ℝ] E}
    (hA : A.IsPositive) (W : Submodule ℝ E) [W.HasOrthogonalProjection] :
    (W.starProjection * A * W.starProjection).IsPositive := by
  refine (ContinuousLinearMap.isPositive_iff _).mpr ⟨fun x y => ?_, fun x => ?_⟩
  · change ⟪W.starProjection (A (W.starProjection x)), y⟫_ℝ =
      ⟪x, W.starProjection (A (W.starProjection y))⟫_ℝ
    calc ⟪W.starProjection (A (W.starProjection x)), y⟫_ℝ
        = ⟪A (W.starProjection x), W.starProjection y⟫_ℝ :=
          Submodule.inner_starProjection_left_eq_right W _ _
      _ = ⟪W.starProjection x, A (W.starProjection y)⟫_ℝ :=
          hA.inner_left_eq_inner_right _ _
      _ = ⟪x, W.starProjection (A (W.starProjection y))⟫_ℝ :=
          Submodule.inner_starProjection_left_eq_right W _ _
  · change 0 ≤ ⟪W.starProjection (A (W.starProjection x)), x⟫_ℝ
    rw [Submodule.inner_starProjection_left_eq_right W]
    exact hA.inner_nonneg_left _

/-- **The real Halmos cosine `|S|` is a positive operator.**

Descended from `ContinuousLinearMap.modulus_nonneg` on the complexification. -/
theorem isPositive_canonicalAbsoluteValueR :
    (canonicalAbsoluteValueR U V).IsPositive := by
  refine isPositive_of_complexify ?_
  rw [complexify_canonicalAbsoluteValueR]
  exact (ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mp
    (ContinuousLinearMap.modulus_nonneg _)

/-- Rewriting a diagonal block of the real direct rotation as a compression of the Halmos
cosine.  Multiplying `P A P = |S| P` on the left by the idempotent `P` replaces the loose
right factor by a two-sided compression. -/
private theorem starProjection_compression_eq_of_block {A : E →L[ℝ] E} {W : Submodule ℝ E}
    [W.HasOrthogonalProjection] (h : W.starProjection * A * W.starProjection =
      canonicalAbsoluteValueR U V * W.starProjection) :
    W.starProjection * A * W.starProjection =
      W.starProjection * canonicalAbsoluteValueR U V * W.starProjection := by
  have hPP : (W.starProjection : E →L[ℝ] E) * W.starProjection = W.starProjection :=
    W.isIdempotentElem_starProjection
  calc W.starProjection * A * W.starProjection
      = W.starProjection * (W.starProjection * A * W.starProjection) := by
        rw [← mul_assoc, ← mul_assoc, hPP]
    _ = W.starProjection * (canonicalAbsoluteValueR U V * W.starProjection) := by rw [h]
    _ = W.starProjection * canonicalAbsoluteValueR U V * W.starProjection := by
        rw [mul_assoc]

/-- **The source diagonal block of the real direct rotation is a positive operator.**

Property (i) of Definition 3.1 for the source block, over `ℝ`, in the `IsPositive` form the
printed third clause needs. -/
theorem isPositive_projection_mul_directRotationR_mul_projection
    (hacute : IsUniformlyAcute U V) :
    (U.starProjection * directRotationR U V hacute * U.starProjection).IsPositive := by
  rw [starProjection_compression_eq_of_block U V
    (projection_mul_directRotationR_mul_projection U V hacute)]
  exact isPositive_starProjection_compression (isPositive_canonicalAbsoluteValueR U V) U

/-- **The complementary diagonal block of the real direct rotation is a positive
operator.** -/
theorem isPositive_complementaryProjection_mul_directRotationR_mul_complementaryProjection
    (hacute : IsUniformlyAcute U V) :
    (Uᗮ.starProjection * directRotationR U V hacute * Uᗮ.starProjection).IsPositive := by
  rw [starProjection_compression_eq_of_block U V
    (complementaryProjection_mul_directRotationR_mul_complementaryProjection U V hacute)]
  exact isPositive_starProjection_compression (isPositive_canonicalAbsoluteValueR U V) Uᗮ

/-- **Davis--Kahan 1970, Proposition 3.1, third clause as a biconditional, over `ℝ`.**

`W` is the real direct rotation exactly when it is orthogonal, intertwines the two
orthogonal projections, and has positive diagonal blocks.  The square identity (3.8) is
neither assumed nor listed: it is a consequence.  Contrast
`eq_directRotationR_iff_diagonalBlocks_nonneg`, which lists (3.8) among the conditions and
weakens the blocks to a pointwise sign; that is also correct, but it is not the printed
clause, which is by "property (i)" alone.

Over `ℝ` the block condition must be `IsPositive` of the compression rather than a
pointwise sign: see the section note above for the `ℝ⁴` rotation that separates them. -/
theorem eq_directRotationR_iff_diagonalBlocks_pos (hacute : IsUniformlyAcute U V)
    (W : E →L[ℝ] E) :
    W = directRotationR U V hacute ↔
      W ∈ unitary (E →L[ℝ] E) ∧
        W * U.starProjection = V.starProjection * W ∧
        (U.starProjection * W * U.starProjection).IsPositive ∧
        (Uᗮ.starProjection * W * Uᗮ.starProjection).IsPositive := by
  constructor
  · rintro rfl
    exact ⟨directRotationR_mem_unitary U V hacute, directRotationR_intertwines U V hacute,
      isPositive_projection_mul_directRotationR_mul_projection U V hacute,
      isPositive_complementaryProjection_mul_directRotationR_mul_complementaryProjection
        U V hacute⟩
  · rintro ⟨hWunit, hint, hblockU, hblockUperp⟩
    exact directRotationR_unique_of_diagonalBlocks_pos U V hacute W hWunit hint
      hblockU hblockUperp

end PrintedThirdClause

/-! ### Corollary 3.2: reversal symmetry -/

/-- **Davis--Kahan 1970, Corollary 3.2, over `ℝ`.**  Reversing the ordered pair
transposes the direct rotation. -/
theorem directRotationR_reversal (hacute : IsUniformlyAcute U V) :
    directRotationR V U (IsUniformlyAcuteReal.symm hacute) =
      star (directRotationR U V hacute) := by
  refine complexify_injective ?_
  rw [complexify_star, complexify_directRotationR, complexify_directRotationR]
  exact spectraDirectRotation_reversal (complexifySubmodule U) (complexifySubmodule V)
    (isUniformlyAcute_complexifySubmodule U V hacute)

end

end DavisKahan
end TauCeti
