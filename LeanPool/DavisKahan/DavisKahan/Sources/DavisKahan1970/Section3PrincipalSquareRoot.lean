/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.PrincipalSquareRoot
-- supplies `IsPrincipalUnitarySquareRoot` together with both halves of Proposition 3.3 at
-- the arbitrary-pair scope.  It is a `Geometry` module.
import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotationBlocks
-- supplies the two reflection/projection identities this file needs,
-- `projection_mul_reflectionOperator_self` and `reflectionOperator_mul_projection_self`.
-- It is a `Geometry` module.
import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotationReal

/-! # Section3Principal Square Root -/

open TauCeti.DavisKahan.Angle


/-!
# Davis--Kahan 1970, Proposition 3.3, at the printed nonacute scope

The arbitrary-pair complex mathematics is owned by
`DavisKahan.Geometry.Polar.PrincipalSquareRoot`: every paper direct rotation with genuinely
positive diagonal blocks is a principal unitary square root of the reflection
product, and every principal square root carrying the source crossed defect onto
the target crossed defect is a direct rotation. Neither theorem assumes
acuteness.

This file exposes that exact source surface and transports it to real Hilbert
spaces. For a bounded real operator, "principal" means exactly that its
canonical complexification is the principal square root of the complexified
reflection product. This avoids introducing a second, weaker real branch
condition.
-/

open scoped InnerProductSpace ComplexOrder

namespace TauCeti
namespace DavisKahan1970

open DavisKahan
open TauCeti.RealComplexification
open DavisKahan.Foundation.RealComplexification

/-! ## Complex source-facing form -/

section Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- A principal square root satisfying the crossed-defect condition has genuinely
positive diagonal blocks. The arbitrary-pair converse already supplies the
paper direct-rotation predicate; the square identity and intertwining relation
make its diagonal compressions self-adjoint, upgrading their numerical-range
signs to operator positivity. -/
private theorem principalSquareRoot_positiveDiagonalBlocks
    (T : H →L[ℂ] H)
    (hroot : IsPrincipalUnitarySquareRoot (spectraReflectionProduct U V) T)
    (hT : DavisKahan.IsDirectRotation U V T) :
    (U.starProjection * T * U.starProjection).IsPositive ∧
      (Uᗮ.starProjection * T * Uᗮ.starProjection).IsPositive := by
  have hintR : T * U.reflectionOperator = V.reflectionOperator * T := by
    rw [DavisKahan.reflectionOperator_eq_projection_add_projection_sub_one U,
      DavisKahan.reflectionOperator_eq_projection_add_projection_sub_one V,
      mul_sub, mul_add, mul_one, sub_mul, add_mul, one_mul, hT.intertwines]
  have hconj : U.reflectionOperator * T * U.reflectionOperator = star T :=
    DavisKahan.reflection_conjugate_eq_star_of_sq_of_intertwines
      U V T hroot.unitary_mem hroot.square_eq hintR
  have hsource_sa : IsSelfAdjoint (U.starProjection * T * U.starProjection) := by
    rw [IsSelfAdjoint, star_mul, star_mul,
      (isSelfAdjoint_starProjection U).star_eq]
    calc
      U.starProjection * star T * U.starProjection =
          U.starProjection * (U.reflectionOperator * T * U.reflectionOperator) *
            U.starProjection := by rw [hconj]
      _ = (U.starProjection * U.reflectionOperator) * T *
            (U.reflectionOperator * U.starProjection) := by
          simp only [mul_assoc]
      _ = U.starProjection * T * U.starProjection := by
          rw [projection_mul_reflectionOperator_self U,
            reflectionOperator_mul_projection_self U]
  have hRsub : U.reflectionOperator = U.starProjection - Uᗮ.starProjection := by
    rw [DavisKahan.reflectionOperator_eq_projection_add_projection_sub_one U]
    have hsum : U.starProjection + Uᗮ.starProjection = (1 : H →L[ℂ] H) := by
      apply ContinuousLinearMap.ext
      intro x
      simpa only [add_apply, one_apply_eq_self] using
        U.starProjection_add_starProjection_orthogonal x
    rw [← hsum]
    abel
  have hPcR : Uᗮ.starProjection * U.reflectionOperator = -Uᗮ.starProjection := by
    rw [hRsub, mul_sub, DavisKahan.complementaryProjection_mul_projection U,
      DavisKahan.complementaryProjection_sq U, zero_sub]
  have hRPc : U.reflectionOperator * Uᗮ.starProjection = -Uᗮ.starProjection := by
    rw [hRsub, sub_mul, DavisKahan.projection_mul_complementaryProjection U,
      DavisKahan.complementaryProjection_sq U, zero_sub]
  have hcomplement_sa : IsSelfAdjoint (Uᗮ.starProjection * T * Uᗮ.starProjection) := by
    rw [IsSelfAdjoint, star_mul, star_mul,
      (isSelfAdjoint_starProjection Uᗮ).star_eq]
    calc
      Uᗮ.starProjection * star T * Uᗮ.starProjection =
          Uᗮ.starProjection * (U.reflectionOperator * T * U.reflectionOperator) *
            Uᗮ.starProjection := by rw [hconj]
      _ = (Uᗮ.starProjection * U.reflectionOperator) * T *
            (U.reflectionOperator * Uᗮ.starProjection) := by
          simp only [mul_assoc]
      _ = (-Uᗮ.starProjection) * T * (-Uᗮ.starProjection) := by rw [hPcR, hRPc]
      _ = Uᗮ.starProjection * T * Uᗮ.starProjection := by noncomm_ring
  constructor
  · refine ContinuousLinearMap.isPositive_def'.mpr ⟨hsource_sa, fun x => ?_⟩
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm (𝕜 := ℂ)]
    exact hT.source_compression_nonnegative x
  · refine ContinuousLinearMap.isPositive_def'.mpr ⟨hcomplement_sa, fun x => ?_⟩
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm (𝕜 := ℂ)]
    exact hT.complement_compression_nonnegative x

/-- **Davis--Kahan 1970, Proposition 3.3, forward direction over `ℂ`, at the
printed nonacute scope.** Every direct rotation is the principal unitary square
root of the ordered reflection product. -/
theorem proposition3_3_complex_forward
    (T : H →L[ℂ] H)
    (hunitary : T ∈ unitary (H →L[ℂ] H))
    (hintertwines : T * U.starProjection = V.starProjection * T)
    (hsource_pos : (U.starProjection * T * U.starProjection).IsPositive)
    (hcomplement_pos : (Uᗮ.starProjection * T * Uᗮ.starProjection).IsPositive)
    (hcrossed : Uᗮ.starProjection * T * U.starProjection =
      -star (U.starProjection * T * Uᗮ.starProjection)) :
    IsPrincipalUnitarySquareRoot (spectraReflectionProduct U V) T := by
  have hsource_nonneg : (0 : H →L[ℂ] H) ≤ U.starProjection * T * U.starProjection :=
    (ContinuousLinearMap.nonneg_iff_isPositive
      (U.starProjection * T * U.starProjection)).mpr hsource_pos
  have hcomplement_nonneg : (0 : H →L[ℂ] H) ≤
      Uᗮ.starProjection * T * Uᗮ.starProjection :=
    (ContinuousLinearMap.nonneg_iff_isPositive
      (Uᗮ.starProjection * T * Uᗮ.starProjection)).mpr hcomplement_pos
  exact (proposition3_3_principalSquareRoot_forward_of_nonneg_blocks
    U V T hunitary hintertwines hcrossed hsource_nonneg hcomplement_nonneg).2.1

/-- **Davis--Kahan 1970, Proposition 3.3, converse direction over `ℂ`, at the
printed nonacute scope.** A principal square root carrying the source crossed
intersection onto the target crossed intersection satisfies Definition 3.1,
including genuine positivity of its two diagonal blocks. -/
theorem proposition3_3_complex_converse
    (T : H →L[ℂ] H)
    (hroot : IsPrincipalUnitarySquareRoot (spectraReflectionProduct U V) T)
    (hcross : T '' (halmosSourceDefect U V : Set H) =
      (halmosTargetDefect U V : Set H)) :
    T ∈ unitary (H →L[ℂ] H) ∧
      T * U.starProjection = V.starProjection * T ∧
      (U.starProjection * T * U.starProjection).IsPositive ∧
      (Uᗮ.starProjection * T * Uᗮ.starProjection).IsPositive ∧
      Uᗮ.starProjection * T * U.starProjection =
        -star (U.starProjection * T * Uᗮ.starProjection) := by
  have hT : DavisKahan.IsDirectRotation U V T :=
    proposition3_3_principalSquareRoot_converse U V T hroot hcross
  have hpos := principalSquareRoot_positiveDiagonalBlocks U V T hroot hT
  exact ⟨hT.unitary_mem, hT.intertwines, hpos.1, hpos.2, hT.crossed_blocks⟩

end Complex

/-! ## Real source-facing form -/

section Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- The paper's real principal square root: after canonical complexification,
the operator is the complex principal unitary square root of the complexified
ordered reflection product. -/
def IsRealPrincipalUnitarySquareRoot (T : E →L[ℝ] E) : Prop :=
  IsPrincipalUnitarySquareRoot
    (spectraReflectionProduct (complexifySubmodule U) (complexifySubmodule V))
    (complexify T)

private theorem isPositive_complexify {A : E →L[ℝ] E} (hA : A.IsPositive) :
    (complexify A).IsPositive := by
  refine ContinuousLinearMap.isPositive_def'.mpr ⟨?_, fun z => ?_⟩
  · exact (complexify_isSelfAdjoint_iff A).2 hA.isSelfAdjoint
  · rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    exact DavisKahan.re_inner_complexify_nonneg hA.inner_nonneg_left z

omit [CompleteSpace E] in
private theorem complexify_sourceCompression (T : E →L[ℝ] E) :
    complexify (U.starProjection * T * U.starProjection) =
      (complexifySubmodule U).starProjection * complexify T *
        (complexifySubmodule U).starProjection := by
  rw [DavisKahan.complexify_mul, DavisKahan.complexify_mul,
    starProjection_complexifySubmodule]

omit [CompleteSpace E] in
private theorem complexify_complementCompression (T : E →L[ℝ] E) :
    complexify (Uᗮ.starProjection * T * Uᗮ.starProjection) =
      (complexifySubmodule U)ᗮ.starProjection * complexify T *
        (complexifySubmodule U)ᗮ.starProjection := by
  rw [DavisKahan.complexify_mul, DavisKahan.complexify_mul,
    starProjection_complexifySubmodule_orthogonal]

omit [CompleteSpace E] [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] in
private theorem mem_complexified_sourceDefect_iff (z : RealComplexification E) :
    z ∈ halmosSourceDefect (complexifySubmodule U) (complexifySubmodule V) ↔
      re z ∈ halmosSourceDefect U V ∧ im z ∈ halmosSourceDefect U V := by
  simp only [mem_halmosSourceDefect, ← complexifySubmodule_orthogonal V,
    mem_complexifySubmodule]
  tauto

omit [CompleteSpace E] [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] in
private theorem mem_complexified_targetDefect_iff (z : RealComplexification E) :
    z ∈ halmosTargetDefect (complexifySubmodule U) (complexifySubmodule V) ↔
      re z ∈ halmosTargetDefect U V ∧ im z ∈ halmosTargetDefect U V := by
  simp only [mem_halmosTargetDefect, ← complexifySubmodule_orthogonal U,
    mem_complexifySubmodule]
  tauto

omit [CompleteSpace E] [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] in
private theorem complexify_crossedDefect_image_eq (T : E →L[ℝ] E)
    (hcross : T '' (halmosSourceDefect U V : Set E) =
      (halmosTargetDefect U V : Set E)) :
    complexify T ''
        (halmosSourceDefect (complexifySubmodule U) (complexifySubmodule V) :
          Set (RealComplexification E)) =
      (halmosTargetDefect (complexifySubmodule U) (complexifySubmodule V) :
        Set (RealComplexification E)) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : w ∈
        halmosSourceDefect (complexifySubmodule U) (complexifySubmodule V) := hw
    have hwparts : re w ∈ halmosSourceDefect U V ∧ im w ∈ halmosSourceDefect U V :=
      (mem_complexified_sourceDefect_iff U V w).mp hw'
    apply (mem_complexified_targetDefect_iff U V (complexify T w)).mpr
    simp only [re_complexify, im_complexify]
    constructor
    · have hmem : T (re w) ∈ T '' (halmosSourceDefect U V : Set E) :=
        ⟨re w, hwparts.1, rfl⟩
      rw [hcross] at hmem
      exact hmem
    · have hmem : T (im w) ∈ T '' (halmosSourceDefect U V : Set E) :=
        ⟨im w, hwparts.2, rfl⟩
      rw [hcross] at hmem
      exact hmem
  · intro hz
    have hz' : z ∈
        halmosTargetDefect (complexifySubmodule U) (complexifySubmodule V) := hz
    have hzparts : re z ∈ halmosTargetDefect U V ∧ im z ∈ halmosTargetDefect U V :=
      (mem_complexified_targetDefect_iff U V z).mp hz'
    have hre : re z ∈ T '' (halmosSourceDefect U V : Set E) := by
      rw [hcross]
      exact hzparts.1
    have him : im z ∈ T '' (halmosSourceDefect U V : Set E) := by
      rw [hcross]
      exact hzparts.2
    rcases hre with ⟨xr, hxr, hxr_eq⟩
    rcases him with ⟨xi, hxi, hxi_eq⟩
    refine ⟨mk xr xi, ?_, ?_⟩
    · apply (mem_complexified_sourceDefect_iff U V (mk xr xi)).mpr
      simpa using And.intro hxr hxi
    · apply RealComplexification.ext
      · simpa using hxr_eq
      · simpa using hxi_eq

/-- **Davis--Kahan 1970, Proposition 3.3, forward direction over `ℝ`, at the
printed nonacute scope.** Every real direct rotation is principal after
canonical complexification. -/
theorem proposition3_3_real_forward
    (T : E →L[ℝ] E)
    (hunitary : T ∈ unitary (E →L[ℝ] E))
    (hintertwines : T * U.starProjection = V.starProjection * T)
    (hsource_pos : (U.starProjection * T * U.starProjection).IsPositive)
    (hcomplement_pos : (Uᗮ.starProjection * T * Uᗮ.starProjection).IsPositive)
    (hcrossed : Uᗮ.starProjection * T * U.starProjection =
      -star (U.starProjection * T * Uᗮ.starProjection)) :
    IsRealPrincipalUnitarySquareRoot U V T := by
  let CU := complexifySubmodule U
  let CV := complexifySubmodule V
  let TC := complexify T
  have hunitaryC : TC ∈ unitary (RealComplexification E →L[ℂ] RealComplexification E) :=
    DavisKahan.complexify_mem_unitary hunitary
  have hintertwinesC : TC * CU.starProjection = CV.starProjection * TC := by
    dsimp only [CU, CV, TC]
    rw [starProjection_complexifySubmodule, starProjection_complexifySubmodule,
      ← DavisKahan.complexify_mul, ← DavisKahan.complexify_mul, hintertwines]
  have hcrossedC : CUᗮ.starProjection * TC * CU.starProjection =
      -star (CU.starProjection * TC * CUᗮ.starProjection) := by
    dsimp only [CU, TC]
    have h := congrArg (fun A : E →L[ℝ] E => complexify A) hcrossed
    simpa only [DavisKahan.complexify_mul, DavisKahan.complexify_star, complexify_neg,
      starProjection_complexifySubmodule, starProjection_complexifySubmodule_orthogonal]
      using h
  have hsource_posC : (CU.starProjection * TC * CU.starProjection).IsPositive := by
    dsimp only [CU, TC]
    rw [← complexify_sourceCompression U T]
    exact isPositive_complexify hsource_pos
  have hcomplement_posC :
      (CUᗮ.starProjection * TC * CUᗮ.starProjection).IsPositive := by
    dsimp only [CU, TC]
    rw [← complexify_complementCompression U T]
    exact isPositive_complexify hcomplement_pos
  simpa [IsRealPrincipalUnitarySquareRoot, CU, CV, TC] using
    proposition3_3_complex_forward CU CV TC hunitaryC hintertwinesC
      hsource_posC hcomplement_posC hcrossedC

/-- **Davis--Kahan 1970, Proposition 3.3, converse direction over `ℝ`, at the
printed nonacute scope.** A real principal square root carrying the source
crossed intersection onto the target one has all of Definition 3.1, including
positive diagonal blocks. -/
theorem proposition3_3_real_converse
    (T : E →L[ℝ] E)
    (hroot : IsRealPrincipalUnitarySquareRoot U V T)
    (hcross : T '' (halmosSourceDefect U V : Set E) =
      (halmosTargetDefect U V : Set E)) :
    T ∈ unitary (E →L[ℝ] E) ∧
      T * U.starProjection = V.starProjection * T ∧
      (U.starProjection * T * U.starProjection).IsPositive ∧
      (Uᗮ.starProjection * T * Uᗮ.starProjection).IsPositive ∧
      Uᗮ.starProjection * T * U.starProjection =
        -star (U.starProjection * T * Uᗮ.starProjection) := by
  let CU := complexifySubmodule U
  let CV := complexifySubmodule V
  let TC := complexify T
  have hrootC : IsPrincipalUnitarySquareRoot (spectraReflectionProduct CU CV) TC := by
    simpa [IsRealPrincipalUnitarySquareRoot, CU, CV, TC] using hroot
  have hcrossC : TC '' (halmosSourceDefect CU CV : Set (RealComplexification E)) =
      (halmosTargetDefect CU CV : Set (RealComplexification E)) := by
    simpa [CU, CV, TC] using complexify_crossedDefect_image_eq U V T hcross
  have hTcomplex : DavisKahan.IsDirectRotation CU CV TC :=
    proposition3_3_principalSquareRoot_converse CU CV TC hrootC hcrossC
  have hposC := principalSquareRoot_positiveDiagonalBlocks CU CV TC hrootC hTcomplex
  have hunitary : T ∈ unitary (E →L[ℝ] E) :=
    DavisKahan.mem_unitary_of_complexify hTcomplex.unitary_mem
  have hintertwines : T * U.starProjection = V.starProjection * T := by
    apply RealComplexification.complexify_injective
    have h := hTcomplex.intertwines
    change TC * CU.starProjection = CV.starProjection * TC at h
    simpa only [CU, CV, TC, DavisKahan.complexify_mul,
      starProjection_complexifySubmodule] using h
  have hsource_pos : (U.starProjection * T * U.starProjection).IsPositive := by
    apply DavisKahan.isPositive_of_complexify
    rw [complexify_sourceCompression U T]
    exact hposC.1
  have hcomplement_pos : (Uᗮ.starProjection * T * Uᗮ.starProjection).IsPositive := by
    apply DavisKahan.isPositive_of_complexify
    rw [complexify_complementCompression U T]
    exact hposC.2
  have hcrossed : Uᗮ.starProjection * T * U.starProjection =
      -star (U.starProjection * T * Uᗮ.starProjection) := by
    apply RealComplexification.complexify_injective
    rw [DavisKahan.complexify_mul, DavisKahan.complexify_mul, complexify_neg,
      DavisKahan.complexify_star, DavisKahan.complexify_mul, DavisKahan.complexify_mul]
    have h := hTcomplex.crossed_blocks
    change CUᗮ.starProjection * TC * CU.starProjection =
      -star (CU.starProjection * TC * CUᗮ.starProjection) at h
    dsimp only [CU, TC] at h
    rw [starProjection_complexifySubmodule_orthogonal,
      starProjection_complexifySubmodule] at h
    exact h
  exact ⟨hunitary, hintertwines, hsource_pos, hcomplement_pos, hcrossed⟩

end Real

end DavisKahan1970
end TauCeti
