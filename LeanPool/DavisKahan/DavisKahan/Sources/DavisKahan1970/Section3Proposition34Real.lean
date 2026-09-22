/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section3Proposition34
import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotationReal

/-! # Section3Proposition34Real -/

open TauCeti.DavisKahan.Angle


/-!
# Davis--Kahan 1970, Proposition 3.4 over real Hilbert spaces

The full nonacute complex theorem with the genuine Definition 3.1 conclusion is
`TauCeti.DavisKahan1970.proposition3_4_full_complex`, in the companion
module `Section3Proposition34.lean`, which also owns the positivity upgrade
`positiveDiagonalBlocks_of_sq` that both scalar fields use.
This file transports that theorem to the real scalar field without identifying
reflected submodules by dependent rewriting.  Instead, the projection onto the
real reflected subspace is complexified directly and identified algebraically
with the projection onto the reflected complex subspace.

The conclusion uses genuine `IsPositive` diagonal compressions, not merely the
weaker real numerical-range predicate.  Thus it is the exact real form of
Definition 3.1 required by the printed Proposition 3.4.
-/

open scoped InnerProductSpace ComplexOrder

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahan
open TauCeti.DavisKahanExt
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification

section Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- Complexification carries the orthogonal projection onto the real reflected
subspace to the projection onto the reflected complex subspace. -/
private theorem complexify_reflectedProjection :
    complexify (reflectedSubspace U V).starProjection =
      (reflectedSubspace (complexifySubmodule U) (complexifySubmodule V)).starProjection := by
  rw [starProjection_reflectedSubspace U V,
    complexify_comp, complexify_comp,
    DavisKahan.complexify_reflectionOperator,
    ← starProjection_complexifySubmodule V,
    starProjection_reflectedSubspace (complexifySubmodule U) (complexifySubmodule V)]

/-- The complementary projection of the reflected subspace transports as well. -/
private theorem complexify_reflectedComplementaryProjection :
    complexify ((reflectedSubspace U V)ᗮ.starProjection) =
      (reflectedSubspace (complexifySubmodule U) (complexifySubmodule V))ᗮ.starProjection := by
  let R := reflectedSubspace U V
  let CR := reflectedSubspace (complexifySubmodule U) (complexifySubmodule V)
  calc
    complexify (Rᗮ.starProjection) = complexify (1 - R.starProjection) := by
      rw [Submodule.starProjection_orthogonal' R]
    _ = 1 - complexify R.starProjection := by
      rw [complexify_sub, DavisKahan.complexify_one]
    _ = 1 - CR.starProjection := by
      dsimp only [R, CR]
      rw [complexify_reflectedProjection U V]
    _ = CRᗮ.starProjection := (Submodule.starProjection_orthogonal' CR).symm

/-- A positive real operator complexifies to a positive complex operator.
Completeness is intentionally retained: the self-adjointness transport instance
used here requires the complete real and complexified Hilbert spaces. -/
private theorem isPositive_complexify {A : E →L[ℝ] E} (hA : A.IsPositive) :
    (complexify A).IsPositive := by
  refine ContinuousLinearMap.isPositive_def'.mpr ⟨?_, fun z => ?_⟩
  · exact (complexify_isSelfAdjoint_iff A).2 hA.isSelfAdjoint
  · rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    exact DavisKahan.re_inner_complexify_nonneg hA.inner_nonneg_left z

omit [CompleteSpace E] in
private theorem complexify_sourceCompression (W : E →L[ℝ] E) :
    complexify (U.starProjection * W * U.starProjection) =
      (complexifySubmodule U).starProjection * complexify W *
        (complexifySubmodule U).starProjection := by
  rw [DavisKahan.complexify_mul, DavisKahan.complexify_mul,
    starProjection_complexifySubmodule]

omit [CompleteSpace E] in
private theorem complexify_complementCompression (W : E →L[ℝ] E) :
    complexify (Uᗮ.starProjection * W * Uᗮ.starProjection) =
      (complexifySubmodule U)ᗮ.starProjection * complexify W *
        (complexifySubmodule U)ᗮ.starProjection := by
  rw [DavisKahan.complexify_mul, DavisKahan.complexify_mul,
    starProjection_complexifySubmodule_orthogonal]

omit [CompleteSpace E] [U.HasOrthogonalProjection] in
/-- The printed real `C₀² ≥ 1/2` inequality transports exactly to the
complexified source subspace. -/
private theorem halfAngle_complexify
    (hcos : ∀ x ∈ U, ‖x‖ ^ 2 / 2 ≤ ‖V.starProjection x‖ ^ 2)
    (z : RealComplexification E) (hz : z ∈ complexifySubmodule U) :
    ‖z‖ ^ 2 / 2 ≤ ‖(complexifySubmodule V).starProjection z‖ ^ 2 := by
  have hzparts : re z ∈ U ∧ im z ∈ U := mem_complexifySubmodule.mp hz
  have hre := hcos (re z) hzparts.1
  have him := hcos (im z) hzparts.2
  rw [starProjection_complexifySubmodule]
  simp only [norm_sq, re_complexify, im_complexify]
  linarith

/-- **Proposition 3.4's explicit direct rotation discharges the Section 3
standing assumption, over `ℝ`.**

The real analogue of `proposition3_4_crossedDefectsEquivalent_complex`:
the printed hypotheses exhibit a direct rotation, and by Proposition 3.2 that is
equivalent to the inherited crossed-defect condition (3.5), so the standing
assumption is a consequence of this result's own hypotheses rather than an extra
one it silently relies on. -/
theorem proposition3_4_crossedDefectsEquivalent_real
    (W : E →L[ℝ] E)
    (hunitary : W ∈ unitary (E →L[ℝ] E))
    (hintertwines : W * U.starProjection = V.starProjection * W)
    (hcrossed : Uᗮ.starProjection * W * U.starProjection =
      -star (U.starProjection * W * Uᗮ.starProjection))
    (hsource_pos : (U.starProjection * W * U.starProjection).IsPositive)
    (hcomplement_pos : (Uᗮ.starProjection * W * Uᗮ.starProjection).IsPositive) :
    CrossedDefectsEquivalent U V :=
  (proposition3_2_exists_iff_crossedDefectsEquivalent U V).mp
    ⟨W,
      { unitary_mem := hunitary
        intertwines := hintertwines
        source_compression_nonnegative := fun x => by
          have h := (ContinuousLinearMap.isPositive_def'.mp hsource_pos).2 x
          rwa [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm (𝕜 := ℝ)] at h
        complement_compression_nonnegative := fun x => by
          have h := (ContinuousLinearMap.isPositive_def'.mp hcomplement_pos).2 x
          rwa [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm (𝕜 := ℝ)] at h
        crossed_blocks := hcrossed }⟩


/-- **Davis--Kahan 1970, Proposition 3.4, full nonacute real source scope.**

If `W` is an arbitrary real direct rotation from `U` to `V` in the printed
Definition 3.1 sense and its source cosine square satisfies `C₀² ≥ 1/2`, then
`W²` is a direct rotation from the reflected target `Q₋ℋ` to `Qℋ`.

The conclusion spells out the exact real Definition 3.1 clauses.  In particular
the two diagonal compressions are `IsPositive`, which is stronger than the
real numerical-range fields of the generic `IsDirectRotation` structure. -/
theorem proposition3_4_full_real
    (W : E →L[ℝ] E)
    (hunitary : W ∈ unitary (E →L[ℝ] E))
    (hintertwines : W * U.starProjection = V.starProjection * W)
    (hcrossed : Uᗮ.starProjection * W * U.starProjection =
      -star (U.starProjection * W * Uᗮ.starProjection))
    (hsource_pos : (U.starProjection * W * U.starProjection).IsPositive)
    (hcomplement_pos : (Uᗮ.starProjection * W * Uᗮ.starProjection).IsPositive)
    (hcos : ∀ x ∈ U, ‖x‖ ^ 2 / 2 ≤ ‖V.starProjection x‖ ^ 2) :
    (W * W) ∈ unitary (E →L[ℝ] E) ∧
      (W * W) * (reflectedSubspace U V).starProjection =
        V.starProjection * (W * W) ∧
      ((reflectedSubspace U V).starProjection * (W * W) *
        (reflectedSubspace U V).starProjection).IsPositive ∧
      ((reflectedSubspace U V)ᗮ.starProjection * (W * W) *
        (reflectedSubspace U V)ᗮ.starProjection).IsPositive ∧
      (reflectedSubspace U V)ᗮ.starProjection * (W * W) *
          (reflectedSubspace U V).starProjection =
        -star ((reflectedSubspace U V).starProjection * (W * W) *
          (reflectedSubspace U V)ᗮ.starProjection) := by
  let CU := complexifySubmodule U
  let CV := complexifySubmodule V
  let WC := complexify W
  let R := reflectedSubspace U V
  let CR := reflectedSubspace CU CV
  have hproj : complexify R.starProjection = CR.starProjection := by
    dsimp only [R, CR, CU, CV]
    exact complexify_reflectedProjection U V
  have hprojc : complexify Rᗮ.starProjection = CRᗮ.starProjection := by
    dsimp only [R, CR, CU, CV]
    exact complexify_reflectedComplementaryProjection U V
  have hunitaryC :
      WC ∈ unitary (RealComplexification E →L[ℂ] RealComplexification E) :=
    DavisKahan.complexify_mem_unitary hunitary
  have hintertwinesC : WC * CU.starProjection = CV.starProjection * WC := by
    dsimp only [WC, CU, CV]
    have h := congrArg (fun A : E →L[ℝ] E => complexify A) hintertwines
    simpa only [DavisKahan.complexify_mul, starProjection_complexifySubmodule] using h
  have hcrossedC : CUᗮ.starProjection * WC * CU.starProjection =
      -star (CU.starProjection * WC * CUᗮ.starProjection) := by
    dsimp only [WC, CU]
    have h := congrArg (fun A : E →L[ℝ] E => complexify A) hcrossed
    simpa only [DavisKahan.complexify_mul, DavisKahan.complexify_star,
      complexify_neg, starProjection_complexifySubmodule,
      starProjection_complexifySubmodule_orthogonal] using h
  have hsource_posC : (CU.starProjection * WC * CU.starProjection).IsPositive := by
    dsimp only [WC, CU]
    rw [← complexify_sourceCompression U W]
    exact isPositive_complexify hsource_pos
  have hcomplement_posC :
      (CUᗮ.starProjection * WC * CUᗮ.starProjection).IsPositive := by
    dsimp only [WC, CU]
    rw [← complexify_complementCompression U W]
    exact isPositive_complexify hcomplement_pos
  have hsource_nonnegC :
      (0 : RealComplexification E →L[ℂ] RealComplexification E) ≤
        CU.starProjection * WC * CU.starProjection :=
    (ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mpr hsource_posC
  have hcomplement_nonnegC :
      (0 : RealComplexification E →L[ℂ] RealComplexification E) ≤
        CUᗮ.starProjection * WC * CUᗮ.starProjection :=
    (ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mpr hcomplement_posC
  have hcosC : ∀ z ∈ CU, ‖z‖ ^ 2 / 2 ≤ ‖CV.starProjection z‖ ^ 2 := by
    intro z hz
    exact halfAngle_complexify U V hcos z hz
  have hC : IsDirectRotation CR CV (WC * WC) := by
    dsimp only [CR]
    exact proposition3_4_isDirectRotation_complex
      CU CV WC hunitaryC hintertwinesC hcrossedC
        hsource_nonnegC hcomplement_nonnegC hcosC
  have hWsq : WC * WC = spectraReflectionProduct CU CV :=
    sq_eq_spectraReflectionProduct CU CV WC hunitaryC hintertwinesC
      hsource_posC.isSelfAdjoint hcomplement_posC.isSelfAdjoint hcrossedC
  have hrefl : CR.reflectionOperator =
      CU.reflectionOperator * CV.reflectionOperator * CU.reflectionOperator := by
    dsimp only [CR]
    exact reflectionOperator_reflectedSubspace CV CU
  have hRU : CU.reflectionOperator * CU.reflectionOperator = 1 :=
    reflectionOperator_mul_self_complex CU
  have hsqC : (WC * WC) * (WC * WC) = spectraReflectionProduct CR CV := by
    change (WC * WC) * (WC * WC) = CV.reflectionOperator * CR.reflectionOperator
    rw [hrefl, hWsq]
    noncomm_ring
  have hpositiveC := positiveDiagonalBlocks_of_sq CR CV (WC * WC) hC hsqC
  have hC_intertwines :
      (WC * WC) * CR.starProjection = CV.starProjection * (WC * WC) :=
    hC.intertwines
  have hC_crossed :
      CRᗮ.starProjection * (WC * WC) * CR.starProjection =
        -star (CR.starProjection * (WC * WC) * CRᗮ.starProjection) :=
    hC.crossed_blocks
  have hintertwinesR :
      (W * W) * (reflectedSubspace U V).starProjection =
        V.starProjection * (W * W) := by
    change (W * W) * R.starProjection = V.starProjection * (W * W)
    apply RealComplexification.complexify_injective
    simp only [DavisKahan.complexify_mul]
    rw [hproj, ← starProjection_complexifySubmodule V]
    exact hC_intertwines
  have hsource_posR :
      ((reflectedSubspace U V).starProjection * (W * W) *
        (reflectedSubspace U V).starProjection).IsPositive := by
    change (R.starProjection * (W * W) * R.starProjection).IsPositive
    apply DavisKahan.isPositive_of_complexify
    simp only [DavisKahan.complexify_mul]
    rw [hproj]
    exact hpositiveC.1
  have hcomplement_posR :
      ((reflectedSubspace U V)ᗮ.starProjection * (W * W) *
        (reflectedSubspace U V)ᗮ.starProjection).IsPositive := by
    change (Rᗮ.starProjection * (W * W) * Rᗮ.starProjection).IsPositive
    apply DavisKahan.isPositive_of_complexify
    simp only [DavisKahan.complexify_mul]
    rw [hprojc]
    exact hpositiveC.2
  have hcrossedR :
      (reflectedSubspace U V)ᗮ.starProjection * (W * W) *
          (reflectedSubspace U V).starProjection =
        -star ((reflectedSubspace U V).starProjection * (W * W) *
          (reflectedSubspace U V)ᗮ.starProjection) := by
    change Rᗮ.starProjection * (W * W) * R.starProjection =
      -star (R.starProjection * (W * W) * Rᗮ.starProjection)
    apply RealComplexification.complexify_injective
    simp only [DavisKahan.complexify_mul, complexify_neg, DavisKahan.complexify_star]
    rw [hproj, hprojc]
    exact hC_crossed
  exact ⟨mul_mem hunitary hunitary, hintertwinesR,
    hsource_posR, hcomplement_posR, hcrossedR⟩

end Real

end DavisKahan1970
end TauCeti
