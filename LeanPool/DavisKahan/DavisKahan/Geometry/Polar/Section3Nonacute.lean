/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


public import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.Section3Elementary
public import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.PolarIntertwining
public import LeanPool.DavisKahan.ForTauCeti.Analysis.Normed.Operator.LinearIsometry
public import LeanPool.DavisKahan.ForTauCeti.Analysis.RCLike.ScalarTransportFunctionalCalculus

/-! # Section3Nonacute -/

@[expose] public section

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
  ContinuousLinearMap.instStarOrderedRingRCLike

open TauCeti.DavisKahan.Sylvester

/-!
# Nonacute direct rotations from crossed-defect data

For two projections, the canonical polar factor is the direct rotation on the
orthogonal complement of the two crossed defect spaces and vanishes on those
defects.  A unitary identification of the crossed defects supplies the missing
quarter-turn.  Adding the two orthogonal blocks gives the nonacute direct
rotation of Davis--Kahan Proposition 3.2.

This file keeps the construction operator-valued.  Equality of Hilbert
cardinals enters only through the existence of the linear isometric equivalence
between the crossed defects.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan



noncomputable section

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]


variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

omit [CompleteSpace H] in
private theorem projection_mul_projection_eq_zero_of_le_orthogonal
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] (hKL : K ≤ Lᗮ) :
    L.starProjection * K.starProjection = 0 := by
  ext x
  have hxK : K.starProjection x ∈ K := K.starProjection_apply_mem x
  have hxOrth : K.starProjection x ∈ Lᗮ := hKL hxK
  rw [mul_apply_eq_comp, zero_apply,
    Submodule.starProjection_apply_eq_zero_iff]
  exact hxOrth

omit [CompleteSpace H] in
private theorem projection_mul_projection_eq_zero_of_ge_orthogonal
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] (hKL : K ≤ Lᗮ) :
    K.starProjection * L.starProjection = 0 := by
  have hLK : L ≤ Kᗮ := by
    intro x hx y hy
    exact inner_eq_zero_symm.mp (hKL hy x hx)
  exact projection_mul_projection_eq_zero_of_le_orthogonal L K hLK

/-- Orthogonal sum of the two crossed defect spaces. -/
noncomputable def crossedDefectSum : Submodule 𝕜 H :=
  halmosSourceDefect U V ⊔ halmosTargetDefect U V

/-- The sum of the two crossed defect subspaces is orthogonally complemented, so the nonacute
decomposition has an orthogonal projection onto it. -/
noncomputable instance crossedDefectSum_hasOrthogonalProjection :
    (crossedDefectSum U V).HasOrthogonalProjection :=
  hasOrthogonalProjection_sup_of_le_orthogonal
    (halmosSourceDefect U V) (halmosTargetDefect U V)
    (halmosSourceDefect_le_targetDefect_orthogonal U V)

/-- Projection onto the crossed-defect block. -/
noncomputable def crossedDefectProjection : H →L[𝕜] H :=
  Submodule.starProjection (crossedDefectSum U V)

/-- Projection onto the regular block complementary to the crossed defects. -/
noncomputable def regularProjection : H →L[𝕜] H :=
  Submodule.starProjection ((crossedDefectSum U V)ᗮ)

/-- Inclusion--transport--projection operator from the source defect to the
target defect. -/
noncomputable def sourceToTargetDefect
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    H →L[𝕜] H :=
  (halmosTargetDefect U V).subtypeL ∘L
    J.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      (halmosSourceDefect U V).orthogonalProjectionOnto

/-- Reverse inclusion--transport--projection operator. -/
noncomputable def targetToSourceDefect
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    H →L[𝕜] H :=
  (halmosSourceDefect U V).subtypeL ∘L
    J.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      (halmosTargetDefect U V).orthogonalProjectionOnto

/-- Quarter-turn on the crossed defect block, zero on its orthogonal
complement.  It maps source defect to target defect and target defect to the
negative source defect. -/
noncomputable def crossedDefectQuarterTurn
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    H →L[𝕜] H :=
  sourceToTargetDefect U V J - targetToSourceDefect U V J

omit [CompleteSpace H] in
@[simp]
private theorem ofEq_orthogonalProjectionOnto
    {K L : Submodule 𝕜 H} [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] (h : K = L) (x : H) :
    LinearIsometryEquiv.ofEq K L h (K.orthogonalProjectionOnto x) =
      L.orthogonalProjectionOnto x := by
  subst L
  rfl

/-- The same crossed-defect identification for the reversed ordered pair.
The two defect spaces exchange roles, so reversal uses the inverse isometry. -/
noncomputable def swapCrossedDefectEquiv
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    halmosSourceDefect V U ≃ₗᵢ[𝕜] halmosTargetDefect V U :=
  ((LinearIsometryEquiv.ofEq _ _ (by
      simp only [halmosSourceDefect, halmosTargetDefect, inf_comm])).trans J.symm).trans
    (LinearIsometryEquiv.ofEq _ _ (by
      simp only [halmosSourceDefect, halmosTargetDefect, inf_comm]))

/-- The crossed-defect identification for the complementary pair.  Source and target defects
exchange roles, and the extra minus sign makes the completed quarter-turn agree with the original
one on both defect summands. -/
noncomputable def orthogonalCrossedDefectEquiv
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    halmosSourceDefect U.orthogonal V.orthogonal ≃ₗᵢ[𝕜]
      halmosTargetDefect U.orthogonal V.orthogonal :=
  (LinearIsometryEquiv.ofEq _ _ (by
      simp only [halmosSourceDefect, halmosTargetDefect,
        Submodule.orthogonal_orthogonal])).trans
    (J.symm.trans (LinearIsometryEquiv.neg 𝕜)) |>.trans
      (LinearIsometryEquiv.ofEq _ _ (by
        simp only [halmosSourceDefect, halmosTargetDefect,
          Submodule.orthogonal_orthogonal]))

/-- The crossed defect map on a source vector. -/
@[simp]
theorem sourceToTargetDefect_apply_source
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V)
    (x : halmosSourceDefect U V) :
    sourceToTargetDefect U V J (x : H) = (J x : H) := by
  simp [sourceToTargetDefect,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

/-- The crossed defect map on a target vector. -/
@[simp]
theorem targetToSourceDefect_apply_target
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V)
    (y : halmosTargetDefect U V) :
    targetToSourceDefect U V J (y : H) = (J.symm y : H) := by
  simp [targetToSourceDefect,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

/-- The source-to-target defect annihilates target vectors -- the *crossed* half of the name, and
what makes the two defects act on complementary summands. -/
@[simp]
theorem sourceToTargetDefect_apply_target
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V)
    (y : halmosTargetDefect U V) :
    sourceToTargetDefect U V J (y : H) = 0 := by
  have hy : (y : H) ∈ (halmosSourceDefect U V)ᗮ :=
    Submodule.orthogonal_le (halmosSourceDefect_le_targetDefect_orthogonal U V)
      (Submodule.le_orthogonal_orthogonal _ y.property)
  simp [sourceToTargetDefect,
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hy]

/-- The target-to-source defect annihilates source vectors. -/
@[simp]
theorem targetToSourceDefect_apply_source
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V)
    (x : halmosSourceDefect U V) :
    targetToSourceDefect U V J (x : H) = 0 := by
  have hx : (x : H) ∈ (halmosTargetDefect U V)ᗮ :=
    halmosSourceDefect_le_targetDefect_orthogonal U V x.property
  simp [targetToSourceDefect,
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hx]

/-- The quarter turn sends a source vector to its target-side defect. -/
@[simp]
theorem crossedDefectQuarterTurn_apply_source
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V)
    (x : halmosSourceDefect U V) :
    crossedDefectQuarterTurn U V J (x : H) = (J x : H) := by
  simp [crossedDefectQuarterTurn]

/-- The quarter turn sends a target vector to the negative of its source-side defect; the sign is
what makes it a quarter turn rather than a reflection. -/
@[simp]
theorem crossedDefectQuarterTurn_apply_target
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V)
    (y : halmosTargetDefect U V) :
    crossedDefectQuarterTurn U V J (y : H) = -(J.symm y : H) := by
  simp [crossedDefectQuarterTurn]

/-- The quarter-turn vanishes on the regular block. -/
theorem crossedDefectQuarterTurn_apply_regular
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V)
    {x : H} (hx : x ∈ (crossedDefectSum U V)ᗮ) :
    crossedDefectQuarterTurn U V J x = 0 := by
  have hxS : x ∈ (halmosSourceDefect U V)ᗮ :=
    Submodule.orthogonal_le le_sup_left hx
  have hxT : x ∈ (halmosTargetDefect U V)ᗮ :=
    Submodule.orthogonal_le le_sup_right hx
  simp [crossedDefectQuarterTurn, sourceToTargetDefect,
    targetToSourceDefect,
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hxS,
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hxT]

/-- The two directional defect transports are adjoints. -/
theorem star_sourceToTargetDefect
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    star (sourceToTargetDefect U V J) = targetToSourceDefect U V J := by
  refine ContinuousLinearMap.ext fun x => ?_
  refine ext_inner_left 𝕜 fun y => ?_
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  simp only [sourceToTargetDefect, targetToSourceDefect,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [← Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
    ← Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    LinearIsometryEquiv.inner_map_eq_flip]

/-- The crossed-defect quarter-turn is skew-adjoint. -/
theorem star_crossedDefectQuarterTurn
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    star (crossedDefectQuarterTurn U V J) =
      -crossedDefectQuarterTurn U V J := by
  rw [crossedDefectQuarterTurn, star_sub, star_sourceToTargetDefect U V J]
  have h2 : star (targetToSourceDefect U V J) = sourceToTargetDefect U V J := by
    rw [← star_sourceToTargetDefect U V J, star_star]
  rw [h2]
  abel

/-- Reversing the ordered pair and the chosen crossed-defect isometry negates
the defect quarter turn. -/
theorem crossedDefectQuarterTurn_swap
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    crossedDefectQuarterTurn V U (swapCrossedDefectEquiv U V J) =
      -crossedDefectQuarterTurn U V J := by
  apply ContinuousLinearMap.ext
  intro x
  simp [crossedDefectQuarterTurn, sourceToTargetDefect, targetToSourceDefect,
    swapCrossedDefectEquiv, halmosSourceDefect, halmosTargetDefect]

/-- Initial and final projection of the defect quarter-turn. -/
theorem star_crossedDefectQuarterTurn_mul_self
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    star (crossedDefectQuarterTurn U V J) *
        crossedDefectQuarterTurn U V J =
      crossedDefectProjection U V := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨d, hd, hdperp⟩ :=
    Submodule.HasOrthogonalProjection.exists_orthogonal
      (K := crossedDefectSum U V) x
  obtain ⟨r, hr, hxr⟩ : ∃ r ∈ (crossedDefectSum U V)ᗮ, x = d + r :=
    ⟨x - d, hdperp, by abel⟩
  obtain ⟨s, hs, t, ht, rfl⟩ :
      ∃ s ∈ halmosSourceDefect U V, ∃ t ∈ halmosTargetDefect U V, s + t = d :=
    Submodule.mem_sup.mp hd
  have hQr : crossedDefectQuarterTurn U V J r = 0 :=
    crossedDefectQuarterTurn_apply_regular U V J hr
  have hQx : crossedDefectQuarterTurn U V J x =
      (J ⟨s, hs⟩ : H) - (J.symm ⟨t, ht⟩ : H) := by
    simp only [hxr, map_add, hQr, add_zero,
      show crossedDefectQuarterTurn U V J s = (J ⟨s, hs⟩ : H) from
        crossedDefectQuarterTurn_apply_source U V J ⟨s, hs⟩,
      show crossedDefectQuarterTurn U V J t = -(J.symm ⟨t, ht⟩ : H) from
        crossedDefectQuarterTurn_apply_target U V J ⟨t, ht⟩,
      ← sub_eq_add_neg]
  have hQQx : crossedDefectQuarterTurn U V J
      (crossedDefectQuarterTurn U V J x) = -(s + t) := by
    rw [hQx, map_sub,
      crossedDefectQuarterTurn_apply_target U V J (J ⟨s, hs⟩),
      crossedDefectQuarterTurn_apply_source U V J (J.symm ⟨t, ht⟩),
      LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.apply_symm_apply]
    change -(s : H) - (t : H) = -(s + t)
    abel
  have hproj : crossedDefectProjection U V x = s + t := by
    rw [crossedDefectProjection, hxr, map_add,
      (Submodule.starProjection_apply_eq_zero_iff _).mpr hr, add_zero]
    exact Submodule.starProjection_eq_self_iff.mpr
      (Submodule.mem_sup.mpr ⟨s, hs, t, ht, rfl⟩)
  rw [mul_apply_eq_comp, star_crossedDefectQuarterTurn,
    neg_apply, hQQx, neg_neg, hproj]

omit [CompleteSpace H] in
/-- The canonical intertwiner vanishes on the source defect. -/
theorem canonicalIntertwiner_apply_sourceDefect_eq_zero
    (x : halmosSourceDefect U V) :
    spectraCanonicalIntertwiner U V (x : H) = 0 := by
  obtain ⟨hPx, hQperpx⟩ := mem_halmosSourceDefect.mp x.property
  have hP : U.starProjection (x : H) = x :=
    Submodule.starProjection_eq_self_iff.mpr hPx
  have hQ : V.starProjection (x : H) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr hQperpx
  have hPc : (Uᗮ).starProjection (x : H) = 0 := by
    simp [hP]
  simp [spectraCanonicalIntertwiner, hP, hQ, hPc]

omit [CompleteSpace H] in
/-- The canonical intertwiner vanishes on the target defect. -/
theorem canonicalIntertwiner_apply_targetDefect_eq_zero
    (x : halmosTargetDefect U V) :
    spectraCanonicalIntertwiner U V (x : H) = 0 := by
  obtain ⟨hPperpx, hQx⟩ := mem_halmosTargetDefect.mp x.property
  have hP : U.starProjection (x : H) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr hPperpx
  have hPc : (Uᗮ).starProjection (x : H) = x := by
    simp [hP]
  have hQc : (Vᗮ).starProjection (x : H) = 0 := by
    have hQ : V.starProjection (x : H) = x :=
      Submodule.starProjection_eq_self_iff.mpr hQx
    simp [hQ]
  simp [spectraCanonicalIntertwiner, hP, hPc, hQc]

omit [CompleteSpace H] in
/-- The kernel of the canonical intertwiner is exactly the crossed-defect sum. -/
theorem ker_canonicalIntertwiner_eq_crossedDefectSum :
    LinearMap.ker (spectraCanonicalIntertwiner U V).toLinearMap =
      crossedDefectSum U V := by
  ext x
  constructor
  · intro hx
    have hzero := congrArg (fun y => ‖y‖ * ‖y‖) hx
    have horth :
        ⟪V.starProjection (U.starProjection x),
          (Vᗮ).starProjection ((Uᗮ).starProjection x)⟫_𝕜 = 0 := by
      exact Submodule.inner_right_of_mem_orthogonal
        (V.starProjection_apply_mem _) (Vᗮ.starProjection_apply_mem _)
    have hsumzero :
        V.starProjection (U.starProjection x) = 0 ∧
        (Vᗮ).starProjection ((Uᗮ).starProjection x) = 0 := by
      have hsquares :=
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
      rw [spectraCanonicalIntertwiner, ContinuousLinearMap.coe_coe,
        add_apply,
        mul_apply_eq_comp, mul_apply_eq_comp] at hzero
      rw [hsquares] at hzero
      exact (add_eq_zero_iff_of_nonneg (mul_self_nonneg _) (mul_self_nonneg _)).mp
          (by simpa using hzero)
        |>.imp (fun h => by simpa [mul_self_eq_zero] using h)
               (fun h => by simpa [mul_self_eq_zero] using h)
    let s : H := U.starProjection x
    let t : H := (Uᗮ).starProjection x
    have hsU : s ∈ U := U.starProjection_apply_mem x
    have hsVperp : s ∈ Vᗮ :=
      (Submodule.starProjection_apply_eq_zero_iff _).mp hsumzero.1
    have htUperp : t ∈ Uᗮ := Uᗮ.starProjection_apply_mem x
    have htV : t ∈ V := by
      have hmem : t ∈ (Vᗮ)ᗮ :=
        (Submodule.starProjection_apply_eq_zero_iff _).mp hsumzero.2
      rwa [V.orthogonal_orthogonal] at hmem
    have hs : s ∈ halmosSourceDefect U V :=
      mem_halmosSourceDefect.mpr ⟨hsU, hsVperp⟩
    have ht : t ∈ halmosTargetDefect U V :=
      mem_halmosTargetDefect.mpr ⟨htUperp, htV⟩
    have hsplit : x = s + t := by
      exact (U.starProjection_add_starProjection_orthogonal x).symm
    rw [hsplit]
    exact Submodule.mem_sup.mpr ⟨s, hs, t, ht, rfl⟩
  · intro hx
    rcases Submodule.mem_sup.mp hx with ⟨s, hs, t, ht, rfl⟩
    refine LinearMap.mem_ker.mpr ?_
    simp only [ContinuousLinearMap.coe_coe, map_add,
      canonicalIntertwiner_apply_sourceDefect_eq_zero U V ⟨s, hs⟩,
      canonicalIntertwiner_apply_targetDefect_eq_zero U V ⟨t, ht⟩, add_zero]

/-- The polar initial space is the regular block. -/
theorem polarInitial_canonicalIntertwiner_eq_regular :
    (spectraCanonicalIntertwiner U V).polarInitial =
      (crossedDefectSum U V)ᗮ := by
  have hker : LinearMap.ker ((spectraCanonicalIntertwiner U V).modulus).toLinearMap =
      crossedDefectSum U V := by
    rw [← ker_canonicalIntertwiner_eq_crossedDefectSum U V]
    ext y
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    constructor
    · intro hy
      have hn := ContinuousLinearMap.norm_modulus_apply
        (spectraCanonicalIntertwiner U V) y
      rw [hy, norm_zero, eq_comm, norm_eq_zero] at hn
      exact hn
    · intro hy
      have hn := ContinuousLinearMap.norm_modulus_apply
        (spectraCanonicalIntertwiner U V) y
      rw [hy, norm_zero, norm_eq_zero] at hn
      exact hn
  simp only [ContinuousLinearMap.polarInitial,
    ← Submodule.orthogonal_orthogonal_eq_closure,
    ContinuousLinearMap.orthogonal_range,
    ← ContinuousLinearMap.star_eq_adjoint,
    (ContinuousLinearMap.modulus_isSelfAdjoint
      (spectraCanonicalIntertwiner U V)).star_eq,
    hker]

/-- The canonical polar factor vanishes on the crossed defect block. -/
theorem canonicalPolarFactor_apply_crossedDefect_eq_zero
    {x : H} (hx : x ∈ crossedDefectSum U V) :
    spectraCanonicalPolarFactor U V x = 0 := by
  have hxperp : x ∈ (spectraCanonicalIntertwiner U V).polarInitialᗮ := by
    rw [polarInitial_canonicalIntertwiner_eq_regular U V]
    exact Submodule.le_orthogonal_orthogonal (crossedDefectSum U V) hx
  rw [spectraCanonicalPolarFactor]
  exact ContinuousLinearMap.polarPartial_eq_zero_of_mem_orthogonal _ hxperp

/-- The final range of the canonical intertwiner is the regular block. -/
theorem polarFinal_canonicalIntertwiner_eq_regular :
    (spectraCanonicalIntertwiner U V).polarFinal =
      (crossedDefectSum U V)ᗮ := by
  simp only [ContinuousLinearMap.polarFinal,
    ← Submodule.orthogonal_orthogonal_eq_closure,
    ContinuousLinearMap.orthogonal_range,
    ← ContinuousLinearMap.star_eq_adjoint,
    star_spectraCanonicalIntertwiner,
    ker_canonicalIntertwiner_eq_crossedDefectSum V U]
  congr 1
  simp only [crossedDefectSum, halmosSourceDefect, halmosTargetDefect,
    inf_comm, sup_comm]

/-- The polar factor has both initial and final projection equal to the regular
projection. -/
theorem canonicalPolarFactor_initial_final_projection :
    star (spectraCanonicalPolarFactor U V) *
        spectraCanonicalPolarFactor U V = regularProjection U V ∧
    spectraCanonicalPolarFactor U V *
        star (spectraCanonicalPolarFactor U V) = regularProjection U V := by
  constructor
  · have h := ContinuousLinearMap.adjoint_comp_polarPartial
      (spectraCanonicalIntertwiner U V)
    simp only [polarInitial_canonicalIntertwiner_eq_regular U V] at h
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact h
  · have h := ContinuousLinearMap.polarPartial_comp_adjoint
      (spectraCanonicalIntertwiner U V)
    simp only [polarFinal_canonicalIntertwiner_eq_regular U V] at h
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact h

/-- The polar factor maps the regular block into itself. -/
theorem canonicalPolarFactor_mem_regular (x : H) :
    spectraCanonicalPolarFactor U V x ∈ (crossedDefectSum U V)ᗮ := by
  rw [← polarFinal_canonicalIntertwiner_eq_regular U V,
    ContinuousLinearMap.polarFinal_eq_range_polarPartial]
  exact ⟨x, rfl⟩

/-- **The crossed quarter-turn lands in the crossed defect sum.**

Its two summands are the images of the source and target defect projections.
Derived twice in the theorem below, once per orthogonality it establishes. -/
private theorem crossedDefectQuarterTurn_mem_crossedDefectSum
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) (x : H) :
    crossedDefectQuarterTurn U V J x ∈ crossedDefectSum U V := by
  let s := (halmosSourceDefect U V).orthogonalProjectionOnto x
  let t := (halmosTargetDefect U V).orthogonalProjectionOnto x
  refine Submodule.mem_sup.mpr
    ⟨-(J.symm t : H), Submodule.neg_mem _ (J.symm t).property,
      (J s : H), (J s).property, ?_⟩
  simp [crossedDefectQuarterTurn, sourceToTargetDefect,
    targetToSourceDefect, s, t]
  abel

/-- The canonical polar factor and defect quarter-turn have orthogonal initial
and final blocks. -/
theorem canonicalPolarFactor_orthogonal_defectQuarterTurn
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    star (spectraCanonicalPolarFactor U V) * crossedDefectQuarterTurn U V J = 0 ∧
    star (crossedDefectQuarterTurn U V J) * spectraCanonicalPolarFactor U V = 0 ∧
    spectraCanonicalPolarFactor U V * star (crossedDefectQuarterTurn U V J) = 0 ∧
    crossedDefectQuarterTurn U V J * star (spectraCanonicalPolarFactor U V) = 0 := by
  have hfirst : star (spectraCanonicalPolarFactor U V) *
      crossedDefectQuarterTurn U V J = 0 := by
    ext x
    rw [mul_apply_eq_comp, zero_apply,
      ContinuousLinearMap.star_eq_adjoint]
    refine ext_inner_right 𝕜 fun y => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left]
    have hrange := crossedDefectQuarterTurn_mem_crossedDefectSum U V J x
    have hyreg := canonicalPolarFactor_mem_regular U V y
    exact Submodule.inner_right_of_mem_orthogonal hrange hyreg
  have hsecond : star (crossedDefectQuarterTurn U V J) *
      spectraCanonicalPolarFactor U V = 0 := by
    have h := congrArg star hfirst
    simpa [star_mul] using h
  have hthird : spectraCanonicalPolarFactor U V *
      star (crossedDefectQuarterTurn U V J) = 0 := by
    rw [star_crossedDefectQuarterTurn]
    ext x
    have hrange := crossedDefectQuarterTurn_mem_crossedDefectSum U V J x
    simp [mul_apply_eq_comp,
      canonicalPolarFactor_apply_crossedDefect_eq_zero U V hrange]
  have hfourth : crossedDefectQuarterTurn U V J *
      star (spectraCanonicalPolarFactor U V) = 0 := by
    have h := congrArg star hthird
    simpa [star_mul] using h
  exact ⟨hfirst, hsecond, hthird, hfourth⟩

/-- The quarter-turn has the same initial and final defect projection. -/
theorem crossedDefectQuarterTurn_mul_star_self
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    crossedDefectQuarterTurn U V J *
        star (crossedDefectQuarterTurn U V J) = crossedDefectProjection U V := by
  have hinit := star_crossedDefectQuarterTurn_mul_self U V J
  rw [star_crossedDefectQuarterTurn] at hinit ⊢
  rw [mul_neg, ← neg_mul]
  exact hinit

/-- The canonical polar factor intertwines the two projections without an
acuteness assumption. -/
theorem canonicalPolarFactor_intertwines_general :
    spectraCanonicalPolarFactor U V * U.starProjection =
      V.starProjection * spectraCanonicalPolarFactor U V := by
  simpa [ContinuousLinearMap.mul_def] using
    canonicalPolarFactor_intertwines_from_polar U V

/-- The modulus of the canonical intertwiner kills the crossed-defect sum: the
crossed defects are exactly the kernel of `C`, hence of `|C|`. -/
theorem canonicalAbsoluteValue_apply_crossedDefect_eq_zero
    {x : H} (hx : x ∈ crossedDefectSum U V) :
    ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) x = 0 := by
  have hCx : spectraCanonicalIntertwiner U V x = 0 := by
    have hmem : x ∈ LinearMap.ker (spectraCanonicalIntertwiner U V).toLinearMap := by
      rw [ker_canonicalIntertwiner_eq_crossedDefectSum]; exact hx
    exact hmem
  have hnorm := ContinuousLinearMap.norm_modulus_apply (spectraCanonicalIntertwiner U V) x
  rw [hCx, norm_zero] at hnorm
  exact norm_eq_zero.mp hnorm

/-- **Real-part identity for the direct rotation.**  The polar factor `W` of the
canonical intertwiner satisfies `W + W⋆ = 2 |C|`.

Because `C` is normal (`spectraCanonicalIntertwiner_normal`), `W` commutes with
`|C|`, so `C + C⋆ = |C| (W + W⋆)`; combined with `C + C⋆ = 2|C|²`
(`spectraCanonicalIntertwiner_add_star`) this gives `|C| (W + W⋆ - 2|C|) = 0`.
The difference `D := W + W⋆ - 2|C|` is self-adjoint, maps everything into
`ker |C|`, and vanishes on `ker |C|`, so `D² = 0` and hence `D = 0`. -/
theorem polarFactor_add_star_eq_two_absoluteValue :
    spectraCanonicalPolarFactor U V + star (spectraCanonicalPolarFactor U V) =
      ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) +
        ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) := by
  set C := spectraCanonicalIntertwiner U V with hCdef
  set A := ContinuousLinearMap.modulus C with hAdef
  set W := spectraCanonicalPolarFactor U V with hWdef
  have hAsa : IsSelfAdjoint A := ContinuousLinearMap.modulus_isSelfAdjoint C
  have hWA : W * A = C := by
    rw [ContinuousLinearMap.mul_def]; exact spectraCanonicalPolarFactor_decomposition U V
  have hAA : A * A = star C * C := ContinuousLinearMap.modulus_mul_self_eq_star_mul_self C
  have hAsW : A * star W = star C := by
    have h : star (W * A) = star C := by rw [hWA]
    rwa [star_mul, hAsa.star_eq] at h
  obtain ⟨hWstarW, hWWstar⟩ := canonicalPolarFactor_initial_final_projection U V
  -- `A` vanishes on the crossed block, so `A · P_reg = A`.
  have hRegCross1 : regularProjection U V + crossedDefectProjection U V = 1 := by
    simp only [regularProjection, crossedDefectProjection]
    rw [Submodule.starProjection_orthogonal']
    abel
  have hAcrossProj : A * crossedDefectProjection U V = 0 := by
    ext y
    simp only [mul_apply_eq_comp, zero_apply]
    exact canonicalAbsoluteValue_apply_crossedDefect_eq_zero U V
      ((crossedDefectSum U V).starProjection_apply_mem y)
  have hAreg : A * regularProjection U V = A := by
    have h : A * (regularProjection U V + crossedDefectProjection U V) = A * 1 := by
      rw [hRegCross1]
    rwa [mul_add, hAcrossProj, add_zero, mul_one] at h
  have hsCW : star C * W = A := by
    rw [← hAsW, mul_assoc, hWstarW, hAreg]
  -- `W` commutes with the Gram operator, hence with `|C|`.
  have hcomm : Commute (star C * C) W := by
    change star C * C * W = W * (star C * C)
    calc star C * C * W
        = C * star C * W := by rw [spectraCanonicalIntertwiner_normal U V]
      _ = C * (star C * W) := by rw [mul_assoc]
      _ = C * A := by rw [hsCW]
      _ = W * A * A := by rw [← hWA]
      _ = W * (A * A) := by rw [mul_assoc]
      _ = W * (star C * C) := by rw [hAA]
  have hcommAW : Commute A W :=
    ContinuousLinearMap.commute_modulus_of_commute_star_mul_self C W hcomm
  have hAW : A * W = C := hcommAW.eq.trans hWA
  have hsum1 : C + star C = A * (W + star W) := by rw [mul_add, hAW, hAsW]
  have hsum2 : star C * C + star C * C = A * (A + A) := by rw [mul_add, hAA]
  have hAD : A * ((W + star W) - (A + A)) = 0 := by
    rw [mul_sub, ← hsum1, ← hsum2, spectraCanonicalIntertwiner_add_star U V, sub_self]
  -- `E := W + W⋆ - 2A` is self-adjoint, `A E = 0`, and vanishes on the crossed block.
  set E := (W + star W) - (A + A) with hEdef
  have hEsa : IsSelfAdjoint E := by
    change star E = E
    rw [hEdef, star_sub, star_add, star_add, star_star, hAsa.star_eq]
    abel
  have hEcross : ∀ z : H, z ∈ crossedDefectSum U V → E z = 0 := by
    intro z hz
    have hWz : W z = 0 := canonicalPolarFactor_apply_crossedDefect_eq_zero U V hz
    have hAz : A z = 0 := canonicalAbsoluteValue_apply_crossedDefect_eq_zero U V hz
    have hreg : regularProjection U V z = 0 := by
      simp only [regularProjection]
      exact (Submodule.starProjection_apply_eq_zero_iff _).mpr
        (Submodule.le_orthogonal_orthogonal _ hz)
    have hWsWz : W (star W z) = 0 := by
      rw [← mul_apply_eq_comp, hWWstar]; exact hreg
    have hsWz : star W z = 0 := by
      have hip : ⟪star W z, star W z⟫_𝕜 = ⟪z, W (star W z)⟫_𝕜 := by
        rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
      rw [hWsWz, inner_zero_right] at hip
      exact inner_self_eq_zero.mp hip
    rw [hEdef]
    simp only [sub_apply, add_apply,
      hWz, hsWz, hAz, add_zero, sub_zero]
  have hEE : E * E = 0 := by
    ext y
    have hAEy : A (E y) = 0 := by
      have h := congrArg (fun T : H →L[𝕜] H => T y) hAD
      simpa only [mul_apply_eq_comp, zero_apply] using h
    have hCEy : C (E y) = 0 := by
      have hn := ContinuousLinearMap.norm_modulus_apply C (E y)
      rw [hAEy, norm_zero] at hn
      exact norm_eq_zero.mp hn.symm
    have hEycross : E y ∈ crossedDefectSum U V := by
      rw [← ker_canonicalIntertwiner_eq_crossedDefectSum]
      exact LinearMap.mem_ker.mpr hCEy
    simp only [mul_apply_eq_comp, zero_apply,
      hEcross (E y) hEycross]
  have hEzero : E = 0 := by
    have hs : star E * E = 0 := by rw [hEsa.star_eq]; exact hEE
    exact (CStarRing.star_mul_self_eq_zero_iff E).mp hs
  have : (W + star W) - (A + A) = 0 := hEdef.symm.trans hEzero
  exact sub_eq_zero.mp this

/-- Real part of the polar factor equals the real part of its modulus on every
vector: a direct consequence of `W + W⋆ = 2|C|`. -/
theorem re_inner_polarFactor_eq_absoluteValue (u : H) :
    RCLike.re ⟪spectraCanonicalPolarFactor U V u, u⟫_𝕜 =
      RCLike.re ⟪ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) u, u⟫_𝕜 := by
  set W := spectraCanonicalPolarFactor U V with hWdef
  set A := ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) with hAdef
  have hWsW : W + star W = A + A := polarFactor_add_star_eq_two_absoluteValue U V
  have hkey : ⟪(W + star W) u, u⟫_𝕜 = ⟪(A + A) u, u⟫_𝕜 := by rw [hWsW]
  rw [add_apply, add_apply,
    inner_add_left, inner_add_left] at hkey
  have hstar : ⟪star W u, u⟫_𝕜 = ⟪u, W u⟫_𝕜 := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  have hre1 : RCLike.re ⟪star W u, u⟫_𝕜 = RCLike.re ⟪W u, u⟫_𝕜 := by
    rw [hstar]; exact inner_re_symm (𝕜 := 𝕜) u (W u)
  have hre := congrArg RCLike.re hkey
  rw [map_add, map_add, hre1] at hre
  linarith

/-- Positivity of the source diagonal compression of the canonical partial
polar factor.  On the source block, `re⟪x, P W P x⟫ = re⟪P x, |C| (P x)⟫ ≥ 0`
because `W + W⋆ = 2|C|` and `|C| ≥ 0`. -/
theorem canonicalPolarFactor_sourceCompression_nonnegative (x : H) :
    0 ≤ RCLike.re
      ⟪x, (U.starProjection * spectraCanonicalPolarFactor U V * U.starProjection) x⟫_𝕜 := by
  rw [re_inner_projection_compression U (spectraCanonicalPolarFactor U V) x,
    re_inner_polarFactor_eq_absoluteValue U V (U.starProjection x)]
  have hnonneg : (0 : H →L[𝕜] H) ≤
      ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) :=
    ContinuousLinearMap.modulus_nonneg _
  exact ((ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mp hnonneg).re_inner_nonneg_left
    (U.starProjection x)

/-- Positivity of the complementary diagonal compression. -/
theorem canonicalPolarFactor_complementCompression_nonnegative (x : H) :
    0 ≤ RCLike.re
      ⟪x, ((Uᗮ).starProjection * spectraCanonicalPolarFactor U V *
        (Uᗮ).starProjection) x⟫_𝕜 := by
  have hswap : spectraCanonicalPolarFactor Uᗮ Vᗮ = spectraCanonicalPolarFactor U V := by
    have hI : spectraCanonicalIntertwiner Uᗮ Vᗮ = spectraCanonicalIntertwiner U V := by
      simp only [spectraCanonicalIntertwiner,
        Submodule.orthogonal_orthogonal]
      abel
    unfold spectraCanonicalPolarFactor
    rw [hI]
  have h := canonicalPolarFactor_sourceCompression_nonnegative Uᗮ Vᗮ x
  rwa [hswap] at h

/-- The crossed blocks of the canonical partial polar factor are skew-adjoint.
Since `W + W⋆ = 2|C|` and `|C|` commutes with `P` (its Gram operator does, and
`|C|` is a continuous function of it), the Hermitian part `W + W⋆` is block
diagonal for `P`, so the off-diagonal block of `W` is the negative adjoint of
the opposite off-diagonal block. -/
theorem canonicalPolarFactor_crossed_blocks_general :
    (Uᗮ).starProjection * spectraCanonicalPolarFactor U V * U.starProjection =
      -star (U.starProjection * spectraCanonicalPolarFactor U V *
        (Uᗮ).starProjection) := by
  set W := spectraCanonicalPolarFactor U V with hWdef
  set A := ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) with hAdef
  have hcommAP : Commute A (U.starProjection) :=
    ContinuousLinearMap.commute_modulus_of_commute_star_mul_self _ _
      (commute_projection_spectraCanonicalIntertwiner_star_mul_self U V).symm
  have hP'P : (Uᗮ).starProjection * U.starProjection = 0 := by
    rw [show (Uᗮ).starProjection = 1 - U.starProjection from
        Submodule.starProjection_orthogonal' U, sub_mul, one_mul,
      U.isIdempotentElem_starProjection, sub_self]
  have hP'AP : (Uᗮ).starProjection * A * U.starProjection = 0 := by
    rw [mul_assoc, hcommAP.eq, ← mul_assoc, hP'P, zero_mul]
  have hRHS : star (U.starProjection * W * (Uᗮ).starProjection) =
      (Uᗮ).starProjection * star W * U.starProjection := by
    rw [star_mul, star_mul, (isSelfAdjoint_starProjection U).star_eq,
      (isSelfAdjoint_starProjection Uᗮ).star_eq, ← mul_assoc]
  rw [hRHS]
  have hsum : (Uᗮ).starProjection * W * U.starProjection +
      (Uᗮ).starProjection * star W * U.starProjection = 0 := by
    calc (Uᗮ).starProjection * W * U.starProjection +
          (Uᗮ).starProjection * star W * U.starProjection
        = (Uᗮ).starProjection * (W + star W) * U.starProjection := by
          rw [mul_add, add_mul]
      _ = (Uᗮ).starProjection * (A + A) * U.starProjection := by
          rw [polarFactor_add_star_eq_two_absoluteValue U V]
      _ = (Uᗮ).starProjection * A * U.starProjection +
            (Uᗮ).starProjection * A * U.starProjection := by rw [mul_add, add_mul]
      _ = 0 := by rw [hP'AP, add_zero]
  exact eq_neg_of_add_eq_zero_left hsum

/-- The defect quarter-turn has the paper crossed-block relation. -/
theorem crossedDefectQuarterTurn_crossed_blocks
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    (Uᗮ).starProjection * crossedDefectQuarterTurn U V J * U.starProjection =
      -star (U.starProjection * crossedDefectQuarterTurn U V J *
        (Uᗮ).starProjection) := by
  rw [star_mul, star_mul,
    (isSelfAdjoint_starProjection U).star_eq,
    (isSelfAdjoint_starProjection Uᗮ).star_eq,
    star_crossedDefectQuarterTurn]
  noncomm_ring

/-- The nonacute direct-rotation candidate obtained by filling the two defect
spaces with the chosen quarter-turn. -/
noncomputable def nonacuteDirectRotation
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    H →L[𝕜] H :=
  spectraCanonicalPolarFactor U V + crossedDefectQuarterTurn U V J

/-- The completed direct rotation for the complementary pair is the same operator when its
crossed-defect identification is obtained by reversing `J` and changing sign. -/
theorem nonacuteDirectRotation_orthogonal
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    nonacuteDirectRotation U.orthogonal V.orthogonal
        (orthogonalCrossedDefectEquiv U V J) =
      nonacuteDirectRotation U V J := by
  rw [nonacuteDirectRotation, nonacuteDirectRotation]
  congr 1
  · simp only [spectraCanonicalPolarFactor, spectraCanonicalIntertwiner_orthogonal]
  · ext x
    simp [crossedDefectQuarterTurn, sourceToTargetDefect, targetToSourceDefect,
      orthogonalCrossedDefectEquiv]
    abel

/-- Reversing the ordered pair sends the completed direct rotation to its
adjoint when the crossed-defect choice is reversed. -/
theorem nonacuteDirectRotation_swap
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    nonacuteDirectRotation V U (swapCrossedDefectEquiv U V J) =
      star (nonacuteDirectRotation U V J) := by
  rw [nonacuteDirectRotation, nonacuteDirectRotation, star_add,
    canonicalPolarFactor_adjoint_swap_from_polar U V,
    crossedDefectQuarterTurn_swap U V J, star_crossedDefectQuarterTurn U V J]

/-- Initial projection identity for the nonacute rotation. -/
theorem star_nonacuteDirectRotation_mul_self
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    star (nonacuteDirectRotation U V J) * nonacuteDirectRotation U V J = 1 := by
  have hcross := canonicalPolarFactor_orthogonal_defectQuarterTurn U V J
  rw [nonacuteDirectRotation, star_add]
  rw [add_mul, mul_add, mul_add]
  rw [hcross.1, hcross.2.1,
    star_crossedDefectQuarterTurn_mul_self U V J,
    (canonicalPolarFactor_initial_final_projection U V).1]
  simp [regularProjection, crossedDefectProjection,
    Submodule.starProjection_orthogonal']

/-- Final projection identity for the nonacute rotation. -/
theorem nonacuteDirectRotation_mul_star_self
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    nonacuteDirectRotation U V J * star (nonacuteDirectRotation U V J) = 1 := by
  have hcross := canonicalPolarFactor_orthogonal_defectQuarterTurn U V J
  have hpolar := (canonicalPolarFactor_initial_final_projection U V).2
  rw [nonacuteDirectRotation, star_add]
  rw [add_mul, mul_add, mul_add]
  rw [hcross.2.2.1, hcross.2.2.2,
    crossedDefectQuarterTurn_mul_star_self U V J, hpolar]
  simp [regularProjection, crossedDefectProjection,
    Submodule.starProjection_orthogonal']

/-- The completed nonacute rotation is unitary. -/
theorem nonacuteDirectRotation_mem_unitary
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    nonacuteDirectRotation U V J ∈ unitary (H →L[𝕜] H) := by
  exact ⟨star_nonacuteDirectRotation_mul_self U V J,
    nonacuteDirectRotation_mul_star_self U V J⟩

/-- The Hermitian part of the completed nonacute direct rotation is twice the
modulus of the canonical intertwiner. -/
theorem nonacuteDirectRotation_add_star_eq_two_absoluteValue
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    nonacuteDirectRotation U V J + star (nonacuteDirectRotation U V J) =
      ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) +
        ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) := by
  rw [nonacuteDirectRotation, star_add,
    star_crossedDefectQuarterTurn U V J]
  rw [← polarFactor_add_star_eq_two_absoluteValue U V]
  abel

/-- The real quadratic form of a completed nonacute direct rotation is the
quadratic form of the canonical positive cosine. -/
theorem re_inner_nonacuteDirectRotation_eq_absoluteValue
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) (x : H) :
    RCLike.re ⟪nonacuteDirectRotation U V J x, x⟫_𝕜 =
      RCLike.re ⟪ContinuousLinearMap.modulus
        (spectraCanonicalIntertwiner U V) x, x⟫_𝕜 := by
  let W := nonacuteDirectRotation U V J
  let A := ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)
  have hsum : W + star W = A + A := by
    simpa [W, A] using nonacuteDirectRotation_add_star_eq_two_absoluteValue U V J
  have hkey : ⟪(W + star W) x, x⟫_𝕜 = ⟪(A + A) x, x⟫_𝕜 := by rw [hsum]
  rw [add_apply, add_apply, inner_add_left, inner_add_left] at hkey
  have hstar : ⟪star W x, x⟫_𝕜 = ⟪x, W x⟫_𝕜 := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  have hreStar : RCLike.re ⟪star W x, x⟫_𝕜 = RCLike.re ⟪W x, x⟫_𝕜 := by
    rw [hstar]
    exact inner_re_symm (𝕜 := 𝕜) x (W x)
  have hre := congrArg RCLike.re hkey
  rw [map_add, map_add, hreStar] at hre
  linarith

omit [CompleteSpace H] in
private theorem add_self_cancel_nonacute
    {a b : H →L[𝕜] H} (h : a + a = b + b) : a = b := by
  let twoUnit : 𝕜ˣ := Units.mk0 2 (by norm_num)
  apply smul_left_cancel twoUnit
  change (2 : 𝕜) • a = (2 : 𝕜) • b
  simpa only [two_smul 𝕜] using h

/-- The completed nonacute direct rotation commutes with the modulus of the
canonical intertwiner. -/
theorem nonacuteDirectRotation_comm_absoluteValue
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    Commute (nonacuteDirectRotation U V J)
      (ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)) := by
  let W := nonacuteDirectRotation U V J
  let A := ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)
  have hunit : W ∈ unitary (H →L[𝕜] H) :=
    nonacuteDirectRotation_mem_unitary U V J
  have hsum : W + star W = A + A := by
    simpa [W, A] using nonacuteDirectRotation_add_star_eq_two_absoluteValue U V J
  have hcommStar : Commute W (star W) := by
    rw [commute_iff_eq]
    exact (Unitary.mul_star_self_of_mem hunit).trans
      (Unitary.star_mul_self_of_mem hunit).symm
  have hcommSum : Commute W (W + star W) :=
    (Commute.refl W).add_right hcommStar
  have hcommDouble : Commute W (A + A) := by rwa [← hsum]
  have hleft : W * A + W * A = A * W + A * W := by
    simpa [mul_add, add_mul] using hcommDouble.eq
  rw [commute_iff_eq]
  exact add_self_cancel_nonacute hleft

/-- The defect quarter-turn intertwines the source and target projections. -/
theorem crossedDefectQuarterTurn_intertwines
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    crossedDefectQuarterTurn U V J * U.starProjection =
      V.starProjection * crossedDefectQuarterTurn U V J := by
  ext x
  let s := (halmosSourceDefect U V).orthogonalProjectionOnto x
  let t := (halmosTargetDefect U V).orthogonalProjectionOnto x
  have hVJs : V.starProjection (J s : H) = J s :=
    Submodule.starProjection_eq_self_iff.mpr (J s).property.2
  have hVJt : V.starProjection (J.symm t : H) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr (J.symm t).property.2
  have hpS : (halmosSourceDefect U V).orthogonalProjectionOnto (U.starProjection x) = s :=
    Submodule.orthogonalProjectionOnto_starProjection_of_le inf_le_left x
  have hpT : (halmosTargetDefect U V).orthogonalProjectionOnto (U.starProjection x) = 0 := by
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff]
    exact Submodule.orthogonal_le inf_le_left
      (Submodule.le_orthogonal_orthogonal U (U.starProjection_apply_mem x))
  simp [crossedDefectQuarterTurn, sourceToTargetDefect,
    targetToSourceDefect, s, t, hVJs, hVJt, hpS, hpT]

/-- The completed nonacute rotation intertwines the two projections. -/
theorem nonacuteDirectRotation_intertwines
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    nonacuteDirectRotation U V J * U.starProjection =
      V.starProjection * nonacuteDirectRotation U V J := by
  rw [nonacuteDirectRotation, add_mul, mul_add,
    canonicalPolarFactor_intertwines_general,
    crossedDefectQuarterTurn_intertwines]

/-- Positivity of both diagonal compressions of the nonacute construction. -/
theorem nonacuteDirectRotation_compressions_nonnegative
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    (∀ x : H, 0 ≤ RCLike.re
      ⟪x, (U.starProjection * nonacuteDirectRotation U V J * U.starProjection) x⟫_𝕜) ∧
    (∀ x : H, 0 ≤ RCLike.re
      ⟪x, ((Uᗮ).starProjection * nonacuteDirectRotation U V J *
        (Uᗮ).starProjection) x⟫_𝕜) := by
  constructor
  · intro x
    rw [nonacuteDirectRotation, mul_add, add_mul]
    have hdefectZero :
        U.starProjection * crossedDefectQuarterTurn U V J * U.starProjection = 0 := by
      ext y
      simp only [mul_apply_eq_comp, zero_apply]
      have hpT : (halmosTargetDefect U V).orthogonalProjectionOnto
          (U.starProjection y) = 0 := by
        rw [Submodule.orthogonalProjectionOnto_eq_zero_iff]
        exact Submodule.orthogonal_le inf_le_left
          (Submodule.le_orthogonal_orthogonal U (U.starProjection_apply_mem y))
      have hval : crossedDefectQuarterTurn U V J (U.starProjection y) =
          (J ((halmosSourceDefect U V).orthogonalProjectionOnto
            (U.starProjection y)) : H) -
          (J.symm ((halmosTargetDefect U V).orthogonalProjectionOnto
            (U.starProjection y)) : H) := by
        simp only [crossedDefectQuarterTurn, sourceToTargetDefect,
          targetToSourceDefect, sub_apply,
          ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
          ContinuousLinearEquiv.coe_coe,
          LinearIsometryEquiv.coe_toContinuousLinearEquiv]
      rw [hval, hpT, map_zero, Submodule.coe_zero, sub_zero]
      exact (Submodule.starProjection_apply_eq_zero_iff _).mpr
        (mem_halmosTargetDefect.mp (J _).property).1
    rw [hdefectZero, add_zero]
    exact canonicalPolarFactor_sourceCompression_nonnegative U V x
  · intro x
    rw [nonacuteDirectRotation, mul_add, add_mul]
    have hdefectZero :
        (Uᗮ).starProjection * crossedDefectQuarterTurn U V J *
          (Uᗮ).starProjection = 0 := by
      ext y
      simp only [mul_apply_eq_comp, zero_apply]
      have hpS : (halmosSourceDefect U V).orthogonalProjectionOnto
          ((Uᗮ).starProjection y) = 0 := by
        rw [Submodule.orthogonalProjectionOnto_eq_zero_iff]
        exact Submodule.orthogonal_le inf_le_left (Uᗮ.starProjection_apply_mem y)
      have hval : crossedDefectQuarterTurn U V J ((Uᗮ).starProjection y) =
          (J ((halmosSourceDefect U V).orthogonalProjectionOnto
            ((Uᗮ).starProjection y)) : H) -
          (J.symm ((halmosTargetDefect U V).orthogonalProjectionOnto
            ((Uᗮ).starProjection y)) : H) := by
        simp only [crossedDefectQuarterTurn, sourceToTargetDefect,
          targetToSourceDefect, sub_apply,
          ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
          ContinuousLinearEquiv.coe_coe,
          LinearIsometryEquiv.coe_toContinuousLinearEquiv]
      simp only [hval, hpS, map_zero, Submodule.coe_zero, zero_sub, map_neg, neg_eq_zero]
      exact (Submodule.starProjection_apply_eq_zero_iff _).mpr
        (Submodule.le_orthogonal_orthogonal U
          (mem_halmosSourceDefect.mp (J.symm _).property).1)
    rw [hdefectZero, add_zero]
    exact canonicalPolarFactor_complementCompression_nonnegative U V x

/-- The crossed blocks of the nonacute construction are skew-adjoint. -/
theorem nonacuteDirectRotation_crossed_blocks
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    (Uᗮ).starProjection * nonacuteDirectRotation U V J * U.starProjection =
      -star (U.starProjection * nonacuteDirectRotation U V J *
        (Uᗮ).starProjection) := by
  simp only [nonacuteDirectRotation, mul_add, add_mul,
    star_add, neg_add]
  congr 1
  · exact canonicalPolarFactor_crossed_blocks_general U V
  · exact crossedDefectQuarterTurn_crossed_blocks U V J

/-- The explicit nonacute construction satisfies the paper's direct-rotation
predicate. -/
theorem nonacuteDirectRotation_isDirectRotation
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    IsDirectRotation U V (nonacuteDirectRotation U V J) := by
  refine
    { unitary_mem := nonacuteDirectRotation_mem_unitary U V J
      intertwines := nonacuteDirectRotation_intertwines U V J
      source_compression_nonnegative :=
        (nonacuteDirectRotation_compressions_nonnegative U V J).1
      complement_compression_nonnegative :=
        (nonacuteDirectRotation_compressions_nonnegative U V J).2
      crossed_blocks := nonacuteDirectRotation_crossed_blocks U V J }

/-- The chosen defect identification can be recovered from the completed
rotation, so the parameterization is injective. -/
theorem nonacuteDirectRotation_injective :
    Function.Injective
      (nonacuteDirectRotation U V :
        (halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) →
          H →L[𝕜] H) := by
  intro J K hJK
  apply LinearIsometryEquiv.ext
  intro x
  have hx := DFunLike.congr_fun hJK (x : H)
  have hpolar : spectraCanonicalPolarFactor U V (x : H) = 0 :=
    canonicalPolarFactor_apply_crossedDefect_eq_zero U V
      (Submodule.mem_sup.mpr ⟨x, x.property, 0, Submodule.zero_mem _, by simp⟩)
  simpa [nonacuteDirectRotation, hpolar] using hx

/-- Constructive half of Davis--Kahan Proposition 3.2. -/
theorem exists_directRotation_of_crossedDefectsEquivalent
    (hdefect : CrossedDefectsEquivalent U V) :
    ∃ T : H →L[𝕜] H, IsDirectRotation U V T := by
  rcases hdefect with ⟨J⟩
  exact ⟨nonacuteDirectRotation U V J,
    nonacuteDirectRotation_isDirectRotation U V J⟩

/-- A positive operator that has vanishing quadratic form at a vector
annihilates that vector: write `S = √S · √S`, so `⟪x, S x⟫ = ‖√S x‖²`. -/
private theorem apply_eq_zero_of_nonneg_inner_self_eq_zero
    {S : H →L[𝕜] H} (hS : (0 : H →L[𝕜] H) ≤ S) {x : H} (hx : ⟪x, S x⟫_𝕜 = 0) :
    S x = 0 := by
  have hRR : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S hS
  have hRnn : (0 : H →L[𝕜] H) ≤ CFC.sqrt S := CFC.sqrt_nonneg S
  have hRsa : IsSelfAdjoint (CFC.sqrt S) :=
    ((ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mp hRnn).isSelfAdjoint
  have hkey : ⟪CFC.sqrt S x, CFC.sqrt S x⟫_𝕜 = ⟪x, S x⟫_𝕜 := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      hRsa.star_eq, ← mul_apply_eq_comp, hRR]
  have hRx : CFC.sqrt S x = 0 := inner_self_eq_zero.mp (hkey.trans hx)
  rw [← hRR, mul_apply_eq_comp, hRx, map_zero]

/-- The adjoint of an intertwiner intertwines the swapped projections. -/
private theorem starIntertwines_of_intertwines
    {T : H →L[𝕜] H} (hint : T * U.starProjection = V.starProjection * T) :
    U.starProjection * star T = star T * V.starProjection := by
  have h := congrArg star hint
  rwa [star_mul, star_mul, (isSelfAdjoint_starProjection U).star_eq,
    (isSelfAdjoint_starProjection V).star_eq] at h

/-- A paper direct rotation conjugates the source projection to the target projection. -/
theorem directRotation_conjugates_projection
    (T : H →L[𝕜] H) (hT : IsDirectRotation U V T) :
    T * U.starProjection * star T = V.starProjection := by
  calc
    T * U.starProjection * star T = (V.starProjection * T) * star T := by
      rw [hT.intertwines]
    _ = V.starProjection * (T * star T) := by rw [mul_assoc]
    _ = V.starProjection := by rw [hT.unitary_mem.2, mul_one]

/-- A paper direct rotation also conjugates the complementary source projection to the
complementary target projection. -/
theorem directRotation_conjugates_complementaryProjection
    (T : H →L[𝕜] H) (hT : IsDirectRotation U V T) :
    T * (Uᗮ).starProjection * star T = (Vᗮ).starProjection := by
  have hinter : T * (Uᗮ).starProjection = (Vᗮ).starProjection * T := by
    rw [show (Uᗮ).starProjection = 1 - U.starProjection from
      Submodule.starProjection_orthogonal' U]
    rw [show (Vᗮ).starProjection = 1 - V.starProjection from
      Submodule.starProjection_orthogonal' V]
    rw [mul_sub, sub_mul, mul_one, one_mul, hT.intertwines]
  calc
    T * (Uᗮ).starProjection * star T =
        ((Vᗮ).starProjection * T) * star T := by rw [hinter]
    _ = (Vᗮ).starProjection * (T * star T) := by rw [mul_assoc]
    _ = (Vᗮ).starProjection := by rw [hT.unitary_mem.2, mul_one]

/-- A paper direct rotation is **accretive**: `re⟪z, T z⟫ ≥ 0`.  The two diagonal
`U`-blocks are the nonnegative compressions; the two off-diagonal blocks are
adjoint-negatives of each other (crossed blocks), so their real parts cancel. -/
theorem re_inner_directRotation_nonneg
    (T : H →L[𝕜] H) (hT : IsDirectRotation U V T) (z : H) :
    0 ≤ RCLike.re ⟪z, T z⟫_𝕜 := by
  have hsplit : T = U.starProjection * T * U.starProjection
      + U.starProjection * T * (Uᗮ).starProjection
      + (Uᗮ).starProjection * T * U.starProjection
      + (Uᗮ).starProjection * T * (Uᗮ).starProjection := by
    have hPP : U.starProjection + (Uᗮ).starProjection = 1 := by
      rw [show (Uᗮ).starProjection = 1 - U.starProjection from
        Submodule.starProjection_orthogonal' U]; abel
    calc T = (U.starProjection + (Uᗮ).starProjection) * T *
          (U.starProjection + (Uᗮ).starProjection) := by rw [hPP, one_mul, mul_one]
      _ = _ := by noncomm_ring
  have key : ⟪z, T z⟫_𝕜 = ⟪z, (U.starProjection * T * U.starProjection) z⟫_𝕜
      + ⟪z, (U.starProjection * T * (Uᗮ).starProjection) z⟫_𝕜
      + ⟪z, ((Uᗮ).starProjection * T * U.starProjection) z⟫_𝕜
      + ⟪z, ((Uᗮ).starProjection * T * (Uᗮ).starProjection) z⟫_𝕜 := by
    conv_lhs => rw [hsplit]
    simp only [add_apply, inner_add_right]
  have h2 : RCLike.re ⟪z, ((Uᗮ).starProjection * T * U.starProjection) z⟫_𝕜
      = - RCLike.re ⟪z, (U.starProjection * T * (Uᗮ).starProjection) z⟫_𝕜 := by
    rw [hT.crossed_blocks, neg_apply, inner_neg_right, map_neg]
    congr 1
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    exact inner_re_symm (𝕜 := 𝕜) _ _
  rw [key, map_add, map_add, map_add, h2]
  have hd1 := hT.source_compression_nonnegative z
  have hd2 := hT.complement_compression_nonnegative z
  linarith

/-- The Hermitian part of a paper direct rotation is a positive operator. -/
theorem directRotation_add_star_nonneg
    (T : H →L[𝕜] H) (hT : IsDirectRotation U V T) :
    (0 : H →L[𝕜] H) ≤ T + star T := by
  have hSA : IsSelfAdjoint (T + star T) := by
    rw [isSelfAdjoint_iff, star_add, star_star]; abel
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hSA, fun x => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, add_apply,
    inner_add_left, map_add]
  have e1 : RCLike.re ⟪T x, x⟫_𝕜 = RCLike.re ⟪x, T x⟫_𝕜 := inner_re_symm (𝕜 := 𝕜) (T x) x
  have e2 : RCLike.re ⟪star T x, x⟫_𝕜 = RCLike.re ⟪x, T x⟫_𝕜 := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  rw [e1, e2]
  have := re_inner_directRotation_nonneg U V T hT x
  linarith

/-- A paper direct rotation maps the source defect into the target defect.
Both `⟪x, T x⟫` and `⟪x, T⋆ x⟫` vanish (by intertwining), so `(T + T⋆) x = 0` by
positivity; hence `T x = -T⋆ x ∈ Uᗮ`. -/
theorem directRotation_mapsto_targetDefect
    (T : H →L[𝕜] H) (hT : IsDirectRotation U V T) {x : H}
    (hx : x ∈ halmosSourceDefect U V) :
    T x ∈ halmosTargetDefect U V := by
  obtain ⟨hxU, hxVp⟩ := mem_halmosSourceDefect.mp hx
  have hTxV : T x ∈ V := by
    have hPx : U.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hxU
    have h := congrArg (fun f : H →L[𝕜] H => f x) hT.intertwines
    simp only [mul_apply_eq_comp, hPx] at h
    exact Submodule.starProjection_eq_self_iff.mp h.symm
  have hsTxUp : star T x ∈ Uᗮ := by
    have h := congrArg (fun f : H →L[𝕜] H => f x)
      (starIntertwines_of_intertwines U V hT.intertwines)
    simp only [mul_apply_eq_comp,
      (Submodule.starProjection_apply_eq_zero_iff _).mpr hxVp, map_zero] at h
    exact (Submodule.starProjection_apply_eq_zero_iff _).mp h
  have hHx : (T + star T) x = 0 := by
    refine apply_eq_zero_of_nonneg_inner_self_eq_zero
      (directRotation_add_star_nonneg U V T hT) ?_
    rw [add_apply, inner_add_right,
      Submodule.inner_left_of_mem_orthogonal hTxV hxVp,
      Submodule.inner_right_of_mem_orthogonal hxU hsTxUp, add_zero]
  rw [mem_halmosTargetDefect]
  refine ⟨?_, hTxV⟩
  have hTx : T x = - star T x :=
    eq_neg_of_add_eq_zero_left (by rw [← add_apply]; exact hHx)
  rw [hTx]
  exact Submodule.neg_mem _ hsTxUp

/-- Dually, the adjoint of a paper direct rotation maps the target defect into
the source defect. -/
theorem directRotation_star_mapsto_sourceDefect
    (T : H →L[𝕜] H) (hT : IsDirectRotation U V T) {y : H}
    (hy : y ∈ halmosTargetDefect U V) :
    star T y ∈ halmosSourceDefect U V := by
  obtain ⟨hyUp, hyV⟩ := mem_halmosTargetDefect.mp hy
  have hsTyU : star T y ∈ U := by
    have h := congrArg (fun f : H →L[𝕜] H => f y)
      (starIntertwines_of_intertwines U V hT.intertwines)
    simp only [mul_apply_eq_comp,
      Submodule.starProjection_eq_self_iff.mpr hyV] at h
    exact Submodule.starProjection_eq_self_iff.mp h
  have hTyVp : T y ∈ Vᗮ := by
    have h := congrArg (fun f : H →L[𝕜] H => f y) hT.intertwines
    simp only [mul_apply_eq_comp,
      (Submodule.starProjection_apply_eq_zero_iff _).mpr hyUp, map_zero] at h
    exact (Submodule.starProjection_apply_eq_zero_iff _).mp h.symm
  have hHy : (T + star T) y = 0 := by
    refine apply_eq_zero_of_nonneg_inner_self_eq_zero
      (directRotation_add_star_nonneg U V T hT) ?_
    rw [add_apply, inner_add_right,
      Submodule.inner_right_of_mem_orthogonal hyV hTyVp,
      Submodule.inner_left_of_mem_orthogonal hsTyU hyUp, add_zero]
  rw [mem_halmosSourceDefect]
  refine ⟨hsTyU, ?_⟩
  have hsTy : star T y = - T y :=
    eq_neg_of_add_eq_zero_right (by rw [← add_apply]; exact hHy)
  rw [hsTy]
  exact Submodule.neg_mem _ hTyVp

/-- On the source crossed defect, every paper direct rotation agrees with the
negative of its adjoint.  This is the quarter-turn identity used in the proof
of Davis--Kahan Proposition 3.2. -/
theorem directRotation_apply_sourceDefect_eq_neg_star
    (T : H →L[𝕜] H) (hT : IsDirectRotation U V T) {x : H}
    (hx : x ∈ halmosSourceDefect U V) :
    T x = - star T x := by
  obtain ⟨hxU, hxVp⟩ := mem_halmosSourceDefect.mp hx
  have hTxV : T x ∈ V := by
    have hPx : U.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hxU
    have h := congrArg (fun f : H →L[𝕜] H => f x) hT.intertwines
    simp only [mul_apply_eq_comp, hPx] at h
    exact Submodule.starProjection_eq_self_iff.mp h.symm
  have hsTxUp : star T x ∈ Uᗮ := by
    have h := congrArg (fun f : H →L[𝕜] H => f x)
      (starIntertwines_of_intertwines U V hT.intertwines)
    simp only [mul_apply_eq_comp,
      (Submodule.starProjection_apply_eq_zero_iff _).mpr hxVp, map_zero] at h
    exact (Submodule.starProjection_apply_eq_zero_iff _).mp h
  have hHx : (T + star T) x = 0 := by
    refine apply_eq_zero_of_nonneg_inner_self_eq_zero
      (directRotation_add_star_nonneg U V T hT) ?_
    rw [add_apply, inner_add_right,
      Submodule.inner_left_of_mem_orthogonal hTxV hxVp,
      Submodule.inner_right_of_mem_orthogonal hxU hsTxUp, add_zero]
  exact eq_neg_of_add_eq_zero_left (by rw [← add_apply]; exact hHx)

/-- On the target crossed defect, the adjoint of every paper direct rotation
agrees with the negative of the rotation. -/
theorem directRotation_star_apply_targetDefect_eq_neg
    (T : H →L[𝕜] H) (hT : IsDirectRotation U V T) {y : H}
    (hy : y ∈ halmosTargetDefect U V) :
    star T y = - T y := by
  obtain ⟨hyUp, hyV⟩ := mem_halmosTargetDefect.mp hy
  have hsTyU : star T y ∈ U := by
    have h := congrArg (fun f : H →L[𝕜] H => f y)
      (starIntertwines_of_intertwines U V hT.intertwines)
    simp only [mul_apply_eq_comp,
      Submodule.starProjection_eq_self_iff.mpr hyV] at h
    exact Submodule.starProjection_eq_self_iff.mp h
  have hTyVp : T y ∈ Vᗮ := by
    have h := congrArg (fun f : H →L[𝕜] H => f y) hT.intertwines
    simp only [mul_apply_eq_comp,
      (Submodule.starProjection_apply_eq_zero_iff _).mpr hyUp, map_zero] at h
    exact (Submodule.starProjection_apply_eq_zero_iff _).mp h.symm
  have hHy : (T + star T) y = 0 := by
    refine apply_eq_zero_of_nonneg_inner_self_eq_zero
      (directRotation_add_star_nonneg U V T hT) ?_
    rw [add_apply, inner_add_right,
      Submodule.inner_right_of_mem_orthogonal hyV hTyVp,
      Submodule.inner_left_of_mem_orthogonal hsTyU hyUp, add_zero]
  exact eq_neg_of_add_eq_zero_right (by rw [← add_apply]; exact hHy)

/-- Every paper direct rotation squares to minus the identity on the source
crossed defect. -/
theorem directRotation_sq_apply_sourceDefect
    (T : H →L[𝕜] H) (hT : IsDirectRotation U V T) {x : H}
    (hx : x ∈ halmosSourceDefect U V) :
    T (T x) = -x := by
  have hstar : T (star T x) = x := by
    have h := DFunLike.congr_fun hT.unitary_mem.2 x
    simpa [mul_apply_eq_comp] using h
  calc
    T (T x) = T (-star T x) := by
      rw [directRotation_apply_sourceDefect_eq_neg_star U V T hT hx]
    _ = -T (star T x) := by rw [map_neg]
    _ = -x := by rw [hstar]

/-- Every paper direct rotation squares to minus the identity on the target
crossed defect. -/
theorem directRotation_sq_apply_targetDefect
    (T : H →L[𝕜] H) (hT : IsDirectRotation U V T) {y : H}
    (hy : y ∈ halmosTargetDefect U V) :
    T (T y) = -y := by
  have hrel := directRotation_star_apply_targetDefect_eq_neg U V T hT hy
  have hTy : T y = -star T y := by
    rw [hrel, neg_neg]
  have hstar : T (star T y) = y := by
    have h := DFunLike.congr_fun hT.unitary_mem.2 y
    simpa [mul_apply_eq_comp] using h
  calc
    T (T y) = T (-star T y) := by rw [hTy]
    _ = -T (star T y) := by rw [map_neg]
    _ = -y := by rw [hstar]

/-- A paper direct rotation restricts to a linear isometric equivalence between
the two crossed defects. -/
noncomputable def crossedDefectEquivOfDirectRotation
    (T : H →L[𝕜] H) (hT : IsDirectRotation U V T) :
    halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V where
  toFun x := ⟨T x, directRotation_mapsto_targetDefect U V T hT x.property⟩
  invFun y := ⟨star T y, directRotation_star_mapsto_sourceDefect U V T hT y.property⟩
  left_inv x := by
    apply Subtype.ext
    have hunit := hT.unitary_mem
    have hleft : star T * T = 1 := hunit.1
    have h := DFunLike.congr_fun hleft (x : H)
    simpa [mul_apply_eq_comp] using h
  right_inv y := by
    apply Subtype.ext
    have hunit := hT.unitary_mem
    have hright : T * star T = 1 := hunit.2
    have h := DFunLike.congr_fun hright (y : H)
    simpa [mul_apply_eq_comp] using h
  map_add' x y := by
    apply Subtype.ext
    exact map_add T (x : H) (y : H)
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul T c (x : H)
  norm_map' x := by
    have hunit := hT.unitary_mem
    exact Unitary.norm_map ⟨T, hunit⟩ x

/-- Necessity half of Davis--Kahan Proposition 3.2. -/
theorem crossedDefectsEquivalent_of_exists_directRotation
    (h : ∃ T : H →L[𝕜] H, IsDirectRotation U V T) :
    CrossedDefectsEquivalent U V := by
  rcases h with ⟨T, hT⟩
  exact ⟨crossedDefectEquivOfDirectRotation U V T hT⟩

/-- Davis--Kahan Proposition 3.2 in constructive Hilbert-dimension form. -/
theorem proposition3_2_completed :
    (∃ T : H →L[𝕜] H, IsDirectRotation U V T) ↔
      CrossedDefectsEquivalent U V := by
  constructor
  · exact crossedDefectsEquivalent_of_exists_directRotation U V
  · exact exists_directRotation_of_crossedDefectsEquivalent U V

/-- Explicit injective parameterization of all constructed extensions. -/
theorem proposition3_2_parameterization_completed
    (_hdefect : CrossedDefectsEquivalent U V) :
    ∃ build :
        (halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) →
          H →L[𝕜] H,
      (∀ J, IsDirectRotation U V (build J)) ∧
      Function.Injective build := by
  refine ⟨nonacuteDirectRotation U V, ?_,
    nonacuteDirectRotation_injective U V⟩
  intro J
  exact nonacuteDirectRotation_isDirectRotation U V J

end

end DavisKahan
end TauCeti
