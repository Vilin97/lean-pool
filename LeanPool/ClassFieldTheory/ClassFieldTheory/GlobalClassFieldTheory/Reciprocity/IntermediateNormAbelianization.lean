/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueAbelianizationNaturality
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormTowerConductor
/-!
# Abelianized restriction over intermediate fields

For a finite Galois extension and an arbitrary intermediate field, this file
identifies the image of abelianized restriction with the image of the fixing
subgroup.  It then proves naturality for the ordinary idèle-class norm and
identifies its range as the Artin preimage of that abelianized fixing-subgroup
image.  No normality of the intermediate extension over the base is assumed.
-/

@[expose] public section

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    {K N : Type}
    [Field K] [NumberField K]
    [Field N] [NumberField N]
    [Algebra K N] [IsGalois K N]

/-- Restriction from the Galois group over an intermediate field, passed to
abelianizations. -/
noncomputable def intermediateAbelianizedRestriction
    (M : IntermediateField K N) :
    Abelianization Gal(N/M) →* Abelianization Gal(N/K) :=
  Abelianization.map
    (AlgEquiv.restrictScalarsHom K : Gal(N/M) →* Gal(N/K))

omit [NumberField K] [NumberField N] [IsGalois K N] in
/-- The image of abelianized restriction from an intermediate field is the
image of its fixing subgroup in the ambient abelianization. -/
theorem intermediateAbelianizedRestriction_range_eq_fixingSubgroup_image
    (M : IntermediateField K N) :
    (intermediateAbelianizedRestriction (K := K) (N := N) M).range =
      M.fixingSubgroup.map
        (Abelianization.of : Gal(N/K) →* Abelianization Gal(N/K)) := by
  ext z
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨sigma, rfl⟩ :=
      QuotientGroup.mk'_surjective
        (_root_.commutator Gal(N/M)) q
    let tau : M.fixingSubgroup :=
      (IntermediateField.fixingSubgroupEquiv M).symm sigma
    refine ⟨tau, tau.property, ?_⟩
    change
      Abelianization.of (tau : Gal(N/K)) =
        Abelianization.of
          ((AlgEquiv.restrictScalarsHom K) sigma)
    rfl
  · rintro ⟨tau, htau, rfl⟩
    let sigma : Gal(N/M) :=
      IntermediateField.fixingSubgroupEquiv M ⟨tau, htau⟩
    refine ⟨Abelianization.of sigma, ?_⟩
    change
      Abelianization.of
          ((AlgEquiv.restrictScalarsHom K) sigma) =
        Abelianization.of tau
    rfl

/-- After the surjective global norm-residue map over an intermediate field,
abelianized restriction still has exactly the fixing-subgroup image. -/
theorem
    intermediateAbelianizedRestriction_comp_globalNormResidue_range_eq_fixingSubgroup_image
    (M : IntermediateField K N) :
    ((intermediateAbelianizedRestriction (K := K) (N := N) M).comp
        (globalNormResidueAbelianizationMonoidHom M N)).range =
      M.fixingSubgroup.map
        (Abelianization.of : Gal(N/K) →* Abelianization Gal(N/K)) := by
  calc
    ((intermediateAbelianizedRestriction (K := K) (N := N) M).comp
        (globalNormResidueAbelianizationMonoidHom M N)).range =
        (intermediateAbelianizedRestriction (K := K) (N := N) M).range := by
      apply le_antisymm
      · rintro z ⟨c, rfl⟩
        exact ⟨globalNormResidueAbelianizationMonoidHom M N c, rfl⟩
      · rintro z ⟨q, rfl⟩
        obtain ⟨c, hc⟩ :=
          globalNormResidueAbelianizationMonoidHom_surjective M N q
        refine ⟨c, ?_⟩
        simp only [MonoidHom.comp_apply, hc]
    _ = M.fixingSubgroup.map
        (Abelianization.of : Gal(N/K) →* Abelianization Gal(N/K)) :=
      intermediateAbelianizedRestriction_range_eq_fixingSubgroup_image M

/-- Ordinary idèle-class norm from an arbitrary intermediate field agrees
with restriction of the finite-Galois global norm-residue symbol after
abelianization.  No normality of the intermediate field over the base is
assumed. -/
theorem globalNormResidueAbelianization_comp_ideleClassNorm_intermediate
    (M : IntermediateField K N) :
    (globalNormResidueAbelianizationMonoidHom K N).comp
        (_root_.ideleClassNorm K M) =
      (intermediateAbelianizedRestriction (K := K) (N := N) M).comp
        (globalNormResidueAbelianizationMonoidHom M N) := by
  exact
    (globalNormResidueAbelianizationMonoidHom_norm_restriction
      K M N).symm

/-- The norm subgroup from an arbitrary intermediate field is the inverse
image, under finite-Galois global reciprocity, of the image of its fixing
subgroup in the ambient Galois abelianization. -/
theorem ideleClassNorm_range_eq_artin_preimage_abelianizedFixingSubgroup
    (M : IntermediateField K N) :
    (_root_.ideleClassNorm K M).range =
      (M.fixingSubgroup.map
        (Abelianization.of : Gal(N/K) →* Abelianization Gal(N/K))).comap
        (globalNormResidueAbelianizationMonoidHom K N) := by
  let f := globalNormResidueAbelianizationMonoidHom K N
  let g := globalNormResidueAbelianizationMonoidHom M N
  let r := intermediateAbelianizedRestriction (K := K) (N := N) M
  let n := _root_.ideleClassNorm K M
  have hnat :=
    globalNormResidueAbelianization_comp_ideleClassNorm_intermediate
      (K := K) (N := N) M
  have hrange :=
    intermediateAbelianizedRestriction_range_eq_fixingSubgroup_image
      (K := K) (N := N) M
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    change f (n c) ∈
      M.fixingSubgroup.map
        (Abelianization.of : Gal(N/K) →* Abelianization Gal(N/K))
    have hpoint : f (n c) = r (g c) :=
      DFunLike.congr_fun hnat c
    rw [hpoint, ← hrange]
    exact ⟨g c, rfl⟩
  · intro hx
    change f x ∈
      M.fixingSubgroup.map
        (Abelianization.of : Gal(N/K) →* Abelianization Gal(N/K))
      at hx
    have hxrange : f x ∈ r.range := by
      rw [hrange]
      exact hx
    obtain ⟨q, hq⟩ := hxrange
    obtain ⟨c, hc⟩ :=
      globalNormResidueAbelianizationMonoidHom_surjective M N q
    have hpoint : f (n c) = r (g c) :=
      DFunLike.congr_fun hnat c
    have heq : f x = f (n c) := by
      calc
        f x = r q := hq.symm
        _ = r (g c) := congrArg r hc.symm
        _ = f (n c) := hpoint.symm
    have hker : x * (n c)⁻¹ ∈ f.ker := by
      change f (x * (n c)⁻¹) = 1
      rw [map_mul, map_inv, heq, mul_inv_cancel]
    have htop :
        x * (n c)⁻¹ ∈ (_root_.ideleClassNorm K N).range := by
      rw [← globalNormResidueAbelianizationMonoidHom_ker K N]
      exact hker
    have htopIntermediate :
        x * (n c)⁻¹ ∈ (_root_.ideleClassNorm K M).range :=
      GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_range_le_of_tower
        (K := K) (M := M) (L := N) htop
    have hnc : n c ∈ (_root_.ideleClassNorm K M).range := ⟨c, rfl⟩
    have hproduct :=
      (_root_.ideleClassNorm K M).range.mul_mem htopIntermediate hnc
    simpa only [inv_mul_cancel_right] using hproduct

end Reciprocity
end GlobalClassFieldTheory
