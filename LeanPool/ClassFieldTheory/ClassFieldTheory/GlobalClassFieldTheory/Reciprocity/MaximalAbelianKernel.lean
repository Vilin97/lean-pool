/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerAlgEquivNaturality
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdentityComponent
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldOriginalField
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MaximalAbelianGlobalArtin
/-!
# The kernel of maximal abelian global reciprocity

This module identifies the kernel of the maximal abelian global Artin map
with the identity component of the idele class group.  It then descends the
map to the component quotient.

The separation argument is intrinsic to the compact totally disconnected
component quotient.  A separating open normal subgroup is pulled back to a
closed finite-index idele-class subgroup, whose selected finite class field
supplies the detecting finite Galois coordinate.
-/

open scoped Classical NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open GlobalClassFields

variable (K : Type) [Field K] [NumberField K]

/-- A class outside the identity component is excluded by a closed
finite-index subgroup which contains the identity component. -/
theorem exists_closedFiniteIndexSubgroup_not_mem_of_not_mem_identityComponent
    (c : IdeleClassGroup K)
    (hc : c ∉ ideleClassIdentityComponent K) :
    ∃ H : Subgroup (IdeleClassGroup K),
      IsClosed (H : Set (IdeleClassGroup K)) ∧
        H.FiniteIndex ∧
          ideleClassIdentityComponent K ≤ H ∧ c ∉ H := by
  let C := ideleClassIdentityComponent K
  let q : IdeleClassGroup K →* ideleClassComponentQuotient K :=
    QuotientGroup.mk' C
  have hqc : q c ≠ 1 := by
    intro h
    exact hc ((QuotientGroup.eq_one_iff c).mp h)
  let U : Set (ideleClassComponentQuotient K) := {q c}ᶜ
  have hUopen : IsOpen U := isClosed_singleton.isOpen_compl
  have hUone : (1 : ideleClassComponentQuotient K) ∈ U := by
    simpa [U, eq_comm] using hqc
  obtain ⟨V, hVU⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      hUopen hUone
  let H : Subgroup (IdeleClassGroup K) :=
    (V : Subgroup (ideleClassComponentQuotient K)).comap q
  have hHopen : IsOpen (H : Set (IdeleClassGroup K)) := by
    change IsOpen (q ⁻¹' (V : Set (ideleClassComponentQuotient K)))
    exact V.isOpen.preimage QuotientGroup.continuous_mk
  have hHclosed : IsClosed (H : Set (IdeleClassGroup K)) :=
    Subgroup.isClosed_of_isOpen H hHopen
  have hVfinite :
      (V : Subgroup (ideleClassComponentQuotient K)).FiniteIndex :=
    V.toOpenSubgroup.finiteIndex_of_finite_quotient
  have hHfinite : H.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    rw [show H.index =
        (V : Subgroup (ideleClassComponentQuotient K)).index by
      simpa only [H] using
        (V : Subgroup (ideleClassComponentQuotient K)).index_comap_of_surjective
          (QuotientGroup.mk'_surjective C)]
    exact hVfinite.index_ne_zero
  have hCH : C ≤ H := by
    intro x hx
    change q x ∈ V
    have hqx : q x = 1 :=
      (QuotientGroup.eq_one_iff x).2 hx
    rw [hqx]
    change (1 : ideleClassComponentQuotient K) ∈ V.toOpenSubgroup
    exact V.toOpenSubgroup.one_mem
  have hcH : c ∉ H := by
    intro hcH
    have hqcV : q c ∈ V := hcH
    have : q c ∈ ({q c} : Set (ideleClassComponentQuotient K))ᶜ :=
      hVU hqcV
    exact this (by simp)
  exact ⟨H, hHclosed, hHfinite, hCH, hcH⟩

/-- Replacing a finite abelian extension by its selected finite layer in the
maximal abelian extension preserves its idele-class norm range. -/
theorem finiteAbelianExtensionInMaximalAbelianExtension_ideleClassNorm_range
    (L : Type) [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    let E := finiteAbelianExtensionInMaximalAbelianExtension K L
    letI : NumberField E := NumberField.of_module_finite K E
    (_root_.ideleClassNorm K E).range =
      (_root_.ideleClassNorm K L).range := by
  let E := finiteAbelianExtensionInMaximalAbelianExtension K L
  let e : L ≃ₐ[K] E :=
    finiteAbelianExtensionEquivInMaximalAbelianExtension K L
  let hE : NumberField E := NumberField.of_module_finite K E
  let : NumberField E := hE
  have htransport :=
    ordinaryIdeleClassNorm_range_map_congrOfAlgEquiv
      (K := K) (K' := K) (L := L) (L' := E)
      (AlgEquiv.refl : K ≃ₐ[ℚ] K)
      (e.restrictScalars ℚ)
      (fun x => e.commutes x)
  calc
    (_root_.ideleClassNorm K E).range =
        (_root_.ideleClassNorm K L).range.map
          (ideleClassCongr
            (AlgEquiv.refl : K ≃ₐ[ℚ] K)).toMonoidHom :=
      htransport.symm
    _ = (_root_.ideleClassNorm K L).range := by
      ext c
      constructor
      · rintro ⟨d, hd, rfl⟩
        simpa using hd
      · intro hc
        exact ⟨c, hc, by simp⟩

/-- The kernel of the maximal abelian global Artin map is exactly the
identity component of the idele class group. -/
@[simp]
theorem maximalAbelianGlobalArtin_ker :
    (maximalAbelianGlobalArtin K).ker =
      ideleClassIdentityComponent K := by
  apply le_antisymm
  · intro c hc
    change (maximalAbelianGlobalArtin K).toMonoidHom c = 1 at hc
    by_contra hcIdentity
    obtain ⟨H, hHclosed, hHfinite, _, hcH⟩ :=
      exists_closedFiniteIndexSubgroup_not_mem_of_not_mem_identityComponent
        K c hcIdentity
    let : H.FiniteIndex := hHfinite
    let L := closedFiniteIndexClassField (K := K) H hHclosed
    let : NumberField L := NumberField.of_module_finite K L
    let E := finiteAbelianExtensionInMaximalAbelianExtension K L
    let : NumberField E := NumberField.of_module_finite K E
    have hNormE : (_root_.ideleClassNorm K E).range = H := by
      calc
        (_root_.ideleClassNorm K E).range =
            (_root_.ideleClassNorm K L).range :=
          finiteAbelianExtensionInMaximalAbelianExtension_ideleClassNorm_range
            K L
        _ = H :=
          closedFiniteIndexClassField_ideleClassNorm_range
            (K := K) H hHclosed
    obtain ⟨a, rfl⟩ :=
      QuotientGroup.mk'_surjective
        (IdeleGroup.principalSubgroup K) c
    have hFiniteArtin :
        globalIdeleClassArtinMonoidHom
            (K := K) (L := E)
            (QuotientGroup.mk'
              (IdeleGroup.principalSubgroup K) a) = 1 := by
      rw [globalIdeleClassArtinMonoidHom_mk,
        ← maximalAbelianGlobalArtin_finiteProjection K a E]
      change
        (AlgEquiv.restrictNormalHom
          (F := K) (K₁ := maximalAbelianExtension K) E)
            ((maximalAbelianGlobalArtin K).toMonoidHom
              (QuotientGroup.mk'
                (IdeleGroup.principalSubgroup K) a)) = 1
      calc
        _ = (AlgEquiv.restrictNormalHom
              (F := K) (K₁ := maximalAbelianExtension K) E) 1 :=
          congrArg
            (AlgEquiv.restrictNormalHom
              (F := K) (K₁ := maximalAbelianExtension K) E) hc
        _ = 1 := map_one _
    have hNormMem :
        QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a ∈
          (_root_.ideleClassNorm K E).range :=
      (globalIdeleClassArtinMonoidHom_eq_one_iff
        (K := K) (L := E) _).mp hFiniteArtin
    rw [hNormE] at hNormMem
    exact hcH hNormMem
  · exact
      ideleClassIdentityComponent_le_ker K
        (maximalAbelianGlobalArtin K)

/-- Maximal abelian reciprocity identifies the component quotient of the
idele class group with the maximal abelian Galois group. -/
noncomputable def ideleClassComponentQuotientEquivMaximalAbelianGalois :
    ideleClassComponentQuotient K ≃ₜ*
      Gal(maximalAbelianExtension K / K) := by
  let e : ideleClassComponentQuotient K ≃*
      Gal(maximalAbelianExtension K / K) :=
    QuotientGroup.liftEquiv
      (ideleClassIdentityComponent K)
      (maximalAbelianGlobalArtin_surjective K)
      (maximalAbelianGlobalArtin_ker K).symm
  have heContinuous : Continuous e := by
    apply
      (QuotientGroup.isQuotientMap_mk
        (ideleClassIdentityComponent K)).continuous_iff.mpr
    refine
      (maximalAbelianGlobalArtin K).continuous_toFun.congr
        (fun c => ?_)
    exact
      (QuotientGroup.liftEquiv_coe
        (ideleClassIdentityComponent K)
        (maximalAbelianGlobalArtin_surjective K)
        (maximalAbelianGlobalArtin_ker K).symm c).symm
  let h := heContinuous.homeoOfEquivCompactToT2
  exact
    { toMulEquiv := e
      continuous_toFun := h.continuous
      continuous_invFun := h.symm.continuous }

/-- Evaluation of component-quotient reciprocity on an idele class is the
maximal abelian global Artin map. -/
@[simp]
theorem ideleClassComponentQuotientEquivMaximalAbelianGalois_mk
    (c : IdeleClassGroup K) :
    ideleClassComponentQuotientEquivMaximalAbelianGalois K
        (QuotientGroup.mk'
          (ideleClassIdentityComponent K) c) =
      maximalAbelianGlobalArtin K c := by
  change
    QuotientGroup.liftEquiv
        (ideleClassIdentityComponent K)
        (maximalAbelianGlobalArtin_surjective K)
        (maximalAbelianGlobalArtin_ker K).symm
        (QuotientGroup.mk'
          (ideleClassIdentityComponent K) c) =
      maximalAbelianGlobalArtin K c
  exact QuotientGroup.liftEquiv_coe _ _ _ _

end Reciprocity
end GlobalClassFieldTheory
