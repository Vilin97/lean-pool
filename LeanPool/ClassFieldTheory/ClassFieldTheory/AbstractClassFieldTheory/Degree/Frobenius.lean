/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields

/-! # Frobenius -/

@[expose] public section
namespace ClassFormation

/-!
# normalized degree and Frobenius theory: normalized degree maps and Frobenius

For a field of finite residue degree, this file constructs the map
`d_K = (1 / f_K) d`; division is performed only after proving that
`d(G_K) = f_K ℤ̂`.  The Frobenius is then the unique class mapping to `1`.
-/

noncomputable
section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The image `d(G_K)`, written additively inside `ℤ̂`. -/
def fieldImageAdd (D : DegreeData G) (K : ClosedSubgroup G) : AddSubgroup ZHat :=
  Subgroup.toAddSubgroup' (D.fieldImage K)

/-- The additive degree image has index equal to the field's positive residue degree. -/
@[simp]
theorem fieldImageAdd_index (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    (D.fieldImageAdd K.field).index = (K.residueDegree : ℕ) := by
  change (D.fieldImage K.field).index = (K.residueDegree : ℕ)
  rw [← Subgroup.relIndex_top_right]
  change Nat.card (D.residueQuotient K.field) = (K.residueDegree : ℕ)
  exact K.residueDegree_coe.symm

/-- Finite residue degree identifies `d(G_K)` with `f_K ℤ̂`. -/
theorem fieldImageAdd_eq_mulNat_range (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    D.fieldImageAdd K.field =
      (zHatMulNat (K.residueDegree : ℕ)).toAddMonoidHom.range := by
  apply zHatAddSubgroup_eq_mulNat_range_of_index_eq
  · exact K.residueDegree.property
  · exact D.fieldImageAdd_index K

/-- The raw value `d(k)` regarded as an element of the subgroup `f_K ℤ̂`. -/
def restrictedDegreeInMulNatRange (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (k : K.field.toSubgroup) :
    (zHatMulNat (K.residueDegree : ℕ)).toAddMonoidHom.range := by
  refine ⟨(D.degree k.1).toAdd, ?_⟩
  rw [← D.fieldImageAdd_eq_mulNat_range K]
  change D.degree k.1 ∈ D.fieldImage K.field
  exact ⟨k, rfl⟩

/-- The restricted degree in the natural-multiple range has the original additive value. -/
@[simp]
theorem restrictedDegreeInMulNatRange_coe (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (k : K.toSubgroup) :
    (D.restrictedDegreeInMulNatRange K k).1 = (D.degree k.1).toAdd :=
  rfl

/-- The normalized degree map `d_K = (1 / f_K)d`. -/
def normalizedDegree (D : DegreeData G) (K : FiniteResidueAbstractField D) :
    K.field.toSubgroup →ₜ* ZHatMul where
  toFun k := Multiplicative.ofAdd
    (zHatDivide (K.residueDegree : ℕ) K.residueDegree.property
      (D.restrictedDegreeInMulNatRange K k))
  map_one' := by
    apply Multiplicative.ext
    change zHatDivide (K.residueDegree : ℕ) K.residueDegree.property
      (D.restrictedDegreeInMulNatRange K 1) = 0
    rw [show D.restrictedDegreeInMulNatRange K 1 = 0 by
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd (map_one D.degree)]
    exact map_zero (zHatDivide (K.residueDegree : ℕ) K.residueDegree.property)
  map_mul' x y := by
    apply Multiplicative.ext
    change zHatDivide (K.residueDegree : ℕ) K.residueDegree.property
        (D.restrictedDegreeInMulNatRange K (x * y)) =
      zHatDivide (K.residueDegree : ℕ) K.residueDegree.property
          (D.restrictedDegreeInMulNatRange K x) +
        zHatDivide (K.residueDegree : ℕ) K.residueDegree.property
          (D.restrictedDegreeInMulNatRange K y)
    rw [show D.restrictedDegreeInMulNatRange K (x * y) =
        D.restrictedDegreeInMulNatRange K x +
          D.restrictedDegreeInMulNatRange K y by
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd
        (map_mul D.degree x.1 y.1)]
    exact map_add (zHatDivide (K.residueDegree : ℕ) K.residueDegree.property) _ _
  continuous_toFun := by
    apply (map_continuous
      (zHatDivide (K.residueDegree : ℕ) K.residueDegree.property)).comp
    exact Continuous.subtype_mk
      (D.restrictedDegree K.field).continuous_toFun
      (fun k => (D.restrictedDegreeInMulNatRange K k).2)

/-- The additive coordinate of normalized degree is obtained by dividing by the residue degree. -/
@[simp]
theorem normalizedDegree_apply_toAdd (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (k : K.field.toSubgroup) :
    (D.normalizedDegree K k).toAdd =
      zHatDivide (K.residueDegree : ℕ) K.residueDegree.property
        (D.restrictedDegreeInMulNatRange K k) :=
  rfl

/-- The defining identity `f_K d_K = d`. -/
theorem residueDegree_nsmul_normalizedDegree (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (k : K.field.toSubgroup) :
    (K.residueDegree : ℕ) • (D.normalizedDegree K k).toAdd =
      (D.degree k.1).toAdd := by
  exact zHatMulNat_zHatDivide (K.residueDegree : ℕ) K.residueDegree.property
    (D.restrictedDegreeInMulNatRange K k)

/-- The normalized map is surjective, exactly as asserted before the normalized Frobenius
definition. -/
theorem normalizedDegree_surjective (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    Function.Surjective (D.normalizedDegree K) := by
  intro z
  have hzImageAdd : (K.residueDegree : ℕ) • z.toAdd ∈
      D.fieldImageAdd K.field := by
    rw [D.fieldImageAdd_eq_mulNat_range K]
    exact ⟨z.toAdd, rfl⟩
  have hzImage : Multiplicative.ofAdd ((K.residueDegree : ℕ) • z.toAdd) ∈
      D.fieldImage K.field := hzImageAdd
  obtain ⟨k, hk⟩ := hzImage
  refine ⟨k, ?_⟩
  apply Multiplicative.ext
  apply zHatMulNat_injective K.residueDegree.property
  change (K.residueDegree : ℕ) • (D.normalizedDegree K k).toAdd =
    (K.residueDegree : ℕ) • z.toAdd
  rw [D.residueDegree_nsmul_normalizedDegree K k]
  exact congrArg Multiplicative.toAdd hk

/-- The kernel of `d_K` is the inertia group `I_K`. -/
theorem normalizedDegree_ker (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    (D.normalizedDegree K).toMonoidHom.ker = D.fieldInertiaWithin K.field := by
  ext k
  constructor
  · intro hk
    change D.degree k.1 = 1
    apply Multiplicative.ext
    rw [← D.residueDegree_nsmul_normalizedDegree K k]
    change (K.residueDegree : ℕ) • (D.normalizedDegree K k).toAdd = 0
    rw [show D.normalizedDegree K k = 1 from hk]
    simp
  · intro hk
    apply Multiplicative.ext
    apply zHatMulNat_injective K.residueDegree.property
    change (K.residueDegree : ℕ) • (D.normalizedDegree K k).toAdd =
      (K.residueDegree : ℕ) • (1 : ZHatMul).toAdd
    rw [D.residueDegree_nsmul_normalizedDegree K k]
    rw [show D.degree k.1 = 1 from hk]
    simp

private theorem fieldInertiaWithin_le_normalizedDegree_ker
    (D : DegreeData G) (K : FiniteResidueAbstractField D) :
    D.fieldInertiaWithin K.field ≤ (D.normalizedDegree K).toMonoidHom.ker := by
  rw [D.normalizedDegree_ker K]

/-- The isomorphism `d_K : G(\widetilde K|K) ≃ ℤ̂`. -/
def maximalUnramifiedDegreeEquiv (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    (K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field) ≃* ZHatMul := by
  let dquot : (K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field) →* ZHatMul :=
    QuotientGroup.lift (D.fieldInertiaWithin K.field)
      (D.normalizedDegree K).toMonoidHom
      (by exact D.fieldInertiaWithin_le_normalizedDegree_ker K)
  apply MulEquiv.ofBijective dquot
  constructor
  · intro x y hxy
    refine Quotient.inductionOn₂' x y ?_ hxy
    intro a b hab
    apply QuotientGroup.eq.mpr
    change a⁻¹ * b ∈ D.fieldInertiaWithin K.field
    rw [← D.normalizedDegree_ker K]
    change D.normalizedDegree K (a⁻¹ * b) = 1
    rw [map_mul, map_inv]
    have hab' : D.normalizedDegree K a = D.normalizedDegree K b := by
      simpa [dquot] using hab
    rw [hab', inv_mul_cancel]
  · exact QuotientGroup.lift_surjective_of_surjective
      (D.fieldInertiaWithin K.field)
      (D.normalizedDegree K).toMonoidHom
      (D.normalizedDegree_surjective K)
      (by exact D.fieldInertiaWithin_le_normalizedDegree_ker K)

/-- On quotient representatives, the maximal-unramified degree equivalence is normalized degree. -/
@[simp]
theorem maximalUnramifiedDegreeEquiv_mk (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (k : K.field.toSubgroup) :
    D.maximalUnramifiedDegreeEquiv K (QuotientGroup.mk k) =
      D.normalizedDegree K k := by
  rfl

/-- **the normalized Frobenius definition.** The Frobenius over `K`, characterized by
`d_K(φ_K)=1`. -/
def frobenius (D : DegreeData G) (K : FiniteResidueAbstractField D) :
    K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field :=
  (D.maximalUnramifiedDegreeEquiv K).symm
    (Multiplicative.ofAdd (1 : ZHat))

/-- The maximal-unramified degree equivalence sends Frobenius to the generator one. -/
@[simp]
theorem maximalUnramifiedDegreeEquiv_frobenius (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    D.maximalUnramifiedDegreeEquiv K (D.frobenius K) =
      Multiplicative.ofAdd (1 : ZHat) := by
  exact (D.maximalUnramifiedDegreeEquiv K).apply_symm_apply _

/-- Uniqueness clause in the normalized Frobenius definition. -/
theorem eq_frobenius_iff (D : DegreeData G)
    (K : FiniteResidueAbstractField D)
    (σ : K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field) :
    σ = D.frobenius K ↔
      D.maximalUnramifiedDegreeEquiv K σ =
        Multiplicative.ofAdd (1 : ZHat) := by
  constructor
  · rintro rfl
    exact D.maximalUnramifiedDegreeEquiv_frobenius K
  · intro h
    exact (D.maximalUnramifiedDegreeEquiv K).injective
      (h.trans (D.maximalUnramifiedDegreeEquiv_frobenius K).symm)

/-- For a finite extension, its positive residue degree times the absolute
residue degree of the base is the absolute residue degree of the field. -/
theorem FiniteResidueAbstractExtension.residueDegree_mul_absoluteResidueDegree
    (D : DegreeData G) (E : FiniteResidueAbstractExtension D) :
    (E.residueDegree : ℕ) * (E.base.residueDegree : ℕ) =
      (E.field.residueDegree : ℕ) := by
  have h :=
    AbstractExtension.relativeResidueDegreeCardinal_mul_residueDegreeCardinal
      E.toFiniteAbstractExtension.toAbstractExtension D
  rw [E.toFiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe D] at h
  change ((E.residueDegree : ℕ) : Cardinal) *
      D.residueDegreeCardinal E.base.field =
    D.residueDegreeCardinal E.field.field at h
  rw [E.base.residueDegreeCardinal_eq_coe,
    E.field.residueDegreeCardinal_eq_coe] at h
  exact_mod_cast h

/-- **Frobenius residue-degree compatibility (residue degrees).** If `f_K` and `f_L` are finite,
then `f_{L|K} = f_L / f_K`. -/
theorem frobeniusRestrictionNaturality_residueDegree (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) :
    (E.residueDegree : ℕ) =
      (E.field.residueDegree : ℕ) / (E.base.residueDegree : ℕ) := by
  rw [← E.residueDegree_mul_absoluteResidueDegree D]
  rw [Nat.mul_comm (E.residueDegree : ℕ) (E.base.residueDegree : ℕ)]
  exact (Nat.mul_div_cancel_left _ E.base.residueDegree.property).symm

/-- **Frobenius residue-degree compatibility (commutative square).** On `G_L`, the normalized
degree maps satisfy `d_K = f_{L|K} d_L`. -/
theorem frobeniusRestrictionNaturality_normalizedDegree (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D)
    (l : E.field.field.toSubgroup) :
    (D.normalizedDegree E.base (Subgroup.inclusion E.below l)).toAdd =
      (E.residueDegree : ℕ) •
        (D.normalizedDegree E.field l).toAdd := by
  apply zHatMulNat_injective E.base.residueDegree.property
  change (E.base.residueDegree : ℕ) •
      (D.normalizedDegree E.base (Subgroup.inclusion E.below l)).toAdd =
    (E.base.residueDegree : ℕ) •
      ((E.residueDegree : ℕ) •
        (D.normalizedDegree E.field l).toAdd)
  rw [D.residueDegree_nsmul_normalizedDegree E.base]
  change (D.degree l.1).toAdd = _
  rw [smul_smul, Nat.mul_comm (E.base.residueDegree : ℕ),
    E.residueDegree_mul_absoluteResidueDegree D,
    D.residueDegree_nsmul_normalizedDegree E.field]

private theorem fieldInertiaWithin_le_comap_inclusion
    (D : DegreeData G) {L K : ClosedSubgroup G}
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    D.fieldInertiaWithin L ≤
      (D.fieldInertiaWithin K).comap (Subgroup.inclusion hLK) := by
  intro l hl
  exact hl

/-- Restriction `G(\widetilde L/L) → G(\widetilde K/K)` for `L | K`. -/
def maximalUnramifiedRestriction (D : DegreeData G) {L K : ClosedSubgroup G}
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    (L.toSubgroup ⧸ D.fieldInertiaWithin L) →*
      (K.toSubgroup ⧸ D.fieldInertiaWithin K) :=
  QuotientGroup.map (D.fieldInertiaWithin L) (D.fieldInertiaWithin K)
    (Subgroup.inclusion hLK) (by exact D.fieldInertiaWithin_le_comap_inclusion hLK)

/-- Maximal-unramified restriction sends a quotient representative to its
restricted representative. -/
@[simp]
theorem maximalUnramifiedRestriction_mk (D : DegreeData G)
    {L K : ClosedSubgroup G} (hLK : L.toSubgroup ≤ K.toSubgroup)
    (l : L.toSubgroup) :
    D.maximalUnramifiedRestriction hLK (QuotientGroup.mk l) =
      QuotientGroup.mk (Subgroup.inclusion hLK l) := by
  rfl

/-- The quotient form of the commutative square in Frobenius residue-degree compatibility. -/
theorem frobeniusRestrictionNaturality_quotient_square (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D)
    (σ : E.field.field.toSubgroup ⧸ D.fieldInertiaWithin E.field.field) :
    (D.maximalUnramifiedDegreeEquiv E.base
      (D.maximalUnramifiedRestriction E.below σ)).toAdd =
      (E.residueDegree : ℕ) •
        (D.maximalUnramifiedDegreeEquiv E.field σ).toAdd := by
  refine Quotient.inductionOn' σ ?_
  intro l
  simpa using D.frobeniusRestrictionNaturality_normalizedDegree E l

/-- The final assertion of Frobenius residue-degree compatibility:
`φ_L|_{\widetilde K} = φ_K ^ f_{L|K}`. -/
theorem frobenius_restriction_eq_power (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) :
    D.maximalUnramifiedRestriction E.below (D.frobenius E.field) =
      (D.frobenius E.base) ^ (E.residueDegree : ℕ) := by
  apply (D.maximalUnramifiedDegreeEquiv E.base).injective
  apply Multiplicative.ext
  rw [map_pow]
  change (D.maximalUnramifiedDegreeEquiv E.base
      (D.maximalUnramifiedRestriction E.below
        (D.frobenius E.field))).toAdd =
    (E.residueDegree : ℕ) •
      (D.maximalUnramifiedDegreeEquiv E.base
        (D.frobenius E.base)).toAdd
  rw [D.frobeniusRestrictionNaturality_quotient_square E,
    D.maximalUnramifiedDegreeEquiv_frobenius,
    D.maximalUnramifiedDegreeEquiv_frobenius]

end DegreeData

end
end ClassFormation
