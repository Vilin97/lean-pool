/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction
/-!
# Frobenius lifts for totally ramified extensions

This file constructs degree-one Frobenius lifts and the finite auxiliary
Galois extension used in the totally ramified reciprocity argument.
-/

@[expose] public section

noncomputable
section

namespace ClassFormation

open KummerTheory
open CyclicCohomology

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Every automorphism of a totally ramified Galois extension has a
Frobenius lift of exponent one. -/
theorem exists_degreeOneFrobeniusLiftOfTotallyRamified
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : GaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    ∃ σ : D.FrobeniusElements K L.field L.below,
      D.frobeniusExponent K L.field L.below σ = 1 ∧
      L.extensionQuotientMulEquiv.symm
        (D.frobeniusRestriction K L.field L.below σ) = q := by
  let φ := D.chosenDegreeOneFrobeniusElement K L.field L.below
  let q₀ := D.frobeniusRestriction K L.field L.below φ
  let qRaw := L.extensionQuotientMulEquiv q
  obtain ⟨s, hs⟩ := QuotientGroup.mk'_surjective
    (extensionSubgroup K.field L.field L.below) (qRaw * q₀⁻¹)
  have hsDegree : D.degree s.1 ∈
      K.field.toSubgroup.map D.degree.toMonoidHom := ⟨s.1, s.2, rfl⟩
  have hImage :=
    (L.isTotallyRamified_iff_image_le D).1 hTot hsDegree
  obtain ⟨l, hlL, hlDegree⟩ := hImage
  let lL : L.field.toSubgroup := ⟨l, hlL⟩
  let lK : K.field.toSubgroup := Subgroup.inclusion L.below lL
  let i : K.field.toSubgroup := s * lK⁻¹
  let t : K.field.toSubgroup ⧸
      D.extensionInertiaWithin K.field L.field L.below :=
    QuotientGroup.mk i * φ.1
  have hiDegree : D.normalizedDegree K i = 1 := by
    change i ∈ (D.normalizedDegree K).toMonoidHom.ker
    rw [D.normalizedDegree_ker K]
    change D.degree i.1 = 1
    dsimp [i, lK, lL]
    rw [map_mul, map_inv]
    change D.degree s.1 * (D.degree l)⁻¹ = 1
    rw [← hlDegree]
    simp
  have htDegree : D.extensionNormalizedDegree K L.field L.below t =
      (Multiplicative.ofAdd (1 : ZHat) : ZHatMul) ^ (1 : ℕ) := by
    change D.extensionNormalizedDegree K L.field L.below
        (QuotientGroup.mk i * φ.1) = _
    rw [map_mul, D.extensionNormalizedDegree_mk, hiDegree, one_mul]
    calc
      D.extensionNormalizedDegree K L.field L.below φ.1 =
          (Multiplicative.ofAdd (1 : ZHat) : ZHatMul) ^
              D.frobeniusExponent K L.field L.below φ :=
        D.extensionNormalizedDegree_frobenius_eq_pow K L.field L.below φ
      _ = (Multiplicative.ofAdd (1 : ZHat) : ZHatMul) ^ (1 : ℕ) := by
        rw [D.frobeniusExponent_chosenDegreeOneFrobeniusElement]
  let σ : D.FrobeniusElements K L.field L.below :=
    ⟨t, 1, Nat.one_pos, htDegree⟩
  have hσExponent : D.frobeniusExponent K L.field L.below σ = 1 := by
    apply proCIntegerOne_pow_nat_injective
    calc
      (Multiplicative.ofAdd (1 : ZHat) : ZHatMul) ^
            D.frobeniusExponent K L.field L.below σ =
          D.extensionNormalizedDegree K L.field L.below σ.1 :=
        (D.extensionNormalizedDegree_frobenius_eq_pow
          K L.field L.below σ).symm
      _ = (Multiplicative.ofAdd (1 : ZHat) : ZHatMul) ^ (1 : ℕ) :=
        htDegree
  refine ⟨σ, hσExponent, ?_⟩
  refine L.extensionQuotientMulEquiv.symm_apply_eq.mpr ?_
  change D.extensionRestriction K.field L.field L.below
      (QuotientGroup.mk i * φ.1) = qRaw
  rw [map_mul, D.extensionRestriction_mk]
  have hiRestriction :
      (QuotientGroup.mk i :
        K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below) =
        QuotientGroup.mk s := by
    dsimp [i]
    change (QuotientGroup.mk' (extensionSubgroup K.field L.field L.below))
        (s * lK⁻¹) =
      (QuotientGroup.mk' (extensionSubgroup K.field L.field L.below)) s
    rw [map_mul, map_inv]
    have hlOne :
        (QuotientGroup.mk' (extensionSubgroup K.field L.field L.below)) lK = 1 := by
      apply (QuotientGroup.eq_one_iff _).2
      exact lL.2
    rw [hlOne, inv_one, mul_one]
  rw [hiRestriction]
  change (QuotientGroup.mk' (extensionSubgroup K.field L.field L.below)) s * q₀ = qRaw
  rw [hs]
  simp [q₀]
/-- In a totally ramified finite Galois extension every finite automorphism
has a degree-one Frobenius lift.  This is the element denoted
`\tilde\sigma = \sigma\varphi_L`. -/
noncomputable def chosenDegreeOneFrobeniusLiftOfTotallyRamified
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : GaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    D.FrobeniusElements K L.field L.below :=
  Classical.choose
    (D.exists_degreeOneFrobeniusLiftOfTotallyRamified
      K L hTot q)
/-- The chosen Frobenius lift for a totally ramified extension has exponent one. -/
@[simp]
theorem frobeniusExponent_chosenDegreeOneFrobeniusLiftOfTotallyRamified
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : GaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    D.frobeniusExponent K L.field L.below
      (D.chosenDegreeOneFrobeniusLiftOfTotallyRamified
        K L hTot q) = 1 := by
  exact (Classical.choose_spec
    (D.exists_degreeOneFrobeniusLiftOfTotallyRamified
      K L hTot q)).1
/-- The chosen degree-one Frobenius lift restricts to the prescribed automorphism. -/
@[simp]
theorem frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfTotallyRamified
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : GaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    L.extensionQuotientMulEquiv.symm
        (D.frobeniusRestriction K L.field L.below
          (D.chosenDegreeOneFrobeniusLiftOfTotallyRamified
            K L hTot q)) = q := by
  exact (Classical.choose_spec
    (D.exists_degreeOneFrobeniusLiftOfTotallyRamified
      K L hTot q)).2
/-- Underlying quotient form of the Galois-bundle restriction theorem. -/
theorem frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfTotallyRamified_underlying
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : GaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    D.frobeniusRestriction K L.field L.below
        (D.chosenDegreeOneFrobeniusLiftOfTotallyRamified
          K L hTot q) =
      L.extensionQuotientMulEquiv q := by
  apply L.extensionQuotientMulEquiv.symm.injective
  exact
    D.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfTotallyRamified
      K L hTot q
/-- The degree-one lift specialized to a bundled finite Galois extension.
The conversion to the non-finite Galois boundary and the quotient comparison
are performed once in this definition. -/
noncomputable def chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    D.FrobeniusElements K L.field L.below :=
  D.chosenDegreeOneFrobeniusLiftOfTotallyRamified
    K L.toGaloisSubextension
      (L.isTotallyRamified_toGaloisSubextension D hTot)
      (L.toGaloisExtensionQuotientMulEquiv q)
/-- The finite totally ramified Frobenius lift has exponent one. -/
@[simp]
theorem frobeniusExponent_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    D.frobeniusExponent K L.field L.below
      (D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
        K L hTot q) = 1 := by
  exact D.frobeniusExponent_chosenDegreeOneFrobeniusLiftOfTotallyRamified
    K L.toGaloisSubextension
      (L.isTotallyRamified_toGaloisSubextension D hTot)
      (L.toGaloisExtensionQuotientMulEquiv q)
/-- The finite totally ramified Frobenius lift restricts to the chosen automorphism. -/
@[simp]
theorem frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    L.extensionQuotientMulEquiv.symm
        (D.frobeniusRestriction K L.field L.below
          (D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
            K L hTot q)) = q := by
  refine L.extensionQuotientMulEquiv.symm_apply_eq.mpr ?_
  have h :=
    D.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfTotallyRamified_underlying
      K L.toGaloisSubextension
        (L.isTotallyRamified_toGaloisSubextension D hTot)
        (L.toGaloisExtensionQuotientMulEquiv q)
  change
    D.frobeniusRestriction K L.field L.below
        (D.chosenDegreeOneFrobeniusLiftOfTotallyRamified
          K L.toGaloisSubextension
            (L.isTotallyRamified_toGaloisSubextension D hTot)
            (L.toGaloisExtensionQuotientMulEquiv q)) =
      L.extensionQuotientMulEquiv q at h
  exact h
/-- Underlying quotient form of the preceding finite-bundle theorem. -/
theorem frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified_underlying
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    D.frobeniusRestriction K L.field L.below
        (D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
          K L hTot q) =
      L.extensionQuotientMulEquiv q := by
  apply L.extensionQuotientMulEquiv.symm.injective
  exact
    D.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
      K L hTot q
/-- The finite Galois extension `M / K` chosen.  It contains both
`L` and the degree-one Frobenius fixed field `Σ`, and is contained in the
maximal unramified extension of `L`. -/
noncomputable def abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    FiniteGaloisSubextension K.field := by
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    K L hTot q
  letI : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below) :=
    L.finite
  let SigmaI := D.frobeniusFixedIntermediateField K L.field L.below σ
  let LI := D.fieldAsMaximalUnramifiedIntermediate K.field L.field L.below
  let C := SigmaI.compositum LI
  letI : (extensionSubgroup K.field (D.maximalUnramifiedField L.field)
      (D.maximalUnramifiedField_le_of_le L.below)).Normal :=
    D.extensionSubgroup_maximalUnramifiedField_normal K.field L.field L.below
  let M := C.galoisRefinement
  exact
    { field := M.field
      below := M.below
      normal := by
        exact FiniteIntermediateField.galoisRefinement_normal C
      finite := M.finite }
/-- The auxiliary reciprocity extension lies below the given totally ramified extension. -/
theorem abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    (D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q).field.toSubgroup ≤ L.field.toSubgroup := by
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    K L hTot q
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below) :=
    L.finite
  let SigmaI := D.frobeniusFixedIntermediateField K L.field L.below σ
  let LI := D.fieldAsMaximalUnramifiedIntermediate K.field L.field L.below
  let C := SigmaI.compositum LI
  let : (extensionSubgroup K.field (D.maximalUnramifiedField L.field)
      (D.maximalUnramifiedField_le_of_le L.below)).Normal :=
    D.extensionSubgroup_maximalUnramifiedField_normal K.field L.field L.below
  change (C.galoisRefinement).field.toSubgroup ≤ L.field.toSubgroup
  exact C.galoisRefinement_le_field.trans
    (FiniteIntermediateField.compositum_le_right SigmaI LI)
/-- The auxiliary reciprocity extension is fixed by the selected automorphism. -/
theorem abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_sigma
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    (D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q).field.toSubgroup ≤
      (D.frobeniusFixedField K L.field L.below
        (D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
          K L hTot q)).toSubgroup := by
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    K L hTot q
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below) :=
    L.finite
  let SigmaI := D.frobeniusFixedIntermediateField K L.field L.below σ
  let LI := D.fieldAsMaximalUnramifiedIntermediate K.field L.field L.below
  let C := SigmaI.compositum LI
  let : (extensionSubgroup K.field (D.maximalUnramifiedField L.field)
      (D.maximalUnramifiedField_le_of_le L.below)).Normal :=
    D.extensionSubgroup_maximalUnramifiedField_normal K.field L.field L.below
  change (C.galoisRefinement).field.toSubgroup ≤ SigmaI.field.toSubgroup
  exact C.galoisRefinement_le_field.trans
    (FiniteIntermediateField.compositum_le_left SigmaI LI)

/-- The maximal unramified field lies below the auxiliary totally ramified reciprocity field. -/
theorem maximalUnramifiedField_le_abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    (D.maximalUnramifiedField L.field).toSubgroup ≤
      (D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
        K L hTot q).field.toSubgroup := by
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    K L hTot q
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below) :=
    L.finite
  let SigmaI := D.frobeniusFixedIntermediateField K L.field L.below σ
  let LI := D.fieldAsMaximalUnramifiedIntermediate K.field L.field L.below
  let C := SigmaI.compositum LI
  let : (extensionSubgroup K.field (D.maximalUnramifiedField L.field)
      (D.maximalUnramifiedField_le_of_le L.below)).Normal :=
    D.extensionSubgroup_maximalUnramifiedField_normal K.field L.field L.below
  change (D.maximalUnramifiedField L.field).toSubgroup ≤
    (C.galoisRefinement).field.toSubgroup
  exact (C.galoisRefinement).above

end DegreeData

end ClassFormation
