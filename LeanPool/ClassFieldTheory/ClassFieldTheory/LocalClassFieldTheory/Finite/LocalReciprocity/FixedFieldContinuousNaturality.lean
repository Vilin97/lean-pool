/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldNormResidueNaturality
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology
/-!
# Continuous fixed-field naturality diagrams

The algebraic norm--restriction and transfer--inclusion diagrams are upgraded
here to diagrams of continuous homomorphisms.  Every finite fixed field uses
the spectral norm extended from the original local field.  Thus no source is
made discrete merely to obtain continuity.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped NNReal ValuativeRel
open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation LocalClassFieldTheory

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- The quotient topology on the algebraic abelianization.  Its underlying
quotient is opaque to typeclass search, so expose the canonical topology
locally while constructing the continuous finite maps. -/
private local instance abelianizationQuotientTopologicalSpace
    (G : Type*) [Group G] [TopologicalSpace G] :
    TopologicalSpace (Abelianization G) := by
  change TopologicalSpace (G ⧸ commutator G)
  exact QuotientGroup.instTopologicalSpace (commutator G)

/-! ## Multiplicative forms of the algebraic arrows -/

/-- The fixed-field norm-residue symbol on the native multiplicative unit
group.  This is the multiplicative form of
`abstractFixedFieldNormResidueSymbol`. -/
noncomputable def abstractFixedFieldNormResidueMonoidHom
    (D : DegreeData (Gal(Ω/k)))
    (v : ValuationData D (galoisAmbientUnitsRep k Ω))
    (hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep k Ω))
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω / k))) K
          (le_baseField K))] :
    (abstractFixedField k Ω K)ˣ →*
      Abelianization
        Gal(abstractRelativeFixedField k Ω hLK /
          abstractFixedField k Ω K) :=
  MonoidHom.toAdditive.symm
    (abstractFixedFieldNormResidueSymbol
      k Ω D v hcf K L hLK)

/-- The ordinary fixed-field norm on native multiplicative unit groups. -/
def abstractFixedFieldNormUnitsMonoidHom
    (K K' : ClosedSubgroup (Gal(Ω/k)))
    (hK'K : K'.toSubgroup ≤ K.toSubgroup) :
    (abstractRelativeFixedField k Ω hK'K)ˣ →*
      (abstractFixedField k Ω K)ˣ :=
  MonoidHom.toAdditive.symm
    (abstractFixedFieldNormUnits k Ω K K' hK'K)

/-- Inclusion of native multiplicative fixed-field unit groups. -/
def abstractFixedFieldUnitsInclusionMonoidHom
    (K K' : ClosedSubgroup (Gal(Ω/k)))
    (hK'K : K'.toSubgroup ≤ K.toSubgroup) :
    (abstractFixedField k Ω K)ˣ →*
      (abstractFixedField k Ω K')ˣ :=
  MonoidHom.toAdditive.symm
    (abstractFixedFieldUnitsInclusion k Ω K K' hK'K)

/-- Restriction on native multiplicative finite abelianizations. -/
noncomputable def abstractFixedFieldAbelianizedRestrictionMonoidHom
    (K K' L L' : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hL'normal : (extensionSubgroup K' L' hL'K').Normal] :
    Abelianization
        Gal(abstractRelativeFixedField k Ω hL'K' /
          abstractFixedField k Ω K') →*
      Abelianization
        Gal(abstractRelativeFixedField k Ω hLK /
          abstractFixedField k Ω K) :=
  MonoidHom.toAdditive.symm
    (abstractFixedFieldAbelianizedRestriction
      k Ω K K' L L' hLK hL'K' hK'K hL'L)

/-- Transfer on native multiplicative finite abelianizations. -/
noncomputable def abstractFixedFieldAbelianizedTransferMonoidHom
    (K K' L : ClosedSubgroup (Gal(Ω/k)))
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hLfinite : Finite
      (K.toSubgroup ⧸
        extensionSubgroup K L (hLK'.trans hK'K))] :
    letI : (extensionSubgroup K' L hLK').Normal :=
      transferNormNaturality_intermediateExtension_normal
        K K' L hLK' hK'K
    letI : Finite
        (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
      FiniteGaloisSubextension.finite_extension_over_intermediate
        (hLK'.trans hK'K) hK'K hLK'
    Abelianization
        Gal(abstractRelativeFixedField k Ω
            (hLK'.trans hK'K) /
          abstractFixedField k Ω K) →*
      Abelianization
        Gal(abstractRelativeFixedField k Ω hLK' /
          abstractFixedField k Ω K') :=
  MonoidHom.toAdditive.symm
    (abstractFixedFieldAbelianizedTransfer
      k Ω K K' L hLK' hK'K)

/-! ## The norm kernel -/

/-- Under the concrete fixed-unit equivalence, the finite abstract norm
subgroup pulls back to the ordinary field-norm subgroup. -/
theorem abstractFixedFieldUnitsEquiv_finiteNormSubgroup_preimage
    [IsSepClosed Ω]
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω / k))) K
          (le_baseField K))] :
    (finiteNormSubgroup (galoisAmbientUnitsRep k Ω)
        K L hLK).comap
      (abstractFixedFieldUnitsEquivGaloisFixed
        k Ω K).toAddMonoidHom =
      additiveNormSubgroup
        (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK) := by
  let uK := abstractFixedFieldUnitsEquivGaloisFixed k Ω K
  let uL := abstractRelativeFixedFieldUnitsEquivGaloisFixed
    k Ω K L hLK
  ext x
  constructor
  · intro hx
    change uK x ∈ finiteNormSubgroup
      (galoisAmbientUnitsRep k Ω) K L hLK at hx
    rcases hx with ⟨b, hb⟩
    let y : Additive (abstractRelativeFixedField k Ω hLK)ˣ :=
      uL.symm b
    have hy : uL y = b := uL.apply_symm_apply b
    have hnorm :=
      relativeNorm_abstractFixedFieldUnit_eq_normUnits
        k Ω K L hLK (Additive.toMul y)
    rw [show Additive.ofMul (Additive.toMul y) = y by rfl, hy] at hnorm
    change Additive.toMul x ∈ (LocalFieldTheory.normUnits
      (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK)).range
    refine ⟨Additive.toMul y, ?_⟩
    apply Additive.ofMul.injective
    apply uK.injective
    exact hnorm.symm.trans hb
  · intro hx
    change Additive.toMul x ∈ (LocalFieldTheory.normUnits
      (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK)).range at hx
    rcases hx with ⟨y, hy⟩
    change uK x ∈ finiteNormSubgroup
      (galoisAmbientUnitsRep k Ω) K L hLK
    refine ⟨uL (Additive.ofMul y), ?_⟩
    rw [relativeNorm_abstractFixedFieldUnit_eq_normUnits
      k Ω K L hLK y]
    exact congrArg uK (congrArg Additive.ofMul hy)

/-- The kernel of the additive fixed-field norm-residue symbol is the
ordinary norm subgroup, written additively. -/
theorem abstractFixedFieldNormResidueSymbol_ker
    (D : DegreeData (Gal(Ω/k)))
    (v : ValuationData D (galoisAmbientUnitsRep k Ω))
    (hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep k Ω))
    [IsSepClosed Ω]
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω / k))) K
          (le_baseField K))] :
    (abstractFixedFieldNormResidueSymbol
      k Ω D v hcf K L hLK).ker =
      additiveNormSubgroup
        (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK) := by
  let A := galoisAmbientUnitsRep k Ω
  let KF : FiniteAbstractField (Gal(Ω / k)) :=
    ⟨K, hKabsolute⟩
  let E : FiniteGaloisSubextension K :=
    ⟨L, hLK, hnormal, hfinite⟩
  let q := abstractExtensionQuotientEquivGaloisGroup
    k Ω K L hLK hnormal
  let e := (D.normResidueSymbol A v hcf KF E).trans
    (MulEquiv.toAdditive q.abelianizationCongr)
  let uK := abstractFixedFieldUnitsEquivGaloisFixed k Ω K
  calc
    (abstractFixedFieldNormResidueSymbol
        k Ω D v hcf K L hLK).ker =
        (finiteNormSubgroup A K L hLK).comap
          uK.toAddMonoidHom := by
      ext x
      change e
          (finiteNormClass A K L hLK (uK x)) = 0 ↔
        uK x ∈ finiteNormSubgroup A K L hLK
      rw [e.map_eq_zero_iff]
      exact finiteNormClass_eq_zero_iff A K L hLK (uK x)
    _ = additiveNormSubgroup
          (abstractFixedField k Ω K)
          (abstractRelativeFixedField k Ω hLK) :=
      abstractFixedFieldUnitsEquiv_finiteNormSubgroup_preimage
        k Ω K L hLK

/-- The kernel of the multiplicative fixed-field norm-residue homomorphism
is the ordinary norm subgroup. -/
theorem abstractFixedFieldNormResidueMonoidHom_ker
    (D : DegreeData (Gal(Ω/k)))
    (v : ValuationData D (galoisAmbientUnitsRep k Ω))
    (hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep k Ω))
    [IsSepClosed Ω]
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω / k))) K
          (le_baseField K))] :
    (abstractFixedFieldNormResidueMonoidHom
      k Ω D v hcf K L hLK).ker =
      localNormSubgroup
        (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK) := by
  change (abstractFixedFieldNormResidueSymbol
    k Ω D v hcf K L hLK).ker.toSubgroup = _
  rw [abstractFixedFieldNormResidueSymbol_ker
    k Ω D v hcf K L hLK]
  rfl

/-! ## Continuous arrows -/

/-- The fixed-field norm-residue symbol, bundled as a genuinely continuous
homomorphism for the spectral topology on the source field. -/
noncomputable def abstractFixedFieldNormResidueMap
    [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    [IsSepClosed Ω]
    (D : DegreeData (Gal(Ω/k)))
    (v : ValuationData D (galoisAmbientUnitsRep k Ω))
    (hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep k Ω))
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω / k))) K
          (le_baseField K))] :
    letI : FiniteDimensional k (abstractFixedField k Ω K) :=
      abstractFixedField_finiteDimensional k Ω K hKabsolute
    letI : NontriviallyNormedField (abstractFixedField k Ω K) :=
      finiteExtensionSpectralNormedField k (abstractFixedField k Ω K)
    (abstractFixedField k Ω K)ˣ →ₜ*
      Abelianization
        Gal(abstractRelativeFixedField k Ω hLK /
          abstractFixedField k Ω K) := by
  let F := abstractFixedField k Ω K
  let E := abstractRelativeFixedField k Ω hLK
  letI : FiniteDimensional k F :=
    abstractFixedField_finiteDimensional k Ω K hKabsolute
  letI : NontriviallyNormedField F :=
    finiteExtensionSpectralNormedField k F
  letI : CompleteSpace F := finiteExtensionSpectralCompleteSpace k F
  letI : ValuativeRel F := finiteExtensionSpectralValuativeRel k F
  letI : IsNonarchimedeanLocalField F :=
    finiteExtensionSpectralIsNonarchimedeanLocalField k F
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K L hLK hKabsolute hfinite
  letI : IsGalois F E :=
    abstractRelativeFixedField_isGalois k Ω K L hLK hnormal
  letI : DiscreteTopology (Abelianization Gal(E / F)) :=
    QuotientGroup.discreteTopology (isOpen_discrete _)
  let f := abstractFixedFieldNormResidueMonoidHom
    k Ω D v hcf K L hLK
  refine { f with continuous_toFun := ?_ }
  apply continuous_of_continuousAt_one f
  rw [ContinuousAt, map_one,
    @nhds_discrete (Abelianization Gal(E / F)) _ _, Filter.tendsto_pure]
  have hopen : IsOpen (f.ker : Set Fˣ) := by
    rw [abstractFixedFieldNormResidueMonoidHom_ker
      k Ω D v hcf K L hLK]
    exact localNormSubgroup_isOpen F E
  exact hopen.mem_nhds (by simp)

/-- The ordinary norm on fixed-field units, continuously bundled for the
two spectral topologies extended from the original local field. -/
noncomputable def abstractFixedFieldNormUnitsMap
    [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (K K' : ClosedSubgroup (Gal(Ω / k)))
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω / k))) K
          (le_baseField K))]
    [hK'absolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω / k))) K'
          (le_baseField K'))]
    [hK'Kfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K K' hK'K)] :
    letI : FiniteDimensional k (abstractFixedField k Ω K) :=
      abstractFixedField_finiteDimensional k Ω K hKabsolute
    letI : FiniteDimensional k
        (abstractRelativeFixedField k Ω hK'K) :=
      abstractFixedField_finiteDimensional k Ω K' hK'absolute
    letI : NontriviallyNormedField (abstractFixedField k Ω K) :=
      finiteExtensionSpectralNormedField k (abstractFixedField k Ω K)
    letI : NontriviallyNormedField
        (abstractRelativeFixedField k Ω hK'K) :=
      finiteExtensionSpectralNormedField k
        (abstractRelativeFixedField k Ω hK'K)
    (abstractRelativeFixedField k Ω hK'K)ˣ →ₜ*
      (abstractFixedField k Ω K)ˣ := by
  let F := abstractFixedField k Ω K
  let F' := abstractRelativeFixedField k Ω hK'K
  letI : FiniteDimensional k F :=
    abstractFixedField_finiteDimensional k Ω K hKabsolute
  letI : FiniteDimensional k F' :=
    abstractFixedField_finiteDimensional k Ω K' hK'absolute
  letI : NontriviallyNormedField F :=
    finiteExtensionSpectralNormedField k F
  letI : NontriviallyNormedField F' :=
    finiteExtensionSpectralNormedField k F'
  letI : IsScalarTower k F F' := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional F F' :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K K' hK'K hKabsolute hK'Kfinite
  letI : CompleteSpace F := finiteExtensionSpectralCompleteSpace k F
  letI : NormedAlgebra F F' :=
    finiteExtensionSpectralNormedAlgebra k F F'
  let f := abstractFixedFieldNormUnitsMonoidHom
    k Ω K K' hK'K
  refine { f with continuous_toFun := ?_ }
  change Continuous (LocalFieldTheory.normUnits F F')
  exact normUnits_continuous_of_finiteDimensional F F'

/-- Inclusion of fixed-field units, continuously bundled for the two
spectral topologies extended from the original local field. -/
noncomputable def abstractFixedFieldUnitsInclusionMap
    [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (K K' : ClosedSubgroup (Gal(Ω / k)))
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω / k))) K
          (le_baseField K))]
    [hK'absolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω / k))) K'
          (le_baseField K'))] :
    letI : FiniteDimensional k (abstractFixedField k Ω K) :=
      abstractFixedField_finiteDimensional k Ω K hKabsolute
    letI : FiniteDimensional k (abstractFixedField k Ω K') :=
      abstractFixedField_finiteDimensional k Ω K' hK'absolute
    letI : NontriviallyNormedField (abstractFixedField k Ω K) :=
      finiteExtensionSpectralNormedField k (abstractFixedField k Ω K)
    letI : NontriviallyNormedField (abstractFixedField k Ω K') :=
      finiteExtensionSpectralNormedField k (abstractFixedField k Ω K')
    (abstractFixedField k Ω K)ˣ →ₜ*
      (abstractFixedField k Ω K')ˣ := by
  let F := abstractFixedField k Ω K
  let F' := abstractFixedField k Ω K'
  letI : FiniteDimensional k F :=
    abstractFixedField_finiteDimensional k Ω K hKabsolute
  letI : FiniteDimensional k F' :=
    abstractFixedField_finiteDimensional k Ω K' hK'absolute
  letI : NontriviallyNormedField F :=
    finiteExtensionSpectralNormedField k F
  letI : NontriviallyNormedField F' :=
    finiteExtensionSpectralNormedField k F'
  letI : NontriviallyNormedField k :=
    localFieldNontriviallyNormedField k
  letI : IsUltrametricDist k := localFieldIsUltrametricDist k
  letI : CompleteSpace k := inferInstance
  letI : NormedSpace k F := spectralNorm.normedSpace k F
  letI : NormedSpace k F' := spectralNorm.normedSpace k F'
  let f := abstractFixedFieldUnitsInclusionMonoidHom
    k Ω K K' hK'K
  refine { f with continuous_toFun := ?_ }
  exact Continuous.units_map _
    (IntermediateField.inclusion
      (abstractFixedField_le k Ω hK'K)).toLinearMap.continuous_of_finiteDimensional

/-- Abelianized restriction, continuously bundled for the finite native
Krull quotient topologies. -/
noncomputable def abstractFixedFieldAbelianizedRestrictionMap
    (K K' L L' : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hL'normal : (extensionSubgroup K' L' hL'K').Normal]
    [hL'K'finite : Finite
      (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K')]
    [hK'absolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω / k))) K'
          (le_baseField K'))] :
    Abelianization
        Gal(abstractRelativeFixedField k Ω hL'K' /
          abstractFixedField k Ω K') →ₜ*
      Abelianization
        Gal(abstractRelativeFixedField k Ω hLK /
          abstractFixedField k Ω K) := by
  let F' := abstractFixedField k Ω K'
  let E' := abstractRelativeFixedField k Ω hL'K'
  letI : FiniteDimensional F' E' :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K' L' hL'K' hK'absolute hL'K'finite
  letI : IsGalois F' E' :=
    abstractRelativeFixedField_isGalois
      k Ω K' L' hL'K' hL'normal
  letI : DiscreteTopology (Abelianization Gal(E' / F')) :=
    QuotientGroup.discreteTopology (isOpen_discrete _)
  let f := abstractFixedFieldAbelianizedRestrictionMonoidHom
    k Ω K K' L L' hLK hL'K' hK'K hL'L
  exact { f with continuous_toFun := continuous_of_discreteTopology }

/-- Abelianized transfer, continuously bundled for the finite native Krull
quotient topologies. -/
noncomputable def abstractFixedFieldAbelianizedTransferMap
    (K K' L : ClosedSubgroup (Gal(Ω/k)))
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hLfinite : Finite
      (K.toSubgroup ⧸
        extensionSubgroup K L (hLK'.trans hK'K))]
    [hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω / k))) K
          (le_baseField K))] :
    letI : (extensionSubgroup K' L hLK').Normal :=
      transferNormNaturality_intermediateExtension_normal
        K K' L hLK' hK'K
    letI : Finite
        (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
      FiniteGaloisSubextension.finite_extension_over_intermediate
        (hLK'.trans hK'K) hK'K hLK'
    Abelianization
        Gal(abstractRelativeFixedField k Ω
            (hLK'.trans hK'K) /
          abstractFixedField k Ω K) →ₜ*
      Abelianization
        Gal(abstractRelativeFixedField k Ω hLK' /
          abstractFixedField k Ω K') := by
  letI : (extensionSubgroup K' L hLK').Normal :=
    transferNormNaturality_intermediateExtension_normal
      K K' L hLK' hK'K
  letI : Finite
      (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
    FiniteGaloisSubextension.finite_extension_over_intermediate
      (hLK'.trans hK'K) hK'K hLK'
  let F := abstractFixedField k Ω K
  let E := abstractRelativeFixedField k Ω
    (hLK'.trans hK'K)
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K L (hLK'.trans hK'K) hKabsolute hLfinite
  letI : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      k Ω K L (hLK'.trans hK'K) hLnormal
  letI : DiscreteTopology (Abelianization Gal(E / F)) :=
    QuotientGroup.discreteTopology (isOpen_discrete _)
  let f := abstractFixedFieldAbelianizedTransferMonoidHom
    k Ω K K' L hLK' hK'K
  exact { f with continuous_toFun := continuous_of_discreteTopology }

/-! ## Continuous norm--restriction square -/

namespace LocalFixedFieldNormRestrictionSquare

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

/-- The lower horizontal norm-residue arrow as a continuous homomorphism. -/
noncomputable def lowerNormResidueMap
    (T : LocalFixedFieldNormRestrictionSquare k) :
    letI : FiniteDimensional k
        (abstractFixedField k (SeparableClosure k) T.lowerBase) :=
      abstractFixedField_finiteDimensional
        k (SeparableClosure k) T.lowerBase T.lowerAbsoluteFinite
    letI : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.lowerBase) :=
      finiteExtensionSpectralNormedField k
        (abstractFixedField k (SeparableClosure k) T.lowerBase)
    (abstractFixedField k (SeparableClosure k) T.lowerBase)ˣ →ₜ*
      Abelianization
        Gal(abstractRelativeFixedField k (SeparableClosure k)
            T.lowerTop_le_lowerBase /
          abstractFixedField k (SeparableClosure k) T.lowerBase) := by
  letI := T.lowerNormal
  letI := T.lowerFinite
  letI := T.lowerAbsoluteFinite
  exact abstractFixedFieldNormResidueMap
    k (SeparableClosure k)
    (localResidueDatum k) (localHenselianValuation k)
    (separableClosureUnits_isClassFormation k)
    T.lowerBase T.lowerTop T.lowerTop_le_lowerBase

/-- Forgetting continuity recovers the lower algebraic norm-residue map. -/
theorem lowerNormResidueMap_toMonoidHom
    (T : LocalFixedFieldNormRestrictionSquare k) :
    letI : FiniteDimensional k
        (abstractFixedField k (SeparableClosure k) T.lowerBase) :=
      abstractFixedField_finiteDimensional
        k (SeparableClosure k) T.lowerBase T.lowerAbsoluteFinite
    letI : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.lowerBase) :=
      finiteExtensionSpectralNormedField k
        (abstractFixedField k (SeparableClosure k) T.lowerBase)
    (lowerNormResidueMap T).toMonoidHom =
      MonoidHom.toAdditive.symm (lowerNormResidueSymbol T) := rfl

/-- The upper horizontal norm-residue arrow as a continuous homomorphism. -/
noncomputable def upperNormResidueMap
    (T : LocalFixedFieldNormRestrictionSquare k) :
    letI : FiniteDimensional k
        (abstractFixedField k (SeparableClosure k) T.upperBase) :=
      abstractFixedField_finiteDimensional
        k (SeparableClosure k) T.upperBase (upperAbsoluteFinite T)
    letI : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.upperBase) :=
      finiteExtensionSpectralNormedField k
        (abstractFixedField k (SeparableClosure k) T.upperBase)
    (abstractFixedField k (SeparableClosure k) T.upperBase)ˣ →ₜ*
      Abelianization
        Gal(abstractRelativeFixedField k (SeparableClosure k)
            T.upperTop_le_upperBase /
          abstractFixedField k (SeparableClosure k) T.upperBase) := by
  letI := T.upperNormal
  letI := T.upperFinite
  letI := upperAbsoluteFinite T
  exact abstractFixedFieldNormResidueMap
    k (SeparableClosure k)
    (localResidueDatum k) (localHenselianValuation k)
    (separableClosureUnits_isClassFormation k)
    T.upperBase T.upperTop T.upperTop_le_upperBase

/-- Forgetting continuity recovers the upper algebraic norm-residue map. -/
theorem upperNormResidueMap_toMonoidHom
    (T : LocalFixedFieldNormRestrictionSquare k) :
    letI : FiniteDimensional k
        (abstractFixedField k (SeparableClosure k) T.upperBase) :=
      abstractFixedField_finiteDimensional
        k (SeparableClosure k) T.upperBase (upperAbsoluteFinite T)
    letI : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.upperBase) :=
      finiteExtensionSpectralNormedField k
        (abstractFixedField k (SeparableClosure k) T.upperBase)
    (upperNormResidueMap T).toMonoidHom =
      MonoidHom.toAdditive.symm (upperNormResidueSymbol T) := rfl

/-- The vertical ordinary norm arrow as a continuous homomorphism. -/
noncomputable def normUnitsMap
    (T : LocalFixedFieldNormRestrictionSquare k) :
    letI : FiniteDimensional k
        (abstractFixedField k (SeparableClosure k) T.lowerBase) :=
      abstractFixedField_finiteDimensional
        k (SeparableClosure k) T.lowerBase T.lowerAbsoluteFinite
    letI : FiniteDimensional k
        (abstractRelativeFixedField k (SeparableClosure k)
          T.upperBase_le_lowerBase) :=
      abstractFixedField_finiteDimensional
        k (SeparableClosure k) T.upperBase (upperAbsoluteFinite T)
    letI : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.lowerBase) :=
      finiteExtensionSpectralNormedField k
        (abstractFixedField k (SeparableClosure k) T.lowerBase)
    letI : NontriviallyNormedField
        (abstractRelativeFixedField k (SeparableClosure k)
          T.upperBase_le_lowerBase) :=
      finiteExtensionSpectralNormedField k
        (abstractRelativeFixedField k (SeparableClosure k)
          T.upperBase_le_lowerBase)
    (abstractRelativeFixedField k (SeparableClosure k)
        T.upperBase_le_lowerBase)ˣ →ₜ*
      (abstractFixedField k (SeparableClosure k) T.lowerBase)ˣ := by
  letI := T.lowerAbsoluteFinite
  letI := upperAbsoluteFinite T
  letI := T.baseFinite
  exact abstractFixedFieldNormUnitsMap
    k (SeparableClosure k)
    T.lowerBase T.upperBase T.upperBase_le_lowerBase

/-- Forgetting continuity recovers the algebraic norm on units. -/
theorem normUnitsMap_toMonoidHom
    (T : LocalFixedFieldNormRestrictionSquare k) :
    letI : FiniteDimensional k
        (abstractFixedField k (SeparableClosure k) T.lowerBase) :=
      abstractFixedField_finiteDimensional
        k (SeparableClosure k) T.lowerBase T.lowerAbsoluteFinite
    letI : FiniteDimensional k
        (abstractRelativeFixedField k (SeparableClosure k)
          T.upperBase_le_lowerBase) :=
      abstractFixedField_finiteDimensional
        k (SeparableClosure k) T.upperBase (upperAbsoluteFinite T)
    letI : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.lowerBase) :=
      finiteExtensionSpectralNormedField k
        (abstractFixedField k (SeparableClosure k) T.lowerBase)
    letI : NontriviallyNormedField
        (abstractRelativeFixedField k (SeparableClosure k)
          T.upperBase_le_lowerBase) :=
      finiteExtensionSpectralNormedField k
        (abstractRelativeFixedField k (SeparableClosure k)
          T.upperBase_le_lowerBase)
    (normUnitsMap T).toMonoidHom =
      MonoidHom.toAdditive.symm (normUnits T) := rfl

/-- The vertical abelianized restriction arrow as a continuous
homomorphism. -/
noncomputable def abelianizedRestrictionMap
    (T : LocalFixedFieldNormRestrictionSquare k) := by
  letI := T.lowerNormal
  letI := T.upperNormal
  letI := T.upperFinite
  letI := upperAbsoluteFinite T
  exact abstractFixedFieldAbelianizedRestrictionMap
    k (SeparableClosure k)
    T.lowerBase T.upperBase T.lowerTop T.upperTop
    T.lowerTop_le_lowerBase T.upperTop_le_upperBase
    T.upperBase_le_lowerBase T.upperTop_le_lowerTop

/-- Forgetting continuity recovers algebraic abelianized restriction. -/
theorem abelianizedRestrictionMap_toMonoidHom
    (T : LocalFixedFieldNormRestrictionSquare k) :
    (abelianizedRestrictionMap T).toMonoidHom =
      MonoidHom.toAdditive.symm (abelianizedRestriction T) := rfl

/-- Norm--restriction naturality as a commuting square of continuous
homomorphisms. -/
theorem norm_restriction_commutes_continuous
    (T : LocalFixedFieldNormRestrictionSquare k) :
    letI : FiniteDimensional k
        (abstractFixedField k (SeparableClosure k) T.lowerBase) :=
      abstractFixedField_finiteDimensional
        k (SeparableClosure k) T.lowerBase T.lowerAbsoluteFinite
    letI : FiniteDimensional k
        (abstractFixedField k (SeparableClosure k) T.upperBase) :=
      abstractFixedField_finiteDimensional
        k (SeparableClosure k) T.upperBase (upperAbsoluteFinite T)
    letI : FiniteDimensional k
        (abstractRelativeFixedField k (SeparableClosure k)
          T.upperBase_le_lowerBase) :=
      abstractFixedField_finiteDimensional
        k (SeparableClosure k) T.upperBase (upperAbsoluteFinite T)
    letI : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.lowerBase) :=
      finiteExtensionSpectralNormedField k
        (abstractFixedField k (SeparableClosure k) T.lowerBase)
    letI : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.upperBase) :=
      finiteExtensionSpectralNormedField k
        (abstractFixedField k (SeparableClosure k) T.upperBase)
    letI : NontriviallyNormedField
        (abstractRelativeFixedField k (SeparableClosure k)
          T.upperBase_le_lowerBase) :=
      finiteExtensionSpectralNormedField k
        (abstractRelativeFixedField k (SeparableClosure k)
          T.upperBase_le_lowerBase)
    (abelianizedRestrictionMap T).comp (upperNormResidueMap T) =
      (lowerNormResidueMap T).comp (normUnitsMap T) := by
  let : FiniteDimensional k
      (abstractFixedField k (SeparableClosure k) T.lowerBase) :=
    abstractFixedField_finiteDimensional
      k (SeparableClosure k) T.lowerBase T.lowerAbsoluteFinite
  let : FiniteDimensional k
      (abstractFixedField k (SeparableClosure k) T.upperBase) :=
    abstractFixedField_finiteDimensional
      k (SeparableClosure k) T.upperBase (upperAbsoluteFinite T)
  let : FiniteDimensional k
      (abstractRelativeFixedField k (SeparableClosure k)
        T.upperBase_le_lowerBase) :=
    abstractFixedField_finiteDimensional
      k (SeparableClosure k) T.upperBase (upperAbsoluteFinite T)
  let : NontriviallyNormedField
      (abstractFixedField k (SeparableClosure k) T.lowerBase) :=
    finiteExtensionSpectralNormedField k
      (abstractFixedField k (SeparableClosure k) T.lowerBase)
  let : NontriviallyNormedField
      (abstractFixedField k (SeparableClosure k) T.upperBase) :=
    finiteExtensionSpectralNormedField k
      (abstractFixedField k (SeparableClosure k) T.upperBase)
  let : NontriviallyNormedField
      (abstractRelativeFixedField k (SeparableClosure k)
        T.upperBase_le_lowerBase) :=
    finiteExtensionSpectralNormedField k
      (abstractRelativeFixedField k (SeparableClosure k)
        T.upperBase_le_lowerBase)
  apply ContinuousMonoidHom.ext
  intro x
  change Additive.toMul
      (abelianizedRestriction T
        (upperNormResidueSymbol T (Additive.ofMul x))) =
    Additive.toMul
      (lowerNormResidueSymbol T
        (normUnits T (Additive.ofMul x)))
  exact congrArg Additive.toMul
    (DFunLike.congr_fun (norm_restriction_commutes T)
      (Additive.ofMul x))

end LocalFixedFieldNormRestrictionSquare

/-! ## Continuous transfer--inclusion square -/

namespace LocalFixedFieldTransferTower

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

/-- The total horizontal norm-residue arrow as a continuous homomorphism. -/
noncomputable def baseNormResidueMap
    (T : LocalFixedFieldTransferTower k) :
    letI : FiniteDimensional k
        (abstractFixedField k (SeparableClosure k) T.base) :=
      abstractFixedField_finiteDimensional
        k (SeparableClosure k) T.base T.baseAbsoluteFinite
    letI : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.base) :=
      finiteExtensionSpectralNormedField k
        (abstractFixedField k (SeparableClosure k) T.base)
    (abstractFixedField k (SeparableClosure k) T.base)ˣ →ₜ*
      Abelianization
        Gal(abstractRelativeFixedField k (SeparableClosure k)
            (T.top_le_intermediate.trans T.intermediate_le_base) /
          abstractFixedField k (SeparableClosure k) T.base) := by
  letI := T.totalNormal
  letI := T.totalFinite
  letI := T.baseAbsoluteFinite
  exact abstractFixedFieldNormResidueMap
    k (SeparableClosure k)
    (localResidueDatum k) (localHenselianValuation k)
    (separableClosureUnits_isClassFormation k)
    T.base T.top
    (T.top_le_intermediate.trans T.intermediate_le_base)

/-- Forgetting continuity recovers the total algebraic norm-residue map. -/
theorem baseNormResidueMap_toMonoidHom
    (T : LocalFixedFieldTransferTower k) :
    letI : FiniteDimensional k
        (abstractFixedField k (SeparableClosure k) T.base) :=
      abstractFixedField_finiteDimensional
        k (SeparableClosure k) T.base T.baseAbsoluteFinite
    letI : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.base) :=
      finiteExtensionSpectralNormedField k
        (abstractFixedField k (SeparableClosure k) T.base)
    (baseNormResidueMap T).toMonoidHom =
      MonoidHom.toAdditive.symm (baseNormResidueSymbol T) := rfl

/-- The intermediate horizontal norm-residue arrow as a continuous
homomorphism. -/
noncomputable def intermediateNormResidueMap
    (T : LocalFixedFieldTransferTower k) :
    letI : FiniteDimensional k
        (abstractFixedField k (SeparableClosure k) T.intermediate) :=
      abstractFixedField_finiteDimensional
        k (SeparableClosure k) T.intermediate
          (intermediateAbsoluteFinite T)
    letI : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.intermediate) :=
      finiteExtensionSpectralNormedField k
        (abstractFixedField k (SeparableClosure k) T.intermediate)
    (abstractFixedField k (SeparableClosure k) T.intermediate)ˣ →ₜ*
      Abelianization
        Gal(abstractRelativeFixedField k (SeparableClosure k)
            T.top_le_intermediate /
          abstractFixedField k (SeparableClosure k) T.intermediate) := by
  letI := intermediateNormal T
  letI := intermediateFinite T
  letI := intermediateAbsoluteFinite T
  exact abstractFixedFieldNormResidueMap
    k (SeparableClosure k)
    (localResidueDatum k) (localHenselianValuation k)
    (separableClosureUnits_isClassFormation k)
    T.intermediate T.top T.top_le_intermediate

/-- Forgetting continuity recovers the intermediate norm-residue map. -/
theorem intermediateNormResidueMap_toMonoidHom
    (T : LocalFixedFieldTransferTower k) :
    letI : FiniteDimensional k
        (abstractFixedField k (SeparableClosure k) T.intermediate) :=
      abstractFixedField_finiteDimensional
        k (SeparableClosure k) T.intermediate
          (intermediateAbsoluteFinite T)
    letI : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.intermediate) :=
      finiteExtensionSpectralNormedField k
        (abstractFixedField k (SeparableClosure k) T.intermediate)
    (intermediateNormResidueMap T).toMonoidHom =
      MonoidHom.toAdditive.symm (intermediateNormResidueSymbol T) := rfl

/-- The vertical inclusion of fixed-field units as a continuous
homomorphism. -/
noncomputable def unitsInclusionMap
    (T : LocalFixedFieldTransferTower k) :
    letI : FiniteDimensional k
        (abstractFixedField k (SeparableClosure k) T.base) :=
      abstractFixedField_finiteDimensional
        k (SeparableClosure k) T.base T.baseAbsoluteFinite
    letI : FiniteDimensional k
        (abstractFixedField k (SeparableClosure k) T.intermediate) :=
      abstractFixedField_finiteDimensional
        k (SeparableClosure k) T.intermediate
          (intermediateAbsoluteFinite T)
    letI : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.base) :=
      finiteExtensionSpectralNormedField k
        (abstractFixedField k (SeparableClosure k) T.base)
    letI : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.intermediate) :=
      finiteExtensionSpectralNormedField k
        (abstractFixedField k (SeparableClosure k) T.intermediate)
    (abstractFixedField k (SeparableClosure k) T.base)ˣ →ₜ*
      (abstractFixedField k (SeparableClosure k) T.intermediate)ˣ := by
  letI := T.baseAbsoluteFinite
  letI := intermediateAbsoluteFinite T
  exact abstractFixedFieldUnitsInclusionMap
    k (SeparableClosure k)
    T.base T.intermediate T.intermediate_le_base

/-- Forgetting continuity recovers algebraic inclusion of fixed-field units. -/
theorem unitsInclusionMap_toMonoidHom
    (T : LocalFixedFieldTransferTower k) :
    letI : FiniteDimensional k
        (abstractFixedField k (SeparableClosure k) T.base) :=
      abstractFixedField_finiteDimensional
        k (SeparableClosure k) T.base T.baseAbsoluteFinite
    letI : FiniteDimensional k
        (abstractFixedField k (SeparableClosure k) T.intermediate) :=
      abstractFixedField_finiteDimensional
        k (SeparableClosure k) T.intermediate
          (intermediateAbsoluteFinite T)
    letI : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.base) :=
      finiteExtensionSpectralNormedField k
        (abstractFixedField k (SeparableClosure k) T.base)
    letI : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.intermediate) :=
      finiteExtensionSpectralNormedField k
        (abstractFixedField k (SeparableClosure k) T.intermediate)
    (unitsInclusionMap T).toMonoidHom =
      MonoidHom.toAdditive.symm (unitsInclusion T) := rfl

/-- The vertical abelianized transfer arrow as a continuous homomorphism. -/
noncomputable def abelianizedTransferMap
    (T : LocalFixedFieldTransferTower k) := by
  letI := T.totalNormal
  letI := T.totalFinite
  letI := T.baseAbsoluteFinite
  exact abstractFixedFieldAbelianizedTransferMap
    k (SeparableClosure k)
    T.base T.intermediate T.top
    T.top_le_intermediate T.intermediate_le_base

/-- Forgetting continuity recovers algebraic abelianized transfer. -/
theorem abelianizedTransferMap_toMonoidHom
    (T : LocalFixedFieldTransferTower k) :
    (abelianizedTransferMap T).toMonoidHom =
      MonoidHom.toAdditive.symm (abelianizedTransfer T) := rfl

/-- Transfer--inclusion naturality as a commuting square of continuous
homomorphisms. -/
theorem transfer_inclusion_commutes_continuous
    (T : LocalFixedFieldTransferTower k) :
    letI : FiniteDimensional k
        (abstractFixedField k (SeparableClosure k) T.base) :=
      abstractFixedField_finiteDimensional
        k (SeparableClosure k) T.base T.baseAbsoluteFinite
    letI : FiniteDimensional k
        (abstractFixedField k (SeparableClosure k) T.intermediate) :=
      abstractFixedField_finiteDimensional
        k (SeparableClosure k) T.intermediate
          (intermediateAbsoluteFinite T)
    letI : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.base) :=
      finiteExtensionSpectralNormedField k
        (abstractFixedField k (SeparableClosure k) T.base)
    letI : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.intermediate) :=
      finiteExtensionSpectralNormedField k
        (abstractFixedField k (SeparableClosure k) T.intermediate)
    (abelianizedTransferMap T).comp (baseNormResidueMap T) =
      (intermediateNormResidueMap T).comp (unitsInclusionMap T) := by
  let : FiniteDimensional k
      (abstractFixedField k (SeparableClosure k) T.base) :=
    abstractFixedField_finiteDimensional
      k (SeparableClosure k) T.base T.baseAbsoluteFinite
  let : FiniteDimensional k
      (abstractFixedField k (SeparableClosure k) T.intermediate) :=
    abstractFixedField_finiteDimensional
      k (SeparableClosure k) T.intermediate
        (intermediateAbsoluteFinite T)
  let : NontriviallyNormedField
      (abstractFixedField k (SeparableClosure k) T.base) :=
    finiteExtensionSpectralNormedField k
      (abstractFixedField k (SeparableClosure k) T.base)
  let : NontriviallyNormedField
      (abstractFixedField k (SeparableClosure k) T.intermediate) :=
    finiteExtensionSpectralNormedField k
      (abstractFixedField k (SeparableClosure k) T.intermediate)
  apply ContinuousMonoidHom.ext
  intro x
  change Additive.toMul
      (abelianizedTransfer T
        (baseNormResidueSymbol T (Additive.ofMul x))) =
    Additive.toMul
      (intermediateNormResidueSymbol T
        (unitsInclusion T (Additive.ofMul x)))
  exact congrArg Additive.toMul
    (DFunLike.congr_fun (transfer_inclusion_commutes T)
      (Additive.ofMul x))

end LocalFixedFieldTransferTower

end LocalClassFieldTheory
