/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Main
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteExtensionClassFieldAxiom
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnitTopology
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.OpenSubgroup
/-!
# Topological finite local reciprocity

This module upgrades the algebraic finite local reciprocity isomorphism to a
homeomorphic group isomorphism.  The key input is that the norm subgroup of a
finite Galois extension is open.  Consequently its quotient is discrete, as
is the topological abelianization of the finite Krull Galois group.
-/

@[expose] public section

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  valuationSubring_isIntegralClosure_of_isIntegral →
    valuationSubring_isIntegralClosure_of_isIntegral


noncomputable
section

namespace LocalClassFieldTheory

open scoped NNReal ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- The norm quotient inherits its topology from the quotient of the base-field unit group. -/
noncomputable local instance normQuotientTopologicalSpace
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [TopologicalSpace K] :
    TopologicalSpace (NormQuotient K L) := by
  change TopologicalSpace (Kˣ ⧸ localNormSubgroup K L)
  infer_instance

section NormSubgroupTopology

universe u

/-- The norm map restricted to valuation-ring units upstairs. -/
private def integerUnitNormMap
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [ValuativeRel L] : 𝒪[L]ˣ →* Kˣ :=
  (LocalFieldTheory.normUnits K L).comp (integerUnitsToFieldUnits L)

/-- The image of valuation-ring units under the field norm. -/
private def integerUnitNormSubgroup
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [ValuativeRel L] : Subgroup Kˣ :=
  MonoidHom.range (integerUnitNormMap K L)

private theorem integerUnitNormSubgroup_isCompact
    (K L : Type u) [NontriviallyNormedField K] [NormedField L]
    [NormedAlgebra K L] [FiniteDimensional K L] [CompleteSpace K]
    [ValuativeRel L] [CompactSpace 𝒪[L]] :
    IsCompact (integerUnitNormSubgroup K L : Set Kˣ) := by
  have hcontinuous : Continuous (integerUnitNormMap K L) :=
    (normUnits_continuous_of_finiteDimensional K L).comp
      (integerUnitsToFieldUnits_continuous L)
  have hcompact : IsCompact (Set.univ : Set 𝒪[L]ˣ) := isCompact_univ
  have himage := hcompact.image hcontinuous
  change IsCompact (Set.range (integerUnitNormMap K L))
  simpa only [Set.image_univ] using himage

private theorem integerUnitNormSubgroup_eq_localNormSubgroup_inf_baseUnits
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    integerUnitNormSubgroup K L =
      localNormSubgroup K L ⊓ localBaseUnitSubgroup K := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨⟨integerUnitsToFieldUnits L a, rfl⟩, ?_⟩
    refine ⟨normIntegerUnits K L a, ?_⟩
    apply Units.ext
    rfl
  · rintro ⟨⟨y, hy⟩, ⟨a, ha⟩⟩
    have hxv : v K (Additive.ofMul x) = 0 := by
      rw [← ha]
      exact v_integerUnitsToFieldUnits K a
    have hnorm := v_normUnits_eq_residue_finrank_mul_of_isSeparable K L y
    change v K (Additive.ofMul (LocalFieldTheory.normUnits K L y)) =
      (@Module.finrank 𝓀[K] 𝓀[L] _ _
        (IsLocalRing.ResidueField.instModule (R := 𝒪[K]) (S := 𝒪[L])) : Int) *
        v L (Additive.ofMul y) at hnorm
    have hproduct :
        (@Module.finrank 𝓀[K] 𝓀[L] _ _
          (IsLocalRing.ResidueField.instModule (R := 𝒪[K]) (S := 𝒪[L])) : Int) *
          v L (Additive.ofMul y) = 0 := by
      rw [← hnorm, hy]
      exact hxv
    have hfinrank :
        (@Module.finrank 𝓀[K] 𝓀[L] _ _
          (IsLocalRing.ResidueField.instModule (R := 𝒪[K]) (S := 𝒪[L])) : Int) ≠ 0 := by
      have hnat :
          @Module.finrank 𝓀[K] 𝓀[L] _ _
            (IsLocalRing.ResidueField.instModule (R := 𝒪[K]) (S := 𝒪[L])) ≠ 0 :=
        Nat.ne_of_gt Module.finrank_pos
      exact_mod_cast hnat
    have hyv : v L (Additive.ofMul y) = 0 :=
      (mul_eq_zero.mp hproduct).resolve_left hfinrank
    have hyvaluation : valuationMap L (Additive.ofMul y) = 0 := by
      rw [valuationMap_apply]
      exact hyv
    obtain ⟨b, hb⟩ :=
      (integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero L y).2 hyvaluation
    refine ⟨b, ?_⟩
    change LocalFieldTheory.normUnits K L (integerUnitsToFieldUnits L b) = x
    rw [hb, hy]

private theorem localNormSubgroup_isOpen_of_compatibleLocalField
    (K L : Type)
    [NontriviallyNormedField K] [NormedField L] [NormedAlgebra K L]
    [CompleteSpace K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [IsNonarchimedeanLocalField L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    IsOpen (localNormSubgroup K L : Set Kˣ) := by
  have hintersection :
      integerUnitNormSubgroup K L =
        localNormSubgroup K L ⊓ localBaseUnitSubgroup K :=
    integerUnitNormSubgroup_eq_localNormSubgroup_inf_baseUnits K L
  have hcompact : IsCompact (integerUnitNormSubgroup K L : Set Kˣ) :=
    integerUnitNormSubgroup_isCompact K L
  have hclosed : IsClosed (integerUnitNormSubgroup K L : Set Kˣ) :=
    hcompact.isClosed
  let : Finite (Gal(L/K)) := by
    apply Nat.finite_of_card_ne_zero
    rw [IsGalois.card_aut_eq_finrank K L]
    exact Nat.ne_of_gt Module.finrank_pos
  let : Finite (Abelianization (Gal(L/K))) :=
    Finite.of_surjective Abelianization.of QuotientGroup.mk_surjective
  let : Finite (NormQuotient K L) :=
    Finite.of_equiv
      (Abelianization (Gal(L/K)))
      (abelianizationEquivNormQuotient K L).toEquiv
  let : Finite (Kˣ ⧸ localNormSubgroup K L) := by
    change Finite (NormQuotient K L)
    infer_instance
  let : (localNormSubgroup K L).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  let : ((localNormSubgroup K L).subgroupOf
      (localBaseUnitSubgroup K)).FiniteIndex := inferInstance
  have hrelativeClosed :
      IsClosed
        ((localNormSubgroup K L).subgroupOf (localBaseUnitSubgroup K) :
          Set (localBaseUnitSubgroup K)) := by
    have hpreimage :
        IsClosed ((fun z : localBaseUnitSubgroup K => (z : Kˣ)) ⁻¹'
          (integerUnitNormSubgroup K L : Set Kˣ)) :=
      hclosed.preimage continuous_subtype_val
    rw [show
        ((localNormSubgroup K L).subgroupOf (localBaseUnitSubgroup K) :
            Set (localBaseUnitSubgroup K)) =
          (fun z : localBaseUnitSubgroup K => (z : Kˣ)) ⁻¹'
            (integerUnitNormSubgroup K L : Set Kˣ) by
      ext z
      change (z : Kˣ) ∈ localNormSubgroup K L ↔
        (z : Kˣ) ∈ integerUnitNormSubgroup K L
      rw [hintersection]
      constructor
      · intro hz
        exact ⟨hz, z.property⟩
      · exact fun hz => hz.1]
    exact hpreimage
  have hrelativeOpen :
      IsOpen
        ((localNormSubgroup K L).subgroupOf (localBaseUnitSubgroup K) :
          Set (localBaseUnitSubgroup K)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ hrelativeClosed
  have himageOpen :
      IsOpen (Subtype.val ''
        ((localNormSubgroup K L).subgroupOf (localBaseUnitSubgroup K) :
          Set (localBaseUnitSubgroup K))) :=
    (localBaseUnitSubgroup_isOpen K).isOpenMap_subtype_val _ hrelativeOpen
  have himage :
      Subtype.val ''
          ((localNormSubgroup K L).subgroupOf (localBaseUnitSubgroup K) :
            Set (localBaseUnitSubgroup K)) =
        (integerUnitNormSubgroup K L : Set Kˣ) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hintersection]
      exact ⟨hz, z.property⟩
    · intro hx
      have hx' := hx
      rw [hintersection] at hx'
      exact ⟨⟨x, hx'.2⟩, hx'.1, rfl⟩
  rw [himage] at himageOpen
  apply Subgroup.isOpen_mono
    (H₁ := integerUnitNormSubgroup K L)
    (H₂ := localNormSubgroup K L) ?_ himageOpen
  intro x hx
  rw [hintersection] at hx
  exact hx.1

/-- The norm subgroup of a finite Galois extension of a nonarchimedean local
field is open in the native topology of the base-field unit group. -/
theorem localNormSubgroup_isOpen
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    IsOpen (localNormSubgroup K L : Set Kˣ) := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  let : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let : (Valued.v : Valuation K
      (ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField
      (L := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)
  let : NontriviallyNormedField L :=
    spectralNorm.nontriviallyNormedField K L
  let : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  let : CompleteSpace L := spectralNorm.completeSpace K L
  let : LocallyCompactSpace L :=
    LocallyCompactSpace.of_finiteDimensional_of_complete K L
  let : IsUltrametricDist L :=
    ⟨fun x y z => by
      change ‖x - z‖ ≤ max ‖x - y‖ ‖y - z‖
      rw [← sub_add_sub_cancel x y z]
      exact isNonarchimedean_spectralNorm
        (K := K) (L := L) (x - y) (y - z)⟩
  let : Valued L ℝ≥0 := NormedField.toValued
  let vL : Valuation L ℝ≥0 := Valued.v
  let : vL.IsNontrivial :=
    (inferInstance : (NormedField.valuation (K := L)).IsNontrivial)
  let : ValuativeRel L := ValuativeRel.ofValuation vL
  let : vL.Compatible := Valuation.Compatible.ofValuation vL
  let : ValuativeRel.IsNontrivial L :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vL).2 inferInstance
  let : IsValuativeTopology L :=
    isValuativeTopology_of_valued_ofValuation L ℝ≥0
  let : IsNonarchimedeanLocalField L :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let : (ValuativeRel.valuation K).HasExtension
      (ValuativeRel.valuation L) := by
    apply Valuation.HasExtension.ofComapInteger
    ext x
    change ValuativeRel.valuation L (algebraMap K L x) ≤ 1 ↔
      ValuativeRel.valuation K x ≤ 1
    rw [← (ValuativeRel.valuation L).vle_one_iff, vL.vle_one_iff]
    change spectralNorm K L (algebraMap K L x) ≤ 1 ↔
      ValuativeRel.valuation K x ≤ 1
    rw [spectralNorm_extends]
    exact Valued.toNormedField.norm_le_one_iff
  let : Algebra.IsIntegral 𝒪[K] 𝒪[L] := ⟨by
    intro y
    apply IsIntegral.tower_bot
      (R := 𝒪[K]) (A := 𝒪[L]) (B := L)
      (Subring.subtype_injective (ValuativeRel.valuation L).integer)
    have hyv : vL (y : L) ≤ 1 := by
      apply (vL.vle_one_iff).1
      apply ((ValuativeRel.valuation L).vle_one_iff).2
      exact y.property
    have hynorm : ‖(y : L)‖ ≤ 1 := by
      have hynormNN : ‖(y : L)‖₊ ≤ 1 := by
        simpa [vL, NormedField.valuation_apply] using hyv
      exact_mod_cast hynormNN
    change spectralNorm K L (y : L) ≤ 1 at hynorm
    have hcoeffNorm :
        ∀ n : ℕ, ‖(minpoly K (y : L)).coeff n‖ ≤ 1 :=
      (spectralValue_le_one_iff
        (minpoly.monic (Algebra.IsIntegral.isIntegral (y : L)))).1
        (by simpa [spectralNorm] using hynorm)
    have hcoeff :
        (↑(minpoly K (y : L)).coeffs : Set K) ⊆
          (ValuativeRel.valuation K).integer := by
      intro c hc
      obtain ⟨n, _hn, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
      exact ((ValuativeRel.valuation K).mem_integer_iff _).2
        (Valued.toNormedField.norm_le_one_iff.mp (hcoeffNorm n))
    let p : Polynomial 𝒪[K] :=
      (minpoly K (y : L)).toSubring
        (ValuativeRel.valuation K).integer hcoeff
    refine ⟨p, ?_, ?_⟩
    · exact (Polynomial.monic_toSubring
        (minpoly K (y : L)) (ValuativeRel.valuation K).integer hcoeff).2
          (minpoly.monic (Algebra.IsIntegral.isIntegral (y : L)))
    · have hmaproot :
          Polynomial.aeval (y : L)
            (p.map (algebraMap 𝒪[K] K)) = 0 := by
        dsimp only [p]
        rw [show algebraMap 𝒪[K] K =
          (ValuativeRel.valuation K).integer.subtype from rfl,
          Polynomial.map_toSubring]
        exact minpoly.aeval K (y : L)
      rwa [Polynomial.aeval_map_algebraMap K (y : L) p] at hmaproot⟩
  let : Algebra.IsIntegral
      (ValuativeRel.valuation K).valuationSubring
      (ValuativeRel.valuation L).valuationSubring := by
    change Algebra.IsIntegral 𝒪[K] 𝒪[L]
    infer_instance
  let hIntegralClosure : IsIntegralClosure
      (ValuativeRel.valuation L).valuationSubring
      (ValuativeRel.valuation K).valuationSubring L :=
    valuationSubring_isIntegralClosure_of_isIntegral
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)
  let : IsIntegralClosure 𝒪[L] 𝒪[K] L := by
    change IsIntegralClosure
      (ValuativeRel.valuation L).valuationSubring
      (ValuativeRel.valuation K).valuationSubring L
    exact hIntegralClosure
  exact localNormSubgroup_isOpen_of_compatibleLocalField K L

/-- The native quotient topology on the finite norm quotient is discrete. -/
theorem normQuotient_discrete
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    DiscreteTopology (NormQuotient K L) := by
  let N := localNormSubgroup K L
  change DiscreteTopology (Kˣ ⧸ N)
  apply QuotientGroup.discreteTopology
  simpa only [N] using localNormSubgroup_isOpen K L

end NormSubgroupTopology

section TopologicalReciprocity

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsGalois K L]

private theorem commutator_topologicalClosure_eq
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DiscreteTopology G] :
    Subgroup.topologicalClosure (commutator G) = commutator G := by
  apply le_antisymm
  · exact Subgroup.topologicalClosure_minimal _ le_rfl (isClosed_discrete _)
  · exact Subgroup.le_topologicalClosure _

/-- For a finite-dimensional Galois extension, algebraic and topological
abelianization agree as multiplicative groups. -/
noncomputable def topologicalAbelianizationFiniteEquiv :
    Abelianization (Gal(L/K)) ≃* TopologicalAbelianization (Gal(L/K)) := by
  let h : Subgroup.topologicalClosure (commutator (Gal(L/K))) =
      commutator (Gal(L/K)) :=
    commutator_topologicalClosure_eq (Gal(L/K))
  exact QuotientGroup.quotientMulEquivOfEq h.symm

/-- Finite local reciprocity as a homeomorphic group isomorphism from the
norm quotient to the topological abelianization of the Krull Galois group. -/
noncomputable def localReciprocityEquiv :
    NormQuotient K L ≃ₜ* TopologicalAbelianization (Gal(L/K)) := by
  letI : DiscreteTopology (NormQuotient K L) := normQuotient_discrete K L
  letI : DiscreteTopology (TopologicalAbelianization (Gal(L/K))) :=
    QuotientGroup.discreteTopology (isOpen_discrete _)
  let e : NormQuotient K L ≃* TopologicalAbelianization (Gal(L/K)) :=
    (abelianizationEquivNormQuotient K L).symm.trans
      (topologicalAbelianizationFiniteEquiv K L)
  exact
    { e with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- The underlying multiplicative equivalence is the algebraic reciprocity
isomorphism followed by the finite abelianization comparison. -/
theorem localReciprocityEquiv_toMulEquiv :
    (localReciprocityEquiv K L).toMulEquiv =
      (abelianizationEquivNormQuotient K L).symm.trans
        (topologicalAbelianizationFiniteEquiv K L) := by
  rfl

/-- The quotient map to the norm quotient, bundled as a continuous
homomorphism for the native quotient topology. -/
noncomputable def normClassContinuous :
    Kˣ →ₜ* NormQuotient K L :=
  { normClass K L with
    continuous_toFun := QuotientGroup.continuous_mk }

/-- The continuous finite local Artin map. -/
noncomputable def localArtinMap :
    Kˣ →ₜ* TopologicalAbelianization (Gal(L/K)) :=
  (ContinuousMonoidHom.toContinuousMonoidHom (localReciprocityEquiv K L)).comp
    (normClassContinuous K L)

/-- Forgetting the topology and comparing finite abelianizations recovers the
algebraic local Artin homomorphism. -/
theorem localArtinMap_toMonoidHom :
    (topologicalAbelianizationFiniteEquiv K L).symm.toMonoidHom.comp
        (localArtinMap K L).toMonoidHom =
      localArtinMonoidHom K L := by
  ext x
  change
    (topologicalAbelianizationFiniteEquiv K L).symm
        (localReciprocityEquiv K L (normClass K L x)) =
      (abelianizationEquivNormQuotient K L).symm
        (normClass K L x)
  rw [show localReciprocityEquiv K L (normClass K L x) =
      topologicalAbelianizationFiniteEquiv K L
        ((abelianizationEquivNormQuotient K L).symm
          (normClass K L x)) by
    change (localReciprocityEquiv K L).toMulEquiv
        (normClass K L x) = _
    rw [localReciprocityEquiv_toMulEquiv]
    rfl]
  exact (topologicalAbelianizationFiniteEquiv K L).symm_apply_apply _

/-- The continuous local Artin map is canonical: after forgetting topology,
it agrees with the reciprocity symbol computed from any realization of the
extension in the fixed separable closure. -/
theorem localArtinMap_embedding_independent
    (i : L →ₐ[K] SeparableClosure K) :
    (topologicalAbelianizationFiniteEquiv K L).symm.toMonoidHom.comp
        (localArtinMap K L).toMonoidHom =
      concreteNormResidueSymbolOfEmbedding K L i
        (localResidueDatum K)
        (localHenselianValuation K)
        (separableClosureUnits_isClassFormation K) := by
  rw [localArtinMap_toMonoidHom,
    localArtinMonoidHom_eq_of_embedding K L i]

/-- The continuous finite local Artin map is surjective. -/
theorem localArtinMap_surjective :
    Function.Surjective (localArtinMap K L) :=
  (localReciprocityEquiv K L).surjective.comp
    (QuotientGroup.mk'_surjective (localNormSubgroup K L))

/-- The kernel of the continuous finite local Artin map is the norm
subgroup. -/
theorem localArtinMap_ker :
    (localArtinMap K L).toMonoidHom.ker = localNormSubgroup K L := by
  ext x
  rw [MonoidHom.mem_ker]
  change
    localReciprocityEquiv K L (normClass K L x) = 1 ↔
      x ∈ localNormSubgroup K L
  rw [← map_one (localReciprocityEquiv K L)]
  rw [(localReciprocityEquiv K L).apply_eq_iff_eq]
  exact normClass_eq_one_iff_mem K L x

/-- The canonical first-isomorphism equivalence induced by the continuous
local Artin map. -/
noncomputable def localArtinMapQuotientKerEquiv :
    Kˣ ⧸ (localArtinMap K L).toMonoidHom.ker ≃*
      TopologicalAbelianization (Gal(L/K)) :=
  QuotientGroup.quotientKerEquivOfSurjective
    (localArtinMap K L).toMonoidHom (localArtinMap_surjective K L)

/-- The first-isomorphism equivalence sends the class of a field unit to its
image under the local Artin map. -/
theorem localArtinMap_quotientKerEquiv_mk (x : Kˣ) :
    localArtinMapQuotientKerEquiv K L (QuotientGroup.mk x) =
      localArtinMap K L x := by
  rfl

end TopologicalReciprocity

end LocalClassFieldTheory
