/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Topology.Algebra.Module.FiniteDimension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuedTopology
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Main

/-! # Finite Extension Class Field Axiom -/
namespace LocalClassFieldTheory

open LocalFieldTheory

open ValuationTheory

open CyclicCohomology

/-!
# Finite local reciprocity

The local class-field-axiom theorem on finite extensions of a local field.

Mathlib's local-field predicate is topology-first, while the local class-field-axiom theorem also
needs a compatible local-field structure on the finite extension.  This file
constructs that structure from the spectral norm.  In particular, the target
valuation ring is proved integral over the base valuation ring; no local-field
structure on the target is assumed.
-/

noncomputable section

open scoped NNReal ValuativeRel

/-- Finite-cardinality data for the two actual unit Tate groups.  Bundling the
`H⁰` finiteness proof keeps `Nat.card` honest when the local-field
structure on the extension is constructed inside a theorem. -/
structure UnitsTateCardinalityData
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] where
  /-- Finiteness of the degree-zero Tate cohomology group of the unit representation. -/
  finiteH0 : Finite (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0)
  /-- The degree-zero unit Tate group has cardinality equal to the extension degree. -/
  cardH0 :
    letI := finiteH0
    Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) = Module.finrank K L
  /-- The degree-minus-one unit Tate group is trivial at the level of cardinality. -/
  cardHminusOne : Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) = 1

/-- The local class-field-axiom theorem for an arbitrary finite Galois extension of a
nonarchimedean local field.  All local-field data on the extension is
constructed from the spectral norm. -/
theorem finiteExtensionUnits_tate_card_of_generator
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (g : Gal(L/K))
    (hg : ∀ sigma : Gal(L/K), sigma ∈ Subgroup.zpowers g) :
    UnitsTateCardinalityData K L := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  let : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let : (Valued.v : Valuation K (ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField
      (L := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)
  let : NontriviallyNormedField L :=
    spectralNorm.nontriviallyNormedField K L
  let : NormedSpace K L := spectralNorm.normedSpace K L
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
  let : Algebra.IsIntegral
      (ValuativeRel.valuation K).valuationSubring
      (ValuativeRel.valuation L).valuationSubring := by
    change Algebra.IsIntegral 𝒪[K] 𝒪[L]
    refine ⟨?_⟩
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
      rwa [Polynomial.aeval_map_algebraMap K (y : L) p] at hmaproot
  let hIntegralClosure : IsIntegralClosure
      (ValuativeRel.valuation L).valuationSubring
      (ValuativeRel.valuation K).valuationSubring L :=
    DiscreteValuationField.Valuation.valuationSubring_isIntegralClosure_of_isIntegral
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)
  let : IsIntegralClosure 𝒪[L] 𝒪[K] L := by
    change IsIntegralClosure
      (ValuativeRel.valuation L).valuationSubring
      (ValuativeRel.valuation K).valuationSubring L
    exact hIntegralClosure
  let : Module.Finite 𝒪[K] 𝒪[L] :=
    integerRing_moduleFinite_of_isIntegralClosure K L
  let : Finite (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) :=
    localFieldUnitsTateH0FiniteOfGenerator K L g hg
  have hcard := localFieldUnits_tate_card_of_generator K L g hg
  exact
    { finiteH0 := inferInstance
      cardH0 := hcard.1
      cardHminusOne := hcard.2 }

/-- Tower form of the local class-field-axiom theorem.  It is enough that the lower field of the
cyclic extension be finite over a nonarchimedean local field; its local-field
structure is again supplied by the spectral norm. -/
theorem finiteTowerUnits_tate_card_of_generator
    (k K L : Type) [Field k] [Field K] [Field L]
    [Algebra k K] [FiniteDimensional k K]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (g : Gal(L/K))
    (hg : ∀ sigma : Gal(L/K), sigma ∈ Subgroup.zpowers g) :
    UnitsTateCardinalityData K L := by
  let : UniformSpace k := IsTopologicalAddGroup.rightUniformSpace k
  let : IsUniformAddGroup k := isUniformAddGroup_of_addCommGroup
  let : (Valued.v : Valuation k (ValuativeRel.ValueGroupWithZero k)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := k) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField k :=
    Valued.toNontriviallyNormedField
      (L := k) (Γ₀ := ValuativeRel.ValueGroupWithZero k)
  let : NontriviallyNormedField K :=
    spectralNorm.nontriviallyNormedField k K
  let : NormedSpace k K := spectralNorm.normedSpace k K
  let : CompleteSpace K := spectralNorm.completeSpace k K
  let : LocallyCompactSpace K :=
    LocallyCompactSpace.of_finiteDimensional_of_complete k K
  let : IsUltrametricDist K :=
    ⟨fun x y z => by
      change ‖x - z‖ ≤ max ‖x - y‖ ‖y - z‖
      rw [← sub_add_sub_cancel x y z]
      exact isNonarchimedean_spectralNorm
        (K := k) (L := K) (x - y) (y - z)⟩
  let : Valued K ℝ≥0 := NormedField.toValued
  let vK : Valuation K ℝ≥0 := Valued.v
  let : vK.IsNontrivial :=
    (inferInstance : (NormedField.valuation (K := K)).IsNontrivial)
  let : ValuativeRel K := ValuativeRel.ofValuation vK
  let : vK.Compatible := Valuation.Compatible.ofValuation vK
  let : ValuativeRel.IsNontrivial K :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vK).2 inferInstance
  let : IsValuativeTopology K :=
    isValuativeTopology_of_valued_ofValuation K ℝ≥0
  let : IsNonarchimedeanLocalField K :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  exact finiteExtensionUnits_tate_card_of_generator K L g hg

end
end LocalClassFieldTheory
