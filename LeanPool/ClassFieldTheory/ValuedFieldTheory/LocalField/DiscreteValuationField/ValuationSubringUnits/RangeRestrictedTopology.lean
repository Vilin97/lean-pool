/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CompleteRangeRestriction
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.ValuedAdicComplete
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.NormedValued
/-!
# Topology of range-restricted complete discretely valued fields

This file equips the multiplicative-range valuation with its valued and normed
field structures and transports adic completeness, compactness, properness,
and completeness.
-/

noncomputable section

universe u v

open Filter WithZero
open scoped NNReal Valued Filter WithZero

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- The canonical `Valued` structure attached to the range-restricted complete
DVF valuation. -/
@[implicit_reducible]
noncomputable def mrangeRestrictValued
    (F : CompleteDVF.{u, v} K) :
    Valued K (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
  Valued.mk' (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F)

@[instance_reducible]
private noncomputable def mrangeRestrictValued_rankOne
    (F : CompleteDVF.{u, v} K) :
    (@Valued.v K _
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) _
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)).RankOne := by
  change
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).RankOne
  exact
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_rankOne F

/-- The rank-one normalized complete-DVF valuation supplies the normed-field
structure expected by mathlib's finite-dimensional closed-subspace theorem. -/
@[implicit_reducible]
noncomputable def mrangeRestrict_nontriviallyNormedField
    (F : CompleteDVF.{u, v} K) :
    NontriviallyNormedField K :=
  Valued.toNontriviallyNormedField
    (L := K)
    (Γ₀ := MonoidHom.mrange F.valuation.toMonoidWithZeroHom)
    (val := LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    (hv := mrangeRestrictValued_rankOne F)

/-- Powers of a uniformizer are cofinal among neighborhoods of zero for the
range-restricted valuation topology. -/
theorem mrangeRestrict_exists_uniformizer_pow_lt_unit
    (F : CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (gamma :
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom)ˣ) :
    ∃ N : ℕ,
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F) (((π ^ N : F.valuationSubring) : K)) < gamma := by
  let Γ : Type v :=
    MonoidHom.mrange F.valuation.toMonoidWithZeroHom
  have hπ_ne :
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F) (π : K) ≠ (0 : Γ) := by
    intro hzero
    exact hπ.val_ne_zero (by
      simpa [Γ, CompleteDVF.mrangeRestrict] using
        congrArg (fun z : Γ => (z : F.ValueGroup)) hzero)
  let delta : Γˣ := Units.mk0 ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F) (π : K)) hπ_ne
  have hdelta_lt_one : delta < (1 : Γˣ) := by
    rw [← Units.val_lt_val]
    change (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F) (π : K) < (1 : Γ)
    rw [← Subtype.coe_lt_coe]
    simpa [Γ, CompleteDVF.mrangeRestrict] using hπ.val_lt_one
  have : IsCyclic Γˣ := by
    simpa [Γ] using (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_units_isCyclic F)
  have : MulArchimedean Γˣ :=
    WithZeroValuation.isCyclic_mulArchimedean Γˣ
  have hdelta_inv : (1 : Γˣ) < delta⁻¹ :=
    one_lt_inv'.2 hdelta_lt_one
  obtain ⟨N, hN⟩ := exists_lt_pow hdelta_inv gamma⁻¹
  refine ⟨N, ?_⟩
  have hpow_lt : delta ^ N < gamma := by
    have hN' : gamma⁻¹ < (delta ^ N)⁻¹ := by
      simpa [inv_pow] using hN
    exact lt_of_inv_lt_inv hN'
  simpa [delta, Γ, _root_.Valuation.map_pow] using
    (show (((LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F) (π : K)) ^ N : Γ) < gamma from
      (Units.val_lt_val.2 hpow_lt))

/-- A closed subfield for the range-restricted valuation topology contains any
valuation-ring element that is approximated modulo all powers of the maximal
ideal by elements of that subfield. -/
theorem mem_subfield_of_mrangeRestrict_isClosed_of_forall_valuationSubring_smodEq
    (F : CompleteDVF.{u, v} K) (E : Subfield K)
    (hEclosed :
      letI :
          Valued K (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
      IsClosed (E : Set K))
    (b : F.valuationSubring)
    (happrox :
      ∀ N : ℕ,
        ∃ z : E,
          ∃ hz : (z : K) ∈ F.valuation.valuationSubring,
            (⟨(z : K), hz⟩ : F.valuationSubring) ≡ b
              [SMOD
                ((F.maximalIdeal ^ N) •
                  (⊤ : Submodule F.valuationSubring F.valuationSubring))]) :
    (b : K) ∈ E := by
  let :
      Valued K (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  have hbClosure : (b : K) ∈ closure (E : Set K) := by
    rw [mem_closure_iff_nhds]
    intro U hU
    rw [Valued.mem_nhds] at hU
    rcases hU with ⟨gamma, hgamma⟩
    rcases F.exists_uniformizer with ⟨π, hπ⟩
    let gamma' :
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom)ˣ :=
      Units.map
        MonoidWithZeroHom.ValueGroup₀.embedding.toMonoidHom gamma
    obtain ⟨N, hN⟩ :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_exists_uniformizer_pow_lt_unit F)
        hπ gamma'
    obtain ⟨z, hz, hzcongr⟩ := happrox N
    let zInt : F.valuationSubring := ⟨(z : K), hz⟩
    have hdiff_mem :
        zInt - b ∈ F.maximalIdeal ^ N := by
      have hsub := SModEq.sub_mem.mp hzcongr
      simpa [smul_eq_mul, Ideal.mul_top] using hsub
    have hdiff_le :
        F.valuation ((zInt - b : F.valuationSubring) : K) ≤
          F.valuation (((π ^ N : F.valuationSubring) : K)) := by
      exact
        (ValuationTheory.DiscreteValuationField.Valuation.mem_maximalIdeal_pow_iff_valuation_le_uniformizer_pow
          (val := F.valuation) hπ N (x := zInt - b)).1 hdiff_mem
    refine ⟨(z : K), ?_, z.2⟩
    apply hgamma
    have hdiff_le' :
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F) ((z : K) - (b : K)) ≤
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F) (((π ^ N : F.valuationSubring) : K)) := by
      rw [← Subtype.coe_le_coe]
      simpa [zInt] using hdiff_le
    change
      (Valued.v :
        _root_.Valuation K
          (MonoidHom.mrange
            F.valuation.toMonoidWithZeroHom)).restrict
          ((z : K) - (b : K)) < gamma
    rw [_root_.Valuation.restrict_lt_iff_lt_embedding]
    rw [← Subtype.coe_lt_coe]
    have hlt := lt_of_le_of_lt hdiff_le' hN
    rw [← Subtype.coe_lt_coe] at hlt
    change
      F.valuation ((z : K) - (b : K)) <
        ((MonoidWithZeroHom.ValueGroup₀.embedding
            (f := MonoidWithZeroHom.ofClass
              (Valued.v :
                _root_.Valuation K
                  (MonoidHom.mrange
                    F.valuation.toMonoidWithZeroHom)))
            (↑gamma) :
          MonoidHom.mrange F.valuation.toMonoidWithZeroHom) : F.ValueGroup)
    simpa [gamma'] using hlt
  simpa [hEclosed.closure_eq] using hbClosure

/-- The complete-DVF package obtained by replacing the ambient value group by
the actual multiplicative range of the chosen valuation. -/
def mrangeRestrictCompleteDVF (F : CompleteDVF.{u, v} K) :
    CompleteDVF.{u, v} K := by
  let vK : _root_.Valuation K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F)
  letI : vK.IsRankOneDiscrete := by
    simpa [vK] using (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_isRankOneDiscrete F)
  letI :
      IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
        vK.valuationSubring := by
    simpa [vK] using (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_isAdicComplete F)
  letI : ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vK :=
    { isRankOneDiscrete := inferInstance
      isAdicComplete := inferInstance }
  exact
    { ValueGroup := MonoidHom.mrange F.valuation.toMonoidWithZeroHom
      valuation := vK }

/-- For the topology induced by the range-restricted rank-one valuation, the
valuation ring has its maximal-ideal adic topology. -/
theorem mrangeRestrict_integer_isAdic
    (F : CompleteDVF.{u, v} K) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
    IsAdic (𝓂[K]) := by
  let Γ : Type v :=
    MonoidHom.mrange F.valuation.toMonoidWithZeroHom
  let : Valued K Γ :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  let : NontriviallyNormedField K :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
  have : IsCyclic Γˣ := by
    simpa [Γ] using
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_units_isCyclic F)
  let : MulArchimedean Γ :=
    WithZeroValuation.units_isCyclic_mulArchimedean Γ
  have : (Valued.v : _root_.Valuation K Γ).IsRankOneDiscrete := by
    change
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).IsRankOneDiscrete
    exact
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_isRankOneDiscrete F)
  exact ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdic

/-- The valuation ring of a range-restricted complete DVF is complete for the
subspace topology coming from the corresponding normed-field topology. -/
theorem mrangeRestrict_integer_completeSpace
    (F : CompleteDVF.{u, v} K) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
    CompleteSpace 𝒪[K] := by
  let Γ : Type v :=
    MonoidHom.mrange F.valuation.toMonoidWithZeroHom
  let : Valued K Γ := (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  have : (Valued.v : _root_.Valuation K Γ).IsRankOneDiscrete := by
    change
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).IsRankOneDiscrete
    exact
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_isRankOneDiscrete F)
  have : (Valued.v : _root_.Valuation K Γ).RankOne := by
    change
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).RankOne
    exact
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_rankOne F)
  let : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField
      (L := K)
      (Γ₀ := MonoidHom.mrange
        F.valuation.toMonoidWithZeroHom)
  have : IsUltrametricDist K := by infer_instance
  have : IsDiscreteValuationRing 𝒪[K] := by
    change IsDiscreteValuationRing (Valued.v : _root_.Valuation K Γ).valuationSubring
    infer_instance
  have hadic : IsAdic (𝓂[K]) :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_integer_isAdic F)
  have hcomplete : IsAdicComplete (𝓂[K]) 𝒪[K] := by
    change
      IsAdicComplete
        (IsLocalRing.maximalIdeal (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring)
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring
    exact (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_isAdicComplete F)
  exact (hadic.isAdicComplete_iff.mp hcomplete).1

/-- The valuation ring of a range-restricted complete DVF with finite residue
field is compact.  This is the compactness input in the local-field structure theory,
the local compactness criterion. -/
theorem mrangeRestrict_integer_compactSpace_of_residueField_finite
    (F : CompleteDVF.{u, v} K) [Finite F.residueField] :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
    CompactSpace 𝒪[K] := by
  let : Valued K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  have :
      (Valued.v :
        _root_.Valuation K
          (MonoidHom.mrange
            F.valuation.toMonoidWithZeroHom)).IsRankOneDiscrete :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_isRankOneDiscrete F)
  have :
      (Valued.v :
        _root_.Valuation K
          (MonoidHom.mrange
            F.valuation.toMonoidWithZeroHom)).RankOne :=
    mrangeRestrictValued_rankOne F
  let : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField
      (L := K)
      (Γ₀ := MonoidHom.mrange
        F.valuation.toMonoidWithZeroHom)
  have : IsUltrametricDist K := by infer_instance
  have : IsDiscreteValuationRing 𝒪[K] := by
    change
      IsDiscreteValuationRing
        (Valued.v :
          _root_.Valuation K
            (MonoidHom.mrange
              F.valuation.toMonoidWithZeroHom)).valuationSubring
    infer_instance
  have : Finite 𝓀[K] := by
    change
      Finite
        (IsLocalRing.ResidueField (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring)
    exact (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_residueField_finite F)
  have hcomplete : CompleteSpace 𝒪[K] :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_integer_completeSpace F)
  exact
    (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
      (K := K)
      (Γ₀ := MonoidHom.mrange F.valuation.toMonoidWithZeroHom)).2
      ⟨hcomplete, inferInstance, inferInstance⟩

/-- A range-restricted complete DVF with finite residue field is proper for
the associated normed-field topology. -/
theorem mrangeRestrict_properSpace_of_residueField_finite
    (F : CompleteDVF.{u, v} K) [Finite F.residueField] :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
    ProperSpace K := by
  let : Valued K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  have :
      (Valued.v :
        _root_.Valuation K
          (MonoidHom.mrange
            F.valuation.toMonoidWithZeroHom)).RankOne :=
    mrangeRestrictValued_rankOne F
  let : NontriviallyNormedField K :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
  have hcompact : CompactSpace 𝒪[K] :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_integer_compactSpace_of_residueField_finite F)
  unfold mrangeRestrict_nontriviallyNormedField
  unfold Valued.toNontriviallyNormedField
  change @ProperSpace K
    (Valued.toNormedField K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom)
      (val := LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
      (hv := mrangeRestrictValued_rankOne F)).toPseudoMetricSpace
  exact
    (@Valued.integer.properSpace_iff_compactSpace_integer
      K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom)
      inferInstance inferInstance
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
      (mrangeRestrictValued_rankOne F)).2 hcompact

/-- A range-restricted complete DVF with finite residue field is complete for
the associated normed-field topology. -/
theorem mrangeRestrict_completeSpace_of_residueField_finite
    (F : CompleteDVF.{u, v} K) [Finite F.residueField] :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
    CompleteSpace K := by
  let Γ : Type v :=
    MonoidHom.mrange F.valuation.toMonoidWithZeroHom
  let : Valued K Γ := (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  let : NontriviallyNormedField K :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
  have : ProperSpace K :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_properSpace_of_residueField_finite F)
  exact complete_of_proper

end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

end
