/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.Topology.Algebra.Valued.ValuedField

/-! # Valued Adic Complete -/
universe u v

namespace ValuationTheory

/-!
# Adic completeness of complete rank-one discrete valued fields

This file supplies the common source used in the valuation-topology and adic-completeness
  arguments: on a
rank-one discrete valued field with archimedean ambient value group, the
native topology of the valuation ring is its maximal-ideal adic topology.
Consequently a complete valued field has an adically complete valuation ring.
-/

noncomputable section

namespace Valuations

open DiscreteValuationField

/-- The valuation ring of a rank-one discrete valued field is a discrete
valuation ring. -/
theorem rankOneDiscreteValuationSubring_isDiscreteValuationRing
    {K : Type u} [Field K] {Gamma : Type v}
    [LinearOrderedCommGroupWithZero Gamma]
    [Valued K Gamma]
    [(Valued.v : Valuation K Gamma).IsRankOneDiscrete] :
    IsDiscreteValuationRing
      (Valued.v : Valuation K Gamma).valuationSubring := by
  let F : DVF.{u, v} K :=
    { ValueGroup := Gamma
      valuation := Valued.v }
  exact F.valuationSubring_isDiscreteValuationRing

/-- The native subtype topology on the valuation ring of a rank-one discrete
valued field is its maximal-ideal adic topology. -/
theorem rankOneDiscreteValuationSubring_isAdic
    {K : Type u} [Field K] {Gamma : Type v}
    [LinearOrderedCommGroupWithZero Gamma] [MulArchimedean Gamma]
    [Valued K Gamma]
    [(Valued.v : Valuation K Gamma).IsRankOneDiscrete] :
    IsAdic
      (IsLocalRing.maximalIdeal
        (Valued.v : Valuation K Gamma).valuationSubring) := by
  let val := (Valued.v : Valuation K Gamma)
  let : IsTopologicalRing val.valuationSubring :=
    Subring.instIsTopologicalRing val.valuationSubring.toSubring
  rcases Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial val with
    ⟨pi, hpi⟩
  rw [isAdic_iff]
  constructor
  · intro n
    have h_radius_ne :
        val (((pi ^ n : val.valuationSubring) : K)) ≠ 0 := by
      change val ((pi : K) ^ n) ≠ 0
      rw [map_pow]
      exact pow_ne_zero n hpi.val_ne_zero
    have h_restrict_radius_ne :
        val.restrict (((pi ^ n : val.valuationSubring) : K)) ≠ 0 := by
      simpa using h_radius_ne
    have h_open_ball_restrict : IsOpen
        {x : K |
          val.restrict x ≤
            val.restrict (((pi ^ n : val.valuationSubring) : K))} :=
      Valued.isOpen_closedBall K h_restrict_radius_ne
    have h_open_ball : IsOpen
        {x : K |
          val x ≤ val (((pi ^ n : val.valuationSubring) : K))} := by
      simpa only [val.restrict_le_iff] using h_open_ball_restrict
    have h_preimage_open : IsOpen
        {x : val.valuationSubring |
          val (x : K) ≤ val (((pi ^ n : val.valuationSubring) : K))} :=
      h_open_ball.preimage continuous_subtype_val
    convert h_preimage_open using 1
    ext x
    exact
      (ValuationTheory.DiscreteValuationField.Valuation.mem_maximalIdeal_pow_iff_valuation_le_uniformizer_pow
          (val := val) (pi := pi) hpi n)
  · intro s hs
    rcases
        (mem_nhds_subtype (val.valuationSubring : Set K)
          (0 : val.valuationSubring) s).1 hs with
      ⟨t, ht, hts⟩
    rcases (Valued.hasBasis_nhds_zero K Gamma).mem_iff.mp ht with
      ⟨gamma, _hgamma, hgamma_t⟩
    let gamma' : Gammaˣ :=
      Units.map
        (MonoidWithZeroHom.ValueGroup₀.embedding (f := (.ofClass val)))
        gamma
    rcases exists_pow_lt
        (Valuation.IsRankOneDiscrete.generator_lt_one val)
        gamma' with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    intro x hx
    apply hts
    apply hgamma_t
    change val.restrict (x : K) < gamma.1
    rw [Valuation.restrict_lt_iff_lt_embedding]
    have hx_le :=
      (ValuationTheory.DiscreteValuationField.Valuation.mem_maximalIdeal_pow_iff_valuation_le_uniformizer_pow
          (val := val) (pi := pi) hpi n).1 hx
    calc
      val (x : K) ≤ val (((pi ^ n : val.valuationSubring) : K)) := hx_le
      _ = ((Valuation.IsRankOneDiscrete.generator val) ^ n : Gamma) := by
            simp [map_pow, hpi.val]
      _ < MonoidWithZeroHom.ValueGroup₀.embedding (f := (.ofClass val)) gamma.1 := by
        have hn_coe := Units.val_lt_val.mp hn
        change
          ((Valuation.IsRankOneDiscrete.generator val : Gammaˣ) : Gamma) ^ n <
            MonoidWithZeroHom.ValueGroup₀.embedding
              (f := (.ofClass val)) gamma.1 at hn_coe
        exact hn_coe

/-- Completeness of a rank-one discrete valued field produces adic
completeness of its valuation ring; no adic-completeness assumption is
exposed. -/
theorem rankOneDiscreteValuationSubring_isAdicComplete
    {K : Type u} [Field K] {Gamma : Type v}
    [LinearOrderedCommGroupWithZero Gamma] [MulArchimedean Gamma]
    [Valued K Gamma]
    [(Valued.v : Valuation K Gamma).IsRankOneDiscrete]
    [CompleteSpace K] :
    IsAdicComplete
      (IsLocalRing.maximalIdeal
        (Valued.v : Valuation K Gamma).valuationSubring)
      (Valued.v : Valuation K Gamma).valuationSubring := by
  let val := (Valued.v : Valuation K Gamma)
  let : IsUniformAddGroup val.valuationSubring :=
    val.valuationSubring.toAddSubgroup.isUniformAddGroup
  let : IsTopologicalRing val.valuationSubring :=
    Subring.instIsTopologicalRing val.valuationSubring.toSubring
  let : CompleteSpace val.valuationSubring :=
    (Valued.isClosed_valuationSubring K).completeSpace_coe
  exact rankOneDiscreteValuationSubring_isAdic.isAdicComplete_iff.2
    ⟨inferInstance, inferInstance⟩

/-- A complete rank-one discrete valued field, equipped with its distinguished
valuation, gives a `CompleteDVF` by construction. -/
noncomputable def completeDVFOfCompleteValuedField
    {K : Type u} [Field K] {Gamma : Type v}
    [LinearOrderedCommGroupWithZero Gamma] [MulArchimedean Gamma]
    [Valued K Gamma]
    [(Valued.v : Valuation K Gamma).IsRankOneDiscrete]
    [CompleteSpace K] :
    CompleteDVF.{u, v} K where
  ValueGroup := Gamma
  valuation := Valued.v
  instCompleteDiscrete :=
    { isRankOneDiscrete := inferInstance
      isAdicComplete := rankOneDiscreteValuationSubring_isAdicComplete }

end Valuations
end

end ValuationTheory
