/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPointTail
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.SetOrderType
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPointSupport
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPointOrderType
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPointWellOrdered
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPointCofinality
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.OrderedUnion
import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.LeftNeighborhood
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Berarducci residual-point tail statements

This module gives direct Lean statements of Berarducci, Lemmas 6.8 and 6.9. Lemma 6.8 combines
the proved cofinality, well-ordering, and order-type results. Lemma 6.9 invokes Lemma 6.8, applies
the proved support-family construction, and then applies the proved ordered-union estimate from
Berarducci, Lemma 4.7.

The phrase "sufficiently close to zero" is the filter `nhdsWithin 0 (Set.Iio 0)`. The order type
in Lemma 6.8 is an `Ordinal`, hence the explicit `.val` on the `NatOrdinal` principal value. The
product in Lemma 6.9 is ordinary ordinal multiplication inside `NatOrdinal.of`, not Hessenberg
multiplication.

Berarducci prints Lemma 6.9 for arbitrary `b`, although both `X(b)` and `v_J^p(b)` were
defined only when `1 < v_J(b)`. The Lean statement uses `SeriesWithOrdinalValueAboveOne K` for `b`,
making that necessary domain explicit without adding a mathematical hypothesis to a well-formed
source formula.

The theorem statements agree with the printed Lemmas 6.8 and 6.9. For residual value one, the
proof of Lemma 6.8 uses isolated successor-indexed support points instead of the failing
limit-index construction in the printed proof; its conclusion is unchanged.

Berarducci's ambient coefficient field has characteristic zero. The source statements retain
that hypothesis even though their proved definitions and cofinality prerequisite are available over
an arbitrary field.
-/

universe v

open scoped HahnSeries NatOrdinal Topology

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K]

/-- Berarducci, Lemma 6.8: sufficiently high residual-point tails have principal order type and
least upper bound zero. -/
theorem residualPointTail_eventually [CharZero K]
    (b : SeriesWithOrdinalValueAboveOne K) :
    ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Iio 0),
      (residualPointTail b η).Nonempty ∧
        ∃ htail : (residualPointTail b η).IsPWO,
          htail.orderType = b.principalValue.val ∧
            IsLUB (residualPointTail b η) 0 := by
  have hX := residualPointSet_isPWO b
  have hXLUB := residualPointSet_isLUB_zero b
  filter_upwards [residualPointTail_orderType_eventually b hX,
    self_mem_nhdsWithin] with η htailType hη
  have htailStructure := residualPointTail_nonempty_and_isLUB b hη hXLUB
  exact ⟨htailStructure.1, residualPointTail_isPWO b η hX,
    htailType, htailStructure.2⟩

/-- Berarducci, Lemma 6.9: an eventual lower bound on values of translated truncations along
`X(b)` gives the corresponding ordinary-product lower bound on `v_J(c)`. -/
theorem ordinalValue_ge_of_eventually_ordinalValue_translatedTruncation_ge [CharZero K]
    (b : SeriesWithOrdinalValueAboveOne K) (c : Series K) {ρ : Ordinal}
    (hρ : Ordinal.IsPrincipal (fun α β ↦ α + β) ρ)
    (hc : ∀ᶠ γ in nhdsWithin (0 : ℝ) (Set.Iio 0),
      γ ∈ residualPointSet b →
        NatOrdinal.of ρ ≤ ordinalValue (translatedTruncation (c : K⟦ℝ⟧) γ)) :
    NatOrdinal.of (ρ * b.principalValue.val) ≤ ordinalValue c := by
  by_cases hρ0 : ρ = 0
  · subst ρ
    simp
  obtain ⟨ηc, hηc, hcAbove⟩ :=
    eventually_nhdsLT_iff_exists.mp hc
  obtain ⟨ηt, hηt, htailAbove⟩ :=
    eventually_nhdsLT_iff_exists.mp (residualPointTail_eventually b)
  obtain ⟨η, hηLower, hη⟩ := exists_between (max_lt hηc hηt)
  have hηcη : ηc < η := (le_max_left ηc ηt).trans_lt hηLower
  have hηtη : ηt < η := (le_max_right ηc ηt).trans_lt hηLower
  obtain ⟨_, ⟨htail, htailType, htailLUB⟩⟩ :=
    htailAbove η hηtη hη
  have hcTail : ∀ γ ∈ residualPointTail b η,
      NatOrdinal.of ρ ≤ ordinalValue (translatedTruncation (c : K⟦ℝ⟧) γ) := by
    intro γ hγ
    obtain ⟨hγX, hηγ⟩ := mem_residualPointTail_iff.mp hγ
    exact hcAbove γ (hηcη.trans hηγ)
      (residualPointSet_subset_Iio b hγX) hγX
  apply le_ordinalValue_of_forall_mem_representativeOrderTypes
  intro o ho
  obtain ⟨d, hcd, rfl⟩ := mem_representativeOrderTypes_iff.mp ho
  rw [NatOrdinal.of.le_iff_le]
  obtain ⟨B, hB, hseparated, hfinal, hUnion, hsubset⟩ :=
    exists_supportFamily_of_residualPointTail b c hρ0 htail htailType htailLUB hcTail d hcd
  have hproduct := hUnion.mul_le_orderType_iUnion_of_isSuccLimit
    b.principalValue_isInfiniteMultiplicativelyPrincipal.isSuccLimit B hB
      hseparated hfinal
  calc
    ρ * b.principalValue.val ≤ hUnion.orderType := hproduct
    _ ≤ (d : K⟦ℝ⟧).isPWO_support.orderType :=
      hUnion.orderType_mono (d : K⟦ℝ⟧).isPWO_support hsubset
    _ = (d : K⟦ℝ⟧).supportOrderType :=
      (HahnSeries.supportOrderType_eq_setOrderType _).symm

end Berarducci
