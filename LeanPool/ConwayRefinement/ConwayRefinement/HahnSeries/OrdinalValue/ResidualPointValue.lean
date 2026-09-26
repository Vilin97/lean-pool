/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalValue
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPoint

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.GermValueCut

/-!
# Values of translated truncations at residual points

Berarducci, Remark 9.4 and Remark 6.7, in the forms used by the complexity induction of Section 9.

Every sufficiently high translated truncation has strictly smaller ordinal value, because the
value cut bounds it by a proper ordinary multiple of the residual value. At a residual point the
truncation value is the residual value itself, so its principal value is the principal factor of
the residual factor, which is at least the principal value of the series.
-/

universe v

public noncomputable section

open HahnSeries Ordinal

namespace Berarducci

variable {K : Type v} [Field K]

/-- Berarducci, Remark 9.4: sufficiently high translated truncations have strictly smaller
ordinal value. -/
theorem exists_ordinalValue_translatedTruncation_lt (b : SeriesWithOrdinalValueAboveOne K) :
    ∃ η < (0 : ℝ), ∀ γ : ℝ, η < γ → γ < 0 →
      ordinalValue (translatedTruncation (b.1 : K⟦ℝ⟧) γ) < ordinalValue b.1 := by
  obtain ⟨η, hη, hcut⟩ := exists_ordinalValue_translatedTruncation_le b
  refine ⟨η, hη, fun γ hlow hhigh ↦ ?_⟩
  obtain ⟨α, hα, hle⟩ := hcut γ hlow hhigh
  have hρpos : 0 < b.residualValue.val := by
    rw [pos_iff_ne_zero]
    exact NatOrdinal.val_ne_zero.mpr b.residualValue_ne_zero
  have hlt : b.residualValue.val * α < (ordinalValue b.1).val := by
    rw [← b.residualValue_val_mul_principalValue_val]
    exact (Ordinal.isNormal_mul_right hρpos).strictMono hα
  exact NatOrdinal.val.lt_iff_lt.mp (hle.trans_lt hlt)

/-- Berarducci, Remark 6.7: at a residual point, the translated truncation has principal value at
least that of the series. -/
theorem principalValue_le_of_mem_residualPointSet
    (b d : SeriesWithOrdinalValueAboveOne K) {γ : ℝ} (hγ : γ ∈ residualPointSet b)
    (hd : d.1 = translatedTruncation (b.1 : K⟦ℝ⟧) γ) :
    b.principalValue ≤ d.principalValue := by
  refine b.principalValue_le_of_ordinalValue_eq_residualValue d ?_
  rw [hd]
  exact (mem_residualPointSet_iff.mp hγ).2

end Berarducci
