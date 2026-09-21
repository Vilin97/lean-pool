/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralMeasure

/-!
# `A - c` on a spectral range, as a bounded operator

`SpectralMeasure.lean` proves the estimate `‖A y - c y‖ ≤ r ‖y‖` for `y` in the
spectral range of a set lying within `r` of `c`, but only pointwise.  A
Hilbert–Schmidt block argument needs it as an *operator* bound, because the
ideal properties of the Hilbert–Schmidt energy are stated for compositions with
bounded operators.

The bundling is free.  `specProjection_apply_sub_smul` already identifies
`A (E_A(B) y) - c E_A(B) y` with the Borel calculus of a symbol bounded by `r`,
and the Borel calculus is a bounded operator; so the operator wanted is that one,
and its norm bound is `norm_borelCalculus_apply_le`.

`specCutOp_apply` records the identification in the form the block argument
uses: on the spectral range — where the projection acts as the identity — the
operator *is* `A - c`.

## Sources

*Follows nothing in particular*: a pointwise spectral estimate promoted to an operator
bound, because the ideal properties of the Hilbert--Schmidt energy are stated for
operators.

## Provenance

*New.*  Everything here is a repackaging of `specProjection_apply_sub_smul`.
-/

public section

open scoped InnerProductSpace

namespace TauCeti
namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ) (hB : MeasurableSet B)

/-- `A - c`, cut down to the spectral range of `B`, as a bounded operator. -/
@[expose]
noncomputable def specCutOp {c r : ℝ} (hr : 0 ≤ r) (hcr : ∀ s ∈ B, |s - c| ≤ r) :
    H →L[ℂ] H :=
  BorelCalculus.borelCalculus (isStarNormal_cayley hA)
    (isBddMeasurable_truncSymbol hA B hB hr hcr)

/-- The cut operator is bounded by the radius of the spectral set. -/
theorem norm_specCutOp_apply_le {c r : ℝ} (hr : 0 ≤ r) (hcr : ∀ s ∈ B, |s - c| ≤ r)
    (y : H) : ‖specCutOp hA B hB hr hcr y‖ ≤ r * ‖y‖ :=
  BorelCalculus.norm_borelCalculus_apply_le _ _ hr (norm_truncSymbol_le hA B hr hcr) y

/-- Operator-norm form of the cut bound, from the pointwise one. -/
theorem norm_specCutOp_le {c r : ℝ} (hr : 0 ≤ r) (hcr : ∀ s ∈ B, |s - c| ≤ r) :
    ‖specCutOp hA B hB (c := c) hr hcr‖ ≤ r :=
  ContinuousLinearMap.opNorm_le_bound _ hr (norm_specCutOp_apply_le hA B hB hr hcr)

/-- **On the spectral range the cut operator is `A - c`.**  This is the form the
block argument consumes: the left factor of `(A - c) W` is bounded, so the
Hilbert–Schmidt ideal property applies. -/

theorem specCutOp_apply {M c r : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) (hr : 0 ≤ r)
    (hcr : ∀ s ∈ B, |s - c| ≤ r) {y : H} (hy : y ∈ specRange hA B hB)
    (hmem : y ∈ A.domain) :
    specCutOp hA B hB hr hcr y = A ⟨y, hmem⟩ - (c : ℂ) • y := by
  have hfix : specProjection hA B hB y = y := (mem_specRange_iff hA B hB y).mp hy
  obtain ⟨hy', hb⟩ := specProjection_apply_sub_smul hA B hB hbnd hr hcr y
  have hsub : (⟨specProjection hA B hB y, hy'⟩ : A.domain) = ⟨y, hmem⟩ := Subtype.ext hfix
  rw [hsub, hfix] at hb
  exact hb.symm

end LinearPMap
end TauCeti
