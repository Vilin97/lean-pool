/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.ProjValMeasure.Additivity

/-!
# A lower bound proved blockwise

If a family of bounded operators splits vector norms — `∑ ‖blocks i f‖² = ‖f‖²`
— then a lower bound holding on every block holds globally.

This is the reassembly step of a block-diagonal argument, stated with nothing
about where the blocks come from: no projections, no spectral theory, no
countability, no convergence of `∑ blocks i` in any operator topology.  The only
hypothesis is the norm split, which is what a projection-valued measure supplies
along a partition (`ProjValMeasure.tsum_enorm_sq_proj`).

Working in `ℝ≥0∞` keeps it free of summability side conditions: the sums are
unconditional and no term has to be shown finite.

## Sources

*Follows nothing in particular*: the reassembly step of a block-diagonal argument,
stated with no projections, no spectral theory and no convergence hypothesis.

## Provenance

*New.*
-/

@[expose] public section

open scoped ENNReal NNReal

namespace TauCeti

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **A lower bound that holds blockwise holds globally.**

Stated between two *vectors* rather than for an operator and its argument.  The
operator never appears in the proof — only its value — and phrasing it this way
makes the shifted case free: to bound `S - s` below, take `y = S x - s • x`, with
no need to build `S - s` as a partial map. -/
theorem enorm_ge_of_blocks {c : ℝ≥0∞} {ι : Type*}
    (blocks : ι → (H →L[ℂ] H))
    (hsplit : ∀ f : H, ∑' i, ‖blocks i f‖ₑ ^ 2 = ‖f‖ₑ ^ 2)
    {x y : H} (hblock : ∀ i, c * ‖blocks i x‖ₑ ≤ ‖blocks i y‖ₑ) :
    c * ‖x‖ₑ ≤ ‖y‖ₑ := by
  have hsq : (c * ‖x‖ₑ) ^ 2 ≤ ‖y‖ₑ ^ 2 := by
    calc (c * ‖x‖ₑ) ^ 2
        = c ^ 2 * ∑' i, ‖blocks i x‖ₑ ^ 2 := by rw [mul_pow, hsplit]
      _ = ∑' i, (c * ‖blocks i x‖ₑ) ^ 2 := by
          simp_rw [mul_pow]
          exact (ENNReal.tsum_mul_left).symm
      _ ≤ ∑' i, ‖blocks i y‖ₑ ^ 2 :=
          ENNReal.tsum_le_tsum fun i => by gcongr; exact hblock i
      _ = ‖y‖ₑ ^ 2 := hsplit _
  by_contra hcon
  push Not at hcon
  exact absurd ((ENNReal.pow_lt_pow_left_iff (n := 2) two_ne_zero).mpr hcon) (not_lt.mpr hsq)

end TauCeti
