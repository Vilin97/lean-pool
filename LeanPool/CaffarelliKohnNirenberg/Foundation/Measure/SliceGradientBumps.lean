/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Basic

/-!
# Mollifier radii and almost-everywhere convergence

The approximate-identity sequence underlying the paper's mollification input
(`ext:mollify`) is indexed by the outer radius `sliceRadius n = 1 / (n + 1)`,
which decreases to zero as `n` grows. The normalized kernel produced by
`standardMollifier` has inner radius equal to half its outer radius, so the
ratio of the two radii is bounded by the constant `2`. Mathlib's
almost-everywhere convergence theorem for mollifications of a locally
integrable function therefore applies: for any `g`, the functions
`mollify g (sliceRadius n) _` converge to `g` almost everywhere.
-/

@[expose] public section

open MeasureTheory Filter Topology


noncomputable section

namespace CKN

/-- The outer radius of the `n`-th mollifier in the approximate-identity sequence. -/
def sliceRadius (n : ℕ) : ℝ := 1 / (n + 1)

theorem sliceRadius_pos (n : ℕ) : 0 < sliceRadius n := by
  unfold sliceRadius
  positivity

theorem tendsto_sliceRadius_atTop :
    Filter.Tendsto sliceRadius Filter.atTop (nhds (0 : ℝ)) := by
  unfold sliceRadius
  exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

theorem ae_tendsto_mollify_sliceRadius {d : ℕ} {g : Vec d → ℝ}
    (hg : MeasureTheory.LocallyIntegrable g MeasureTheory.volume) :
    ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Vec d)),
      Filter.Tendsto (fun n : ℕ => mollify g (sliceRadius n) (sliceRadius_pos n) x)
        Filter.atTop (nhds (g x)) := by
  let φ : ℕ → ContDiffBump (0 : Vec d) :=
    fun n => standardMollifier (sliceRadius n) (sliceRadius_pos n)
  have hφ : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (𝓝 0) := by
    simpa only [φ, standardMollifier, sliceRadius] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h'φ : ∀ᶠ n in Filter.atTop, (φ n).rOut ≤ 2 * (φ n).rIn :=
    Filter.Eventually.of_forall fun n => by
      simp only [φ, standardMollifier]
      exact le_of_eq (by ring)
  exact (ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := MeasureTheory.volume) (K := 2) hφ h'φ hg).mono fun x hx => by
      simpa only [φ, mollify, mollifier] using hx

end CKN

end
