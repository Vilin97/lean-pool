/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyEnergyClassification

/-!
# Cardinality-free diagonal aggregation for the scalar-standard branch

The scalar-standard far-energy estimate is summable over every physical tail
without a cardinality loss. Passing from this diagonal statement to a norm
of the *sum* requires a signed cross-scale estimate; that estimate is kept
separate here rather than being silently inferred from diagonal energy.
-/

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction

attribute [local instance] Classical.propDecidable

/-- Restricting a scalar-standard collection to one physical tail retains the
exact scale lower bound encoded by the actual length cutoff. -/
theorem scale_le_of_mem_energyStandard_physicalTail
    {S : Finset RealInterval} {f : ℝ → ℂ} (I₀ : RealInterval) (k₀ s ell : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval)
    (hN : N ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    {I : RealInterval} (hI : I ∈ N.filter fun I ↦ (2 : ℝ) ^ ell ≤ I.length) :
    ell - 2 ≤ scale I := by
  have hlen := (Finset.mem_filter.mp (Finset.mem_filter.mp (hN
    (Finset.mem_filter.mp hI).1)).1).2.1
  have htail := (Finset.mem_filter.mp hI).2
  rw [hlen] at htail
  have hpow : ell ≤ scale I + 2 :=
    (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
      htail
  omega

/-- The actual physical tail has a uniform scalar-standard *diagonal* energy
bound. Its constant is independent of `N.card` and of the number of scales.
This is the precise far-energy aggregation available before cross-scale
signed-sum control is supplied. -/
theorem sum_energyStandard_physicalTail_diagonalEnergy_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s ell : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ energyStandardIntervals S f I₀ k₀ s scale) :
    (∑ I ∈ N.filter fun I ↦ (2 : ℝ) ^ ell ≤ I.length,
      localizedEnergy (scale I) I
        (badScaleInput S f I₀ k₀ (scale I + 2 - s))) ≤
      (2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ /
        (2 : ℝ) ^ ell) * ∫ x, ‖f x‖ := by
  have h := sum_energyStandard_badPiece_diagonalEnergy_le hf I₀ k₀ s (ell - 2) scale
    hlam hsub (N.filter fun I ↦ (2 : ℝ) ^ ell ≤ I.length)
    ((Finset.filter_subset _ N).trans hN)
    (fun I hI ↦ scale_le_of_mem_energyStandard_physicalTail I₀ k₀ s ell scale N hN hI)
  convert h using 1; congr 1; ring


end KrauseLaceyBadScale
end QuadraticCarleson
