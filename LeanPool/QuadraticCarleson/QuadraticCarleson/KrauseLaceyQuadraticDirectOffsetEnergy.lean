/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectAction
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectEnergyAssembly

/-!
# Energy of the exact fixed-offset inputs

This module transfers the one-piece quadratic energy estimate from the
global smallest-region scale pieces to the actual interval-dependent inputs
appearing in the finite offset reconstruction. It contains no frequency
projection or maximal-tail argument.
-/

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyQuadraticDirectOffsetEnergy

open KrauseLaceyBadScale KrauseLaceyQuadraticDirectPartition
open KrauseLaceyQuadraticDirectAction


noncomputable
section

/-- Applying the localized piece after restricting its input to the same
central third does not change the output. -/
theorem krauseLaceyLocalizedPiece_indicator_centralThird
    (k : ℤ) (I : RealInterval) (b : ℝ → ℂ) :
    krauseLaceyLocalizedPiece 1 k I (I.centralThird.indicator b) =
      krauseLaceyLocalizedPiece 1 k I b := by
  funext x
  unfold krauseLaceyLocalizedPiece
  apply integral_congr_ae
  filter_upwards with y
  congr 1
  simp only [Set.indicator_indicator, Set.inter_self]

/-- Consequently the genuine squared energy is unchanged by repeating the
central-third restriction. -/
theorem localizedEnergy_indicator_centralThird
    (k : ℤ) (I : RealInterval) (b : ℝ → ℂ) :
    localizedEnergy k I (I.centralThird.indicator b) = localizedEnergy k I b := by
  unfold localizedEnergy
  rw [krauseLaceyLocalizedPiece_indicator_centralThird]

/-- The actual interval-dependent fixed-offset input has the exact
`2^{-s}` one-piece energy gain. This is the per-output input to the smooth
annular square-function argument. -/
theorem localizedEnergy_offsetGroupedInput_le
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ J ∈ S, J.length = (2 : ℝ) ^ (scale J + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s)
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (I : RealInterval) (hI : I ∈ S)
    (hgap : 0 ≤ scale I + 2 - s) :
    localizedEnergy (scale I) I (offsetGroupedInput S scale f I s) ≤
      (432 * positiveDyadicAmplitudeBound ^ 2 * M * (2 : ℝ) ^ (-s)) *
        ∫ x in I.centralThird, ‖offsetGroupedInput S scale f I s x‖ := by
  let b := smallestScaleInput S scale f (scale I - s)
  have hoff : offsetGroupedInput S scale f I s = I.centralThird.indicator b := by
    simpa only [b] using
      offsetGroupedInput_eq_indicator_smallestScaleInput
        hlam scale hscale hI (f : ℝ → ℂ) hs
  have henergy := localizedEnergy_smallestScaleInput_le
    hlam scale hscale f hgap hM hmass I hI (hscale I hI)
  rw [hoff, localizedEnergy_indicator_centralThird]
  calc
    localizedEnergy (scale I) I b ≤
        (432 * positiveDyadicAmplitudeBound ^ 2 * M * (2 : ℝ) ^ (-s)) *
          ∫ x in I.centralThird, ‖b x‖ := henergy
    _ = (432 * positiveDyadicAmplitudeBound ^ 2 * M * (2 : ℝ) ^ (-s)) *
          ∫ x in I.centralThird, ‖I.centralThird.indicator b x‖ := by
      congr 1
      apply setIntegral_congr_fun I.measurableSet_centralThird
      intro x hx
      change ‖b x‖ = ‖I.centralThird.indicator b x‖
      rw [Set.indicator_of_mem hx]
    _ = _ := by rw [← hoff]


end
end KrauseLaceyQuadraticDirectOffsetEnergy
end QuadraticCarleson
