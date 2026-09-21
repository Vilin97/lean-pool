/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectPartition
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticOnePieceEnergy

/-!
# Connecting the direct partition to quadratic one-piece energy

This file discharges the elementary geometric hypotheses of the direct
quadratic energy estimate for the smallest-selected-interval scale pieces.
-/

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyQuadraticDirectPartition

open KrauseLaceyBadScale KrauseLaceyStoppingExtraction


noncomputable section

local instance : DecidableEq RealInterval := Classical.decEq _

/-- In a laminar dyadic family, distinct intervals with one common scale
are disjoint. -/
theorem sameScale_carriers_pairwiseDisjoint
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ J ∈ S, J.length = (2 : ℝ) ^ (scale J + 2))
    (m : ℤ) :
    Set.Pairwise (↑(S.filter (fun J ↦ scale J = m)) : Set RealInterval)
      (Disjoint on RealInterval.carrier) := by
  intro I hI J hJ hne
  have hIS : I ∈ S := (Finset.mem_filter.mp hI).1
  have hJS : J ∈ S := (Finset.mem_filter.mp hJ).1
  have him : scale I = m := (Finset.mem_filter.mp hI).2
  have hjm : scale J = m := (Finset.mem_filter.mp hJ).2
  have hlen : I.length = J.length := by rw [hscale I hIS, hscale J hJS, him, hjm]
  rcases hlam hIS hJS hne with hsub | hsub | hdis
  · exact (hne (interval_eq_of_carrier_subset_of_length_le hsub hlen.ge)).elim
  · exact (hne (interval_eq_of_carrier_subset_of_length_le hsub hlen.le).symm).elim
  · exact hdis

/-- Exact dyadic lengths turn carrier inclusion into scale monotonicity. -/
theorem scale_le_of_carrier_subset
    {S : Finset RealInterval} (scale : RealInterval → ℤ)
    (hscale : ∀ J ∈ S, J.length = (2 : ℝ) ^ (scale J + 2))
    {I J : RealInterval} (hI : I ∈ S) (hJ : J ∈ S)
    (hsub : J.carrier ⊆ I.carrier) : scale J ≤ scale I := by
  have he := (Ioc_subset_Ioc_iff J.left_lt_right).mp hsub
  have hlen : J.length ≤ I.length := by
    dsimp [RealInterval.length]
    linarith [he.1, he.2]
  rw [hscale J hJ, hscale I hI] at hlen
  have hexp : scale J + 2 ≤ scale I + 2 :=
    (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hlen
  omega

/-- Every scale occurring below a selected root is at most the root scale. -/
theorem mem_image_selectedSubintervals_scale_le
    {S : Finset RealInterval} (scale : RealInterval → ℤ)
    (hscale : ∀ J ∈ S, J.length = (2 : ℝ) ^ (scale J + 2))
    {I : RealInterval} (hI : I ∈ S) {m : ℤ}
    (hm : m ∈ (selectedSubintervals S I).image scale) :
    m ≤ scale I := by
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hm
  have hJ' := mem_selectedSubintervals_iff.mp hJ
  exact scale_le_of_carrier_subset scale hscale hI hJ'.1 hJ'.2

/-- Restricting a scale input to an output interval's central third can
only lower its mass, and the scale input is pointwise dominated by `f`. -/
theorem integral_centralThird_norm_smallestScaleInput_le
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ) (f : L0Infinity) (m : ℤ)
    (I : RealInterval) :
    (∫ x in I.centralThird, ‖smallestScaleInput S scale f m x‖) ≤
      ∫ x in I.carrier, ‖f x‖ := by
  calc
    (∫ x in I.centralThird, ‖smallestScaleInput S scale f m x‖) ≤
        ∫ x in I.centralThird, ‖f x‖ := by
      apply integral_mono
      · exact (integrable_smallestScaleInput S scale f m).norm.integrableOn
      · exact f.integrable_finiteSparseProof.norm.integrableOn
      · intro x
        exact norm_smallestScaleInput_le_norm hlam scale f m x
    _ ≤ ∫ x in I.carrier, ‖f x‖ :=
      setIntegral_mono_set f.integrable_finiteSparseProof.norm.integrableOn
        (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
        I.centralThird_subset_carrier.eventuallyLE

/-- A unit window sees at most three interval lengths of one scale. -/
theorem localUnitMass_smallestScaleInput_le
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ J ∈ S, J.length = (2 : ℝ) ^ (scale J + 2))
    (f : L0Infinity) (m : ℤ) (hm : 0 ≤ m + 2)
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (I : RealInterval) (x : ℝ) :
    localUnitMass I (smallestScaleInput S scale f m) x ≤
      3 * M * (2 : ℝ) ^ (m + 2) := by
  let L : ℝ := (2 : ℝ) ^ (m + 2)
  have hL : 0 < L := by dsimp [L]; positivity
  have hLone : 1 ≤ L := by
    dsimp [L]
    simpa only [zpow_zero] using
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm
  have hwindow := integral_window_norm_smallestScaleInput_le hlam scale f m
    (sameScale_carriers_pairwiseDisjoint hlam scale hscale m)
    hL hM (by linarith : x - 1 / 2 ≤ x + 1 / 2)
    (fun J hJ ↦ by
      dsimp [L]
      rw [hscale J (Finset.mem_filter.mp hJ).1,
        (Finset.mem_filter.mp hJ).2])
    (fun J hJ ↦ hmass J (Finset.mem_filter.mp hJ).1)
  have hrestricted :
      localUnitMass I (smallestScaleInput S scale f m) x ≤
        ∫ t in Icc (x - 1 / 2) (x + 1 / 2),
          ‖smallestScaleInput S scale f m t‖ := by
    unfold localUnitMass
    apply integral_mono
    · exact ((integrable_smallestScaleInput S scale f m).indicator
        I.measurableSet_centralThird).norm.integrableOn
    · exact (integrable_smallestScaleInput S scale f m).norm.integrableOn
    · intro t
      change ‖I.centralThird.indicator
          (smallestScaleInput S scale f m) t‖ ≤
        ‖smallestScaleInput S scale f m t‖
      by_cases ht : t ∈ I.centralThird
      · rw [Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht, norm_zero]
        exact norm_nonneg _
  calc
    localUnitMass I (smallestScaleInput S scale f m) x ≤
        ∫ t in Icc (x - 1 / 2) (x + 1 / 2),
          ‖smallestScaleInput S scale f m t‖ := hrestricted
    _ ≤ M * ((x + 1 / 2) - (x - 1 / 2) + 2 * L) := hwindow
    _ ≤ 3 * M * L := by nlinarith
    _ = 3 * M * (2 : ℝ) ^ (m + 2) := rfl

/-- The direct partition pieces satisfy the quadratic one-piece energy
estimate with the exact gap gain `2^{-s}`. -/
theorem localizedEnergy_smallestScaleInput_le
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ J ∈ S, J.length = (2 : ℝ) ^ (scale J + 2))
    (f : L0Infinity) {k s : ℤ} (hgap : 0 ≤ k + 2 - s)
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ∀ J ∈ S, (∫ x in J.carrier, ‖f x‖) ≤ M * J.length)
    (I : RealInterval) (hI : I ∈ S)
    (hIscale : I.length = (2 : ℝ) ^ (k + 2)) :
    localizedEnergy k I (smallestScaleInput S scale f (k - s)) ≤
      (432 * positiveDyadicAmplitudeBound ^ 2 * M * (2 : ℝ) ^ (-s)) *
        ∫ x in I.centralThird, ‖smallestScaleInput S scale f (k - s) x‖ := by
  have hmindex : 0 ≤ (k - s) + 2 := by omega
  have hunit : ∀ x : ℝ,
      localUnitMass I (smallestScaleInput S scale f (k - s)) x ≤
        (3 * M) * (2 : ℝ) ^ (k + 2 - s) := by
    intro x
    simpa only [show k - s + 2 = k + 2 - s by ring] using
      localUnitMass_smallestScaleInput_le hlam scale hscale f (k - s)
        hmindex hM hmass I x
  have hpow : 1 ≤ (2 : ℝ) ^ (k + 2 - s) := by
    simpa only [zpow_zero] using
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hgap
  have hcentral :
      (∫ x in I.centralThird, ‖smallestScaleInput S scale f (k - s) x‖) ≤
        ((3 * M) * (2 : ℝ) ^ (k + 2 - s)) * I.length := by
    calc
      _ ≤ ∫ x in I.carrier, ‖f x‖ :=
        integral_centralThird_norm_smallestScaleInput_le hlam scale f (k - s) I
      _ ≤ M * I.length := hmass I hI
      _ ≤ ((3 * M) * (2 : ℝ) ^ (k + 2 - s)) * I.length := by
        apply mul_le_mul_of_nonneg_right _ I.length_pos.le
        calc
          M ≤ 3 * M := by nlinarith
          _ = (3 * M) * 1 := by ring
          _ ≤ (3 * M) * (2 : ℝ) ^ (k + 2 - s) :=
            mul_le_mul_of_nonneg_left hpow (mul_nonneg (by norm_num) hM)
  have henergy := localizedEnergy_le_of_gap_localMass k s I hIscale
    (integrable_smallestScaleInput S scale f (k - s))
    (A := 3 * M) (mul_nonneg (by norm_num) hM) hunit hcentral
  calc
    localizedEnergy k I (smallestScaleInput S scale f (k - s)) ≤
        (144 * positiveDyadicAmplitudeBound ^ 2 * (3 * M) *
          (2 : ℝ) ^ (-s)) *
          ∫ x in I.centralThird,
            ‖smallestScaleInput S scale f (k - s) x‖ := henergy
    _ = _ := by ring


end
end KrauseLaceyQuadraticDirectPartition
end QuadraticCarleson
