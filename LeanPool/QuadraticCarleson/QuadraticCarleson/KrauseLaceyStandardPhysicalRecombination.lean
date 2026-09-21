/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyStandardSourceInterpolation
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyPrunedPhysicalMaximal

/-!
# Exact physical-scale recombination of the scalar-standard collection

The scalar-standard estimates are proved at one physical exponent `j`, with
the source gap in the exact interval `0 ≤ s ≤ j - k₀`. This file supplies
the finite algebraic bridge from the original standard collections (one for
each gap) to those fixed-`j` estimates.

The outer tail condition is never reversed: a lower physical cutoff `ell`
retains precisely the layers with `ell ≤ j`. We also record the change of
variables `ℓ = j - s`, under which the source-gap interval becomes exactly
`k₀ ≤ ℓ ≤ j`.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

attribute [local instance] Classical.propDecidable

/-- The finite set of physical exponents represented by the ambient interval
family. The exponent is `scale I + 2`, matching the actual length relation
used throughout the scalar energy classification. -/
noncomputable def standardPhysicalScaleSupport
    (S : Finset RealInterval) (scale : RealInterval → ℤ) : Finset ℤ :=
  S.image fun I ↦ scale I + 2

/-- The scalar-standard part at gap `s` and one exact physical exponent `j`. -/
noncomputable def energyStandardPhysicalLayer
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (j : ℤ) : Finset RealInterval :=
  (energyStandardIntervals S f I₀ k₀ s scale).filter fun I ↦ scale I + 2 = j

theorem energyStandardPhysicalLayer_subset
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (j : ℤ) :
    energyStandardPhysicalLayer S f I₀ k₀ s scale j ⊆
      energyStandardIntervals S f I₀ k₀ s scale :=
  Finset.filter_subset _ _

theorem physical_eq_of_mem_energyStandardPhysicalLayer
    {S : Finset RealInterval} {f : ℝ → ℂ} {I₀ : RealInterval} {k₀ s : ℤ}
    {scale : RealInterval → ℤ} {j : ℤ} {I : RealInterval}
    (hI : I ∈ energyStandardPhysicalLayer S f I₀ k₀ s scale j) :
    scale I + 2 = j :=
  (Finset.mem_filter.mp hI).2

theorem length_eq_zpow_of_mem_energyStandardPhysicalLayer
    {S : Finset RealInterval} {f : ℝ → ℂ} {I₀ : RealInterval} {k₀ s : ℤ}
    {scale : RealInterval → ℤ} {j : ℤ} {I : RealInterval}
    (hI : I ∈ energyStandardPhysicalLayer S f I₀ k₀ s scale j) :
    I.length = (2 : ℝ) ^ j := by
  have he := Finset.mem_filter.mp (Finset.mem_filter.mp
    (energyStandardPhysicalLayer_subset S f I₀ k₀ s scale j hI)).1
  rw [he.2.1, physical_eq_of_mem_energyStandardPhysicalLayer hI]

/-- Membership in the source-gap set, in the additive form most convenient
for preserving the lower physical scale `k₀ + s`. -/
theorem mem_standardSourceGaps_iff {k₀ j s : ℤ} :
    s ∈ standardSourceGaps k₀ j ↔ 0 ≤ s ∧ k₀ + s ≤ j := by
  simp only [standardSourceGaps, Finset.mem_Icc]
  omega

/-- An inhabited standard layer with a nonnegative gap automatically lies in
the paper's exact source-gap range. -/
theorem mem_standardSourceGaps_of_mem_energyStandardPhysicalLayer
    {S : Finset RealInterval} {f : ℝ → ℂ} {I₀ : RealInterval} {k₀ s j : ℤ}
    {scale : RealInterval → ℤ} {I : RealInterval} (hs : 0 ≤ s)
    (hI : I ∈ energyStandardPhysicalLayer S f I₀ k₀ s scale j) :
    s ∈ standardSourceGaps k₀ j := by
  rw [mem_standardSourceGaps_iff]
  refine ⟨hs, ?_⟩
  have he := Finset.mem_filter.mp (energyStandardPhysicalLayer_subset
    S f I₀ k₀ s scale j hI)
  have hgap := (Finset.mem_filter.mp he.1).2.2
  have hj := physical_eq_of_mem_energyStandardPhysicalLayer hI
  omega

/-- Hence a nonnegative gap outside `0 ≤ s ≤ j-k₀` contributes no
interval at physical exponent `j`. -/
theorem energyStandardPhysicalLayer_eq_empty_of_nonneg_not_mem
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s j : ℤ)
    (scale : RealInterval → ℤ) (hs : 0 ≤ s)
    (hsj : s ∉ standardSourceGaps k₀ j) :
    energyStandardPhysicalLayer S f I₀ k₀ s scale j = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro I hI
  exact hsj (mem_standardSourceGaps_of_mem_energyStandardPhysicalLayer hs hI)

/-- Every scalar-standard collection at a fixed gap is exactly the disjoint
sum of its physical layers. The target scale set is finite because it is the
image of the ambient finite interval family. -/
theorem sum_energyStandardPhysicalLayer_eq
    {E : Type*} [AddCommMonoid E]
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (v : RealInterval → E) :
    (∑ j ∈ standardPhysicalScaleSupport S scale,
      ∑ I ∈ energyStandardPhysicalLayer S f I₀ k₀ s scale j, v I) =
      ∑ I ∈ energyStandardIntervals S f I₀ k₀ s scale, v I := by
  unfold energyStandardPhysicalLayer standardPhysicalScaleSupport
  exact Finset.sum_fiberwise_of_maps_to
    (fun I hI ↦ Finset.mem_image.mpr ⟨I,
      energyEligibleIntervals_subset S f I₀ k₀ s scale
        (Finset.mem_filter.mp hI).1, rfl⟩) _

/-- The power cutoff on an eligible standard interval is exactly the lower
cutoff on its physical exponent. -/
theorem zpow_cutoff_iff_of_mem_energyStandardIntervals
    {S : Finset RealInterval} {f : ℝ → ℂ} {I₀ : RealInterval} {k₀ s ell : ℤ}
    {scale : RealInterval → ℤ} {I : RealInterval}
    (hI : I ∈ energyStandardIntervals S f I₀ k₀ s scale) :
    (2 : ℝ) ^ ell ≤ I.length ↔ ell ≤ scale I + 2 := by
  have he := Finset.mem_filter.mp (Finset.mem_filter.mp hI).1
  rw [he.2.1]
  exact zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)

/-- Exact physical-layer recombination with a moving lower cutoff. The
orientation is `ell ≤ j`: large spatial scales survive the tail. -/
theorem sum_energyStandardPhysicalLayer_tail_eq
    {E : Type*} [AddCommMonoid E]
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s ell : ℤ)
    (scale : RealInterval → ℤ) (v : RealInterval → E) :
    (∑ j ∈ (standardPhysicalScaleSupport S scale).filter fun j ↦ ell ≤ j,
      ∑ I ∈ energyStandardPhysicalLayer S f I₀ k₀ s scale j, v I) =
      ∑ I ∈ energyStandardIntervals S f I₀ k₀ s scale,
        if ell ≤ scale I + 2 then v I else 0 := by
  rw [← Finset.sum_filter]
  let A := (energyStandardIntervals S f I₀ k₀ s scale).filter
    fun I ↦ ell ≤ scale I + 2
  let T := (standardPhysicalScaleSupport S scale).filter fun j ↦ ell ≤ j
  have hmaps : (A : Set RealInterval).MapsTo (fun I ↦ scale I + 2) T := by
    intro I hI
    have hIA := Finset.mem_filter.mp hI
    apply Finset.mem_filter.mpr
    refine ⟨?_, hIA.2⟩
    exact Finset.mem_image.mpr ⟨I,
      energyEligibleIntervals_subset S f I₀ k₀ s scale
        (Finset.mem_filter.mp hIA.1).1, rfl⟩
  change (∑ j ∈ T,
      ∑ I ∈ energyStandardPhysicalLayer S f I₀ k₀ s scale j, v I) =
    ∑ I ∈ A, v I
  calc
    _ = ∑ j ∈ T, ∑ I ∈ A.filter (fun I ↦ scale I + 2 = j), v I := by
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      ext I
      have hellj := (Finset.mem_filter.mp hj).2
      simp only [A, energyStandardPhysicalLayer, Finset.mem_filter]
      constructor
      · rintro ⟨hI, hIj⟩
        exact ⟨⟨hI, hIj.symm ▸ hellj⟩, hIj⟩
      · rintro ⟨⟨hI, hcut⟩, hIj⟩
        exact ⟨hI, hIj⟩
    _ = _ := Finset.sum_fiberwise_of_maps_to hmaps _

/-- The preceding abstract recombination specializes to the actual localized
standard tail at one gap. -/
theorem badLengthTailAction_energyStandardIntervals_eq_physicalLayers
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (ell : ℤ) (x : ℝ) :
    badLengthTailAction S f I₀ k₀ s scale
        (energyStandardIntervals S f I₀ k₀ s scale) ell x =
      ∑ j ∈ (standardPhysicalScaleSupport S scale).filter fun j ↦ ell ≤ j,
        ∑ I ∈ energyStandardPhysicalLayer S f I₀ k₀ s scale j,
          krauseLaceyLocalizedPiece 1 (scale I) I
            (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x := by
  unfold badLengthTailAction
  calc
    _ = ∑ I ∈ energyStandardIntervals S f I₀ k₀ s scale,
        if ell ≤ scale I + 2 then
          krauseLaceyLocalizedPiece 1 (scale I) I
            (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x else 0 := by
      apply Finset.sum_congr rfl
      intro I hI
      by_cases hcut : (2 : ℝ) ^ ell ≤ I.length
      · have hcut' := (zpow_cutoff_iff_of_mem_energyStandardIntervals hI).mp hcut
        rw [ite_eq_left hcut, ite_eq_left hcut']
      · have hcut' : ¬ ell ≤ scale I + 2 :=
          mt (zpow_cutoff_iff_of_mem_energyStandardIntervals hI).mpr hcut
        rw [ite_eq_right hcut, ite_eq_right hcut']
    _ = _ := (sum_energyStandardPhysicalLayer_tail_eq S f I₀ k₀ s ell scale
      (fun I ↦ krauseLaceyLocalizedPiece 1 (scale I) I
        (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x)).symm

/-- At one physical exponent, use all and only the source gaps allowed by
`k₀ ≤ j-s`. This is the actual fixed-scale action to which the interpolation
theorems apply. -/
noncomputable def energyStandardPhysicalLayerAction
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ)
    (scale : RealInterval → ℤ) (j : ℤ) (x : ℝ) : ℂ :=
  energyStandardFixedPhysicalSourceAction S f I₀ k₀ scale
    (standardSourceGaps k₀ j)
    (fun s ↦ energyStandardPhysicalLayer S f I₀ k₀ s scale j) x

/-- The fixed-scale interpolation theorem applies directly to the exact
physical layers, with no extra selection hypotheses. -/
theorem eLpNorm_energyStandardPhysicalLayerAction_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ j : ℤ) (hk₀ : 1 ≤ k₀) (hk₀j : k₀ ≤ j)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier) {q : ℝ} (hq : 2 ≤ q) :
    eLpNorm (energyStandardPhysicalLayerAction S f I₀ k₀ scale j)
        (ENNReal.ofReal q) volume ≤
      (ENNReal.ofReal
          ((80 * positiveDyadicAmplitudeBound * intervalL1Average f I₀) ^ (q - 2)) *
        ENNReal.ofReal ((j : ℝ) *
          ((2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ /
            (2 : ℝ) ^ j) * ∫ x, ‖f x‖))) ^ (1 / q) := by
  exact eLpNorm_energyStandardFixedPhysicalSourceAction_le_j_mul
    hf I₀ k₀ j hk₀ hk₀j scale hlam hsub
    (fun s ↦ energyStandardPhysicalLayer S f I₀ k₀ s scale j)
    (fun s _ ↦ energyStandardPhysicalLayer_subset S f I₀ k₀ s scale j)
    (fun _ _ I hI ↦ physical_eq_of_mem_energyStandardPhysicalLayer hI) hq

/-- Reversing the gap coordinate sends `0 ≤ s ≤ j-k₀` bijectively to
the original bad-input exponent range `k₀ ≤ ℓ ≤ j`. -/
theorem sum_standardSourceGaps_eq_sum_sourceLevels
    {E : Type*} [AddCommMonoid E] (k₀ j : ℤ) (F : ℤ → ℤ → E) :
    (∑ s ∈ standardSourceGaps k₀ j, F s (j - s)) =
      ∑ ell ∈ Finset.Icc k₀ j, F (j - ell) ell := by
  apply Finset.sum_bij (fun s _ ↦ j - s)
  · intro s hs
    rw [mem_standardSourceGaps_iff] at hs
    simp only [Finset.mem_Icc]
    omega
  · intro s₁ hs₁ s₂ hs₂ h
    omega
  · intro ell hell
    refine ⟨j - ell, ?_, by omega⟩
    rw [mem_standardSourceGaps_iff]
    simp only [Finset.mem_Icc] at hell
    omega
  · intro s hs
    congr 1
    omega

/-- Fixed physical action written with the original bad-input exponent
`ℓ ∈ [k₀,j]`, rather than the gap `s = j-ℓ`. -/
theorem energyStandardPhysicalLayerAction_eq_sourceLevels
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ)
    (scale : RealInterval → ℤ) (j : ℤ) (x : ℝ) :
    energyStandardPhysicalLayerAction S f I₀ k₀ scale j x =
      ∑ ell ∈ Finset.Icc k₀ j,
        ∑ I ∈ energyStandardPhysicalLayer S f I₀ k₀ (j - ell) scale j,
          krauseLaceyLocalizedPiece 1 (scale I) I
            (badScaleInput S f I₀ k₀ ell) x := by
  unfold energyStandardPhysicalLayerAction energyStandardFixedPhysicalSourceAction
  calc
    _ = ∑ s ∈ standardSourceGaps k₀ j,
        ∑ I ∈ energyStandardPhysicalLayer S f I₀ k₀ s scale j,
          krauseLaceyLocalizedPiece 1 (scale I) I
            (badScaleInput S f I₀ k₀ (j - s)) x := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro I hI
      rw [physical_eq_of_mem_energyStandardPhysicalLayer hI]
    _ = _ := sum_standardSourceGaps_eq_sum_sourceLevels k₀ j
      (fun s ell ↦ ∑ I ∈ energyStandardPhysicalLayer S f I₀ k₀ s scale j,
        krauseLaceyLocalizedPiece 1 (scale I) I (badScaleInput S f I₀ k₀ ell) x)

/-- All nonnegative gap indices represented by at least one physical scale
of the ambient finite family. -/
noncomputable def standardSourceGapSupport
    (S : Finset RealInterval) (k₀ : ℤ) (scale : RealInterval → ℤ) : Finset ℤ :=
  (standardPhysicalScaleSupport S scale).biUnion fun j ↦ standardSourceGaps k₀ j

theorem nonneg_of_mem_standardSourceGapSupport
    {S : Finset RealInterval} {k₀ s : ℤ} {scale : RealInterval → ℤ}
    (hs : s ∈ standardSourceGapSupport S k₀ scale) : 0 ≤ s := by
  obtain ⟨j, hj, hsj⟩ := Finset.mem_biUnion.mp hs
  exact (mem_standardSourceGaps_iff.mp hsj).1

/-- The complete finite scalar-standard tail, presented in the fixed
physical-scale order required by the source estimates. -/
noncomputable def energyStandardPhysicalTailAction
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ)
    (scale : RealInterval → ℤ) (ell : ℤ) (x : ℝ) : ℂ :=
  ∑ j ∈ (standardPhysicalScaleSupport S scale).filter fun j ↦ ell ≤ j,
    energyStandardPhysicalLayerAction S f I₀ k₀ scale j x

/-- Exact global recombination: summing the original standard physical tails
over every represented nonnegative gap equals summing first by physical
exponent. The right side therefore has exactly the fixed-`j` functions used
by the source interpolation estimate. -/
theorem sum_badLengthTailAction_energyStandardIntervals_eq_physicalTail
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ)
    (scale : RealInterval → ℤ) (ell : ℤ) (x : ℝ) :
    (∑ s ∈ standardSourceGapSupport S k₀ scale,
      badLengthTailAction S f I₀ k₀ s scale
        (energyStandardIntervals S f I₀ k₀ s scale) ell x) =
      energyStandardPhysicalTailAction S f I₀ k₀ scale ell x := by
  let P := (standardPhysicalScaleSupport S scale).filter fun j ↦ ell ≤ j
  let G := standardSourceGapSupport S k₀ scale
  let V (s j : ℤ) : ℂ :=
    ∑ I ∈ energyStandardPhysicalLayer S f I₀ k₀ s scale j,
      krauseLaceyLocalizedPiece 1 (scale I) I
        (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x
  calc
    _ = ∑ s ∈ G, ∑ j ∈ P, V s j := by
      apply Finset.sum_congr rfl
      intro s hs
      exact badLengthTailAction_energyStandardIntervals_eq_physicalLayers
        S f I₀ k₀ s scale ell x
    _ = ∑ j ∈ P, ∑ s ∈ G, V s j := by rw [Finset.sum_comm]
    _ = ∑ j ∈ P, ∑ s ∈ standardSourceGaps k₀ j, V s j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjscale : j ∈ standardPhysicalScaleSupport S scale :=
        (Finset.mem_filter.mp hj).1
      have hsub : standardSourceGaps k₀ j ⊆ G := by
        intro s hs
        exact Finset.mem_biUnion.mpr ⟨j, hjscale, hs⟩
      symm
      apply Finset.sum_subset hsub
      intro s hsG hsnot
      have hs0 := nonneg_of_mem_standardSourceGapSupport hsG
      change (∑ I ∈ energyStandardPhysicalLayer S f I₀ k₀ s scale j,
        krauseLaceyLocalizedPiece 1 (scale I) I
          (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x) = 0
      rw [energyStandardPhysicalLayer_eq_empty_of_nonneg_not_mem
        S f I₀ k₀ s j scale hs0 hsnot]
      simp
    _ = _ := by
      unfold energyStandardPhysicalTailAction energyStandardPhysicalLayerAction
      exact Finset.sum_congr rfl fun j _ ↦ rfl

/-- The global physical-tail recombination with both indices in the literal
source orientation: `ell ≤ j` outside and `k₀ ≤ ℓ ≤ j` inside. -/
theorem energyStandardPhysicalTailAction_eq_sourceLevels
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ)
    (scale : RealInterval → ℤ) (ell : ℤ) (x : ℝ) :
    energyStandardPhysicalTailAction S f I₀ k₀ scale ell x =
      ∑ j ∈ (standardPhysicalScaleSupport S scale).filter fun j ↦ ell ≤ j,
        ∑ sourceLevel ∈ Finset.Icc k₀ j,
          ∑ I ∈ energyStandardPhysicalLayer
              S f I₀ k₀ (j - sourceLevel) scale j,
            krauseLaceyLocalizedPiece 1 (scale I) I
              (badScaleInput S f I₀ k₀ sourceLevel) x := by
  unfold energyStandardPhysicalTailAction
  apply Finset.sum_congr rfl
  intro j hj
  exact energyStandardPhysicalLayerAction_eq_sourceLevels S f I₀ k₀ scale j x


end KrauseLaceyBadScale
end QuadraticCarleson
