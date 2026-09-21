/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyActiveCarlesonPacking

/-!
# Concrete overlap pruning of the actual active family

Intervals entirely inside the high-overlap set are removed. The retained
family has the literal pointwise overlap cap, proved from laminarity. The
exceptional-set estimate below is the proved first-moment bound; no
exponential John--Nirenberg tail is asserted.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction KrauseLaceyGenerationLayers

attribute [local instance] Classical.propDecidable

/-- The intervals containing at least one point where the overlap count is at most `M`. -/
noncomputable def overlapPrunedFamily (A : Finset RealInterval) (M : ℕ) :
    Finset RealInterval :=
  A.filter fun I ↦ ∃ x ∈ I.carrier, overlapCount A x ≤ M

theorem overlapPrunedFamily_subset (A : Finset RealInterval) (M : ℕ) :
    overlapPrunedFamily A M ⊆ A := Finset.filter_subset _ _

theorem removed_interval_subset_highOverlap
    {A : Finset RealInterval} {M : ℕ} {I : RealInterval}
    (hI : I ∈ A) (hremoved : I ∉ overlapPrunedFamily A M) :
    I.carrier ⊆ {x | M < overlapCount A x} := by
  intro x hx
  by_contra hn
  exact hremoved (Finset.mem_filter.mpr ⟨hI, x, hx, le_of_not_gt hn⟩)

/-- The retained overlap is genuinely bounded everywhere. A smallest
retained interval through a point transfers the whole covering chain to
its witness point of low original overlap. -/
theorem overlapCount_overlapPrunedFamily_le
    (A : Finset RealInterval) (M : ℕ)
    (hlam : Set.Pairwise (↑A : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (x : ℝ) : overlapCount (overlapPrunedFamily A M) x ≤ M := by
  let F := (overlapPrunedFamily A M).filter fun I ↦ x ∈ I.carrier
  change F.card ≤ M
  by_cases hempty : F = ∅
  · simp [hempty]
  obtain ⟨I, hI, hmin⟩ := F.exists_min_image RealInterval.length
    (Finset.nonempty_iff_ne_empty.mpr hempty)
  have hi := Finset.mem_filter.mp hI
  obtain ⟨y, hyI, hycount⟩ := (Finset.mem_filter.mp hi.1).2
  have hsub (J : RealInterval) (hJ : J ∈ F) : I.carrier ⊆ J.carrier := by
    by_cases heq : I = J
    · exact heq ▸ Subset.rfl
    have hj := Finset.mem_filter.mp hJ
    rcases hlam (Finset.mem_filter.mp hi.1).1 (Finset.mem_filter.mp hj.1).1 heq with
      h | h | hd
    · exact h
    · have he := interval_eq_of_carrier_subset_of_length_le h (hmin J hJ)
      exact he ▸ Subset.rfl
    · exact (Set.disjoint_left.mp hd hi.2 hj.2).elim
  have hFy : F ⊆ A.filter (fun J ↦ y ∈ J.carrier) := by
    intro J hJ
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hJ).1).1, hsub J hJ hyI⟩
  exact (Finset.card_le_card hFy).trans hycount

theorem overlapCount_cast_eq_sum_indicator (A : Finset RealInterval) (x : ℝ) :
    (overlapCount A x : ℝ≥0∞) =
      ∑ I ∈ A, I.carrier.indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
  simp only [overlapCount, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter, Set.indicator_apply]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs <;> norm_num

theorem measurable_overlapCount_cast (A : Finset RealInterval) :
    Measurable (fun x ↦ (overlapCount A x : ℝ≥0∞)) := by
  simp_rw [overlapCount_cast_eq_sum_indicator]
  exact Finset.measurable_sum _ fun I _ ↦ measurable_const.indicator I.measurableSet_carrier

theorem lintegral_overlapCount_cast (A : Finset RealInterval) :
    (∫⁻ x, (overlapCount A x : ℝ≥0∞)) = ENNReal.ofReal (∑ I ∈ A, I.length) := by
  simp_rw [overlapCount_cast_eq_sum_indicator]
  rw [lintegral_finsetSum _ (fun I _ ↦
    measurable_const.indicator I.measurableSet_carrier)]
  have heq (I : RealInterval) :
      (∫⁻ x, I.carrier.indicator (fun _ ↦ (1 : ℝ≥0∞)) x) = ENNReal.ofReal I.length := by
    rw [lintegral_indicator I.measurableSet_carrier]
    simp [RealInterval.volume_carrier]
  simp_rw [heq]
  exact (ENNReal.ofReal_sum_of_nonneg fun I _ ↦ I.length_pos.le).symm

/-- The exact first-moment exceptional-set bound. The stronger
exponential tail at the paper's cutoff is a separate remaining estimate. -/
theorem volume_highOverlap_le
    (A : Finset RealInterval) (M : ℕ) :
    volume {x | M < overlapCount A x} ≤
      ENNReal.ofReal (∑ I ∈ A, I.length) / (M + 1 : ℝ≥0∞) := by
  have h := meas_ge_le_lintegral_div (μ := volume) (measurable_overlapCount_cast A).aemeasurable
    (by positivity : (M + 1 : ℝ≥0∞) ≠ 0) (by simp : (M + 1 : ℝ≥0∞) ≠ ∞)
  rw [lintegral_overlapCount_cast] at h
  apply (measure_mono _).trans h
  intro x hx
  change M < overlapCount A x at hx
  change (M + 1 : ℝ≥0∞) ≤ (overlapCount A x : ℝ≥0∞)
  exact_mod_cast (show M + 1 ≤ overlapCount A x by omega)

theorem volume_active_highOverlap_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) (M : ℕ) :
    volume {x | M < overlapCount (activeBadIntervals S f I₀ k₀ s scale N) x} ≤
      ENNReal.ofReal ((1 + (2 : ℝ) ^ s) * K.length) / (M + 1 : ℝ≥0∞) := by
  apply (volume_highOverlap_le _ M).trans
  exact ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal
    (sum_activeBadIntervals_length_le f I₀ k₀ s scale hlam N hN K hsub)) _

/-- Outside the actual high-overlap exceptional set, pruning leaves
every fixed weighted operator sum unchanged. -/
theorem sum_weighted_localizedBadPiece_eq_pruned_of_lowOverlap
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval)
    (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale)
    (M : ℕ) (c : RealInterval → ℂ) (x : ℝ)
    (hx : overlapCount (activeBadIntervals S f I₀ k₀ s scale N) x ≤ M) :
    (∑ I ∈ N, c I * krauseLaceyLocalizedPiece 1 (scale I) I
      (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x) =
    ∑ I ∈ overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M,
      c I * krauseLaceyLocalizedPiece 1 (scale I) I
        (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x := by
  rw [sum_weighted_localizedBadPiece_eq_active]
  symm
  apply Finset.sum_subset (overlapPrunedFamily_subset _ M)
  intro I hI hn
  have hnot : x ∉ I.carrier := fun hxI ↦ hn (Finset.mem_filter.mpr ⟨hI, x, hxI, hx⟩)
  rw [krauseLaceyLocalizedPiece_eq_zero_of_notMem 1 (scale I) I _
    (Finset.mem_filter.mp (hN (Finset.mem_filter.mp hI).1)).2.1 hnot, mul_zero]

/-- The actual pruned family's maximal-prefix bound now has no assumed
overlap estimate: the concrete pruning construction supplies it. -/
theorem eLpNorm_prunedActivePrefixMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 3 ≤ k₀) (hs : 0 ≤ s)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale) (L M : ℕ) :
    eLpNorm (badSubcollectionPrefixMaximal S f I₀ k₀ s scale
      (overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M) L) 2 volume ≤
      ENNReal.ofReal ((Nat.log2 M + 1 : ℝ) *
        Real.sqrt (nonstandardSignedEnergyBudget f I₀ s)) := by
  have hAS := (activeBadIntervals_subset S f I₀ k₀ s scale N).trans
    (hN.trans (nonstandardIntervals_subset S f I₀ k₀ s scale))
  apply eLpNorm_badSubcollectionPrefixMaximal_le_of_ae_overlapCount_le hf I₀ k₀ s hk₀ hs
    scale hlam hparent hsub _
    ((overlapPrunedFamily_subset _ M).trans
      ((activeBadIntervals_subset S f I₀ k₀ s scale N).trans hN)) L M
  exact Filter.Eventually.of_forall (overlapCount_overlapPrunedFamily_le _ M
    (fun I hI J hJ hne ↦ hlam (hAS hI) (hAS hJ) hne))


end KrauseLaceyBadScale
end QuadraticCarleson
