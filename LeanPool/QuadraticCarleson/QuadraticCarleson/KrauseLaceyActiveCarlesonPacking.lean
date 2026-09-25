/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyActiveBadIntervals

/-!
# Carleson length packing for the genuine active nonstandard family

Every interval above the grouped base scale is charged to a contained
selected bad cell, with exact length ratio `2^s`. No cell can be charged
twice. The grouped base scale is handled separately by disjointness.
-/

@[expose] public section

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction

attribute [local instance] Classical.propDecidable

theorem eq_of_common_subinterval_of_length_eq
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    {I J K : RealInterval} (hI : I ∈ S) (hJ : J ∈ S)
    (hlen : I.length = J.length)
    (hKI : K.carrier ⊆ I.carrier) (hKJ : K.carrier ⊆ J.carrier) : I = J := by
  by_contra hne
  rcases hlam hI hJ hne with hsub | hsub | hd
  · exact hne (interval_eq_of_carrier_subset_of_length_le hsub hlen.ge)
  · exact hne (interval_eq_of_carrier_subset_of_length_le hsub hlen.le).symm
  · exact Set.disjoint_left.mp hd (hKI ⟨K.left_lt_right, le_rfl⟩)
      (hKJ ⟨K.left_lt_right, le_rfl⟩)

/-- All active intervals above the grouped base scale satisfy the exact
local `2^s` packing estimate, uniformly over arbitrary subcollections. -/
theorem sum_active_aboveBase_length_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale)
    (hactive : ∀ I ∈ N, ∃ x, intervalBadInput S f I₀ k₀ s scale I x ≠ 0)
    (hbase : ∀ I ∈ N, k₀ < scale I + 2 - s)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) :
    (∑ I ∈ N, I.length) ≤ (2 : ℝ) ^ s * K.length := by
  let : Nonempty RealInterval := ⟨I₀⟩
  have hex (I : RealInterval) (hI : I ∈ N) :=
    exists_chargedCell_of_active_above_base f I₀ k₀ s scale hlam (hN hI)
      (hbase I hI) (hactive I hI)
  choose! cell hcell hinside hlength using hex
  let C := (stoppingChildren S f 0 I₀).filter fun J ↦ J.carrier ⊆ K.carrier
  have hCS : Set.Pairwise (↑C) (Disjoint on RealInterval.carrier) := by
    intro I hI J hJ hne
    exact stoppingChildren_pairwiseDisjoint f 0 I₀ hlam
      (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hJ).1 hne
  have hinj : Set.InjOn cell (↑N : Set RealInterval) := by
    intro I hI J hJ heq
    have hlen : I.length = J.length := by rw [hlength I hI, hlength J hJ, heq]
    exact eq_of_common_subinterval_of_length_eq hlam
      (nonstandardIntervals_subset S f I₀ k₀ s scale (hN hI))
      (nonstandardIntervals_subset S f I₀ k₀ s scale (hN hJ)) hlen
      (hinside I hI) (heq ▸ hinside J hJ)
  have hmap : N.image cell ⊆ C := by
    intro J hJ
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
    exact Finset.mem_filter.mpr ⟨hcell I hI, (hinside I hI).trans (hsub I hI)⟩
  calc
    _ ≤ ∑ J ∈ C, (2 : ℝ) ^ s * J.length :=
      Finset.sum_le_sum_of_injOn cell hinj hmap
        (fun I hI ↦ (hlength I hI).le) (fun J _ _ ↦ by positivity [J.length_pos])
    _ = (2 : ℝ) ^ s * ∑ J ∈ C, J.length := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_intervalLength_le_of_disjoint C K hCS
        (fun J hJ ↦ (Finset.mem_filter.mp hJ).2)) (by positivity)

/-- The base-scale pieces have one fixed parent length, so laminarity
alone makes them disjoint. Tiny stopping cells are not charged their
parent's length in this exceptional grouped scale. -/
theorem sum_baseScale_length_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale)
    (hbase : ∀ I ∈ N, scale I + 2 - s ≤ k₀)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) :
    (∑ I ∈ N, I.length) ≤ K.length := by
  apply sum_intervalLength_le_of_disjoint N K _ hsub
  intro I hI J hJ hne
  have hi := (Finset.mem_filter.mp (hN hI)).2
  have hj := (Finset.mem_filter.mp (hN hJ)).2
  have hidx : scale I = scale J := by have := hbase I hI; have := hbase J hJ; omega
  have hlen : I.length = J.length := by rw [hi.1, hj.1, hidx]
  have hNS := nonstandardIntervals_subset S f I₀ k₀ s scale
  rcases hlam (hNS (hN hI)) (hNS (hN hJ)) hne with hsub | hsub | hd
  · exact (hne (interval_eq_of_carrier_subset_of_length_le hsub hlen.ge)).elim
  · exact (hne (interval_eq_of_carrier_subset_of_length_le hsub hlen.le).symm).elim
  · exact hd

/-- The genuine active family is Carleson with constant `1 + 2^s`.
Neither a packing estimate nor an operator bound is an input. -/
theorem sum_activeBadIntervals_length_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) :
    (∑ I ∈ activeBadIntervals S f I₀ k₀ s scale N, I.length) ≤
      (1 + (2 : ℝ) ^ s) * K.length := by
  let A := activeBadIntervals S f I₀ k₀ s scale N
  have hAN := activeBadIntervals_subset S f I₀ k₀ s scale N
  have hfar := sum_active_aboveBase_length_le f I₀ k₀ s scale hlam
    (A.filter fun I ↦ k₀ < scale I + 2 - s)
    ((Finset.filter_subset _ A).trans (hAN.trans hN))
    (fun I hI ↦ (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2)
    (fun I hI ↦ (Finset.mem_filter.mp hI).2) K
    (fun I hI ↦ hsub I (hAN (Finset.mem_filter.mp hI).1))
  have hnear := sum_baseScale_length_le f I₀ k₀ s scale hlam
    (A.filter fun I ↦ ¬ k₀ < scale I + 2 - s)
    ((Finset.filter_subset _ A).trans (hAN.trans hN))
    (fun I hI ↦ le_of_not_gt (Finset.mem_filter.mp hI).2) K
    (fun I hI ↦ hsub I (hAN (Finset.mem_filter.mp hI).1))
  have heq := Finset.sum_filter_add_sum_filter_not A
    (fun I ↦ k₀ < scale I + 2 - s) RealInterval.length
  dsimp only [A] at heq
  linarith

/-- Local Carleson packing in the form used by overlap pruning. -/
theorem sum_activeBadIntervals_descendants_length_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale)
    (K : RealInterval) :
    (∑ I ∈ (activeBadIntervals S f I₀ k₀ s scale N).filter
      (fun I ↦ I.carrier ⊆ K.carrier), I.length) ≤ (1 + (2 : ℝ) ^ s) * K.length := by
  have heq : (activeBadIntervals S f I₀ k₀ s scale N).filter
      (fun I ↦ I.carrier ⊆ K.carrier) =
      activeBadIntervals S f I₀ k₀ s scale (N.filter fun I ↦ I.carrier ⊆ K.carrier) := by
    ext I
    simp only [activeBadIntervals, Finset.mem_filter, and_assoc, and_left_comm, and_comm]
  rw [heq]
  exact sum_activeBadIntervals_length_le f I₀ k₀ s scale hlam _
    ((Finset.filter_subset _ N).trans hN) K (fun I hI ↦ (Finset.mem_filter.mp hI).2)


end KrauseLaceyBadScale
end QuadraticCarleson
