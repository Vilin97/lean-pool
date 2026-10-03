/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyOverlapStopping

/-!
# Exponential overlap decay from finite Carleson packing

A direct finite laminar-tree proof. No BMO or John--Nirenberg estimate is
assumed: one-step Markov bounds and the maximal removed-interval geometry
are iterated on actual descendant families.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction KrauseLaceyGenerationLayers

attribute [local instance] Classical.propDecidable

theorem sum_volume_overlapStoppingIntervals
    (A : Finset RealInterval) (M : ℕ)
    (hlam : Set.Pairwise (↑A : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier) :
    (∑ I ∈ overlapStoppingIntervals A M, ENNReal.ofReal I.length) =
      volume {x | M < overlapCount A x} := by
  rw [highOverlap_eq_biUnion_overlapStoppingIntervals A M hlam,
    measure_biUnion_finset (overlapStoppingIntervals_pairwiseDisjoint A M hlam)
      (fun I _ ↦ I.measurableSet_carrier)]
  simp only [RealInterval.volume_carrier]

/-- Subfamilies inherit the literal local Carleson packing bound. -/
theorem local_length_packing_mono
    {A B : Finset RealInterval} {Λ : ℝ} (hBA : B ⊆ A)
    (hpack : ∀ K : RealInterval,
      (∑ I ∈ A.filter (fun I ↦ I.carrier ⊆ K.carrier), I.length) ≤ Λ * K.length) :
    ∀ K : RealInterval,
      (∑ I ∈ B.filter (fun I ↦ I.carrier ⊆ K.carrier), I.length) ≤ Λ * K.length := by
  intro K
  apply le_trans _ (hpack K)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ hBA)
    (fun I _ _ ↦ I.length_pos.le)

/-- Finite John--Nirenberg in exact block form. The ratio is the actual
Carleson constant divided by the block length. -/
theorem volume_overlap_blocks_le
    (t : ℕ) (A : Finset RealInterval) (K : RealInterval) (M : ℕ) (Λ : ℝ)
    (hlam : Set.Pairwise (↑A : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hsub : ∀ I ∈ A, I.carrier ⊆ K.carrier)
    (hpack : ∀ J : RealInterval,
      (∑ I ∈ A.filter (fun I ↦ I.carrier ⊆ J.carrier), I.length) ≤ Λ * J.length) :
    volume {x | t * (M + 1) < overlapCount A x} ≤
      (ENNReal.ofReal Λ / (M + 1 : ℝ≥0∞)) ^ t * ENNReal.ofReal K.length := by
  induction t generalizing A K with
  | zero =>
    simp only [Nat.zero_mul, pow_zero, one_mul]
    rw [← K.volume_carrier]
    apply measure_mono
    intro x hx
    change 0 < (A.filter fun I ↦ x ∈ I.carrier).card at hx
    obtain ⟨I, hI⟩ := Finset.card_pos.mp hx
    have hi := Finset.mem_filter.mp hI
    exact hsub I hi.1 hi.2
  | succ t ih =>
    let C := overlapStoppingIntervals A M
    let D := fun I : RealInterval ↦ A.filter fun J ↦ J.carrier ⊆ I.carrier
    have hdeep : {x | (t + 1) * (M + 1) < overlapCount A x} ⊆
        ⋃ I ∈ C, {x | t * (M + 1) < overlapCount (D I) x} := by
      intro x hx
      change (t + 1) * (M + 1) < overlapCount A x at hx
      have hxM : M < overlapCount A x := by nlinarith
      obtain ⟨I, hI⟩ := Set.mem_iUnion.mp
        (highOverlap_subset_biUnion_overlapStoppingIntervals A M hlam hxM)
      obtain ⟨hIC, hxI⟩ := Set.mem_iUnion.mp hI
      refine Set.mem_iUnion.mpr ⟨I, Set.mem_iUnion.mpr ⟨hIC, ?_⟩⟩
      have hc := overlapCount_le_descendants_add_of_mem_overlapStoppingIntervals hlam hIC hxI
      change t * (M + 1) < overlapCount (D I) x
      dsimp only [D]
      nlinarith
    have hmass : (∑ I ∈ C, ENNReal.ofReal I.length) ≤
        (ENNReal.ofReal Λ / (M + 1 : ℝ≥0∞)) * ENNReal.ofReal K.length := by
      rw [sum_volume_overlapStoppingIntervals A M hlam]
      apply (volume_highOverlap_le A M).trans
      have hall : A.filter (fun I ↦ I.carrier ⊆ K.carrier) = A :=
        Finset.filter_eq_self.mpr hsub
      have hp := hpack K
      rw [hall] at hp
      calc
        ENNReal.ofReal (∑ I ∈ A, I.length) / (M + 1 : ℝ≥0∞) ≤
            ENNReal.ofReal (Λ * K.length) / (M + 1 : ℝ≥0∞) :=
          ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal hp) _
        _ = (ENNReal.ofReal Λ / (M + 1 : ℝ≥0∞)) * ENNReal.ofReal K.length := by
          rw [ENNReal.ofReal_mul' K.length_pos.le]
          simp only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    calc
      volume {x | (t + 1) * (M + 1) < overlapCount A x} ≤
          volume (⋃ I ∈ C, {x | t * (M + 1) < overlapCount (D I) x}) := measure_mono hdeep
      _ ≤ ∑ I ∈ C, volume {x | t * (M + 1) < overlapCount (D I) x} :=
        measure_biUnion_finset_le _ _
      _ ≤ ∑ I ∈ C, (ENNReal.ofReal Λ / (M + 1 : ℝ≥0∞)) ^ t *
          ENNReal.ofReal I.length := by
        apply Finset.sum_le_sum
        intro I hI
        apply ih (D I) I
        · exact fun J hJ L hL hne ↦ hlam (Finset.mem_filter.mp hJ).1
            (Finset.mem_filter.mp hL).1 hne
        · exact fun J hJ ↦ (Finset.mem_filter.mp hJ).2
        · exact local_length_packing_mono (Finset.filter_subset _ _) hpack
      _ = (ENNReal.ofReal Λ / (M + 1 : ℝ≥0∞)) ^ t *
          (∑ I ∈ C, ENNReal.ofReal I.length) := (Finset.mul_sum _ _ _).symm
      _ ≤ (ENNReal.ofReal Λ / (M + 1 : ℝ≥0∞)) ^ t *
          ((ENNReal.ofReal Λ / (M + 1 : ℝ≥0∞)) * ENNReal.ofReal K.length) :=
        mul_le_mul_right hmass _
      _ = (ENNReal.ofReal Λ / (M + 1 : ℝ≥0∞)) ^ (t + 1) *
          ENNReal.ofReal K.length := by rw [pow_succ, mul_assoc]

/-- The usual dyadic exponential decay, with an explicit block-size
condition and no analytic overlap hypothesis. -/
theorem volume_overlap_blocks_le_half_pow
    (t : ℕ) (A : Finset RealInterval) (K : RealInterval) (M : ℕ) (Λ : ℝ)
    (hblock : 2 * Λ ≤ M + 1)
    (hlam : Set.Pairwise (↑A : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hsub : ∀ I ∈ A, I.carrier ⊆ K.carrier)
    (hpack : ∀ J : RealInterval,
      (∑ I ∈ A.filter (fun I ↦ I.carrier ⊆ J.carrier), I.length) ≤ Λ * J.length) :
    volume {x | t * (M + 1) < overlapCount A x} ≤
      (1 / 2 : ℝ≥0∞) ^ t * ENNReal.ofReal K.length := by
  apply (volume_overlap_blocks_le t A K M Λ hlam hsub hpack).trans
  have hratio : ENNReal.ofReal Λ / (M + 1 : ℝ≥0∞) ≤ 1 / 2 := by
    have hpos : (0 : ℝ) < M + 1 := by positivity
    have hr : Λ / (M + 1) ≤ 1 / 2 := (div_le_iff₀ hpos).mpr (by linarith)
    have he : (M + 1 : ℝ≥0∞) = ENNReal.ofReal (M + 1 : ℝ) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    rw [he, ← ENNReal.ofReal_div_of_pos hpos]
    exact (ENNReal.ofReal_le_ofReal hr).trans_eq (by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num)
  exact mul_le_mul_left (pow_le_pow_left' hratio t) _


end KrauseLaceyBadScale
end QuadraticCarleson
