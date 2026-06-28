/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Union
import LeanPool.OrdvecFormalization.QuotientKernel

/-!
# Finite fiber topology

This file records the finite "clump" structure induced by a quotient map on a
sample: observed buckets, bucket fiber sizes, collisions, and the counting
relationship between a sample and its observed quotient image.
-/

namespace OrdvecFormalization

open scoped BigOperators

/-- Observed bucket fibers in a sample are pairwise disjoint. -/
theorem observedBucketFibers_pairwiseDisjoint {Ω Z : Type}
    [DecidableEq Z]
    (C : Ω → Z) (sample : Finset Ω) :
    Set.PairwiseDisjoint ↑(ObservedBuckets C sample)
      (fun z => sample.filter fun ω => C ω = z) := by
  intro z₁ _hz₁ z₂ _hz₂ hne
  exact Finset.disjoint_left.mpr (by
    intro ω hω₁ hω₂
    exact hne
      ((Finset.mem_filter.mp hω₁).2.symm.trans (Finset.mem_filter.mp hω₂).2))

/-- A sample is the disjoint union of its fibers over observed buckets. -/
theorem sample_eq_disjiUnion_fibers_over_observed {Ω Z : Type}
    [DecidableEq Z]
    (C : Ω → Z) (sample : Finset Ω) :
    (ObservedBuckets C sample).disjiUnion
        (fun z => sample.filter fun ω => C ω = z)
        (observedBucketFibers_pairwiseDisjoint C sample) =
      sample := by
  ext ω
  constructor
  · intro hω
    rcases Finset.mem_disjiUnion.mp hω with ⟨z, _hz, hωz⟩
    exact (Finset.mem_filter.mp hωz).1
  · intro hω
    exact Finset.mem_disjiUnion.mpr
      ⟨C ω, Finset.mem_image.mpr ⟨ω, hω, rfl⟩,
        Finset.mem_filter.mpr ⟨hω, rfl⟩⟩

/-- The sample cardinality is the sum of observed bucket fiber sizes. -/
theorem sample_card_eq_sum_fiberSize_observed {Ω Z : Type}
    [DecidableEq Z]
    (C : Ω → Z) (sample : Finset Ω) :
    sample.card = ∑ z ∈ ObservedBuckets C sample, FiberSize C sample z := by
  classical
  symm
  calc
    ∑ z ∈ ObservedBuckets C sample, FiberSize C sample z =
        ((ObservedBuckets C sample).disjiUnion
          (fun z => sample.filter fun ω => C ω = z)
          (observedBucketFibers_pairwiseDisjoint C sample)).card := by
      rw [Finset.card_disjiUnion]
      simp [FiberSize]
    _ = sample.card := by
      rw [sample_eq_disjiUnion_fibers_over_observed C sample]

/-- A sample has a collision iff the quotient map is not injective on it. -/
theorem hasCollision_iff_not_injectiveOnSample {Ω Z : Type}
    (C : Ω → Z) (sample : Finset Ω) :
    HasCollision C sample ↔ ¬ InjectiveOnSample C sample := by
  classical
  constructor
  · rintro ⟨ω₁, ω₂, hω₁, hω₂, hne, hC⟩ hinj
    exact hne (hinj hω₁ hω₂ hC)
  · intro hnot
    by_contra hnocoll
    exact hnot (by
      intro ω₁ ω₂ hω₁ hω₂ hC
      by_contra hne
      exact hnocoll ⟨ω₁, ω₂, hω₁, hω₂, hne, hC⟩)

/-- If the sample is larger than its observed quotient image, some sampled collision exists. -/
theorem hasCollision_of_card_gt_observedBuckets_card {Ω Z : Type}
    [DecidableEq Z]
    (C : Ω → Z) (sample : Finset Ω)
    (hcard : (ObservedBuckets C sample).card < sample.card) :
    HasCollision C sample := by
  classical
  by_contra hcollision
  have hinj : InjectiveOnSample C sample := by
    intro ω₁ ω₂ hω₁ hω₂ hC
    by_contra hne
    exact hcollision ⟨ω₁, ω₂, hω₁, hω₂, hne, hC⟩
  have hinjOn : Set.InjOn C (↑sample) := by
    intro ω₁ hω₁ ω₂ hω₂ hC
    exact hinj hω₁ hω₂ hC
  have himage : (ObservedBuckets C sample).card = sample.card :=
    Finset.card_image_of_injOn hinjOn
  rw [himage] at hcard
  exact Nat.lt_irrefl sample.card hcard

/--
Same-bucket label disagreement remains the finite sample falsifier for an
image/topology view of the quotient.
-/
theorem no_compatible_target_of_same_bucket_label_disagreement {Ω Z A : Type}
    (C : Ω → Z) (label : Ω → A) (sample : Finset Ω)
    {ω₁ ω₂ : Ω}
    (hω₁ : ω₁ ∈ sample) (hω₂ : ω₂ ∈ sample)
    (hC : C ω₁ = C ω₂)
    (hlabel : label ω₁ ≠ label ω₂) :
    ¬ ∃ target : Ω → A,
      QuotientCompatible C target ∧ FullTargetFitsSample label target sample :=
  no_compatible_target_of_sample_collision C label sample hω₁ hω₂ hC hlabel

end OrdvecFormalization
