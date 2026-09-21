/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Compact exhaustions of open subsets

## Main results

* `IsOpen.exists_compact_exhaustion`: An open subset of a locally compact, second-countable
  topological space has an increasing sequence of compact subsets containing every compact
  subset of the open set in some term. The construction uses `CompactExhaustion.choice` on
  the open subtype and maps its terms into the ambient space.

In particular, the result applies to open subsets of proper metric spaces. No norm, group
structure, or nonemptiness assumption is needed.
-/

public section

open Set

/-- An open subset of a locally compact, second-countable space has an increasing compact
exhaustion containing each compact subset in some term. -/
theorem IsOpen.exists_compact_exhaustion {E : Type*} [TopologicalSpace E]
    [LocallyCompactSpace E] [SecondCountableTopology E] {U : Set E} (hU : IsOpen U) :
    ∃ L : ℕ → Set E, (∀ k, IsCompact (L k)) ∧ (∀ k, L k ⊆ U) ∧ (∀ k, L k ⊆ L (k + 1)) ∧
      ∀ K, IsCompact K → K ⊆ U → ∃ k, K ⊆ L k := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let B := CompactExhaustion.choice U
  refine ⟨fun k => Subtype.val '' B k,
    fun k => (B.isCompact k).image continuous_subtype_val,
    fun k z hz => ?_, fun k => image_mono (B.subset_succ k), fun K hK hKU => ?_⟩
  · obtain ⟨z, _, rfl⟩ := hz
    exact z.property
  · have hpre : IsCompact ((Subtype.val : U → E) ⁻¹' K) := by
      apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
      rwa [image_preimage_eq_of_subset (by simpa using hKU)]
    obtain ⟨k, hk⟩ := B.exists_superset_of_isCompact hpre
    exact ⟨k, fun z hz => ⟨⟨z, hKU hz⟩, hk hz, rfl⟩⟩

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
