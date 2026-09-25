/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Tricycle.Core
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SpecBurning
public import Mathlib.Tactic

/-!
# Lemma 3.5 of van Dobben de Bruyn–Smit–van der Wegen

Part (a) is proved in full generality in `Utilities/Gonality/BurnedSet.lean`
(`not_mem_burned_of_qReduced`): a positive-rank `q`-reduced divisor's own base
point is never burned by a fire started at a chip-free vertex.

Part (b) is the counting half, here specialised to the spokes of the tricycle
core:

> if `I` is a set of spokes whose transition vertices are all burned, then
> `{v₀} ∪ ⋃_{i ∈ I} (interior of spoke i)` carries at least `|I|` chips.

The split is the source's own `I = I₀ ⊔ I₁`.  For `i ∈ I₀` the first vertex up
the spoke is burned; those vertices are distinct across spokes, so `v₀` — which
is *not* burned — pays for all of them at once, giving `|I₀| ≤ D(v₀)`.  For
`i ∈ I₁` the first vertex up the spoke is unburned while the far end is burned,
so the slot has a burned/unburned split and therefore a chip in its interior.
-/

@[expose] public section

namespace Utilities.Tricycle

open Finset

open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec
open Utilities.Gonality

/-! ## Indexing the six spokes -/

/-- The six spoke slots, indexed by `Fin 6`. -/
def spokeOf : Fin 6 → Fin 15 := ![0, 1, 2, 3, 4, 5]

/-- The transition vertex at the far end of spoke `i`. -/
def transitionOf : Fin 6 → Fin 7 := ![1, 2, 3, 4, 5, 6]

theorem spokeOf_injective : Function.Injective spokeOf := by decide

theorem transitionOf_injective : Function.Injective transitionOf := by decide

theorem tricycleCore_spoke_tail (i : Fin 6) : tricycleCore.tail (spokeOf i) = centre := by
  fin_cases i <;> decide

theorem tricycleCore_spoke_head (i : Fin 6) :
    tricycleCore.head (spokeOf i) = transitionOf i := by
  fin_cases i <;> decide

/-! ## Lemma 3.5(b) -/

variable {spec : Spec 7 15}

theorem spoke_tail (hcore : spec.core = tricycleCore) (i : Fin 6) :
    spec.core.tail (spokeOf i) = centre := by
  rw [hcore]; exact tricycleCore_spoke_tail i

theorem spoke_head (hcore : spec.core = tricycleCore) (i : Fin 6) :
    spec.core.head (spokeOf i) = transitionOf i := by
  rw [hcore]; exact tricycleCore_spoke_head i

/-- The first vertex up spoke `i` from the centre. -/
def spokeStep (spec : Spec 7 15) (i : Fin 6) : spec.Vertex :=
  spec.slotVertex (spokeOf i) 1

theorem spokeStep_of_length_one (hcore : spec.core = tricycleCore) {i : Fin 6}
    (h : spec.length (spokeOf i) = 1) :
    spokeStep spec i = spec.coreVertex (transitionOf i) := by
  have hL := slotVertex_length (spec := spec) (spokeOf i)
  rw [h] at hL
  rw [spokeStep, hL, spoke_head hcore]

/-- The centre is adjacent to the first vertex up each spoke. -/
theorem num_edges_centre_spokeStep (hcore : spec.core = tricycleCore) (i : Fin 6) :
    0 < numEdges spec.graph (spec.coreVertex centre) (spokeStep spec i) := by
  have h := slotVertex_num_edges_pos (spec := spec) (edge := spokeOf i) (k := 0)
    (spec.length_pos _)
  rwa [slotVertex_zero, spoke_tail hcore] at h

/-- The six first-steps are distinct vertices. -/
theorem spokeStep_injective (hcore : spec.core = tricycleCore) :
    Function.Injective (spokeStep spec) := by
  intro i j hij
  by_contra hne
  have hslot : spokeOf i ≠ spokeOf j := fun h => hne (spokeOf_injective h)
  rcases Nat.lt_or_ge 1 (spec.length (spokeOf i)) with hbi | hsi
  · rcases Nat.lt_or_ge 1 (spec.length (spokeOf j)) with hbj | hsj
    · exact slotVertex_ne_of_slot_ne hslot Nat.one_pos hbi Nat.one_pos hbj hij
    · have hj1 : spec.length (spokeOf j) = 1 := by
        have := spec.length_pos (spokeOf j); omega
      rw [spokeStep_of_length_one hcore hj1] at hij
      exact slotVertex_ne_coreVertex Nat.one_pos hbi _ hij
  · have hi1 : spec.length (spokeOf i) = 1 := by
      have := spec.length_pos (spokeOf i); omega
    rcases Nat.lt_or_ge 1 (spec.length (spokeOf j)) with hbj | hsj
    · rw [spokeStep_of_length_one hcore hi1] at hij
      exact slotVertex_ne_coreVertex Nat.one_pos hbj _ hij.symm
    · have hj1 : spec.length (spokeOf j) = 1 := by
        have := spec.length_pos (spokeOf j); omega
      rw [spokeStep_of_length_one hcore hi1, spokeStep_of_length_one hcore hj1] at hij
      exact hne (transitionOf_injective (Sum.inl.inj hij))

/-- **Lemma 3.5(b).**  A set of spokes whose transition vertices are all burned
costs its cardinality in chips, counted on the centre and the spoke
interiors. -/
theorem helper_lemma_b (hcore : spec.core = tricycleCore)
    {D : CFDiv spec.graph} (hEff : effective D)
    (hred : qReduced spec.graph (spec.coreVertex centre) D)
    (hrank : rank spec.graph D ≥ 1)
    {w : spec.Vertex} (hw : D w = 0)
    (I : Finset (Fin 6))
    (hI : ∀ i ∈ I, spec.coreVertex (transitionOf i) ∈ burned spec.graph D w) :
    (I.card : ℤ) ≤ D (spec.coreVertex centre)
      + ∑ i ∈ I, spec.slotInteriorChips D (spokeOf i) := by
  classical
  have hv0 : spec.coreVertex centre ∉ burned spec.graph D w :=
    not_mem_burned_of_qReduced hEff hred hrank hw
  -- the spokes whose first step is already burned, and the rest
  have hsub : I.filter (fun i => spokeStep spec i ∈ burned spec.graph D w) ⊆ I :=
    Finset.filter_subset _ _
  have hcard :
      (I.filter (fun i => spokeStep spec i ∈ burned spec.graph D w)).card
        + (I.filter (fun i => spokeStep spec i ∉ burned spec.graph D w)).card
        = I.card := Finset.card_filter_add_card_filter_not _
  -- `|I₀| ≤ D v₀`: the centre pays one chip per burned first step.
  have hI₀le :
      ((I.filter (fun i => spokeStep spec i ∈ burned spec.graph D w)).card : ℤ)
        ≤ D (spec.coreVertex centre) := by
    have hle := sum_burned_le_of_not_mem_burned hv0
    have hTsub :
        (I.filter (fun i => spokeStep spec i ∈ burned spec.graph D w)).image
            (spokeStep spec) ⊆ burned spec.graph D w := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hi).2
    have hTcard :
        ((I.filter (fun i => spokeStep spec i ∈ burned spec.graph D w)).image
            (spokeStep spec)).card
          = (I.filter (fun i => spokeStep spec i ∈ burned spec.graph D w)).card :=
      Finset.card_image_of_injective _ (spokeStep_injective hcore)
    have hsum :
        (((I.filter (fun i => spokeStep spec i ∈ burned spec.graph D w)).image
            (spokeStep spec)).card : ℤ)
          ≤ ∑ u ∈ (I.filter (fun i => spokeStep spec i ∈ burned spec.graph D w)).image
              (spokeStep spec),
              (numEdges spec.graph (spec.coreVertex centre) u : ℤ) := by
      calc (((I.filter (fun i => spokeStep spec i ∈ burned spec.graph D w)).image
              (spokeStep spec)).card : ℤ)
          = ∑ _u ∈ (I.filter (fun i => spokeStep spec i ∈ burned spec.graph D w)).image
              (spokeStep spec), (1 : ℤ) := by simp
        _ ≤ _ := by
            refine Finset.sum_le_sum fun u hu => ?_
            obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
            have := num_edges_centre_spokeStep hcore i
            omega
    have hmono :
        ∑ u ∈ (I.filter (fun i => spokeStep spec i ∈ burned spec.graph D w)).image
            (spokeStep spec), (numEdges spec.graph (spec.coreVertex centre) u : ℤ)
          ≤ ∑ u ∈ burned spec.graph D w,
              (numEdges spec.graph (spec.coreVertex centre) u : ℤ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hTsub fun _ _ _ => Int.natCast_nonneg _
    omega
  -- each remaining spoke has a chip in its interior
  have hI₁le : ∀ i ∈ I.filter (fun i => spokeStep spec i ∉ burned spec.graph D w),
      (1 : ℤ) ≤ spec.slotInteriorChips D (spokeOf i) := by
    intro i hi
    obtain ⟨hiI, hnot⟩ := Finset.mem_filter.mp hi
    have hburn : spec.slotVertex (spokeOf i) (spec.length (spokeOf i))
        ∈ burned spec.graph D w := by
      rw [slotVertex_length, spoke_head hcore]
      exact hI i hiI
    have hlen : 1 < spec.length (spokeOf i) := by
      rcases Nat.lt_or_ge 1 (spec.length (spokeOf i)) with h | h
      · exact h
      · exfalso
        have h1 : spec.length (spokeOf i) = 1 := by
          have := spec.length_pos (spokeOf i); omega
        refine hnot ?_
        show spec.slotVertex (spokeOf i) 1 ∈ _
        rw [← h1]
        exact hburn
    obtain ⟨k, hk1, hk2, hk3, -, -⟩ :=
      exists_chip_down hburn hnot (le_of_lt hlen) (le_refl _)
    exact le_trans hk3 (apply_slotVertex_le_slotInteriorChips hEff (by omega) hk2)
  have hsumI₁ :
      (((I.filter (fun i => spokeStep spec i ∉ burned spec.graph D w)).card : ℤ))
        ≤ ∑ i ∈ I.filter (fun i => spokeStep spec i ∉ burned spec.graph D w),
            spec.slotInteriorChips D (spokeOf i) := by
    calc (((I.filter (fun i => spokeStep spec i ∉ burned spec.graph D w)).card : ℤ))
        = ∑ _i ∈ I.filter (fun i => spokeStep spec i ∉ burned spec.graph D w), (1 : ℤ) := by
          simp
      _ ≤ _ := Finset.sum_le_sum hI₁le
  have hsumMono :
      ∑ i ∈ I.filter (fun i => spokeStep spec i ∉ burned spec.graph D w),
          spec.slotInteriorChips D (spokeOf i)
        ≤ ∑ i ∈ I, spec.slotInteriorChips D (spokeOf i) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun i _ _ => slotInteriorChips_nonneg hEff _
  have hcast :
      (((I.filter (fun i => spokeStep spec i ∈ burned spec.graph D w)).card : ℤ))
        + (((I.filter (fun i => spokeStep spec i ∉ burned spec.graph D w)).card : ℤ))
        = (I.card : ℤ) := by exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) hcard
  omega

end Utilities.Tricycle
