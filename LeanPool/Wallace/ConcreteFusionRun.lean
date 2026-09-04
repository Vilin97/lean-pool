/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.LocalEnumeration
import LeanPool.Wallace.LocalFusion

/-!
# The unconditional concrete local fusion

For each nonzero vector this module instantiates the generic scheduling recursion with the
prepared local blocks.  It then converts the bounded deletion at every stage into a
block-density certificate for every relevant code.  No marker sequence is used.
-/

open Filter Set Topology

namespace Wallace
namespace ConcreteFusionRun

noncomputable section

open TriangularPreprocess
open ConcreteData
open ConcreteClosure
open ConcreteLocalSetup
open FiniteCombinatorics
open LocalFusion

/-! ## Specialization of the numerical schedule -/

abbrev blockSize : ℕ → ℕ := FusionSchedule.blockSize

theorem blockSize_pos (l : ℕ) : 0 < blockSize l :=
  FusionSchedule.blockSize_pos l

abbrev independenceBound : ℕ → ℕ := FusionSchedule.stageIndependenceBound

abbrev localCarrier (x : ContinuumFreeGroup) : Set ContinuumIndex :=
  closure blockSize blockSize_pos independenceBound x

abbrev LocalGroup (x : ContinuumFreeGroup) := localCarrier x →₀ ℤ

abbrev fresh (x : ContinuumFreeGroup) : ℕ → Finset (LocalGroup x) :=
  localActiveBlock blockSize blockSize_pos independenceBound x

abbrev enumeration (x : ContinuumFreeGroup) : ℕ → LocalGroup x :=
  groupEnumeration blockSize blockSize_pos independenceBound x

def distinguished (x : ContinuumFreeGroup) : LocalGroup x := by
  classical
  exact Finsupp.subtypeDomain (localCarrier x) x

theorem distinguished_ne_zero {x : ContinuumFreeGroup} (hx : x ≠ 0) :
    distinguished x ≠ 0 := by
  classical
  intro hzero
  apply hx
  exact (Finsupp.subtypeDomain_eq_zero_iff
    (support_subset_closure blockSize blockSize_pos independenceBound x)).mp hzero

/-! ## The scheduled run -/

/-- The generic recursion, instantiated with the concrete local blocks. -/
def scheduledCertificate (x : {x : ContinuumFreeGroup // x ≠ 0}) :
    ScheduledRunCertificate (fresh x.1) (distinguished x.1) :=
  Classical.choice <| exists_scheduledRunCertificate
    (fresh x.1) (enumeration x.1) (distinguished x.1)
    (distinguished_ne_zero x.2)
    (localActiveBlock_card_le blockSize blockSize_pos independenceBound x.1)
    (localActiveBlock_boundedIndependent blockSize blockSize_pos independenceBound x.1)
    (groupEnumeration_surjective blockSize blockSize_pos independenceBound x.1)

abbrev run (x : {x : ContinuumFreeGroup // x ≠ 0}) :
    FusionRun (LocalGroup x.1) :=
  (scheduledCertificate x).run

/-! ## Deleted positions and their density estimate -/

/-- Positions discarded from the block of a relevant code.  Away from that code's refined
label this definition is harmless; only labelled stages enter its density certificate. -/
def deletedPositions (x : {x : ContinuumFreeGroup // x ≠ 0})
    (a : RelevantCode blockSize blockSize_pos independenceBound x.1) (l : ℕ) :
    Finset ℕ :=
  (blockPositions blockSize blockSize_pos l).filter fun n ↦
    localDifference blockSize blockSize_pos independenceBound x.1 a n ∉
      (run x).retained l

theorem deletedPositions_subset_block (x : {x : ContinuumFreeGroup // x ≠ 0})
    (a : RelevantCode blockSize blockSize_pos independenceBound x.1) (l : ℕ) :
    deletedPositions x a l ⊆ blockPositions blockSize blockSize_pos l := by
  intro n hn
  exact (Finset.mem_filter.mp hn).1

private theorem image_deletedPositions (x : {x : ContinuumFreeGroup // x ≠ 0})
    (a : RelevantCode blockSize blockSize_pos independenceBound x.1) (l : ℕ) :
    (deletedPositions x a l).image
        (localDifference blockSize blockSize_pos independenceBound x.1 a) =
      localDifferenceBlock blockSize blockSize_pos independenceBound x.1 a l \
        (run x).retained l := by
  classical
  ext g
  constructor
  · intro hg
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hg
    have hn' := Finset.mem_filter.mp hn
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_image_of_mem _ hn'.1, hn'.2⟩
  · intro hg
    have hg' := Finset.mem_sdiff.mp hg
    obtain ⟨n, hn, hng⟩ := Finset.mem_image.mp hg'.1
    subst g
    exact Finset.mem_image.mpr
      ⟨n, Finset.mem_filter.mpr ⟨hn, hg'.2⟩, rfl⟩

theorem deletedPositions_card_le (x : {x : ContinuumFreeGroup // x ≠ 0})
    (a : RelevantCode blockSize blockSize_pos independenceBound x.1)
    (l : ℕ)
    (hl : l ∈ refinedLabel blockSize blockSize_pos independenceBound x.1 a) :
    (deletedPositions x a l).card ≤ FusionSchedule.protectedBound l := by
  classical
  let f := localDifference blockSize blockSize_pos independenceBound x.1 a
  have hinj : Function.Injective f :=
    localDifference_injective blockSize blockSize_pos independenceBound x.1 a
  calc
    (deletedPositions x a l).card =
        ((deletedPositions x a l).image f).card := by
          exact (Finset.card_image_of_injective _ hinj).symm
    _ = (localDifferenceBlock blockSize blockSize_pos independenceBound x.1 a l \
          (run x).retained l).card := by
          rw [image_deletedPositions]
    _ = (fresh x.1 l \ (run x).retained l).card := by
          change (localDifferenceBlock blockSize blockSize_pos independenceBound x.1 a l \
              (run x).retained l).card =
            (localActiveBlock blockSize blockSize_pos independenceBound x.1 l \
              (run x).retained l).card
          rw [localActiveBlock_eq_of_mem blockSize blockSize_pos independenceBound x.1 l a hl]
    _ ≤ ((run x).guardSet l).card :=
      (scheduledCertificate x).deleted_card_le l
    _ ≤ FusionSchedule.protectedBound l :=
      (scheduledCertificate x).guard_card_le l

theorem retainedPositions_mem_ultrafilter
    (x : {x : ContinuumFreeGroup // x ≠ 0})
    (a : RelevantCode blockSize blockSize_pos independenceBound x.1) :
    (BlockSystem.ofBlockPositions blockSize blockSize_pos).retainedBlocks
        (refinedLabel blockSize blockSize_pos independenceBound x.1 a)
        (deletedPositions x a) ∈
      ultrafilter blockSize blockSize_pos a.1 := by
  apply ultrafilter_le_density blockSize blockSize_pos a.1
  apply BlockSystem.retainedBlocks_mem_densityFilter_ofBlockPositions
      blockSize blockSize_pos (deletedPositions x a)
      FusionSchedule.protectedBound
  · exact label_diff_refinedLabel_finite
      blockSize blockSize_pos independenceBound x.1 a
  · exact deletedPositions_subset_block x a
  · exact deletedPositions_card_le x a
  · exact FusionSchedule.tendsto_protectedBound_div_blockSize

/-! ## Concrete block certificates and the local output -/

def codeBlocks (x : {x : ContinuumFreeGroup // x ≠ 0})
    (a : RelevantCode blockSize blockSize_pos independenceBound x.1) :
    ConcreteCodeBlocks blockSize blockSize_pos independenceBound x.1 (run x) a where
  blocks := {
    p := ultrafilter blockSize blockSize_pos a.1
    block := blockPositions blockSize blockSize_pos
    labels := refinedLabel blockSize blockSize_pos independenceBound x.1 a
    deletions := deletedPositions x a
    difference := localDifference blockSize blockSize_pos independenceBound x.1 a
    retained_mem := by
      simpa only [BlockSystem.retainedBlocks,
        BlockSystem.ofBlockPositions_block] using
        retainedPositions_mem_ultrafilter x a
    retained_in_stage := by
      intro l n hl hn
      have hnparts := Finset.mem_sdiff.mp hn
      by_contra hnot
      exact hnparts.2 (Finset.mem_filter.mpr ⟨hnparts.1, hnot⟩)
  }
  p_eq := rfl
  block_eq := fun _ ↦ rfl
  difference_eq := fun _ ↦ rfl

/-- A complete local fusion certificate for a fixed nonzero vector. -/
def localRunCertificate (x : {x : ContinuumFreeGroup // x ≠ 0}) :
    LocalRunCertificate blockSize blockSize_pos independenceBound x where
  run := run x
  self_ne_zero := by
    apply (run x).limitCharacter_ne_zero_of_initial_half
    · exact (scheduledCertificate x).initial_half
    · exact (scheduledCertificate x).distinguished_protected
  codeBlocks := codeBlocks x

theorem exists_localRunCertificate
    (x : {x : ContinuumFreeGroup // x ≠ 0}) :
    Nonempty (LocalRunCertificate blockSize blockSize_pos independenceBound x) :=
  ⟨localRunCertificate x⟩

/-- The local character required by the transfinite extension exists for every nonzero vector. -/
theorem hasLocalSeparatingCharacters :
    GlobalAssembly.HasLocalSeparatingCharacters
      blockSize blockSize_pos independenceBound :=
  hasLocalSeparatingCharacters_of_certificates
    blockSize blockSize_pos independenceBound exists_localRunCertificate

end

end ConcreteFusionRun
end Wallace
