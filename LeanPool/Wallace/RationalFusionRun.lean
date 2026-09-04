/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.RationalLocalSetup
import LeanPool.Wallace.LocalFusion

/-!
# The unconditional local fusion for the rational direct sum

For each nonzero rational vector this module instantiates the generic fusion recursion with the
prepared local blocks, proves the density bound for deleted positions, and packages the
resulting separating, locally admissible character.
-/

open Filter Set Topology

namespace Wallace
namespace RationalFusionRun

noncomputable section

open RationalTriangularPreprocess
open RationalData
open RationalClosure
open RationalLocalSetup
open FiniteCombinatorics
open LocalFusion

abbrev blockSize : ℕ → ℕ := FusionSchedule.blockSize
theorem blockSize_pos (l : ℕ) : 0 < blockSize l := FusionSchedule.blockSize_pos l
abbrev independenceBound : ℕ → ℕ := FusionSchedule.stageIndependenceBound

abbrev localCarrier (x : ContinuumRationalGroup) : Set ContinuumIndex :=
  closure blockSize blockSize_pos independenceBound x

abbrev LocalGroup (x : ContinuumRationalGroup) := localCarrier x →₀ ℚ

abbrev fresh (x : ContinuumRationalGroup) : ℕ → Finset (LocalGroup x) :=
  localActiveBlock blockSize blockSize_pos independenceBound x

theorem localGroup_countable (x : ContinuumRationalGroup) : Countable (LocalGroup x) := by
  letI : Countable (localCarrier x) :=
    (closure_countable blockSize blockSize_pos independenceBound x).to_subtype
  infer_instance

/-- A fixed surjection used to make every local point eventually protected. -/
def localEnumeration (x : ContinuumRationalGroup) : ℕ → LocalGroup x := by
  letI : Countable (localCarrier x) :=
    (closure_countable blockSize blockSize_pos independenceBound x).to_subtype
  exact Classical.choose (exists_surjective_nat (LocalGroup x))

theorem localEnumeration_surjective (x : ContinuumRationalGroup) :
    Function.Surjective (localEnumeration x) := by
  letI : Countable (localCarrier x) :=
    (closure_countable blockSize blockSize_pos independenceBound x).to_subtype
  exact Classical.choose_spec (exists_surjective_nat (LocalGroup x))

def distinguished (x : ContinuumRationalGroup) : LocalGroup x := by
  classical
  exact Finsupp.subtypeDomain (localCarrier x) x

theorem distinguished_ne_zero {x : ContinuumRationalGroup} (hx : x ≠ 0) :
    distinguished x ≠ 0 := by
  classical
  intro hzero
  apply hx
  exact (Finsupp.subtypeDomain_eq_zero_iff
    (support_subset_closure blockSize blockSize_pos independenceBound x)).mp hzero

/-- The generic scheduling recursion instantiated on the rational local group. -/
def scheduledCertificate (x : {x : ContinuumRationalGroup // x ≠ 0}) :
    ScheduledRunCertificate (fresh x.1) (distinguished x.1) :=
  Classical.choice <| exists_scheduledRunCertificate
    (fresh x.1) (localEnumeration x.1) (distinguished x.1)
    (distinguished_ne_zero x.2)
    (localActiveBlock_card_le blockSize blockSize_pos independenceBound x.1)
    (localActiveBlock_boundedIndependent blockSize blockSize_pos independenceBound x.1)
    (localEnumeration_surjective x.1)

abbrev run (x : {x : ContinuumRationalGroup // x ≠ 0}) :
    FusionRun (LocalGroup x.1) := (scheduledCertificate x).run

def deletedPositions (x : {x : ContinuumRationalGroup // x ≠ 0})
    (a : RelevantCode blockSize blockSize_pos independenceBound x.1) (l : ℕ) :
    Finset ℕ :=
  (TriangularPreprocess.blockPositions blockSize blockSize_pos l).filter fun n ↦
    localDifference blockSize blockSize_pos independenceBound x.1 a n ∉ (run x).retained l

theorem deletedPositions_subset_block
    (x : {x : ContinuumRationalGroup // x ≠ 0})
    (a : RelevantCode blockSize blockSize_pos independenceBound x.1) (l : ℕ) :
    deletedPositions x a l ⊆ TriangularPreprocess.blockPositions blockSize blockSize_pos l := by
  intro n hn
  exact (Finset.mem_filter.mp hn).1

private theorem image_deletedPositions
    (x : {x : ContinuumRationalGroup // x ≠ 0})
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
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem _ hn'.1, hn'.2⟩
  · intro hg
    have hg' := Finset.mem_sdiff.mp hg
    obtain ⟨n, hn, hng⟩ := Finset.mem_image.mp hg'.1
    subst g
    exact Finset.mem_image.mpr
      ⟨n, Finset.mem_filter.mpr ⟨hn, hg'.2⟩, rfl⟩

theorem deletedPositions_card_le
    (x : {x : ContinuumRationalGroup // x ≠ 0})
    (a : RelevantCode blockSize blockSize_pos independenceBound x.1) (l : ℕ)
    (hl : l ∈ refinedLabel blockSize blockSize_pos independenceBound x.1 a) :
    (deletedPositions x a l).card ≤ FusionSchedule.protectedBound l := by
  classical
  let f := localDifference blockSize blockSize_pos independenceBound x.1 a
  have hinj : Function.Injective f :=
    localDifference_injective blockSize blockSize_pos independenceBound x.1 a
  calc
    (deletedPositions x a l).card = ((deletedPositions x a l).image f).card := by
      exact (Finset.card_image_of_injective _ hinj).symm
    _ = (localDifferenceBlock blockSize blockSize_pos independenceBound x.1 a l \
          (run x).retained l).card := by rw [image_deletedPositions]
    _ = (fresh x.1 l \ (run x).retained l).card := by
      change (localDifferenceBlock blockSize blockSize_pos independenceBound x.1 a l \
          (run x).retained l).card =
        (localActiveBlock blockSize blockSize_pos independenceBound x.1 l \
          (run x).retained l).card
      rw [localActiveBlock_eq_of_mem blockSize blockSize_pos independenceBound x.1 l a hl]
    _ ≤ ((run x).guardSet l).card := (scheduledCertificate x).deleted_card_le l
    _ ≤ FusionSchedule.protectedBound l := (scheduledCertificate x).guard_card_le l

theorem retainedPositions_mem_ultrafilter
    (x : {x : ContinuumRationalGroup // x ≠ 0})
    (a : RelevantCode blockSize blockSize_pos independenceBound x.1) :
    (BlockSystem.ofBlockPositions blockSize blockSize_pos).retainedBlocks
        (refinedLabel blockSize blockSize_pos independenceBound x.1 a)
        (deletedPositions x a) ∈ ultrafilter blockSize blockSize_pos a.1 := by
  apply ultrafilter_le_density blockSize blockSize_pos a.1
  apply BlockSystem.retainedBlocks_mem_densityFilter_ofBlockPositions
      blockSize blockSize_pos (deletedPositions x a) FusionSchedule.protectedBound
  · exact label_diff_refinedLabel_finite
      blockSize blockSize_pos independenceBound x.1 a
  · exact deletedPositions_subset_block x a
  · exact deletedPositions_card_le x a
  · exact FusionSchedule.tendsto_protectedBound_div_blockSize

/-! ## Rational block and run certificates -/

structure RationalCodeBlocks
    (x : ContinuumRationalGroup) (R : FusionRun (LocalGroup x))
    (a : RelevantCode blockSize blockSize_pos independenceBound x) where
  blocks : R.CodeBlocks
  p_eq : blocks.p = ultrafilter blockSize blockSize_pos a.1
  block_eq : ∀ l, blocks.block l =
    TriangularPreprocess.blockPositions blockSize blockSize_pos l
  difference_eq : ∀ n,
    blocks.difference n = localDifference blockSize blockSize_pos independenceBound x a n

namespace RationalCodeBlocks

theorem tendsto_prepared
    {x : ContinuumRationalGroup} {R : FusionRun (LocalGroup x)}
    {a : RelevantCode blockSize blockSize_pos independenceBound x}
    (C : RationalCodeBlocks x R a) :
    Tendsto
      (fun n ↦ R.limitCharacter
        (Finsupp.subtypeDomain (localCarrier x)
          (prepared blockSize blockSize_pos independenceBound a.1 n)))
      (ultrafilter blockSize blockSize_pos a.1)
      (nhds (R.limitCharacter (Finsupp.single ⟨codeIndex a.1, a.2⟩ 1))) := by
  have hp : (C.blocks.p : Filter ℕ) ≤ cofinite := by
    rw [C.p_eq]
    exact ultrafilter_free blockSize blockSize_pos a.1
  have hzero := R.tendsto_limit_difference_zero_of_blockPositions
    C.blocks blockSize blockSize_pos hp C.block_eq
  have hdifference : ∀ n, C.blocks.difference n =
      Finsupp.subtypeDomain (localCarrier x)
          (prepared blockSize blockSize_pos independenceBound a.1 n) -
        Finsupp.single ⟨codeIndex a.1, a.2⟩ 1 := by
    intro n
    rw [C.difference_eq]
    simp only [localDifference]
    ext i
    change prepared blockSize blockSize_pos independenceBound a.1 n i.val -
        codeBasisVector a.1 i.val =
      prepared blockSize blockSize_pos independenceBound a.1 n i.val -
        Finsupp.single ⟨codeIndex a.1, a.2⟩ 1 i
    by_cases hi : i.val = codeIndex a.1
    · have hisub : i = ⟨codeIndex a.1, a.2⟩ := Subtype.ext hi
      subst i
      simp [codeBasisVector]
    · have hisub : i ≠ ⟨codeIndex a.1, a.2⟩ := by
        intro heq
        exact hi (congrArg Subtype.val heq)
      simp [codeBasisVector, hi, hisub]
  have hprepared := R.tendsto_limit_prepared C.blocks
    (fun n ↦ Finsupp.subtypeDomain (localCarrier x)
      (prepared blockSize blockSize_pos independenceBound a.1 n))
    (Finsupp.single ⟨codeIndex a.1, a.2⟩ 1) hdifference hzero
  simpa only [C.p_eq] using hprepared

end RationalCodeBlocks

structure LocalRunCertificate (x : {x : ContinuumRationalGroup // x ≠ 0}) where
  run : FusionRun (LocalGroup x.1)
  self_ne_zero : run.limitCharacter (Finsupp.subtypeDomain (localCarrier x.1) x.1) ≠ 0
  codeBlocks : ∀ a : RelevantCode blockSize blockSize_pos independenceBound x.1,
    RationalCodeBlocks x.1 run a

theorem LocalRunCertificate.locallyAdmissible
    {x : {x : ContinuumRationalGroup // x ≠ 0}} (C : LocalRunCertificate x) :
    RationalTransfiniteExtension.LocallyAdmissible
      (transfiniteData blockSize blockSize_pos independenceBound)
      (localCarrier x.1) C.run.limitCharacter := by
  intro a ha
  exact (C.codeBlocks ⟨a, ha⟩).tendsto_prepared

def codeBlocks (x : {x : ContinuumRationalGroup // x ≠ 0})
    (a : RelevantCode blockSize blockSize_pos independenceBound x.1) :
    RationalCodeBlocks x.1 (run x) a where
  blocks := {
    p := ultrafilter blockSize blockSize_pos a.1
    block := TriangularPreprocess.blockPositions blockSize blockSize_pos
    labels := refinedLabel blockSize blockSize_pos independenceBound x.1 a
    deletions := deletedPositions x a
    difference := localDifference blockSize blockSize_pos independenceBound x.1 a
    retained_mem := by
      simpa only [BlockSystem.retainedBlocks, BlockSystem.ofBlockPositions_block] using
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

/-- Complete local separating and admissibility certificate. -/
def localRunCertificate (x : {x : ContinuumRationalGroup // x ≠ 0}) :
    LocalRunCertificate x where
  run := run x
  self_ne_zero := by
    apply (run x).limitCharacter_ne_zero_of_initial_half
    · exact (scheduledCertificate x).initial_half
    · exact (scheduledCertificate x).distinguished_protected
  codeBlocks := codeBlocks x

theorem exists_localRunCertificate
    (x : {x : ContinuumRationalGroup // x ≠ 0}) :
    Nonempty (LocalRunCertificate x) := ⟨localRunCertificate x⟩

end
end RationalFusionRun
end Wallace
