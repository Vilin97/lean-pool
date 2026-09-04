/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.BlockFilters
import LeanPool.Wallace.TransfiniteExtension

/-!
# Concrete triangular data and block-density ultrafilters

This module makes all global choices which are shared by the local character fusions.  For
arbitrary positive block sizes and arbitrary bounded-independence thresholds, it chooses the
prepared subsequence of every triangularly coded injective sequence.  It also transports the
standard continuum-sized almost-disjoint family to the canonical continuum index and chooses a
free block-density ultrafilter for every code.

The choices here are entirely set-theoretic.  No topology on the free group and no character is
assumed.
-/

open Filter Set Topology

namespace Wallace
namespace ConcreteData

noncomputable section

open TriangularPreprocess
open FiniteCombinatorics

/-! ## Almost-disjoint labels indexed by the triangular codes -/

/-- The canonical continuum index is in bijection with the binary streams. -/
def continuumIndexEquivBinaryStream : ContinuumIndex ≃ (ℕ → Bool) := by
  apply Classical.choice
  apply Cardinal.eq.mp
  rw [mk_continuumIndex, Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat]
  simp only [Cardinal.lift_id, Cardinal.two_power_aleph0]

/-- The almost-disjoint set of block labels assigned to a code. -/
def label (a : ContinuumIndex) : Set ℕ :=
  binaryBranchOnNat (continuumIndexEquivBinaryStream a)

theorem label_infinite (a : ContinuumIndex) : (label a).Infinite :=
  binaryBranchOnNat_infinite _

theorem label_inter_finite {a b : ContinuumIndex} (hab : a ≠ b) :
    (label a ∩ label b).Finite := by
  apply binaryBranchOnNat_inter_finite
  exact continuumIndexEquivBinaryStream.injective.ne hab

theorem label_pairwise :
    Pairwise fun a b : ContinuumIndex ↦ (label a ∩ label b).Finite := by
  intro a b hab
  exact label_inter_finite hab

/-! ## The globally prepared sequences -/

variable (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (M : ℕ → ℕ)

/-- The strictly increasing subsequence selector supplied by block preprocessing. -/
def selector (a : ContinuumIndex) : ℕ → ℕ :=
  Classical.choose (triangular_block_preprocess a N hN M)

theorem selector_strictMono (a : ContinuumIndex) : StrictMono (selector N hN M a) :=
  (Classical.choose_spec (triangular_block_preprocess a N hN M)).1

/-- The prepared subsequence coded by `a`. -/
def prepared (a : ContinuumIndex) (n : ℕ) : ContinuumFreeGroup :=
  codedSequence a (selector N hN M a n)

/-- The shifted finite set in block `l`. -/
def differenceBlock (a : ContinuumIndex) (l : ℕ) : Finset ContinuumFreeGroup :=
  (blockPositions N hN l).image fun n ↦ prepared N hN M a n - codeBasisVector a

theorem differenceBlock_boundedIndependent (a : ContinuumIndex) (l : ℕ) :
    BoundedIndependent (M l) (differenceBlock N hN M a l) := by
  exact (Classical.choose_spec (triangular_block_preprocess a N hN M)).2.1 l |>.2

theorem prepared_support_lt (a : ContinuumIndex) (n : ℕ) (i : ContinuumIndex)
    (hi : i ∈ (prepared N hN M a n).support) : i < codeIndex a := by
  exact (Classical.choose_spec (triangular_block_preprocess a N hN M)).2.2 n i hi

theorem prepared_injective (a : ContinuumIndex) :
    Function.Injective (prepared N hN M a) :=
  (codedSequence_injective a).comp (selector_strictMono N hN M a).injective

/-- Translating a prepared sequence by its prescribed basis point preserves injectivity. -/
theorem preparedDifference_injective (a : ContinuumIndex) :
    Function.Injective
      (fun n ↦ prepared N hN M a n - codeBasisVector a) := by
  intro m n hmn
  apply prepared_injective N hN M a
  exact sub_left_injective hmn

/-- Each shifted block has exactly the scheduled cardinality `N l`, as in
Lemma 5.3 of the paper. -/
theorem differenceBlock_card (a : ContinuumIndex) (l : ℕ) :
    (differenceBlock N hN M a l).card = N l := by
  rw [differenceBlock,
    Finset.card_image_iff.mpr (preparedDifference_injective N hN M a).injOn,
    blockPositions_card]

theorem differenceBlock_subset_range (a : ContinuumIndex) (l : ℕ) :
    ↑(differenceBlock N hN M a l) ⊆
      Set.range (fun n ↦ prepared N hN M a n - codeBasisVector a) := by
  intro x hx
  simp only [differenceBlock, Finset.mem_coe, Finset.mem_image] at hx
  obtain ⟨n, _hn, rfl⟩ := hx
  exact Set.mem_range_self n

/-! ## The fixed free ultrafilters -/

/-- The block system determined by the prescribed sizes. -/
abbrev blocks : BlockSystem := BlockSystem.ofBlockPositions N hN

/-- A free ultrafilter extending the density filter assigned to code `a`. -/
def ultrafilter (a : ContinuumIndex) : Ultrafilter ℕ :=
  Classical.choose ((blocks N hN).exists_free_ultrafilter_le_densityFilter (label_infinite a))

theorem ultrafilter_le_density (a : ContinuumIndex) :
    (ultrafilter N hN a : Filter ℕ) ≤ (blocks N hN).densityFilter (label a) :=
  (Classical.choose_spec
    ((blocks N hN).exists_free_ultrafilter_le_densityFilter (label_infinite a))).1

theorem ultrafilter_free (a : ContinuumIndex) :
    (ultrafilter N hN a : Filter ℕ) ≤ cofinite :=
  (Classical.choose_spec
    ((blocks N hN).exists_free_ultrafilter_le_densityFilter (label_infinite a))).2

/-! ## Packaging for the transfinite extension -/

/-- The concrete triangular data used by the transfinite recursion. -/
def transfiniteData : TransfiniteExtension.ContinuumData where
  Code := ContinuumIndex
  codeIndex := codeIndex
  prepared := prepared N hN M
  support_lt := prepared_support_lt N hN M
  p := ultrafilter N hN

end

end ConcreteData
end Wallace
