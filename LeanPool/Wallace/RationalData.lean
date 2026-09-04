/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.BlockFilters
import LeanPool.Wallace.RationalTransfiniteExtension

/-!
# Concrete triangular data for the rational direct sum

This module chooses, uniformly for every coded injective rational sequence, its prepared
subsequence and its free block-density ultrafilter.
-/

open Filter Set Topology

namespace Wallace
namespace RationalData

noncomputable section

open RationalTriangularPreprocess
open FiniteCombinatorics

/-- The canonical continuum index is in bijection with binary streams. -/
def continuumIndexEquivBinaryStream : ContinuumIndex ≃ (ℕ → Bool) := by
  apply Classical.choice
  apply Cardinal.eq.mp
  rw [mk_continuumIndex, Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat]
  simp only [Cardinal.lift_id, Cardinal.two_power_aleph0]

/-- Almost-disjoint block label assigned to a rational sequence code. -/
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

variable (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (M : ℕ → ℕ)

/-- Strictly increasing selector supplied by rational block preprocessing. -/
def selector (a : ContinuumIndex) : ℕ → ℕ :=
  Classical.choose (triangular_block_preprocess a N hN M)

theorem selector_strictMono (a : ContinuumIndex) : StrictMono (selector N hN M a) :=
  (Classical.choose_spec (triangular_block_preprocess a N hN M)).1

/-- Prepared subsequence represented by code `a`. -/
def prepared (a : ContinuumIndex) (n : ℕ) : ContinuumRationalGroup :=
  codedSequence a (selector N hN M a n)

/-- Shifted finite set in block `l`. -/
def differenceBlock (a : ContinuumIndex) (l : ℕ) : Finset ContinuumRationalGroup :=
  (TriangularPreprocess.blockPositions N hN l).image fun n ↦
    prepared N hN M a n - codeBasisVector a

theorem differenceBlock_boundedIndependent (a : ContinuumIndex) (l : ℕ) :
    BoundedIndependent (M l) (differenceBlock N hN M a l) := by
  exact (Classical.choose_spec (triangular_block_preprocess a N hN M)).2.1 l |>.2

theorem prepared_support_lt (a : ContinuumIndex) (n : ℕ) (i : ContinuumIndex)
    (hi : i ∈ (prepared N hN M a n).support) : i < codeIndex a := by
  exact (Classical.choose_spec (triangular_block_preprocess a N hN M)).2.2 n i hi

theorem prepared_injective (a : ContinuumIndex) :
    Function.Injective (prepared N hN M a) :=
  (codedSequence_injective a).comp (selector_strictMono N hN M a).injective

theorem preparedDifference_injective (a : ContinuumIndex) :
    Function.Injective (fun n ↦ prepared N hN M a n - codeBasisVector a) := by
  intro m n hmn
  apply prepared_injective N hN M a
  exact sub_left_injective hmn

/-- Each shifted rational block has exactly the scheduled cardinality `N l`, as in
Lemma 5.3 of the paper. -/
theorem differenceBlock_card (a : ContinuumIndex) (l : ℕ) :
    (differenceBlock N hN M a l).card = N l := by
  rw [differenceBlock,
    Finset.card_image_iff.mpr (preparedDifference_injective N hN M a).injOn,
    TriangularPreprocess.blockPositions_card]

theorem differenceBlock_subset_range (a : ContinuumIndex) (l : ℕ) :
    ↑(differenceBlock N hN M a l) ⊆
      Set.range (fun n ↦ prepared N hN M a n - codeBasisVector a) := by
  intro x hx
  simp only [differenceBlock, Finset.mem_coe, Finset.mem_image] at hx
  obtain ⟨n, _hn, rfl⟩ := hx
  exact Set.mem_range_self n

abbrev blocks : BlockSystem := BlockSystem.ofBlockPositions N hN

/-- A free ultrafilter refining the block-density filter for code `a`. -/
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

/-- Concrete input for the rational transfinite recursion. -/
def transfiniteData : RationalTransfiniteExtension.ContinuumData where
  Code := ContinuumIndex
  codeIndex := codeIndex
  prepared := prepared N hN M
  support_lt := prepared_support_lt N hN M
  p := ultrafilter N hN

end
end RationalData
end Wallace
