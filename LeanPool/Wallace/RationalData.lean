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
open BlockData
open FiniteCombinatorics

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
