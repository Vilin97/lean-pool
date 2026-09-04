/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.RationalData
import LeanPool.Wallace.CountableClosure

/-!
# Countable dependency closures for the rational direct sum

Starting from the finite support of a vector, close under the supports of every prepared
sequence whose code coordinate has entered the set.
-/

open Set

namespace Wallace
namespace RationalClosure

noncomputable section

open RationalTriangularPreprocess
open RationalData

variable (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (M : ℕ → ℕ)

/-- Coordinates occurring in the prepared sequence represented by `a`. -/
def dependency (a : ContinuumIndex) : Set ContinuumIndex :=
  ⋃ n, ↑(prepared N hN M a n).support

theorem dependency_countable (a : ContinuumIndex) :
    (dependency N hN M a).Countable := by
  apply Set.countable_iUnion
  intro n
  exact (prepared N hN M a n).support.finite_toSet.countable

/-- Least finite-stage dependency closure of the support of `x`. -/
def closure (x : ContinuumRationalGroup) : Set ContinuumIndex :=
  dependencyClosure codeIndex (dependency N hN M) ↑x.support

theorem support_subset_closure (x : ContinuumRationalGroup) :
    ↑x.support ⊆ closure N hN M x :=
  subset_dependencyClosure codeIndex (dependency N hN M) ↑x.support

theorem closure_countable (x : ContinuumRationalGroup) :
    (closure N hN M x).Countable := by
  apply countable_dependencyClosure codeIndex (dependency N hN M)
  · exact dependency_countable N hN M
  · exact x.support.finite_toSet.countable

theorem prepared_support_mem_closure (x : ContinuumRationalGroup)
    (a : ContinuumIndex) (ha : codeIndex a ∈ closure N hN M x)
    (n : ℕ) (i : ContinuumIndex) (hi : i ∈ (prepared N hN M a n).support) :
    i ∈ closure N hN M x := by
  apply dependency_subset_closure_of_index_mem
      codeIndex (dependency N hN M) ↑x.support ha
  exact Set.mem_iUnion_of_mem n hi

theorem closure_closedUnderPreparedSupports (x : ContinuumRationalGroup) :
    RationalTransfiniteExtension.ClosedUnderPreparedSupports
      (transfiniteData N hN M) (closure N hN M x) := by
  intro a ha n i hi
  exact prepared_support_mem_closure N hN M x a ha n i hi

end
end RationalClosure
end Wallace
