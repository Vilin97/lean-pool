/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.ConcreteData
import LeanPool.Wallace.CountableClosure

/-!
# Concrete countable dependency closures

For a nonzero vector `x`, this module closes its finite support under all prepared sequences
whose fresh code coordinate has entered the closure.  The resulting coordinate set is
countable, contains the support of `x`, and has exactly the closure property required by the
transfinite character extension.
-/

open Set

namespace Wallace
namespace ConcreteClosure

noncomputable section

open TriangularPreprocess
open ConcreteData

variable (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (M : ℕ → ℕ)

/-- All coordinates occurring in the prepared sequence attached to `a`. -/
def dependency (a : ContinuumIndex) : Set ContinuumIndex :=
  ⋃ n, ↑(prepared N hN M a n).support

theorem dependency_countable (a : ContinuumIndex) :
    (dependency N hN M a).Countable := by
  apply Set.countable_iUnion
  intro n
  exact (prepared N hN M a n).support.finite_toSet.countable

/-- The least closure obtained in finitely many dependency steps from the support of `x`. -/
def closure (x : ContinuumFreeGroup) : Set ContinuumIndex :=
  dependencyClosure codeIndex (dependency N hN M) ↑x.support

theorem support_subset_closure (x : ContinuumFreeGroup) :
    ↑x.support ⊆ closure N hN M x :=
  subset_dependencyClosure codeIndex (dependency N hN M) ↑x.support

theorem closure_countable (x : ContinuumFreeGroup) :
    (closure N hN M x).Countable := by
  apply countable_dependencyClosure codeIndex (dependency N hN M)
  · exact dependency_countable N hN M
  · exact x.support.finite_toSet.countable

/-- The closure contains every coordinate of each relevant prepared sequence. -/
theorem prepared_support_mem_closure (x : ContinuumFreeGroup)
    (a : ContinuumIndex) (ha : codeIndex a ∈ closure N hN M x)
    (n : ℕ) (i : ContinuumIndex) (hi : i ∈ (prepared N hN M a n).support) :
    i ∈ closure N hN M x := by
  apply dependency_subset_closure_of_index_mem
      codeIndex (dependency N hN M) ↑x.support ha
  exact Set.mem_iUnion_of_mem n hi

theorem closure_closedUnderPreparedSupports (x : ContinuumFreeGroup) :
    TransfiniteExtension.ClosedUnderPreparedSupports
      (transfiniteData N hN M) (closure N hN M x) := by
  intro a ha n i hi
  exact prepared_support_mem_closure N hN M x a ha n i hi

/-- A nonzero vector gives a nonempty coordinate closure. -/
theorem closure_nonempty {x : ContinuumFreeGroup} (hx : x ≠ 0) :
    (closure N hN M x).Nonempty := by
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hx
  exact ⟨i, support_subset_closure N hN M x hi⟩

/-- A fixed surjective enumeration of a nonempty concrete closure. -/
def enumeration {x : ContinuumFreeGroup} (hx : x ≠ 0) :
    ℕ → closure N hN M x := by
  letI : Countable (closure N hN M x) := (closure_countable N hN M x).to_subtype
  letI : Nonempty (closure N hN M x) := (closure_nonempty N hN M hx).to_subtype
  exact Classical.choose (exists_surjective_nat (closure N hN M x))

end

end ConcreteClosure
end Wallace
