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

/-- The least closure obtained in finitely many dependency steps from the support of `x`. -/
def closure (x : ContinuumFreeGroup) : Set ContinuumIndex :=
  preparedClosure codeIndex (prepared N hN M) x

theorem support_subset_closure (x : ContinuumFreeGroup) :
    ↑x.support ⊆ closure N hN M x :=
  support_subset_preparedClosure codeIndex (prepared N hN M) x

theorem closure_countable (x : ContinuumFreeGroup) :
    (closure N hN M x).Countable :=
  preparedClosure_countable codeIndex (prepared N hN M) x

/-- The closure contains every coordinate of each relevant prepared sequence. -/
theorem prepared_support_mem_closure (x : ContinuumFreeGroup)
    (a : ContinuumIndex) (ha : codeIndex a ∈ closure N hN M x)
    (n : ℕ) (i : ContinuumIndex) (hi : i ∈ (prepared N hN M a n).support) :
    i ∈ closure N hN M x :=
  preparedSupport_subset_preparedClosure codeIndex (prepared N hN M) x a ha n hi

theorem closure_closedUnderPreparedSupports (x : ContinuumFreeGroup) :
    TransfiniteExtension.ClosedUnderPreparedSupports
      (transfiniteData N hN M) (closure N hN M x) := by
  intro a ha n i hi
  exact prepared_support_mem_closure N hN M x a ha n i hi

end

end ConcreteClosure
end Wallace
