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

/-- Least finite-stage dependency closure of the support of `x`. -/
def closure (x : ContinuumRationalGroup) : Set ContinuumIndex :=
  preparedClosure codeIndex (prepared N hN M) x

theorem support_subset_closure (x : ContinuumRationalGroup) :
    ↑x.support ⊆ closure N hN M x :=
  support_subset_preparedClosure codeIndex (prepared N hN M) x

theorem closure_countable (x : ContinuumRationalGroup) :
    (closure N hN M x).Countable :=
  preparedClosure_countable codeIndex (prepared N hN M) x

theorem prepared_support_mem_closure (x : ContinuumRationalGroup)
    (a : ContinuumIndex) (ha : codeIndex a ∈ closure N hN M x)
    (n : ℕ) (i : ContinuumIndex) (hi : i ∈ (prepared N hN M a n).support) :
    i ∈ closure N hN M x :=
  preparedSupport_subset_preparedClosure codeIndex (prepared N hN M) x a ha n hi

theorem closure_closedUnderPreparedSupports (x : ContinuumRationalGroup) :
    RationalTransfiniteExtension.ClosedUnderPreparedSupports
      (transfiniteData N hN M) (closure N hN M x) := by
  intro a ha n i hi
  exact prepared_support_mem_closure N hN M x a ha n i hi

end
end RationalClosure
end Wallace
