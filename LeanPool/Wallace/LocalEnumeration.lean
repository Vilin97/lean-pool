/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.ConcreteClosure
import Mathlib.Data.Finsupp.Encodable

/-!
# Enumeration of a countable local free group
-/

namespace Wallace
namespace ConcreteClosure

noncomputable section

open TriangularPreprocess

variable (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (M : ℕ → ℕ)

/-- A fixed surjective enumeration of every local free group. -/
def groupEnumeration (x : ContinuumFreeGroup) :
    ℕ → (closure N hN M x →₀ ℤ) := by
  letI : Countable (closure N hN M x) := (closure_countable N hN M x).to_subtype
  exact Classical.choose (exists_surjective_nat (closure N hN M x →₀ ℤ))

theorem groupEnumeration_surjective (x : ContinuumFreeGroup) :
    Function.Surjective (groupEnumeration N hN M x) := by
  let : Countable (closure N hN M x) := (closure_countable N hN M x).to_subtype
  exact Classical.choose_spec (exists_surjective_nat (closure N hN M x →₀ ℤ))

end

end ConcreteClosure
end Wallace
