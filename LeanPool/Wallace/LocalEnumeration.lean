/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Set.Countable

/-!
# Enumeration of a countable local direct sum
-/

namespace Wallace

noncomputable section

universe u v

/-- A fixed surjective enumeration of the direct sum over a countable coordinate set. -/
def countableFinsuppEnumeration {I : Type u} {R : Type v} [Zero R] [Countable R]
    (D : Set I) (hD : D.Countable) : ℕ → (D →₀ R) := by
  letI : Countable D := hD.to_subtype
  exact Classical.choose (exists_surjective_nat (D →₀ R))

theorem countableFinsuppEnumeration_surjective {I : Type u} {R : Type v}
    [Zero R] [Countable R] (D : Set I) (hD : D.Countable) :
    Function.Surjective (countableFinsuppEnumeration D hD : ℕ → (D →₀ R)) := by
  let : Countable D := hD.to_subtype
  exact Classical.choose_spec (exists_surjective_nat (D →₀ R))

end

end Wallace
