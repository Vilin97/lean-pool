/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.Data.Finset.Basic

/-!
# Elementary lemmas about finite sets
-/

namespace Finset
variable {α : Type*} {s : Finset α}

@[simp]
public
lemma ne_empty_iff_nonempty : s ≠ ∅ ↔ s.Nonempty := nonempty_iff_ne_empty.symm

end Finset
