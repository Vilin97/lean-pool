/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Disjoint halves of a finite index set

The two inclusions of an index into the doubled finite set have
distinct values.
-/

namespace RS

/-- The two inclusions of the same finite index have distinct values. -/
theorem castAdd_ne_natAdd {n : ℕ} (i : Fin n) :
    Fin.castAdd n i ≠ Fin.natAdd n i := by
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
  omega

end RS
