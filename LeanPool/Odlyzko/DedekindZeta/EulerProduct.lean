/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.Convergence
public import Mathlib.NumberTheory.EulerProduct.Basic

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Nat

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

/-- A dedekind zeta summand used in the Odlyzko-bound argument. -/
noncomputable def dedekindZetaSummand (s : ℂ) (n : ℕ) : ℂ :=
  LSeries.term (fun m ↦ (idealNormCount K m : ℂ)) s n

@[simp] lemma dedekindZetaSummand_zero (s : ℂ) :
    dedekindZetaSummand K s 0 = 0 := by
  simp [dedekindZetaSummand]

end NumberField.Odlyzko
