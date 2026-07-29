/-
Copyright (c) 2026 Imperial College London. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Coefficients

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

open Ideal

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

/-- An ideal norm count used in the Odlyzko-bound argument. -/
noncomputable def idealNormCount (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // absNorm I = n}

lemma dedekindZeta_eq_LSeries_idealNormCount (s : ℂ) :
    NumberField.dedekindZeta K s = LSeries (fun n ↦ (idealNormCount K n : ℂ)) s :=
  rfl

end NumberField.Odlyzko
