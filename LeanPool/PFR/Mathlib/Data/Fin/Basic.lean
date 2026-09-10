/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.Data.Fin.Basic

/-!
# Elementary lemmas about finite types
-/

public
theorem Fin.cast_bijective {k l : ℕ} (h : k = l) : Function.Bijective (Fin.cast h) := by
  subst l; simpa using Function.bijective_id



public
theorem Fin.forall_fin_three {p : Fin 3 → Prop} : (∀ i, p i) ↔ p 0 ∧ p 1 ∧ p 2 :=
  Fin.forall_fin_succ.trans <| and_congr_right fun _ => Fin.forall_fin_two
