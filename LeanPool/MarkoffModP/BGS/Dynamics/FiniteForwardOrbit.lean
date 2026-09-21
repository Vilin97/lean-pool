/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Function.Iterate

/-!
# Finite forward orbits of injective maps

An injective self-map cannot have a finite forward orbit with a nonperiodic initial point.  The
injectivity hypothesis is what lets us cancel the transient part of a repeated pair of iterates.
-/

namespace BGS

universe u

variable {X : Type u} {f : X → X} {x : X}

/-- If the forward orbit of `x` under an injective self-map is finite, then a positive iterate
returns to `x`. -/
theorem exists_positive_iterate_eq_self_of_finite_forwardOrbit
    (hf : Function.Injective f)
    (horbit : (Set.range fun n : ℕ ↦ (f^[n]) x).Finite) :
    ∃ n : ℕ, 0 < n ∧ (f^[n]) x = x := by
  let orbitMap : ℕ → X := fun n ↦ (f^[n]) x
  obtain ⟨m, -, n, -, hmn, hcollision⟩ :=
    Set.infinite_univ.exists_ne_map_eq_of_mapsTo
      (f := orbitMap) (t := Set.range orbitMap)
      (fun k _ ↦ ⟨k, rfl⟩) horbit
  rcases lt_or_gt_of_ne hmn with hmn | hnm
  · refine ⟨n - m, Nat.sub_pos_of_lt hmn, ?_⟩
    exact Function.iterate_cancel hf hcollision.symm
  · refine ⟨m - n, Nat.sub_pos_of_lt hnm, ?_⟩
    exact Function.iterate_cancel hf hcollision

/-- A finite set containing every forward iterate forces a positive return for an injective
self-map.  This form is convenient when an orbit has already been bounded by a concrete finite
set. -/
theorem exists_positive_iterate_eq_self_of_forwardOrbit_subset
    (hf : Function.Injective f) {s : Set X} (hs : s.Finite)
    (horbit : Set.range (fun n : ℕ ↦ (f^[n]) x) ⊆ s) :
    ∃ n : ℕ, 0 < n ∧ (f^[n]) x = x :=
  exists_positive_iterate_eq_self_of_finite_forwardOrbit hf (hs.subset horbit)

end BGS
