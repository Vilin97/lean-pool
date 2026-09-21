/-
Copyright (c) 2026 Arthur F. Ramos, David Barros Hulak, Ruy J.G.B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
import LeanPool.MarshallHall.MarshallHall

/-!
# Checked finite separator solution

The selected theorem is obtained from the finite suffix-state completion in
`MarshallHall.Separation`.  The implementation's separator is repackaged at
the Challenge boundary so the Comparator sees the explicit finite action,
not only its finite-index stabilizer corollary.
-/

noncomputable section

namespace LERFChallenge

universe u

/-- A finite permutation action with a base state fixed by the subgroup and moved by the
separating element. -/
structure FinitePermutationSeparator
    {α : Type u} (H : Subgroup (FreeGroup α)) (g : FreeGroup α) where
  /-- The finite set of states on which the free group acts. -/
  State : Type u
  /-- A finite enumeration of the action states. -/
  [stateFintype : Fintype State]
  /-- The homomorphism realizing the free group as permutations of the state set. -/
  representation : FreeGroup α →* Equiv.Perm State
  /-- The distinguished state fixed by the subgroup and moved by the separating element. -/
  base : State
  fixes_subgroup : ∀ h : H, representation (h : FreeGroup α) base = base
  separates : representation g base ≠ base



theorem freeGroup_finite_permutation_separator
    {α : Type*}
    (H : Subgroup (FreeGroup α))
    [Group.FG H]
    (g : FreeGroup α)
    (hg : g ∉ H) :
    Nonempty (FinitePermutationSeparator H g) := by
  obtain ⟨s⟩ := MarshallHall.freeGroup_finite_permutation_separator_proved H g hg
  let : Fintype s.State := s.stateFintype
  exact ⟨{
    State := s.State
    representation := s.representation
    base := s.base
    fixes_subgroup := s.fixes_subgroup
    separates := s.separates
  }⟩

end LERFChallenge
