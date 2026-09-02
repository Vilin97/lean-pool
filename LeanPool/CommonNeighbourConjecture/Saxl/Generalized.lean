/-
Copyright (c) 2026 Aluna Rizzoli and Adam R. Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aluna Rizzoli, Adam R. Thomas
-/

import LeanPool.CommonNeighbourConjecture.Saxl.Basic

/-!
# Generalized Saxl adjacency

The generalized adjacency definition stores the two displayed vertices in the
first two positions of an ordered base.  This file shows that the order is
irrelevant: generalized adjacency is exactly membership of two distinct
vertices in a common set-like base of the required size.
-/

namespace Saxl

variable (G Ω : Type*) [Group G] [MulAction G Ω]

/-- Two vertices are generalized-adjacent exactly when they are distinct
members of a common base of size `tail + 2`. -/
theorem generalizedAdjacent_iff_mem_base (tail : Nat) (x y : Ω) :
    GeneralizedAdjacent G Ω tail x y ↔
      x ≠ y ∧ ∃ b : Fin (tail + 2) → Ω,
        IsSetBaseTuple G Ω b ∧ x ∈ Set.range b ∧ y ∈ Set.range b := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨?_, Fin.cons x (Fin.cons y z), hz, ?_, ?_⟩
    · have h01 : (0 : Fin (tail + 2)) ≠ 1 := by
        intro h
        have := congrArg Fin.val h
        simp at this
      simpa using hz.1.ne h01
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  · rintro ⟨hxy, b, hb, ⟨i, hi⟩, ⟨j, hj⟩⟩
    have hij : i ≠ j := by
      intro h
      apply hxy
      rw [← hi, ← hj, h]
    obtain ⟨j', rfl⟩ :=
      (Fin.eq_self_or_eq_succAbove i j).resolve_left hij.symm
    let e : Fin (tail + 2) → Fin (tail + 2) :=
      Fin.cons i <| Fin.cons (i.succAbove j') fun k ↦ i.succAbove (j'.succAbove k)
    have he_injective : Function.Injective e := by
      dsimp only [e]
      apply Fin.cons_injective_of_injective
      · rintro ⟨k, hk⟩
        cases k using Fin.cases with
        | zero => exact Fin.succAbove_ne i j' hk
        | succ k => exact Fin.succAbove_ne i (j'.succAbove k) hk
      · apply Fin.cons_injective_of_injective
        · rintro ⟨k, hk⟩
          exact Fin.succAbove_ne j' k (Fin.succAbove_right_injective hk)
        · intro k l hkl
          apply Fin.succAbove_right_injective (p := j')
          apply Fin.succAbove_right_injective (p := i)
          exact hkl
    have he_surjective : Function.Surjective e := by
      intro k
      cases k using Fin.succAboveCases i with
      | x => exact ⟨0, by simp [e]⟩
      | p k =>
          cases k using Fin.succAboveCases j' with
          | x => exact ⟨1, by simp [e]⟩
          | p k => exact ⟨k.succ.succ, by simp [e]⟩
    let z : Fin tail → Ω := fun k ↦ b (i.succAbove (j'.succAbove k))
    have htuple : Fin.cons x (Fin.cons y z) = b ∘ e := by
      funext k
      cases k using Fin.cases with
      | zero => simpa [e] using hi.symm
      | succ k =>
          cases k using Fin.cases with
          | zero => simpa [e] using hj.symm
          | succ k => simp [e, z]
    refine ⟨z, ?_⟩
    rw [htuple]
    refine ⟨hb.1.comp he_injective, ?_⟩
    intro g hg
    apply hb.2 g
    intro k
    obtain ⟨l, rfl⟩ := he_surjective k
    exact hg l

end Saxl
