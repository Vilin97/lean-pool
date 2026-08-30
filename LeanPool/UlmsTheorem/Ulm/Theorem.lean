/-
Copyright (c) 2026 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth
-/

import LeanPool.UlmsTheorem.Ulm.Classification
import LeanPool.UlmsTheorem.Ulm.Invariance

/-!
# Ulm's theorem

Public entry point for the Ulm-theorem track of the project.
-/

namespace UlmsTheorem

open Cardinal Ordinal

universe u

variable (p : ℕ) [hp : Fact p.Prime]

/-- Public easy direction of Ulm's theorem: an isomorphism preserves all
classical Ulm invariants. -/
theorem ulm_invariants_of_iso {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (hiso : Nonempty (G ≃+ H)) :
    ∀ α : Ordinal.{0},
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H) := by
  rcases hiso with ⟨φ⟩
  intro α
  exact ulmInvariant_iso_invariant (p := p) φ α

/-- Public hard direction of Ulm's theorem: equal classical Ulm invariants imply isomorphism
for countable reduced abelian `p`-groups. -/
theorem iso_of_ulm_invariants {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    (hGred : IsReducedPGroup p G) (hHred : IsReducedPGroup p H)
    (hinv : ∀ α : Ordinal.{0},
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H)) :
    Nonempty (G ≃+ H) := by
  exact iso_of_ulmInvariant_eq (p := p) hGred hHred hinv

/-- Named forward direction for running the proof in two separate parts. -/
theorem ulm_theorem_forward {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (hiso : Nonempty (G ≃+ H)) :
    ∀ α : Ordinal.{0},
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H) :=
  ulm_invariants_of_iso (p := p) hiso

/-- Named backward direction for running the proof in two separate parts. -/
theorem ulm_theorem_backward {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    (hGred : IsReducedPGroup p G) (hHred : IsReducedPGroup p H)
    (hinv : ∀ α : Ordinal.{0},
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H)) :
    Nonempty (G ≃+ H) :=
  iso_of_ulm_invariants (p := p) hGred hHred hinv

/-- Ulm's theorem: two countable reduced abelian p-groups are isomorphic iff
their classical Ulm invariants agree. -/
theorem ulm_theorem {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    (hGred : IsReducedPGroup p G) (hHred : IsReducedPGroup p H) :
    Nonempty (G ≃+ H) ↔
    ∀ α : Ordinal.{0},
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H) := by
  constructor
  · exact ulm_theorem_forward (p := p)
  · exact ulm_theorem_backward (p := p) hGred hHred

end UlmsTheorem
