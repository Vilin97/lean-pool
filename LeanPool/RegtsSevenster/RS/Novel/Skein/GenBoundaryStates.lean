/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.MixedPartition

/-!
# Boundary states over general label types

A boundary state gives one colour per boundary label: even when
the boundary edge is outside the Eulerian subset, odd when it
participates.  The labels are an arbitrary type, because the
single-pair gluing decomposition works label-locally and its
states are indexed by the surviving labels of a `gluePair` rather
than by an initial segment of ℕ.
-/

@[expose] public section

namespace RS

/-- A boundary state over an arbitrary label type: one colour per
label, even (`Sum.inl`) when the boundary edge is outside the
Eulerian subset and odd (`Sum.inr`) when it participates. -/
def GenBoundaryState (k ℓ : ℕ) (α : Type) : Type :=
  α → (Fin k ⊕ Fin (2 * ℓ))

/-- Boundary states over a finite label type are finite in
number. -/
instance {k ℓ : ℕ} {α : Type} [Fintype α] [DecidableEq α] :
    Fintype (GenBoundaryState k ℓ α) :=
  inferInstanceAs (Fintype (α → (Fin k ⊕ Fin (2 * ℓ))))

/-- And can be compared, classically. -/
noncomputable instance {k ℓ : ℕ} {α : Type} :
    DecidableEq (GenBoundaryState k ℓ α) :=
  Classical.decEq _

/-- There are `(k + 2ℓ)` colours per label, so that many states to
the number of labels. -/
theorem card_genBoundaryState (k ℓ : ℕ) (α : Type) [Fintype α]
    [DecidableEq α] :
    Fintype.card (GenBoundaryState k ℓ α) =
      (k + 2 * ℓ) ^ Fintype.card α := by
  change Fintype.card (α → (Fin k ⊕ Fin (2 * ℓ))) = _
  rw [Fintype.card_fun, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin]

/-- The boundary-membership constraint over a general label type. -/
def genBoundarySubsetMatches {k ℓ : ℕ} {α : Type}
    (W : Fragment α) (s : Finset W.Flag)
    (st : GenBoundaryState k ℓ α) : Prop :=
  ∀ i : α, W.boundaryFlag i ∈ s ↔ ∃ c, st i = Sum.inr c

section GenHelpers

variable {k ℓ : ℕ} {α : Type} {W : Fragment α} {s : Finset W.Flag}
  {st : GenBoundaryState k ℓ α}

/-- An even-coloured label's boundary flag is outside matching
subsets. -/
theorem genBoundaryFlag_not_mem_of_even
    (hbnd : genBoundarySubsetMatches W s st)
    (i : α) (c : Fin k) (hst : st i = Sum.inl c) :
    W.boundaryFlag i ∉ s := by
  intro hmem
  obtain ⟨d, hd⟩ := (hbnd i).mp hmem
  simp [hst] at hd

end GenHelpers

/-- The even-colouring boundary constraint over a general label
type. -/
def genEvenBoundaryMatch {k ℓ : ℕ} {α : Type} {W : Fragment α}
    (F : EdgeSubset W) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (ψ : F.EvenColouring k) : Prop :=
  ∀ (i : α) (c : Fin k) (hst : st i = Sum.inl c),
    ψ.val ⟨W.boundaryFlag i,
      genBoundaryFlag_not_mem_of_even hbnd i c hst⟩ = c

end RS
