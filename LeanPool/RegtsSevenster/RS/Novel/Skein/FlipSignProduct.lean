/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.StateFlipSet

/-!
# The sign product of a flip sequence

The port signs of a sequence of chain flips, at the evolving
colours: the closed form is a per-label product of the initial
sign to the instance count times a triangular-number sign, so a
sequence in which every label occurs evenly contributes exactly
`(−1)^length`.
-/

@[expose] public section

namespace RS



variable {α : Type} {ℓ : ℕ}

open scoped Classical in
/-- The colour relabel of one flip. -/
noncomputable def flipColours (f : α → Fin (2 * ℓ))
    (p : α × α) : α → Fin (2 * ℓ) :=
  fun a => if a = p.1 ∨ a = p.2 then oddPartner ℓ (f a) else f a

/-- The accumulated port-sign product of a flip sequence, at the
evolving colours. -/
noncomputable def flipSignProd (f : α → Fin (2 * ℓ)) :
    List (α × α) → ℤ
  | [] => 1
  | p :: L =>
      oddPartnerSign ℓ (f p.1) * oddPartnerSign ℓ (f p.2) *
        flipSignProd (flipColours f p) L

/-- The label instances of a flip sequence. -/
def flipLabels (L : List (α × α)) : List α :=
  L.flatMap (fun p => [p.1, p.2])

/-- No flips list no labels. -/
theorem flipLabels_nil : flipLabels ([] : List (α × α)) = [] := rfl

/-- One more flip lists its two labels first. -/
theorem flipLabels_cons (p : α × α) (L : List (α × α)) :
    flipLabels (p :: L) = p.1 :: p.2 :: flipLabels L := rfl

variable {k : ℕ}

open Classical in
/-- The labels with odd instance count. -/
noncomputable def oddCountLabels (L : List (α × α)) : Finset α :=
  (flipLabels L).toFinset.filter
    (fun a => (flipLabels L).count a % 2 = 1)

open Classical in
/-- A label counts as odd exactly when it occurs an odd number of
times — the labels the fold has actually moved. -/
theorem mem_oddCountLabels {L : List (α × α)} {a : α} :
    a ∈ oddCountLabels L ↔ (flipLabels L).count a % 2 = 1 := by
  unfold oddCountLabels
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    refine ⟨List.mem_toFinset.mpr ?_, h⟩
    by_contra hmem
    rw [List.count_eq_zero_of_not_mem hmem] at h
    cases h

end RS
