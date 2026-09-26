/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.ContentCount
public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.StabCount

/-!
# Colour classes of prescribed composition

Colourings `Fin n → Fin N` with prescribed fibre sizes
`α : Fin N → ℕ`: the class count (`n!` divided by the fibre
factorials, in product form), the fixed-colouring permutation
character `colourChar`, and the Fubini exchange expressing its
weighted permutation sum as a sum of stabilizer weights over the
class.
-/

@[expose] public section

namespace RS

open Finset

variable {n N : ℕ}

/-- The content multiset of a composition. -/
def compContent (α : Fin N → ℕ) : Multiset (Fin N) :=
  ∑ j : Fin N, Multiset.replicate (α j) j

/-- A composition's content multiset carries each colour as often as
prescribed. -/
theorem compContent_count (α : Fin N → ℕ) (j : Fin N) :
    (compContent α).count j = α j := by
  classical
  rw [compContent, Multiset.count_sum']
  rw [Finset.sum_eq_single j
    (fun b _ hb => by
      rw [Multiset.count_replicate, ite_eq_right hb])
    (fun h => absurd (Finset.mem_univ j) h)]
  rw [Multiset.count_replicate, ite_eq_left rfl]

/-- Its size is the composition's total. -/
theorem compContent_card (α : Fin N → ℕ) :
    Multiset.card (compContent α) = ∑ j : Fin N, α j := by
  rw [compContent]
  simp [Multiset.card_replicate]

/-- The composition content as a symmetric power, given total
`n`. -/
def compContentSym (α : Fin N → ℕ) (hsum : ∑ j : Fin N, α j = n) :
    Sym (Fin N) n :=
  ⟨compContent α, by rw [compContent_card, hsum]⟩

/-- A colouring has fibre sizes `α` iff its content is
`compContent α`. -/
theorem fibreCard_eq_iff (g : Fin n → Fin N) (α : Fin N → ℕ) :
    (∀ j, fibreCard g j = α j) ↔ (content g).1 = compContent α := by
  constructor
  · intro h
    refine Multiset.ext.mpr fun j => ?_
    rw [← fibreCard_eq_count, compContent_count, h j]
  · intro h j
    rw [fibreCard_eq_count, h, compContent_count]

/-- **The colour-class count**: the number of colourings with
fibre sizes `α` times the product of the fibre factorials is
`n!`. -/
theorem card_colourClass (α : Fin N → ℕ)
    (hsum : ∑ j : Fin N, α j = n) :
    Fintype.card {g : Fin n → Fin N // ∀ j, fibreCard g j = α j} *
      ∏ j : Fin N, (α j).factorial = n.factorial := by
  classical
  obtain ⟨f₀, hf₀⟩ := exists_content_eq (compContentSym α hsum)
  have h := orbit_stab f₀ (card_fixing_perms f₀)
  have hval : (content f₀).1 = compContent α := by
    rw [hf₀]; rfl
  have hcount : ∀ j : Fin N, (content f₀).1.count j = α j := by
    intro j
    rw [hval, compContent_count]
  have hequiv :
      Fintype.card {g : Fin n → Fin N // content g = content f₀} =
      Fintype.card
        {g : Fin n → Fin N // ∀ j, fibreCard g j = α j} := by
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro g
    constructor
    · intro hc
      refine (fibreCard_eq_iff g α).mpr ?_
      rw [congrArg Subtype.val hc, hval]
    · intro hc
      apply Subtype.ext
      rw [(fibreCard_eq_iff g α).mp hc, hval]
  rw [hequiv] at h
  rw [Finset.prod_congr rfl (fun j _ => by rw [hcount j])] at h
  exact h

open scoped Classical in
/-- The permutation character of the colour class `α`: the number
of colourings with fibre sizes `α` fixed by `π`. -/
noncomputable def colourChar (α : Fin N → ℕ)
    (π : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter
    (fun g : Fin n → Fin N =>
      (∀ j, fibreCard g j = α j) ∧ g ∘ π = g)).card

open scoped Classical in
/-- **Fubini for the colour character**: the `colourChar`-weighted
permutation sum is the sum, over the colour class, of the
stabilizer weight sums. -/
theorem sum_colourChar_weight (α : Fin N → ℕ)
    (W : Equiv.Perm (Fin n) → ℂ) :
    (∑ π : Equiv.Perm (Fin n), (colourChar α π : ℂ) * W π) =
      ∑ g : {g : Fin n → Fin N // ∀ j, fibreCard g j = α j},
        ∑ π ∈ Finset.univ.filter
          (fun π : Equiv.Perm (Fin n) => g.1 ∘ π = g.1), W π := by
  calc (∑ π : Equiv.Perm (Fin n), (colourChar α π : ℂ) * W π)
      = ∑ π : Equiv.Perm (Fin n), ∑ g : Fin n → Fin N,
          (if (∀ j, fibreCard g j = α j) ∧ g ∘ π = g
            then W π else 0) := by
        refine Finset.sum_congr rfl fun π _ => ?_
        rw [colourChar, ← Finset.sum_filter, Finset.sum_const,
          nsmul_eq_mul]
    _ = ∑ g : Fin n → Fin N, ∑ π : Equiv.Perm (Fin n),
          (if (∀ j, fibreCard g j = α j) ∧ g ∘ π = g
            then W π else 0) := Finset.sum_comm
    _ = ∑ g : Fin n → Fin N,
          (if (∀ j, fibreCard g j = α j)
            then ∑ π ∈ Finset.univ.filter
              (fun π : Equiv.Perm (Fin n) => g ∘ π = g), W π
            else 0) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        by_cases hg : ∀ j, fibreCard g j = α j
        · rw [ite_eq_left hg, Finset.sum_filter]
          exact Finset.sum_congr rfl fun π _ => by
            by_cases hf : g ∘ π = g
            · rw [ite_eq_left ⟨hg, hf⟩, ite_eq_left hf]
            · rw [ite_eq_right (fun hc => hf hc.2), ite_eq_right hf]
        · rw [ite_eq_right hg]
          rw [Finset.sum_eq_zero fun π _ =>
            ite_eq_right (fun hc => hg hc.1)]
    _ = ∑ g : {g : Fin n → Fin N // ∀ j, fibreCard g j = α j},
          ∑ π ∈ Finset.univ.filter
            (fun π : Equiv.Perm (Fin n) => g.1 ∘ π = g.1), W π := by
        rw [← Finset.sum_filter]
        exact Finset.sum_subtype _ (fun g => by simp) _

end RS
