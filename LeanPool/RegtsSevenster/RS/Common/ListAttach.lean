/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Attached lists and list-to-finset products

Two facts used wherever a proof enumerates a finite set as a list
and then maps or multiplies over it: mapping a function defined on
the attached subtype agrees with mapping the total function, and a
list product is the finset product of the finset the list
enumerates.
-/

@[expose] public section

namespace RS

/-- Mapping over an attached list agrees with mapping the total
function, when the two agree pointwise. -/
theorem attachWith_map_eq {β γ : Type*} {p : β → Prop}
    (fsub : {g : β // p g} → γ) (ftot : β → γ)
    (hpt : ∀ (g : β) (hg : p g), fsub ⟨g, hg⟩ = ftot g) :
    ∀ (l : List β) (H : ∀ g ∈ l, p g),
      (l.attachWith p H).map fsub = l.map ftot
  | [], _ => rfl
  | g :: t, H => by
    rw [List.attachWith_cons, List.map_cons, List.map_cons, hpt,
      attachWith_map_eq fsub ftot hpt t _]

/-- A list product is the finset product of the finset the list
enumerates. -/
theorem list_map_prod_eq_finset_prod {β M : Type*} [CommMonoid M]
    (s : Finset β) (l : List β)
    (hl : (↑l : Multiset β) = s.val) (f : β → M) :
    (l.map f).prod = ∏ g ∈ s, f g := by
  rw [← Multiset.prod_coe, ← Multiset.map_coe, hl]
  rfl

end RS
