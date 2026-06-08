/-
Copyright (c) 2026 Paul Mure, Joonhyup Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Mure, Joonhyup Lee
-/
import Lean.Meta
import Lean.Elab

namespace Lean.Order.CompleteLattice

open PartialOrder
-- The meet (`⊓ₚ`) and top (`⊤ₚ`) notations and the `meet_le_*` helper lemmas
-- below use the `ₚ`/`'` suffix to avoid clashing with the `Lean.Order` complete
-- lattice operations (`⊓`, `⊤`, `meet_le_left`, `meet_le_right`) that Lean core
-- introduced (via `Std.Internal.Do.Assertion`) and which are now in scope here.
/-- The binary meet of a complete lattice, as the infimum of `{x, y}`. -/
noncomputable instance instMinCompleteLattice [CompleteLattice α] : Min α where
  min x y := inf (λ z => z = x ∨ z = y)

/-- The top element of a complete lattice, as the supremum of the whole carrier. -/
noncomputable def top [CompleteLattice α] : α := sup (λ _ => True)

/-- Notation `⊤ₚ` for the Paco lattice top (to avoid clashing with core's `⊤`). -/
scoped notation "⊤ₚ" => top
/-- Notation `x ⊓ₚ y` for the Paco lattice meet (to avoid clashing with core's `⊓`). -/
scoped infixl:60 " ⊓ₚ " => min

theorem top_spec [CompleteLattice α] (x : α) : x ⊑ ⊤ₚ := le_sup _ True.intro

theorem meet_spec [CompleteLattice α] (x y : α) : z ⊑ x ⊓ₚ y ↔ z ⊑ x ∧ z ⊑ y := by
  constructor <;> simp only [min, inf_spec]
  · exact λ h => ⟨h _ <| Or.intro_left _ rfl, h _ <| Or.intro_right _ rfl⟩
  · intro ⟨hx, hy⟩
    intros; rename_i h
    cases h <;> (rename_i h; subst h; assumption)

theorem meet_le_left' [CompleteLattice α] (x : α) : x ⊑ z → x ⊓ₚ y ⊑ z := by
  simp only [min]
  intros
  apply rel_trans _ (by assumption)
  apply sup_le
  intros; rename_i h; apply h; left; rfl

theorem meet_le_right' [CompleteLattice α] (y : α) : y ⊑ z → x ⊓ₚ y ⊑ z := by
  simp only [min]
  intros
  apply rel_trans _ (by assumption)
  apply sup_le
  intros; rename_i h; apply h; right; rfl

theorem meet_top [CompleteLattice α] (x : α) : x ⊓ₚ ⊤ₚ = x :=
  rel_antisymm (meet_le_left' _ rel_refl) <| (meet_spec x ⊤ₚ).mpr ⟨rel_refl, top_spec _⟩

theorem meet_comm [CompleteLattice α] (x y : α) : x ⊓ₚ y = y ⊓ₚ x :=
  rel_antisymm
    ((meet_spec _ _).mpr ⟨meet_le_right' _ rel_refl, meet_le_left' _ rel_refl⟩)
    ((meet_spec _ _).mpr ⟨meet_le_right' _ rel_refl, meet_le_left' _ rel_refl⟩)

theorem meet_assoc [CompleteLattice α] (x y z : α) : x ⊓ₚ y ⊓ₚ z = x ⊓ₚ (y ⊓ₚ z) := by
  apply rel_antisymm <;> (rw [meet_spec]; apply And.intro)
  · apply meet_le_left'; apply meet_le_left'; apply rel_refl
  · rw [meet_spec]; apply And.intro
    · apply meet_le_left'; apply meet_le_right'; apply rel_refl
    · apply meet_le_right'; apply rel_refl
  · rw [meet_spec]; apply And.intro
    · apply meet_le_left'; apply rel_refl
    · apply meet_le_right'; apply meet_le_left'; apply rel_refl
  · apply meet_le_right'; apply meet_le_right'; apply rel_refl

end Lean.Order.CompleteLattice

namespace Lean4Itree

open Lean.Order PartialOrder CompleteLattice

-- note that we don't require monotonicity for f
-- this is the version in paco
theorem monotonize_mon [Lean.Order.CompleteLattice α] (f : α → α) (r : α) :
  monotone (λ x => inf (λ z => ∃ y, z = f y ∧ r ⊓ₚ x ⊑ y)) := by
  simp only [monotone]
  intros _ _ h
  apply le_sup; intro z ⟨y, heq, h'⟩
  subst heq
  apply Lean.Order.sup_le; intro _ le
  apply le
  exists y; apply And.intro rfl
  apply rel_trans _ h'
  rw [meet_spec]
  apply And.intro
  · apply meet_le_left' _ rel_refl
  · apply meet_le_right' _ h

theorem plfp_arg_mon [Lean.Order.CompleteLattice α] {f : α → α} (hm : monotone f) (r : α) :
  monotone (λ x => f (r ⊓ₚ x)) := by
  simp only [monotone]
  intros
  apply hm
  rw [meet_spec]
  apply And.intro
  · apply meet_le_left'; apply rel_refl
  · apply meet_le_right'; assumption

/--
Parameterized least fixed point, we don't "monotonize" f (⌈f⌉) as in paco for now
version in paco: lfp (λ x => inf (λ z => ∃ y, z = f y ∧ r ⊓ₚ x ⊑ y)
-/
noncomputable def plfp [Lean.Order.CompleteLattice α] (f : α → α) {hm : monotone f} (r : α) :=
  lfp_monotone (λ x => f (r ⊓ₚ x)) (plfp_arg_mon hm r)

/-- The "unfolded" parameterized least fixed point `r ⊓ₚ plfp f r`. -/
noncomputable def uplfp [Lean.Order.CompleteLattice α] (f : α → α) {hm : monotone f} (r : α) :=
  r ⊓ₚ (plfp f (hm := hm) r)

theorem plfp_mon [Lean.Order.CompleteLattice α] {f : α → α} (hm : monotone f) :
  monotone (plfp f (hm := hm)) := by
  simp only [monotone, plfp]
  intros
  apply le_sup; intros; apply Lean.Order.sup_le; intros
  rename_i h; apply h
  rename_i h' _; apply rel_trans _ h'; simp only; apply hm
  rw [meet_spec]; apply And.intro
  · apply rel_trans _ (by assumption)
    apply meet_le_left'; apply rel_refl
  · apply meet_le_right'; apply rel_refl

theorem plfp_init [Lean.Order.CompleteLattice α] {f : α → α} (hm : monotone f) :
  lfp_monotone f hm = plfp f (hm := hm) ⊤ₚ := by
  apply rel_antisymm <;>
  (apply le_sup; intros; apply Lean.Order.sup_le; intros; rename_i h; apply h) <;>
  (rename_i h' _; apply rel_trans _ h'; simp only) <;>
  (rw [meet_comm, meet_top] <;> apply rel_refl)

theorem plfp_unfold [Lean.Order.CompleteLattice α] {f : α → α} (hm : monotone f) :
  plfp f (hm := hm) r = f (uplfp f (hm := hm) r) := by
  rw [plfp]
  delta lfp_monotone
  have h := plfp_arg_mon hm r
  rw [lfp_fix h]
  congr

theorem uplfp_goal [Lean.Order.CompleteLattice α] {f : α → α} (hm : monotone f) :
  r ⊑ z ∨ plfp f (hm := hm) r ⊑ z → uplfp (hm := hm) f r ⊑ z := by
  simp only [uplfp]
  intro h; cases h
  · apply meet_le_left'; assumption
  · apply meet_le_right'; assumption

theorem uplfp_hyp [Lean.Order.CompleteLattice α] {f : α → α} (hm : monotone f) :
  z ⊑ uplfp (hm := hm) f r → z ⊑ r ∧ z ⊑ plfp f (hm := hm) r := by
  simp only [uplfp]
  rw [meet_spec]
  exact id

theorem fun_sup_equiv {α : Sort u} {β : α → Sort v} [(x : α) → CompleteLattice (β x)]
  (c : ((x : α) → β x) → Prop) (x : α) :
  fun_sup c x = inf λ y => ∀ f, c f → f x ⊑ y := by
  rw [inf, fun_sup]
  apply rel_antisymm
  · apply sup_le; intro y ⟨f, inc, eqf⟩
    subst eqf
    apply le_sup
    intros; rename_i h; apply h _ inc
  · rw [sup_spec]
    intros
    rename_i h
    apply h
    intros
    apply le_sup; rename_i f _; exists f

theorem plfp_acc_aux [Lean.Order.CompleteLattice α] {f : α → α} (hm : monotone f) (r x : α) :
  plfp f (hm := hm) r ⊑ x ↔ plfp f (hm := hm) (r ⊓ₚ x) ⊑ x := by
  constructor <;> (intro h; apply rel_trans _ h)
  · apply plfp_mon hm; exact meet_le_left' _ rel_refl
  · apply lfp_le_of_le
    apply rel_trans _ (by rw [plfp_unfold] <;> apply rel_refl)
    apply hm
    rw [uplfp, meet_spec]
    apply And.intro
    · rw [meet_spec]
      exact And.intro (meet_le_left' _ rel_refl) (meet_le_right' _ h)
    · exact meet_le_right' _ rel_refl

theorem plfp_acc [Lean.Order.CompleteLattice α] {f : α → α} (hm : monotone f) l r
  (obg : ∀ φ, φ ⊑ r → φ ⊑ l → plfp f (hm := hm) φ ⊑ l) : plfp f (hm := hm) r ⊑ l := by
  rw [plfp_acc_aux hm]
  apply obg
  · apply meet_le_left' _ rel_refl
  · apply meet_le_right' _ rel_refl

end Lean4Itree
