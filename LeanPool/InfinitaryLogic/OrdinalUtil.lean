/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.SetTheory.Ordinal.Family

/-!
# Small ordinal facts

Neutral helpers about countable ordinals, used by the Scott refinement count, the Borel
`BFEquiv` analysis, and the ranked-thinness package. Nothing here is specific to infinitary
logic, descriptive set theory, or any one of those consumers.

Both shapes of the countability statement are provided: `Set.Countable (Set.Iio β)` and the
`Countable` *instance* on the coercion, since consumers need one or the other and converting
at each site is noise.
-/

universe u

namespace InfinitaryLogic

/-- For `β < ω₁`, the ordinals below `β` form a countable **type**. -/
theorem countable_Iio_of_lt_omega1 (β : Ordinal.{0}) (hβ : β < Ordinal.omega 1) :
    Countable (Set.Iio β) := by
  have hle : β.card ≤ Cardinal.aleph0 := by
    have hlt : β.card < Cardinal.aleph 1 := Cardinal.lt_omega_iff_card_lt.mp hβ
    rw [← Cardinal.succ_aleph0] at hlt
    exact Order.lt_succ_iff.mp hlt
  rw [← Cardinal.mk_le_aleph0_iff]
  calc Cardinal.mk (Set.Iio β)
      = Cardinal.lift.{1, 0} β.card := Cardinal.mk_Iio_ordinal β
    _ ≤ Cardinal.lift.{1, 0} Cardinal.aleph0 := Cardinal.lift_le.mpr hle
    _ = Cardinal.aleph0 := by simp

/-- The same fact as a `Set.Countable`. -/
theorem setCountable_Iio_of_lt_omega1 (β : Ordinal.{0}) (hβ : β < Ordinal.omega 1) :
    Set.Countable (Set.Iio β) :=
  Set.countable_coe_iff.mp (countable_Iio_of_lt_omega1 β hβ)

/-- `ω₁` absorbs `+ ω`: a countable ordinal stays countable after appending `ω`.

The standard way to exceed a bound `α < ω₁` while staying countable — `α + ω` is at least `α`,
infinite, and still countable — which is what order-type diagonalizations against a boundedness
theorem need. -/
theorem add_omega0_lt_omega1 {α : Ordinal.{0}} (hα : α < (Cardinal.aleph 1).ord) :
    α + Ordinal.omega0 < (Cardinal.aleph 1).ord := by
  rw [Cardinal.ord_aleph, Cardinal.lt_omega_iff_card_lt] at hα ⊢
  rw [← Cardinal.succ_aleph0] at hα
  rw [Ordinal.card_add, Ordinal.card_omega0, ← Cardinal.succ_aleph0]
  calc α.card + Cardinal.aleph0 ≤ Cardinal.aleph0 + Cardinal.aleph0 :=
        add_le_add (Order.lt_succ_iff.mp hα) le_rfl
    _ = Cardinal.aleph0 := Cardinal.aleph0_add_aleph0
    _ < Order.succ Cardinal.aleph0 := Order.lt_succ _

/-! ## Rank is monotone in the relation -/

/-- If `r ⊆ s` are both well-founded, ranks under `r` are bounded by ranks under `s`. -/
theorem rank_le_rank_of_imp {α : Type*} {r s : α → α → Prop} [IsWellFounded α r]
    [IsWellFounded α s] (h : ∀ a b, r a b → s a b) (a : α) :
    IsWellFounded.rank r a ≤ IsWellFounded.rank s a := by
  induction a using IsWellFounded.induction r with
  | ind a ih =>
    rw [IsWellFounded.rank_eq r, IsWellFounded.rank_eq s]
    refine Ordinal.iSup_le fun b => ?_
    exact (Order.succ_le_succ (ih b b.2)).trans
      (Ordinal.le_iSup (fun c : {c // s c a} => Order.succ (IsWellFounded.rank s c)) ⟨b, h _ _ b.2⟩)

end InfinitaryLogic
