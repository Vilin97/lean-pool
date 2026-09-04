/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.ModelTheory.HanfSpectrum.LadderSyntax
import Mathlib.SetTheory.Cardinal.Aleph

/-!
# The ordinal interpretation of the ladder index order

The ladder syntax (`LadderSyntax.lean`) keeps all clause indexing internal to the order on
`Index α = (α + 2).ToType`; this file is the deferred `typein` layer that the SEMANTIC files
use to interpret indices as ordinals:

* `idxVal : Index α → Ordinal` (with `idxOf` inverse) — order-isomorphic onto `Iio (α + 2)`;
* the endpoint values `idxVal_bot = 0`, `idxVal_top = α + 1`;
* the structural transfers: `covBy_iff_idxVal` (adjacency = ordinal successor) and
  `isSuccLimit_iff_idxVal` (order limits = ordinal limits);
* `countable_index_of_lt_omega1` — the `[Countable (Index α)]` hypothesis of the sentence,
  discharged for every `α < ω₁`.
-/

namespace FirstOrder

namespace Language

namespace HanfLadder

open Ordinal

variable {α : Ordinal.{0}}

/-- The ordinal value of a ladder index (the inverse of `ToType.mk`). -/
noncomputable def idxVal (i : Index α) : Ordinal.{0} :=
  (ToType.mk.symm i : Set.Iio (α + 2)).1

theorem idxVal_lt (i : Index α) : idxVal i < α + 2 :=
  (ToType.mk.symm i).2

/-- The ladder index with a given ordinal value. -/
noncomputable def idxOf (β : Ordinal.{0}) (h : β < α + 2) : Index α :=
  ToType.mk ⟨β, Set.mem_Iio.mpr h⟩

@[simp]
theorem idxVal_idxOf (β : Ordinal.{0}) (h : β < α + 2) : idxVal (idxOf (α := α) β h) = β := by
  rw [idxVal, idxOf, OrderIso.symm_apply_apply]

@[simp]
theorem idxOf_idxVal (i : Index α) : idxOf (idxVal i) (idxVal_lt i) = i := by
  rw [idxOf]
  -- `eq_symm_apply` states the iff in the opposite direction from the lemma it replaces, and
  -- takes the two points implicitly, so this is `.mp` of one argument rather than `.mpr` of three
  exact (OrderIso.eq_symm_apply _).mp (Subtype.ext rfl)

theorem idxVal_lt_idxVal_iff {i j : Index α} : idxVal i < idxVal j ↔ i < j := by
  rw [idxVal, idxVal, show ((ToType.mk.symm i : Set.Iio (α + 2)) : Ordinal)
      < (ToType.mk.symm j : Set.Iio (α + 2)) ↔ ToType.mk.symm i < ToType.mk.symm j from
    Iff.rfl]
  exact ToType.mk.symm.lt_iff_lt

theorem idxVal_le_idxVal_iff {i j : Index α} : idxVal i ≤ idxVal j ↔ i ≤ j := by
  rw [← not_lt, ← not_lt, not_iff_not]
  exact idxVal_lt_idxVal_iff

theorem idxVal_injective : Function.Injective (idxVal (α := α)) := by
  intro i j hij
  exact le_antisymm (idxVal_le_idxVal_iff.mp hij.le) (idxVal_le_idxVal_iff.mp hij.ge)

@[simp]
theorem idxVal_bot : idxVal (⊥ : Index α) = 0 := by
  have h0 : (0 : Ordinal) < α + 2 := lt_of_le_of_lt zero_le (idxVal_lt ⊥)
  have h := idxVal_le_idxVal_iff.mpr (bot_le (a := idxOf (α := α) 0 h0))
  rw [idxVal_idxOf] at h
  exact le_antisymm h zero_le

@[simp]
theorem idxVal_top : idxVal (⊤ : Index α) = α + 1 := by
  have h1 : (α + 1 : Ordinal) < α + 2 := by
    have he : (α + 2 : Ordinal) = Order.succ (α + 1) := by
      rw [Order.succ_eq_add_one, add_assoc, one_add_one_eq_two]
    exact lt_of_lt_of_eq (Order.lt_succ _) he.symm
  have h := idxVal_le_idxVal_iff.mpr (le_top (a := idxOf (α := α) (α + 1) h1))
  rw [idxVal_idxOf] at h
  refine le_antisymm ?_ h
  exact Order.lt_succ_iff.mp (lt_of_lt_of_eq (idxVal_lt (⊤ : Index α))
    (by rw [Order.succ_eq_add_one, add_assoc, one_add_one_eq_two]))

/-- Adjacency in the index order is ordinal successor on values. -/
theorem covBy_iff_idxVal {i j : Index α} : i ⋖ j ↔ idxVal j = idxVal i + 1 := by
  constructor
  · intro hij
    refine le_antisymm ?_ ?_
    · by_contra hlt
      rw [not_le] at hlt
      have hi1 : idxVal i + 1 < α + 2 := lt_trans hlt (idxVal_lt j)
      refine hij.2 (c := idxOf (idxVal i + 1) hi1) ?_ ?_
      · rw [← idxVal_lt_idxVal_iff, idxVal_idxOf]
        exact lt_of_lt_of_eq (Order.lt_succ _) (Order.succ_eq_add_one _)
      · rw [← idxVal_lt_idxVal_iff, idxVal_idxOf]
        exact hlt
    · rw [← Order.succ_eq_add_one, Order.succ_le_iff]
      exact idxVal_lt_idxVal_iff.mpr hij.1
  · intro hval
    have hij : i < j := idxVal_lt_idxVal_iff.mp
      (lt_of_lt_of_eq (lt_of_lt_of_eq (Order.lt_succ _) (Order.succ_eq_add_one _)) hval.symm)
    refine ⟨hij, fun {c} hic hcj => ?_⟩
    have h1 := idxVal_lt_idxVal_iff.mpr hic
    have h2 := idxVal_lt_idxVal_iff.mpr hcj
    rw [hval, ← Order.succ_eq_add_one, Order.lt_succ_iff] at h2
    exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)

/-- Order limits of the index order are ordinal limits of values. -/
theorem isSuccLimit_iff_idxVal {j : Index α} :
    Order.IsSuccLimit j ↔ Order.IsSuccLimit (idxVal j) := by
  constructor
  · intro hj
    constructor
    · intro hmin
      refine hj.not_isMin ?_
      have h0 : idxVal j = 0 := le_antisymm (hmin zero_le : idxVal j ≤ 0) zero_le
      intro b _
      rw [← idxVal_le_idxVal_iff, h0]
      exact zero_le
    · intro β hβ
      have hβ2 : β < α + 2 := lt_trans hβ.1 (idxVal_lt j)
      refine hj.isSuccPrelimit (idxOf β hβ2) ?_
      rw [covBy_iff_idxVal, idxVal_idxOf]
      exact hβ.succ_eq.symm.trans (Order.succ_eq_add_one β)
  · intro hv
    constructor
    · intro hmin
      refine hv.not_isMin ?_
      have h0 : j = ⊥ := le_antisymm (hmin bot_le : j ≤ ⊥) bot_le
      intro b _
      rw [h0, idxVal_bot]
      exact zero_le
    · intro i hij
      rw [covBy_iff_idxVal] at hij
      exact hv.isSuccPrelimit (idxVal i)
        (Order.succ_eq_iff_covBy.mp ((Order.succ_eq_add_one (idxVal i)).trans hij.symm))

/-- Below `ω₁` the index order is countable — the formation hypothesis of the ladder
sentence. -/
theorem countable_index_of_lt_omega1 (hα : α < Ordinal.omega 1) : Countable (Index α) := by
  refine Cardinal.mk_le_aleph0_iff.mp ?_
  rw [Cardinal.mk_toType]
  have hlim : Order.IsSuccLimit (Ordinal.omega 1) := Cardinal.isSuccLimit_omega 1
  have h2 : α + 2 < Ordinal.omega 1 := by
    have h1 : α + 1 < Ordinal.omega 1 := Order.succ_eq_add_one α ▸ hlim.succ_lt hα
    have he : (α + 2 : Ordinal) = (α + 1) + 1 := by rw [add_assoc, one_add_one_eq_two]
    exact lt_of_eq_of_lt he (Order.succ_eq_add_one (α + 1) ▸ hlim.succ_lt h1)
  exact Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_omega_iff_card_lt.mp h2)

end HanfLadder

end Language

end FirstOrder
