/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.WellOrdering.Boundedness
/-!
# Undefinability of well-ordering (issue #12, step 6 layer 3)

The packaging layer, deliberately distinguishing two inequivalent statements:

* the **strong** form is layer 2's uniform order-type bound
  (`wellOrder_type_boundedness_relational`): every sentence all of whose models are
  well-ordered has its order types bounded by a single countable ordinal;
* the **weak** form proved here (`wellOrdering_undefinable_relational`): no sentence has as
  models *exactly* the structures whose interpreted relation is a well-order — the ordinal
  `α` produced by the bound is itself a well-order of type `α`, so it would be a model
  violating its own bound.

The countable-coded/Borel form of undefinability (¬ MeasurableSet of the well-order class,
issue #33) is **not** this statement: it additionally needs López–Escobar and the countable
fragment-elementary-substructure bridge, and stays in #33.

The witness structure interprets **every** binary relation symbol as the ordinal order and
every other arity as empty — this avoids deciding equality against the distinguished symbol
`lt`, which a general language does not support.
-/

namespace FirstOrder.Language

open FirstOrder Structure

/-- The all-arities relation family on an ordinal's type: binary positions get the ordinal
order, every other arity is empty. -/
def ordRel (α : Ordinal.{0}) : ∀ n, (Fin n → α.ToType) → Prop
  | 2, v => v 0 < v 1
  | _, _ => False

/-- The comparison structure on an ordinal's type over a relational language: every binary
relation symbol is the ordinal order, everything else is empty. -/
@[reducible] def ordinalStructure (L : Language.{0, 0}) [L.IsRelational] (α : Ordinal.{0}) :
    L.Structure α.ToType where
  funMap {n} f _ := (‹L.IsRelational› n).elim f
  RelMap {n} _ v := ordRel α n v

/-- Any binary relation symbol of the comparison structure is the ordinal order. -/
theorem ordinalStructure_relMap (L : Language.{0, 0}) [L.IsRelational] (α : Ordinal.{0})
    (lt : L.Relations 2) (x y : α.ToType) :
    @RelMap L α.ToType (ordinalStructure L α) 2 lt ![x, y] ↔ x < y := by
  show ordRel α 2 ![x, y] ↔ x < y
  simp [ordRel, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The comparison structure interprets any binary relation symbol as a well-order. -/
theorem ordinalStructure_isWellOrder (L : Language.{0, 0}) [L.IsRelational] (α : Ordinal.{0})
    (lt : L.Relations 2) :
    IsWellOrder α.ToType fun x y => @RelMap L α.ToType (ordinalStructure L α) 2 lt ![x, y] := by
  have h : (fun x y : α.ToType => @RelMap L α.ToType (ordinalStructure L α) 2 lt ![x, y])
      = (· < ·) := funext fun x => funext fun y => propext (ordinalStructure_relMap L α lt x y)
  rw [h]
  infer_instance

/-- **Undefinability of well-ordering** (weak form, relational/countable): no sentence has
as models exactly the structures whose interpreted relation is a well-order.  From the
uniform order-type bound: the bounding ordinal `α`, as a comparison structure, would be a
model of order type `α < α`. -/
theorem wellOrdering_undefinable_relational {L : Language.{0, 0}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] (lt : L.Relations 2) :
    ¬ ∃ φ : L.Sentenceω, ∀ (M : Type) (_ : L.Structure M),
        (Sentenceω.Realize φ M ↔ IsWellOrder M fun x y : M => RelMap lt ![x, y]) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨α, hα, hbound⟩ := wellOrder_type_boundedness_relational φ lt
    (fun M inst h => (hφ M inst).mp h)
  let instα : L.Structure α.ToType := ordinalStructure L α
  have hwo := ordinalStructure_isWellOrder L α lt
  have hreal : Sentenceω.Realize φ α.ToType := (hφ α.ToType instα).mpr hwo
  have hb := hbound α.ToType instα hreal
  have hiso : (fun x y : α.ToType => RelMap lt ![x, y]) ≃r
      ((· < ·) : α.ToType → α.ToType → Prop) :=
    ⟨_root_.Equiv.refl _, fun {a b} => (ordinalStructure_relMap L α lt a b).symm⟩
  rw [RelIso.ordinalType_congr hiso, Ordinal.type_toType] at hb
  exact absurd hb (lt_irrefl α)

end FirstOrder.Language
