/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.WellOrdering.Descent
import LeanPool.InfinitaryLogic.Methods.WellOrdering.ModelExtraction
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

end FirstOrder.Language
