/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Descriptive.LopezEscobar
import LeanPool.InfinitaryLogic.Descriptive.WellOrderBridge
import LeanPool.InfinitaryLogic.OrdinalUtil
/-!
# Non-Borelness of the countable well-order class (issue #33)

The descriptive-set-theoretic payoff of Marker's boundedness theorem: the class **WO** of
countable well-orders is **not Borel** as a subset of the logic space.

```
theorem wellOrderClass_not_measurableSet (lt : L.Relations 2) : ¬ MeasurableSet (wellOrderClass lt)
```

Were it Borel, López–Escobar (#10) would give a sentence `φ` with `ModelsOf φ = WO` — but only
over **coded** structures, whose carrier is `ℕ`.  The bridge from there to arbitrary models is
the fragment-elementary substructure machinery (#13), applied to `φ ⊓ infiniteAxiom` so that
finite models cannot escape:

* `exists_countable_defect_seed` — a structure whose distinguished relation is not a well-order
  carries a **countable nonempty seed** of witnesses (a trichotomy or transitivity failure, or
  the range of an infinite descending sequence) whose presence forces the same failure in every
  subset containing it;
* `isWellOrder_of_realize` — hence every model of `φ ⊓ infiniteAxiom` is well-ordered: seed a
  countable fragment-elementary substructure with the defect, transport it to the carrier `ℕ`,
  and the resulting code would be a member of `ModelsOf φ = WO` that is not a well-order.

Marker's Corollary 4.27 then bounds the order types of all models of `φ ⊓ infiniteAxiom` by a
single countable ordinal, which `exists_code_type_eq` contradicts.
-/

namespace FirstOrder.Language

open FirstOrder Structure Set

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-! ## The endpoint -/

/-- **The countable well-order class is not Borel** (issue #33): no Borel set of codes consists
exactly of the well-ordered ones. -/
theorem wellOrderClass_not_measurableSet (lt : L.Relations 2) :
    ¬ MeasurableSet (wellOrderClass lt) := by
  intro hB
  -- López–Escobar: the class is defined by a sentence, on codes
  obtain ⟨φ, hφ⟩ := lopez_escobar hB (wellOrderClass_isomorphismInvariant lt)
  -- every model of `φ ⊓ infiniteAxiom` is well-ordered, so its order types are bounded
  obtain ⟨α, hα, hbound⟩ := wellOrder_type_boundedness (φ.and (infiniteAxiom L)) lt
    (fun M inst hreal => isWellOrder_of_realize lt hφ.symm M hreal)
  -- but the class realizes every countably infinite order type, and `α + ω` is one
  obtain ⟨c, hc, htype⟩ := exists_code_type_eq (L := L) lt
    (β := α + Ordinal.omega0) le_add_self (InfinitaryLogic.add_omega0_lt_omega1 hα)
  have hcφ : @Sentenceω.Realize L (φ.and (infiniteAxiom L)) ℕ c.toStructure := by
    let : L.Structure ℕ := c.toStructure
    have hinf : Sentenceω.Realize (infiniteAxiom L) ℕ := realize_infiniteAxiom.mpr inferInstance
    refine (BoundedFormulaω.realize_and _ _).mpr ⟨?_, hinf⟩
    have hmem : c ∈ ModelsOf φ := by rw [← hφ]; exact hc
    exact hmem
  have hb : @Ordinal.type ℕ
      (fun x y : ℕ => @Structure.RelMap L ℕ c.toStructure 2 lt ![x, y]) hc < α :=
    hbound ℕ c.toStructure hcφ
  rw [htype] at hb
  exact absurd hb (not_lt.mpr le_self_add)

end FirstOrder.Language
