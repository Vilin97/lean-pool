/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Descriptive.CodeTransport
import LeanPool.InfinitaryLogic.Descriptive.LopezEscobarEasy
import LeanPool.InfinitaryLogic.ModelTheory.WellOrdering
/-!
# The coded class of countable well-orders (issue #33, step 1)

`wellOrderClass lt` is the set of codes whose distinguished binary relation is a well-order of
the carrier `ℕ` — the class **WO** as a subset of the logic space.  This file freezes the class
and supplies the two facts the non-Borelness argument needs about it:

* `wellOrderClass_isomorphismInvariant` — it is isomorphism-invariant, so López–Escobar applies
  to it once it is assumed Borel;
* `exists_code_type_eq` — **every countably infinite order type is realized in it**: for
  `ω ≤ β < ω₁` some code of the class has order type exactly `β`.  This is what contradicts the
  uniform bound of Marker's Corollary 4.27.

The comparison structures are the arbitrary-language ones already built for
`wellOrdering_undefinable` (`ordinalStructureFull`), transported to the carrier `ℕ` by the
generic code-transport API.
-/

namespace FirstOrder.Language

open FirstOrder Structure Set

variable {L : Language.{0, 0}} [L.IsRelational]

/-! ## The class -/

/-- **The coded well-order class**: codes whose distinguished relation well-orders `ℕ`. -/
def wellOrderClass (lt : L.Relations 2) : Set (StructureSpace L) :=
  {c | IsWellOrder ℕ fun x y : ℕ => @Structure.RelMap L ℕ c.toStructure 2 lt ![x, y]}

theorem mem_wellOrderClass_iff (lt : L.Relations 2) (c : StructureSpace L) :
    c ∈ wellOrderClass lt ↔
      IsWellOrder ℕ fun x y : ℕ => @Structure.RelMap L ℕ c.toStructure 2 lt ![x, y] :=
  Iff.rfl

/-- An `L`-isomorphism of decoded structures is an order isomorphism of the distinguished
relations. -/
def relIsoOfEquiv (lt : L.Relations 2) {c d : StructureSpace L}
    (f : @Language.Equiv L ℕ ℕ c.toStructure d.toStructure) :
    (fun x y : ℕ => @Structure.RelMap L ℕ c.toStructure 2 lt ![x, y]) ≃r
      fun x y : ℕ => @Structure.RelMap L ℕ d.toStructure 2 lt ![x, y] where
  toEquiv := @Language.Equiv.toEquiv L ℕ ℕ c.toStructure d.toStructure f
  map_rel_iff' {a b} := by
    have h := @Language.Equiv.map_rel L ℕ ℕ c.toStructure d.toStructure f 2 lt ![a, b]
    rwa [show (⇑f ∘ ![a, b]) = ![f a, f b] from funext fun i => by fin_cases i <;> rfl] at h

/-- **The class is isomorphism-invariant** — the hypothesis López–Escobar consumes. -/
theorem wellOrderClass_isomorphismInvariant (lt : L.Relations 2) :
    IsomorphismInvariant (wellOrderClass lt) := by
  rintro c d ⟨f⟩
  constructor
  · intro hc
    have : IsWellOrder ℕ fun x y : ℕ => @Structure.RelMap L ℕ c.toStructure 2 lt ![x, y] := hc
    exact (relIsoOfEquiv lt f).symm.toRelEmbedding.isWellOrder
  · intro hd
    have : IsWellOrder ℕ fun x y : ℕ => @Structure.RelMap L ℕ d.toStructure 2 lt ![x, y] := hd
    exact (relIsoOfEquiv lt f).toRelEmbedding.isWellOrder

/-! ## Every countably infinite order type occurs -/

/-- Below `ω₁` the ordinal's type is countable. -/
theorem countable_toType_of_lt_omega1 {β : Ordinal.{0}} (hβ : β < (Cardinal.aleph 1).ord) :
    Countable β.ToType := by
  have hcard : β.card < Cardinal.aleph 1 := Cardinal.lt_ord.mp hβ
  rw [show Cardinal.aleph 1 = Order.succ (Cardinal.aleph 0) from by
    rw [Cardinal.succ_aleph, zero_add], Cardinal.aleph_zero] at hcard
  rw [← Cardinal.mk_le_aleph0_iff, Cardinal.mk_toType]
  exact Order.lt_succ_iff.mp hcard

/-- From `ω` on, the ordinal's type is infinite. -/
theorem infinite_toType_of_omega0_le {β : Ordinal.{0}} (hβ : Ordinal.omega0 ≤ β) :
    Infinite β.ToType := by
  rw [Cardinal.infinite_iff, Cardinal.mk_toType]
  simpa using Ordinal.card_le_card hβ

/-- **The order-type supply**: every countably infinite ordinal is the order type of some code
in the well-order class.  The witness is the arbitrary-language comparison structure on `β`,
transported to the carrier `ℕ`. -/
theorem exists_code_type_eq (lt : L.Relations 2) {β : Ordinal.{0}}
    (hinf : Ordinal.omega0 ≤ β) (hcnt : β < (Cardinal.aleph 1).ord) :
    ∃ c : StructureSpace L, ∃ h : IsWellOrder ℕ
        fun x y : ℕ => @Structure.RelMap L ℕ c.toStructure 2 lt ![x, y],
      @Ordinal.type ℕ (fun x y : ℕ => @Structure.RelMap L ℕ c.toStructure 2 lt ![x, y]) h = β := by
  have : Countable β.ToType := countable_toType_of_lt_omega1 hcnt
  have : Infinite β.ToType := infinite_toType_of_omega0_le hinf
  have : Nonempty β.ToType := inferInstance
  let instβ : L.Structure β.ToType := ordinalStructureFull L β
  let e : β.ToType ≃ ℕ := (nonempty_equiv_of_countable (α := β.ToType) (β := ℕ)).some
  -- the code's relation is the ordinal order read through `e.symm`
  have hrel : ∀ x y : ℕ, @Structure.RelMap L ℕ
      (StructureSpaceOn.encodeViaEquiv e).toStructure 2 lt ![x, y] ↔ e.symm x < e.symm y := by
    intro x y
    rw [StructureSpaceOn.toStructure_encodeViaEquiv_eq, Equiv.inducedStructure_RelMap]
    rw [show (⇑e.symm ∘ ![x, y]) = ![e.symm x, e.symm y] from
      funext fun i => by fin_cases i <;> rfl]
    exact ordinalStructureFull_relMap L β lt _ _
  have hiso : (fun x y : ℕ => @Structure.RelMap L ℕ
      (StructureSpaceOn.encodeViaEquiv e).toStructure 2 lt ![x, y]) ≃r
        ((· < ·) : β.ToType → β.ToType → Prop) :=
    ⟨e.symm, fun {a b} => (hrel a b).symm⟩
  have hwo : IsWellOrder ℕ (fun x y : ℕ => @Structure.RelMap L ℕ
      (StructureSpaceOn.encodeViaEquiv e).toStructure 2 lt ![x, y]) :=
    hiso.toRelEmbedding.isWellOrder
  exact ⟨StructureSpaceOn.encodeViaEquiv e, hwo, by
    rw [RelIso.ordinalType_congr hiso, Ordinal.type_toType]⟩

end FirstOrder.Language
