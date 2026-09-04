/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Lomega1omega.Semantics
import Mathlib.ModelTheory.Basic
/-!
# Coding Space for Countable Structures

This file defines the space of countable relational L-structures coded as
functions from relation queries to Bool. The carrier-parametric versions
`RelQueryOn L α` and `StructureSpaceOn L α` generalize over the carrier type,
while `RelQuery L` and `StructureSpace L` specialize to carrier ℕ.

## Main Definitions

- `RelQueryOn L α`: Carrier-parametric relation query index type.
- `StructureSpaceOn L α`: Carrier-parametric coding space `RelQueryOn L α → Bool`.
- `RelQuery L`: Relation queries for carrier ℕ (= `RelQueryOn L ℕ`).
- `StructureSpace L`: The coding space for ℕ-structures (= `StructureSpaceOn L ℕ`).
- `StructureSpaceOn.toStructure`: Decode a code into an L-structure on carrier α.
- `StructureSpaceOn.ofStructure`: Encode a structure into a code.

## Main Results

- `StructureSpaceOn.relMap_toStructure`: Relation holding in the decoded structure
  corresponds to the code returning `true`.
- `StructureSpaceOn.toStructure_ofStructure`: Round-trip from structure to code to structure
  preserves relation satisfaction.
-/

universe u v

namespace FirstOrder

namespace Language

open Structure

variable (L : Language.{u, v})

/-- A carrier-parametric relation query: a choice of relation symbol and a tuple
of elements from the carrier type α. -/
def RelQueryOn (α : Type*) := Σ (R : Σ l, L.Relations l), (Fin R.1 → α)

/-- A relation query for carrier ℕ. -/
def RelQuery := RelQueryOn L ℕ

variable {L}

instance [Countable (Σ l, L.Relations l)] [Countable α] : Countable (RelQueryOn L α) := by
  unfold RelQueryOn
  infer_instance

instance [Countable (Σ l, L.Relations l)] : Countable (RelQuery L) := by
  unfold RelQuery
  infer_instance

/-- The carrier-parametric coding space for L-structures on α: for each relation
query, does the relation hold on that tuple? This is an `abbrev` so type class
resolution can see through it. -/
abbrev StructureSpaceOn (L : Language.{u, v}) (α : Type*) := RelQueryOn L α → Bool

/-- The coding space for countable L-structures on ℕ: for each relation query,
does the relation hold on that tuple? -/
def StructureSpace (L : Language.{u, v}) := StructureSpaceOn L ℕ

/-- The pair space for carrier α. -/
abbrev StructurePairSpaceOn (L : Language.{u, v}) (α : Type*) :=
  StructureSpaceOn L α × StructureSpaceOn L α

namespace StructureSpaceOn

variable {α : Type*}

/-- Decode a code into an L-structure on carrier α.
Relations are determined by the code; functions are eliminated by `IsRelational`. -/
@[reducible] noncomputable def toStructure [L.IsRelational]
    (c : StructureSpaceOn L α) : L.Structure α where
  funMap := fun f => isEmptyElim f
  RelMap := fun {_} R v => c ⟨⟨_, R⟩, v⟩ = true

/-- The relation holding in the decoded structure corresponds to the code value. -/
@[simp]
theorem relMap_toStructure [L.IsRelational] (c : StructureSpaceOn L α)
    {l : ℕ} (R : L.Relations l) (v : Fin l → α) :
    @Structure.RelMap _ _ c.toStructure _ R v ↔ c ⟨⟨l, R⟩, v⟩ = true :=
  Iff.rfl

/-- Encode an L-structure on carrier α into a code.
Takes an explicit structure instance rather than using the typeclass. -/
noncomputable def ofStructure [L.IsRelational]
    (inst : L.Structure α) : StructureSpaceOn L α :=
  fun ⟨⟨_, R⟩, v⟩ => @decide _ (Classical.dec (@Structure.RelMap _ _ inst _ R v))

/-- Round-trip: decoding the code of a structure preserves relation satisfaction. -/
theorem toStructure_ofStructure [L.IsRelational]
    (inst : L.Structure α) {l : ℕ} (R : L.Relations l) (v : Fin l → α) :
    @Structure.RelMap _ _ (ofStructure inst).toStructure _ R v ↔
    @Structure.RelMap _ _ inst _ R v := by
  simp only [relMap_toStructure, ofStructure, decide_eq_true_eq]

/-- Round-trip: encoding a decoded structure recovers the original code. -/
theorem ofStructure_toStructure [L.IsRelational]
    (c : StructureSpaceOn L α) : ofStructure (c.toStructure) = c := by
  funext ⟨⟨l, R⟩, v⟩
  simp only [ofStructure, relMap_toStructure]
  cases c ⟨⟨l, R⟩, v⟩ <;> simp

end StructureSpaceOn

-- ℕ-specialized wrappers for dot-notation on `StructureSpace`.
namespace StructureSpace

/-- Decode a code into an L-structure on ℕ. -/
@[reducible] noncomputable def toStructure [L.IsRelational]
    (c : StructureSpace L) : L.Structure ℕ :=
  StructureSpaceOn.toStructure c

/-- The relation holding in the decoded structure corresponds to the code value. -/
@[simp]
theorem relMap_toStructure [L.IsRelational] (c : StructureSpace L)
    {l : ℕ} (R : L.Relations l) (v : Fin l → ℕ) :
    @Structure.RelMap _ _ c.toStructure _ R v ↔ c ⟨⟨l, R⟩, v⟩ = true :=
  Iff.rfl

/-- Encode an L-structure on ℕ into a code. -/
noncomputable def ofStructure [L.IsRelational]
    (inst : L.Structure ℕ) : StructureSpace L :=
  StructureSpaceOn.ofStructure inst

/-- Round-trip: decoding the code of a structure preserves relation satisfaction. -/
theorem toStructure_ofStructure [L.IsRelational]
    (inst : L.Structure ℕ) {l : ℕ} (R : L.Relations l) (v : Fin l → ℕ) :
    @Structure.RelMap _ _ (ofStructure inst).toStructure _ R v ↔
    @Structure.RelMap _ _ inst _ R v := by
  simp only [relMap_toStructure, ofStructure, StructureSpaceOn.ofStructure, decide_eq_true_eq]

/-- Round-trip: encoding a decoded structure recovers the original code. -/
theorem ofStructure_toStructure [L.IsRelational]
    (c : StructureSpace L) : ofStructure (c.toStructure) = c := by
  funext ⟨⟨l, R⟩, v⟩
  simp only [ofStructure, StructureSpaceOn.ofStructure, relMap_toStructure]
  cases c ⟨⟨l, R⟩, v⟩ <;> simp

end StructureSpace

end Language

end FirstOrder
