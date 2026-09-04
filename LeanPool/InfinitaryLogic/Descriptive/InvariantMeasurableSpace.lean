/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Descriptive.LogicAction
/-!
# The invariant σ-algebras on the structure space (issue #28, commit 1)

Two σ-algebras of *invariant* measurable classes of coded structures, and their equality.

- `MeasurableSpace.smulInvariant G m`: the **generic** construction — for any `SMul G X` and any
  explicitly supplied base `MeasurableSpace X`, the σ-algebra of `m`-measurable `G`-invariant sets.
  Genuinely reusable, and taking the base measurable space as an explicit argument avoids
  recursive-instance ambiguity when specializing.
- `FirstOrder.Language.actionInvariantMeasurableSpace`: the specialization to the `S∞`-action on
  `StructureSpace L`.
- `FirstOrder.Language.isoInvariantMeasurableSpace`: the σ-algebra of measurable
  isomorphism-invariant classes.
- `FirstOrder.Language.actionInvariantMeasurableSpace_eq_isoInvariantMeasurableSpace`: the two
  coincide, via `actionInvariant_iff_isomorphismInvariant`.

Everything here is elementary: **no Polishness and no symbol-countability hypothesis** is used —
the invariance predicates are closed under complement and countable union on the nose, and the
σ-algebra equality is a pointwise membership equivalence. (`[L.IsRelational]` is needed only for the
isomorphism-invariant side and the equality, since `IsomorphismInvariant` is defined via decoded
structures.) Measurability of concrete classes such as `ModelsOf φ` is the compatibility commit.
-/

open MeasureTheory

/-! ## The generic invariant σ-algebra -/

/-- **The generic invariant σ-algebra.** For an `SMul G X` action and an explicitly supplied base
`MeasurableSpace X`, the measurable `G`-invariant sets form a σ-algebra (a sub-σ-algebra of `m`).
The base measurable space is explicit so specializing never triggers recursive instance search. -/
@[reducible] def MeasurableSpace.smulInvariant (G : Type*) {X : Type*} [SMul G X]
    (m : MeasurableSpace X) : MeasurableSpace X where
  MeasurableSet' B := MeasurableSet[m] B ∧ ∀ (g : G) (x : X), x ∈ B ↔ g • x ∈ B
  measurableSet_empty := ⟨m.measurableSet_empty, fun _ _ => by simp⟩
  measurableSet_compl _ hB := ⟨hB.1.compl, fun g x => by
    simp only [Set.mem_compl_iff, not_iff_not]; exact hB.2 g x⟩
  measurableSet_iUnion _ hf := ⟨MeasurableSet.iUnion fun n => (hf n).1, fun g x => by
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨n, hn⟩ => ⟨n, ((hf n).2 g x).mp hn⟩,
      fun ⟨n, hn⟩ => ⟨n, ((hf n).2 g x).mpr hn⟩⟩⟩

/-- Membership in the generic invariant σ-algebra: measurable and invariant. -/
theorem MeasurableSpace.measurableSet_smulInvariant {G X : Type*} [SMul G X]
    {m : MeasurableSpace X} {B : Set X} :
    MeasurableSet[MeasurableSpace.smulInvariant G m] B
      ↔ MeasurableSet[m] B ∧ ∀ (g : G) (x : X), x ∈ B ↔ g • x ∈ B := Iff.rfl

namespace FirstOrder.Language

variable {L : Language.{0, 0}}

/-! ## Closure of the invariance predicates -/

/-- Action invariance is closed under complement. -/
theorem ActionInvariant.compl {B : Set (StructureSpace L)} (h : ActionInvariant B) :
    ActionInvariant Bᶜ := fun σ c => by
  simp only [Set.mem_compl_iff, not_iff_not]; exact h σ c

/-- Action invariance is closed under countable union. -/
theorem ActionInvariant.iUnion {f : ℕ → Set (StructureSpace L)}
    (h : ∀ n, ActionInvariant (f n)) : ActionInvariant (⋃ n, f n) := fun σ c => by
  simp only [Set.mem_iUnion]
  exact ⟨fun ⟨n, hn⟩ => ⟨n, (h n σ c).mp hn⟩, fun ⟨n, hn⟩ => ⟨n, (h n σ c).mpr hn⟩⟩

theorem actionInvariant_empty : ActionInvariant (∅ : Set (StructureSpace L)) :=
  fun _ _ => by simp

variable [L.IsRelational]

/-- Isomorphism invariance is closed under complement. -/
theorem IsomorphismInvariant.compl {B : Set (StructureSpace L)} (h : IsomorphismInvariant B) :
    IsomorphismInvariant Bᶜ := fun c d hcd => by
  simp only [Set.mem_compl_iff]; rw [h c d hcd]

/-- Isomorphism invariance is closed under countable union. -/
theorem IsomorphismInvariant.iUnion {f : ℕ → Set (StructureSpace L)}
    (h : ∀ n, IsomorphismInvariant (f n)) : IsomorphismInvariant (⋃ n, f n) := fun c d hcd => by
  simp only [Set.mem_iUnion]
  exact ⟨fun ⟨n, hn⟩ => ⟨n, (h n c d hcd).mp hn⟩, fun ⟨n, hn⟩ => ⟨n, (h n c d hcd).mpr hn⟩⟩

theorem isomorphismInvariant_empty : IsomorphismInvariant (∅ : Set (StructureSpace L)) :=
  fun _ _ _ => by simp

/-! ## The two named invariant σ-algebras -/

/-- The σ-algebra of measurable **isomorphism-invariant** classes of coded structures. -/
@[reducible] def isoInvariantMeasurableSpace : MeasurableSpace (StructureSpace L) where
  MeasurableSet' B := MeasurableSet B ∧ IsomorphismInvariant B
  measurableSet_empty := ⟨MeasurableSet.empty, isomorphismInvariant_empty⟩
  measurableSet_compl _ hB := ⟨hB.1.compl, hB.2.compl⟩
  measurableSet_iUnion _ hf := ⟨MeasurableSet.iUnion fun n => (hf n).1,
    IsomorphismInvariant.iUnion fun n => (hf n).2⟩

end FirstOrder.Language

namespace FirstOrder.Language

variable {L : Language.{0, 0}}

/-- The σ-algebra of measurable **action-invariant** classes, i.e. the generic invariant σ-algebra
for the `S∞`-action on `StructureSpace L` over the product σ-algebra. Needs no relationality. -/
@[reducible] def actionInvariantMeasurableSpace : MeasurableSpace (StructureSpace L) :=
  MeasurableSpace.smulInvariant (Equiv.Perm ℕ)
    (inferInstanceAs (MeasurableSpace (StructureSpace L)))

/-! ## Membership iff lemmas -/

/-- A class is `actionInvariantMeasurableSpace`-measurable iff it is measurable and
action-invariant. -/
theorem measurableSet_actionInvariantMeasurableSpace {B : Set (StructureSpace L)} :
    MeasurableSet[actionInvariantMeasurableSpace] B ↔ MeasurableSet B ∧ ActionInvariant B :=
  Iff.rfl

/-- A class is `isoInvariantMeasurableSpace`-measurable iff it is measurable and
isomorphism-invariant. -/
theorem measurableSet_isoInvariantMeasurableSpace [L.IsRelational] {B : Set (StructureSpace L)} :
    MeasurableSet[isoInvariantMeasurableSpace] B ↔ MeasurableSet B ∧ IsomorphismInvariant B :=
  Iff.rfl

/-! ## The two σ-algebras coincide -/

/-- **The invariant σ-algebras coincide.** Action invariance and isomorphism invariance define the
same measurable classes, by `actionInvariant_iff_isomorphismInvariant`. No Polishness or
symbol-countability hypothesis is used. -/
theorem actionInvariantMeasurableSpace_eq_isoInvariantMeasurableSpace [L.IsRelational] :
    (actionInvariantMeasurableSpace : MeasurableSpace (StructureSpace L)) =
      isoInvariantMeasurableSpace := by
  refine MeasurableSpace.ext fun B => ?_
  rw [measurableSet_actionInvariantMeasurableSpace, measurableSet_isoInvariantMeasurableSpace,
    actionInvariant_iff_isomorphismInvariant]

end FirstOrder.Language
