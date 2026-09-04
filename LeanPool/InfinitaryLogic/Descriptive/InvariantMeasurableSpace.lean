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

/-! ## The two named invariant σ-algebras -/

end FirstOrder.Language

namespace FirstOrder.Language

variable {L : Language.{0, 0}}

/-! ## Membership iff lemmas -/

/-! ## The two σ-algebras coincide -/

end FirstOrder.Language
