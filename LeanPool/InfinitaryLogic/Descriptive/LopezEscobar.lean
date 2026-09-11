/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.LopezEscobar.Separation
import LeanPool.InfinitaryLogic.Descriptive.LogicAction
/-!
# The López–Escobar theorem (issue #10, Unit 6)

The public face of issue #10: the hard direction (`lopez_escobar`, `Methods/LopezEscobar/`) and
the easy direction (`lopezEscobar_easy`, `Descriptive/LopezEscobarEasy.lean`) packaged as the
two-directional equivalences.

* `lopezEscobar_iff` — over a countable relational vocabulary, a class of coded countable
  structures is Borel and isomorphism-invariant **iff** it is the model class of a single
  `L_ω₁ω`-sentence;
* `lopezEscobar_action_iff` — the same with invariance under the logic action of
  `S∞ = Equiv.Perm ℕ`, a rewrite by `actionInvariant_iff_isomorphismInvariant` (#27);
* `invariantMeasurableSets_eq_range_modelsOf` (and its isomorphism-invariant twin) — issue
  #28's post-#10 target 7, the collection equality
  `{B | MeasurableSet B ∧ ActionInvariant B} = Set.range ModelsOf`.  It lives here, in the
  López–Escobar facade, rather than in `Descriptive/InvariantMeasurableModels.lean`, so that
  the σ-algebra files stay below the hard theorem in the import order.

Only the hard direction is new; the reverse of each is the easy direction, and the action form
adds no mathematical content beyond the orbit = isomorphism identification.
-/

namespace FirstOrder.Language

open FirstOrder Structure Set

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- **The López–Escobar theorem**: over a countable relational vocabulary, a class of coded
countable structures is Borel and isomorphism-invariant exactly when it is the class of models
of a single `L_ω₁ω`-sentence.  The forward direction is the hard theorem of issue #10
(`lopez_escobar`); the reverse is `lopezEscobar_easy`. -/
theorem lopezEscobar_iff {B : Set (StructureSpace L)} :
    (MeasurableSet B ∧ IsomorphismInvariant B) ↔ ∃ φ : L.Sentenceω, B = ModelsOf φ := by
  constructor
  · rintro ⟨hB, hinv⟩
    exact lopez_escobar hB hinv
  · rintro ⟨φ, rfl⟩
    exact lopezEscobar_easy φ

/-- **The López–Escobar theorem, action form**: invariance under the logic action of
`S∞ = Equiv.Perm ℕ` may replace isomorphism invariance, by the orbit = isomorphism identity
`actionInvariant_iff_isomorphismInvariant` (#27). -/
theorem lopezEscobar_action_iff {B : Set (StructureSpace L)} :
    (MeasurableSet B ∧ ActionInvariant B) ↔ ∃ φ : L.Sentenceω, B = ModelsOf φ := by
  rw [actionInvariant_iff_isomorphismInvariant, lopezEscobar_iff]

/-! ## The collection equality (issue #28, target 7) -/

end FirstOrder.Language
