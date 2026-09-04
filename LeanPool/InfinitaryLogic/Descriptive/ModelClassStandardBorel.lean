/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Descriptive.Polish
import LeanPool.InfinitaryLogic.Descriptive.SatisfactionBorel
/-!
# Standard Borel Structure on the Model Class

This file shows that `ModelsOf φ` (the set of coded ℕ-models of an Lω₁ω sentence φ)
inherits `StandardBorelSpace` as a measurable subspace of the structure space.

## Main Results

- `modelsOf_isClopenable`: `ModelsOf φ` is clopenable (admits a finer Polish
  topology making it clopen).
- `modelsOf_standardBorel`: The subtype `↥(ModelsOf φ)` is standard Borel.
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- `ModelsOf φ` is clopenable in the structure space: there exists a finer Polish
topology making it both open and closed. This follows from `ModelsOf φ` being
measurable in a Polish + Borel space. -/
theorem modelsOf_isClopenable (φ : L.Sentenceω) :
    PolishSpace.IsClopenable (ModelsOf φ) :=
  (modelsOf_measurableSet φ).isClopenable

/-- The subtype of coded ℕ-models of φ is standard Borel: it inherits a
standard Borel structure as a measurable subspace of the standard Borel
structure space. -/
instance modelsOf_standardBorel (φ : L.Sentenceω) :
    StandardBorelSpace ↥(ModelsOf φ) :=
  (modelsOf_measurableSet φ).standardBorel

/-- The space of coded ℕ-models of φ, as a standard Borel space. -/
abbrev ModelSpace (φ : L.Sentenceω) := ↥(ModelsOf φ)

end Language

end FirstOrder
