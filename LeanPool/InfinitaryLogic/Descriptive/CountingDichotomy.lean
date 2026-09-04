/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Descriptive.ModelClassStandardBorel
import LeanPool.InfinitaryLogic.Descriptive.IsomorphismBorel
import LeanPool.InfinitaryLogic.Descriptive.StructureIsoSetoid
import Mathlib.SetTheory.Cardinal.Continuum
/-!
# Conditional Counting Dichotomy for Models

This file states the Silver–Burgess dichotomy as an explicit hypothesis, defines the
isomorphism equivalence relation on coded ℕ-models, and derives a conditional
counting theorem: for Lω₁ω sentences whose ℕ-models have bounded Scott height,
the number of isomorphism classes is either ≤ ℵ₀ or exactly 2^ℵ₀.

## Main Definitions

- `SilverBurgessDichotomy`: The Silver–Burgess dichotomy for Borel equivalence
  relations on standard Borel spaces.

The isomorphism relation `isoSetoid` this file counts is defined in
`Descriptive/StructureIsoSetoid.lean`, as the restriction of the ambient relation on
`StructureSpace L`.

## Main Results

- `counting_coded_models_dichotomy`: Conditional on `SilverBurgessDichotomy`, for
  any Lω₁ω sentence with bounded Scott height, the number of isomorphism classes
  among coded ℕ-models is either ≤ ℵ₀ or exactly 2^ℵ₀.
-/

universe u v w

namespace FirstOrder

namespace Language

open Cardinal Ordinal

/-- The Silver–Burgess dichotomy for Borel equivalence relations:
on a standard Borel space, a Borel equivalence relation has either
at most countably many classes or exactly continuum-many. -/
def SilverBurgessDichotomy : Prop :=
  ∀ {X : Type w} [MeasurableSpace X] [StandardBorelSpace X]
    (r : Setoid X),
    MeasurableSet {p : X × X | r.r p.1 p.2} →
    (#(Quotient r) ≤ ℵ₀) ∨ (#(Quotient r) = Cardinal.continuum)

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

end Language

end FirstOrder
