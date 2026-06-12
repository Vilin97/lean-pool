/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import LeanPool.TwoColoringOneRound.LowerBound.Defs

/-!
# Distributed2Coloring: Definitions

This file exposes the key definitions intended for downstream use.

Most internal development lives under `Distributed2Coloring.LowerBound` and
`Distributed2Coloring.UpperBound`; users should not need to import those files directly unless
they want to follow the detailed proofs.
-/

namespace Distributed2Coloring

open MeasureTheory
open scoped unitInterval

/-!
## One-round classical algorithms

`Rand` is the unit interval `[0,1]` (as a measurable space). A `ClassicalAlgorithm` is a measurable
local rule `f : Rand × Rand × Rand → Fin 2` applied to i.i.d. labels on the directed cycle.

The quantity `ClassicalAlgorithm.p alg` is the probability that an oriented edge is monochromatic:
`alg.f` agrees on consecutive windows `(x₀,x₁,x₂)` and `(x₁,x₂,x₃)` under i.i.d. labels.
-/

/-- The source of local randomness for one-round algorithms: the unit interval `[0,1]`. -/
abbrev Rand : Type := I

/-- The two output colors. -/
abbrev Color := Fin 2

/-- A seed assignment of i.i.d. labels to `n` vertices. -/
abbrev Samples (n : ℕ) : Type := Fin n → Rand

/--
A one-round *classical* distributed algorithm for 2-coloring the directed cycle.

It is a measurable local rule `f` that reads the three labels on a directed length-2 neighborhood
and outputs one of two colors.
-/
structure ClassicalAlgorithm where
  /-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
  f : Rand × Rand × Rand → Color
  measurable_f : Measurable f

namespace ClassicalAlgorithm

/--
The event that a fixed oriented edge is monochromatic.

We represent an oriented edge by four consecutive i.i.d. labels `x 0, x 1, x 2, x 3`; the two
endpoints apply the same local rule to the overlapping triples `(x0,x1,x2)` and `(x1,x2,x3)`.
-/
def pEvent (alg : ClassicalAlgorithm) : Set (Samples 4) :=
  {x | alg.f (x 0, x 1, x 2) = alg.f (x 1, x 2, x 3)}

/-- The monochromatic-edge probability of a one-round algorithm on the directed cycle. -/
noncomputable def p (alg : ClassicalAlgorithm) : ENNReal :=
  (volume : Measure (Samples 4)) (pEvent alg)

lemma measurable_fstTriple :
    Measurable (fun x : Samples 4 => (x 0, x 1, x 2) : Samples 4 → Rand × Rand × Rand) := by
  simpa using
    (measurable_pi_apply 0).prodMk ((measurable_pi_apply 1).prodMk (measurable_pi_apply 2))

lemma measurable_sndTriple :
    Measurable (fun x : Samples 4 => (x 1, x 2, x 3) : Samples 4 → Rand × Rand × Rand) := by
  simpa using
    (measurable_pi_apply 1).prodMk ((measurable_pi_apply 2).prodMk (measurable_pi_apply 3))

lemma measurable_nodeColor₀ (alg : ClassicalAlgorithm) :
    Measurable fun x : Samples 4 => alg.f (x 0, x 1, x 2) := by
  simpa [Function.comp_def] using alg.measurable_f.comp measurable_fstTriple

lemma measurable_nodeColor₁ (alg : ClassicalAlgorithm) :
    Measurable fun x : Samples 4 => alg.f (x 1, x 2, x 3) := by
  simpa [Function.comp_def] using alg.measurable_f.comp measurable_sndTriple

lemma measurableSet_pEvent (alg : ClassicalAlgorithm) : MeasurableSet (pEvent alg) := by
  classical
  refine measurableSet_eq_fun (measurable_nodeColor₀ alg) (measurable_nodeColor₁ alg)

end ClassicalAlgorithm

/-!
## The finite digraph model for the lower bound

The lower bound reduces to a purely finite problem on a digraph `G_n`:
- vertices are injective triples `(a,b,c)` of symbols in `{0,…,n-1}`,
- edges are injective quadruples `(a,b,c,d)` encoding `(a,b,c) → (b,c,d)`,
- a `LowerBound.Coloring n` is a `Bool`-coloring of vertices,
- `LowerBound.monoFraction f` is the fraction of monochromatic edges.
-/

end Distributed2Coloring
