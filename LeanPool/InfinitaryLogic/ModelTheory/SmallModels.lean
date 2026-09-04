/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.UniformCollapse
/-!
# Small models: public facade

The stable entry point for the small-model theorem (Marker, *Lectures on Infinitary Model
Theory*, Theorem 11.2). Importing this file (or the default `import InfinitaryLogic`) exposes:

* `infinitaryType` / `RealizedInfinitaryTypes` / `Lomega1omegaSmall` — the complete-type API
  (`ModelTheory/InfinitaryTypes.lean`);
* `exists_small_model_of_hasArbLargeModels` — **a sentence with arbitrarily large models has,
  at every infinite `κ`, a model of size exactly `κ` realizing only countably many complete
  `L_{ω₁ω}`-types** — over an arbitrary language;
* `exists_small_model_of_hasArbLargeModels_countable_symbols` — the transparent
  countable-symbol core.

The proof route (issue #11): the schema term source of the Morley seed (the `morley_hanf`
machinery) over a highly order-transitive skeleton of size `κ` (every linear ordered field is
highly order-transitive; Hahn-series subfields realize every infinite cardinality); the local
EM quotient is equivariant under order automorphisms of the skeleton, so tuples are classified
up to automorphism by countably many compressed term codes; located term codes give the exact
carrier cardinality; and the arbitrary-language wrapper is a reduct along the uniform
collapsing hom, so smallness descends generically.
-/
