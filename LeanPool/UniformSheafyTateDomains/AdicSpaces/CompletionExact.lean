/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.AdicCompletion.Exactness
import LeanPool.UniformSheafyTateDomains.AdicSpaces.NoetherianTateModules

/-!
# Completion Preserves Strict Exact Sequences

For finitely generated modules over a noetherian ring with I-adic topology, the I-adic
completion functor preserves exact sequences. This is the key infrastructure for the
non-discrete case of Tate acyclicity.

## Main results

* `AdicCompletion.map_exact` : I-adic completion preserves exactness (from mathlib).
* `AdicCompletion.map_surjective` : Completion preserves surjectivity (from mathlib).
* `AdicCompletion.map_injective` : Completion preserves injectivity (from mathlib).
* `adicCompletion_shortExact` : Completion preserves short exact sequences.

## Context

Wedhorn Theorem 8.28(b) requires that completing a strict short exact sequence
`0 → K → M → N → 0` of f.g. modules over a noetherian I-adic ring gives an
exact sequence `0 → K̂ → M̂ → N̂ → 0`.

Mathlib's `AdicCompletion` provides this directly via `map_exact`, `map_surjective`,
and `map_injective`. These work for `AdicCompletion I M` (the projective limit
`lim M/I^n M`), which is the appropriate completion for the adic space theory.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §6.18, §8.28
* Stacks Project, Tag 00MA (completion of Noetherian modules)
-/

/-! ### Short exact sequences under completion -/

-- Bumped from default 200000 to 400000: completion-preservation proof
-- exercises Lean's typeclass synthesis heavily through nested completions
-- + module instances.
universe u in
/-- **Completion preserves short exact sequences** of finitely generated modules
over a noetherian ring.

Given `0 → K →f M →g N → 0` exact with `f` injective, `g` surjective,
and `range f = ker g`, the completed sequence
`0 → K̂ →f̂ M̂ →ĝ N̂ → 0` is also exact.

This combines three mathlib results:
- `AdicCompletion.map_injective` (injectivity)
- `AdicCompletion.map_exact` (exactness at middle)
- `AdicCompletion.map_surjective` (surjectivity) -/
theorem adicCompletion_shortExact
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {I : Ideal R}
    {K M N : Type u}
    [AddCommGroup K] [Module R K] [Module.Finite R K]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (f : K →ₗ[R] M) (g : M →ₗ[R] N)
    (hf : Function.Injective f)
    (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    Function.Injective (AdicCompletion.map I f) ∧
    Function.Surjective (AdicCompletion.map I g) ∧
    Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) :=
  ⟨AdicCompletion.map_injective I hf,
   AdicCompletion.map_surjective I hg,
   AdicCompletion.map_exact hf hfg hg⟩
