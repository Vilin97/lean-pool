/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.KroneckerNaturality
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.InducedOnRPCohomology
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.MonodromyCharacter

/-!
# Constructing the degree-one projective cohomology class

Uses the mod-two Kronecker equivalence to turn a linear functional on
`H₁(RPⁿ; F₂)` into a class of `H¹(RPⁿ; F₂)` and proves naturality under
descended odd sphere maps. The structure `MonodromyFunctional n` isolates the
homology functional and its invariance property. The canonical instance used by
the final proof is constructed later in `RPnMonodromyFunctional`.
-/

@[expose] public section
open CategoryTheory AlgebraicTopology

noncomputable section

namespace SphereOddDegree

/-- The cohomology class `α ∈ H¹(RPⁿ; F₂)` produced from a `ZMod 2`-valued
functional `g` on `H₁(RPⁿ; F₂)` via the surjectivity of the Kronecker classifier
(`kroneckerMap_surjective`). It is a genuine element of `rpCohomology n 1`. -/
noncomputable def rpAlphaOfFunctional (n : ℕ)
    (g : homologyZMod2 (TopCat.of (RP n)) 1 →ₗ[ZMod 2] ZMod 2) :
    rpCohomology n 1 :=
  Classical.choose (kroneckerMap_surjective (TopCat.of (RP n)) 1 g)

/-- Defining property: the Kronecker functional of `rpAlphaOfFunctional n g` is
exactly `g`. -/
theorem rpAlphaOfFunctional_spec (n : ℕ)
    (g : homologyZMod2 (TopCat.of (RP n)) 1 →ₗ[ZMod 2] ZMod 2) :
    (kroneckerMap (TopCat.of (RP n)) 1).hom (rpAlphaOfFunctional n g) = g :=
  Classical.choose_spec (kroneckerMap_surjective (TopCat.of (RP n)) 1 g)

/-- **Conditional naturality.** If a functional `g : H₁(RPⁿ; F₂) → F₂` is
invariant under the homology pushforward of a descended odd map
`fbar = inducedOnRP f hf` (i.e. `g ∘ fbar_* = g`), then the pullback of the
descended odd map fixes the corresponding cohomology class:
`fbar^*(rpAlphaOfFunctional n g) = rpAlphaOfFunctional n g`.

The proof uses the universal coefficient theorem over `F₂` in full: naturality
(`kroneckerMap_naturality_apply`) transports the invariance of `g` to an equality
of Kronecker functionals, and injectivity (`kroneckerMap_injective`) lifts it back
to an equality of cohomology classes. -/
theorem inducedOnRPPullback_rpAlphaOfFunctional (n : ℕ)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (g : homologyZMod2 (TopCat.of (RP n)) 1 →ₗ[ZMod 2] ZMod 2)
    (hg : g.comp (homologyPushZMod2 (TopCat.ofHom (inducedOnRP f hf)) 1).hom = g) :
    (inducedOnRPPullback f hf 1).hom (rpAlphaOfFunctional n g)
      = rpAlphaOfFunctional n g := by
  apply kroneckerMap_injective (TopCat.of (RP n)) 1
  have key := kroneckerMap_naturality_apply (TopCat.ofHom (inducedOnRP f hf)) 1
    (rpAlphaOfFunctional n g)
  rw [rpAlphaOfFunctional_spec, hg] at key
  rw [rpAlphaOfFunctional_spec]
  exact key

/-- A mod-two functional on `H₁(RPⁿ; F₂)` together with invariance under the
homology pushforward of every descended odd map. This is the interface used to
construct the degree-one class; `RPnMonodromyFunctional` supplies the canonical
instance. -/
structure MonodromyFunctional (n : ℕ) where
  /-- The `ZMod 2`-valued functional on `H₁(RPⁿ; F₂)`. -/
  g : homologyZMod2 (TopCat.of (RP n)) 1 →ₗ[ZMod 2] ZMod 2
  /-- Invariance under the homology pushforward of every descended odd map. -/
  invariant : ∀ (f : C(Sphere n, Sphere n)) (hf : IsOddMap f),
    g.comp (homologyPushZMod2 (TopCat.ofHom (inducedOnRP f hf)) 1).hom = g

/-- **The canonical degree-one class** `α ∈ H¹(RPⁿ; F₂)` associated to the
canonical double cover, built from the monodromy functional `m`. It is a genuine
element of `rpCohomology n 1`. -/
noncomputable def rpAlpha (n : ℕ) (m : MonodromyFunctional n) : rpCohomology n 1 :=
  rpAlphaOfFunctional n m.g

/-- `rpAlpha n m` is the class produced by the universal coefficient surjection
from the monodromy functional `m.g`. -/
theorem rpAlpha_def (n : ℕ) (m : MonodromyFunctional n) :
    rpAlpha n m = rpAlphaOfFunctional n m.g := rfl

/-- The defining property of `rpAlpha`: its Kronecker functional is the monodromy
functional `m.g`. -/
theorem rpAlpha_kroneckerMap (n : ℕ) (m : MonodromyFunctional n) :
    (kroneckerMap (TopCat.of (RP n)) 1).hom (rpAlpha n m) = m.g :=
  rpAlphaOfFunctional_spec n m.g

/-- **Descended odd maps preserve `rpAlpha`** — unconditionally (given the
monodromy functional `m`). For every odd self-map `f` of `Sⁿ` with descent
`fbar = inducedOnRP f hf`,

```text
(inducedOnRPPullback f hf 1) (rpAlpha n m) = rpAlpha n m,
```

i.e. `fbar^*(α) = α`. This is exactly the action hypothesis the final-assembly
theorems take as input; here it is proved. -/
theorem inducedOnRPPullback_rpAlpha (n : ℕ) (m : MonodromyFunctional n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    (inducedOnRPPullback f hf 1).hom (rpAlpha n m) = rpAlpha n m :=
  inducedOnRPPullback_rpAlphaOfFunctional n f hf m.g (m.invariant f hf)

end SphereOddDegree
