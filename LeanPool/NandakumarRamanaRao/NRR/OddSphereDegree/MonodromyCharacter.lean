/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.MonodromyNontrivial

/-!
# The abelianized monodromy classifying character of the double cover

This file constructs the abelianized monodromy character associated with the canonical degree-one class

```text
α ∈ H¹(RPⁿ; F₂).
```

The conceptual classifier chain is

```text
monodromy of Sⁿ → RPⁿ
 → character π₁(RPⁿ, x) →* ZMod 2 (classifyingHom, DoubleCoverClass.lean)
 → character H₁(RPⁿ; ℤ) →* ZMod 2 (this file, via abelianization)
 → class α ∈ H¹(RPⁿ; F₂) (degree-one cohomological classifier)
```

Since the target `Multiplicative (ZMod 2)` is abelian, the classifying
homomorphism `classifyingHom n x` factors **uniquely** through the abelianization
`Abelianization (FundamentalGroup (RP n) x)`. By the (degree-one) Hurewicz
theorem the abelianization of the fundamental group is the first integral
homology group `H₁(RP n; ℤ)`; the abelianized character is therefore exactly the
group-theoretic shadow of the `Hom(H₁, F₂)` side of the universal coefficient
theorem `H¹(X; F₂) ≅ Hom(H₁(X; ℤ), F₂)`. The character supplies the group-theoretic input to a degree-one cohomological classifier.

## Main declarations

* `classifyingHomAb n x` — the **abelianized monodromy classifying character**
 `Abelianization (FundamentalGroup (RP n) x) →* Multiplicative (ZMod 2)`.
* `classifyingHomAb_of` / `classifyingHomAb_comp_of` — it restricts to
 `classifyingHom` along `Abelianization.of` (factorisation).
* `classifyingHomAb_surjective` — for `n ≥ 1` it is surjective (nontriviality on
 the `H₁` side).
* `classifyingHomAb_inducedOnRP_naturality` — the descended odd map `fbar` acts
 trivially on the abelianized character, the `H₁`-level form of `fbar^*(α) = α`.
-/

noncomputable section

namespace SphereOddDegree

open CategoryTheory

/-- The **abelianized monodromy classifying character** of the double cover
`proj n : S^n → RP n`. Because the target `Multiplicative (ZMod 2)` is abelian,
the classifying homomorphism `classifyingHom n x` factors uniquely through the
abelianization of `π₁(RP n, x)`. By the degree-one Hurewicz theorem the
abelianization of the fundamental group is the first integral homology
`H₁(RP n; ℤ)`, so this is the group-theoretic shadow of the `Hom(H₁, F₂)` side of
the universal coefficient theorem — the last honest object before `α`. -/
noncomputable def classifyingHomAb (n : ℕ) (x : RP n) :
    Abelianization (FundamentalGroup (RP n) x) →* Multiplicative (ZMod 2) :=
  Abelianization.lift (classifyingHom n x)

/-- The abelianized character restricts to `classifyingHom` on the image of a
fundamental-group class under `Abelianization.of`. -/
@[simp] theorem classifyingHomAb_of (n : ℕ) (x : RP n) (a : FundamentalGroup (RP n) x) :
    classifyingHomAb n x (Abelianization.of a) = classifyingHom n x a :=
  Abelianization.lift_apply_of _ _

/-- The factorisation of `classifyingHom` through the abelianization:
`classifyingHomAb n x ∘ Abelianization.of = classifyingHom n x`. -/
theorem classifyingHomAb_comp_of (n : ℕ) (x : RP n) :
    (classifyingHomAb n x).comp Abelianization.of = classifyingHom n x :=
  MonoidHom.ext (classifyingHomAb_of n x)

/-- **Surjectivity / nontriviality of the abelianized character.** For `n ≥ 1`,
the abelianized monodromy classifying character is surjective onto
`Multiplicative (ZMod 2)`. Equivalently, the abelianization of `π₁(RP n, x)`
(i.e. `H₁(RP n; ℤ)` by Hurewicz) has a nontrivial `ZMod 2`-valued character — the
honest nontriviality statement on the `H₁` side of Route A. -/
theorem classifyingHomAb_surjective (n : ℕ) (hn : 1 ≤ n) (x : RP n) :
    Function.Surjective (classifyingHomAb n x) := by
  intro g
  obtain ⟨a, ha⟩ := classifyingHom_surjective n hn x g
  exact ⟨Abelianization.of a, by rw [classifyingHomAb_of]; exact ha⟩

/-- **Naturality of the abelianized character under a descended odd map.** The
descended odd map `fbar = inducedOnRP f hf` acts trivially on the abelianized
monodromy classifying character:
```text
classifyingHomAb n (fbar x) ∘ Abelianization.map (π₁ map fbar) = classifyingHomAb n x.
```
This is the `H₁`-level form of the eventual cohomological identity `fbar^*(α) = α`;
it descends `classifyingHom_inducedOnRP_naturality` along `Abelianization.of`
using the uniqueness of the abelianized lift. -/
theorem classifyingHomAb_inducedOnRP_naturality (n : ℕ) (f : C(Sphere n, Sphere n))
    (hf : IsOddMap f) (x : RP n) :
    (classifyingHomAb n (inducedOnRP f hf x)).comp
        (Abelianization.map
          (FundamentalGroup.map ⟨inducedOnRP f hf, (inducedOnRP f hf).continuous⟩ x))
      = classifyingHomAb n x := by
  refine Abelianization.hom_ext _ _ (MonoidHom.ext fun a => ?_)
  change classifyingHomAb n (inducedOnRP f hf x)
      (Abelianization.map
        (FundamentalGroup.map ⟨inducedOnRP f hf, (inducedOnRP f hf).continuous⟩ x)
        (Abelianization.of a))
    = classifyingHomAb n x (Abelianization.of a)
  simp only [Abelianization.map_of, classifyingHomAb_of]
  exact DFunLike.congr_fun (classifyingHom_inducedOnRP_naturality n f hf x) a

end SphereOddDegree
