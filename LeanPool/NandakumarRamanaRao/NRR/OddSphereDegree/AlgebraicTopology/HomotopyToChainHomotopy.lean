/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Chain-homotopy implies equality on singular homology

Specializes Mathlib's `Homotopy.homologyMap_eq` to the integral singular chain and homology
functors. The theorem consumes an explicit chain homotopy; the prism-operator modules construct
that chain homotopy from a topological homotopy.
-/

open CategoryTheory AlgebraicTopology

namespace SphereOddDegree

/-- The integral singular chain complex functor `TopCat ⥤ ChainComplex (ModuleCat ℤ) ℕ`,
i.e. `singularChainComplexFunctor` specialised to coefficients `ℤ`. -/
noncomputable abbrev singularChainℤ :
    TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)

/-- The `n`-th integral singular homology functor `TopCat ⥤ ModuleCat ℤ`,
i.e. `singularHomologyFunctor` specialised to coefficients `ℤ`. -/
noncomputable abbrev singularHomologyℤ (n : ℕ) :
    TopCat.{0} ⥤ ModuleCat.{0} ℤ :=
  (singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)

/-- **Reduction lemma via the prism operator.**

If the singular chain maps induced by two continuous maps `f, g : X ⟶ Y` are
chain-homotopic, then the induced maps on the `n`-th integral singular homology
are equal.

The chain homotopy `H` is a *hypothesis*: this is the reusable step that turns the
required prism operator (`ContinuousMap.Homotopy → Homotopy (chain maps)`)
into homotopy invariance of singular homology, via `Homotopy.homologyMap_eq`. It
is therefore not a homotopy-invariance theorem on its own. -/
theorem singularHomologyMap_eq_of_singularChainHomotopy
    {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : Homotopy (singularChainℤ.map f) (singularChainℤ.map g)) (n : ℕ) :
    (singularHomologyℤ n).map f = (singularHomologyℤ n).map g := by
  dsimp [singularHomologyℤ, singularHomologyFunctor, HomologicalComplex.homologyFunctor]
  exact H.homologyMap_eq n

end SphereOddDegree
