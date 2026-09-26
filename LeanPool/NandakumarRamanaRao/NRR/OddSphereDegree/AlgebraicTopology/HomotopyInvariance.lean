/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.HomotopyInvarianceWrappers
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.PrismOperator

/-!
# Singular-homology homotopy invariance from a prism operator

Defines the abstract proposition `SingularPrismOperator` and derives the standard homotopy
invariance statements for integral singular homology from it. A concrete proof is exported as
`singularPrismOperator` by `SingularHomologyHomotopyInvariance.lean`; this module remains the
reusable conditional API.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology

namespace SphereOddDegree

/-- **The prism-operator hypothesis** (the required keystone).

A `SingularPrismOperator` is the assertion that every topological homotopy
between two `TopCat` maps gives rise to a chain homotopy of the induced integral
singular chain maps. This is precisely the classical prism operator
`P_n : C_n(X) → C_{n+1}(Y)` with `∂P + P∂ = g_# − f_#`, the one ingredient of
homotopy invariance of singular homology not provided by the pinned Mathlib version (the
topological half is built in `PrismOperator.lean` as `cylinder`).

It is phrased as a `Prop` (using `Nonempty` of the chain-homotopy data) so it can
be assumed cleanly as a hypothesis; this suffices for every homology-level
*equality* below, which are propositions. -/
def SingularPrismOperator : Prop :=
  ∀ {X Y : TopCat.{0}} {f g : X ⟶ Y},
    ContinuousMap.Homotopy f.hom g.hom →
      Nonempty (Homotopy (singularChainℤ.map f) (singularChainℤ.map g))

/-- **Conditional homotopy invariance (topological homotopy form).**

Assuming the prism operator, a topological homotopy between two `TopCat` maps
`f, g : X ⟶ Y` induces equal maps on the `n`-th integral singular homology. -/
theorem singularHomologyMap_eq_of_homotopy
    (prism : SingularPrismOperator)
    {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) (n : ℕ) :
    (singularHomologyℤ n).map f = (singularHomologyℤ n).map g := by
  obtain ⟨ch⟩ := prism H
  exact singularHomologyMap_eq_of_singularChainHomotopy ch n

/-- **Conditional homotopy invariance (`Homotopic` form).**

Assuming the prism operator, homotopic `TopCat` maps `f, g : X ⟶ Y` (i.e.
`ContinuousMap.Homotopic f.hom g.hom`) induce equal maps on the `n`-th integral
singular homology. -/
theorem singularHomologyMap_eq_of_homotopic
    (prism : SingularPrismOperator)
    {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (h : ContinuousMap.Homotopic f.hom g.hom) (n : ℕ) :
    (singularHomologyℤ n).map f = (singularHomologyℤ n).map g := by
  obtain ⟨H⟩ := h
  exact singularHomologyMap_eq_of_homotopy prism H n

/-- **Conditional homotopy invariance (`C(X, Y)` interface).**

Assuming the prism operator, two homotopic continuous maps `f, g : C(X, Y)`
between topological spaces underlying `TopCat` objects induce equal maps on the
`n`-th integral singular homology (after the canonical `TopCat.ofHom`). -/
theorem singularHomologyMap_eq_of_homotopic_continuousMap
    (prism : SingularPrismOperator)
    {X Y : TopCat.{0}} {f g : C(X, Y)}
    (h : ContinuousMap.Homotopic f g) (n : ℕ) :
    (singularHomologyℤ n).map (TopCat.ofHom f)
      = (singularHomologyℤ n).map (TopCat.ofHom g) :=
  singularHomologyMap_eq_of_homotopic prism h n

/-- **Conditional homotopy invariance (raw functor form).**

The same statement as `singularHomologyMap_eq_of_homotopic`, written directly in
terms of `AlgebraicTopology.singularHomologyFunctor`, for callers that prefer the
unfolded functor. -/
theorem singularHomologyFunctor_map_eq_of_homotopic
    (prism : SingularPrismOperator)
    {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (h : ContinuousMap.Homotopic f.hom g.hom) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).map f
      = ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).map g :=
  singularHomologyMap_eq_of_homotopic prism h n

end SphereOddDegree
