/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.HomotopyInvariance
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.Backports.PrismSimplicialHomotopy

/-!
# Homotopy invariance of singular homology — unconditional

Combining the backported algebraic prism
(`CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy`, in
`Backports/SimplicialObjectChainHomotopy.lean`) with the library's singular
cylinder (`PrismOperator.cylinder`) assembled into a combinatorial simplicial
homotopy (`Backports/PrismSimplicialHomotopy.lean`,
`prismHomotopy`/`singularChainHomotopyOfHomotopy`), the prism-operator hypothesis
`SingularPrismOperator` isolated in `HomotopyInvariance.lean` is a **theorem**.

Consequently every theorem there that was *conditional* on
`SingularPrismOperator` is dischargeable, and the singular-homology
homotopy-invariance results below are **unconditional**.

Integer coefficients (`ModuleCat.{0} ℤ`), the case relevant to the topological
degree of sphere maps.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology

namespace SphereOddDegree

/-- **The singular prism operator, discharged.** The hypothesis
`SingularPrismOperator` (isolated in `HomotopyInvariance.lean`) holds: it is
witnessed by `singularChainHomotopyOfHomotopy`. -/
theorem singularPrismOperator : SingularPrismOperator :=
  fun H => ⟨singularChainHomotopyOfHomotopy H⟩

/-- **Homotopy invariance of singular homology (unconditional, `TopCat` form).**
A topological homotopy between `f, g : X ⟶ Y` induces equal maps on the `n`-th
integral singular homology. -/
theorem map_singularHomologyℤ_eq_of_homotopy
    {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : ContinuousMap.Homotopy f.hom g.hom) (n : ℕ) :
    (singularHomologyℤ n).map f = (singularHomologyℤ n).map g :=
  singularHomologyMap_eq_of_homotopy singularPrismOperator H n

/-- **Homotopy invariance of singular homology (unconditional, `Homotopic` form).**
Homotopic `TopCat` maps induce equal maps on integral singular homology. -/
theorem map_singularHomologyℤ_eq_of_homotopic
    {X Y : TopCat.{0}} {f g : X ⟶ Y} (h : ContinuousMap.Homotopic f.hom g.hom) (n : ℕ) :
    (singularHomologyℤ n).map f = (singularHomologyℤ n).map g :=
  singularHomologyMap_eq_of_homotopic singularPrismOperator h n

/-- **Homotopy invariance of singular homology (unconditional, `C(X, Y)` form).**
Homotopic continuous maps induce equal maps on integral singular homology. -/
theorem map_singularHomologyℤ_eq_of_homotopic_continuousMap
    {X Y : TopCat.{0}} {f g : C(X, Y)} (h : ContinuousMap.Homotopic f g) (n : ℕ) :
    (singularHomologyℤ n).map (TopCat.ofHom f)
      = (singularHomologyℤ n).map (TopCat.ofHom g) :=
  singularHomologyMap_eq_of_homotopic_continuousMap singularPrismOperator h n

end SphereOddDegree
