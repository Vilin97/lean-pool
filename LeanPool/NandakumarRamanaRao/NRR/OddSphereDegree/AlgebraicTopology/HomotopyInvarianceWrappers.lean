/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SingularHomologyFunctorAPI

/-!
# Chain-homotopy wrappers for singular homology

Composition, symmetry, and homotopy-equivalence wrappers around
`singularHomologyMap_eq_of_singularChainHomotopy`. These lemmas are independent of the
particular construction of the singular prism operator.
-/

open CategoryTheory AlgebraicTopology

namespace SphereOddDegree

variable {X Y Z : TopCat.{0}}

/-- **Chain-homotopy wrapper (precomposition).** Transport a chain homotopy
between the singular chain maps of `f, g : Y ⟶ Z` along precomposition with a
continuous map `h : X ⟶ Y`, yielding a chain homotopy between the singular chain
maps of `h ≫ f` and `h ≫ g`.

This is `Homotopy.compLeft` repackaged through the functoriality
`singularChainℤ.map_comp`. -/
noncomputable def singularChainHomotopyPrecomp (h : X ⟶ Y) {f g : Y ⟶ Z}
    (H : Homotopy (singularChainℤ.map f) (singularChainℤ.map g)) :
    Homotopy (singularChainℤ.map (h ≫ f)) (singularChainℤ.map (h ≫ g)) := by
  rw [singularChainℤ.map_comp, singularChainℤ.map_comp]
  exact H.compLeft _

/-- **Chain-homotopy wrapper (postcomposition).** Transport a chain homotopy
between the singular chain maps of `f, g : X ⟶ Y` along postcomposition with a
continuous map `h : Y ⟶ Z`, yielding a chain homotopy between the singular chain
maps of `f ≫ h` and `g ≫ h`.

This is `Homotopy.compRight` repackaged through `singularChainℤ.map_comp`. -/
noncomputable def singularChainHomotopyPostcomp (h : Y ⟶ Z) {f g : X ⟶ Y}
    (H : Homotopy (singularChainℤ.map f) (singularChainℤ.map g)) :
    Homotopy (singularChainℤ.map (f ≫ h)) (singularChainℤ.map (g ≫ h)) := by
  rw [singularChainℤ.map_comp, singularChainℤ.map_comp]
  exact H.compRight _

/-- **Homology naturality (precomposition).** If the singular chain maps of
`f, g : Y ⟶ Z` are chain-homotopic, then for any `h : X ⟶ Y` the induced maps of
`h ≫ f` and `h ≫ g` on the `n`-th integral singular homology are equal. -/
theorem singularHomologyℤ_map_eq_precomp (h : X ⟶ Y) {f g : Y ⟶ Z}
    (H : Homotopy (singularChainℤ.map f) (singularChainℤ.map g)) (n : ℕ) :
    (singularHomologyℤ n).map (h ≫ f) = (singularHomologyℤ n).map (h ≫ g) :=
  singularHomologyMap_eq_of_singularChainHomotopy (singularChainHomotopyPrecomp h H) n

/-- **Homology naturality (postcomposition).** If the singular chain maps of
`f, g : X ⟶ Y` are chain-homotopic, then for any `h : Y ⟶ Z` the induced maps of
`f ≫ h` and `g ≫ h` on the `n`-th integral singular homology are equal. -/
theorem singularHomologyℤ_map_eq_postcomp (h : Y ⟶ Z) {f g : X ⟶ Y}
    (H : Homotopy (singularChainℤ.map f) (singularChainℤ.map g)) (n : ℕ) :
    (singularHomologyℤ n).map (f ≫ h) = (singularHomologyℤ n).map (g ≫ h) :=
  singularHomologyMap_eq_of_singularChainHomotopy (singularChainHomotopyPostcomp h H) n

/-- **Symmetry of the consumer.** The equality on singular homology produced by a
chain homotopy is symmetric: a chain homotopy between the singular chain maps of
`f` and `g` gives the same homology equality read in either direction (via
`Homotopy.symm`). -/
theorem singularHomologyℤ_map_eq_symm {f g : X ⟶ Y}
    (H : Homotopy (singularChainℤ.map f) (singularChainℤ.map g)) (n : ℕ) :
    (singularHomologyℤ n).map g = (singularHomologyℤ n).map f :=
  singularHomologyMap_eq_of_singularChainHomotopy H.symm n

/-- **Homotopy-equivalence wrapper.** A chain homotopy equivalence between the
integral singular chain complexes of `X` and `Y` induces an isomorphism on the
`n`-th integral singular homology.

This is `HomotopyEquiv.toHomologyIso` repackaged for the singular homology
functor (the functor's object value is definitionally the homology of the chain
complex). Like the rest of this file it takes the chain-level equivalence as a
hypothesis: it is the homology-isomorphism consumer that homotopy invariance will
feed once the prism operator upgrades a topological homotopy equivalence to a
chain homotopy equivalence. -/
noncomputable def singularHomologyℤIsoOfHomotopyEquiv
    (e : HomotopyEquiv ((singularChainℤ).obj X) ((singularChainℤ).obj Y)) (n : ℕ) :
    (singularHomologyℤ n).obj X ≅ (singularHomologyℤ n).obj Y :=
  e.toHomologyIso n

end SphereOddDegree
