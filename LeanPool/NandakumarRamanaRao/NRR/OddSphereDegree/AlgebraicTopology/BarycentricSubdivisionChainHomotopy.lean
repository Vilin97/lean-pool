/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricSubdivisionChainMap
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricSubdivisionHomotopyFormula
import Mathlib.Tactic

/-! # Barycentric Subdivision Chain Homotopy -/

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits

namespace SphereOddDegree
namespace AffineBarycentricSubdivision
/-- The components of the chain homotopy between barycentric subdivision and the
identity: in the slot `(p, q)` it is `-H_p` when `q = p + 1` and `0` otherwise. -/
noncomputable def barycentricSubdivisionChainHomotopyHom
    (R : Type) [CommRing R] (X : TopCat.{0}) (p q : ℕ) :
    (singularChainComplex R X).X p ⟶ (singularChainComplex R X).X q :=
  if h : p + 1 = q then
    -((barycentricSubdivisionHomotopyLinearMap R X p) ≫ eqToHom (by rw [h]))
  else 0

/-- In the relevant slot, the homotopy component is `-H_p`. -/
theorem barycentricSubdivisionChainHomotopyHom_succ
    (R : Type) [CommRing R] (X : TopCat.{0}) (p : ℕ) :
    barycentricSubdivisionChainHomotopyHom R X p (p + 1)
      = -(barycentricSubdivisionHomotopyLinearMap R X p) := by
  rw [barycentricSubdivisionChainHomotopyHom, dite_eq_left rfl, eqToHom_refl, Category.comp_id]

/-- Outside the relevant slot, the homotopy component vanishes. -/
theorem barycentricSubdivisionChainHomotopyHom_zero
    (R : Type) [CommRing R] (X : TopCat.{0}) (p q : ℕ) (h : p + 1 ≠ q) :
    barycentricSubdivisionChainHomotopyHom R X p q = 0 := by
  rw [barycentricSubdivisionChainHomotopyHom, dite_eq_right h]

/--
**The chain-homotopy identity in Mathlib's sign convention.** For every degree
`n`, the degree-`n` component of the subdivision chain map equals
`dNext + prevD` of the homotopy operator plus the identity component. This is the
`comm` field of the `Homotopy` structure, isolated as a theorem.
-/
theorem barycentricSubdivisionChainHomotopy_comm
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    (barycentricSubdivisionChainMap R X).f n
      = dNext n (barycentricSubdivisionChainHomotopyHom R X)
        + prevD n (barycentricSubdivisionChainHomotopyHom R X)
        + HomologicalComplex.Hom.f (𝟙 (singularChainComplex R X)) n := by
  have hd_0 : (singularChainComplex R X).d 1 0 = singularBoundary R X 0 := rfl
  have hd_succ : ∀ m : ℕ, (singularChainComplex R X).d (m + 1) m = singularBoundary R X m := fun _ => rfl
  cases n with
  | zero =>
    have h_dNext : dNext 0 (barycentricSubdivisionChainHomotopyHom R X) = 0 := by
      apply dNext_eq_zero
      rw [ComplexShape.down_Rel]; intro h; omega
    have h_prevD : prevD 0 (barycentricSubdivisionChainHomotopyHom R X)
        = (barycentricSubdivisionChainHomotopyHom R X 0 1) ≫ (singularChainComplex R X).d 1 0 := by
      apply prevD_eq (w := (show (ComplexShape.down ℕ).Rel 1 0 from rfl))
    rw [h_dNext, h_prevD, barycentricSubdivisionChainHomotopyHom_succ, hd_0]
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro c
    have hform := barycentricSubdivisionHomotopy_boundary_formula R X 0 c
    rw [homotopyBoundaryTerm_zero] at hform
    change (barycentricSubdivisionLinearMap R X 0).hom c =
      0 + (singularBoundary R X 0).hom ((-barycentricSubdivisionHomotopyLinearMap R X 0).hom c) + c
    rw [zero_add, show (-barycentricSubdivisionHomotopyLinearMap R X 0).hom c
        = - (barycentricSubdivisionHomotopyLinearMap R X 0).hom c from rfl, map_neg]
    apply eq_of_sub_eq_zero
    calc
      (barycentricSubdivisionLinearMap R X 0).hom c - (-(singularBoundary R X 0).hom ((barycentricSubdivisionHomotopyLinearMap R X 0).hom c) + c)
        = (singularBoundary R X 0).hom ((barycentricSubdivisionHomotopyLinearMap R X 0).hom c) + 0 - (c - (barycentricSubdivisionLinearMap R X 0).hom c) := by abel
      _ = 0 := by rw [hform, sub_self]
  | succ m =>
    have h_dNext : dNext (m + 1) (barycentricSubdivisionChainHomotopyHom R X)
        = (singularChainComplex R X).d (m + 1) m ≫ (barycentricSubdivisionChainHomotopyHom R X m (m + 1)) := by
      apply dNext_eq (w := (show (ComplexShape.down ℕ).Rel (m + 1) m from rfl))
    have h_prevD : prevD (m + 1) (barycentricSubdivisionChainHomotopyHom R X)
        = (barycentricSubdivisionChainHomotopyHom R X (m + 1) (m + 2)) ≫ (singularChainComplex R X).d (m + 2) (m + 1) := by
      apply prevD_eq (w := (show (ComplexShape.down ℕ).Rel (m + 2) (m + 1) from rfl))
    rw [h_dNext, h_prevD, barycentricSubdivisionChainHomotopyHom_succ, barycentricSubdivisionChainHomotopyHom_succ,
        hd_succ m, hd_succ (m + 1)]
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro c
    have hform := barycentricSubdivisionHomotopy_boundary_formula R X (m + 1) c
    rw [homotopyBoundaryTerm_succ] at hform
    change (barycentricSubdivisionLinearMap R X (m + 1)).hom c =
      (-barycentricSubdivisionHomotopyLinearMap R X m).hom ((singularBoundary R X m).hom c)
      + (singularBoundary R X (m + 1)).hom ((-barycentricSubdivisionHomotopyLinearMap R X (m + 1)).hom c) + c
    rw [show (-barycentricSubdivisionHomotopyLinearMap R X m).hom ((singularBoundary R X m).hom c)
        = - (barycentricSubdivisionHomotopyLinearMap R X m).hom ((singularBoundary R X m).hom c) from rfl,
        show (-barycentricSubdivisionHomotopyLinearMap R X (m + 1)).hom c
        = - (barycentricSubdivisionHomotopyLinearMap R X (m + 1)).hom c from rfl,
        map_neg]
    apply eq_of_sub_eq_zero
    calc
      (barycentricSubdivisionLinearMap R X (m + 1)).hom c
          - (-(barycentricSubdivisionHomotopyLinearMap R X m).hom ((singularBoundary R X m).hom c)
             + -(singularBoundary R X (m + 1)).hom ((barycentricSubdivisionHomotopyLinearMap R X (m + 1)).hom c) + c)
        = ((singularBoundary R X (m + 1)).hom ((barycentricSubdivisionHomotopyLinearMap R X (m + 1)).hom c)
           + (barycentricSubdivisionHomotopyLinearMap R X m).hom ((singularBoundary R X m).hom c))
          - (c - (barycentricSubdivisionLinearMap R X (m + 1)).hom c) := by abel
      _ = 0 := by rw [hform, sub_self]

/-- **Barycentric subdivision is chain-homotopic to the identity.**

A `Homotopy` between the barycentric subdivision chain map and the identity chain
map of the singular chain complex, built from the homotopy operator `-H`. -/
noncomputable def barycentricSubdivisionChainHomotopicId
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    Homotopy (barycentricSubdivisionChainMap R X) (𝟙 (singularChainComplex R X)) where
  hom := barycentricSubdivisionChainHomotopyHom R X
  zero i j hij := by
    apply barycentricSubdivisionChainHomotopyHom_zero
    rw [ComplexShape.down_Rel] at hij; omega
  comm := barycentricSubdivisionChainHomotopy_comm R X

/-- **Induced map on homology is the identity (named form).**

Since barycentric subdivision is chain-homotopic to the identity, it induces the
identity on every singular homology group. -/
theorem barycentricSubdivision_induces_identity_on_homology
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap (barycentricSubdivisionChainMap R X) n
      = 𝟙 ((singularChainComplex R X).homology n) := by
  rw [(barycentricSubdivisionChainHomotopicId R X).homologyMap_eq n,
    HomologicalComplex.homologyMap_id]

/-- **Induced map on homology is the identity (alias).** Same statement as
`barycentricSubdivision_induces_identity_on_homology`, kept under the design's
preferred name. -/
theorem barycentricSubdivision_homologyMap_eq_id
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap (barycentricSubdivisionChainMap R X) n
      = 𝟙 ((singularChainComplex R X).homology n) :=
  barycentricSubdivision_induces_identity_on_homology R X n

/-- **Chain-level boundary witness.**

The difference `sd(c) - c` is the (negative of the) chain-homotopy boundary
`∂ H(c) + H(∂ c)`. Concretely, with the library's index convention,
```text
sd(c) - c = -(∂ H(c) + H(∂ c)),
```
where `H(∂ c)` is `homotopyBoundaryTerm R X n c`. This is the explicit formula
needed later to show that a cycle and its subdivision represent the same homology
class. -/
theorem barycentricSubdivision_sub_id_is_boundary
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (c : singularChainGroup R X n) :
    (barycentricSubdivisionLinearMap R X n).hom c - c
      = -((singularBoundary R X n).hom
            ((barycentricSubdivisionHomotopyLinearMap R X n).hom c)
          + homotopyBoundaryTerm R X n c) := by
  rw [show (singularBoundary R X n).hom
        ((barycentricSubdivisionHomotopyLinearMap R X n).hom c)
        + homotopyBoundaryTerm R X n c
        = c - (barycentricSubdivisionLinearMap R X n).hom c from
      barycentricSubdivisionHomotopy_boundary_formula R X n c]
  abel

end AffineBarycentricSubdivision
end SphereOddDegree
