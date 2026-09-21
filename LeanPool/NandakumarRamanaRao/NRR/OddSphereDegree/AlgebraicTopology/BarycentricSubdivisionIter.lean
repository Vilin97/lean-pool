/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricSubdivisionChainHomotopy
import Mathlib

/-! # Barycentric Subdivision Iter -/

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits

namespace SphereOddDegree
namespace AffineBarycentricSubdivision
/-- The `N`-fold barycentric subdivision chain map `sd^N`, defined by
`sd^0 = 𝟙` and `sd^(N+1) = sd ≫ sd^N`. -/
noncomputable def barycentricSubdivisionIterChainMap
    (R : Type) [CommRing R] (X : TopCat.{0}) (N : ℕ) :
    singularChainComplex R X ⟶ singularChainComplex R X :=
  match N with
  | 0 => 𝟙 _
  | N + 1 => barycentricSubdivisionChainMap R X ≫ barycentricSubdivisionIterChainMap R X N

@[simp] theorem barycentricSubdivisionIterChainMap_zero
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    barycentricSubdivisionIterChainMap R X 0 = 𝟙 _ := rfl

theorem barycentricSubdivisionIterChainMap_succ
    (R : Type) [CommRing R] (X : TopCat.{0}) (N : ℕ) :
    barycentricSubdivisionIterChainMap R X (N+1)
      = barycentricSubdivisionChainMap R X ≫ barycentricSubdivisionIterChainMap R X N := rfl

/-- The degree-`n` component of `sd^N` as an `R`-linear map. -/
noncomputable def barycentricSubdivisionIterLinearMap
    (R : Type) [CommRing R] (X : TopCat.{0}) (N n : ℕ) :
    singularChainGroup R X n →ₗ[R] singularChainGroup R X n :=
  ((barycentricSubdivisionIterChainMap R X N).f n).hom

/-- In iterate `0`, the degree-wise map is the identity. -/
theorem barycentricSubdivisionIterLinearMap_zero
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) (c : singularChainGroup R X n) :
    barycentricSubdivisionIterLinearMap R X 0 n c = c := rfl

/-- The degree-wise successor formula `(sd^(N+1))_n c = (sd^N)_n (sd_n c)`. -/
theorem barycentricSubdivisionIterLinearMap_succ
    (R : Type) [CommRing R] (X : TopCat.{0}) (N n : ℕ) (c : singularChainGroup R X n) :
    barycentricSubdivisionIterLinearMap R X (N+1) n c
      = barycentricSubdivisionIterLinearMap R X N n
          ((barycentricSubdivisionLinearMap R X n).hom c) := rfl

/-- **`sd^N` commutes with the boundary** (degree-wise, pointwise form). This is
the chain-map condition of `barycentricSubdivisionIterChainMap`. -/
theorem barycentricSubdivisionIterLinearMap_commutes_boundary
    (R : Type) [CommRing R] (X : TopCat.{0}) (N n : ℕ) (c : singularChainGroup R X (n+1)) :
    (singularBoundary R X n).hom (barycentricSubdivisionIterLinearMap R X N (n+1) c)
      = barycentricSubdivisionIterLinearMap R X N n ((singularBoundary R X n).hom c) := by
  have h := (barycentricSubdivisionIterChainMap R X N).comm (n+1) n
  have h3 := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) c
  erw [ModuleCat.hom_comp, LinearMap.comp_apply,
       ModuleCat.hom_comp, LinearMap.comp_apply] at h3
  exact h3

/-- The explicit accumulated homotopy operator
`H^(N) = Σ_{r=0}^{N-1} (sd^r) ∘ H`, defined by `H^(0) = 0` and
`H^(N+1)_n = H^(N)_n + (sd^N)_{n+1} ∘ H_n`. -/
noncomputable def barycentricSubdivisionIterHomotopyLinearMap
    (R : Type) [CommRing R] (X : TopCat.{0}) (N n : ℕ) :
    singularChainGroup R X n →ₗ[R] singularChainGroup R X (n + 1) :=
  match N with
  | 0 => 0
  | N + 1 => barycentricSubdivisionIterHomotopyLinearMap R X N n
      + (barycentricSubdivisionIterLinearMap R X N (n+1)) ∘ₗ
          (barycentricSubdivisionHomotopyLinearMap R X n).hom

@[simp] theorem barycentricSubdivisionIterHomotopyLinearMap_zero
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) (c : singularChainGroup R X n) :
    barycentricSubdivisionIterHomotopyLinearMap R X 0 n c = 0 := rfl

theorem barycentricSubdivisionIterHomotopyLinearMap_succ
    (R : Type) [CommRing R] (X : TopCat.{0}) (N n : ℕ) (c : singularChainGroup R X n) :
    barycentricSubdivisionIterHomotopyLinearMap R X (N+1) n c
      = barycentricSubdivisionIterHomotopyLinearMap R X N n c
        + barycentricSubdivisionIterLinearMap R X N (n+1)
            ((barycentricSubdivisionHomotopyLinearMap R X n).hom c) := rfl

/-- The degree-wise "`H ∘ ∂`" term of the iterated homotopy formula. In degree
`0` it is `0`; in degree `m+1` it is `H^(N)_m (∂_m c)`. This matches the library's
index convention `∂ : C_{n+1} → C_n = singularBoundary R X n`, exactly as
`homotopyBoundaryTerm` did for the one-step formula. -/
noncomputable def barycentricSubdivisionIterHomotopyBoundaryTerm
    (R : Type) [CommRing R] (X : TopCat.{0}) (N n : ℕ)
    (c : singularChainGroup R X n) : singularChainGroup R X n :=
  match n with
  | 0 => 0
  | m + 1 => barycentricSubdivisionIterHomotopyLinearMap R X N m
      ((singularBoundary R X m).hom c)

theorem barycentricSubdivisionIterHomotopyBoundaryTerm_zero
    (R : Type) [CommRing R] (X : TopCat.{0}) (N : ℕ) (c : singularChainGroup R X 0) :
    barycentricSubdivisionIterHomotopyBoundaryTerm R X N 0 c = 0 := rfl

theorem barycentricSubdivisionIterHomotopyBoundaryTerm_succ
    (R : Type) [CommRing R] (X : TopCat.{0}) (N m : ℕ) (c : singularChainGroup R X (m+1)) :
    barycentricSubdivisionIterHomotopyBoundaryTerm R X N (m+1) c
      = barycentricSubdivisionIterHomotopyLinearMap R X N m
          ((singularBoundary R X m).hom c) := rfl

/-- **Recursion for the boundary term.** Increasing the iterate by one adds the
contribution `(sd^N)_n (H(∂ c))` from the one-step boundary term. -/
theorem barycentricSubdivisionIterHomotopyBoundaryTerm_succ_iter
    (R : Type) [CommRing R] (X : TopCat.{0}) (N n : ℕ) (c : singularChainGroup R X n) :
    barycentricSubdivisionIterHomotopyBoundaryTerm R X (N+1) n c
      = barycentricSubdivisionIterHomotopyBoundaryTerm R X N n c
        + barycentricSubdivisionIterLinearMap R X N n (homotopyBoundaryTerm R X n c) := by
  cases n with
  | zero =>
    rw [barycentricSubdivisionIterHomotopyBoundaryTerm_zero,
        barycentricSubdivisionIterHomotopyBoundaryTerm_zero,
        homotopyBoundaryTerm_zero, map_zero, add_zero]
  | succ m =>
    rw [barycentricSubdivisionIterHomotopyBoundaryTerm_succ,
        barycentricSubdivisionIterHomotopyLinearMap_succ,
        homotopyBoundaryTerm_succ,
        barycentricSubdivisionIterHomotopyBoundaryTerm_succ]

/-- **Every iterate of barycentric subdivision is chain-homotopic to the
identity.** -/
noncomputable def barycentricSubdivisionIter_chainHomotopic_id
    (R : Type) [CommRing R] (X : TopCat.{0}) (N : ℕ) :
    Homotopy (barycentricSubdivisionIterChainMap R X N)
      (𝟙 (singularChainComplex R X)) := by
  induction N with
  | zero => exact Homotopy.refl _
  | succ N ih =>
    exact (Homotopy.comp (barycentricSubdivision_chainHomotopic_id R X) ih).trans
      (Homotopy.ofEq (Category.id_comp _))

/-- **`sd^N` induces the identity on homology.** -/
theorem barycentricSubdivisionIter_induces_identity_on_homology
    (R : Type) [CommRing R] (X : TopCat.{0}) (N n : ℕ) :
    HomologicalComplex.homologyMap (barycentricSubdivisionIterChainMap R X N) n
      = 𝟙 ((singularChainComplex R X).homology n) := by
  rw [(barycentricSubdivisionIter_chainHomotopic_id R X N).homologyMap_eq n,
    HomologicalComplex.homologyMap_id]

/--
**The iterated barycentric subdivision boundary formula.**

For every singular chain `c ∈ C_n(X; R)` and every `N`,
```text
c - sd^N(c) = ∂ (H^(N) c) + H^(N)(∂ c),
```
where `sd^N = barycentricSubdivisionIterLinearMap`, `H^(N) =
barycentricSubdivisionIterHomotopyLinearMap` is the explicit accumulated
homotopy, `∂ = singularBoundary`, and the term `H^(N)(∂ c)` is packaged degree-wise
as `barycentricSubdivisionIterHomotopyBoundaryTerm` (which is `H^(N)_{n-1}(∂_{n-1} c)`
in positive degree and `0` in degree `0`, matching the library's index convention
`∂ : C_{n+1} → C_n = singularBoundary R X n`).
-/
theorem barycentricSubdivisionIter_boundary_formula
    (R : Type) [CommRing R] (X : TopCat.{0}) (N n : ℕ)
    (c : singularChainGroup R X n) :
    c - barycentricSubdivisionIterLinearMap R X N n c
      = (singularBoundary R X n).hom
          (barycentricSubdivisionIterHomotopyLinearMap R X N n c)
        + barycentricSubdivisionIterHomotopyBoundaryTerm R X N n c := by
  induction N generalizing n c with
  | zero =>
    cases n with
    | zero =>
      rw [barycentricSubdivisionIterLinearMap_zero, sub_self,
          barycentricSubdivisionIterHomotopyLinearMap_zero, map_zero,
          barycentricSubdivisionIterHomotopyBoundaryTerm_zero, add_zero]
    | succ m =>
      rw [barycentricSubdivisionIterLinearMap_zero, sub_self,
          barycentricSubdivisionIterHomotopyLinearMap_zero, map_zero,
          barycentricSubdivisionIterHomotopyBoundaryTerm_succ,
          barycentricSubdivisionIterHomotopyLinearMap_zero, add_zero]
  | succ N ih =>
    have h1step := barycentricSubdivisionHomotopy_boundary_formula R X n c
    have hlin : c - barycentricSubdivisionIterLinearMap R X (N + 1) n c
        = (c - barycentricSubdivisionIterLinearMap R X N n c)
          + barycentricSubdivisionIterLinearMap R X N n
              (c - (barycentricSubdivisionLinearMap R X n).hom c) := by
      rw [barycentricSubdivisionIterLinearMap_succ, map_sub]
      abel
    rw [hlin, ih, ← h1step, map_add,
        ← barycentricSubdivisionIterLinearMap_commutes_boundary,
        barycentricSubdivisionIterHomotopyBoundaryTerm_succ_iter,
        barycentricSubdivisionIterHomotopyLinearMap_succ,
        map_add]
    abel

end AffineBarycentricSubdivision
end SphereOddDegree
