/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricSubdivisionCone
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Sifted
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic

/-! # Barycentric Subdivision Homotopy Operator -/

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits
open Finset

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

/-! ## 1. Pushforward of singular chains along a continuous map -/

/-- The degreewise singular-chain map induced by a continuous map. -/
noncomputable def singularChainMap (R : Type) [CommRing R] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) :
    singularChainGroup R X n ⟶ singularChainGroup R Y n :=
  (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map f).f n

/-- Postcompose a singular simplex with a continuous map. -/
noncomputable def pushSimplex {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (σ : singularSimplices X n) : singularSimplices Y n :=
  (TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n)) σ

theorem singularChainMap_generator (R : Type) [CommRing R] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) (σ : singularSimplices X n) :
    (singularChainMap R f n).hom (chainGenerator R X n σ)
      = chainGenerator R Y n (pushSimplex f n σ) := by
  unfold singularChainMap chainGenerator pushSimplex
  have key : (Limits.Sigma.ι (fun (_ : singularSimplices X n) => ModuleCat.of R R) σ)
      ≫ (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map f).f n
      = Limits.Sigma.ι (fun (_ : singularSimplices Y n) => ModuleCat.of R R)
        ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n)) σ) := by
    change Sigma.ι (fun _ => ModuleCat.of R R) σ ≫
         (sigmaConst.obj (ModuleCat.of R R)).map ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌)) = _
    rw [sigmaConst_obj_map, Sigma.ι_comp_map']
    simp
  have := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom key) (1 : R)
  erw [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact this

theorem singularChainMap_boundary (R : Type) [CommRing R] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) :
    singularChainMap R f (n + 1) ≫ singularBoundary R Y n
      = singularBoundary R X n ≫ singularChainMap R f n := by
  have h := ((((singularChainComplexFunctor (ModuleCat.{0} R)).obj
      (ModuleCat.of R R)).map f)).comm (n + 1) n
  simp [singularChainMap, singularBoundary, h]

/-! ## 2. The barycenter and the identity singular simplex of `Δⁿ` -/

/-- The barycenter of the standard real simplex. -/
noncomputable def deltaBarycenter (n : ℕ) : Delta n :=
  stdSimplex.barycenter (X := Fin (n + 1)) (𝕜 := ℝ)

/-- The identity map of the standard simplex viewed as a singular simplex. -/
noncomputable def stdSimplexIdSingularSimplex (n : ℕ) :
    singularSimplices (TopCat.of (Delta n)) n :=
  continuousMapAsSingularSimplex (TopCat.of (Delta n)) n (ContinuousMap.id (Delta n))

/-! ## 3. The homotopy operator built from a universal chain -/

/-- Push a universal homotopy chain along a singular simplex and scale by a coefficient. -/
noncomputable def pushUniversalHom (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (T : singularChainGroup R (TopCat.of (Delta n)) (n + 1))
    (σ : singularSimplices X n) :
    ModuleCat.of R R ⟶ singularChainGroup R X (n + 1) :=
  ModuleCat.ofHom
    { toFun := fun r =>
        r • (singularChainMap R (TopCat.ofHom (singularSimplexAsContinuousMap X n σ)) (n + 1)).hom T
      map_add' := fun r s => add_smul r s _
      map_smul' := fun a r => mul_smul a r _ }

/-- Extend a universal homotopy chain to arbitrary singular chains by linearity. -/
noncomputable def homotopyFromUniversal (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (T : singularChainGroup R (TopCat.of (Delta n)) (n + 1)) :
    singularChainGroup R X n ⟶ singularChainGroup R X (n + 1) :=
  Sigma.desc (pushUniversalHom R X n T)

theorem homotopyFromUniversal_generator (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (T : singularChainGroup R (TopCat.of (Delta n)) (n + 1))
    (σ : singularSimplices X n) :
    (homotopyFromUniversal R X n T).hom (chainGenerator R X n σ)
      = (singularChainMap R (TopCat.ofHom (singularSimplexAsContinuousMap X n σ)) (n + 1)).hom T := by
  have h := Sigma.ι_comp_desc (fun σ => pushUniversalHom R X n T σ) σ
  have happ := congrArg (fun (m : ModuleCat.of R R ⟶ singularChainGroup R X (n + 1)) => m.hom (1 : R)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at happ
  have h1 : (pushUniversalHom R X n T σ).hom (1 : R)
      = (singularChainMap R (TopCat.ofHom (singularSimplexAsContinuousMap X n σ)) (n + 1)).hom T :=
    one_smul R _
  have hgen : chainGenerator R X n σ = (Sigma.ι (fun (_ : singularSimplices X n) => ModuleCat.of R R) σ).hom (1 : R) := rfl
  rw [hgen]
  exact happ.trans h1

/-! ## 4. The universal homotopy chain `T_n(ι_n)` -/

/-- The recursively coned universal chain witnessing homotopy to barycentric subdivision. -/
noncomputable def barycentricHomotopyUniversal (R : Type) [CommRing R] (n : ℕ) :
    singularChainGroup R (TopCat.of (Delta n)) (n + 1) :=
  match n with
  | 0 =>
      (coneLinearMap R 0 0 (deltaBarycenter 0)).hom
        (chainGenerator R (TopCat.of (Delta 0)) 0 (stdSimplexIdSingularSimplex 0)
          - (barycentricSubdivisionLinearMap R (TopCat.of (Delta 0)) 0).hom
              (chainGenerator R (TopCat.of (Delta 0)) 0 (stdSimplexIdSingularSimplex 0)))
  | m + 1 =>
      (coneLinearMap R (m + 1) (m + 1) (deltaBarycenter (m + 1))).hom
        (chainGenerator R (TopCat.of (Delta (m + 1))) (m + 1) (stdSimplexIdSingularSimplex (m + 1))
          - (barycentricSubdivisionLinearMap R (TopCat.of (Delta (m + 1))) (m + 1)).hom
              (chainGenerator R (TopCat.of (Delta (m + 1))) (m + 1)
                (stdSimplexIdSingularSimplex (m + 1)))
          - (homotopyFromUniversal R (TopCat.of (Delta (m + 1))) m
                (barycentricHomotopyUniversal R m)).hom
              ((singularBoundary R (TopCat.of (Delta (m + 1))) m).hom
                (chainGenerator R (TopCat.of (Delta (m + 1))) (m + 1)
                  (stdSimplexIdSingularSimplex (m + 1)))))

/-! ## 5. The degree-wise homotopy operator -/

/-- The degree-raising chain homotopy map induced by the universal subdivision chain. -/
noncomputable def barycentricSubdivisionHomotopyLinearMap (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ) :
    singularChainGroup R X n ⟶ singularChainGroup R X (n + 1) :=
  homotopyFromUniversal R X n (barycentricHomotopyUniversal R n)

theorem barycentricSubdivisionHomotopyLinearMap_apply_generator (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ) (σ : singularSimplices X n) :
    (barycentricSubdivisionHomotopyLinearMap R X n).hom (chainGenerator R X n σ)
      = (singularChainMap R (TopCat.ofHom (singularSimplexAsContinuousMap X n σ)) (n + 1)).hom
          (barycentricHomotopyUniversal R n) := by
  rw [barycentricSubdivisionHomotopyLinearMap, homotopyFromUniversal_generator]

theorem barycentricSubdivisionHomotopyLinearMap_map_zero (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ) :
    (barycentricSubdivisionHomotopyLinearMap R X n).hom 0 = 0 :=
  map_zero _

theorem barycentricSubdivisionHomotopyLinearMap_map_add (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ) (c d : singularChainGroup R X n) :
    (barycentricSubdivisionHomotopyLinearMap R X n).hom (c + d)
      = (barycentricSubdivisionHomotopyLinearMap R X n).hom c
        + (barycentricSubdivisionHomotopyLinearMap R X n).hom d :=
  map_add _ c d

theorem barycentricSubdivisionHomotopyLinearMap_smul (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ) (a : R) (c : singularChainGroup R X n) :
    (barycentricSubdivisionHomotopyLinearMap R X n).hom (a • c)
      = a • (barycentricSubdivisionHomotopyLinearMap R X n).hom c :=
  map_smul _ a c

end AffineBarycentricSubdivision
end SphereOddDegree
