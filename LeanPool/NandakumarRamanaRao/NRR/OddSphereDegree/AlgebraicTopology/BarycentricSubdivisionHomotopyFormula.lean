/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricSubdivisionChainMap
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricSubdivisionHomotopyOperator
import Mathlib.Tactic

/-! # Barycentric Subdivision Homotopy Formula -/

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits
open Finset

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

/-! ## 0. Functoriality of the pushforward on singular chains -/

theorem singularChainMap_id (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    singularChainMap R (𝟙 X) n = 𝟙 (singularChainGroup R X n) := by
  simp [singularChainMap]

theorem singularChainMap_comp (R : Type) [CommRing R] {X Y Z : TopCat.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    singularChainMap R (f ≫ g) n = singularChainMap R f n ≫ singularChainMap R g n := by
  simp [singularChainMap]

theorem pushSimplex_continuousMap {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (σ : singularSimplices X n) :
    singularSimplexAsContinuousMap Y n (pushSimplex f n σ)
      = (ConcreteCategory.hom f).comp (singularSimplexAsContinuousMap X n σ) := by
  apply ContinuousMap.ext
  intro x
  simp only [pushSimplex, singularSimplexAsContinuousMap, TopCat.toSSetObjEquiv, TopCat.toSSet,
    ContinuousMap.comp_apply]
  rfl

/-! ## 1. `∂∂ = 0` -/

theorem singularBoundary_boundary_zero (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (c : singularChainGroup R X (n + 2)) :
    (singularBoundary R X n).hom ((singularBoundary R X (n + 1)).hom c) = 0 := by
  have h := ((((singularChainComplexFunctor (ModuleCat.{0} R)).obj
      (ModuleCat.of R R)).obj X)).d_comp_d (n + 2) (n + 1) n
  have h2 := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at h2
  exact h2

/-! ## 2. Subdivision in degree `0` is the identity -/

theorem delta0_subsingleton (a b : Delta 0) : a = b := by
  apply Subtype.ext; funext i
  have ha := a.2.2; have hb := b.2.2
  have hi : i = 0 := by omega
  subst hi; rw [Fin.sum_univ_one] at ha hb; rw [ha, hb]

theorem barycentricSubdivisionGenerator_zero (R : Type) [CommRing R] (X : TopCat.{0})
    (σ : singularSimplices X 0) :
    barycentricSubdivisionGenerator R X 0 σ = chainGenerator R X 0 σ := by
  rw [barycentricSubdivisionGenerator]
  have hsimp : ∀ π : Equiv.Perm (Fin 1), barycentricSubdivSimplex X 0 π σ = σ := by
    intro π
    apply singularSimplices_ext
    rw [barycentricSubdivSimplex_continuousMap]
    ext x
    show singularSimplexAsContinuousMap X 0 σ (affineSubdivContinuousMap 0 π x)
       = singularSimplexAsContinuousMap X 0 σ x
    rw [delta0_subsingleton (affineSubdivContinuousMap 0 π x) x]
  have huniq : (Finset.univ : Finset (Equiv.Perm (Fin 1))) = {1} := by
    ext π; simp [Subsingleton.elim π 1]
  rw [huniq]
  simp [hsimp, permSignCoeff]

theorem barycentricHomotopyUniversal_zero (R : Type) [CommRing R] :
    barycentricHomotopyUniversal R 0 = 0 := by
  rw [barycentricHomotopyUniversal, barycentricSubdivisionLinearMap_generator,
      barycentricSubdivisionGenerator_zero, sub_self, map_zero]

/-! ## 3. Naturality of subdivision and homotopy under pushforward -/

theorem pushSimplex_stdSimplexId (X : TopCat.{0}) (n : ℕ) (σ : singularSimplices X n) :
    pushSimplex (TopCat.ofHom (singularSimplexAsContinuousMap X n σ)) n
        (stdSimplexIdSingularSimplex n) = σ := by
  apply singularSimplices_ext
  rw [pushSimplex_continuousMap,
    show stdSimplexIdSingularSimplex n
        = continuousMapAsSingularSimplex (TopCat.of (Delta n)) n (ContinuousMap.id (Delta n)) from rfl]
  simp only [singularSimplexAsContinuousMap_continuousMapAsSingularSimplex, TopCat.hom_ofHom]
  ext x; rfl

theorem pushSimplex_barycentricSubdivSimplex {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (π : Equiv.Perm (Fin (n + 1))) (σ : singularSimplices X n) :
    pushSimplex f n (barycentricSubdivSimplex X n π σ)
      = barycentricSubdivSimplex Y n π (pushSimplex f n σ) := by
  apply singularSimplices_ext
  rw [pushSimplex_continuousMap, barycentricSubdivSimplex_continuousMap,
    barycentricSubdivSimplex_continuousMap, pushSimplex_continuousMap]
  rfl

theorem singularChainMap_barycentricSubdivision_generator (R : Type) [CommRing R]
    {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (σ : singularSimplices X n) :
    (singularChainMap R f n).hom (barycentricSubdivisionGenerator R X n σ)
      = barycentricSubdivisionGenerator R Y n (pushSimplex f n σ) := by
  simp only [barycentricSubdivisionGenerator, map_sum, map_smul, singularChainMap_generator,
    pushSimplex_barycentricSubdivSimplex]

theorem singularChainMap_barycentricSubdivision (R : Type) [CommRing R]
    {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (c : singularChainGroup R X n) :
    (singularChainMap R f n).hom ((barycentricSubdivisionLinearMap R X n).hom c)
      = (barycentricSubdivisionLinearMap R Y n).hom ((singularChainMap R f n).hom c) := by
  have key : barycentricSubdivisionLinearMap R X n ≫ singularChainMap R f n
       = singularChainMap R f n ≫ barycentricSubdivisionLinearMap R Y n := by
    apply Sigma.hom_ext; intro σ; ext
    show (singularChainMap R f n).hom ((barycentricSubdivisionLinearMap R X n).hom
        (chainGenerator R X n σ))
       = (barycentricSubdivisionLinearMap R Y n).hom
          ((singularChainMap R f n).hom (chainGenerator R X n σ))
    rw [singularChainMap_generator, barycentricSubdivisionLinearMap_generator,
        barycentricSubdivisionLinearMap_generator,
        singularChainMap_barycentricSubdivision_generator]
  have h2 := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom key) c
  simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

theorem singularChainMap_barycentricHomotopy_generator (R : Type) [CommRing R]
    {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (σ : singularSimplices X n) :
    (singularChainMap R f (n + 1)).hom
        ((barycentricSubdivisionHomotopyLinearMap R X n).hom (chainGenerator R X n σ))
      = (barycentricSubdivisionHomotopyLinearMap R Y n).hom
          (chainGenerator R Y n (pushSimplex f n σ)) := by
  rw [barycentricSubdivisionHomotopyLinearMap_apply_generator,
      barycentricSubdivisionHomotopyLinearMap_apply_generator,
      ← ModuleCat.comp_apply, ← singularChainMap_comp]
  congr 2

theorem singularChainMap_barycentricHomotopy (R : Type) [CommRing R]
    {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (c : singularChainGroup R X n) :
    (singularChainMap R f (n + 1)).hom
        ((barycentricSubdivisionHomotopyLinearMap R X n).hom c)
      = (barycentricSubdivisionHomotopyLinearMap R Y n).hom ((singularChainMap R f n).hom c) := by
  have key : barycentricSubdivisionHomotopyLinearMap R X n ≫ singularChainMap R f (n+1)
       = singularChainMap R f n ≫ barycentricSubdivisionHomotopyLinearMap R Y n := by
    apply Sigma.hom_ext; intro σ; ext
    show (singularChainMap R f (n+1)).hom ((barycentricSubdivisionHomotopyLinearMap R X n).hom
        (chainGenerator R X n σ))
       = (barycentricSubdivisionHomotopyLinearMap R Y n).hom
          ((singularChainMap R f n).hom (chainGenerator R X n σ))
    rw [singularChainMap_generator, singularChainMap_barycentricHomotopy_generator]
  have h2 := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom key) c
  simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-! ## 4. The recursion equation for the universal chain -/

theorem barycentricHomotopyUniversal_succ_eq (R : Type) [CommRing R] (m : ℕ) :
    barycentricHomotopyUniversal R (m+1)
      = (coneLinearMap R (m + 1) (m + 1) (deltaBarycenter (m + 1))).hom
          (chainGenerator R (TopCat.of (Delta (m + 1))) (m + 1) (stdSimplexIdSingularSimplex (m + 1))
            - (barycentricSubdivisionLinearMap R (TopCat.of (Delta (m + 1))) (m + 1)).hom
                (chainGenerator R (TopCat.of (Delta (m + 1))) (m + 1)
                  (stdSimplexIdSingularSimplex (m + 1)))
            - (barycentricSubdivisionHomotopyLinearMap R (TopCat.of (Delta (m + 1))) m).hom
                ((singularBoundary R (TopCat.of (Delta (m + 1))) m).hom
                  (chainGenerator R (TopCat.of (Delta (m + 1))) (m + 1)
                    (stdSimplexIdSingularSimplex (m + 1))))) := rfl

/-! ## 5. The boundary term and the chain-homotopy formula -/

/-- Apply the subdivision homotopy to the boundary of a chain, using zero in degree zero. -/
noncomputable def homotopyBoundaryTerm (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (c : singularChainGroup R X n) : singularChainGroup R X n :=
  match n with
  | 0 => 0
  | m + 1 => (barycentricSubdivisionHomotopyLinearMap R X m).hom
      ((singularBoundary R X m).hom c)

theorem homotopyBoundaryTerm_succ (R : Type) [CommRing R] (X : TopCat.{0}) (m : ℕ)
    (c : singularChainGroup R X (m+1)) :
    homotopyBoundaryTerm R X (m+1) c
      = (barycentricSubdivisionHomotopyLinearMap R X m).hom
          ((singularBoundary R X m).hom c) := rfl

theorem homotopyBoundaryTerm_zero (R : Type) [CommRing R] (X : TopCat.{0})
    (c : singularChainGroup R X 0) :
    homotopyBoundaryTerm R X 0 c = 0 := rfl

theorem singularChainMap_boundary_apply (R : Type) [CommRing R] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) (c : singularChainGroup R X (n+1)) :
    (singularBoundary R Y n).hom ((singularChainMap R f (n+1)).hom c)
      = (singularChainMap R f n).hom ((singularBoundary R X n).hom c) := by
  have h := singularChainMap_boundary R f n
  have h2 := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) c
  simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

theorem homotopyBoundaryTerm_singularBoundary_eq_zero (R : Type) [CommRing R] (X : TopCat.{0})
    (n : ℕ) (c : singularChainGroup R X (n+1)) :
    homotopyBoundaryTerm R X n ((singularBoundary R X n).hom c) = 0 := by
  cases n with
  | zero => rfl
  | succ k =>
    rw [homotopyBoundaryTerm_succ, singularBoundary_boundary_zero, map_zero]

/-! ## 6. The chain-homotopy formula `∂H + H∂ = id - sd` -/

theorem barycentricSubdivisionHomotopy_boundary_formula (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ) (c : singularChainGroup R X n) :
    (singularBoundary R X n).hom
        ((barycentricSubdivisionHomotopyLinearMap R X n).hom c)
      + homotopyBoundaryTerm R X n c
    = c - (barycentricSubdivisionLinearMap R X n).hom c := by
  induction n generalizing X with
  | zero =>
    have gen : ∀ (X : TopCat.{0}) (σ : singularSimplices X 0),
        (singularBoundary R X 0).hom
            ((barycentricSubdivisionHomotopyLinearMap R X 0).hom (chainGenerator R X 0 σ))
          = chainGenerator R X 0 σ
            - (barycentricSubdivisionLinearMap R X 0).hom (chainGenerator R X 0 σ) := by
      intro X σ
      rw [barycentricSubdivisionHomotopyLinearMap_apply_generator,
          barycentricHomotopyUniversal_zero, map_zero, map_zero,
          barycentricSubdivisionLinearMap_generator, barycentricSubdivisionGenerator_zero,
          sub_self]
    rw [homotopyBoundaryTerm_zero, add_zero]
    have key : barycentricSubdivisionHomotopyLinearMap R X 0 ≫ singularBoundary R X 0
        = 𝟙 _ - barycentricSubdivisionLinearMap R X 0 := by
      apply Sigma.hom_ext; intro σ
      erw [Preadditive.comp_sub, Category.comp_id]
      have hval : ∀ (f g : ModuleCat.of R R ⟶ singularChainGroup R X 0),
          f.hom (1 : R) = g.hom (1 : R) → f = g := by
        intro f g h
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
        have hf := f.hom.map_smul x (1 : R); have hg := g.hom.map_smul x (1 : R)
        simp at hf hg; rw [hf, hg, h]
      apply hval
      erw [ModuleCat.hom_comp, LinearMap.comp_apply,
           ModuleCat.hom_comp, LinearMap.comp_apply,
           ModuleCat.hom_sub, LinearMap.sub_apply,
           ModuleCat.hom_comp, LinearMap.comp_apply]
      exact gen X σ
    have h2 := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom key) c
    simpa [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sub, LinearMap.sub_apply,
      ModuleCat.hom_id, LinearMap.id_apply] using h2
  | succ m IH =>
    have univ : (singularBoundary R (TopCat.of (Delta (m+1))) (m+1)).hom
          (barycentricHomotopyUniversal R (m+1))
        = chainGenerator R (TopCat.of (Delta (m+1))) (m+1) (stdSimplexIdSingularSimplex (m+1))
          - (barycentricSubdivisionLinearMap R (TopCat.of (Delta (m+1))) (m+1)).hom
              (chainGenerator R (TopCat.of (Delta (m+1))) (m+1) (stdSimplexIdSingularSimplex (m+1)))
          - (barycentricSubdivisionHomotopyLinearMap R (TopCat.of (Delta (m+1))) m).hom
              ((singularBoundary R (TopCat.of (Delta (m+1))) m).hom
                (chainGenerator R (TopCat.of (Delta (m+1))) (m+1)
                  (stdSimplexIdSingularSimplex (m+1)))) := by
      rw [barycentricHomotopyUniversal_succ_eq]
      set z := chainGenerator R (TopCat.of (Delta (m+1))) (m+1) (stdSimplexIdSingularSimplex (m+1))
                - (barycentricSubdivisionLinearMap R (TopCat.of (Delta (m+1))) (m+1)).hom
                    (chainGenerator R (TopCat.of (Delta (m+1))) (m+1)
                      (stdSimplexIdSingularSimplex (m+1)))
                - (barycentricSubdivisionHomotopyLinearMap R (TopCat.of (Delta (m+1))) m).hom
                    ((singularBoundary R (TopCat.of (Delta (m+1))) m).hom
                      (chainGenerator R (TopCat.of (Delta (m+1))) (m+1)
                        (stdSimplexIdSingularSimplex (m+1)))) with hz
      have hboundaryz : (singularBoundary R (TopCat.of (Delta (m+1))) m).hom z = 0 := by
        rw [hz, map_sub, map_sub,
            boundary_barycentricSubdivision_apply R (TopCat.of (Delta (m+1))) m
              (chainGenerator R (TopCat.of (Delta (m+1))) (m+1) (stdSimplexIdSingularSimplex (m+1)))]
        have hIH := IH (TopCat.of (Delta (m+1)))
          ((singularBoundary R (TopCat.of (Delta (m+1))) m).hom
            (chainGenerator R (TopCat.of (Delta (m+1))) (m+1) (stdSimplexIdSingularSimplex (m+1))))
        rw [homotopyBoundaryTerm_singularBoundary_eq_zero R (TopCat.of (Delta (m+1))) m
              (chainGenerator R (TopCat.of (Delta (m+1))) (m+1) (stdSimplexIdSingularSimplex (m+1))),
            add_zero] at hIH
        rw [hIH]; abel
      have hcone := DFunLike.congr_fun
        (congrArg ModuleCat.Hom.hom
          (singularBoundary_coneLinearMap R (m+1) m (deltaBarycenter (m+1)))) z
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add, LinearMap.add_apply,
        ModuleCat.hom_id, LinearMap.id_apply] at hcone
      rw [hboundaryz, map_zero, add_zero] at hcone
      exact hcone
    have gen : ∀ (X : TopCat.{0}) (σ : singularSimplices X (m+1)),
        (singularBoundary R X (m+1)).hom
            ((barycentricSubdivisionHomotopyLinearMap R X (m+1)).hom (chainGenerator R X (m+1) σ))
          + (barycentricSubdivisionHomotopyLinearMap R X m).hom
              ((singularBoundary R X m).hom (chainGenerator R X (m+1) σ))
        = chainGenerator R X (m+1) σ
          - (barycentricSubdivisionLinearMap R X (m+1)).hom (chainGenerator R X (m+1) σ) := by
      intro X σ
      rw [barycentricSubdivisionHomotopyLinearMap_apply_generator]
      set f := TopCat.ofHom (singularSimplexAsContinuousMap X (m+1) σ)
      have hpush : pushSimplex f (m+1) (stdSimplexIdSingularSimplex (m+1)) = σ :=
        pushSimplex_stdSimplexId X (m+1) σ
      have hι : (singularChainMap R f (m+1)).hom
          (chainGenerator R (TopCat.of (Delta (m+1))) (m+1) (stdSimplexIdSingularSimplex (m+1)))
          = chainGenerator R X (m+1) σ := by
        rw [singularChainMap_generator, hpush]
      rw [singularChainMap_boundary_apply R f (m+1) (barycentricHomotopyUniversal R (m+1)), univ,
          map_sub, map_sub, hι,
          singularChainMap_barycentricSubdivision R f (m+1)
            (chainGenerator R (TopCat.of (Delta (m+1))) (m+1) (stdSimplexIdSingularSimplex (m+1))),
          hι,
          singularChainMap_barycentricHomotopy R f m
            ((singularBoundary R (TopCat.of (Delta (m+1))) m).hom
              (chainGenerator R (TopCat.of (Delta (m+1))) (m+1) (stdSimplexIdSingularSimplex (m+1)))),
          ← singularChainMap_boundary_apply R f m
            (chainGenerator R (TopCat.of (Delta (m+1))) (m+1) (stdSimplexIdSingularSimplex (m+1))),
          hι]
      abel
    rw [homotopyBoundaryTerm_succ]
    have key : barycentricSubdivisionHomotopyLinearMap R X (m+1) ≫ singularBoundary R X (m+1)
        + singularBoundary R X m ≫ barycentricSubdivisionHomotopyLinearMap R X m
        = 𝟙 _ - barycentricSubdivisionLinearMap R X (m+1) := by
      apply Sigma.hom_ext; intro σ
      erw [Preadditive.comp_add, Preadditive.comp_sub, Category.comp_id]
      have hval : ∀ (f g : ModuleCat.of R R ⟶ singularChainGroup R X (m + 1)),
          f.hom (1 : R) = g.hom (1 : R) → f = g := by
        intro f g h
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
        have hf := f.hom.map_smul x (1 : R); have hg := g.hom.map_smul x (1 : R)
        simp at hf hg; rw [hf, hg, h]
      apply hval
      erw [ModuleCat.hom_add, LinearMap.add_apply,
           ModuleCat.hom_comp, LinearMap.comp_apply,
           ModuleCat.hom_comp, LinearMap.comp_apply,
           ModuleCat.hom_comp, LinearMap.comp_apply,
           ModuleCat.hom_comp, LinearMap.comp_apply,
           ModuleCat.hom_sub, LinearMap.sub_apply,
           ModuleCat.hom_comp, LinearMap.comp_apply]
      exact gen X σ
    have h2 := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom key) c
    simpa [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add, LinearMap.add_apply,
      ModuleCat.hom_sub, LinearMap.sub_apply, ModuleCat.hom_id, LinearMap.id_apply] using h2

theorem barycentricSubdivisionHomotopy_generator_boundary_formula (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ) (σ : singularSimplices X n) :
    (singularBoundary R X n).hom
        ((barycentricSubdivisionHomotopyLinearMap R X n).hom (chainGenerator R X n σ))
      + homotopyBoundaryTerm R X n (chainGenerator R X n σ)
    = chainGenerator R X n σ - (barycentricSubdivisionLinearMap R X n).hom (chainGenerator R X n σ) :=
  barycentricSubdivisionHomotopy_boundary_formula R X n (chainGenerator R X n σ)

end AffineBarycentricSubdivision
end SphereOddDegree
