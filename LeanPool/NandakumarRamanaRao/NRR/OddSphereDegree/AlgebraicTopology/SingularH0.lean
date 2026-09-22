/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SubChainSubspaceBridge
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricSubdivisionCone

/-! # Singular H0 -/

open CategoryTheory AlgebraicTopology Limits
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision

noncomputable section
namespace SphereOddDegree

variable {X : TopCat.{0}}

/-- The `0`-simplex of `X` sitting at the point `x`. -/
noncomputable def pointSimplex (X : TopCat.{0}) (x : X) : singularSimplices X 0 :=
  continuousMapAsSingularSimplex X 0 (ContinuousMap.const (Delta 0) x)

/-- The singular `1`-simplex of `X` obtained from a path, by reparametrising the
standard `1`-simplex `Δ¹` as the unit interval. -/
noncomputable def pathSimplex {a b : X} (p : Path a b) : singularSimplices X 1 :=
  continuousMapAsSingularSimplex X 1
    (p.toContinuousMap.comp
      (⟨stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval.continuous⟩ :
        C(Delta 1, unitInterval)))

theorem test_coface0 (x : Delta 0) : cofaceTop 0 0 x = ⟨Pi.single 1 1, single_mem_stdSimplex ℝ 1⟩ := by
  ext i
  fin_cases i <;> simp [cofaceTop, delta0_subsingleton x (stdSimplex.vertex 0)]

theorem test_coface1 (x : Delta 0) : cofaceTop 0 1 x = ⟨Pi.single 0 1, single_mem_stdSimplex ℝ 0⟩ := by
  ext i
  fin_cases i <;> simp [cofaceTop, delta0_subsingleton x (stdSimplex.vertex 0)]

theorem faceSimplex_pathSimplex_0 {a b : X} (p : Path a b) :
    AlexanderWhitney.faceSimplex X 0 0 (pathSimplex p) = pointSimplex X b := by
  apply singularSimplices_ext
  change singularSimplexAsContinuousMap X 0 _ = singularSimplexAsContinuousMap X 0 _
  rw [faceSimplex_continuousMap]
  simp only [pathSimplex, pointSimplex,
    singularSimplexAsContinuousMap_continuousMapAsSingularSimplex]
  ext x
  change p (stdSimplexHomeomorphUnitInterval (cofaceTop 0 0 x)) = b
  rw [test_coface0 x, stdSimplexHomeomorphUnitInterval_one]
  exact p.target

theorem faceSimplex_pathSimplex_1 {a b : X} (p : Path a b) :
    AlexanderWhitney.faceSimplex X 0 1 (pathSimplex p) = pointSimplex X a := by
  apply singularSimplices_ext
  change singularSimplexAsContinuousMap X 0 _ = singularSimplexAsContinuousMap X 0 _
  rw [faceSimplex_continuousMap]
  simp only [pathSimplex, pointSimplex,
    singularSimplexAsContinuousMap_continuousMapAsSingularSimplex]
  ext x
  change p (stdSimplexHomeomorphUnitInterval (cofaceTop 0 1 x)) = a
  rw [test_coface1 x, stdSimplexHomeomorphUnitInterval_zero]
  exact p.source

theorem boundary_pathSimplex {a b : X} (p : Path a b) :
    (singularBoundary ℤ X 0).hom (chainGenerator ℤ X 1 (pathSimplex p))
      = chainGenerator ℤ X 0 (pointSimplex X b) - chainGenerator ℤ X 0 (pointSimplex X a) := by
  have key := singularBoundary_chainGenerator_formula ℤ X 0 (pathSimplex p)
  rw [Fin.sum_univ_two, faceSimplex_pathSimplex_0, faceSimplex_pathSimplex_1] at key
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one, neg_smul] at key
  rw [sub_eq_add_neg]
  convert key using 2
  · exact (@one_smul ℤ (singularChainGroup ℤ X 0) _ (singularChainGroup ℤ X 0).isModule.toMulAction _).symm
  · congr 1
    exact (@one_smul ℤ (singularChainGroup ℤ X 0) _ (singularChainGroup ℤ X 0).isModule.toMulAction _).symm

theorem chainGenerator_sub_mem_range_of_path {a b : X} (p : Path a b) :
    chainGenerator ℤ X 0 (pointSimplex X b) - chainGenerator ℤ X 0 (pointSimplex X a)
      ∈ LinearMap.range (singularBoundary ℤ X 0).hom :=
  ⟨chainGenerator ℤ X 1 (pathSimplex p), boundary_pathSimplex p⟩

theorem pointSimplex_singularSimplex (σ : singularSimplices X 0) :
    pointSimplex X ((singularSimplexAsContinuousMap X 0 σ) (stdSimplex.vertex 0)) = σ := by
  apply singularSimplices_ext
  change singularSimplexAsContinuousMap X 0 _ = singularSimplexAsContinuousMap X 0 σ
  rw [pointSimplex, singularSimplexAsContinuousMap_continuousMapAsSingularSimplex]
  ext x
  change (singularSimplexAsContinuousMap X 0 σ) _ =
    (singularSimplexAsContinuousMap X 0 σ) x
  exact congrArg (singularSimplexAsContinuousMap X 0 σ) (delta0_subsingleton _ x)

theorem chainGenerator_sub_mem_range [PathConnectedSpace X] (σ τ : singularSimplices X 0) :
    chainGenerator ℤ X 0 σ - chainGenerator ℤ X 0 τ
      ∈ LinearMap.range (singularBoundary ℤ X 0).hom := by
  let a := (singularSimplexAsContinuousMap X 0 σ) (stdSimplex.vertex 0)
  let b := (singularSimplexAsContinuousMap X 0 τ) (stdSimplex.vertex 0)
  have hσ : σ = pointSimplex X a := (pointSimplex_singularSimplex σ).symm
  have hτ : τ = pointSimplex X b := (pointSimplex_singularSimplex τ).symm
  rw [hσ, hτ]
  have := chainGenerator_sub_mem_range_of_path (PathConnectedSpace.somePath b a)
  exact this

/-- The augmentation sending every singular zero-simplex to one. -/
noncomputable def aug (X : TopCat.{0}) : singularChainGroup ℤ X 0 ⟶ ModuleCat.of ℤ ℤ :=
  Limits.Sigma.desc (fun _ => 𝟙 (ModuleCat.of ℤ ℤ))

@[simp] theorem aug_generator (σ : singularSimplices X 0) :
    (aug X).hom (chainGenerator ℤ X 0 σ) = 1 := by
  have key : (Sigma.ι (fun _ : singularSimplices X 0 => ModuleCat.of ℤ ℤ) σ) ≫ (aug X) = 𝟙 _ :=
    Sigma.ι_comp_desc _ _
  have := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom key) (1 : ℤ)
  erw [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact this

theorem aug_boundary (c : singularChainGroup ℤ X 1) :
    (aug X).hom ((singularBoundary ℤ X 0).hom c) = 0 := by
  let f : singularChainGroup ℤ X 1 ⟶ ModuleCat.of ℤ ℤ :=
    singularBoundary ℤ X 0 ≫ aug X
  have hf : f = 0 := by
    apply Limits.colimit.hom_ext
    intro τ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change (aug X).hom ((singularBoundary ℤ X 0).hom (chainGenerator ℤ X 1 τ.as)) = 0
    have key := singularBoundary_chainGenerator_formula ℤ X 0 τ.as
    rw [Fin.sum_univ_two] at key
    simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one, neg_smul] at key
    have h_bnd : (singularBoundary ℤ X 0).hom (chainGenerator ℤ X 1 τ.as) =
        chainGenerator ℤ X 0 (AlexanderWhitney.faceSimplex X 0 0 τ.as) -
        chainGenerator ℤ X 0 (AlexanderWhitney.faceSimplex X 0 1 τ.as) := by
      rw [sub_eq_add_neg]
      convert key using 2
      · exact (@one_smul ℤ (singularChainGroup ℤ X 0) _ (singularChainGroup ℤ X 0).isModule.toMulAction _).symm
      · congr 1
        exact (@one_smul ℤ (singularChainGroup ℤ X 0) _ (singularChainGroup ℤ X 0).isModule.toMulAction _).symm
    rw [h_bnd, map_sub, aug_generator, aug_generator, sub_self]
  have hc := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hf) c
  exact hc

theorem sub_aug_smul_basept_mem_range [PathConnectedSpace X] (b : X)
    (c : singularChainGroup ℤ X 0) :
    c - (aug X).hom c • chainGenerator ℤ X 0 (pointSimplex X b)
      ∈ LinearMap.range (singularBoundary ℤ X 0).hom := by
  have h_span : c ∈ AddSubgroup.closure (Set.range (chainGenerator ℤ X 0)) := by
    have hc0 : c ∈ Submodule.span ℤ (Set.range (chainGenerator ℤ X 0)) := by
      rw [chainGenerator_span_top]; exact Submodule.mem_top
    induction hc0 using Submodule.span_induction with
    | mem y hy => exact AddSubgroup.subset_closure hy
    | zero => exact zero_mem _
    | add p q _ _ hp hq => exact add_mem hp hq
    | smul r a _ ha => convert zsmul_mem ha r using 1; exact int_smul_eq_zsmul _ r a
  induction h_span using AddSubgroup.closure_induction with
  | mem c hc =>
      obtain ⟨σ, rfl⟩ := hc
      rw [aug_generator, one_zsmul]
      exact chainGenerator_sub_mem_range σ (pointSimplex X b)
  | zero => simp
  | add x y _ _ hx hy =>
      have h : x + y - (aug X).hom (x + y) • chainGenerator ℤ X 0 (pointSimplex X b)
          = (x - (aug X).hom x • chainGenerator ℤ X 0 (pointSimplex X b))
            + (y - (aug X).hom y • chainGenerator ℤ X 0 (pointSimplex X b)) := by
        rw [map_add, add_zsmul]; abel
      rw [h]; exact Submodule.add_mem _ hx hy
  | neg x _ hx =>
      have h : -x - (aug X).hom (-x) • chainGenerator ℤ X 0 (pointSimplex X b)
          = -(x - (aug X).hom x • chainGenerator ℤ X 0 (pointSimplex X b)) := by
        rw [map_neg, neg_zsmul]; abel
      rw [h]; exact Submodule.neg_mem _ hx

end SphereOddDegree
