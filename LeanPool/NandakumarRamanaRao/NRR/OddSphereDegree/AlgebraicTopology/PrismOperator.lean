/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.Analysis.Convex.StdSimplex
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.HomotopyToChainHomotopy
/-!
# Singular prism construction

Builds the cylinder associated to a continuous homotopy after applying the
singular simplicial-set functor. The endpoint identities connect this
construction to the algebraic simplicial-homotopy and chain-homotopy machinery
used by the singular-homology homotopy-invariance proof.
-/

@[expose] public section
open CategoryTheory Limits AlgebraicTopology Simplicial

namespace SphereOddDegree

/-- The unit interval as an object of `TopCat`. -/
noncomputable abbrev unitI : TopCat.{0} := TopCat.of unitInterval

/-- The singular simplicial set functor preserves limits, being a right adjoint
(`sSetTopAdj : SSet.toTop ⊣ TopCat.toSSet`). -/
noncomputable instance singularPreservesLimits : Limits.PreservesLimits TopCat.toSSet.{0} :=
  sSetTopAdj.rightAdjoint_preservesLimits

/-- The const-valued continuous map `X → I` at a point `t` of the interval. -/
noncomputable def constI (X : TopCat.{0}) (t : unitInterval) : X ⟶ unitI :=
  TopCat.ofHom (ContinuousMap.const _ t)

/-- The standard topological `1`-simplex, viewed (via
`Convexity.StdSimplex.homeomorphI`) as a continuous map into the interval. -/
noncomputable def edgeCM : C(Convexity.StdSimplex ℝ (Fin (1 + 1)), unitI) :=
  ⟨Convexity.StdSimplex.homeomorphI, Convexity.StdSimplex.homeomorphI.continuous⟩

/-- The singular edge of the interval: the simplicial `1`-simplex of `Sing I`
classified by the homeomorphism `Δ¹_top ≃ₜ I`. -/
noncomputable def edge : Δ[1] ⟶ TopCat.toSSet.obj unitI :=
  SSet.yonedaEquiv.symm
    ((unitI.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 1))).symm edgeCM)

/-- The const-valued simplicial map onto the `j`-th vertex of `Δ[1]`. -/
noncomputable def vtx (Z : SSet.{0}) (j : Fin 2) : Z ⟶ Δ[1] :=
  SSet.const (SSet.stdSimplex.obj₀Equiv.symm j)

/-- A `ContinuousMap.Homotopy` between `f.hom` and `g.hom`, repackaged as a
single morphism out of the categorical product `X ⨯ I`. On a point `p` it is
`H (snd p, fst p)`, i.e. `H` with its interval coordinate first. -/
noncomputable def homotopyMap {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) : X ⨯ unitI ⟶ Y :=
  TopCat.ofHom
    { toFun := fun p => H.toContinuousMap
        ((Limits.prod.snd (X := X) (Y := unitI)) p, (Limits.prod.fst (X := X) (Y := unitI)) p)
      continuous_toFun := by
        apply H.toContinuousMap.continuous.comp
        exact ((Limits.prod.snd (X := X) (Y := unitI)).hom.continuous).prodMk
          ((Limits.prod.fst (X := X) (Y := unitI)).hom.continuous) }

/-- The **singular cylinder map** of a homotopy `H`:
`Sing X × Δ[1] ⟶ Sing Y`, built from the singular edge of the interval, the
product-preservation isomorphism `Sing X × Sing I ≅ Sing (X × I)`, and `Sing H`. -/
noncomputable def cylinder {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) :
    TopCat.toSSet.obj X ⨯ Δ[1] ⟶ TopCat.toSSet.obj Y :=
  Limits.prod.map (𝟙 (TopCat.toSSet.obj X)) edge ≫
    (PreservesLimitPair.iso TopCat.toSSet X unitI).inv ≫
    TopCat.toSSet.map (homotopyMap H)

/-- The `j`-th endpoint section `Sing X ⟶ Sing X × Δ[1]`. -/
noncomputable def sect (X : TopCat.{0}) (j : Fin 2) :
    TopCat.toSSet.obj X ⟶ TopCat.toSSet.obj X ⨯ Δ[1] :=
  Limits.prod.lift (𝟙 (TopCat.toSSet.obj X)) (vtx (TopCat.toSSet.obj X) j)

/-- At interval coordinate `0`, the repackaged homotopy recovers `f`. -/
theorem homotopyMap_zero {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) :
    Limits.prod.lift (𝟙 X) (constI X 0) ≫ homotopyMap H = f := by
  ext x
  have hfst :
      (Limits.prod.fst (X := X) (Y := unitI))
          ((Limits.prod.lift (𝟙 X) (constI X 0)) x) = x := by
    change ((Limits.prod.lift (𝟙 X) (constI X 0) ≫ Limits.prod.fst) : X ⟶ X) x = x
    rw [Limits.prod.lift_fst]
    rfl
  have hsnd :
      (Limits.prod.snd (X := X) (Y := unitI))
          ((Limits.prod.lift (𝟙 X) (constI X 0)) x) = (0 : unitInterval) := by
    change ((Limits.prod.lift (𝟙 X) (constI X 0) ≫ Limits.prod.snd) : X ⟶ unitI) x =
      (0 : unitInterval)
    rw [Limits.prod.lift_snd]
    change (0 : unitInterval) = 0
    rfl
  change H.toContinuousMap
      ((Limits.prod.snd (X := X) (Y := unitI))
          ((Limits.prod.lift (𝟙 X) (constI X 0)) x),
       (Limits.prod.fst (X := X) (Y := unitI))
          ((Limits.prod.lift (𝟙 X) (constI X 0)) x)) = f x
  rw [hsnd, hfst]
  exact H.apply_zero x

/-- At interval coordinate `1`, the repackaged homotopy recovers `g`. -/
theorem homotopyMap_one {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) :
    Limits.prod.lift (𝟙 X) (constI X 1) ≫ homotopyMap H = g := by
  ext x
  have hfst :
      (Limits.prod.fst (X := X) (Y := unitI))
          ((Limits.prod.lift (𝟙 X) (constI X 1)) x) = x := by
    change ((Limits.prod.lift (𝟙 X) (constI X 1) ≫ Limits.prod.fst) : X ⟶ X) x = x
    rw [Limits.prod.lift_fst]
    rfl
  have hsnd :
      (Limits.prod.snd (X := X) (Y := unitI))
          ((Limits.prod.lift (𝟙 X) (constI X 1)) x) = (1 : unitInterval) := by
    change ((Limits.prod.lift (𝟙 X) (constI X 1) ≫ Limits.prod.snd) : X ⟶ unitI) x =
      (1 : unitInterval)
    rw [Limits.prod.lift_snd]
    change (1 : unitInterval) = 1
    rfl
  change H.toContinuousMap
      ((Limits.prod.snd (X := X) (Y := unitI))
          ((Limits.prod.lift (𝟙 X) (constI X 1)) x),
       (Limits.prod.fst (X := X) (Y := unitI))
          ((Limits.prod.lift (𝟙 X) (constI X 1)) x)) = g x
  rw [hsnd, hfst]
  exact H.apply_one x

/-- The `0`-vertex of `Δ[1]`, pushed along the singular edge, is the const-valued
singular map at `0 ∈ I`. -/
theorem edge_vtx_zero (X : TopCat.{0}) :
    vtx (TopCat.toSSet.obj X) 0 ≫ edge = TopCat.toSSet.map (constI X 0) := by
  rw [vtx, SSet.const_comp]
  change SSet.const _ = TopCat.toSSet.map
    (TopCat.const (X := X) (Y := unitI) (show ↑unitI from (0 : unitInterval)))
  rw [TopCat.toSSet_map_const]
  congr 1
  apply TopCat.toSSetObj₀Equiv.injective
  let α := SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)
  change TopCat.toSSetObj₀Equiv
    ((SSet.yonedaEquiv.symm
      ((unitI.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 1))).symm edgeCM)).app _ α) = 0
  rw [show α = SSet.stdSimplex.objEquiv.symm (SSet.stdSimplex.objEquiv α) by simp]
  rw [SSet.yonedaEquiv_symm_app_objEquiv_symm]
  change unitI.toSSetObjEquiv _
    ((TopCat.toSSet.obj unitI).map _
      ((unitI.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 1))).symm edgeCM)) default = 0
  rw [TopCat.toSSetObjEquiv_naturality_apply]
  change Convexity.StdSimplex.homeomorphI _ = 0
  rw [← Convexity.StdSimplex.homeomorphI_single_zero]
  congr 1
  rw [Subsingleton.elim default (Convexity.StdSimplex.single 0), Convexity.StdSimplex.map_single]
  rfl

/-- The `1`-vertex of `Δ[1]`, pushed along the singular edge, is the const-valued
singular map at `1 ∈ I`. -/
theorem edge_vtx_one (X : TopCat.{0}) :
    vtx (TopCat.toSSet.obj X) 1 ≫ edge = TopCat.toSSet.map (constI X 1) := by
  rw [vtx, SSet.const_comp]
  change SSet.const _ = TopCat.toSSet.map
    (TopCat.const (X := X) (Y := unitI) (show ↑unitI from (1 : unitInterval)))
  rw [TopCat.toSSet_map_const]
  congr 1
  apply TopCat.toSSetObj₀Equiv.injective
  let α := SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)
  change TopCat.toSSetObj₀Equiv
    ((SSet.yonedaEquiv.symm
      ((unitI.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 1))).symm edgeCM)).app _ α) = 1
  rw [show α = SSet.stdSimplex.objEquiv.symm (SSet.stdSimplex.objEquiv α) by simp]
  rw [SSet.yonedaEquiv_symm_app_objEquiv_symm]
  change unitI.toSSetObjEquiv _
    ((TopCat.toSSet.obj unitI).map _
      ((unitI.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 1))).symm edgeCM)) default = 1
  rw [TopCat.toSSetObjEquiv_naturality_apply]
  change Convexity.StdSimplex.homeomorphI _ = 1
  rw [← Convexity.StdSimplex.homeomorphI_single_one]
  congr 1
  rw [Subsingleton.elim default (Convexity.StdSimplex.single 0), Convexity.StdSimplex.map_single]
  rfl

/-- Key reduction: the product-comparison inverse turns the lifted const-valued
section into `Sing` of the lifted topological section. -/
theorem lift_const_comp_iso_inv (X : TopCat.{0}) (j : unitInterval) :
    Limits.prod.lift (𝟙 (TopCat.toSSet.obj X)) (TopCat.toSSet.map (constI X j)) ≫
        (PreservesLimitPair.iso TopCat.toSSet X unitI).inv
      = TopCat.toSSet.map (Limits.prod.lift (𝟙 X) (constI X j)) := by
  rw [Iso.comp_inv_eq, PreservesLimitPair.iso_hom]
  apply Limits.prod.hom_ext
  · simp only [Category.assoc, prodComparison_fst, ← Functor.map_comp,
      Limits.prod.lift_fst, CategoryTheory.Functor.map_id]
  · simp only [Category.assoc, prodComparison_snd, ← Functor.map_comp,
      Limits.prod.lift_snd]

/-- **Endpoint identity (start).** The singular cylinder restricts to `Sing f`
along the start inclusion. -/
theorem cylinder_sect_zero {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) :
    sect X 0 ≫ cylinder H = TopCat.toSSet.map f := by
  unfold cylinder sect;
  convert congr_arg ( fun x => x ≫ TopCat.toSSet.map ( homotopyMap H ) ) (
    lift_const_comp_iso_inv X 0 ) using 1;
  · simp +decide [ ← Category.assoc, ← edge_vtx_zero ];
  · rw [ ← Functor.map_comp, homotopyMap_zero ]

/-- **Endpoint identity (end).** The singular cylinder restricts to `Sing g`
along the end inclusion. -/
theorem cylinder_sect_one {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) :
    sect X 1 ≫ cylinder H = TopCat.toSSet.map g := by
  unfold sect cylinder; simp? +decide [ ← Category.assoc ];
  convert congr_arg ( fun x => x ≫ TopCat.toSSet.map ( homotopyMap H ) ) (
    lift_const_comp_iso_inv X 1 ) using 1;
  · rw [ edge_vtx_one ];
  · rw [ ← Functor.map_comp, homotopyMap_one ]

end SphereOddDegree
