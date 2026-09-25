/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.Backports.StdSimplexOne
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.PrismOperator

/-!
# Combinatorial simplicial homotopy from a topological homotopy (prism, link L4)

This file assembles the library's singular cylinder
(`SphereOddDegree.cylinder`, the simplicial-set homotopy
`Sing X ⨯ Δ[1] ⟶ Sing Y` of a `ContinuousMap.Homotopy`) into a *combinatorial*
`CategoryTheory.SimplicialObject.Homotopy (Sing.map f) (Sing.map g)`, the data
consumed by the backported algebraic prism
`CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy`.
-/

@[expose] public section

open CategoryTheory Simplicial Limits AlgebraicTopology SSet

namespace SphereOddDegree

variable {X Y : TopCat.{0}} {f g : X ⟶ Y}

/-- The degree-, index- component of the combinatorial simplicial homotopy
obtained from the singular cylinder of a topological homotopy. -/
noncomputable def prismH (H : ContinuousMap.Homotopy f.hom g.hom) {n : ℕ}
    (i : Fin (n + 1)) :
    (TopCat.toSSet.obj X) _⦋n⦌ ⟶ (TopCat.toSSet.obj Y) _⦋n + 1⦌ :=
  ↾fun x =>
    SSet.yonedaEquiv.{0}
      (prod.lift
        (SSet.stdSimplex.map (SimplexCategory.σ i) ≫ SSet.yonedaEquiv.{0}.symm x)
        (SSet.yonedaEquiv.{0}.symm (SSet.stdSimplex.objMk₁.{0} i.succ.castSucc))
        ≫ cylinder H)

/-- SSet naturality of `SSet.yonedaEquiv`: applying a simplicial operator to a
simplex classified by `ψ` reclassifies it by precomposition. -/
lemma toSSet_map_yonedaEquiv {Z : SSet.{0}} {m k : ℕ}
    (θ : (⦋m⦌ : SimplexCategory) ⟶ ⦋k⦌) (ψ : Δ[k] ⟶ Z) :
    Z.map θ.op (SSet.yonedaEquiv ψ)
      = SSet.yonedaEquiv (SSet.stdSimplex.map θ ≫ ψ) := by
  rw [SSet.yonedaEquiv_comp]
  exact (NatTrans.naturality_apply ψ θ.op (SSet.yonedaEquiv (𝟙 _))).symm.trans (by
    congr 1)

/-- Unfolding of `prismH` via `SSet.yonedaEquiv_comp`: the prism component is the
cylinder applied to the classifying pair simplex. -/
lemma prismH_apply (H : ContinuousMap.Homotopy f.hom g.hom) {n : ℕ} (i : Fin (n + 1))
    (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    prismH H i x = (cylinder H).app (Opposite.op ⦋n + 1⦌)
      (SSet.yonedaEquiv (Limits.prod.lift
        (SSet.stdSimplex.map (SimplexCategory.σ i) ≫ SSet.yonedaEquiv.symm x)
        (SSet.yonedaEquiv.symm (SSet.stdSimplex.objMk₁.{0} i.succ.castSucc)))) := by
  dsimp [prismH]
  rw [SSet.yonedaEquiv_comp]

/-- The classifying pair simplex of `prismH H i x`, mapped by a simplicial
operator `θ`, is the pair simplex with components precomposed by `θ`. -/
lemma prod_lift_map {m k : ℕ} (θ : (⦋m⦌ : SimplexCategory) ⟶ ⦋k⦌)
    (a : Δ[k] ⟶ TopCat.toSSet.obj X) (b : Δ[k] ⟶ Δ[1]) :
    (TopCat.toSSet.obj X ⨯ Δ[1]).map θ.op
        (SSet.yonedaEquiv (Limits.prod.lift a b))
      = SSet.yonedaEquiv (Limits.prod.lift
          (SSet.stdSimplex.map θ ≫ a) (SSet.stdSimplex.map θ ≫ b)) := by
  rw [toSSet_map_yonedaEquiv, Limits.prod.comp_lift]

/-- `yonedaEquiv.symm` naturality: precomposition by a simplicial operator is
reindexing of the classified simplex. -/
lemma yonedaEquiv_symm_natural {Z : SSet.{0}} {m k : ℕ}
    (θ : (⦋m⦌ : SimplexCategory) ⟶ ⦋k⦌) (t : Z.obj (Opposite.op ⦋k⦌)) :
    SSet.stdSimplex.map θ ≫ SSet.yonedaEquiv.symm t
      = SSet.yonedaEquiv.symm (Z.map θ.op t) := by
  rw [show Z.map θ.op t
        = SSet.yonedaEquiv (SSet.stdSimplex.map θ ≫ SSet.yonedaEquiv.symm t) from by
      conv_lhs => rw [← SSet.yonedaEquiv.apply_symm_apply t]
      rw [toSSet_map_yonedaEquiv],
    SSet.yonedaEquiv.symm_apply_apply]
/-- `objMk₁ 0` is the degenerate simplex concentrated at vertex `1` of `Δ[1]`. -/
lemma objMk₁_zero_eq_const (n : ℕ) :
    SSet.stdSimplex.objMk₁ (0 : Fin (n + 2)) = SSet.stdSimplex.const 1 1 (Opposite.op ⦋n⦌) := by
  ext j : 1
  rfl

/-- `objMk₁ (last)` is the degenerate simplex concentrated at vertex `0` of `Δ[1]`. -/
lemma objMk₁_last_eq_const (n : ℕ) :
    SSet.stdSimplex.objMk₁ (Fin.last (n + 1)) = SSet.stdSimplex.const 1 0 (Opposite.op ⦋n⦌) := by
  ext j : 1
  rw [SSet.stdSimplex.objMk₁_of_castSucc_lt _ _ (Fin.castSucc_lt_last j)]
  rfl
lemma prism_id_zero (H : ContinuousMap.Homotopy f.hom g.hom) (n : ℕ) :
    prismH H (0 : Fin (n + 1)) ≫ (TopCat.toSSet.obj Y).δ 0
      = (TopCat.toSSet.map g).app (Opposite.op ⦋n⦌) := by
  ext x
  dsimp [SimplicialObject.δ]
  rw [prismH_apply, ← (cylinder H).naturality_apply, prod_lift_map, ← SSet.yonedaEquiv_comp]
  conv_rhs => rw [← SSet.yonedaEquiv.apply_symm_apply x, ← SSet.yonedaEquiv_comp]
  refine congr_arg SSet.yonedaEquiv ?_
  rw [← cylinder_sect_one H]
  conv_rhs => rw [← Category.assoc]
  refine congr_arg (· ≫ cylinder H) ?_
  unfold sect
  rw [Limits.prod.comp_lift]
  refine congr_arg₂ Limits.prod.lift ?_ ?_
  · rw [← Category.assoc, ← (SSet.stdSimplex : SimplexCategory ⥤ SSet).map_comp,
      SimplexCategory.δ_comp_σ_self' (by apply Fin.ext; simp),
      (SSet.stdSimplex : SimplexCategory ⥤ SSet).map_id, Category.id_comp, Category.comp_id]
  · rw [yonedaEquiv_symm_natural,
      show (Δ[1] : SSet).map (SimplexCategory.δ (0 : Fin (n + 2))).op
          (SSet.stdSimplex.objMk₁ ((0 : Fin (n + 1)).succ.castSucc))
        = (Δ[1] : SSet).δ 0 (SSet.stdSimplex.objMk₁ ((0 : Fin (n + 1)).succ.castSucc)) from rfl,
      SSet.stdSimplex.δ_objMk₁_of_lt _ _ (by apply Fin.lt_def.mpr; simp)]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv.apply_symm_apply, SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply]
    change _ = SSet.stdSimplex.const 1 1 (Opposite.op ⦋n⦌)
    rw [← objMk₁_zero_eq_const]
    congr 1
lemma prism_id_last (H : ContinuousMap.Homotopy f.hom g.hom) (n : ℕ) :
    prismH H (Fin.last n) ≫ (TopCat.toSSet.obj Y).δ (Fin.last (n + 1))
      = (TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) := by
  ext x
  dsimp [SimplicialObject.δ]
  rw [prismH_apply, ← (cylinder H).naturality_apply, prod_lift_map, ← SSet.yonedaEquiv_comp]
  conv_rhs => rw [← SSet.yonedaEquiv.apply_symm_apply x, ← SSet.yonedaEquiv_comp]
  refine congr_arg SSet.yonedaEquiv ?_
  rw [← cylinder_sect_zero H]
  conv_rhs => rw [← Category.assoc]
  refine congr_arg (· ≫ cylinder H) ?_
  unfold sect
  rw [Limits.prod.comp_lift]
  refine congr_arg₂ Limits.prod.lift ?_ ?_
  · rw [← Category.assoc, ← (SSet.stdSimplex : SimplexCategory ⥤ SSet).map_comp,
      SimplexCategory.δ_comp_σ_succ' (by apply Fin.ext; simp),
      (SSet.stdSimplex : SimplexCategory ⥤ SSet).map_id, Category.id_comp, Category.comp_id]
  · rw [yonedaEquiv_symm_natural,
      show (Δ[1] : SSet).map (SimplexCategory.δ (Fin.last (n + 1))).op
          (SSet.stdSimplex.objMk₁ ((Fin.last n).succ.castSucc))
        = (Δ[1] : SSet).δ (Fin.last (n + 1)) (SSet.stdSimplex.objMk₁ ((Fin.last
          n).succ.castSucc)) from rfl,
      SSet.stdSimplex.δ_objMk₁_of_le _ _ (by apply Fin.le_def.mpr; simp)]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv.apply_symm_apply, SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply]
    change _ = SSet.stdSimplex.const 1 0 (Opposite.op ⦋n⦌)
    rw [← objMk₁_last_eq_const]
    congr 1

lemma prism_id_succ_δ_castSucc_of_lt (H : ContinuousMap.Homotopy f.hom g.hom)
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    prismH H j.succ ≫ (TopCat.toSSet.obj Y).δ i.castSucc
      = (TopCat.toSSet.obj X).δ i ≫ prismH H j := by
  ext x
  dsimp [SimplicialObject.δ]
  rw [prismH_apply, prismH_apply, ← (cylinder H).naturality_apply, prod_lift_map]
  refine congr_arg ((cylinder H).app _) (congr_arg SSet.yonedaEquiv ?_)
  refine congr_arg₂ Limits.prod.lift ?_ ?_
  · rw [← yonedaEquiv_symm_natural, ← Category.assoc, ← Category.assoc,
      ← (SSet.stdSimplex : SimplexCategory ⥤ SSet).map_comp, ← (SSet.stdSimplex :
        SimplexCategory ⥤ SSet).map_comp, SimplexCategory.δ_comp_σ_of_le hij]
  · rw [yonedaEquiv_symm_natural]
    refine congr_arg SSet.yonedaEquiv.symm ?_
    rw [show (Δ[1] : SSet).map (SimplexCategory.δ i.castSucc).op
          (SSet.stdSimplex.objMk₁ j.succ.succ.castSucc)
        = (Δ[1] : SSet).δ i.castSucc (SSet.stdSimplex.objMk₁ j.succ.succ.castSucc) from rfl,
      SSet.stdSimplex.δ_objMk₁_of_lt (j.succ.succ.castSucc) (i.castSucc) ?_]
    · exact congr_arg SSet.stdSimplex.objMk₁ (by apply Fin.ext; simp)
    · rw [Fin.lt_def]
      have : i.val ≤ j.val := Fin.le_def.mp hij
      dsimp
      omega

lemma prism_id_succ_δ_castSucc_succ (H : ContinuousMap.Homotopy f.hom g.hom)
    {n : ℕ} (j : Fin (n + 1)) :
    prismH H j.succ ≫ (TopCat.toSSet.obj Y).δ j.castSucc.succ
      = prismH H j.castSucc ≫ (TopCat.toSSet.obj Y).δ j.castSucc.succ := by
  ext x
  dsimp [SimplicialObject.δ]
  rw [prismH_apply, prismH_apply,
    ← (cylinder H).naturality_apply,
    ← (cylinder H).naturality_apply,
    prod_lift_map, prod_lift_map]
  refine congr_arg ((cylinder H).app _) (congr_arg SSet.yonedaEquiv ?_)
  refine congr_arg₂ Limits.prod.lift ?_ ?_
  · rw [← Category.assoc, ← Category.assoc, ← (SSet.stdSimplex : SimplexCategory ⥤
      SSet).map_comp, ← (SSet.stdSimplex : SimplexCategory ⥤ SSet).map_comp,
      SimplexCategory.δ_comp_σ_self' (by apply Fin.ext; simp),
      SimplexCategory.δ_comp_σ_succ' rfl]
  · rw [yonedaEquiv_symm_natural, yonedaEquiv_symm_natural]
    refine congr_arg SSet.yonedaEquiv.symm ?_
    rw [show (Δ[1] : SSet).map (SimplexCategory.δ j.castSucc.succ).op
          (SSet.stdSimplex.objMk₁ j.succ.succ.castSucc)
        = (Δ[1] : SSet).δ j.castSucc.succ (SSet.stdSimplex.objMk₁ j.succ.succ.castSucc) from rfl,
      show (Δ[1] : SSet).map (SimplexCategory.δ j.castSucc.succ).op
          (SSet.stdSimplex.objMk₁ j.castSucc.succ.castSucc)
        = (Δ[1] : SSet).δ j.castSucc.succ (SSet.stdSimplex.objMk₁ j.castSucc.succ.castSucc) from
          rfl,
      SSet.stdSimplex.δ_objMk₁_of_lt _ _
        (Fin.castSucc_lt_castSucc_iff.mpr (by apply Fin.lt_def.mpr; simp)),
      SSet.stdSimplex.δ_objMk₁_of_le _ _ (le_of_eq (by apply Fin.ext; simp))]
    exact congr_arg SSet.stdSimplex.objMk₁ (by apply Fin.ext; simp)

lemma prism_id_castSucc_δ_succ_of_lt (H : ContinuousMap.Homotopy f.hom g.hom)
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    prismH H j.castSucc ≫ (TopCat.toSSet.obj Y).δ i.succ
      = (TopCat.toSSet.obj X).δ i ≫ prismH H j := by
  ext x
  dsimp [SimplicialObject.δ]
  rw [prismH_apply, prismH_apply, ← (cylinder H).naturality_apply, prod_lift_map]
  refine congr_arg ((cylinder H).app _) (congr_arg SSet.yonedaEquiv ?_)
  refine congr_arg₂ Limits.prod.lift ?_ ?_
  · rw [← yonedaEquiv_symm_natural, ← Category.assoc, ← Category.assoc,
      ← (SSet.stdSimplex : SimplexCategory ⥤ SSet).map_comp, ← (SSet.stdSimplex :
        SimplexCategory ⥤ SSet).map_comp, SimplexCategory.δ_comp_σ_of_gt hji]
  · rw [yonedaEquiv_symm_natural]
    refine congr_arg SSet.yonedaEquiv.symm ?_
    rw [show (Δ[1] : SSet).map (SimplexCategory.δ i.succ).op
          (SSet.stdSimplex.objMk₁ j.castSucc.succ.castSucc)
        = (Δ[1] : SSet).δ i.succ (SSet.stdSimplex.objMk₁ j.castSucc.succ.castSucc) from rfl,
      SSet.stdSimplex.δ_objMk₁_of_le _ _
        (Fin.castSucc_le_castSucc_iff.mpr (Fin.succ_le_succ_iff.mpr (le_of_lt hji))),
      Fin.castPred_castSucc]
    exact congr_arg SSet.stdSimplex.objMk₁ (by apply Fin.ext; simp)

lemma prism_id_comp_σ_castSucc_of_le (H : ContinuousMap.Homotopy f.hom g.hom)
    {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    prismH H j ≫ (TopCat.toSSet.obj Y).σ i.castSucc
      = (TopCat.toSSet.obj X).σ i ≫ prismH H j.succ := by
  ext x
  dsimp [SimplicialObject.σ]
  rw [prismH_apply, prismH_apply, ← (cylinder H).naturality_apply, prod_lift_map]
  refine congr_arg ((cylinder H).app _) (congr_arg SSet.yonedaEquiv ?_)
  refine congr_arg₂ Limits.prod.lift ?_ ?_
  · rw [← yonedaEquiv_symm_natural, ← Category.assoc, ← Category.assoc,
      ← (SSet.stdSimplex : SimplexCategory ⥤ SSet).map_comp, ← (SSet.stdSimplex :
        SimplexCategory ⥤ SSet).map_comp, SimplexCategory.σ_comp_σ hij]
  · rw [yonedaEquiv_symm_natural]
    refine congr_arg SSet.yonedaEquiv.symm ?_
    rw [show (Δ[1] : SSet).map (SimplexCategory.σ i.castSucc).op
          (SSet.stdSimplex.objMk₁ j.succ.castSucc)
        = (Δ[1] : SSet).σ i.castSucc (SSet.stdSimplex.objMk₁ j.succ.castSucc) from rfl,
      SSet.stdSimplex.σ_objMk₁_of_lt _ _
        (Fin.castSucc_lt_castSucc_iff.mpr (Fin.castSucc_lt_succ_iff.mpr hij))]
    exact congr_arg SSet.stdSimplex.objMk₁ (by apply Fin.ext; simp)

lemma prism_id_comp_σ_succ_of_lt (H : ContinuousMap.Homotopy f.hom g.hom)
    {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    prismH H j ≫ (TopCat.toSSet.obj Y).σ i.succ
      = (TopCat.toSSet.obj X).σ i ≫ prismH H j.castSucc := by
  ext x
  dsimp [SimplicialObject.σ]
  rw [prismH_apply, prismH_apply, ← (cylinder H).naturality_apply, prod_lift_map]
  refine congr_arg ((cylinder H).app _) (congr_arg SSet.yonedaEquiv ?_)
  refine congr_arg₂ Limits.prod.lift ?_ ?_
  · rw [← yonedaEquiv_symm_natural, ← Category.assoc, ← Category.assoc,
      ← (SSet.stdSimplex : SimplexCategory ⥤ SSet).map_comp, ← (SSet.stdSimplex :
        SimplexCategory ⥤ SSet).map_comp, SimplexCategory.σ_comp_σ hji]
  · rw [yonedaEquiv_symm_natural]
    refine congr_arg SSet.yonedaEquiv.symm ?_
    rw [show (Δ[1] : SSet).map (SimplexCategory.σ i.succ).op
          (SSet.stdSimplex.objMk₁ j.succ.castSucc)
        = (Δ[1] : SSet).σ i.succ (SSet.stdSimplex.objMk₁ j.succ.castSucc) from rfl,
      SSet.stdSimplex.σ_objMk₁_of_le _ _
        (Fin.castSucc_le_castSucc_iff.mpr (Fin.succ_le_succ_iff.mpr hji))]
    exact congr_arg SSet.stdSimplex.objMk₁ (by apply Fin.ext; simp)

/-- The combinatorial simplicial homotopy between the singular simplicial maps
of two homotopic continuous maps, assembled from the singular cylinder. -/
noncomputable def prismHomotopy (H : ContinuousMap.Homotopy f.hom g.hom) :
    SimplicialObject.Homotopy (TopCat.toSSet.map f) (TopCat.toSSet.map g) where
  h i := prismH H i
  h_zero_comp_δ_zero n := prism_id_zero H n
  h_last_comp_δ_last n := prism_id_last H n
  h_succ_comp_δ_castSucc_of_lt i j hij := prism_id_succ_δ_castSucc_of_lt H i j hij
  h_succ_comp_δ_castSucc_succ j := prism_id_succ_δ_castSucc_succ H j
  h_castSucc_comp_δ_succ_of_lt i j hji := prism_id_castSucc_δ_succ_of_lt H i j hji
  h_comp_σ_castSucc_of_le i j hij := prism_id_comp_σ_castSucc_of_le H i j hij
  h_comp_σ_succ_of_lt i j hji := prism_id_comp_σ_succ_of_lt H i j hji

/-- **The singular prism operator (unconditional).** A homotopy of continuous maps
induces a chain homotopy between the induced integral singular chain maps.
It combines the project's singular cylinder (`prismHomotopy`) with the backported algebraic prism
`CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy`. -/
noncomputable def singularChainHomotopyOfHomotopy
    {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : ContinuousMap.Homotopy f.hom g.hom) :
    Homotopy (singularChainℤ.map f) (singularChainℤ.map g) :=
  ((prismHomotopy H).whiskerRight (sigmaConst.obj (ModuleCat.of ℤ ℤ))).toChainHomotopy

/-- **The singular prism operator, general coefficients (unconditional).** A
homotopy of continuous maps induces a chain homotopy between the singular chain
maps with coefficients in an arbitrary module `Mod : ModuleCat R`. This is the
coefficient-`Mod` generalization of `singularChainHomotopyOfHomotopy`; it is the
keystone that discharges the cohomology prism hypothesis. The simplicial homotopy
`prismHomotopy H` is coefficient-independent; whiskering it through
`sigmaConst.obj Mod` and applying the algebraic prism gives the chain homotopy at
coefficient `Mod`. -/
noncomputable def singularChainHomotopyOfHomotopyModule
    (R : Type) [CommRing R] (Mod : ModuleCat.{0} R)
    {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : ContinuousMap.Homotopy f.hom g.hom) :
    Homotopy (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} R)).obj Mod).map f)
             (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} R)).obj Mod).map g) :=
  ((prismHomotopy H).whiskerRight (sigmaConst.obj Mod)).toChainHomotopy

end SphereOddDegree
