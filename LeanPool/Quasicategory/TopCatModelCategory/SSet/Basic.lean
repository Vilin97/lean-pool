/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

universe u

open CategoryTheory Simplicial Opposite

namespace SSet

/-@[simps]
def const {X Y : SSet.{u}} (y : Y _[0]) : X ⟶ Y where
  app n _ := Y.map (n.unop.const _ 0).op y
  naturality n m f := by
    ext
    dsimp
    rw [← Functor.map_comp_apply]
    rfl

@[reassoc (attr := simp)]
lemma comp_const {X Y Z : SSet.{u}} (f : X ⟶ Y) (z : Z _[0]) :
    f ≫ const z = const z := rfl

@[reassoc (attr := simp)]
lemma const_comp {X Y Z : SSet.{u}} (y : Y _[0]) (g : Y ⟶ Z) :
    const (X := X) y ≫ g = const (g.app _ y) := by
  ext m x
  simp [NatTrans.naturality_apply]-/

@[deprecated (since := "2025-03-19")]
alias yonedaEquiv_apply_comp := yonedaEquiv_comp

@[reassoc]
lemma stdSimplex.map_comp_yonedaEquiv_symm {X : SSet.{u}} {n m : SimplexCategory}
    (x : X.obj (op n)) (f : m ⟶ n) :
      stdSimplex.map f ≫ yonedaEquiv.symm x =
        yonedaEquiv.symm (X.map f.op x) := by
  apply yonedaEquiv.injective
  conv_rhs => rw [Equiv.apply_symm_apply, ← Category.id_comp f]
  rfl

@[reassoc]
lemma stdSimplex.δ_comp_yonedaEquiv_symm {X : SSet.{u}} {n : ℕ} (i : Fin (n + 2))
    (x : X _⦋n + 1⦌) :
    stdSimplex.δ i ≫ yonedaEquiv.symm x = yonedaEquiv.symm (X.δ i x) := by
  apply stdSimplex.map_comp_yonedaEquiv_symm

@[reassoc]
lemma stdSimplex.σ_comp_yonedaEquiv_symm {X : SSet.{u}} {n : ℕ} (i : Fin (n + 2))
    (x : X _⦋n + 1⦌) :
    stdSimplex.σ i ≫ yonedaEquiv.symm x = yonedaEquiv.symm (X.σ i x) := by
  apply stdSimplex.map_comp_yonedaEquiv_symm

end SSet
