/-
Copyright (c) 2026 Arthur Freitas Ramos, David Hulak, Ruy de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Hulak, Ruy de Queiroz
-/

import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Combinatorics.Quiver.Arborescence
import LeanPool.FiniteGraphFundamentalGroup.Realization

/-!
# Contraction of a directed tree realization

This module constructs cellwise contraction data from the unique paths in an arborescence.
-/

open Set Function
open CategoryTheory CategoryTheory.SingleObj Quiver
open unitInterval

noncomputable section

universe u

namespace FiniteGraphFreeGroup

/-!
# Contraction data for a directed tree realization

This file isolates the geometric part of the eventual graph comparison theorem.
For an arborescence, every vertex has a unique directed path from the root.  The
cellwise formula below contracts each edge along that root path.  The formula is
the usual square filling of a concatenated path:

`(t, s) ↦ p ((1 - s) * (1 + t) / 2)`.

The horizontal boundary is the edge, while the two vertical boundaries are the
contractions of its endpoints.
-/

section

variable {V : Type u} [Quiver.{u} V] [Quiver.Arborescence V]

/-- The path in the realization associated to a directed quiver path. -/
def graphRealizationDirectedPath {a b : V} (p : Quiver.Path a b) :
    Path (graphVertex a) (graphVertex b) := by
  induction p with
  | nil => exact Path.refl _
  | cons p e ih => exact ih.trans (graphRealizationForwardPath e)

/-- The unique root path in the realization of an arborescence. -/
noncomputable def graphTreeRootPath (b : V) :
    Path (graphVertex (Quiver.root V)) (graphVertex b) :=
  graphRealizationDirectedPath
    (default : Quiver.Path (Quiver.root V) b)

theorem graphTreeRootPath_cons {a b : V} (e : a ⟶ b) :
    graphTreeRootPath b =
      (graphTreeRootPath a).trans (graphRealizationForwardPath e) := by
  have h :
      (default : Quiver.Path (Quiver.root V) b) =
        (default : Quiver.Path (Quiver.root V) a).cons e :=
    Subsingleton.elim _ _
  unfold graphTreeRootPath
  rw [h]
  rfl

private def treeContractionCoordinate (t s : I) : I :=
  ⟨(1 - (s : ℝ)) * ((1 + (t : ℝ)) / 2), by
    have hs : 0 ≤ 1 - (s : ℝ) := by linarith [s.2.2]
    have hs' : 1 - (s : ℝ) ≤ 1 := by linarith [s.2.1]
    have ht : 0 ≤ (1 + (t : ℝ)) / 2 := by linarith [t.2.1]
    have ht' : (1 + (t : ℝ)) / 2 ≤ 1 := by linarith [t.2.2]
    constructor
    · exact mul_nonneg hs ht
    · calc
        (1 - (s : ℝ)) * ((1 + (t : ℝ)) / 2) ≤
            1 * ((1 + (t : ℝ)) / 2) := mul_le_mul_of_nonneg_right hs' ht
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left ht' (by norm_num)
        _ = 1 := by norm_num
  ⟩

private theorem continuous_treeContractionCoordinate :
    Continuous (fun p : I × I => treeContractionCoordinate p.1 p.2) := by
  apply Continuous.subtype_mk
  fun_prop

@[simp]
theorem treeContractionCoordinate_zero_right (t : I) :
    treeContractionCoordinate t 0 = ⟨(1 + (t : ℝ)) / 2, by
      constructor <;> nlinarith [t.2.1, t.2.2]⟩ := by
  apply Subtype.ext
  simp [treeContractionCoordinate]

@[simp]
theorem treeContractionCoordinate_zero_left (s : I) :
    treeContractionCoordinate 0 s = ⟨(1 - (s : ℝ)) / 2, by
      constructor <;> nlinarith [s.2.1, s.2.2]⟩ := by
  apply Subtype.ext
  simp [treeContractionCoordinate]
  ring

@[simp]
theorem treeContractionCoordinate_one_left (s : I) :
    treeContractionCoordinate 1 s = ⟨1 - (s : ℝ), by
      constructor <;> nlinarith [s.2.1, s.2.2]⟩ := by
  apply Subtype.ext
  simp [treeContractionCoordinate]

@[simp]
theorem treeContractionCoordinate_one_right (t : I) :
    treeContractionCoordinate t 1 = 0 := by
  apply Subtype.ext
  simp [treeContractionCoordinate]

/-- The square which contracts the cell of an edge towards the root. -/
def graphTreeEdgeContraction (e : Quiver.Total V) : C(I × I, graphRealization V) where
  toFun p := graphTreeRootPath e.right (treeContractionCoordinate p.1 p.2)
  continuous_toFun :=
    (graphTreeRootPath e.right).continuous.comp continuous_treeContractionCoordinate

/-- The path which contracts a vertex of the tree to the root. -/
def graphTreeVertexContraction (v : V) : C(I, graphRealization V) :=
  (graphTreeRootPath v).symm.toContinuousMap

@[simp]
theorem graphTreeVertexContraction_apply (v : V) (s : I) :
    graphTreeVertexContraction v s = graphTreeRootPath v (σ s) := by
  rfl

@[simp]
theorem graphTreeEdgeContraction_zero_right (e : Quiver.Total V) (t : I) :
    graphTreeEdgeContraction e (t, 0) = graphEdgePath e t := by
  change graphTreeRootPath e.right (treeContractionCoordinate t 0) = graphEdgePath e t
  rw [graphTreeRootPath_cons e.hom, Path.trans_apply]
  by_cases ht : t = 0
  · subst t
    simp [treeContractionCoordinate]
  · have h : ¬(treeContractionCoordinate t 0 : ℝ) ≤ 1 / 2 := by
      rw [treeContractionCoordinate_zero_right]
      norm_num
      have ht_ne : (t : ℝ) ≠ 0 := by
        intro hzero
        apply ht
        apply Subtype.ext
        exact hzero
      have ht_pos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht_ne)
      linarith
    rw [dite_eq_right h]
    change graphEdgePath e _ = graphEdgePath e t
    apply congrArg (graphEdgePath e)
    apply Subtype.ext
    change 2 * (treeContractionCoordinate t 0 : ℝ) - 1 = (t : ℝ)
    rw [treeContractionCoordinate_zero_right]
    ring

@[simp]
theorem graphTreeEdgeContraction_zero_left (e : Quiver.Total V) (s : I) :
    graphTreeEdgeContraction e (0, s) = graphTreeVertexContraction e.left s := by
  change graphTreeRootPath e.right (treeContractionCoordinate 0 s) =
    graphTreeRootPath e.left (σ s)
  rw [graphTreeRootPath_cons e.hom, Path.trans_apply]
  have h : (treeContractionCoordinate 0 s : ℝ) ≤ 1 / 2 := by
    rw [treeContractionCoordinate_zero_left]
    norm_num
    linarith [s.2.1]
  simp only [dite_eq_left h]
  apply congrArg (graphTreeRootPath e.left)
  apply Subtype.ext
  change 2 * (treeContractionCoordinate 0 s : ℝ) = (σ s : ℝ)
  rw [treeContractionCoordinate_zero_left]
  norm_num [unitInterval.coe_symm_eq]
  ring

@[simp]
theorem graphTreeEdgeContraction_one_left (e : Quiver.Total V) (s : I) :
    graphTreeEdgeContraction e (1, s) = graphTreeVertexContraction e.right s := by
  change graphTreeRootPath e.right (treeContractionCoordinate 1 s) =
    graphTreeRootPath e.right (σ s)
  rw [treeContractionCoordinate_one_left]
  congr 1

@[simp]
theorem graphTreeEdgeContraction_one_right (e : Quiver.Total V) (t : I) :
    graphTreeEdgeContraction e (t, 1) = graphVertex (Quiver.root V) := by
  change graphTreeRootPath e.right (treeContractionCoordinate t 1) =
    graphVertex (Quiver.root V)
  rw [treeContractionCoordinate_one_right]
  exact (graphTreeRootPath e.right).source

section QuotientContraction

/-! The cellwise squares agree on the endpoint generators, so the quotient
    universal property turns them into a global homotopy. -/

/-- The continuously parameterized contraction paths assigned to tree vertices. -/
def graphTreeVertexFamily :
    C(WithDiscreteTopology V, C(I, graphRealization V)) where
  toFun v := graphTreeVertexContraction (graphVertexUnderlying v)
  continuous_toFun := continuous_of_discreteTopology

/-- The continuously parameterized contraction squares assigned to tree edges. -/
def graphTreeEdgeFamily :
    C((Σ _e : WithDiscreteTopology (Quiver.Total V), I),
      C(I, graphRealization V)) where
  toFun e := ContinuousMap.curry
    (graphTreeEdgeContraction (graphEdgeUnderlying e.1)) e.2
  continuous_toFun := by
    apply continuous_sigma
    intro e
    exact (ContinuousMap.curry
      (graphTreeEdgeContraction (graphEdgeUnderlying e))).continuous

/-- The uncurried vertex part of the tree contraction. -/
def graphTreeVertexFamilyUncurry :
    C(WithDiscreteTopology V × I, graphRealization V) :=
  ContinuousMap.uncurry graphTreeVertexFamily

/-- The uncurried edge part of the tree contraction. -/
def graphTreeEdgeFamilyUncurry :
    C((Σ _e : WithDiscreteTopology (Quiver.Total V), I) × I,
      graphRealization V) :=
  ContinuousMap.uncurry graphTreeEdgeFamily

/-- The sum of the cellwise vertex and edge contractions before quotienting. -/
def graphTreeContractionPieces :
    C((WithDiscreteTopology V × I) ⊕
      ((Σ _e : WithDiscreteTopology (Quiver.Total V), I) × I),
      graphRealization V) where
  toFun := Sum.elim graphTreeVertexFamilyUncurry graphTreeEdgeFamilyUncurry
  continuous_toFun := continuous_sumElim.2 ⟨
    graphTreeVertexFamilyUncurry.continuous,
    graphTreeEdgeFamilyUncurry.continuous⟩

/-- The cellwise contraction before descending to the endpoint quotient. -/
def graphTreeContractionPre :
    C(graphRealizationPre V × I, graphRealization V) := by
  let pieces := graphTreeContractionPieces (V := V)
  let distribute := Homeomorph.sumProdDistrib
    (X := WithDiscreteTopology V)
    (Y := Σ _e : WithDiscreteTopology (Quiver.Total V), I)
    (Z := I)
  exact pieces.comp ⟨distribute, distribute.continuous⟩

@[simp]
theorem graphTreeContractionPre_vertex
    (v : WithDiscreteTopology V) (s : I) :
    graphTreeContractionPre (Sum.inl v, s) =
      graphTreeVertexContraction (graphVertexUnderlying v) s := by
  simp [graphTreeContractionPre, graphTreeContractionPieces,
    graphTreeVertexFamilyUncurry, graphTreeVertexFamily]

@[simp]
theorem graphTreeContractionPre_edge
    (e : WithDiscreteTopology (Quiver.Total V)) (t s : I) :
    graphTreeContractionPre (Sum.inr ⟨e, t⟩, s) =
      graphTreeEdgeContraction (graphEdgeUnderlying e) (t, s) := by
  simp [graphTreeContractionPre, graphTreeContractionPieces,
    graphTreeEdgeFamilyUncurry, graphTreeEdgeFamily]

theorem graphTreeContractionPre_respects
    {x y : graphRealizationPre V}
    (h : Relation.EqvGen (graphRealizationGenerator (V := V)) x y) (s : I) :
    graphTreeContractionPre (x, s) = graphTreeContractionPre (y, s) := by
  induction h with
  | rel x y h =>
      cases h with
      | source e =>
          simp [graphTreeContractionPre_edge, graphTreeContractionPre_vertex,
            graphTreeEdgeContraction_zero_left]
      | target e =>
          simp [graphTreeContractionPre_edge, graphTreeContractionPre_vertex,
            graphTreeEdgeContraction_one_left]
  | refl x => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

/-- The cellwise contraction descended through the endpoint quotient. -/
def graphTreeContraction :
    C(graphRealization V × I, graphRealization V) := by
  let f : graphRealization V × I → graphRealization V := fun z =>
    Quotient.lift (fun x => graphTreeContractionPre (x, z.2))
      (fun x y h => graphTreeContractionPre_respects h z.2) z.1
  refine { toFun := f, continuous_toFun := ?_ }
  apply isQuotientMap_quotient_mk'.continuous_lift_prod_left
  have hcomp : (fun p : graphRealizationPre V × I =>
      f (graphRealizationQuotient p.1, p.2)) =
      (graphTreeContractionPre (V := V) : graphRealizationPre V × I →
        graphRealization V) := by
    funext p
    rfl
  rw [hcomp]
  exact (graphTreeContractionPre (V := V)).continuous

@[simp]
theorem graphTreeContraction_quotient
    (x : graphRealizationPre V) (s : I) :
    graphTreeContraction (graphRealizationQuotient x, s) =
      graphTreeContractionPre (x, s) := by
  change Quotient.lift (fun y => graphTreeContractionPre (y, s))
      (fun y z h => graphTreeContractionPre_respects h s) (Quotient.mk' x) =
    graphTreeContractionPre (x, s)
  exact Quotient.lift_mk _ _ _

@[simp]
theorem graphTreeContraction_vertex
    (v : WithDiscreteTopology V) (s : I) :
    graphTreeContraction (graphVertex (graphVertexUnderlying v), s) =
      graphTreeVertexContraction (graphVertexUnderlying v) s := by
  change graphTreeContraction (graphRealizationQuotient (Sum.inl v), s) = _
  rw [graphTreeContraction_quotient]
  exact graphTreeContractionPre_vertex v s

theorem graphTreeContraction_edge
    (e : WithDiscreteTopology (Quiver.Total V)) (t s : I) :
    graphTreeContraction
        (graphRealizationQuotient (Sum.inr ⟨e, t⟩), s) =
      graphTreeEdgeContraction (graphEdgeUnderlying e) (t, s) := by
  rw [graphTreeContraction_quotient]
  exact graphTreeContractionPre_edge e t s

theorem graphTreeContraction_zero (x : graphRealization V) :
    graphTreeContraction (x, 0) = x := by
  refine Quotient.inductionOn x ?_
  intro x
  cases x with
  | inl v =>
      change graphTreeContraction
          (graphRealizationQuotient (Sum.inl v), 0) =
        graphRealizationQuotient (Sum.inl v)
      rw [graphTreeContraction_quotient, graphTreeContractionPre_vertex]
      change graphTreeRootPath (graphVertexUnderlying v) (σ 0) =
        graphRealizationQuotient (Sum.inl v)
      rw [show σ (0 : I) = 1 by simp]
      exact (graphTreeRootPath (graphVertexUnderlying v)).target.trans rfl
  | inr z =>
      rcases z with ⟨e, t⟩
      change graphTreeContraction
          (graphRealizationQuotient (Sum.inr ⟨e, t⟩), 0) =
        graphRealizationQuotient (Sum.inr ⟨e, t⟩)
      rw [graphTreeContraction_quotient, graphTreeContractionPre_edge,
        graphTreeEdgeContraction_zero_right]
      rfl

theorem graphTreeContraction_one (x : graphRealization V) :
    graphTreeContraction (x, 1) = graphVertex (Quiver.root V) := by
  refine Quotient.inductionOn x ?_
  intro x
  cases x with
  | inl v =>
      change graphTreeContraction
          (graphRealizationQuotient (Sum.inl v), 1) =
        graphVertex (Quiver.root V)
      rw [graphTreeContraction_quotient, graphTreeContractionPre_vertex]
      change graphTreeRootPath (graphVertexUnderlying v) (σ 1) =
        graphVertex (Quiver.root V)
      rw [show σ (1 : I) = 0 by simp]
      exact (graphTreeRootPath (graphVertexUnderlying v)).source
  | inr z =>
      rcases z with ⟨e, t⟩
      change graphTreeContraction
          (graphRealizationQuotient (Sum.inr ⟨e, t⟩), 1) =
        graphVertex (Quiver.root V)
      rw [graphTreeContraction_quotient, graphTreeContractionPre_edge,
        graphTreeEdgeContraction_one_right]

/-- An arborescence realization is contractible. -/
noncomputable instance graphRealization_contractible :
    ContractibleSpace (graphRealization V) where
  hequiv_unit' := by
    let rootPoint : graphRealization V := graphVertex (Quiver.root V)
    let reverseContraction : C(I × graphRealization V, graphRealization V) := {
      toFun p := graphTreeContraction (p.2, σ p.1)
      continuous_toFun := by
        exact (graphTreeContraction (V := V)).continuous.comp (by fun_prop) }
    refine ⟨{
      toFun := ContinuousMap.const _ (),
      invFun := ContinuousMap.const _ rootPoint,
      left_inv := ?_,
      right_inv := ?_ }⟩
    · exact ⟨{
        toFun := reverseContraction,
        map_zero_left := by
          intro x
          simpa [reverseContraction, rootPoint] using graphTreeContraction_one x,
        map_one_left := by
          intro x
          simpa [reverseContraction] using graphTreeContraction_zero x }⟩
    · have hcomp :
          (ContinuousMap.const (graphRealization V) ()).comp
              (ContinuousMap.const Unit rootPoint) =
            ContinuousMap.id Unit := by
        ext x
      rw [hcomp]

end QuotientContraction

theorem graphRealization_tree_simplyConnected :
    SimplyConnectedSpace (graphRealization V) := by
  infer_instance

end

end FiniteGraphFreeGroup
