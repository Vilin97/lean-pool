/-
Copyright (c) 2026 Arthur Freitas Ramos, David Hulak, Ruy de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Hulak, Ruy de Queiroz
-/

import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.FreeGroup.Reduce
import LeanPool.FiniteGraphFundamentalGroup.Proof

/-!
# Consequences of the spanning-tree computation

This module exposes the free basis, rank identities, basepoint independence, and abelianization.
-/

open Set Function
open CategoryTheory CategoryTheory.SingleObj Quiver FreeGroup

noncomputable section

universe u

namespace FiniteGraphFreeGroup

/-!
# The reusable consequences of the spanning-tree computation

The proof file establishes the cardinality calculation and the free-group
equivalence required by the Palomar statement.  This file exposes the data
that is useful to downstream developments: the actual tree basis, basepoint
independence, the natural-number cycle-rank identities, and the abelianized
version of the computation.
-/

/-- The finite index type used to enumerate the non-tree edges. -/
noncomputable def graphCycleBasisIndexEquiv {V : Type u} [Quiver.{u} V]
    [Fintype V] [FiniteQuiver V] [WeaklyConnected V] (root : V) :
    graphGeneratorSet root ≃ Fin (cycleRank (V := V)) := by
  change graphGeneratorSet root ≃
    Fin (edgeCount (V := V) + 1 - vertexCount (V := V))
  exact (graphGeneratorSet_card root) ▸ Fintype.equivFin (graphGeneratorSet root)

/--
The spanning-tree basis of the graph fundamental group.

Its index is the complement of the certified geodesic tree, so the basis
remembers which graph edges create the independent cycles rather than merely
asserting that some free basis exists.
-/
noncomputable def graphFundamentalGroupBasis {V : Type u} [Quiver.{u} V]
    [WeaklyConnected V] (root : V) :
    FreeGroupBasis (graphGeneratorSet root) (graphFundamentalGroup root) := by
  simpa [graphGeneratorSet] using!
    (spanningTreeBasis (graphTree root))

theorem graphFundamentalGroupBasis_repr_apply {V : Type u} [Quiver.{u} V]
    [WeaklyConnected V] (root : V)
    (e : graphGeneratorSet root) :
    (graphFundamentalGroupBasis root).repr ((graphFundamentalGroupBasis root) e) =
      FreeGroup.of e :=
  FreeGroupBasis.repr_apply_coe _ _

/-- An explicit equivalence, not just a `Nonempty` existence statement. -/
noncomputable def graphFundamentalGroupEquiv {V : Type u} [Quiver.{u} V]
    [Fintype V] [FiniteQuiver V] [WeaklyConnected V] (root : V) :
    graphFundamentalGroup root ≃* FreeGroup (Fin (cycleRank (V := V))) := by
  exact (graphFundamentalGroupBasis root).reindex
    (graphCycleBasisIndexEquiv root) |>.repr

/--
Changing the root produces a group equivalence.  This is the concrete
basepoint-independence statement available for the combinatorial model; no
topological realization is being silently invoked.
-/
noncomputable def graphFundamentalGroupRootEquiv {V : Type u} [Quiver.{u} V]
    [Fintype V] [FiniteQuiver V] [WeaklyConnected V]
    (root₁ root₂ : V) :
    graphFundamentalGroup root₁ ≃* graphFundamentalGroup root₂ :=
  (graphFundamentalGroupEquiv root₁).trans (graphFundamentalGroupEquiv root₂).symm

@[simp]
theorem graphFundamentalGroupRootEquiv_refl {V : Type u} [Quiver.{u} V]
    [Fintype V] [FiniteQuiver V] [WeaklyConnected V] (root : V) :
    graphFundamentalGroupRootEquiv root root = MulEquiv.refl _ := by
  simp [graphFundamentalGroupRootEquiv]

/-- The geodesic tree has `V - 1` edges and therefore cannot exceed the edge set. -/
theorem graph_tree_edge_count_le {V : Type u} [Quiver.{u} V]
    [Fintype V] [FiniteQuiver V] [WeaklyConnected V] (root : V) :
    vertexCount (V := V) - 1 ≤ edgeCount (V := V) := by
  classical
  let G := IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)
  let T := graphTree root
  let S : Set (Quiver.Total G) :=
    wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T)
  have hGcard : Fintype.card G = Fintype.card V :=
    Fintype.card_congr generatorObjEquiv
  have hS : Fintype.card S = Fintype.card V - 1 := by
    have hS' := symmetrified_tree_set_card T
    rw [hGcard] at hS'
    simpa [S, T] using hS'
  have htotal : Fintype.card (Quiver.Total G) = Fintype.card (Quiver.Total V) :=
    Fintype.card_congr generatorTotalEquiv
  have hle : Fintype.card S ≤ Fintype.card (Quiver.Total G) :=
    Fintype.card_subtype_le _
  change Fintype.card V - 1 ≤ Fintype.card (Quiver.Total V)
  rw [← hS, ← htotal]
  exact hle

/-! This identity is the usual `E - (V - 1)` formula, expressed in `ℕ`. -/
theorem cycleRank_eq_edgeCount_sub_tree {V : Type u} [Quiver.{u} V]
    [Fintype V] [FiniteQuiver V] [WeaklyConnected V] (root : V) :
    cycleRank (V := V) = edgeCount (V := V) - (vertexCount (V := V) - 1) := by
  have htree := graph_tree_edge_count_le root
  have hVpos : 1 ≤ vertexCount (V := V) := Fintype.card_pos_iff.mpr ⟨root⟩
  change edgeCount (V := V) + 1 - vertexCount (V := V) =
    edgeCount (V := V) - (vertexCount (V := V) - 1)
  omega

theorem cycleRank_pos_iff {V : Type u} [Quiver.{u} V]
    [Fintype V] [FiniteQuiver V] [WeaklyConnected V] (root : V) :
    0 < cycleRank (V := V) ↔
      vertexCount (V := V) - 1 < edgeCount (V := V) := by
  have htree := graph_tree_edge_count_le root
  rw [cycleRank_eq_edgeCount_sub_tree root]
  omega

theorem cycleRank_eq_zero_iff_tree_edge_count {V : Type u} [Quiver.{u} V]
    [Fintype V] [FiniteQuiver V] [WeaklyConnected V] (root : V) :
    cycleRank (V := V) = 0 ↔
      edgeCount (V := V) = vertexCount (V := V) - 1 := by
  have htree := graph_tree_edge_count_le root
  rw [cycleRank_eq_edgeCount_sub_tree root]
  omega

/-- The combinatorial fundamental group is trivial exactly in the tree case. -/
theorem graphFundamentalGroup_subsingleton_iff_cycleRank_zero
    {V : Type u} [Quiver.{u} V] [Fintype V] [FiniteQuiver V]
    [WeaklyConnected V] (root : V) :
    Subsingleton (graphFundamentalGroup root) ↔ cycleRank (V := V) = 0 := by
  constructor
  · intro h
    by_contra hzero
    have hpos : 0 < cycleRank (V := V) := Nat.pos_of_ne_zero hzero
    let e := graphFundamentalGroupEquiv root
    let i : Fin (cycleRank (V := V)) := ⟨0, hpos⟩
    have hne : FreeGroup.of i ≠ (1 : FreeGroup (Fin (cycleRank (V := V)))) :=
      of_ne_one i
    apply hne
    have heq := h.elim (e.symm (FreeGroup.of i)) (e.symm 1)
    calc
      FreeGroup.of i = e (e.symm (FreeGroup.of i)) := (e.apply_symm_apply _).symm
      _ = e (e.symm 1) := congrArg e heq
      _ = 1 := e.apply_symm_apply _
  · intro hzero
    constructor
    intro x y
    have hfree : Subsingleton (FreeGroup (Fin (cycleRank (V := V)))) := by
      rw [hzero]
      infer_instance
    let e := graphFundamentalGroupEquiv root
    apply e.injective
    exact hfree.elim _ _

/-- Abelianization preserves the explicitly computed rank. -/
noncomputable def graphFundamentalGroupAbelianizationEquiv
    {V : Type u} [Quiver.{u} V] [Fintype V] [FiniteQuiver V]
    [WeaklyConnected V] (root : V) :
    Abelianization (graphFundamentalGroup root) ≃*
      Abelianization (FreeGroup (Fin (cycleRank (V := V)))) :=
  (graphFundamentalGroupEquiv root).abelianizationCongr

/-- The additive free-abelian form of the same consequence. -/
noncomputable def graphFundamentalGroupFreeAbelianizationEquiv
    {V : Type u} [Quiver.{u} V] [Fintype V] [FiniteQuiver V]
    [WeaklyConnected V] (root : V) :
    Additive (Abelianization (graphFundamentalGroup root)) ≃+
      FreeAbelianGroup (Fin (cycleRank (V := V))) :=
  MulEquiv.toAdditive (graphFundamentalGroupAbelianizationEquiv root)

end FiniteGraphFreeGroup
