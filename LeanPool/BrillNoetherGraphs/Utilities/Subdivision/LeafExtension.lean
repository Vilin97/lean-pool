/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Gonality.DivisorialGonality
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.RankOne

/-!
# Divisor rank under adjoining a leaf

This module isolates the pendant-tree reduction needed before a finite stable
core classification.  The graph `addLeaf H root` adjoins one new vertex and a
single edge from it to `root`.  Divisors extend by zero to the new leaf, while
divisors on the extension retract by moving the leaf coefficient to `root`.
These operations preserve degree, linear equivalence, winnability, and rank.

The resulting rank-one interface shows that adjoining or pruning a leaf does
not change divisorial gonality.
-/

namespace Utilities.Certificate

open Multiset Finset
open Utilities.Gonality

universe u

namespace LeafExtension

variable (H : CFGraph.{u}) (root : H.V)

private def liftEdge (edge : H.V × H.V) : Option H.V × Option H.V :=
  (some edge.1, some edge.2)

/-- Adjoin a new leaf `none` to the old vertex `some root`. -/
def addLeaf : CFGraph where
  V := Option H.V
  edges := (none, some root) ::ₘ H.edges.map (liftEdge H)
  loopless := by
    intro vertex hmem
    simp only [Multiset.mem_cons, Multiset.mem_map] at hmem
    rcases hmem with hnew | ⟨edge, hedge, hEq⟩
    · cases vertex <;> simp [Option.some.injEq] at hnew
    · rcases edge with ⟨x, y⟩
      cases vertex with
      | none => simp [liftEdge] at hEq
      | some vertex =>
          simp only [liftEdge, Prod.mk.injEq, Option.some.injEq] at hEq
          rcases hEq with ⟨hx, hy⟩
          subst x
          subst y
          exact H.loopless _ hedge

@[simp] theorem addLeaf_edges :
    (addLeaf H root).edges =
      (none, some root) ::ₘ H.edges.map (liftEdge H) := rfl

private theorem filter_map_liftEdge_some_some
    (edges : Multiset (H.V × H.V)) (x y : H.V) :
    (edges.map (liftEdge H)).filter
        (fun edge =>
          edge = (some x, some y) ∨ edge = (some y, some x)) =
      (edges.filter
        (fun edge => edge = (x, y) ∨ edge = (y, x))).map (liftEdge H) := by
  induction edges using Multiset.induction_on with
  | empty => simp
  | cons edge edges ih =>
      rcases edge with ⟨a, b⟩
      have hiff :
          liftEdge H (a, b) = (some x, some y) ∨
              liftEdge H (a, b) = (some y, some x) ↔
            (a, b) = (x, y) ∨ (a, b) = (y, x) := by
        simp [liftEdge, Prod.ext_iff]
      rw [Multiset.map_cons, Multiset.filter_cons,
        Multiset.filter_cons, Multiset.map_add, ih]
      by_cases h : (a, b) = (x, y) ∨ (a, b) = (y, x)
      · rw [if_pos h, if_pos (hiff.mpr h)]
        simp
      · rw [if_neg h, if_neg (mt hiff.mp h)]
        simp

private theorem filter_map_liftEdge_none_some
    (edges : Multiset (H.V × H.V)) (x : H.V) :
    (edges.map (liftEdge H)).filter
        (fun edge => edge = (none, some x) ∨ edge = (some x, none)) = 0 := by
  induction edges using Multiset.induction_on with
  | empty => simp
  | cons edge edges ih =>
      rcases edge with ⟨a, b⟩
      rw [Multiset.map_cons, Multiset.filter_cons, ih]
      simp [liftEdge]

/-- Old-old edge multiplicities are unchanged. -/
@[simp] theorem num_edges_some_some (x y : H.V) :
    num_edges (addLeaf H root) (some x) (some y) = num_edges H x y := by
  change
    (((none, some root) ::ₘ H.edges.map (liftEdge H)).filter
      (fun edge =>
        edge = (some x, some y) ∨ edge = (some y, some x))).card =
      (H.edges.filter
        (fun edge => edge = (x, y) ∨ edge = (y, x))).card
  rw [Multiset.filter_cons]
  have hnew :
      ¬((none, some root) = (some x, some y) ∨
        (none, some root) = (some y, some x)) := by simp
  rw [if_neg hnew]
  rw [filter_map_liftEdge_some_some]
  simp

/-- The new leaf has one edge to `root` and none to another old vertex. -/
@[simp] theorem num_edges_none_some (x : H.V) :
    num_edges (addLeaf H root) none (some x) = if x = root then 1 else 0 := by
  change
    (((none, some root) ::ₘ H.edges.map (liftEdge H)).filter
      (fun edge =>
        edge = (none, some x) ∨ edge = (some x, none))).card =
      if x = root then 1 else 0
  rw [Multiset.filter_cons, filter_map_liftEdge_none_some]
  by_cases hx : x = root
  · subst x
    simp
  · simp [hx, Ne.symm hx]

-- Mathlib v4.33 flips `backward.isDefEq.respectTransparency` to `true` by
-- default (see `Init/MetaTypes.lean`), so `rw`/`simp` no longer bump
-- instance-implicit unification to `default` transparency and can't see
-- through the semireducible `addLeaf` to identify `Option H.V` with
-- `(addLeaf H root).V`. Lean core itself works around this the same way in
-- several library files (e.g. `Init/Data/List/Lemmas.lean`): disable the
-- flag locally for these `addLeaf`-typed lemmas.
@[simp] theorem num_edges_some_none (x : H.V) :
    num_edges (addLeaf H root) (some x) none = if x = root then 1 else 0 := by
  rw [num_edges_symmetric]
  exact num_edges_none_some H root x

/-- Adjoining one vertex and one edge preserves genus. -/
@[simp] theorem genus_addLeaf : genus (addLeaf H root) = genus H := by
  change
    ((↑(((none, some root) ::ₘ H.edges.map (liftEdge H)).card) : ℤ) -
        ↑(Fintype.card (Option H.V)) + 1) =
      ↑H.edges.card - ↑(Fintype.card H.V) + 1
  simp

/-- A connected graph remains connected after adjoining a leaf. -/
theorem graph_connected_addLeaf (hH : graph_connected H) :
    graph_connected (addLeaf H root) := by
  change ∀ S : Finset (Option H.V),
    (∃ v w : Option H.V, v ∈ S ∧ w ∉ S) →
      ∃ v ∈ S, ∃ w ∉ S,
        num_edges (addLeaf H root) v w > 0
  intro S hS
  by_cases hOldCut :
      ∃ x y : H.V, some x ∈ S ∧ some y ∉ S
  · let oldS : Finset H.V := Finset.univ.filter fun x => some x ∈ S
    have hOldS : ∃ x y : H.V, x ∈ oldS ∧ y ∉ oldS := by
      obtain ⟨x, y, hx, hy⟩ := hOldCut
      exact ⟨x, y, by simpa [oldS] using hx, by simpa [oldS] using hy⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hH oldS hOldS
    refine ⟨some x, ?_, some y, ?_, ?_⟩
    · simpa [oldS] using hx
    · simpa [oldS] using hy
    · simpa using hxy
  · by_cases hRoot : some root ∈ S
    · have hAllOld : ∀ x : H.V, some x ∈ S := by
        intro x
        by_contra hx
        exact hOldCut ⟨root, x, hRoot, hx⟩
      have hLeaf : none ∉ S := by
        intro hNone
        obtain ⟨v, w, hv, hw⟩ := hS
        cases w with
        | none => exact hw hNone
        | some x => exact hw (hAllOld x)
      exact ⟨some root, hRoot, none, hLeaf, by simp⟩
    · have hNoOld : ∀ x : H.V, some x ∉ S := by
        intro x hx
        exact hOldCut ⟨x, root, hx, hRoot⟩
      have hLeaf : none ∈ S := by
        by_contra hNone
        obtain ⟨v, w, hv, _hw⟩ := hS
        cases v with
        | none => exact hNone hv
        | some x => exact hNoOld x hv
      exact ⟨none, hLeaf, some root, hRoot, by simp⟩

/-- Extend an old divisor by zero at the new leaf. -/
def extendDiv (D : CFDiv H) : CFDiv (addLeaf H root)
  | none => 0
  | some x => D x

/-- Extend a firing script constantly across the new leaf edge. -/
def extendScript (script : firing_script H) : firing_script (addLeaf H root)
  | none => script root
  | some x => script x

@[simp] theorem extendDiv_none (D : CFDiv H) :
    extendDiv H root D none = 0 := rfl

@[simp] theorem extendDiv_some (D : CFDiv H) (x : H.V) :
    extendDiv H root D (some x) = D x := rfl

@[simp] theorem extendScript_none (script : firing_script H) :
    extendScript H root script none = script root := rfl

@[simp] theorem extendScript_some (script : firing_script H) (x : H.V) :
    extendScript H root script (some x) = script x := rfl

@[simp] theorem extendDiv_zero :
    extendDiv H root (0 : CFDiv H) = 0 := by
  funext vertex
  cases vertex <;> rfl

@[simp] theorem extendDiv_add (D E : CFDiv H) :
    extendDiv H root (D + E) = extendDiv H root D + extendDiv H root E := by
  funext vertex
  cases vertex <;> rfl

@[simp] theorem extendDiv_sub (D E : CFDiv H) :
    extendDiv H root (D - E) = extendDiv H root D - extendDiv H root E := by
  funext vertex
  cases vertex <;> rfl

-- See the comment above `num_edges_some_none` for why this override is
-- needed (Mathlib v4.33): the `DecidableEq (addLeaf H root).V` instance used
-- by `one_chip`'s `if` needs to be identified with the canonical
-- `DecidableEq (Option H.V)` instance, which requires unfolding the
-- semireducible `addLeaf`.
@[simp] theorem extendDiv_one_chip (x : H.V) :
    extendDiv H root (one_chip x) =
      one_chip (G := addLeaf H root) (some x) := by
  funext vertex
  cases vertex with
  | none => simp [extendDiv, one_chip]
  | some y =>
      by_cases hy : y = x
      · subst y
        simp [extendDiv, one_chip]
      · have hSome : (some y : Option H.V) ≠ some x := by
          exact fun h => hy (Option.some.inj h)
        change (if y = x then 1 else 0) =
          if (some y : Option H.V) = some x then 1 else 0
        rw [if_neg hy, if_neg hSome]

/-- Extending by zero preserves effectivity. -/
theorem effective_extendDiv {D : CFDiv H} (hD : effective D) :
    effective (extendDiv H root D) := by
  intro vertex
  cases vertex with
  | none => simp
  | some x => exact hD x

-- See the comment above `num_edges_some_none` for why this override is
-- needed (Mathlib v4.33).
/-- Extending by zero preserves divisor degree. -/
@[simp] theorem deg_extendDiv (D : CFDiv H) :
    deg (extendDiv H root D) = deg D := by
  change (∑ vertex : Option H.V, extendDiv H root D vertex) =
    ∑ x : H.V, D x
  rw [Fintype.sum_option]
  simp

/-- Constant extension of a firing script has zero Laplacian at the leaf and
the old Laplacian at every old vertex. -/
theorem extendDiv_prin (script : firing_script H) :
    extendDiv H root (prin H script) =
      prin (addLeaf H root) (extendScript H root script) := by
  funext vertex
  cases vertex with
  | none =>
      change 0 =
        ∑ neighbor : Option H.V,
          (extendScript H root script neighbor - script root) *
            (num_edges (addLeaf H root) none neighbor : ℤ)
      simp
  | some x =>
      change
        (∑ y : H.V, (script y - script x) * (num_edges H x y : ℤ)) =
        ∑ neighbor : Option H.V,
          (extendScript H root script neighbor - script x) *
            (num_edges (addLeaf H root) (some x) neighbor : ℤ)
      rw [Fintype.sum_option]
      by_cases hx : x = root
      · subst x
        simp
      · simp [hx]

/-- Linear equivalence transports from the old graph to its leaf extension. -/
theorem linearEquiv_extendDiv {D E : CFDiv H}
    (hEquiv : linear_equiv H D E) :
    linear_equiv (addLeaf H root)
      (extendDiv H root D) (extendDiv H root E) := by
  unfold linear_equiv at hEquiv ⊢
  rw [principal_iff_eq_prin] at hEquiv ⊢
  obtain ⟨script, hscript⟩ := hEquiv
  refine ⟨extendScript H root script, ?_⟩
  rw [← extendDiv_prin H root script, ← extendDiv_sub, hscript]

/-- A winnable old divisor stays winnable after extension by zero. -/
theorem winnable_extendDiv {D : CFDiv H} (hWin : winnable H D) :
    winnable (addLeaf H root) (extendDiv H root D) := by
  rw [winnable_iff_exists_effective] at hWin ⊢
  obtain ⟨E, hEffective, hEquiv⟩ := hWin
  exact ⟨extendDiv H root E, effective_extendDiv H root hEffective,
    linearEquiv_extendDiv H root hEquiv⟩

/-- Script which moves one removed-chip test from `root` to the new leaf. -/
def leafMoveScript : firing_script (addLeaf H root)
  | none => 1
  | some _ => 0

/-- The leaf-move script has principal divisor `root - leaf`. -/
private theorem prin_leafMoveScript_none :
    prin (addLeaf H root) (leafMoveScript H root) none = -1 := by
  change
    (∑ neighbor : Option H.V,
      (leafMoveScript H root neighbor - 1) *
        (num_edges (addLeaf H root) none neighbor : ℤ)) = -1
  rw [Fintype.sum_option]
  simp [leafMoveScript]

private theorem prin_leafMoveScript_some (x : H.V) :
    prin (addLeaf H root) (leafMoveScript H root) (some x) =
      if x = root then 1 else 0 := by
  change
    (∑ neighbor : Option H.V,
      (leafMoveScript H root neighbor - 0) *
        (num_edges (addLeaf H root) (some x) neighbor : ℤ)) =
      if x = root then 1 else 0
  rw [Fintype.sum_option]
  simp [leafMoveScript]

-- See the comment above `extendDiv_one_chip` for why this override is needed
-- (Mathlib v4.33).
theorem prin_leafMoveScript :
    prin (addLeaf H root) (leafMoveScript H root) =
      one_chip (some root) - one_chip none := by
  funext vertex
  cases vertex with
  | none =>
      rw [prin_leafMoveScript_none]
      simp [one_chip]
  | some x =>
      rw [prin_leafMoveScript_some]
      by_cases hx : x = root
      · subst x
        simp [one_chip]
      · have hSome : (some x : Option H.V) ≠ some root := by
          exact fun h => hx (Option.some.inj h)
        simp only [Pi.sub_apply, one_chip]
        change (if x = root then 1 else 0) =
          (if (some x : Option H.V) = some root then 1 else 0) -
            (if (some x : Option H.V) = none then 1 else 0)
        rw [if_neg hx, if_neg hSome, if_neg (by simp)]
        norm_num

/-- Removing a chip at the old root or at the new leaf gives linearly
equivalent divisors on the leaf extension. -/
theorem sub_root_linearEquiv_sub_leaf (D : CFDiv H) :
    linear_equiv (addLeaf H root)
      (extendDiv H root D - one_chip (some root))
      (extendDiv H root D - one_chip none) := by
  unfold linear_equiv
  rw [principal_iff_eq_prin]
  refine ⟨leafMoveScript H root, ?_⟩
  rw [prin_leafMoveScript]
  abel

/-- Rank-one lower bounds survive adjoining a leaf. -/
theorem rank_ge_one_addLeaf {D : CFDiv H} (hRank : rank H D ≥ 1) :
    rank (addLeaf H root) (extendDiv H root D) ≥ 1 := by
  apply (rank_geq_iff (addLeaf H root) (extendDiv H root D) 1).mp
  intro E hE
  obtain ⟨vertex, rfl⟩ :=
    effective_degree_one_eq_one_chip hE.1 hE.2
  cases vertex with
  | some x =>
      have hOld :=
        (rank_geq_iff H D 1).mpr hRank
          (one_chip x) ⟨eff_one_chip x, deg_one_chip x⟩
      have hExtended := winnable_extendDiv H root hOld
      simpa using hExtended
  | none =>
      have hOld :=
        (rank_geq_iff H D 1).mpr hRank
          (one_chip root) ⟨eff_one_chip root, deg_one_chip root⟩
      have hExtended := winnable_extendDiv H root hOld
      have hLinear := sub_root_linearEquiv_sub_leaf H root D
      exact winnable_equiv_winnable (addLeaf H root) _ _
        (by simpa using hExtended) hLinear

/-- A degree-`d`, rank-one divisor remains such after adjoining a leaf. -/
theorem bnExists_rank_one_addLeaf {d : ℤ} :
    BNExists H 1 d → BNExists (addLeaf H root) 1 d := by
  rintro ⟨D, hDegree, hRank⟩
  exact ⟨extendDiv H root D, by simpa using hDegree,
    rank_ge_one_addLeaf H root hRank⟩

/-! ## Retracting the added leaf -/

/-- Move the coefficient at the new leaf into its old neighbour. -/
def retractDiv (E : CFDiv (addLeaf H root)) : CFDiv H :=
  fun x => E (some x) + if x = root then E none else 0

@[simp] theorem retractDiv_apply (E : CFDiv (addLeaf H root)) (x : H.V) :
    retractDiv H root E x = E (some x) + if x = root then E none else 0 := rfl

/-- Restrict a firing script from a leaf extension to the old vertices. -/
def retractScript (script : firing_script (addLeaf H root)) : firing_script H :=
  fun x => script (some x)

@[simp] theorem retractDiv_extendDiv (D : CFDiv H) :
    retractDiv H root (extendDiv H root D) = D := by
  funext x
  simp [retractDiv]
@[simp] theorem retractDiv_add (E F : CFDiv (addLeaf H root)) :
    retractDiv H root (E + F) = retractDiv H root E + retractDiv H root F := by
  funext x
  by_cases hx : x = root
  · simp [retractDiv, hx]
    ring
  · simp [retractDiv, hx]
@[simp] theorem retractDiv_sub (E F : CFDiv (addLeaf H root)) :
    retractDiv H root (E - F) = retractDiv H root E - retractDiv H root F := by
  rw [sub_eq_add_neg, sub_eq_add_neg, retractDiv_add]
  funext x
  by_cases hx : x = root
  · simp [retractDiv, hx]
    ring
  · simp [retractDiv, hx]

/-- Retraction commutes with principal divisors.  The leaf-edge contribution
cancels between the root and the leaf. -/
theorem retractDiv_prin (script : firing_script (addLeaf H root)) :
    retractDiv H root (prin (addLeaf H root) script) =
      prin H (retractScript H root script) := by
  funext x
  by_cases hx : x = root
  · subst x
    simp only [retractDiv_apply, if_pos]
    change
      (∑ neighbor : Option H.V,
        (script neighbor - script (some root)) *
          (num_edges (addLeaf H root) (some root) neighbor : ℤ)) +
        ∑ neighbor : Option H.V,
          (script neighbor - script none) *
            (num_edges (addLeaf H root) none neighbor : ℤ) =
      ∑ neighbor : H.V,
        (script (some neighbor) - script (some root)) *
          (num_edges H root neighbor : ℤ)
    rw [Fintype.sum_option, Fintype.sum_option]
    simp
    ring
  · simp only [retractDiv_apply, if_neg hx]
    simp only [add_zero]
    change
      (∑ neighbor : Option H.V,
        (script neighbor - script (some x)) *
          (num_edges (addLeaf H root) (some x) neighbor : ℤ)) =
      ∑ neighbor : H.V,
        (script (some neighbor) - script (some x)) * (num_edges H x neighbor : ℤ)
    rw [Fintype.sum_option]
    simp [hx]

/-- Linear equivalence on a leaf extension retracts to linear equivalence on
the original graph. -/
theorem linearEquiv_retractDiv {E F : CFDiv (addLeaf H root)}
    (hEquiv : linear_equiv (addLeaf H root) E F) :
    linear_equiv H (retractDiv H root E) (retractDiv H root F) := by
  unfold linear_equiv at hEquiv ⊢
  rw [principal_iff_eq_prin] at hEquiv ⊢
  obtain ⟨script, hscript⟩ := hEquiv
  refine ⟨retractScript H root script, ?_⟩
  rw [← retractDiv_sub, hscript, retractDiv_prin]

/-- Retraction of an effective divisor across the leaf is effective. -/
theorem effective_retractDiv {E : CFDiv (addLeaf H root)} (hE : effective E) :
    effective (retractDiv H root E) := by
  intro x
  by_cases hx : x = root
  · subst x
    simpa [retractDiv] using add_nonneg (hE (some root)) (hE none)
  · simpa [retractDiv, hx] using hE (some x)

/-- Winnability on a leaf extension retracts to the original graph. -/
theorem winnable_retractDiv {E : CFDiv (addLeaf H root)}
    (hWin : winnable (addLeaf H root) E) :
    winnable H (retractDiv H root E) := by
  rw [winnable_iff_exists_effective] at hWin ⊢
  obtain ⟨F, hEffective, hEquiv⟩ := hWin
  exact ⟨retractDiv H root F, effective_retractDiv H root hEffective,
    linearEquiv_retractDiv H root hEquiv⟩
/-- Moving all leaf chips to the root preserves divisor degree. -/
@[simp] theorem deg_retractDiv (E : CFDiv (addLeaf H root)) :
    deg (retractDiv H root E) = deg E := by
  classical
  change
    (∑ x : H.V, (E (some x) + if x = root then E none else 0)) =
      ∑ x : Option H.V, E x
  rw [sum_add_distrib, Fintype.sum_ite_eq', Fintype.sum_option]
  ring
/-- The leaf transfer identifies every divisor with the zero extension of its
retraction, up to linear equivalence. -/
theorem linearEquiv_retractDiv_extendDiv (E : CFDiv (addLeaf H root)) :
    linear_equiv (addLeaf H root) E
      (extendDiv H root (retractDiv H root E)) := by
  unfold linear_equiv
  rw [principal_iff_eq_prin]
  refine ⟨E none • leafMoveScript H root, ?_⟩
  rw [(prin (addLeaf H root)).map_zsmul, prin_leafMoveScript]
  funext vertex
  cases vertex with
  | none =>
      simp [extendDiv, one_chip]
  | some x =>
      by_cases hx : x = root
      · subst x
        simp [extendDiv, retractDiv, one_chip]
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          extendDiv_some, retractDiv_apply, one_chip]
        simp only [if_neg hx]
        have hSome : (some x : (addLeaf H root).V) ≠ some root := by
          intro h
          exact hx (Option.some.inj h)
        have hLeaf : (some x : (addLeaf H root).V) ≠ none := by
          simp
        have hRight : E none *
            ((if (some x : (addLeaf H root).V) = some root then 1 else 0) -
              if (some x : (addLeaf H root).V) = none then 1 else 0) = 0 := by
          simp [hSome, hLeaf]
        calc
          (E (some x) + 0) - E (some x) = 0 := by ring
          _ = E none *
              ((if (some x : (addLeaf H root).V) = some root then 1 else 0) -
                if (some x : (addLeaf H root).V) = none then 1 else 0) :=
            hRight.symm

/-- Zero extension preserves every rank lower bound. -/
theorem rank_geq_addLeaf {D : CFDiv H} {k : ℤ}
    (hRank : rank_geq H D k) :
    rank_geq (addLeaf H root) (extendDiv H root D) k := by
  intro E hE
  have hRetract : retractDiv H root E ∈ eff_of_degree H k :=
    ⟨effective_retractDiv H root hE.1, by simpa using hE.2⟩
  have hOldWin : winnable H (D - retractDiv H root E) :=
    hRank (retractDiv H root E) hRetract
  have hExtendedWin :
      winnable (addLeaf H root)
        (extendDiv H root (D - retractDiv H root E)) :=
    winnable_extendDiv H root hOldWin
  have hDifference :
      extendDiv H root (D - retractDiv H root E) =
        extendDiv H root D - extendDiv H root (retractDiv H root E) := by
    rw [extendDiv_sub]
  rw [hDifference] at hExtendedWin
  apply winnable_equiv_winnable (addLeaf H root) _ _ hExtendedWin
  unfold linear_equiv
  rw [principal_iff_eq_prin]
  obtain ⟨script, hscript⟩ :=
    (principal_iff_eq_prin (addLeaf H root)
      (extendDiv H root (retractDiv H root E) - E)).mp
      (linearEquiv_retractDiv_extendDiv H root E)
  refine ⟨script, ?_⟩
  calc
    extendDiv H root D - E -
        (extendDiv H root D - extendDiv H root (retractDiv H root E)) =
      extendDiv H root (retractDiv H root E) - E := by abel
    _ = prin (addLeaf H root) script := hscript

/-- Every rank lower bound of a zero-extended divisor is already witnessed on
the original graph. -/
theorem rank_geq_of_addLeaf {D : CFDiv H} {k : ℤ}
    (hRank : rank_geq (addLeaf H root) (extendDiv H root D) k) :
    rank_geq H D k := by
  intro A hA
  have hExtended : extendDiv H root A ∈ eff_of_degree (addLeaf H root) k :=
    ⟨effective_extendDiv H root hA.1, by simpa using hA.2⟩
  have hWin : winnable (addLeaf H root)
      (extendDiv H root D - extendDiv H root A) := hRank _ hExtended
  have hRetracted := winnable_retractDiv H root hWin
  simpa using hRetracted

/-- Zero extension preserves and reflects every rank lower bound. -/
theorem rank_geq_addLeaf_iff (D : CFDiv H) (k : ℤ) :
    rank_geq (addLeaf H root) (extendDiv H root D) k ↔ rank_geq H D k := by
  constructor
  · exact rank_geq_of_addLeaf H root
  · exact rank_geq_addLeaf H root

/-- Zero extension preserves divisor rank. -/
theorem rank_addLeaf (D : CFDiv H) :
    rank (addLeaf H root) (extendDiv H root D) = rank H D := by
  apply le_antisymm
  · apply (rank_geq_iff H D (rank (addLeaf H root) (extendDiv H root D))).mp
    apply rank_geq_of_addLeaf H root
    exact (rank_geq_iff (addLeaf H root) (extendDiv H root D) _).mpr le_rfl
  · apply (rank_geq_iff (addLeaf H root) (extendDiv H root D) (rank H D)).mp
    apply rank_geq_addLeaf H root
    exact (rank_geq_iff H D _).mpr le_rfl

/-- Retraction across the added leaf preserves divisor rank. -/
theorem rank_retractDiv (E : CFDiv (addLeaf H root)) :
    rank H (retractDiv H root E) = rank (addLeaf H root) E := by
  calc
    rank H (retractDiv H root E) =
        rank (addLeaf H root) (extendDiv H root (retractDiv H root E)) :=
      (rank_addLeaf H root _).symm
    _ = rank (addLeaf H root) E :=
      (Utilities.rank_eq_of_linear_equiv (addLeaf H root)
        (linearEquiv_retractDiv_extendDiv H root E)).symm

/-- Brill--Noether existence in every rank and degree is invariant under
adjoining a leaf. -/
theorem bnExists_addLeaf_iff (r d : ℤ) :
    BNExists (addLeaf H root) r d ↔ BNExists H r d := by
  constructor
  · rintro ⟨E, hDegree, hRank⟩
    exact ⟨retractDiv H root E, by simpa using hDegree,
      by simpa [rank_retractDiv H root E] using hRank⟩
  · rintro ⟨D, hDegree, hRank⟩
    exact ⟨extendDiv H root D, by simpa using hDegree,
      by simpa [rank_addLeaf H root D] using hRank⟩

/-! ## The public collapse interface -/

/-- Collapse the added leaf onto its root. -/
def collapseDiv (D : CFDiv (addLeaf H root)) : CFDiv H :=
  retractDiv H root D

/-- Collapsing the leaf preserves divisor rank exactly. -/
theorem rank_collapseDiv (D : CFDiv (addLeaf H root)) :
    rank H (collapseDiv H root D) = rank (addLeaf H root) D := by
  exact rank_retractDiv H root D

/-- Collapsing a principal divisor restricts its firing script to the old
vertices. -/
theorem prin_collapse (script : firing_script (addLeaf H root)) :
    collapseDiv H root (prin (addLeaf H root) script) =
      prin H (fun w => script (some w)) := by
  exact retractDiv_prin H root script

/-- Collapsing an effective divisor preserves effectivity. -/
theorem effective_collapseDiv {D : CFDiv (addLeaf H root)}
    (hD : effective D) : effective (collapseDiv H root D) := by
  exact effective_retractDiv H root hD

/-- Rank one descends when the added leaf is collapsed. -/
theorem rank_ge_one_collapseDiv {D : CFDiv (addLeaf H root)}
    (hRank : rank (addLeaf H root) D ≥ 1) :
    rank H (collapseDiv H root D) ≥ 1 := by
  rw [rank_collapseDiv]
  exact hRank

/-- Rank-one Brill--Noether existence descends when the added leaf is
collapsed. -/
theorem bnExists_rank_one_of_addLeaf {d : ℤ} :
    BNExists (addLeaf H root) 1 d → BNExists H 1 d := by
  exact (bnExists_addLeaf_iff H root 1 d).mp

/-- Adjoining one leaf does not change divisorial gonality. -/
theorem divisorialGonality_addLeaf (hconn : graph_connected H) :
    divisorialGonality (addLeaf H root) = divisorialGonality H := by
  apply Nat.le_antisymm
  · have hBN : BNExists (addLeaf H root) 1
        (divisorialGonality H : ℤ) :=
      bnExists_rank_one_addLeaf H root
        (BNExists_one_divisorialGonality hconn)
    exact_mod_cast divisorialGonality_le_of_BNExists hBN
  · have hBN : BNExists H 1
        (divisorialGonality (addLeaf H root) : ℤ) :=
      bnExists_rank_one_of_addLeaf H root
        (BNExists_one_divisorialGonality (graph_connected_addLeaf H root hconn))
    exact_mod_cast divisorialGonality_le_of_BNExists hBN

end LeafExtension

end Utilities.Certificate
