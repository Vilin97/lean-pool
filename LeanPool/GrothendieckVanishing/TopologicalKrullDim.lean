/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/

import Mathlib.Topology.KrullDimension
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring
/-!
# Topological Krull Dimension

API for topological Krull dimension on irreducible spaces.

## Main results

- `TopologicalSpace.IrreducibleCloseds.eq_univ_of_topologicalKrullDim_nonpos`: on an
  irreducible space with dim ≤ 0, every irreducible closed set is the whole space
- `opens_eq_bot_or_top_of_irreducibleSpace_dim_zero`: on an irreducible dim-0 space,
  the only opens are ⊥ and ⊤
- `topologicalKrullDim_nonneg`: non-empty spaces have dim ≥ 0
- `topologicalKrullDim_subspace_lt_of_lt`: strict ambient upper bounds descend to subspaces
- `topologicalKrullDim_lt_top_of_lt_nat`: natural-number upper bounds imply finiteness
- `topologicalKrullDim_lt_nat_of_lt_of_lt_nat_succ`: if `dim Y < dim X < n + 1`, then
  `dim Y < n`
- `topologicalKrullDim_lt_of_isIrreducible_of_isClosed`: proper closed subsets of
  irreducible spaces with finite dim have strictly smaller dim
- `topologicalKrullDim_pos_iff_exists_irreducibleCloseds_ne_univ`: on an irreducible
  space, `dim > 0` iff there is a proper irreducible closed subset
- `exists_closed_subset_lt_topologicalKrullDim_of_irreducible_pos`: on an irreducible
  space of positive finite Krull dimension, there exists a proper closed subset of
  strictly smaller dimension
-/

universe u

open CategoryTheory TopologicalSpace

/-! ## Irreducible spaces of dimension 0 -/

namespace TopologicalSpace
namespace IrreducibleCloseds

variable {X : Type u} [TopologicalSpace X]

/-- On an irreducible space with topologicalKrullDim ≤ 0, every irreducible closed subset
    equals the whole space. -/
theorem eq_univ_of_topologicalKrullDim_nonpos [IrreducibleSpace X]
    (S : IrreducibleCloseds X) (hdim : topologicalKrullDim X ≤ 0) :
    (S : Set X) = Set.univ :=
  le_antisymm (Set.subset_univ _)
    ((Order.krullDim_nonpos_iff_forall_isMax).mp hdim S
      (show S ≤ ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩ from
        Set.subset_univ _))

end IrreducibleCloseds
end TopologicalSpace

/-- On an irreducible space of dimension ≤ 0, the only opens are ⊥ and ⊤.
    Every point is dense, so any nonempty open contains every point. -/
theorem opens_eq_bot_or_top_of_irreducibleSpace_dim_zero
    {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]
    (hdim : topologicalKrullDim X ≤ 0) (U : Opens X) :
    U = ⊥ ∨ U = ⊤ := by
  by_cases hne : (U : Set X).Nonempty
  · right; ext x; refine ⟨fun _ ↦ trivial, fun _ ↦ by_contra fun hx ↦ ?_⟩
    have hclosure : closure ({x} : Set X) = Set.univ :=
      TopologicalSpace.IrreducibleCloseds.eq_univ_of_topologicalKrullDim_nonpos
        (X := X) ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩ hdim
    have := hclosure ▸
      closure_minimal (Set.singleton_subset_iff.mpr hx) U.isOpen.isClosed_compl
    exact this (Set.mem_univ hne.some) hne.some_mem
  · exact Or.inl (Opens.ext (Set.not_nonempty_iff_eq_empty.mp hne))

/-! ## Dimension helpers -/

/-- On a non-empty topological space, the topological Krull dimension is ≥ 0. -/
theorem topologicalKrullDim_nonneg {X : Type u} [TopologicalSpace X]
    [Nonempty X] : topologicalKrullDim X ≥ 0 := by
  rw [topologicalKrullDim, ge_iff_le, Order.krullDim_nonneg_iff]
  obtain ⟨x⟩ := ‹Nonempty X›
  exact ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩

/-- Any strict upper bound on the topological Krull dimension of a space also bounds the
dimension of each subspace. -/
theorem topologicalKrullDim_subspace_lt_of_lt {X : Type u} [TopologicalSpace X]
    (Y : Set X) {a : WithBot ℕ∞} (ha : topologicalKrullDim X < a) :
    topologicalKrullDim Y < a :=
  lt_of_le_of_lt (topologicalKrullDim_subspace_le X Y) ha

/-- A natural-number upper bound on the topological Krull dimension implies that the
dimension is finite. -/
theorem topologicalKrullDim_lt_top_of_lt_nat {X : Type u} [TopologicalSpace X] {m : ℕ}
    (hm : topologicalKrullDim X < ↑↑(m : ℕ)) :
    topologicalKrullDim X < ⊤ :=
  lt_of_lt_of_le hm le_top

/-- If `Y` has strictly smaller topological Krull dimension than `X`, then any natural-number
upper bound `dim X < n + 1` descends to the predecessor bound `dim Y < n`. -/
theorem topologicalKrullDim_lt_nat_of_lt_of_lt_nat_succ {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] {n : ℕ}
    (hYX : topologicalKrullDim Y < topologicalKrullDim X)
    (hXn : topologicalKrullDim X < ↑↑(n + 1 : ℕ)) :
    topologicalKrullDim Y < ↑↑(n : ℕ) :=
  lt_of_lt_of_le hYX ((ENat.WithBot.lt_add_one_iff).mp (by simpa using hXn))

namespace TopologicalSpace
namespace IrreducibleCloseds

variable {X : Type u} [TopologicalSpace X]

/-- The height of an irreducible closed subset in the inclusion order. -/
noncomputable def height (S : IrreducibleCloseds X) : ℕ∞ :=
  Order.height S

theorem height_add_one_le {S T : IrreducibleCloseds X} (hST : S < T) :
    S.height + 1 ≤ T.height := by
  simpa [height] using (Order.height_add_one_le hST)

theorem height_le_topologicalKrullDim (S : IrreducibleCloseds X) :
    S.height ≤ topologicalKrullDim X := by
  simpa [height, topologicalKrullDim] using (Order.height_le_krullDim S)

theorem height_le_height_map_of_isInducing {Y : Type*} [TopologicalSpace Y] {f : Y → X}
    (hf : Topology.IsInducing f) (S : IrreducibleCloseds Y) :
    S.height ≤ (IrreducibleCloseds.map f hf.continuous S).height := by
  simpa [height] using Order.height_le_height_apply_of_strictMono
    (IrreducibleCloseds.map f hf.continuous)
    (IrreducibleCloseds.map_strictMono_of_isInducing hf)
    S

/-- An irreducible closed subset of a proper closed subspace of an irreducible space has height
at most one less than the ambient topological Krull dimension. -/
theorem height_add_one_le_topologicalKrullDim_of_isClosed_of_ne_univ
    [IrreducibleSpace X] {Y : Set X} (hY : IsClosed Y) (hne : Y ≠ Set.univ)
    (S : IrreducibleCloseds Y) :
    (S.height : WithBot ℕ∞) + 1 ≤ topologicalKrullDim X := by
  let T : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  set f : IrreducibleCloseds Y → IrreducibleCloseds X :=
    IrreducibleCloseds.map (Subtype.val : Y → X) continuous_subtype_val
  have h_height_le : S.height ≤ (f S).height :=
    height_le_height_map_of_isInducing Topology.IsInducing.subtypeVal S
  have h_lt_top : f S < T := by
    refine lt_of_le_of_ne (Set.subset_univ _) fun h_eq ↦ hne ?_
    have h_sub : (f S : Set X) ⊆ Y :=
      closure_minimal (fun _ ⟨⟨_, hy⟩, _, rfl⟩ ↦ hy) hY
    have h_eq' : (f S : Set X) = Set.univ := by
      simpa [T] using congrArg (fun Z : IrreducibleCloseds X => (Z : Set X)) h_eq
    rwa [h_eq', Set.univ_subset_iff] at h_sub
  have h_height_add_one : ((f S).height : WithBot ℕ∞) + 1 ≤ T.height := by
    exact_mod_cast height_add_one_le h_lt_top
  refine le_trans ?_ (h_height_add_one.trans ?_)
  · gcongr
    exact_mod_cast h_height_le
  · simpa [T] using (height_le_topologicalKrullDim T : _)

end IrreducibleCloseds

/-- The topological Krull dimension is the supremum of the heights of irreducible closed sets. -/
theorem topologicalKrullDim_eq_iSup_height (X : Type u) [TopologicalSpace X] :
    topologicalKrullDim X = ⨆ S : IrreducibleCloseds X, ↑S.height := by
  simpa [IrreducibleCloseds.height, topologicalKrullDim] using
    (Order.krullDim_eq_iSup_height (α := IrreducibleCloseds X))

/-- The topological Krull dimension plus one is the supremum of the heights of irreducible
closed sets, each shifted by one. -/
theorem topologicalKrullDim_add_one_eq_iSup_height_add_one (X : Type u) [TopologicalSpace X] :
    topologicalKrullDim X + 1 =
      ⨆ S : IrreducibleCloseds X, ((S.height : WithBot ℕ∞) + 1) := by
  cases isEmpty_or_nonempty (IrreducibleCloseds X) with
  | inl h =>
      rw [topologicalKrullDim_eq_iSup_height]
      letI := h
      simp
  | inr h =>
      letI := h
      rw [topologicalKrullDim_eq_iSup_height]
      have bdd :
          BddAbove (Set.range (fun S : IrreducibleCloseds X ↦ IrreducibleCloseds.height S)) :=
        OrderTop.bddAbove _
      have hcoe_iSup :
          (⨆ S : IrreducibleCloseds X, (S.height : WithBot ℕ∞)) =
            ↑(⨆ S : IrreducibleCloseds X, IrreducibleCloseds.height S) :=
        (WithBot.coe_iSup
          (f := fun S : IrreducibleCloseds X ↦ IrreducibleCloseds.height S) bdd).symm
      have hcoe_add :
          (↑(⨆ S : IrreducibleCloseds X, IrreducibleCloseds.height S) : WithBot ℕ∞) + 1 =
            ↑((⨆ S : IrreducibleCloseds X, IrreducibleCloseds.height S) + 1) := by
        push_cast; ring
      have hsucc_coe : ∀ S : IrreducibleCloseds X,
          (↑(S.height + 1 : ℕ∞) : WithBot ℕ∞) = (↑S.height : WithBot ℕ∞) + 1 := by
        intro S; push_cast; ring
      rw [hcoe_iSup, hcoe_add, ENat.iSup_add,
        WithBot.coe_iSup
          (f := fun S : IrreducibleCloseds X ↦ IrreducibleCloseds.height S + 1)
          (OrderTop.bddAbove _)]
      simp_rw [hsucc_coe]

end TopologicalSpace

/-- Unconditional: topologicalKrullDim Y + 1 ≤ topologicalKrullDim X for
    Y ⊊ X closed in irreducible X. -/
theorem topologicalKrullDim_add_one_le_of_isIrreducible_of_isClosed {X : Type u}
    [TopologicalSpace X] [IrreducibleSpace X] {Y : Set X} (hY : IsClosed Y)
    (hne : Y ≠ Set.univ) :
    topologicalKrullDim Y + 1 ≤ topologicalKrullDim X := by
  rw [topologicalKrullDim_add_one_eq_iSup_height_add_one]
  exact iSup_le (fun s ↦
    IrreducibleCloseds.height_add_one_le_topologicalKrullDim_of_isClosed_of_ne_univ hY hne s)

/-- If `topologicalKrullDim Y + 1 ≤ topologicalKrullDim X` and `Y` has finite dimension, then
    `Y` has strictly smaller topological Krull dimension than `X`. -/
private theorem topologicalKrullDim_lt_of_add_one_le_of_lt_top {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    (h : topologicalKrullDim Y + 1 ≤ topologicalKrullDim X)
    (hfin : topologicalKrullDim Y < ⊤) :
    topologicalKrullDim Y < topologicalKrullDim X := by
  have hX_nonbot : (⊥ : WithBot ℕ∞) < topologicalKrullDim X :=
    lt_of_lt_of_le (WithBot.bot_lt_coe (0 : ℕ∞)) topologicalKrullDim_nonneg
  rcases hYdim : topologicalKrullDim Y with _ | ydim
  · exact hX_nonbot
  · rcases hXdim : topologicalKrullDim X with _ | xdim
    · rw [hXdim] at hX_nonbot
      cases hX_nonbot
    · rw [hYdim, hXdim] at h
      rw [hYdim] at hfin
      have hy_coe_ne_top : (((ydim : ℕ∞) : WithBot ℕ∞)) ≠ ⊤ := ne_top_of_lt hfin
      have hy_ne_top : ydim ≠ ⊤ := by
        intro hy_top
        exact hy_coe_ne_top (by simp [hy_top])
      have hy_lt : ydim < ydim + 1 := (ENat.lt_add_one_iff hy_ne_top).mpr le_rfl
      have hy_lt' :
          (((ydim : ℕ∞) : WithBot ℕ∞) < (((ydim + 1 : ℕ∞) : WithBot ℕ∞))) := by
        exact_mod_cast hy_lt
      have h' : (((ydim + 1 : ℕ∞) : WithBot ℕ∞) ≤ ((xdim : ℕ∞) : WithBot ℕ∞)) := by
        simpa [WithBot.some_eq_coe] using h
      exact lt_of_lt_of_le hy_lt' h'

/-- On an irreducible space, a proper closed subset with finite Krull dimension has
strictly smaller Krull dimension. The finiteness hypothesis excludes the case where both
`Y` and `X` have infinite dimension. -/
theorem topologicalKrullDim_lt_of_isIrreducible_of_isClosed {X : Type u} [TopologicalSpace X]
    [IrreducibleSpace X] {Y : Set X} (hY : IsClosed Y) (hne : Y ≠ Set.univ)
    (hfin : topologicalKrullDim Y < ⊤) :
    topologicalKrullDim Y < topologicalKrullDim X :=
  topologicalKrullDim_lt_of_add_one_le_of_lt_top
    (topologicalKrullDim_add_one_le_of_isIrreducible_of_isClosed hY hne) hfin

/-- On an irreducible space, positive topological Krull dimension is equivalent to the
existence of a proper irreducible closed subset. -/
theorem topologicalKrullDim_pos_iff_exists_irreducibleCloseds_ne_univ {X : Type u}
    [TopologicalSpace X] [IrreducibleSpace X] :
    topologicalKrullDim X > 0 ↔ ∃ Z : IrreducibleCloseds X, (Z : Set X) ≠ Set.univ := by
  let T : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  constructor
  · intro hpos
    simp only [topologicalKrullDim, gt_iff_lt] at hpos
    obtain ⟨A, B, hAB⟩ := Order.krullDim_pos_iff.mp hpos
    by_cases hB : (B : Set X) = Set.univ
    · refine ⟨A, fun hA ↦ hAB.ne ?_⟩
      exact IrreducibleCloseds.ext (hA.trans hB.symm)
    · exact ⟨B, hB⟩
  · rintro ⟨Z, hZ_ne_univ⟩
    have hZ_lt : Z < T := by
      refine lt_of_le_of_ne (Set.subset_univ _) fun hZT ↦ hZ_ne_univ ?_
      simpa [T] using congrArg (fun Z : IrreducibleCloseds X => (Z : Set X)) hZT
    simpa [topologicalKrullDim, gt_iff_lt] using (Order.krullDim_pos_iff.mpr ⟨Z, T, hZ_lt⟩)

/-- On an irreducible space of positive finite Krull dimension, one can choose a proper
closed subset `Z ⊊ X` of strictly smaller Krull dimension. This isolates the structural
closed-subset choice from the separate task of passing numerical bounds to `Z`. -/
theorem exists_closed_subset_lt_topologicalKrullDim_of_irreducible_pos
    {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]
    (hpos : topologicalKrullDim X > 0) (hX_lt_top : topologicalKrullDim X < ⊤) :
    ∃ Z : Set X, IsClosed Z ∧ Z ≠ Set.univ ∧
      topologicalKrullDim (TopCat.of Z) < topologicalKrullDim X := by
  obtain ⟨Z, hZ_ne_univ⟩ :=
    topologicalKrullDim_pos_iff_exists_irreducibleCloseds_ne_univ (X := X) |>.mp hpos
  have hZ_lt_top : topologicalKrullDim (TopCat.of (Z : Set X)) < ⊤ := by
    simpa using topologicalKrullDim_subspace_lt_of_lt (X := X) (Z : Set X) hX_lt_top
  refine ⟨Z, Z.isClosed, hZ_ne_univ, ?_⟩
  exact topologicalKrullDim_lt_of_isIrreducible_of_isClosed
    (X := X) Z.isClosed hZ_ne_univ hZ_lt_top
