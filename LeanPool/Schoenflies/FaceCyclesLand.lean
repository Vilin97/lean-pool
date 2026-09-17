/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.FaceCyclesProof
import LeanPool.Schoenflies.PrePolygonArc

/-!
# `lem:face-cycles`, with nothing assumed

`Schoenflies/FaceCyclesProof.lean` proves `lem:face-cycles` modulo one hypothesis,
`Schoenflies.CrosscutSplitsRegion`: the exhaustion clause of `thm:polygonal-crosscut` for a
crosscut whose two endpoints are *arbitrary points* of the curve. This module proves that
hypothesis and restates the lemma without it (`Graph.face_cycles'`,
`Graph.IsDrawing.hasFaceCycles_union'`).

## Why the crosscut theorem had to be redone, and how far

`main`'s Theorem 2.8 (`Schoenflies.IsPolygonalCrosscut`) cuts a `ClosedPolygon` at two of *its
vertices*, and `Schoenflies.ClosedPolygon.isCornerAt_vertex` says a point at which the curve runs
straight is a vertex of no `ClosedPolygon` presentation of it. In the ear induction the two cut
points are graph vertices, at which the two cycle edges may leave along opposite rays. So the
presentation has to be `Schoenflies.PrePolygon`, which has no `corner` field, and the two `main`
hypotheses `edges₁`/`edges₂` — multiset equalities `SameEdges Jᵢ.pieces (Aᵢ ++ K)` — have to go
as well, for the reason `Schoenflies/FaceCyclesProof.lean` records: the merged curve `Aᵢ ∪ P` may
run straight through a cut point, and then no presentation of it has an edge ending there.

Both go away at once by never realizing `J₁` and `J₂` at all. The two curves of the split are
given by *literal* edge lists `Aᵢ ++ K`, so Lemma 2.7 (`Schoenflies.parity_split`) applies with
nothing to check, and only the *easy* half of Theorem 2.3 is asked of them: "points in the same
region have the same crossing count", which is Lemma 2.2
(`Schoenflies.parity_eq_of_mem_connectedComponentIn`) and needs no realization. The hard half —
the two values `0` and `1` — is needed for `J` alone, where
`Schoenflies.PrePolygon.parity_eq_one_iff` of `Schoenflies/PrePolygonSep.lean` supplies it. That
is the whole of the reduction; Lemma 2.6 (`Schoenflies.crosscut_cells`) is already stated at the
set level and is quoted unchanged.

What the presentation still has to do is put the two cut points *on* its vertex list, and that is
`Schoenflies.PrePolygon.insertLast` of `Schoenflies/PrePolygonArc.lean`, the inverse of
`Schoenflies.PrePolygon.deleteLast`. A point interior to an edge is brought to the last edge by
`Schoenflies.PrePolygon.rotate` and the edge is split in two; simplicity survives because the far
end of the split edge lies on neither half.

## For the integrator

The `Schoenflies.PrePolygon` arc apparatus this module runs on —
`Schoenflies.PrePolygon.arcPieces`, `…arc`, `…arcList`, `…insertLast` and
`Schoenflies.exists_prePolygon_split` — lives in `Schoenflies/PrePolygonArc.lean`, shared with
`Schoenflies/Graph/K33Land.lean`. It is `Schoenflies.ClosedPolygon.arcPieces` and its API of
`Schoenflies/ParitySplitting.lean` and `Schoenflies/Realization.lean` transcribed with the
structure changed — the proofs use `vertex_inj` and `edges_meet` and nothing else. The right
arrangement, as `Schoenflies/PrePolygonSep.lean` already says of `pieces`, is to prove them once
for `PrePolygon` and define the `ClosedPolygon` versions as `P.toPre.arcPieces`; that needs
`PrePolygon` moved up beside `ClosedPolygon` in `Schoenflies/Strip.lean`.

Three declarations here are general and belong elsewhere:
`Schoenflies.isSeparating_of_isJordanCurve` in `Schoenflies/Realization.lean`,
`Schoenflies.IsArcBetween.ne` in `Schoenflies/Curve.lean`, and
`Schoenflies.isChainFrom_segsOf` in `Schoenflies/ParitySplitting.lean` beside
`Schoenflies.isChainFrom_pathPieces`. `Schoenflies.two_arcs_unique_of_isClosed` subsumes
`Schoenflies.two_arcs_unique` and should replace it in `Schoenflies/Realization.lean`.

Once this module is moved above `Schoenflies/FaceCyclesProof.lean`, the hypothesis
`Schoenflies.CrosscutSplitsRegion` can be deleted from `Graph.face_cycles` and
`Graph.IsDrawing.hasFaceCycles_union`, and the two primed statements at the end here dropped.

## Blueprint

* `Schoenflies.two_arcs_unique_of_isClosed` — the two arcs a pair of points cuts a curve into are
  determined, with the competing splitting known only to be closed and nondegenerate.
* `Schoenflies.crosscutSplitsRegion` — the exhaustion clause of `thm:polygonal-crosscut` at
  arbitrary cut points: `Schoenflies.CrosscutSplitsRegion`, proved.
* `Graph.IsDrawing.hasFaceCycles_union'` — one ear of `lem:face-cycles`.
* `Graph.face_cycles'` — **`lem:face-cycles`**.
* `Graph.IsFaceCycle.eq_inside_of_isBounded'` — "in particular, every bounded face is the
  interior of its boundary cycle".
-/
open Bornology Metric Set

namespace Schoenflies

/-! ## Small pieces the assembly needs -/

/-- **A polygonal Jordan curve separates the plane** (Theorem 2.3, at the set level): realize it
and quote `Schoenflies.ClosedPolygon.isSeparating_carrier`. -/
theorem isSeparating_of_isJordanCurve {S : Set Plane} (hJ : IsJordanCurve S)
    (hP : IsPolygonal S) : IsSeparating S := by
  obtain ⟨m, Q, hQ⟩ := exists_closedPolygon hJ hP
  exact hQ ▸ Q.isSeparating_carrier

/-- **A polyline is a chain from its first point to its last**, with its degenerate steps
dropped. `Schoenflies.isChainFrom_pathPieces` says this for `Schoenflies.pathPieces`, which keeps
them; `Schoenflies.segsOf` is the list a consumer needing nondegenerate edges must use. -/
theorem isChainFrom_segsOf : ∀ (vs : List Plane) (h : vs ≠ []),
    IsChainFrom (segsOf vs) (vs.head h) (vs.getLast h)
  | [], h => absurd rfl h
  | [v], _ => by simpa using isChainFrom_nil v
  | u :: v :: rest, hu => by
    classical
    have hne : (v :: rest) ≠ [] := List.cons_ne_nil _ _
    have ih : IsChainFrom (segsOf (v :: rest)) v ((v :: rest).getLast hne) :=
      isChainFrom_segsOf (v :: rest) hne
    have hgl : (u :: v :: rest).getLast hu = (v :: rest).getLast hne := List.getLast_cons hne
    rw [show (u :: v :: rest).head hu = u from rfl, hgl, segsOf_cons_cons]
    split_ifs with huv
    · rw [huv]; exact ih
    · intro f
      simp only [List.map_cons, List.sum_cons]
      rw [ih f]
      linear_combination add_self_zmod_two (f v)

/-- **The two-arc decomposition is determined, and the competitor need not be known to be two
arcs.** This is `Schoenflies.two_arcs_unique` with the hypotheses on the second splitting weakened
to what its proof uses: the two sets are closed and neither is just the two cut points. The edge
lists of a polygon supply exactly that, and nothing tells us they are arcs until this lemma has
said so. -/
theorem two_arcs_unique_of_isClosed {C A₁ A₂ D₁ D₂ : Set Plane} {p q : Plane}
    (hA : A₁ ∪ A₂ = C) (hAi : A₁ ∩ A₂ = {p, q})
    (hD : D₁ ∪ D₂ = C) (hDi : D₁ ∩ D₂ = {p, q})
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q)
    (hc1 : IsClosed D₁) (hc2 : IsClosed D₂)
    (hn1 : ¬ D₁ ⊆ ({p, q} : Set Plane)) (hn2 : ¬ D₂ ⊆ ({p, q} : Set Plane)) :
    (A₁ = D₁ ∧ A₂ = D₂) ∨ (A₁ = D₂ ∧ A₂ = D₁) := by
  have hpA : p ∈ A₁ ∩ A₂ := by rw [hAi]; exact Or.inl rfl
  have hqA : q ∈ A₁ ∩ A₂ := by rw [hAi]; exact Or.inr rfl
  have hpD : p ∈ D₁ ∩ D₂ := by rw [hDi]; exact Or.inl rfl
  have hqD : q ∈ D₁ ∩ D₂ := by rw [hDi]; exact Or.inr rfl
  -- An arc between the two points lies on one side of the other splitting.
  have key : ∀ A : Set Plane, IsArcBetween A p q → A ⊆ C → A ⊆ D₁ ∨ A ⊆ D₂ := by
    intro A hAar hAC
    obtain ⟨hconn, hne⟩ := hAar.preconnected_diff
    have hsub : A \ {p, q} ⊆ D₁ᶜ ∪ D₂ᶜ := by
      intro w hw
      by_cases h1 : w ∈ D₁
      · by_cases h2 : w ∈ D₂
        · exact absurd (show w ∈ ({p, q} : Set Plane) by rw [← hDi]; exact ⟨h1, h2⟩) hw.2
        · exact Or.inr h2
      · exact Or.inl h1
    have hnone : ¬ ((A \ {p, q}) ∩ (D₁ᶜ ∩ D₂ᶜ)).Nonempty := by
      rintro ⟨w, hw, h1, h2⟩
      have hwC : w ∈ C := hAC hw.1
      rw [← hD] at hwC
      exact hwC.elim h1 h2
    have hends : ∀ D : Set Plane, p ∈ D → q ∈ D → A \ {p, q} ⊆ D → A ⊆ D := by
      intro D hpD' hqD' hsub' w hw
      by_cases hwpq : w ∈ ({p, q} : Set Plane)
      · rcases hwpq with rfl | rfl
        exacts [hpD', hqD']
      · exact hsub' ⟨hw, hwpq⟩
    by_cases hcase : ((A \ {p, q}) ∩ D₁ᶜ).Nonempty
    · refine Or.inr (hends D₂ hpD.2 hqD.2 fun w hw => ?_)
      by_contra hwD2
      exact hnone (hconn _ _ hc1.isOpen_compl hc2.isOpen_compl hsub hcase ⟨w, hw, hwD2⟩)
    · refine Or.inl (hends D₁ hpD.1 hqD.1 fun w hw => ?_)
      by_contra hwD1
      exact hcase ⟨w, hw, hwD1⟩
  -- Both arcs cannot land on the same side: the other side would be just the two points.
  have hnotboth : ∀ D D' : Set Plane, D ∪ D' = C → D ∩ D' = {p, q} →
      ¬ D' ⊆ ({p, q} : Set Plane) → A₁ ⊆ D → A₂ ⊆ D → False := by
    intro D D' hDD hDDi hD'n h1 h2
    refine hD'n ?_
    rw [← hDDi]
    intro w hw
    have hwC : w ∈ C := by rw [← hDD]; exact Or.inr hw
    rw [← hA] at hwC
    exact hwC.elim (fun h => ⟨h1 h, hw⟩) fun h => ⟨h2 h, hw⟩
  have heq : ∀ X Y X' Y' : Set Plane, X ∪ Y = C → X' ∪ Y' = C → X' ∩ Y' = {p, q} →
      p ∈ X → q ∈ X → X ⊆ X' → Y ⊆ Y' → X = X' := by
    intro X Y X' Y' hXY hX'Y' hX'Y'i hpX hqX hXX hYY
    refine Set.Subset.antisymm hXX fun w hw => ?_
    have hwC : w ∈ C := by rw [← hX'Y']; exact Or.inl hw
    rw [← hXY] at hwC
    rcases hwC with h | h
    · exact h
    · have hwpq : w ∈ ({p, q} : Set Plane) := by rw [← hX'Y'i]; exact ⟨hw, hYY h⟩
      rcases hwpq with rfl | rfl
      exacts [hpX, hqX]
  have hAC₁ : A₁ ⊆ C := by rw [← hA]; exact Set.subset_union_left
  have hAC₂ : A₂ ⊆ C := by rw [← hA]; exact Set.subset_union_right
  rcases key A₁ hA1 hAC₁ with h1 | h1 <;> rcases key A₂ hA2 hAC₂ with h2 | h2
  · exact absurd (hnotboth D₁ D₂ hD hDi hn2 h1 h2) (by simp)
  · exact Or.inl ⟨heq A₁ A₂ D₁ D₂ hA hD hDi hpA.1 hqA.1 h1 h2,
      heq A₂ A₁ D₂ D₁ (by rw [Set.union_comm]; exact hA) (by rw [Set.union_comm]; exact hD)
        (by rw [Set.inter_comm]; exact hDi) hpA.2 hqA.2 h2 h1⟩
  · exact Or.inr ⟨heq A₁ A₂ D₂ D₁ hA (by rw [Set.union_comm]; exact hD)
      (by rw [Set.inter_comm]; exact hDi) hpA.1 hqA.1 h1 h2,
      heq A₂ A₁ D₁ D₂ (by rw [Set.union_comm]; exact hA) hD hDi hpA.2 hqA.2 h2 h1⟩
  · exact absurd (hnotboth D₂ D₁ (by rw [Set.union_comm]; exact hD)
      (by rw [Set.inter_comm]; exact hDi) hn1 h1 h2) (by simp)

/-! ## Theorem 2.8 at arbitrary cut points

The blueprint's Theorem 2.8 is proved on `main` for a crosscut cutting a `ClosedPolygon` at two
of *its vertices*; `Schoenflies.ClosedPolygon.isCornerAt_vertex` makes that a real restriction,
since a point where the curve runs straight is a vertex of no `ClosedPolygon` presentation. The
exhaustion clause is what a consumer splitting a face at two graph vertices needs, and here it is
proved with no condition on the two points beyond lying on the curve.

The route is the blueprint's, with `PrePolygon` in place of `ClosedPolygon` and with the two
`Schoenflies.SameEdges` hypotheses of `Schoenflies.IsPolygonalCrosscut` replaced by *literal*
edge lists: the two curves of the split are presented as `Aᵢ ++ K`, so Lemma 2.7
(`Schoenflies.parity_split`) applies with nothing to check. Only one direction of Theorem 2.3 is
needed for those two lists — "the same region forces the same count", which is Lemma 2.2 and asks
for no realization at all. The other direction is needed only for the curve `C` itself, and there
`Schoenflies.PrePolygon.parity_eq_one_iff` supplies it. -/

/-- **The exhaustion clause of the polygonal crosscut theorem, at arbitrary cut points.** This is
`Schoenflies.CrosscutSplitsRegion`, the hypothesis `Schoenflies/FaceCyclesProof.lean` was left
with. -/
theorem crosscutSplitsRegion : CrosscutSplitsRegion := by
  intro J A₁ A₂ P Ω p q hJsep hJpoly hPpoly hA1 hA2 hunion hinter hParc hPJ hΩ hPsub z hz
  have hpq : p ≠ q := hA1.ne
  have hpJ : p ∈ J := by rw [← hunion]; exact Or.inl hA1.left_mem
  have hqJ : q ∈ J := by rw [← hunion]; exact Or.inl hA1.right_mem
  -- 1. Present the curve with the two cut points among its vertices.
  obtain ⟨m, C, a, k, hcar, hva, hvb, hk1, hk2⟩ :=
    exists_prePolygon_split hJsep.isJordanCurve hJpoly hpJ hqJ hpq
  have hk3 : k ≤ m + 3 := by omega
  have hDunion : C.arc a k ∪ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = J := by
    rw [C.arc_union a hk3, hcar]
  have hDinter : C.arc a k ∩ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = {p, q} := by
    rw [C.arc_inter a hk1 hk2, hva, hvb]
  have hD1n : ¬ C.arc a k ⊆ ({p, q} : Set Plane) := by
    rw [← hva, ← hvb]; exact C.arc_not_subset_endpoints a hk1 hk2
  have hD2n : ¬ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ⊆ ({p, q} : Set Plane) := by
    have h := C.arc_not_subset_endpoints (a + (k : ZMod (m + 3))) (k := m + 3 - k)
      (by omega) (by omega)
    rw [zmod_add_sub_cancel hk3 a, hva, hvb, Set.pair_comm q p] at h
    exact h
  -- 2. The two arcs of the presentation are the two given arcs.
  have hids := two_arcs_unique_of_isClosed hunion hinter hDunion hDinter hA1 hA2
    (C.isCompact_arc a k).isClosed (C.isCompact_arc _ _).isClosed hD1n hD2n
  have harc1 : IsArcBetween (C.arc a k) p q := by
    rcases hids with ⟨e1, -⟩ | ⟨-, e2⟩
    · exact e1 ▸ hA1
    · exact e2 ▸ hA2
  have harc2 : IsArcBetween (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k)) p q := by
    rcases hids with ⟨-, e2⟩ | ⟨e1, -⟩
    · exact e2 ▸ hA2
    · exact e1 ▸ hA1
  have hD1J : C.arc a k ⊆ J := by rw [← hcar]; exact C.arc_subset_carrier a k
  have hD2J : C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ⊆ J := by
    rw [← hcar]; exact C.arc_subset_carrier _ _
  have hpqD1 : ({p, q} : Set Plane) ⊆ C.arc a k := by
    rw [← hDinter]; exact Set.inter_subset_left
  have hpqD2 : ({p, q} : Set Plane) ⊆ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) := by
    rw [← hDinter]; exact Set.inter_subset_right
  -- 3. The crosscut, as a vertex list in each direction and as an edge list.
  obtain ⟨ws, hwsne, hwhead, hwlast, hwpoly⟩ := hParc.exists_poly_eq hPpoly hpq
  obtain ⟨ws', hwsne', hwhead', hwlast', hwpoly'⟩ := hParc.reverse.exists_poly_eq hPpoly hpq.symm
  have hKcover : cover (segsOf ws) = P := by
    rw [cover_segsOf_eq (a := p) (b := q) (by rw [hwpoly]; exact hParc.left_mem)
      (by rw [hwpoly]; exact hParc.right_mem) hpq, hwpoly]
  have hKchain : IsChainFrom (segsOf ws) p q := by
    have h := isChainFrom_segsOf ws hwsne
    rwa [hwhead, hwlast] at h
  -- 4. The two curves of the split are separating.
  have hpolyD1P : IsPolygonal (C.arc a k ∪ P) :=
    ⟨C.arcList a k ++ ws', by
      rw [poly_append_of_eq (C.arcList_ne_nil a k) hwsne'
          (by rw [PrePolygon.getLast_arcList k C a, hvb, hwhead']),
        PrePolygon.poly_arcList_of_pos C a hk1, hwpoly']⟩
  have hpolyD2P : IsPolygonal (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) :=
    ⟨C.arcList (a + (k : ZMod (m + 3))) (m + 3 - k) ++ ws, by
      rw [poly_append_of_eq (C.arcList_ne_nil _ _) hwsne
          (by rw [PrePolygon.getLast_arcList (m + 3 - k) C _, zmod_add_sub_cancel hk3 a, hva,
            hwhead]),
        PrePolygon.poly_arcList_of_pos C _ (by omega : 1 ≤ m + 3 - k), hwpoly]⟩
  have hmeetP : ∀ (S : Set Plane), S ⊆ J → ∀ w ∈ S, w ∈ P → w = p ∨ w = q := by
    intro S hSJ w hw hwP
    have hmem : w ∈ ({p, q} : Set Plane) := by rw [← hPJ]; exact ⟨hwP, hSJ hw⟩
    simpa using hmem
  have hJ1 : IsSeparating (C.arc a k ∪ P) :=
    isSeparating_of_isJordanCurve (isJordanCurve_union harc1 hParc (hmeetP _ hD1J)) hpolyD1P
  have hJ2 : IsSeparating (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) :=
    isSeparating_of_isJordanCurve (isJordanCurve_union harc2 hParc (hmeetP _ hD2J)) hpolyD2P
  -- 5. A reference point in the region the crosscut does not enter.
  obtain ⟨Ω', hΩpair⟩ : ∃ Ω' : Set Plane, IsRegionPair J Ω Ω' := by
    rcases hΩ with h | h
    · exact ⟨outside J, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨inside J, Or.inr ⟨h, rfl⟩⟩
  obtain ⟨y, hy⟩ := (hΩpair.right.isConnected hJsep).nonempty
  have hyJ : y ∉ J := hΩpair.right.subset_compl hy
  have hnotP : ∀ w ∈ Ω', w ∉ P := by
    intro w hw hwP
    have hwJ : w ∉ J := hΩpair.right.subset_compl hw
    have hwpq : w ∉ ({p, q} : Set Plane) := by
      rintro (rfl | rfl)
      exacts [hwJ hpJ, hwJ hqJ]
    exact Set.disjoint_left.1 hΩpair.disjoint (hPsub ⟨hwP, hwpq⟩) hw
  have hΩ'sub : ∀ S : Set Plane, S ⊆ J → Ω' ⊆ (S ∪ P)ᶜ := by
    intro S hSJ w hw
    rintro (h | h)
    · exact hΩpair.right.subset_compl hw (hSJ h)
    · exact hnotP w hw h
  have hyJ1 : y ∉ C.arc a k ∪ P := hΩ'sub _ hD1J hy
  have hyJ2 : y ∉ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P := hΩ'sub _ hD2J hy
  have hΩW1 : Ω' ⊆ connectedComponentIn (C.arc a k ∪ P)ᶜ y :=
    (hΩpair.right.isConnected hJsep).isPreconnected.subset_connectedComponentIn hy
      (hΩ'sub _ hD1J)
  have hΩW2 : Ω' ⊆
      connectedComponentIn (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P)ᶜ y :=
    (hΩpair.right.isConnected hJsep).isPreconnected.subset_connectedComponentIn hy
      (hΩ'sub _ hD2J)
  have heqΩ' : connectedComponentIn Jᶜ y = Ω' := hΩpair.right.connectedComponentIn_eq hJsep hy
  -- 6. Lemma 2.6: the two cells are components of `Ω ∖ P`.
  obtain ⟨⟨-, hV1comp⟩, ⟨-, hV2comp⟩, -, -, -⟩ :=
    crosscut_cells hJsep hJ1 hJ2 hD1J hD2J (by rw [hPJ]; exact hpqD1) (by rw [hPJ]; exact hpqD2)
      (arcs_ne (le_of_eq hDinter) hD1n) hΩpair (hJ1.isRegionPair_farRegion hyJ1) hΩW1
      (hJ2.isRegionPair_farRegion hyJ2) hΩW2
  -- 7. Exhaustion, by Lemma 2.7 and the two values of Theorem 2.3.
  obtain ⟨u, hu, hlev⟩ := exists_direction_hgt_ne (C.pieces ++ segsOf ws) (by
    intro Q hQ
    rcases List.mem_append.1 hQ with h | h
    · exact C.pieces_nondeg Q h
    · exact segsOf_nondeg ws Q h)
  have hlevC : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2 :=
    fun Q hQ => hlev Q (List.mem_append_left _ hQ)
  have hlevK : ∀ Q ∈ segsOf ws, hgt u Q.1 ≠ hgt u Q.2 :=
    fun Q hQ => hlev Q (List.mem_append_right _ hQ)
  have hlev1 : ∀ Q ∈ C.arcPieces a k ++ segsOf ws, hgt u Q.1 ≠ hgt u Q.2 :=
    hgt_ne_append (PrePolygon.arcPieces_hgt_ne hlevC) hlevK
  have hlev2 : ∀ Q ∈ C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws,
      hgt u Q.1 ≠ hgt u Q.2 := hgt_ne_append (PrePolygon.arcPieces_hgt_ne hlevC) hlevK
  have hchain1 : IsChainFrom (C.arcPieces a k) p q := by
    have h := C.isChainFrom_arcPieces a k
    rwa [hva, hvb] at h
  have hchain2 : IsChainFrom (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k)) q p := by
    have h := C.isChainFrom_arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k)
    rw [zmod_add_sub_cancel hk3 a] at h
    rwa [hva, hvb] at h
  have hclosed1 : IsClosedChain (C.arcPieces a k ++ segsOf ws) :=
    hchain1.isClosedChain_append hKchain
  have hclosed2 : IsClosedChain
      (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) :=
    isChainFrom_self_iff.1 (hchain2.append hKchain)
  have hcov1 : cover (C.arcPieces a k ++ segsOf ws) = C.arc a k ∪ P := by
    rw [cover_append, hKcover]
    rfl
  have hcov2 : cover (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws)
      = C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P := by
    rw [cover_append, hKcover]
    rfl
  have hsplit : ∀ w : Plane,
      parity u (C.arcPieces a k ++ segsOf ws) w
        + parity u (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) w
        = parity u C.pieces w :=
    fun w => parity_split u (C.sameEdges_arcPieces_split a hk3) (List.Perm.refl _)
      (List.Perm.refl _) w
  have hexh : ∀ w ∈ Ω \ P, w ∈ farRegion (C.arc a k ∪ P) y ∨
      w ∈ farRegion (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) y := by
    intro w hw
    by_contra hcon
    push Not at hcon
    obtain ⟨hn1, hn2⟩ := hcon
    have hwJ : w ∉ J := hΩ.subset_compl hw.1
    have hw1 : w ∉ C.arc a k ∪ P := by
      rintro (h | h)
      · exact hwJ (hD1J h)
      · exact hw.2 h
    have hw2 : w ∉ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P := by
      rintro (h | h)
      · exact hwJ (hD2J h)
      · exact hw.2 h
    have hmem1 : w ∈ connectedComponentIn (C.arc a k ∪ P)ᶜ y := by
      by_contra hc1
      exact hn1 ⟨hw1, hc1⟩
    have hmem2 : w ∈
        connectedComponentIn (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P)ᶜ y := by
      by_contra hc2
      exact hn2 ⟨hw2, hc2⟩
    have hp1 : parity u (C.arcPieces a k ++ segsOf ws) w
        = parity u (C.arcPieces a k ++ segsOf ws) y :=
      parity_eq_of_mem_connectedComponentIn hu hlev1 hclosed1 (by rw [hcov1]; exact hyJ1)
        (by rw [hcov1]; exact hmem1)
    have hp2 : parity u (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) w
        = parity u (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) y :=
      parity_eq_of_mem_connectedComponentIn hu hlev2 hclosed2 (by rw [hcov2]; exact hyJ2)
        (by rw [hcov2]; exact hmem2)
    have hkey : parity u C.pieces w = parity u C.pieces y := by
      rw [← hsplit w, ← hsplit y, hp1, hp2]
    rcases hΩpair with ⟨hin, hout⟩ | ⟨hout, hin⟩
    · rw [C.parity_eq_one_of_mem_inside hu hlevC
          (show w ∈ inside C.carrier by rw [hcar]; exact hin ▸ hw.1),
        C.parity_eq_zero_of_mem_outside hu hlevC
          (show y ∈ outside C.carrier by rw [hcar]; exact hout ▸ hy)] at hkey
      exact absurd hkey (by decide)
    · rw [C.parity_eq_zero_of_mem_outside hu hlevC
          (show w ∈ outside C.carrier by rw [hcar]; exact hout ▸ hw.1),
        C.parity_eq_one_of_mem_inside hu hlevC
          (show y ∈ inside C.carrier by rw [hcar]; exact hin ▸ hy)] at hkey
      exact absurd hkey (by decide)
  -- 8. Read the conclusion off the identification of the two arcs.
  rcases hids with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rcases hexh z hz with hv | hv
    · exact Or.inl (by rw [e1, hV1comp z hv]; exact hJ1.isRegionOf_farRegion hyJ1)
    · exact Or.inr (by rw [e2, hV2comp z hv]; exact hJ2.isRegionOf_farRegion hyJ2)
  · rcases hexh z hz with hv | hv
    · exact Or.inr (by rw [e2, hV1comp z hv]; exact hJ1.isRegionOf_farRegion hyJ1)
    · exact Or.inl (by rw [e1, hV2comp z hv]; exact hJ2.isRegionOf_farRegion hyJ2)

end Schoenflies

namespace Graph

open scoped Graph

open Schoenflies

variable {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane} {a b : Plane}

/-! ## `lem:face-cycles`, with nothing assumed

`Graph.IsDrawing.hasFaceCycles_union` and `Graph.face_cycles` of
`Schoenflies/FaceCyclesProof.lean` carry the hypothesis `Schoenflies.CrosscutSplitsRegion`;
`Schoenflies.crosscutSplitsRegion` above proves it, so here are the two statements with the
hypothesis discharged. **These are the forms a consumer should use.** Once this module's
`PrePolygon` development is hoisted above `Schoenflies/FaceCyclesProof.lean` the hypothesis can
be deleted from the originals and the primes here dropped. -/

/-- **One ear**, with no hypothesis assumed: `Graph.IsDrawing.hasFaceCycles_union` with
`Schoenflies.CrosscutSplitsRegion` discharged. -/
theorem IsDrawing.hasFaceCycles_union' [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g))
    (hBG : B ≤ G) (hmot : HasFaceCycles B drawing) {D' : List β}
    (hpath : G.IsPath a D' b) (hab : a ≠ b) (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hint : ∀ y ∈ G.walkVertices a D', y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D', g ∉ E(B)) :
    HasFaceCycles (B.union (G.pathGraphOf a D')) drawing :=
  h.hasFaceCycles_union crosscutSplitsRegion hpoly hBG hmot hpath hab ha hb hint hnew

/-- **`lem:face-cycles` (face cycles).** Every face of a finite 2-connected polygonal plane graph
has a cycle as its boundary and is one of the two complementary regions of that cycle.

This is `Graph.face_cycles` with its hypothesis `Schoenflies.CrosscutSplitsRegion` discharged by
`Schoenflies.crosscutSplitsRegion`; nothing is assumed. -/
theorem face_cycles' [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g)) (hG : G.IsTwoConnected) :
    HasFaceCycles G drawing :=
  face_cycles crosscutSplitsRegion h hpoly hG

/-- **Every bounded face is the interior of its boundary cycle.** -/
theorem IsFaceCycle.eq_inside_of_isBounded' {z : Plane} {e : β} {u v : Plane} {D : List β}
    (hf : IsFaceCycle G drawing z e u v D)
    (hbdd : Bornology.IsBounded (face G drawing z)) :
    face G drawing z = Schoenflies.inside (edgesCover drawing (e :: D)) :=
  hf.eq_inside_of_isBounded hbdd

end Graph
