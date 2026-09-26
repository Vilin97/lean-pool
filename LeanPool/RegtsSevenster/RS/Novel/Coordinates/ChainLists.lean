/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.GlobalSlotList

/-!
# The chain enumerations

The intermediate flag enumerations of the parity chain: the
edge-interleaved list, the oriented list, the matched list, and
the global pair concatenation.
-/

@[expose] public section

namespace RS

open Finset

variable {k ℓ : ℕ}

open Classical in
/-- The participating edges in edge order. -/
noncomputable def partEdges (W : ClosedFragment)
    (F : EdgeSubset W) : List (Fin (edgeCount W)) :=
  (edgeIndexSet W F).sort (· ≤ ·)

open Classical in
/-- Representative membership from edge participation. -/
theorem repMem_of_partEdge {W : ClosedFragment}
    {F : EdgeSubset W} {i : Fin (edgeCount W)}
    (hi : i ∈ edgeIndexSet W F) :
    (starFlagEnum W).symm
      (Fin.castAdd (edgeCount W) i) ∈ F.flags := by
  rw [edgeIndexSet, Finset.mem_filter] at hi
  exact hi.2

open Classical in
/-- Partner membership from edge participation. -/
theorem partnerMem_of_partEdge {W : ClosedFragment}
    {F : EdgeSubset W} {i : Fin (edgeCount W)}
    (hi : i ∈ edgeIndexSet W F) :
    (starFlagEnum W).symm
      (Fin.natAdd (edgeCount W) i) ∈ F.flags := by
  rw [← pairing_starFlagEnum_symm]
  exact F.pairing_mem _ (repMem_of_partEdge hi)

open Classical in
/-- **The edge-interleaved enumeration**: each participating edge
contributes its representative then its partner. -/
noncomputable def edgePairList (W : ClosedFragment)
    (F : EdgeSubset W) : List {f : W.Flag // f ∈ F.flags} :=
  ((partEdges W F).attachWith (· ∈ edgeIndexSet W F)
    (fun _ hi => (Finset.mem_sort _).mp hi)).flatMap
    (fun i => [⟨(starFlagEnum W).symm
        (Fin.castAdd (edgeCount W) i.val),
      repMem_of_partEdge i.prop⟩,
      ⟨(starFlagEnum W).symm
        (Fin.natAdd (edgeCount W) i.val),
      partnerMem_of_partEdge i.prop⟩])

open Classical in
/-- **The oriented enumeration**: each participating edge
contributes its incoming then its outgoing flag. -/
noncomputable def orientedPairList (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) : List {f : W.Flag // f ∈ F.flags} :=
  ((partEdges W F).attachWith (· ∈ edgeIndexSet W F)
    (fun _ hi => (Finset.mem_sort _).mp hi)).flatMap
    (fun i =>
      if o.isOut ((starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i.val)) = true then
        [⟨(starFlagEnum W).symm
            (Fin.natAdd (edgeCount W) i.val),
          partnerMem_of_partEdge i.prop⟩,
          ⟨(starFlagEnum W).symm
            (Fin.castAdd (edgeCount W) i.val),
          repMem_of_partEdge i.prop⟩]
      else
        [⟨(starFlagEnum W).symm
            (Fin.castAdd (edgeCount W) i.val),
          repMem_of_partEdge i.prop⟩,
          ⟨(starFlagEnum W).symm
            (Fin.natAdd (edgeCount W) i.val),
          partnerMem_of_partEdge i.prop⟩])

open Classical in
/-- **The matched enumeration**: each participating edge
contributes its incoming flag then that flag's match. -/
noncomputable def matchedPairList (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) : List {f : W.Flag // f ∈ F.flags} :=
  ((partEdges W F).attachWith (· ∈ edgeIndexSet W F)
    (fun _ hi => (Finset.mem_sort _).mp hi)).flatMap
    (fun i =>
      if o.isOut ((starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i.val)) = true then
        [⟨(starFlagEnum W).symm
            (Fin.natAdd (edgeCount W) i.val),
          partnerMem_of_partEdge i.prop⟩,
          ⟨κ.match_ ((starFlagEnum W).symm
            (Fin.natAdd (edgeCount W) i.val)),
          κ.match_mem _ (partnerMem_of_partEdge i.prop)⟩]
      else
        [⟨(starFlagEnum W).symm
            (Fin.castAdd (edgeCount W) i.val),
          repMem_of_partEdge i.prop⟩,
          ⟨κ.match_ ((starFlagEnum W).symm
            (Fin.castAdd (edgeCount W) i.val)),
          κ.match_mem _ (repMem_of_partEdge i.prop)⟩])

open Classical in
/-- **The global pair enumeration**: the vertex pair
enumerations in block order. -/
noncomputable def globalPairList (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) : List {f : W.Flag // f ∈ F.flags} :=
  (List.finRange (ds W).length).flatMap
    (fun v => pairFlagList (F := F) o (blockVertex W v))

/-- `blockVertex W` is injective. -/
theorem blockVertex_injective' (W : ClosedFragment) :
    Function.Injective (blockVertex W) := by
  intro v₁ v₂ h
  unfold blockVertex at h
  have h1 := (Fintype.equivFin W.Vertex).symm.injective h
  exact (finCongr (degList_length (starAssignEnum W))).injective h1

/-- `blockVertex W` is surjective. -/
theorem blockVertex_surjective' (W : ClosedFragment) :
    Function.Surjective (blockVertex W) := by
  intro v₀
  exact ⟨(finCongr (degList_length (starAssignEnum W))).symm
    (Fintype.equivFin W.Vertex v₀), by
    rw [blockVertex, _root_.Equiv.apply_symm_apply,
      _root_.Equiv.symm_apply_apply]⟩

end RS
