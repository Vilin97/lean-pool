/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.PairEnum
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BlockData

/-!
# The two flag enumerations

The Definition 5 pair enumeration and the block-slot enumeration
are duplicate-free lists of the participating flags at a vertex:
the raw material for the canonical index permutation between them.
-/

namespace RS

open Classical Finset

section PairSide

variable {α : Type} {W : Fragment α} {F : EdgeSubset W}
  {κ : F.TransitionSystem}

/-- Members of the pair base are incoming flags. -/
theorem mem_pairBase {o : κ.Orientation} {v : W.Vertex}
    {f : {f : W.Flag // f ∈ F.flags}}
    (hf : f ∈ (F.inFlagsAt o v).attachWith (· ∈ F.flags)
      (fun _ hf' => F.mem_of_mem_inFlagsAt hf')) :
    f.val ∈ F.inFlagsAt o v := by
  rw [show (F.inFlagsAt o v).attachWith (· ∈ F.flags)
      (fun _ hf' => F.mem_of_mem_inFlagsAt hf') =
    (F.inFlagsAt o v).pmap Subtype.mk
      (fun _ hf' => F.mem_of_mem_inFlagsAt hf') from rfl]
    at hf
  obtain ⟨a, ha, hfa⟩ := List.mem_pmap.mp hf
  rw [← hfa]
  exact ha

/-- Incoming flags attach to their vertex. -/
theorem attach_of_mem_inFlagsAt {o : κ.Orientation}
    {v : W.Vertex} {f : W.Flag}
    (hf : f ∈ F.inFlagsAt o v) : W.attach f = Sum.inl v := by
  letI := W.flagOrder
  letI := Classical.dec
  unfold EdgeSubset.inFlagsAt at hf
  exact (Finset.mem_filter.mp
    ((Finset.mem_sort _).mp hf)).2.1

/-- **The pair enumeration is duplicate-free.** -/
theorem pairFlagList_nodup (o : κ.Orientation) (v : W.Vertex) :
    (pairFlagList (F := F) o v).Nodup := by
  rw [pairFlagList, List.nodup_flatMap]
  constructor
  · intro f _
    refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
    intro hmem
    rw [List.mem_singleton] at hmem
    have hval : f.val = κ.match_ f.val :=
      congrArg Subtype.val hmem
    exact κ.match_ne f.val f.prop hval.symm
  · have hnodup : ((F.inFlagsAt o v).attachWith (· ∈ F.flags)
        (fun _ hf' => F.mem_of_mem_inFlagsAt hf')).Nodup := by
      refine List.Nodup.pmap (fun a _ b _ h =>
        congrArg Subtype.val h) ?_
      letI := W.flagOrder
      letI := Classical.dec
      exact Finset.sort_nodup _ _
    refine List.Pairwise.imp_of_mem ?_
      (List.Pairwise.imp (fun {a b} h => h)
        hnodup)
    intro f₁ f₂ h₁ h₂ hne
    have hin₁ : o.isOut f₁.val = false :=
      isOut_of_mem_inFlagsAt o (mem_pairBase h₁)
    have hin₂ : o.isOut f₂.val = false :=
      isOut_of_mem_inFlagsAt o (mem_pairBase h₂)
    intro x hx₁ hx₂
    rcases List.mem_cons.mp hx₁ with rfl | hx₁'
    · rcases List.mem_cons.mp hx₂ with h | hx₂'
      · exact hne h
      · rw [List.mem_singleton] at hx₂'
        have : o.isOut x.val = true := by
          rw [show x.val = κ.match_ f₂.val from
            congrArg Subtype.val hx₂']
          rw [o.match_flip f₂.val f₂.prop, hin₂]
          rfl
        rw [hin₁] at this
        exact Bool.noConfusion this
    · rw [List.mem_singleton] at hx₁'
      rcases List.mem_cons.mp hx₂ with rfl | hx₂'
      · have : o.isOut x.val = true := by
          rw [show x.val = κ.match_ f₁.val from
            congrArg Subtype.val hx₁']
          rw [o.match_flip f₁.val f₁.prop, hin₁]
          rfl
        rw [hin₂] at this
        exact Bool.noConfusion this
      · rw [List.mem_singleton] at hx₂'
        refine hne (Subtype.ext ?_)
        have hmm : κ.match_ f₁.val = κ.match_ f₂.val :=
          (congrArg Subtype.val hx₁').symm.trans
            (congrArg Subtype.val hx₂')
        have h1 := κ.match_invol f₁.val f₁.prop
        have h2 := κ.match_invol f₂.val f₂.prop
        rw [← h1, ← h2, hmm]

/-- **Membership in the pair enumeration** is attachment at the
vertex. -/
theorem mem_pairFlagList (o : κ.Orientation) (v : W.Vertex)
    (x : {f : W.Flag // f ∈ F.flags}) :
    x ∈ pairFlagList (F := F) o v ↔
      W.attach x.val = Sum.inl v := by
  rw [pairFlagList, List.mem_flatMap]
  constructor
  · rintro ⟨f, hf, hx⟩
    have hfin := mem_pairBase hf
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact attach_of_mem_inFlagsAt hfin
    · rw [List.mem_singleton] at hx'
      rw [show x.val = κ.match_ f.val from
        congrArg Subtype.val hx']
      exact κ.match_vertex f.val f.prop v
        (attach_of_mem_inFlagsAt hfin)
  · intro hatt
    by_cases hout : o.isOut x.val = true
    · set f₀ : {f : W.Flag // f ∈ F.flags} :=
        ⟨κ.match_ x.val, κ.match_mem _ x.prop⟩ with hf₀
      have hin₀ : o.isOut f₀.val = false := by
        show o.isOut (κ.match_ x.val) = false
        rw [o.match_flip x.val x.prop, hout]
        rfl
      have hatt₀ : W.attach f₀.val = Sum.inl v :=
        κ.match_vertex x.val x.prop v hatt
      have hmem₀ : f₀.val ∈ F.inFlagsAt o v :=
        mem_inFlagsAt_of f₀.prop hatt₀ hin₀
      refine ⟨f₀, ?_, ?_⟩
      · rw [show (F.inFlagsAt o v).attachWith (· ∈ F.flags)
            (fun _ hf' => F.mem_of_mem_inFlagsAt hf') =
          (F.inFlagsAt o v).pmap Subtype.mk
            (fun _ hf' => F.mem_of_mem_inFlagsAt hf')
          from rfl]
        exact List.mem_pmap.mpr ⟨f₀.val, hmem₀,
          Subtype.ext rfl⟩
      · refine List.mem_cons.mpr (Or.inr ?_)
        rw [List.mem_singleton]
        refine Subtype.ext ?_
        show x.val = κ.match_ f₀.val
        exact (κ.match_invol x.val x.prop).symm
    · have hin : o.isOut x.val = false := by
        cases hb : o.isOut x.val
        · rfl
        · exact absurd hb hout
      have hmem : x.val ∈ F.inFlagsAt o v :=
        mem_inFlagsAt_of x.prop hatt hin
      refine ⟨x, ?_, List.mem_cons_self⟩
      rw [show (F.inFlagsAt o v).attachWith (· ∈ F.flags)
          (fun _ hf' => F.mem_of_mem_inFlagsAt hf') =
        (F.inFlagsAt o v).pmap Subtype.mk
          (fun _ hf' => F.mem_of_mem_inFlagsAt hf')
        from rfl]
      exact List.mem_pmap.mpr ⟨x.val, hmem, Subtype.ext rfl⟩

end PairSide

section BlockSide

variable {k ℓ : ℕ}

open Classical in
/-- The block-slot enumeration: the participating slots of a
block in slot order, as flags. -/
noncomputable def blockOddFlagList (W : ClosedFragment)
    (F : EdgeSubset W) (v : Fin (ds W).length) :
    List {f : W.Flag // f ∈ F.flags} :=
  ((oddSlots W F v).sort (· ≤ ·)).pmap
    (fun j hj => ⟨blockFlag W v j, (mem_oddSlots j).mp hj⟩)
    (fun _ hj => (Finset.mem_sort _).mp hj)

open Classical in
/-- The block-slot enumeration is duplicate-free. -/
theorem blockOddFlagList_nodup (W : ClosedFragment)
    (F : EdgeSubset W) (v : Fin (ds W).length) :
    (blockOddFlagList W F v).Nodup := by
  refine List.Nodup.pmap ?_ (Finset.sort_nodup _ _)
  intro a _ b _ h
  have hv := congrArg
    (fun z : {f : W.Flag // f ∈ F.flags} => z.val) h
  exact blockFlag_injective W v hv

open Classical in
/-- Membership in the block-slot enumeration is attachment at
the block's vertex. -/
theorem mem_blockOddFlagList (W : ClosedFragment)
    (F : EdgeSubset W) (v : Fin (ds W).length)
    (x : {f : W.Flag // f ∈ F.flags}) :
    x ∈ blockOddFlagList W F v ↔
      W.attach x.val = Sum.inl (blockVertex W v) := by
  rw [blockOddFlagList]
  constructor
  · intro hx
    obtain ⟨j, _, hjx⟩ := List.mem_pmap.mp hx
    rw [show x.val = blockFlag W v j from
      (congrArg Subtype.val hjx).symm]
    rw [ClosedFragment.attach_eq_vertexOf, vertexOf_blockFlag]
  · intro hatt
    have hvtx : ClosedFragment.vertexOf W x.val =
        blockVertex W v :=
      Sum.inl.inj
        ((ClosedFragment.attach_eq_vertexOf W x.val).symm.trans
          hatt)
    have hmem : x.val ∈ Finset.univ.filter (fun g =>
        ClosedFragment.vertexOf W g = blockVertex W v) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hvtx⟩
    rw [← image_blockFlag, Finset.mem_image] at hmem
    obtain ⟨j, -, hj⟩ := hmem
    have hjodd : j ∈ oddSlots W F v := by
      rw [mem_oddSlots, hj]
      exact x.prop
    refine List.mem_pmap.mpr ⟨j, ?_, ?_⟩
    · rw [Finset.mem_sort]
      exact hjodd
    · exact Subtype.ext hj

open Classical in
/-- **The two enumerations list the same flags.** -/
theorem mem_blockOddFlagList_iff_pairFlagList
    (W : ClosedFragment) (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (v : Fin (ds W).length)
    (x : {f : W.Flag // f ∈ F.flags}) :
    x ∈ blockOddFlagList W F v ↔
      x ∈ pairFlagList (F := F) o (blockVertex W v) :=
  (mem_blockOddFlagList W F v x).trans
    (mem_pairFlagList o (blockVertex W v) x).symm

end BlockSide

end RS
