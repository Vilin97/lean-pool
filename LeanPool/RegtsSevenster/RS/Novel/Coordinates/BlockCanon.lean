/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CanonPerm
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BlockAlign
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OddListMultiset

/-!
# The block data in canonical form

The colour-data extractors evaluated at the blocks of the flipped
data colouring: the even multiset is the Definition 5 even-colour
multiset at the block's vertex, and the odd list carries the
Definition 5 odd values.
-/

namespace RS

open Finset

variable {k ℓ : ℕ}

private theorem getRight_congr' {γ δ : Type*} {x y : γ ⊕ δ}
    (h : x = y) (hx : x.isRight = true)
    (hy : y.isRight = true) :
    x.getRight hx = y.getRight hy := by subst h; rfl

private theorem getLeft_congr' {γ δ : Type*} {x y : γ ⊕ δ}
    (h : x = y) (hx : x.isLeft = true)
    (hy : y.isLeft = true) :
    x.getLeft hx = y.getLeft hy := by subst h; rfl

/-- Bind a multiset through an all-`none` function. -/
private theorem filterMap_eq_zero {γ δ : Type*}
    (g : γ → Option δ) (m : Multiset γ)
    (h : ∀ x ∈ m, g x = none) :
    m.filterMap g = 0 := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.filterMap_cons,
      h a (Multiset.mem_cons_self a s),
      ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))]
    rfl

/-- Bind a multiset through an all-`some` function. -/
private theorem filterMap_eq_map_of_some {γ δ : Type*}
    (g : γ → Option δ) (g' : γ → δ) (m : Multiset γ)
    (h : ∀ x ∈ m, g x = some (g' x)) :
    m.filterMap g = m.map g' := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.filterMap_cons,
      h a (Multiset.mem_cons_self a s), Multiset.map_cons]
    rw [ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))]
    rw [show ((Option.map (fun b => ({b} : Multiset δ))
        (some (g' a))).getD 0) = {g' a} from rfl]
    rw [Multiset.singleton_add]

-- Raised budget: the list is rewritten through `filterMap` on the
-- universe multiset and split along the participating finset.
open Classical in
/-- **The odd list of a colouring over its participating slots**,
for any finset enumerating them. -/
theorem oddListOf_coe_multiset {d : ℕ}
    (c : MixedColouring k ℓ d) (s : Finset (Fin d))
    (hs : ∀ j, j ∈ s ↔ (c j).isRight = true) :
    (↑(oddListOf c) : Multiset (Fin (2 * ℓ))) =
      s.attach.val.map
        (fun j : {j : Fin d // j ∈ s} =>
          Sum.getRight (c j.val) ((hs j.val).mp j.prop)) := by
  rw [oddListOf, ← Multiset.filterMap_coe,
    ← Fin.univ_val_map, Multiset.filterMap_map]
  have hsplit : (Finset.univ : Finset (Fin d)).val =
      Multiset.filter (fun j => j ∈ s)
        (Finset.univ : Finset (Fin d)).val +
      Multiset.filter (fun j => ¬ j ∈ s)
        (Finset.univ : Finset (Fin d)).val :=
    (Multiset.filter_add_not _ _).symm
  rw [hsplit, Multiset.filterMap_add]
  have hfil : Multiset.filter (fun j => j ∈ s)
      (Finset.univ : Finset (Fin d)).val = s.val := by
    rw [← Finset.filter_val]
    refine congrArg Finset.val ?_
    ext j
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hzero : Multiset.filterMap (Sum.getRight? ∘ c)
      (Multiset.filter (fun j => ¬ j ∈ s)
        (Finset.univ : Finset (Fin d)).val) = 0 := by
    refine filterMap_eq_zero _ _ ?_
    intro x hx
    have hxs : ¬ x ∈ s := (Multiset.mem_filter.mp hx).2
    have hnr : ¬ (c x).isRight = true :=
      fun hr => hxs ((hs x).mpr hr)
    rcases hy : c x with a | u
    · change Sum.getRight? (c x) = none
      rw [hy]
      rfl
    · exact absurd (by rw [hy]; rfl) hnr
  rw [hfil, hzero, add_zero]
  rw [show s.val = s.attach.val.map Subtype.val from by
    rw [Finset.attach_val]
    exact (Multiset.attach_map_val _).symm]
  rw [Multiset.filterMap_map]
  refine filterMap_eq_map_of_some _ _ _ ?_
  intro j _
  have hr := (hs j.val).mp j.prop
  obtain ⟨u, hu⟩ : ∃ u, c j.val = Sum.inr u := by
    rcases hy : c j.val with a | u
    · rw [hy] at hr
      exact Bool.noConfusion hr
    · exact ⟨u, rfl⟩
  change Sum.getRight? (c j.val) =
    some (Sum.getRight (c j.val) hr)
  have h2 : Sum.getRight (c j.val) hr = u :=
    getRight_congr' hu hr rfl
  rw [h2, hu]
  rfl

-- As for the odd list, on the even side.
open Classical in
/-- **The even multiset of a colouring over its even slots**,
for any finset enumerating them. -/
theorem evenMultisetOf_coe {d : ℕ}
    (c : MixedColouring k ℓ d) (s : Finset (Fin d))
    (hs : ∀ j, j ∈ s ↔ (c j).isLeft = true) :
    evenMultisetOf c =
      s.attach.val.map
        (fun j : {j : Fin d // j ∈ s} =>
          Sum.getLeft (c j.val) ((hs j.val).mp j.prop)) := by
  rw [evenMultisetOf, ← Multiset.filterMap_coe,
    ← Fin.univ_val_map, Multiset.filterMap_map]
  have hsplit : (Finset.univ : Finset (Fin d)).val =
      Multiset.filter (fun j => j ∈ s)
        (Finset.univ : Finset (Fin d)).val +
      Multiset.filter (fun j => ¬ j ∈ s)
        (Finset.univ : Finset (Fin d)).val :=
    (Multiset.filter_add_not _ _).symm
  rw [hsplit, Multiset.filterMap_add]
  have hfil : Multiset.filter (fun j => j ∈ s)
      (Finset.univ : Finset (Fin d)).val = s.val := by
    rw [← Finset.filter_val]
    refine congrArg Finset.val ?_
    ext j
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hzero : Multiset.filterMap (Sum.getLeft? ∘ c)
      (Multiset.filter (fun j => ¬ j ∈ s)
        (Finset.univ : Finset (Fin d)).val) = 0 := by
    refine filterMap_eq_zero _ _ ?_
    intro x hx
    have hxs : ¬ x ∈ s := (Multiset.mem_filter.mp hx).2
    have hnl : ¬ (c x).isLeft = true :=
      fun hl => hxs ((hs x).mpr hl)
    rcases hy : c x with a | u
    · exact absurd (by rw [hy]; rfl) hnl
    · change Sum.getLeft? (c x) = none
      rw [hy]
      rfl
  rw [hfil, hzero, add_zero]
  rw [show s.val = s.attach.val.map Subtype.val from by
    rw [Finset.attach_val]
    exact (Multiset.attach_map_val _).symm]
  rw [Multiset.filterMap_map]
  refine filterMap_eq_map_of_some _ _ _ ?_
  intro j _
  have hl := (hs j.val).mp j.prop
  obtain ⟨a, ha⟩ : ∃ a, c j.val = Sum.inl a := by
    rcases hy : c j.val with a | u
    · exact ⟨a, rfl⟩
    · rw [hy] at hl
      exact Bool.noConfusion hl
  change Sum.getLeft? (c j.val) =
    some (Sum.getLeft (c j.val) hl)
  have h2 : Sum.getLeft (c j.val) hl = a :=
    getLeft_congr' ha hl rfl
  rw [h2, ha]
  rfl

/-- Participation of a flipped block slot is participation of its
flag. -/
theorem blockRestrict_colouringOfFlip_isRight
    (W : ClosedFragment) (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (ψ : F.EvenColouring k) (φ : F.OddColouring ℓ)
    (v : Fin (ds W).length) (j : Fin ((ds W).get v)) :
    (blockRestrict (ds W)
        (cSorted W (colouringOfFlip W F o ψ φ)) v j).isRight =
      true ↔ blockFlag W v j ∈ F.flags :=
  blockRestrict_colouringOf_isRight W F ψ _ v j

open Classical in
/-- **The block odd list is the Definition 5 odd list** (as
multisets). -/
theorem oddListOf_blockRestrict (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) (ψ : F.EvenColouring k)
    (φ : F.OddColouring ℓ) (v : Fin (ds W).length) :
    (↑(oddListOf (blockRestrict (ds W)
        (cSorted W (colouringOfFlip W F o ψ φ)) v)) :
      Multiset (Fin (2 * ℓ))) =
    ↑(F.oddListAt o φ (blockVertex W v)) := by
  rw [oddListOf_coe_multiset _ (oddSlots W F v)
    (fun j => (mem_oddSlots j).trans
      (blockRestrict_colouringOfFlip_isRight W F o ψ φ v
        j).symm)]
  rw [oddListAt_coe_multiset o φ (blockVertex W v)]
  refine Eq.trans (Multiset.map_congr rfl ?_)
    (Eq.trans (map_flagsAt_blockVertex W F v
      (fun f => if o.isOut f.val = true
        then oddPartner ℓ (φ.val f) else φ.val f)).symm ?_)
  · intro j _
    exact (getRight_congr'
      (blockRestrict_colouringOfFlip_mem W F o ψ φ v j.val
        (oddSlot_mem j)) _ rfl).trans rfl
  · refine congrArg (Multiset.map _) ?_
    refine congrArg Finset.val ?_
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in
/-- **The block even multiset is the Definition 5 even-colour
multiset.** -/
theorem evenMultisetOf_blockRestrict (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) (ψ : F.EvenColouring k)
    (φ : F.OddColouring ℓ) (v : Fin (ds W).length) :
    evenMultisetOf (blockRestrict (ds W)
        (cSorted W (colouringOfFlip W F o ψ φ)) v) =
    F.evenColoursAt ψ (blockVertex W v) := by
  rw [evenMultisetOf_coe _ (evenSlots W F v)
    (fun j => by
      rw [mem_evenSlots]
      constructor
      · intro h
        rw [blockRestrict_colouringOfFlip_not_mem W F o ψ φ
          v j h]
        rfl
      · intro h hmem
        rw [blockRestrict_colouringOfFlip_mem W F o ψ φ v j
          hmem] at h
        exact Bool.noConfusion h)]
  rw [evenColoursAt_blockVertex W F ψ v]
  refine Multiset.map_congr rfl ?_
  intro j _
  exact (getLeft_congr'
    (blockRestrict_colouringOfFlip_not_mem W F o ψ φ v j.val
      (blockSlot_not_mem j)) _ rfl).trans rfl

open Classical in
/-- The block odd finset is the Definition 5 odd set. -/
theorem oddFinsetOf_blockRestrict (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) (ψ : F.EvenColouring k)
    (φ : F.OddColouring ℓ) (v : Fin (ds W).length) :
    oddFinsetOf (blockRestrict (ds W)
        (cSorted W (colouringOfFlip W F o ψ φ)) v) =
    (F.oddListAt o φ (blockVertex W v)).toFinset := by
  rw [oddFinsetOf, ← List.toFinset_coe,
    oddListOf_blockRestrict W F o ψ φ v, List.toFinset_coe]

open Classical in
/-- The block odd list is duplicate-free iff the Definition 5
odd list is. -/
theorem oddListOf_blockRestrict_nodup_iff (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) (ψ : F.EvenColouring k)
    (φ : F.OddColouring ℓ) (v : Fin (ds W).length) :
    (oddListOf (blockRestrict (ds W)
        (cSorted W (colouringOfFlip W F o ψ φ)) v)).Nodup ↔
    (F.oddListAt o φ (blockVertex W v)).Nodup := by
  rw [← Multiset.coe_nodup, ← Multiset.coe_nodup,
    oddListOf_blockRestrict W F o ψ φ v]

/-- The cast rule for star coordinates. -/
theorem starCoord_cast {R : ℕ} (f : EdgeRankParameter R)
    (P : DelignePackage (SkeinObj f))
    (e' : P.ω.obj (SkeinObj.mk 1) ⟶ stdSuperPair k ℓ)
    {d₁ d₂ : ℕ} (h : d₁ = d₂)
    (c : MixedColouring k ℓ d₂) :
    starCoord f P e' d₁ (c ∘ finCongr h) =
      starCoord f P e' d₂ c := by
  subst h
  rfl

end RS
