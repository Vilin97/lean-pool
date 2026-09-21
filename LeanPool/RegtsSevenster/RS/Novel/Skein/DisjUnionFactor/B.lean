/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.DisjUnionFactor.A

/-!
# The disjoint union: colour and value splitting

The colouring sum and the through-summand of a union split into
the two components.
-/

namespace RS

open scoped Classical

section ColourSplit

open EdgeSubset

variable {α β : Type} {W₁ : Fragment α} {W₂ : Fragment β}
  {F : EdgeSubset (W₁.disjUnion W₂)}

private theorem notmem_left {g : W₁.Flag}
    (hg : (Sum.inl g : (W₁.disjUnion W₂).Flag) ∉ F.flags) :
    g ∉ (leftSub F).flags :=
  fun h => hg (mem_leftSub_flags.mp h)

private theorem notmem_left' {g : W₁.Flag}
    (hg : g ∉ (leftSub F).flags) :
    (Sum.inl g : (W₁.disjUnion W₂).Flag) ∉ F.flags :=
  fun h => hg (mem_leftSub_flags.mpr h)

private theorem notmem_right {g : W₂.Flag}
    (hg : (Sum.inr g : (W₁.disjUnion W₂).Flag) ∉ F.flags) :
    g ∉ (rightSub F).flags :=
  fun h => hg (mem_rightSub_flags.mp h)

private theorem notmem_right' {g : W₂.Flag}
    (hg : g ∉ (rightSub F).flags) :
    (Sum.inr g : (W₁.disjUnion W₂).Flag) ∉ F.flags :=
  fun h => hg (mem_rightSub_flags.mpr h)

/-! ### Joining even colourings -/

private noncomputable def joinEvenVal {k : ℕ}
    (ψ₁ : (leftSub F).EvenColouring k)
    (ψ₂ : (rightSub F).EvenColouring k) :
    {f : (W₁.disjUnion W₂).Flag // f ∉ F.flags} → Fin k :=
  fun f => match f with
  | ⟨Sum.inl g, hg⟩ => ψ₁.val ⟨g, notmem_left hg⟩
  | ⟨Sum.inr g, hg⟩ => ψ₂.val ⟨g, notmem_right hg⟩

private theorem joinEvenVal_inl {k : ℕ}
    (ψ₁ : (leftSub F).EvenColouring k)
    (ψ₂ : (rightSub F).EvenColouring k) (g : W₁.Flag)
    (hg : (Sum.inl g : (W₁.disjUnion W₂).Flag) ∉ F.flags)
    (hg' : g ∉ (leftSub F).flags) :
    joinEvenVal ψ₁ ψ₂ ⟨Sum.inl g, hg⟩ = ψ₁.val ⟨g, hg'⟩ := rfl

private theorem joinEvenVal_inr {k : ℕ}
    (ψ₁ : (leftSub F).EvenColouring k)
    (ψ₂ : (rightSub F).EvenColouring k) (g : W₂.Flag)
    (hg : (Sum.inr g : (W₁.disjUnion W₂).Flag) ∉ F.flags)
    (hg' : g ∉ (rightSub F).flags) :
    joinEvenVal ψ₁ ψ₂ ⟨Sum.inr g, hg⟩ = ψ₂.val ⟨g, hg'⟩ := rfl

private noncomputable def joinEven {k : ℕ}
    (ψ₁ : (leftSub F).EvenColouring k)
    (ψ₂ : (rightSub F).EvenColouring k) : F.EvenColouring k :=
  ⟨joinEvenVal ψ₁ ψ₂, by
    rintro ⟨f, hf⟩
    cases f with
    | inl g =>
      have hgL : g ∉ (leftSub F).flags := notmem_left hf
      exact ((joinEvenVal_inl ψ₁ ψ₂ (W₁.pairing g)
          (F.pairing_not_mem hf)
          ((leftSub F).pairing_not_mem hgL)).trans
        (ψ₁.prop ⟨g, hgL⟩)).trans
        (joinEvenVal_inl ψ₁ ψ₂ g hf hgL).symm
    | inr g =>
      have hgR : g ∉ (rightSub F).flags := notmem_right hf
      exact ((joinEvenVal_inr ψ₁ ψ₂ (W₂.pairing g)
          (F.pairing_not_mem hf)
          ((rightSub F).pairing_not_mem hgR)).trans
        (ψ₂.prop ⟨g, hgR⟩)).trans
        (joinEvenVal_inr ψ₁ ψ₂ g hf hgR).symm⟩

private noncomputable def joinEvenEquiv
    (F : EdgeSubset (W₁.disjUnion W₂)) (k : ℕ) :
    ((leftSub F).EvenColouring k × (rightSub F).EvenColouring k) ≃
      F.EvenColouring k where
  toFun p := joinEven p.1 p.2
  invFun ψ :=
    (⟨fun g => ψ.val ⟨Sum.inl g.val, notmem_left' g.prop⟩,
      fun g => by
        exact ψ.prop ⟨Sum.inl g.val, notmem_left' g.prop⟩⟩,
     ⟨fun g => ψ.val ⟨Sum.inr g.val, notmem_right' g.prop⟩,
      fun g => by
        exact ψ.prop ⟨Sum.inr g.val, notmem_right' g.prop⟩⟩)
  left_inv p := by
    refine Prod.ext ?_ ?_
    · exact Subtype.ext (funext fun g => rfl)
    · exact Subtype.ext (funext fun g => rfl)
  right_inv ψ := by
    refine Subtype.ext (funext fun f => ?_)
    rcases f with ⟨f, hf⟩
    cases f <;> rfl

/-! ### Joining core odd colourings -/

private noncomputable def joinCoreVal {ℓ : ℕ}
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) :
    {f : (W₁.disjUnion W₂).Flag // f ∈ F.coreFlags} → Fin (2 * ℓ) :=
  fun f => match f with
  | ⟨Sum.inl g, hg⟩ => φ₁.val ⟨g, inl_mem_core.mp hg⟩
  | ⟨Sum.inr g, hg⟩ => φ₂.val ⟨g, inr_mem_core.mp hg⟩

private theorem joinCoreVal_inl {ℓ : ℕ}
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) (g : W₁.Flag)
    (hg : (Sum.inl g : (W₁.disjUnion W₂).Flag) ∈ F.coreFlags)
    (hg' : g ∈ (leftSub F).coreFlags) :
    joinCoreVal φ₁ φ₂ ⟨Sum.inl g, hg⟩ = φ₁.val ⟨g, hg'⟩ := rfl

private theorem joinCoreVal_inr {ℓ : ℕ}
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) (g : W₂.Flag)
    (hg : (Sum.inr g : (W₁.disjUnion W₂).Flag) ∈ F.coreFlags)
    (hg' : g ∈ (rightSub F).coreFlags) :
    joinCoreVal φ₁ φ₂ ⟨Sum.inr g, hg⟩ = φ₂.val ⟨g, hg'⟩ := rfl

private noncomputable def joinCore {ℓ : ℕ}
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) :
    F.CoreOddColouring ℓ :=
  ⟨joinCoreVal φ₁ φ₂, by
    rintro ⟨f, hf⟩
    cases f with
    | inl g =>
      have hgL : g ∈ (leftSub F).coreFlags := inl_mem_core.mp hf
      exact ((joinCoreVal_inl φ₁ φ₂ (W₁.pairing g)
          (F.pairing_mem_coreFlags hf)
          ((leftSub F).pairing_mem_coreFlags hgL)).trans
        (φ₁.prop ⟨g, hgL⟩)).trans
        (joinCoreVal_inl φ₁ φ₂ g hf hgL).symm
    | inr g =>
      have hgR : g ∈ (rightSub F).coreFlags := inr_mem_core.mp hf
      exact ((joinCoreVal_inr φ₁ φ₂ (W₂.pairing g)
          (F.pairing_mem_coreFlags hf)
          ((rightSub F).pairing_mem_coreFlags hgR)).trans
        (φ₂.prop ⟨g, hgR⟩)).trans
        (joinCoreVal_inr φ₁ φ₂ g hf hgR).symm⟩

private noncomputable def joinCoreEquiv
    (F : EdgeSubset (W₁.disjUnion W₂)) (ℓ : ℕ) :
    ((leftSub F).CoreOddColouring ℓ ×
        (rightSub F).CoreOddColouring ℓ) ≃
      F.CoreOddColouring ℓ where
  toFun p := joinCore p.1 p.2
  invFun φ :=
    (⟨fun g => φ.val ⟨Sum.inl g.val, inl_mem_core.mpr g.prop⟩,
      fun g => by
        exact φ.prop ⟨Sum.inl g.val, inl_mem_core.mpr g.prop⟩⟩,
     ⟨fun g => φ.val ⟨Sum.inr g.val, inr_mem_core.mpr g.prop⟩,
      fun g => by
        exact φ.prop ⟨Sum.inr g.val, inr_mem_core.mpr g.prop⟩⟩)
  left_inv p := by
    refine Prod.ext ?_ ?_
    · exact Subtype.ext (funext fun g => rfl)
    · exact Subtype.ext (funext fun g => rfl)
  right_inv φ := by
    refine Subtype.ext (funext fun f => ?_)
    rcases f with ⟨f, hf⟩
    cases f <;> rfl

/-! ### Boundary-match transfer -/

private theorem genEvenBoundaryMatch_join {k ℓ : ℕ}
    {st : GenBoundaryState k ℓ (α ⊕ β)}
    (hbnd : genBoundarySubsetMatches (W₁.disjUnion W₂) F.flags st)
    (hbnd₁ : genBoundarySubsetMatches W₁ (leftSub F).flags
      (fun a => st (Sum.inl a)))
    (hbnd₂ : genBoundarySubsetMatches W₂ (rightSub F).flags
      (fun b => st (Sum.inr b)))
    (ψ₁ : (leftSub F).EvenColouring k)
    (ψ₂ : (rightSub F).EvenColouring k) :
    genEvenBoundaryMatch F st hbnd (joinEven ψ₁ ψ₂) ↔
      (genEvenBoundaryMatch (leftSub F) (fun a => st (Sum.inl a))
          hbnd₁ ψ₁ ∧
        genEvenBoundaryMatch (rightSub F) (fun b => st (Sum.inr b))
          hbnd₂ ψ₂) := by
  constructor
  · intro hm
    constructor
    · intro a c hst
      have h0 := hm (Sum.inl a) c hst
      exact (joinEvenVal_inl ψ₁ ψ₂ (W₁.boundaryFlag a)
        (genBoundaryFlag_not_mem_of_even hbnd (Sum.inl a) c hst)
        (genBoundaryFlag_not_mem_of_even hbnd₁ a c hst)).symm.trans h0
    · intro b c hst
      have h0 := hm (Sum.inr b) c hst
      exact (joinEvenVal_inr ψ₁ ψ₂ (W₂.boundaryFlag b)
        (genBoundaryFlag_not_mem_of_even hbnd (Sum.inr b) c hst)
        (genBoundaryFlag_not_mem_of_even hbnd₂ b c hst)).symm.trans h0
  · rintro ⟨h₁, h₂⟩ i c hst
    cases i with
    | inl a =>
      exact (joinEvenVal_inl ψ₁ ψ₂ (W₁.boundaryFlag a)
        (genBoundaryFlag_not_mem_of_even hbnd (Sum.inl a) c hst)
        (genBoundaryFlag_not_mem_of_even hbnd₁ a c hst)).trans
        (h₁ a c hst)
    | inr b =>
      exact (joinEvenVal_inr ψ₁ ψ₂ (W₂.boundaryFlag b)
        (genBoundaryFlag_not_mem_of_even hbnd (Sum.inr b) c hst)
        (genBoundaryFlag_not_mem_of_even hbnd₂ b c hst)).trans
        (h₂ b c hst)

private theorem coreOddBoundaryMatch_join {k ℓ : ℕ}
    {st : GenBoundaryState k ℓ (α ⊕ β)}
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) :
    F.coreOddBoundaryMatch st (joinCore φ₁ φ₂) ↔
      ((leftSub F).coreOddBoundaryMatch (fun a => st (Sum.inl a)) φ₁ ∧
        (rightSub F).coreOddBoundaryMatch (fun b => st (Sum.inr b))
          φ₂) := by
  constructor
  · intro hm
    constructor
    · intro a c hst hcore
      have h0 := hm (Sum.inl a) c hst (inl_mem_core.mpr hcore)
      exact (joinCoreVal_inl φ₁ φ₂ (W₁.boundaryFlag a)
        (inl_mem_core.mpr hcore) hcore).symm.trans h0
    · intro b c hst hcore
      have h0 := hm (Sum.inr b) c hst (inr_mem_core.mpr hcore)
      exact (joinCoreVal_inr φ₁ φ₂ (W₂.boundaryFlag b)
        (inr_mem_core.mpr hcore) hcore).symm.trans h0
  · rintro ⟨h₁, h₂⟩ i c hst hcore
    cases i with
    | inl a =>
      exact (joinCoreVal_inl φ₁ φ₂ (W₁.boundaryFlag a) hcore
        (inl_mem_core.mp hcore)).trans
        (h₁ a c hst (inl_mem_core.mp hcore))
    | inr b =>
      exact (joinCoreVal_inr φ₁ φ₂ (W₂.boundaryFlag b) hcore
        (inr_mem_core.mp hcore)).trans
        (h₂ b c hst (inr_mem_core.mp hcore))

/-! ### Even colour multisets at component vertices -/

private noncomputable def leftComplEmb
    (F : EdgeSubset (W₁.disjUnion W₂)) :
    {g : W₁.Flag // g ∉ (leftSub F).flags} ↪
      {f : (W₁.disjUnion W₂).Flag // f ∉ F.flags} :=
  ⟨fun g => ⟨Sum.inl g.val, notmem_left' g.prop⟩,
   fun _g _g' h =>
     Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))⟩

private noncomputable def rightComplEmb
    (F : EdgeSubset (W₁.disjUnion W₂)) :
    {g : W₂.Flag // g ∉ (rightSub F).flags} ↪
      {f : (W₁.disjUnion W₂).Flag // f ∉ F.flags} :=
  ⟨fun g => ⟨Sum.inr g.val, notmem_right' g.prop⟩,
   fun _g _g' h =>
     Subtype.ext (Sum.inr.inj (congrArg Subtype.val h))⟩

private theorem evenColours_aux_inl {k : ℕ}
    (ψ₁ : (leftSub F).EvenColouring k)
    (ψ₂ : (rightSub F).EvenColouring k) (v : W₁.Vertex)
    (S : Finset {f : (W₁.disjUnion W₂).Flag // f ∉ F.flags})
    (T : Finset {g : W₁.Flag // g ∉ (leftSub F).flags})
    (hS : ∀ x, x ∈ S ↔
      (W₁.disjUnion W₂).attach x.val = Sum.inl (Sum.inl v))
    (hT : ∀ y, y ∈ T ↔ W₁.attach y.val = Sum.inl v) :
    S.val.map (joinEven ψ₁ ψ₂).val = T.val.map ψ₁.val := by
  have hset : S = T.map (leftComplEmb F) := by
    ext x
    rw [hS x]
    constructor
    · intro hatt
      rcases x with ⟨f, hf⟩
      cases f with
      | inl g =>
        exact Finset.mem_map.mpr ⟨⟨g, notmem_left hf⟩,
          (hT _).mpr (attach_inl_eq_inl.mp hatt), Subtype.ext rfl⟩
      | inr g => exact absurd hatt attach_inr_ne_inl
    · intro hx
      obtain ⟨g, hg, hmap⟩ := Finset.mem_map.mp hx
      rw [← hmap]
      exact attach_inl_eq_inl.mpr ((hT g).mp hg)
  rw [hset, Finset.map_val, Multiset.map_map]
  exact Multiset.map_congr rfl fun g hg =>
    joinEvenVal_inl ψ₁ ψ₂ g.val (notmem_left' g.prop) g.prop

private theorem evenColours_aux_inr {k : ℕ}
    (ψ₁ : (leftSub F).EvenColouring k)
    (ψ₂ : (rightSub F).EvenColouring k) (v : W₂.Vertex)
    (S : Finset {f : (W₁.disjUnion W₂).Flag // f ∉ F.flags})
    (T : Finset {g : W₂.Flag // g ∉ (rightSub F).flags})
    (hS : ∀ x, x ∈ S ↔
      (W₁.disjUnion W₂).attach x.val = Sum.inl (Sum.inr v))
    (hT : ∀ y, y ∈ T ↔ W₂.attach y.val = Sum.inl v) :
    S.val.map (joinEven ψ₁ ψ₂).val = T.val.map ψ₂.val := by
  have hset : S = T.map (rightComplEmb F) := by
    ext x
    rw [hS x]
    constructor
    · intro hatt
      rcases x with ⟨f, hf⟩
      cases f with
      | inl g => exact absurd hatt attach_inl_ne_inr
      | inr g =>
        exact Finset.mem_map.mpr ⟨⟨g, notmem_right hf⟩,
          (hT _).mpr (attach_inr_eq_inr.mp hatt), Subtype.ext rfl⟩
    · intro hx
      obtain ⟨g, hg, hmap⟩ := Finset.mem_map.mp hx
      rw [← hmap]
      exact attach_inr_eq_inr.mpr ((hT g).mp hg)
  rw [hset, Finset.map_val, Multiset.map_map]
  exact Multiset.map_congr rfl fun g hg =>
    joinEvenVal_inr ψ₁ ψ₂ g.val (notmem_right' g.prop) g.prop

private theorem evenColoursAt_join_inl {k : ℕ}
    (ψ₁ : (leftSub F).EvenColouring k)
    (ψ₂ : (rightSub F).EvenColouring k) (v : W₁.Vertex) :
    F.evenColoursAt (joinEven ψ₁ ψ₂) (Sum.inl v) =
      (leftSub F).evenColoursAt ψ₁ v := by
  unfold EdgeSubset.evenColoursAt
  refine evenColours_aux_inl ψ₁ ψ₂ v _ _ ?_ ?_
  · intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  · intro y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]

private theorem evenColoursAt_join_inr {k : ℕ}
    (ψ₁ : (leftSub F).EvenColouring k)
    (ψ₂ : (rightSub F).EvenColouring k) (v : W₂.Vertex) :
    F.evenColoursAt (joinEven ψ₁ ψ₂) (Sum.inr v) =
      (rightSub F).evenColoursAt ψ₂ v := by
  unfold EdgeSubset.evenColoursAt
  refine evenColours_aux_inr ψ₁ ψ₂ v _ _ ?_ ?_
  · intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  · intro y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-! ### In-flag lists at component vertices -/

private theorem relInFlagsAt_join_perm_inl
    {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation) (v : W₁.Vertex) :
    (F.relInFlagsAt (prodOrient o₁ o₂) (Sum.inl v)).Perm
      (((leftSub F).relInFlagsAt o₁ v).map Sum.inl) := by
  letI := (W₁.disjUnion W₂).flagOrder
  letI := W₁.flagOrder
  letI := Classical.dec
  apply Multiset.coe_eq_coe.mp
  unfold EdgeSubset.relInFlagsAt
  refine Eq.trans (Finset.sort_eq _ _) ?_
  refine Eq.trans ?_ (Multiset.map_coe Sum.inl _)
  refine Eq.trans ?_
    (congrArg (Multiset.map Sum.inl) (Finset.sort_eq _ _)).symm
  refine (Multiset.Nodup.ext (Finset.nodup _)
    (Multiset.Nodup.map Sum.inl_injective (Finset.nodup _))).mpr ?_
  intro f
  constructor
  · intro hf
    have h := Finset.mem_filter.mp (Finset.mem_val.mp hf)
    cases f with
    | inl g =>
      refine Multiset.mem_map.mpr ⟨g, ?_, rfl⟩
      exact Finset.mem_val.mpr (Finset.mem_filter.mpr
        ⟨mem_leftSub_flags.mpr h.1,
          attach_inl_eq_inl.mp h.2.1, h.2.2⟩)
    | inr g =>
      exact absurd h.2.1 attach_inr_ne_inl
  · intro hf
    obtain ⟨g, hg, rfl⟩ := Multiset.mem_map.mp hf
    have h := Finset.mem_filter.mp (Finset.mem_val.mp hg)
    exact Finset.mem_val.mpr (Finset.mem_filter.mpr
      ⟨mem_leftSub_flags.mp h.1,
        attach_inl_eq_inl.mpr h.2.1, h.2.2⟩)

private theorem relInFlagsAt_join_perm_inr
    {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation) (v : W₂.Vertex) :
    (F.relInFlagsAt (prodOrient o₁ o₂) (Sum.inr v)).Perm
      (((rightSub F).relInFlagsAt o₂ v).map Sum.inr) := by
  letI := (W₁.disjUnion W₂).flagOrder
  letI := W₂.flagOrder
  letI := Classical.dec
  apply Multiset.coe_eq_coe.mp
  unfold EdgeSubset.relInFlagsAt
  refine Eq.trans (Finset.sort_eq _ _) ?_
  refine Eq.trans ?_ (Multiset.map_coe Sum.inr _)
  refine Eq.trans ?_
    (congrArg (Multiset.map Sum.inr) (Finset.sort_eq _ _)).symm
  refine (Multiset.Nodup.ext (Finset.nodup _)
    (Multiset.Nodup.map Sum.inr_injective (Finset.nodup _))).mpr ?_
  intro f
  constructor
  · intro hf
    have h := Finset.mem_filter.mp (Finset.mem_val.mp hf)
    cases f with
    | inl g =>
      exact absurd h.2.1 attach_inl_ne_inr
    | inr g =>
      refine Multiset.mem_map.mpr ⟨g, ?_, rfl⟩
      exact Finset.mem_val.mpr (Finset.mem_filter.mpr
        ⟨mem_rightSub_flags.mpr h.1,
          attach_inr_eq_inr.mp h.2.1, h.2.2⟩)
  · intro hf
    obtain ⟨g, hg, rfl⟩ := Multiset.mem_map.mp hf
    have h := Finset.mem_filter.mp (Finset.mem_val.mp hg)
    exact Finset.mem_val.mpr (Finset.mem_filter.mpr
      ⟨mem_rightSub_flags.mp h.1,
        attach_inr_eq_inr.mpr h.2.1, h.2.2⟩)

private theorem mem_internal_of_mem_map_inl
    {κ₁ : (leftSub F).RelTransitionSystem} {o₁ : κ₁.Orientation}
    {v : W₁.Vertex} {f : (W₁.disjUnion W₂).Flag}
    (hf : f ∈ ((leftSub F).relInFlagsAt o₁ v).map Sum.inl) :
    f ∈ F.internalFlags := by
  obtain ⟨g, hgl, rfl⟩ := List.mem_map.mp hf
  exact inl_mem_internal.mpr
    ((leftSub F).mem_internal_of_mem_relInFlagsAt hgl)

private theorem mem_internal_of_mem_map_inr
    {κ₂ : (rightSub F).RelTransitionSystem} {o₂ : κ₂.Orientation}
    {v : W₂.Vertex} {f : (W₁.disjUnion W₂).Flag}
    (hf : f ∈ ((rightSub F).relInFlagsAt o₂ v).map Sum.inr) :
    f ∈ F.internalFlags := by
  obtain ⟨g, hgl, rfl⟩ := List.mem_map.mp hf
  exact inr_mem_internal.mpr
    ((rightSub F).mem_internal_of_mem_relInFlagsAt hgl)

/-! ### `pmap` helpers (mirrors `MixedPartition`) -/

private theorem perm_pmap' {β' γ' : Type*} {p : β' → Prop}
    (f : ∀ b, p b → γ') {l₁ l₂ : List β'} (hp : l₁.Perm l₂) :
    ∀ (H₁ : ∀ b ∈ l₁, p b) (H₂ : ∀ b ∈ l₂, p b),
      (l₁.pmap f H₁).Perm (l₂.pmap f H₂) := by
  induction hp with
  | nil => exact fun _ _ => List.Perm.refl _
  | cons b _ ih => exact fun _ _ => List.Perm.cons _ (ih _ _)
  | swap x y l => exact fun _ _ => List.Perm.swap _ _ _
  | trans hp₁ _ ih₁ ih₂ =>
    exact fun H₁ H₂ =>
      (ih₁ H₁ (fun b hb => H₁ b (hp₁.mem_iff.mpr hb))).trans
        (ih₂ (fun b hb => H₁ b (hp₁.mem_iff.mpr hb)) H₂)

private theorem pmap_flatMap_congr' {β' β₁ β₂ γ' : Type*}
    {p₁ p₂ : β' → Prop} (f₁ : ∀ b, p₁ b → β₁) (f₂ : ∀ b, p₂ b → β₂)
    (G₁ : β₁ → List γ') (G₂ : β₂ → List γ') (l : List β')
    (H₁ : ∀ b ∈ l, p₁ b) (H₂ : ∀ b ∈ l, p₂ b)
    (hpt : ∀ b ∈ l, ∀ h₁ h₂, G₁ (f₁ b h₁) = G₂ (f₂ b h₂)) :
    (l.pmap f₁ H₁).flatMap G₁ = (l.pmap f₂ H₂).flatMap G₂ := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.pmap, List.flatMap_cons]
    rw [hpt a List.mem_cons_self _ _,
      ih _ _ (fun b hb => hpt b (List.mem_cons_of_mem _ hb))]

/-! ### Vertex-local core data at component vertices -/

private theorem coreOddSignFn_join_inl {ℓ : ℕ}
    {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) (g : W₁.Flag)
    (hg' : (Sum.inl g : (W₁.disjUnion W₂).Flag) ∈ F.internalFlags)
    (hg : g ∈ (leftSub F).internalFlags) :
    F.coreOddSignFn (prodRel κ₁ κ₂) (joinCore φ₁ φ₂)
        ⟨Sum.inl g, hg'⟩ =
      (leftSub F).coreOddSignFn κ₁ φ₁ ⟨g, hg⟩ := rfl

private theorem coreOddSignFn_join_inr {ℓ : ℕ}
    {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) (g : W₂.Flag)
    (hg' : (Sum.inr g : (W₁.disjUnion W₂).Flag) ∈ F.internalFlags)
    (hg : g ∈ (rightSub F).internalFlags) :
    F.coreOddSignFn (prodRel κ₁ κ₂) (joinCore φ₁ φ₂)
        ⟨Sum.inr g, hg'⟩ =
      (rightSub F).coreOddSignFn κ₂ φ₂ ⟨g, hg⟩ := rfl

private theorem coreOddPairFn_join_inl {ℓ : ℕ}
    {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) (g : W₁.Flag)
    (hg' : (Sum.inl g : (W₁.disjUnion W₂).Flag) ∈ F.internalFlags)
    (hg : g ∈ (leftSub F).internalFlags) :
    F.coreOddPairFn (prodRel κ₁ κ₂) (joinCore φ₁ φ₂)
        ⟨Sum.inl g, hg'⟩ =
      (leftSub F).coreOddPairFn κ₁ φ₁ ⟨g, hg⟩ := rfl

private theorem coreOddPairFn_join_inr {ℓ : ℕ}
    {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) (g : W₂.Flag)
    (hg' : (Sum.inr g : (W₁.disjUnion W₂).Flag) ∈ F.internalFlags)
    (hg : g ∈ (rightSub F).internalFlags) :
    F.coreOddPairFn (prodRel κ₁ κ₂) (joinCore φ₁ φ₂)
        ⟨Sum.inr g, hg'⟩ =
      (rightSub F).coreOddPairFn κ₂ φ₂ ⟨g, hg⟩ := rfl

private theorem coreOddSignAt_join_inl {ℓ : ℕ}
    {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation)
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) (v : W₁.Vertex) :
    F.coreOddSignAt (prodOrient o₁ o₂) (joinCore φ₁ φ₂)
        (Sum.inl v) =
      (leftSub F).coreOddSignAt o₁ φ₁ v := by
  unfold EdgeSubset.coreOddSignAt
  have hstep := perm_pmap' Subtype.mk
    (relInFlagsAt_join_perm_inl o₁ o₂ v)
    (fun _ hf => F.mem_internal_of_mem_relInFlagsAt hf)
    (fun _ hg => mem_internal_of_mem_map_inl hg)
  refine ((hstep.map (F.coreOddSignFn (prodRel κ₁ κ₂)
    (joinCore φ₁ φ₂))).prod_eq).trans (congrArg List.prod ?_)
  refine Eq.trans (List.map_pmap _) ?_
  refine Eq.trans (List.pmap_map _) ?_
  exact Eq.trans (List.pmap_congr_left _
    (fun a ha h₁ h₂ => coreOddSignFn_join_inl φ₁ φ₂ a h₁ h₂))
    (List.map_pmap _).symm

private theorem coreOddSignAt_join_inr {ℓ : ℕ}
    {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation)
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) (v : W₂.Vertex) :
    F.coreOddSignAt (prodOrient o₁ o₂) (joinCore φ₁ φ₂)
        (Sum.inr v) =
      (rightSub F).coreOddSignAt o₂ φ₂ v := by
  unfold EdgeSubset.coreOddSignAt
  have hstep := perm_pmap' Subtype.mk
    (relInFlagsAt_join_perm_inr o₁ o₂ v)
    (fun _ hf => F.mem_internal_of_mem_relInFlagsAt hf)
    (fun _ hg => mem_internal_of_mem_map_inr hg)
  refine ((hstep.map (F.coreOddSignFn (prodRel κ₁ κ₂)
    (joinCore φ₁ φ₂))).prod_eq).trans (congrArg List.prod ?_)
  refine Eq.trans (List.map_pmap _) ?_
  refine Eq.trans (List.pmap_map _) ?_
  exact Eq.trans (List.pmap_congr_left _
    (fun a ha h₁ h₂ => coreOddSignFn_join_inr φ₁ φ₂ a h₁ h₂))
    (List.map_pmap _).symm

private theorem evalOdd_coreOddListAt_join_inl {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (μ : Multiset (Fin k))
    {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation)
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) (v : W₁.Vertex) :
    h.evalOdd μ (F.coreOddListAt (prodOrient o₁ o₂)
        (joinCore φ₁ φ₂) (Sum.inl v)) =
      h.evalOdd μ ((leftSub F).coreOddListAt o₁ φ₁ v) := by
  unfold EdgeSubset.coreOddListAt
  have hstep := perm_pmap' Subtype.mk
    (relInFlagsAt_join_perm_inl o₁ o₂ v)
    (fun _ hf => F.mem_internal_of_mem_relInFlagsAt hf)
    (fun _ hg => mem_internal_of_mem_map_inl hg)
  have h1 := h.evalOdd_flatMap_perm μ
    (F.coreOddPairFn (prodRel κ₁ κ₂) (joinCore φ₁ φ₂))
    (fun _ => rfl) hstep []
  simp only [List.nil_append] at h1
  refine h1.trans (congrArg (h.evalOdd μ) ?_)
  refine Eq.trans (congrArg
    (fun l' => l'.flatMap
      (F.coreOddPairFn (prodRel κ₁ κ₂) (joinCore φ₁ φ₂)))
    (List.pmap_map _)) ?_
  exact pmap_flatMap_congr' _ _ _ _ _ _ _
    (fun a ha h₁ h₂ => coreOddPairFn_join_inl φ₁ φ₂ a h₁ h₂)

private theorem evalOdd_coreOddListAt_join_inr {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (μ : Multiset (Fin k))
    {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation)
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) (v : W₂.Vertex) :
    h.evalOdd μ (F.coreOddListAt (prodOrient o₁ o₂)
        (joinCore φ₁ φ₂) (Sum.inr v)) =
      h.evalOdd μ ((rightSub F).coreOddListAt o₂ φ₂ v) := by
  unfold EdgeSubset.coreOddListAt
  have hstep := perm_pmap' Subtype.mk
    (relInFlagsAt_join_perm_inr o₁ o₂ v)
    (fun _ hf => F.mem_internal_of_mem_relInFlagsAt hf)
    (fun _ hg => mem_internal_of_mem_map_inr hg)
  have h1 := h.evalOdd_flatMap_perm μ
    (F.coreOddPairFn (prodRel κ₁ κ₂) (joinCore φ₁ φ₂))
    (fun _ => rfl) hstep []
  simp only [List.nil_append] at h1
  refine h1.trans (congrArg (h.evalOdd μ) ?_)
  refine Eq.trans (congrArg
    (fun l' => l'.flatMap
      (F.coreOddPairFn (prodRel κ₁ κ₂) (joinCore φ₁ φ₂)))
    (List.pmap_map _)) ?_
  exact pmap_flatMap_congr' _ _ _ _ _ _ _
    (fun a ha h₁ h₂ => coreOddPairFn_join_inr φ₁ φ₂ a h₁ h₂)

/-! ### The colouring-sum factorization -/

private theorem joinEvenEquiv_apply {k : ℕ}
    (ψ₁ : (leftSub F).EvenColouring k)
    (ψ₂ : (rightSub F).EvenColouring k) :
    joinEvenEquiv F k (ψ₁, ψ₂) = joinEven ψ₁ ψ₂ := rfl

private theorem joinCoreEquiv_apply {ℓ : ℕ}
    (φ₁ : (leftSub F).CoreOddColouring ℓ)
    (φ₂ : (rightSub F).CoreOddColouring ℓ) :
    joinCoreEquiv F ℓ (φ₁, φ₂) = joinCore φ₁ φ₂ := rfl

private theorem prod_vertex_split
    (X : (W₁.disjUnion W₂).Vertex → ℂ) :
    ∏ v : (W₁.disjUnion W₂).Vertex, X v =
      (∏ v : W₁.Vertex, X (Sum.inl v)) *
        ∏ v : W₂.Vertex, X (Sum.inr v) :=
  Fintype.prod_sum_type X

/-- **The colouring sum factors**: a colouring of the union is a
pair of componentwise colourings, and the summand is their
product. -/
theorem colouringSum_split {k ℓ : ℕ}
    (h : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ (α ⊕ β))
    (hbnd : genBoundarySubsetMatches (W₁.disjUnion W₂) F.flags st)
    (hbnd₁ : genBoundarySubsetMatches W₁ (leftSub F).flags
      (fun a => st (Sum.inl a)))
    (hbnd₂ : genBoundarySubsetMatches W₂ (rightSub F).flags
      (fun b => st (Sum.inr b)))
    {κ₁ : (leftSub F).RelTransitionSystem}
    {κ₂ : (rightSub F).RelTransitionSystem}
    (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation) :
    (∑ ψ : F.EvenColouring k,
      if genEvenBoundaryMatch F st hbnd ψ then
        (∑ φ : F.CoreOddColouring ℓ,
          if F.coreOddBoundaryMatch st φ then
            ∏ v : (W₁.disjUnion W₂).Vertex,
              ((F.coreOddSignAt (prodOrient o₁ o₂) φ v : ℂ) *
                h.evalOdd (F.evenColoursAt ψ v)
                  (F.coreOddListAt (prodOrient o₁ o₂) φ v))
          else 0)
      else 0) =
    (∑ ψ : (leftSub F).EvenColouring k,
      if genEvenBoundaryMatch (leftSub F) (fun a => st (Sum.inl a))
          hbnd₁ ψ then
        (∑ φ : (leftSub F).CoreOddColouring ℓ,
          if (leftSub F).coreOddBoundaryMatch
              (fun a => st (Sum.inl a)) φ then
            ∏ v : W₁.Vertex,
              (((leftSub F).coreOddSignAt o₁ φ v : ℂ) *
                h.evalOdd ((leftSub F).evenColoursAt ψ v)
                  ((leftSub F).coreOddListAt o₁ φ v))
          else 0)
      else 0) *
    (∑ ψ : (rightSub F).EvenColouring k,
      if genEvenBoundaryMatch (rightSub F) (fun b => st (Sum.inr b))
          hbnd₂ ψ then
        (∑ φ : (rightSub F).CoreOddColouring ℓ,
          if (rightSub F).coreOddBoundaryMatch
              (fun b => st (Sum.inr b)) φ then
            ∏ v : W₂.Vertex,
              (((rightSub F).coreOddSignAt o₂ φ v : ℂ) *
                h.evalOdd ((rightSub F).evenColoursAt ψ v)
                  ((rightSub F).coreOddListAt o₂ φ v))
          else 0)
      else 0) := by
  rw [← Equiv.sum_comp (joinEvenEquiv F k), Fintype.sum_prod_type,
    Fintype.sum_mul_sum]
  refine Finset.sum_congr rfl fun ψ₁ _ => ?_
  refine Finset.sum_congr rfl fun ψ₂ _ => ?_
  rw [joinEvenEquiv_apply]
  by_cases hP₁ : genEvenBoundaryMatch (leftSub F)
    (fun a => st (Sum.inl a)) hbnd₁ ψ₁
  · by_cases hP₂ : genEvenBoundaryMatch (rightSub F)
      (fun b => st (Sum.inr b)) hbnd₂ ψ₂
    · rw [if_pos ((genEvenBoundaryMatch_join hbnd hbnd₁ hbnd₂
          ψ₁ ψ₂).mpr ⟨hP₁, hP₂⟩), if_pos hP₁, if_pos hP₂]
      rw [← Equiv.sum_comp (joinCoreEquiv F ℓ),
        Fintype.sum_prod_type, Fintype.sum_mul_sum]
      refine Finset.sum_congr rfl fun φ₁ _ => ?_
      refine Finset.sum_congr rfl fun φ₂ _ => ?_
      rw [joinCoreEquiv_apply]
      by_cases hQ₁ : (leftSub F).coreOddBoundaryMatch
        (fun a => st (Sum.inl a)) φ₁
      · by_cases hQ₂ : (rightSub F).coreOddBoundaryMatch
          (fun b => st (Sum.inr b)) φ₂
        · rw [if_pos ((coreOddBoundaryMatch_join φ₁ φ₂).mpr
              ⟨hQ₁, hQ₂⟩), if_pos hQ₁, if_pos hQ₂]
          refine Eq.trans (prod_vertex_split _) ?_
          refine congrArg₂ (· * ·) ?_ ?_
          · refine Finset.prod_congr rfl fun v _ => ?_
            rw [coreOddSignAt_join_inl o₁ o₂ φ₁ φ₂ v,
              evenColoursAt_join_inl ψ₁ ψ₂ v,
              evalOdd_coreOddListAt_join_inl h _ o₁ o₂ φ₁ φ₂ v]
          · refine Finset.prod_congr rfl fun v _ => ?_
            rw [coreOddSignAt_join_inr o₁ o₂ φ₁ φ₂ v,
              evenColoursAt_join_inr ψ₁ ψ₂ v,
              evalOdd_coreOddListAt_join_inr h _ o₁ o₂ φ₁ φ₂ v]
        · rw [if_neg (fun hu => hQ₂
              ((coreOddBoundaryMatch_join φ₁ φ₂).mp hu).2),
            if_neg hQ₂, mul_zero]
      · rw [if_neg (fun hu => hQ₁
            ((coreOddBoundaryMatch_join φ₁ φ₂).mp hu).1),
          if_neg hQ₁, zero_mul]
    · rw [if_neg (fun hu => hP₂
          ((genEvenBoundaryMatch_join hbnd hbnd₁ hbnd₂
            ψ₁ ψ₂).mp hu).2),
        if_neg hP₂, mul_zero]
  · rw [if_neg (fun hu => hP₁
        ((genEvenBoundaryMatch_join hbnd hbnd₁ hbnd₂
          ψ₁ ψ₂).mp hu).1),
      if_neg hP₁, zero_mul]

end ColourSplit

/-! ## The subset-sum factorization -/

end RS
