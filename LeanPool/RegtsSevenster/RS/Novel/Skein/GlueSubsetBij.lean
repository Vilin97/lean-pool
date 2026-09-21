/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueSplit

/-!
# Subset correspondence for single-pair gluing

The subset-level maps underlying the single-pair gluing
decomposition: lift and drop maps between flag subsets of a glued
fragment `W' = W.gluePair i j hij` and flag subsets of the
original fragment `W`.  Separate definitions and lemma sets for
the open case (the two glued boundary flags bound distinct edges,
unified by rewiring) and the closed case (they bound a common
edge, which closes into a free circle parameterized by a Bool).
-/

namespace RS

open scoped Classical

namespace Fragment

variable {α : Type}

/-! ### Drop map (common to both cases) -/

/-- Drop a flag set from `W` to the surviving flags of a glue at
`{i, j}`: keep only those flags distinct from both boundary
flags. -/
noncomputable def dropSubset (W : Fragment α) (i j : α)
    (s : Finset W.Flag) : Finset (SurvivingFlag W i j) :=
  s.subtype (fun f => f ≠ W.boundaryFlag i ∧ f ≠ W.boundaryFlag j)

/-- Membership in a dropped set is membership of the underlying
flag. -/
theorem mem_dropSubset {W : Fragment α} {i j : α}
    {s : Finset W.Flag} {f : SurvivingFlag W i j} :
    f ∈ W.dropSubset i j s ↔ f.val ∈ s :=
  Finset.mem_subtype

/-! ### Partner surviving flags (open case) -/

section OpenCase

variable {W : Fragment α} {i j : α}

/-- In the open case, the W-partner of boundary flag `i` is a
surviving flag (it is neither `boundaryFlag i` nor
`boundaryFlag j`). -/
def partnerSurvI
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j) :
    SurvivingFlag W i j :=
  ⟨W.pairing (W.boundaryFlag i),
   fun h => W.pairing_ne _ h,
   hopen⟩

/-- In the open case, the W-partner of boundary flag `j` is a
surviving flag. -/
def partnerSurvJ
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j) :
    SurvivingFlag W i j :=
  ⟨W.pairing (W.boundaryFlag j),
   fun h => hopen (W.pairing_boundaryFlag_comm h),
   fun h => W.pairing_ne _ h⟩

/-- The underlying flag of the first partner. -/
@[simp]
theorem partnerSurvI_val
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j) :
    (partnerSurvI hopen).val = W.pairing (W.boundaryFlag i) := rfl

/-- The underlying flag of the second partner. -/
@[simp]
theorem partnerSurvJ_val
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j) :
    (partnerSurvJ hopen).val = W.pairing (W.boundaryFlag j) :=
  rfl

/-- Lift a surviving-flag set to `W` in the open case: the image
under `Subtype.val`, together with boundary flag `i` iff its
W-partner participates, and boundary flag `j` iff its W-partner
participates. -/
noncomputable def liftSubsetOpen
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (s' : Finset (SurvivingFlag W i j)) : Finset W.Flag :=
  s'.image Subtype.val
    ∪ (if partnerSurvI hopen ∈ s' then {W.boundaryFlag i} else ∅)
    ∪ (if partnerSurvJ hopen ∈ s'
       then {W.boundaryFlag j} else ∅)

/-! #### Membership in the open-case lift -/

/-- The first glued boundary flag is not the image of any surviving
flag. -/
theorem boundaryFlagI_not_mem_image
    (s' : Finset (SurvivingFlag W i j)) :
    W.boundaryFlag i ∉ s'.image (Subtype.val) := by
  intro h
  obtain ⟨f, _, hf⟩ := Finset.mem_image.mp h
  exact f.prop.1 hf

/-- Nor is the second. -/
theorem boundaryFlagJ_not_mem_image
    (s' : Finset (SurvivingFlag W i j)) :
    W.boundaryFlag j ∉ s'.image (Subtype.val) := by
  intro h
  obtain ⟨f, _, hf⟩ := Finset.mem_image.mp h
  exact f.prop.2 hf

/-- On surviving flags an open lift is membership in the set it
lifts. -/
theorem surviving_val_mem_liftOpen_iff
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (s' : Finset (SurvivingFlag W i j))
    (f : SurvivingFlag W i j) :
    f.val ∈ liftSubsetOpen hopen s' ↔ f ∈ s' := by
  constructor
  · intro h
    rw [liftSubsetOpen, Finset.mem_union, Finset.mem_union] at h
    rcases h with (h | h) | h
    · rw [Finset.mem_image] at h
      obtain ⟨g, hg, hgv⟩ := h
      exact Subtype.ext hgv.symm ▸ hg
    · split_ifs at h with hp
      · exact absurd (Finset.mem_singleton.mp h) f.prop.1
      · simp at h
    · split_ifs at h with hp
      · exact absurd (Finset.mem_singleton.mp h) f.prop.2
      · simp at h
  · intro h
    rw [liftSubsetOpen]
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ h))

/-- The open lift carries the first glued boundary flag exactly
when the set carries its partner: rewiring joins the two edges into
one, so their flags stand or fall together. -/
theorem boundaryFlagI_mem_liftOpen_iff
    (hij : i ≠ j)
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (s' : Finset (SurvivingFlag W i j)) :
    W.boundaryFlag i ∈ liftSubsetOpen hopen s' ↔
      partnerSurvI hopen ∈ s' := by
  constructor
  · intro h
    rw [liftSubsetOpen, Finset.mem_union, Finset.mem_union] at h
    rcases h with (h | h) | h
    · exact absurd h (boundaryFlagI_not_mem_image s')
    · split_ifs at h with hp
      · exact hp
      · simp at h
    · split_ifs at h with hp
      · exact absurd (Finset.mem_singleton.mp h)
          (fun hh => hij (W.boundaryFlag_injective hh))
      · simp at h
  · intro h
    rw [liftSubsetOpen]
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    rw [if_pos h]
    exact Finset.mem_singleton_self _

/-- The same at the second glued boundary flag. -/
theorem boundaryFlagJ_mem_liftOpen_iff
    (hij : i ≠ j)
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (s' : Finset (SurvivingFlag W i j)) :
    W.boundaryFlag j ∈ liftSubsetOpen hopen s' ↔
      partnerSurvJ hopen ∈ s' := by
  constructor
  · intro h
    rw [liftSubsetOpen, Finset.mem_union, Finset.mem_union] at h
    rcases h with (h | h) | h
    · exact absurd h (boundaryFlagJ_not_mem_image s')
    · split_ifs at h with hp
      · exact absurd (Finset.mem_singleton.mp h).symm
          (fun hh => hij (W.boundaryFlag_injective hh))
      · simp at h
    · split_ifs at h with hp
      · exact hp
      · simp at h
  · intro h
    rw [liftSubsetOpen]
    apply Finset.mem_union_right
    rw [if_pos h]
    exact Finset.mem_singleton_self _

/-! #### Round trips (open case) -/

/-- Dropping an open lift is the identity. -/
theorem dropSubset_liftSubsetOpen
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (s' : Finset (SurvivingFlag W i j)) :
    W.dropSubset i j (liftSubsetOpen hopen s') = s' := by
  ext f
  rw [mem_dropSubset, surviving_val_mem_liftOpen_iff]

/-- Lifting the drop of an edge-closed set is the identity: nothing
is lost across an open glue. -/
theorem liftSubsetOpen_dropSubset
    (hij : i ≠ j)
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (s : Finset W.Flag)
    (hcl : ∀ f ∈ s, W.pairing f ∈ s) :
    liftSubsetOpen hopen (W.dropSubset i j s) = s := by
  ext f
  by_cases hfi : f = W.boundaryFlag i
  · subst hfi
    rw [boundaryFlagI_mem_liftOpen_iff hij, mem_dropSubset,
      partnerSurvI_val]
    constructor
    · intro h
      have := hcl _ h; rwa [W.pairing_invol] at this
    · exact hcl _
  · by_cases hfj : f = W.boundaryFlag j
    · subst hfj
      rw [boundaryFlagJ_mem_liftOpen_iff hij, mem_dropSubset,
        partnerSurvJ_val]
      constructor
      · intro h
        have := hcl _ h; rwa [W.pairing_invol] at this
      · exact hcl _
    · rw [show f = (⟨f, hfi, hfj⟩ : SurvivingFlag W i j).val
          from rfl,
        surviving_val_mem_liftOpen_iff, mem_dropSubset]

/-! #### Forward closure transport (open case) -/

/-- The open lift of a rewire-closed set is edge-closed. -/
theorem liftSubsetOpen_pairing_closed
    (hij : i ≠ j)
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (s' : Finset (SurvivingFlag W i j))
    (hcl : ∀ f ∈ s', rewire hopen f ∈ s') :
    ∀ f ∈ liftSubsetOpen hopen s',
      W.pairing f ∈ liftSubsetOpen hopen s' := by
  intro f hf
  by_cases hfi : f = W.boundaryFlag i
  · subst hfi
    rw [boundaryFlagI_mem_liftOpen_iff hij] at hf
    rw [show W.pairing (W.boundaryFlag i) =
        (partnerSurvI hopen).val from rfl,
      surviving_val_mem_liftOpen_iff]
    exact hf
  · by_cases hfj : f = W.boundaryFlag j
    · subst hfj
      rw [boundaryFlagJ_mem_liftOpen_iff hij] at hf
      rw [show W.pairing (W.boundaryFlag j) =
          (partnerSurvJ hopen).val from rfl,
        surviving_val_mem_liftOpen_iff]
      exact hf
    · set g : SurvivingFlag W i j := ⟨f, hfi, hfj⟩
      rw [show f = g.val from rfl, surviving_val_mem_liftOpen_iff]
        at hf
      have hg := hcl g hf
      unfold rewire at hg
      split_ifs at hg with h1 h2
      · -- W.pairing g.val = bf_i
        rw [show W.pairing f = W.boundaryFlag i from h1,
          boundaryFlagI_mem_liftOpen_iff hij]
        have hge : g = partnerSurvI hopen := Subtype.ext (by
          have h' := congrArg W.pairing h1
          rw [W.pairing_invol] at h'
          exact h')
        rwa [hge] at hf
      · -- W.pairing g.val = bf_j
        rw [show W.pairing f = W.boundaryFlag j from h2,
          boundaryFlagJ_mem_liftOpen_iff hij]
        have hge : g = partnerSurvJ hopen := Subtype.ext (by
          have h' := congrArg W.pairing h2
          rw [W.pairing_invol] at h'
          exact h')
        rwa [hge] at hf
      · -- W.pairing g.val is a surviving flag
        rw [show W.pairing f =
            (⟨W.pairing g.val, h1, h2⟩ :
              SurvivingFlag W i j).val from rfl,
          surviving_val_mem_liftOpen_iff]
        exact hg

end OpenCase

/-! ### Closed case -/

section ClosedCase

variable {W : Fragment α} {i j : α}

/-- Lift a surviving-flag set to `W` in the closed case: the
image under `Subtype.val`, together with both boundary flags `i`
and `j` iff the Bool `b` is true (the closed-off circle-edge
participates). -/
noncomputable def liftSubsetClosed
    (s' : Finset (SurvivingFlag W i j)) (b : Bool) :
    Finset W.Flag :=
  s'.image Subtype.val
    ∪ (if b then {W.boundaryFlag i, W.boundaryFlag j} else ∅)

/-! #### Membership in the closed-case lift -/

/-- On surviving flags a closed lift is membership in the set it
lifts, whatever the circle bit. -/
theorem surviving_val_mem_liftClosed_iff
    (s' : Finset (SurvivingFlag W i j)) (b : Bool)
    (f : SurvivingFlag W i j) :
    f.val ∈ liftSubsetClosed s' b ↔ f ∈ s' := by
  constructor
  · intro h
    rw [liftSubsetClosed, Finset.mem_union] at h
    rcases h with h | h
    · rw [Finset.mem_image] at h
      obtain ⟨g, hg, hgv⟩ := h
      exact Subtype.ext hgv.symm ▸ hg
    · split_ifs at h with hb
      · simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h
        · exact absurd h f.prop.1
        · exact absurd h f.prop.2
      · simp at h
  · intro h
    rw [liftSubsetClosed]
    exact Finset.mem_union_left _
      (Finset.mem_image_of_mem _ h)

/-- The closed lift carries the first glued boundary flag exactly
when the circle bit is set: the closed cut's own edge is either
taken whole or not at all. -/
theorem boundaryFlagI_mem_liftClosed_iff
    (_hij : i ≠ j)
    (s' : Finset (SurvivingFlag W i j)) (b : Bool) :
    W.boundaryFlag i ∈ liftSubsetClosed s' b ↔ b = true := by
  constructor
  · intro h
    rw [liftSubsetClosed, Finset.mem_union] at h
    rcases h with h | h
    · exact absurd h (boundaryFlagI_not_mem_image s')
    · split_ifs at h with hb
      · exact hb
      · simp at h
  · intro h
    rw [liftSubsetClosed, Finset.mem_union]
    right; rw [if_pos h]
    exact Finset.mem_insert_self _ _

/-- The same at the second glued boundary flag, on the same bit. -/
theorem boundaryFlagJ_mem_liftClosed_iff
    (_hij : i ≠ j)
    (s' : Finset (SurvivingFlag W i j)) (b : Bool) :
    W.boundaryFlag j ∈ liftSubsetClosed s' b ↔ b = true := by
  constructor
  · intro h
    rw [liftSubsetClosed, Finset.mem_union] at h
    rcases h with h | h
    · exact absurd h (boundaryFlagJ_not_mem_image s')
    · split_ifs at h with hb
      · exact hb
      · simp at h
  · intro h
    rw [liftSubsetClosed, Finset.mem_union]
    right; rw [if_pos h]
    simp [Finset.mem_insert, Finset.mem_singleton]

/-! #### Round trips (closed case) -/

/-- Dropping a closed lift is the identity. -/
theorem dropSubset_liftSubsetClosed
    (s' : Finset (SurvivingFlag W i j)) (b : Bool) :
    W.dropSubset i j (liftSubsetClosed s' b) = s' := by
  ext f
  rw [mem_dropSubset, surviving_val_mem_liftClosed_iff]

/-- Lifting the drop of an edge-closed set, at the bit recording
whether the set took the closed edge, is the identity. -/
theorem liftSubsetClosed_dropSubset
    (hij : i ≠ j)
    (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
    (s : Finset W.Flag)
    (hcl : ∀ f ∈ s, W.pairing f ∈ s) :
    liftSubsetClosed (W.dropSubset i j s)
      (decide (W.boundaryFlag i ∈ s)) = s := by
  ext f
  by_cases hfi : f = W.boundaryFlag i
  · subst hfi
    rw [boundaryFlagI_mem_liftClosed_iff hij]
    simp [decide_eq_true_eq]
  · by_cases hfj : f = W.boundaryFlag j
    · subst hfj
      rw [boundaryFlagJ_mem_liftClosed_iff hij]
      simp only [decide_eq_true_eq]
      constructor
      · intro h
        have := hcl _ h; rw [hclosed] at this; exact this
      · intro h
        have hpj : W.pairing (W.boundaryFlag j) =
            W.boundaryFlag i := by
          rw [← hclosed, W.pairing_invol]
        have := hcl _ h; rw [hpj] at this; exact this
    · rw [show f = (⟨f, hfi, hfj⟩ : SurvivingFlag W i j).val
          from rfl,
        surviving_val_mem_liftClosed_iff, mem_dropSubset]

/-! #### Closure transport (closed case) -/

/-- The pairing of the closed glued fragment, as an explicit
surviving-flag function. -/
noncomputable def closedPairingSubtype
    (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
    (f : SurvivingFlag W i j) : SurvivingFlag W i j :=
  ⟨W.pairing f.val,
    fun h => f.prop.2 (by
      rw [← W.pairing_invol f.val, h, hclosed]),
    fun h => f.prop.1 (by
      rw [← W.pairing_invol f.val, h, ← hclosed,
        W.pairing_invol])⟩

/-- The closed lift of a pairing-closed set is edge-closed. -/
@[simp]
theorem liftSubsetClosed_pairing_closed
    (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
    (s' : Finset (SurvivingFlag W i j)) (b : Bool)
    (hcl : ∀ f ∈ s', closedPairingSubtype hclosed f ∈ s') :
    ∀ g ∈ liftSubsetClosed s' b,
      W.pairing g ∈ liftSubsetClosed s' b := by
  intro g hg
  by_cases hgi : g = W.boundaryFlag i
  · subst hgi; rw [hclosed]
    rw [liftSubsetClosed, Finset.mem_union] at hg
    rcases hg with hg | hg
    · exact absurd hg (boundaryFlagI_not_mem_image s')
    · split_ifs at hg with hb
      · rw [liftSubsetClosed, Finset.mem_union]; right
        rw [if_pos hb]
        simp [Finset.mem_insert, Finset.mem_singleton]
      · simp at hg
  · by_cases hgj : g = W.boundaryFlag j
    · subst hgj
      have hpj : W.pairing (W.boundaryFlag j) = W.boundaryFlag i :=
        by rw [← hclosed, W.pairing_invol]
      rw [hpj]
      rw [liftSubsetClosed, Finset.mem_union] at hg
      rcases hg with hg | hg
      · exact absurd hg (boundaryFlagJ_not_mem_image s')
      · split_ifs at hg with hb
        · rw [liftSubsetClosed, Finset.mem_union]; right
          rw [if_pos hb]
          exact Finset.mem_insert_self _ _
        · simp at hg
    · set gs : SurvivingFlag W i j := ⟨g, hgi, hgj⟩
      rw [show g = gs.val from rfl, surviving_val_mem_liftClosed_iff]
        at hg
      rw [show W.pairing g = (closedPairingSubtype hclosed gs).val
          from rfl,
        surviving_val_mem_liftClosed_iff]
      exact hcl gs hg

/-- The drop of an edge-closed set is closed under the glued
fragment's pairing. -/
theorem dropSubset_pairing_closed_of_closed
    (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
    (s : Finset W.Flag)
    (hcl : ∀ f ∈ s, W.pairing f ∈ s) :
    ∀ f ∈ W.dropSubset i j s,
      closedPairingSubtype hclosed f ∈ W.dropSubset i j s := by
  intro f hf
  rw [mem_dropSubset] at hf ⊢
  exact hcl _ hf

end ClosedCase

/-! ### Eulerian transport -/

section EulerianTransport

variable {W : Fragment α} {i j : α}

/-- Vertex-attached flags are surviving flags: a flag attached to
an internal vertex cannot be a boundary flag. -/
theorem vertex_flag_surviving
    (f : W.Flag) (v : W.Vertex)
    (hv : W.attach f = Sum.inl v) :
    f ≠ W.boundaryFlag i ∧ f ≠ W.boundaryFlag j := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, W.attach_boundaryFlag] at hv; cases hv
  · rw [h, W.attach_boundaryFlag] at hv; cases hv

/-- Vertex degrees are preserved by the open-case lift. -/
theorem deg_liftSubsetOpen_eq
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (s' : Finset (SurvivingFlag W i j))
    (v : W.Vertex) :
    letI := Classical.decEq (W.Vertex ⊕ α)
    letI := Classical.decEq (W.Vertex ⊕ SurvivingLabel α i j)
    ((liftSubsetOpen hopen s').filter
        (fun f => W.attach f = Sum.inl v)).card =
      (s'.filter
        (fun f => glueAttach W i j f = Sum.inl v)).card := by
  letI := Classical.decEq (W.Vertex ⊕ α)
  letI := Classical.decEq (W.Vertex ⊕ SurvivingLabel α i j)
  have hset : (liftSubsetOpen hopen s').filter
      (fun f => W.attach f = Sum.inl v) =
    (s'.filter (fun f => glueAttach W i j f = Sum.inl v)).image
      Subtype.val := by
    ext f
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · intro ⟨hf, hv⟩
      have hsurv := vertex_flag_surviving (i := i) (j := j) f v hv
      have hf' : (⟨f, hsurv.1, hsurv.2⟩ :
            SurvivingFlag W i j) ∈ s' := by
        rwa [← surviving_val_mem_liftOpen_iff hopen s'
          ⟨f, hsurv.1, hsurv.2⟩]
      exact ⟨⟨f, hsurv.1, hsurv.2⟩, Finset.mem_filter.mpr
        ⟨hf', (glueAttach_inl_iff _ v).mpr hv⟩, rfl⟩
    · intro ⟨g, hg, hgv⟩
      subst hgv
      have hg' := Finset.mem_filter.mp hg
      exact ⟨(surviving_val_mem_liftOpen_iff hopen s' g).mpr
        hg'.1, (glueAttach_inl_iff g v).mp hg'.2⟩
  rw [hset, Finset.card_image_of_injective _
    (fun a b h => Subtype.ext h)]

/-- Vertex degrees are preserved by the closed-case lift. -/
theorem deg_liftSubsetClosed_eq
    (s' : Finset (SurvivingFlag W i j)) (b : Bool)
    (v : W.Vertex) :
    letI := Classical.decEq (W.Vertex ⊕ α)
    letI := Classical.decEq (W.Vertex ⊕ SurvivingLabel α i j)
    ((liftSubsetClosed s' b).filter
        (fun f => W.attach f = Sum.inl v)).card =
      (s'.filter
        (fun f => glueAttach W i j f = Sum.inl v)).card := by
  letI := Classical.decEq (W.Vertex ⊕ α)
  letI := Classical.decEq (W.Vertex ⊕ SurvivingLabel α i j)
  have hset : (liftSubsetClosed s' b).filter
      (fun f => W.attach f = Sum.inl v) =
    (s'.filter (fun f => glueAttach W i j f = Sum.inl v)).image
      Subtype.val := by
    ext f
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · intro ⟨hf, hv⟩
      have hsurv := vertex_flag_surviving (i := i) (j := j) f v hv
      have hf' : (⟨f, hsurv.1, hsurv.2⟩ :
            SurvivingFlag W i j) ∈ s' := by
        rwa [← surviving_val_mem_liftClosed_iff s' b
          ⟨f, hsurv.1, hsurv.2⟩]
      exact ⟨⟨f, hsurv.1, hsurv.2⟩, Finset.mem_filter.mpr
        ⟨hf', (glueAttach_inl_iff _ v).mpr hv⟩, rfl⟩
    · intro ⟨g, hg, hgv⟩
      subst hgv
      have hg' := Finset.mem_filter.mp hg
      exact ⟨(surviving_val_mem_liftClosed_iff s' b g).mpr
        hg'.1, (glueAttach_inl_iff g v).mp hg'.2⟩
  rw [hset, Finset.card_image_of_injective _
    (fun a b h => Subtype.ext h)]

end EulerianTransport

/-! ### State compatibility -/

end Fragment

end RS
