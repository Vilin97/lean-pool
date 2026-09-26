/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueChord

/-!
# The glue ledger at a cut the subset misses

RS21's bookkeeping (14) compares the circuit count of the composed
graph with the two fragments' counts and the number of components of
the union of their matchings.  In the flag model the composition is
built one interface pair at a time, and each step moves those
quantities together: the circuit count and the number of components
of the union.

`GlueChord` carries that ledger across a glue whose edge the subset
uses.  This file carries it across the glues the subset misses —
where the interface edge is not in the subset, and where a closed cut
is left out of it.  There nothing moves at all: the used labels are
the same on both sides, the chord matching is unchanged, and so is
the circuit count.
-/

@[expose] public section

namespace RS

namespace EdgeSubset

open Fragment Equiv
/-! ## The ledger reads only the matching

Both quantities the ledger tracks — the circuit count and the chord
matching's pairing — are read off the transition system's matching
alone, so two systems that match alike carry the same ledger.  That
is what lets the ledger be stated in whichever direction a glue
happens to construct its system.
-/

section MatchEqTransport

variable {α : Type} {W : Fragment α} {F : EdgeSubset W}

/-- **The chord matching reads only the matching.** -/
theorem chordInv_congr_matchEq {κ₁ κ₂ : F.RelTransitionSystem}
    (h : κ₁.MatchEq κ₂) (a : α) :
    chordInv F κ₂ a = chordInv F κ₁ a := by
  by_cases hb : W.boundaryFlag a ∈ F.boundaryFlags
  · refine W.boundaryFlag_injective ?_
    rw [boundaryFlag_chordInv F κ₂ hb, boundaryFlag_chordInv F κ₁ hb,
      pathMatch_matchEq h hb]
  · unfold chordInv
    rw [dite_eq_right hb, dite_eq_right hb]

/-- **The cut matching's pairing reads only the matching.** -/
theorem cutMatching_congr_matchEq
    [LinearOrder α]
    {κ₁ κ₂ : F.RelTransitionSystem}
    (h : κ₁.MatchEq κ₂) (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation) :
    (cutMatching F κ₂ o₂).edge = (cutMatching F κ₁ o₁).edge :=
  funext (fun a => Subtype.ext (chordInv_congr_matchEq h a.val))

/-- **The ledger reads only the matching.** -/
theorem openCircuitCount_add_unionCount_congr_matchEq
    [LinearOrder α]
    [Fintype α]
    {κ₁ κ₂ : F.RelTransitionSystem} (h : κ₁.MatchEq κ₂)
    (o₁ : κ₁.Orientation) (o₂ : κ₂.Orientation)
    (N : DirMatching {a : α // W.boundaryFlag a ∈ F.boundaryFlags}) :
    κ₂.openCircuitCount
        + DirMatching.unionCount (cutMatching F κ₂ o₂) N
      = κ₁.openCircuitCount
        + DirMatching.unionCount (cutMatching F κ₁ o₁) N := by
  rw [openCircuitCount_matchEq h,
    DirMatching.unionCount_congr (cutMatching_congr_matchEq h o₁ o₂)
      (rfl : N.edge = N.edge)]

end MatchEqTransport

/-! ## An open glue whose edge the subset misses -/

section GlueOpenMiss

variable {α : Type} {W : Fragment α} {i j : α}
  (hij : i ≠ j)
  (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
  (s' : Finset (SurvivingFlag W i j))
  (hc' : ∀ f ∈ s',
    (W.gluePairOpen i j hij hopen).pairing f ∈ s')
  (hc : ∀ f ∈ liftSubsetOpen hopen s',
    W.pairing f ∈ liftSubsetOpen hopen s')
  (hni : partnerSurvI hopen ∉ s')

local notation "Fg" =>
  (EdgeSubset.mk s' hc' :
    EdgeSubset (W.gluePairOpen i j hij hopen))

local notation "Fl" =>
  (EdgeSubset.mk (liftSubsetOpen hopen s') hc :
    EdgeSubset W)

include hij hni in
/-- Neither glued label is used when the interface edge is out of the
subset. -/
theorem boundaryFlagI_not_mem_of_miss :
    W.boundaryFlag i ∉ (Fl).boundaryFlags := fun hmem =>
  hni ((boundaryFlagI_mem_liftOpen_iff hij hopen s').mp
    (mem_flags_of_boundaryFlags _ hmem))

include hc' hc hni in
/-- At a cut the subset misses, the second glued flag is not a
boundary flag of the lift. -/
theorem boundaryFlagJ_not_mem_of_miss :
    W.boundaryFlag j ∉ (Fl).boundaryFlags := fun hmem =>
  partnerSurvJ_notMem_of hij hopen s' hc' hni
    ((boundaryFlagJ_mem_liftOpen_iff hij hopen s').mp
      (mem_flags_of_boundaryFlags _ hmem))

include hni in
/-- **The chord matching is unchanged** across a glue whose edge the
subset misses: no chain reaches the cut, so no chain is rerouted. -/
theorem chordInv_glueOpen_miss
    [LinearOrder α]
    (κ : (Fl).RelTransitionSystem)
    (l : SurvivingLabel α i j)
    (hlg : (W.gluePairOpen i j hij hopen).boundaryFlag l ∈
      (Fg).boundaryFlags) :
    (chordInv (Fg) (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)
        l).val
      = chordInv (Fl) κ l.val := by
  have hll : W.boundaryFlag l.val ∈ (Fl).boundaryFlags :=
    (glued_participation_iff hij hopen s' hc' hc l).mp hlg
  have hgf := boundaryFlag_chordInv (Fg)
    (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) hlg
  have hlf := boundaryFlag_chordInv (Fl) κ hll
  have hI : κ.pathMatch (W.boundaryFlag l.val) hll
      ≠ W.boundaryFlag i := fun hx =>
    boundaryFlagI_not_mem_of_miss hij hopen s' hc hni
      (hx ▸ κ.pathMatch_mem hll)
  have hJ : κ.pathMatch (W.boundaryFlag l.val) hll
      ≠ W.boundaryFlag j := fun hx =>
    boundaryFlagJ_not_mem_of_miss hij hopen s' hc' hc hni
      (hx ▸ κ.pathMatch_mem hll)
  have hpm := pathMatch_glueOpen_of_ne hij hopen s' hc' hc κ
    hlg hll hI hJ
  refine W.boundaryFlag_injective ?_
  calc W.boundaryFlag (chordInv (Fg)
        (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) l).val
      = ((W.gluePairOpen i j hij hopen).boundaryFlag
          (chordInv (Fg)
            (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)
            l)).val := rfl
    _ = ((RelTransitionSystem.glueOpen hij hopen s' hc'
          hc κ).pathMatch
          ((W.gluePairOpen i j hij hopen).boundaryFlag l) hlg).val :=
        congrArg Subtype.val hgf
    _ = κ.pathMatch (W.boundaryFlag l.val) hll := hpm
    _ = W.boundaryFlag (chordInv (Fl) κ l.val) := hlf.symm

include hc' hc hni in
/-- **The used labels are the same** across a glue whose edge the
subset misses. -/
noncomputable def usedLabelGlueMissEquiv
    [LinearOrder α]
    :
    {l : SurvivingLabel α i j //
        (W.gluePairOpen i j hij hopen).boundaryFlag l ∈
          (Fg).boundaryFlags}
      ≃ {a : α // W.boundaryFlag a ∈ (Fl).boundaryFlags} where
  toFun x := ⟨x.val.val,
    (glued_participation_iff hij hopen s' hc' hc x.val).mp x.prop⟩
  invFun y :=
    ⟨⟨y.val,
        fun hx => boundaryFlagI_not_mem_of_miss hij hopen s' hc hni
          (by have h := y.prop; rwa [hx] at h),
        fun hx => boundaryFlagJ_not_mem_of_miss hij hopen s' hc' hc
          hni (by have h := y.prop; rwa [hx] at h)⟩,
      (glued_participation_iff hij hopen s' hc' hc _).mpr y.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

include hni in
/-- **The glued cut matching's pairing is the lifted one's** across a
glue whose edge the subset misses. -/
theorem cutMatching_glueOpen_miss_edge
    [LinearOrder α]
    (κ : (Fl).RelTransitionSystem)
    (o : κ.Orientation)
    (o' : (RelTransitionSystem.glueOpen hij hopen s' hc'
      hc κ).Orientation) :
    (((cutMatching (Fg)
        (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) o').map
        (usedLabelGlueMissEquiv hij hopen s' hc' hc hni)).edge)
      = (cutMatching (Fl) κ o).edge := by
  funext y
  refine Subtype.ext ?_
  exact chordInv_glueOpen_miss hij hopen s' hc' hc hni κ
    ((usedLabelGlueMissEquiv hij hopen s' hc' hc hni).symm y).val
    ((usedLabelGlueMissEquiv hij hopen s' hc' hc hni).symm y).prop

include hni in
/-- **A glue whose edge the subset misses moves nothing.**  The
circuit count and the number of components of the union are both
unchanged. -/
theorem openCircuitCount_add_unionCount_glueOpen_miss
    [LinearOrder α]
    [Fintype α]
    (κ : (Fl).RelTransitionSystem) (o : κ.Orientation)
    (o' : (RelTransitionSystem.glueOpen hij hopen s' hc'
      hc κ).Orientation)
    {N : DirMatching
      {a : α // W.boundaryFlag a ∈ (Fl).boundaryFlags}}
    {Ng : DirMatching
      {l : SurvivingLabel α i j //
        (W.gluePairOpen i j hij hopen).boundaryFlag l ∈
          (Fg).boundaryFlags}}
    (hNg : (Ng.map
        (usedLabelGlueMissEquiv hij hopen s' hc' hc hni)).edge
      = N.edge) :
    (RelTransitionSystem.glueOpen hij hopen s' hc'
          hc κ).openCircuitCount
        + DirMatching.unionCount (cutMatching (Fg)
            (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) o') Ng
      = κ.openCircuitCount
        + DirMatching.unionCount (cutMatching (Fl) κ o) N := by
  have hun : (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
      (RelTransitionSystem.glueOpen hij hopen s' hc'
        hc κ)).openCircuitCount = κ.openCircuitCount :=
    openCircuitCount_matchEq
      (fun f hf =>
        (unglueOpen_glueOpen_match hij hopen s' hc' hc κ hf).symm)
  have hcount : (RelTransitionSystem.glueOpen hij hopen s' hc'
      hc κ).openCircuitCount = κ.openCircuitCount := by
    rw [← hun]
    exact (openCircuitCount_unglueOpen hij hopen s' hc' hc hni _).symm
  rw [hcount, ← DirMatching.unionCount_map
    (usedLabelGlueMissEquiv hij hopen s' hc' hc hni)
    (cutMatching (Fg)
      (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) o') Ng,
    DirMatching.unionCount_congr
      (cutMatching_glueOpen_miss_edge hij hopen s' hc' hc hni κ o o')
      hNg]

include hni in
/-- **One stage of the interface recursion at an open cut the subset
misses.** -/
theorem openCircuitCount_add_unionCount_stage_miss
    [LinearOrder α]
    [Fintype α]
    {γ : Type} [LinearOrder γ] [Fintype γ]
    (E : SurvivingLabel α i j ≃o γ)
    (κ : (Fl).RelTransitionSystem) (o : κ.Orientation)
    (o' : (RelTransitionSystem.glueOpen hij hopen s' hc'
      hc κ).Orientation)
    {N : DirMatching
      {a : α // W.boundaryFlag a ∈ (Fl).boundaryFlags}}
    {Ng : DirMatching
      {l : SurvivingLabel α i j //
        (W.gluePairOpen i j hij hopen).boundaryFlag l ∈
          (Fg).boundaryFlags}}
    (hNg : (Ng.map
        (usedLabelGlueMissEquiv hij hopen s' hc' hc hni)).edge
      = N.edge)
    {Mr Nr : DirMatching {b : γ //
      ((W.gluePairOpen i j hij hopen).relabel E.toEquiv).boundaryFlag b
        ∈ ((Fg).relabelUp E.toEquiv).boundaryFlags}}
    (heM : (Mr.map (usedLabRelabelEquiv E (Fg))).edge
      = (cutMatching (Fg)
          (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)
          o').edge)
    (heN : (Nr.map (usedLabRelabelEquiv E (Fg))).edge = Ng.edge) :
    (relabelTransUp E.toEquiv (Fg)
          (RelTransitionSystem.glueOpen hij hopen s' hc'
            hc κ)).openCircuitCount
        + DirMatching.unionCount Mr Nr
      = κ.openCircuitCount
        + DirMatching.unionCount (cutMatching (Fl) κ o) N := by
  rw [openCircuitCount_add_unionCount_relabel E (Fg)
    (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) heM heN]
  exact openCircuitCount_add_unionCount_glueOpen_miss hij hopen s'
    hc' hc hni κ o o' hNg

end GlueOpenMiss

/-! ## A closed glue whose edge the subset leaves out

At a closed cut the subset has a free choice: the closed-off edge is
in it or not.  When it is not, the two glued labels are unused, the
chord matching simply transports, and the circuit count is
unchanged — so nothing moves here either.  (When it is, one component
disappears; that is `GlueChord`'s closed ledger.)
-/

section GlueClosedMiss

variable {α : Type} {W : Fragment α} {i j : α}
  (hij : i ≠ j)
  (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
  (s' : Finset (SurvivingFlag W i j))
  (hc' : ∀ f ∈ s', (W.gluePairClosed i j hclosed).pairing f ∈ s')
  (hcF : ∀ f ∈ liftSubsetClosed s' false,
    W.pairing f ∈ liftSubsetClosed s' false)

local notation "FgF" =>
  (EdgeSubset.mk s' hc' : EdgeSubset (W.gluePairClosed i j hclosed))

local notation "FlF" =>
  (EdgeSubset.mk (liftSubsetClosed s' false) hcF : EdgeSubset W)

omit  hclosed in
include hij in
/-- Neither glued label is used when the closed-off edge is left out
of the subset. -/
theorem boundaryFlagI_not_mem_of_closed_miss :
    W.boundaryFlag i ∉ (FlF).boundaryFlags := fun hmem =>
  Bool.noConfusion
    ((boundaryFlagI_mem_liftClosed_iff hij s' false).mp
      (mem_flags_of_boundaryFlags _ hmem))

omit  hclosed in
include hij in
/-- The same at a closed cut the subset misses. -/
theorem boundaryFlagJ_not_mem_of_closed_miss :
    W.boundaryFlag j ∉ (FlF).boundaryFlags := fun hmem =>
  Bool.noConfusion
    ((boundaryFlagJ_mem_liftClosed_iff hij s' false).mp
      (mem_flags_of_boundaryFlags _ hmem))

include hij hc' hcF in
/-- **The used labels are the same** across a closed glue whose edge
the subset leaves out. -/
noncomputable def usedLabelGlueClosedMissEquiv :
    {l : SurvivingLabel α i j //
        (W.gluePairClosed i j hclosed).boundaryFlag l ∈
          (FgF).boundaryFlags}
      ≃ {a : α // W.boundaryFlag a ∈ (FlF).boundaryFlags} where
  toFun x := ⟨x.val.val,
    (mem_boundaryFlags_glueClosed hclosed false s' hc' hcF).mp
      x.prop⟩
  invFun y :=
    ⟨⟨y.val,
        fun hx => boundaryFlagI_not_mem_of_closed_miss hij s' hcF
          (by have h := y.prop; rwa [hx] at h),
        fun hx => boundaryFlagJ_not_mem_of_closed_miss hij s' hcF
          (by have h := y.prop; rwa [hx] at h)⟩,
      (mem_boundaryFlags_glueClosed hclosed false s' hc' hcF).mpr
        y.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

include hij in
/-- **The glued cut matching's pairing is the lifted one's** across a
closed glue whose edge the subset leaves out. -/
theorem cutMatching_glueClosedMiss_edge
    [LinearOrder α]
    (κ' : (FgF).RelTransitionSystem) (o' : κ'.Orientation)
    (o : (RelTransitionSystem.unglueClosed hclosed false s' hc'
      hcF κ').Orientation) :
    (((cutMatching (FgF) κ' o').map
        (usedLabelGlueClosedMissEquiv hij hclosed s' hc' hcF)).edge)
      = (cutMatching (FlF)
          (RelTransitionSystem.unglueClosed hclosed false s' hc'
            hcF κ') o).edge := by
  funext y
  refine Subtype.ext ?_
  exact chordInv_glueClosed hclosed false s' hc' hcF κ'
    ((usedLabelGlueClosedMissEquiv hij hclosed s' hc' hcF).symm y).val
    ((usedLabelGlueClosedMissEquiv hij hclosed s' hc' hcF).symm y).prop

include hij in
/-- **A closed glue whose edge the subset leaves out moves nothing.**
The circuit count and the number of components of the union are both
unchanged. -/
theorem openCircuitCount_add_unionCount_glueClosed_miss
    [LinearOrder α]
    [Fintype α]
    (κ' : (FgF).RelTransitionSystem) (o' : κ'.Orientation)
    (o : (RelTransitionSystem.unglueClosed hclosed false s' hc'
      hcF κ').Orientation)
    {N : DirMatching
      {a : α // W.boundaryFlag a ∈ (FlF).boundaryFlags}}
    {Ng : DirMatching
      {l : SurvivingLabel α i j //
        (W.gluePairClosed i j hclosed).boundaryFlag l ∈
          (FgF).boundaryFlags}}
    (hNg : (Ng.map
        (usedLabelGlueClosedMissEquiv hij hclosed s' hc' hcF)).edge
      = N.edge) :
    κ'.openCircuitCount
        + DirMatching.unionCount (cutMatching (FgF) κ' o') Ng
      = (RelTransitionSystem.unglueClosed hclosed false s' hc'
            hcF κ').openCircuitCount
        + DirMatching.unionCount (cutMatching (FlF)
            (RelTransitionSystem.unglueClosed hclosed false s' hc'
              hcF κ') o) N := by
  rw [openCircuitCount_unglueClosed hclosed false s' hc' hcF κ',
    ← DirMatching.unionCount_map
      (usedLabelGlueClosedMissEquiv hij hclosed s' hc' hcF)
      (cutMatching (FgF) κ' o') Ng,
    DirMatching.unionCount_congr
      (cutMatching_glueClosedMiss_edge hij hclosed s' hc' hcF κ' o' o)
      hNg]

end GlueClosedMiss

/-! ## The closed glue, in the direction the recursion runs

The interface recursion is given the fragment before the glue and
builds the one after it, so it wants its transition system built the
same way round.  `RelTransitionSystem.glueClosed` does that, and the
ledger transports to it because the round trip leaves the matching
alone.
-/

section GlueClosedForward

variable {α : Type} {W : Fragment α} {i j : α}
  (hij : i ≠ j)
  (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
  (b : Bool)
  (s' : Finset (SurvivingFlag W i j))
  (hc' : ∀ f ∈ s', (W.gluePairClosed i j hclosed).pairing f ∈ s')
  (hc : ∀ f ∈ liftSubsetClosed s' b,
    W.pairing f ∈ liftSubsetClosed s' b)

local notation "Fgb" =>
  (EdgeSubset.mk s' hc' : EdgeSubset (W.gluePairClosed i j hclosed))

local notation "Flb" =>
  (EdgeSubset.mk (liftSubsetClosed s' b) hc : EdgeSubset W)

include hc' hc in
/-- **The ledger transports to the forward glue.**  Ungluing the
forward glue returns a system matching like the original, so the two
carry the same ledger. -/
theorem openCircuitCount_add_unionCount_unglue_glueClosed
    [LinearOrder α]
    [Fintype α]
    (κ : (Flb).RelTransitionSystem) (o : κ.Orientation)
    (o₀ : (RelTransitionSystem.unglueClosed hclosed b s' hc' hc
      (RelTransitionSystem.glueClosed hclosed b s' hc'
        hc κ)).Orientation)
    (N : DirMatching
      {a : α // W.boundaryFlag a ∈ (Flb).boundaryFlags}) :
    (RelTransitionSystem.unglueClosed hclosed b s' hc' hc
            (RelTransitionSystem.glueClosed hclosed b s' hc'
              hc κ)).openCircuitCount
        + DirMatching.unionCount (cutMatching (Flb)
            (RelTransitionSystem.unglueClosed hclosed b s' hc' hc
              (RelTransitionSystem.glueClosed hclosed b s' hc'
                hc κ)) o₀) N
      = κ.openCircuitCount
        + DirMatching.unionCount (cutMatching (Flb) κ o) N :=
  openCircuitCount_add_unionCount_congr_matchEq
    (fun _ hf =>
      (unglueClosed_glueClosed_match hclosed b s' hc' hc κ hf).symm)
    o o₀ N

end GlueClosedForward

section GlueClosedForwardTrue

variable {α : Type} {W : Fragment α} {i j : α}
  (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
  (s' : Finset (SurvivingFlag W i j))
  (hc' : ∀ f ∈ s', (W.gluePairClosed i j hclosed).pairing f ∈ s')
  (hcT : ∀ f ∈ liftSubsetClosed s' true,
    W.pairing f ∈ liftSubsetClosed s' true)

local notation "FgT" =>
  (EdgeSubset.mk s' hc' : EdgeSubset (W.gluePairClosed i j hclosed))

local notation "FlT" =>
  (EdgeSubset.mk (liftSubsetClosed s' true) hcT : EdgeSubset W)

include hc' hcT in
/-- **A closed glue whose edge the subset carries drops one
component**, stated at the forward glue. -/
theorem openCircuitCount_add_unionCount_glueClosed_forward
    [LinearOrder α]
    [Fintype α]
    (κ : (FlT).RelTransitionSystem) (o : κ.Orientation)
    (o' : (RelTransitionSystem.glueClosed hclosed true s' hc'
      hcT κ).Orientation)
    (o₀ : (RelTransitionSystem.unglueClosed hclosed true s' hc' hcT
      (RelTransitionSystem.glueClosed hclosed true s' hc'
        hcT κ)).Orientation)
    (hbi : W.boundaryFlag i ∈ (FlT).boundaryFlags)
    (hbj : W.boundaryFlag j ∈ (FlT).boundaryFlags)
    {N : DirMatching
      {a : α // W.boundaryFlag a ∈ (FlT).boundaryFlags}}
    (hNij : N.edge ⟨i, hbi⟩ = ⟨j, hbj⟩)
    {Ng : DirMatching
      {l : SurvivingLabel α i j //
        (W.gluePairClosed i j hclosed).boundaryFlag l ∈
          (FgT).boundaryFlags}}
    (hNg : (Ng.map (usedLabelGlueClosedEquiv hclosed s' hc' hcT
        hbi hbj)).edge = (N.restrict hNij).edge) :
    (RelTransitionSystem.glueClosed hclosed true s' hc'
          hcT κ).openCircuitCount
        + DirMatching.unionCount
            (cutMatching (FgT)
              (RelTransitionSystem.glueClosed hclosed true s' hc'
                hcT κ) o') Ng
        + 1
      = κ.openCircuitCount
        + DirMatching.unionCount (cutMatching (FlT) κ o) N := by
  rw [← openCircuitCount_add_unionCount_unglue_glueClosed hclosed
    true s' hc' hcT κ o o₀ N]
  exact openCircuitCount_add_unionCount_glueClosed hclosed s' hc' hcT
    (RelTransitionSystem.glueClosed hclosed true s' hc' hcT κ) o' o₀
    hbi hbj hNij hNg

include hc' hcT in
/-- **One stage of the interface recursion at a closed cut the subset
carries**, stated at the forward glue. -/
theorem openCircuitCount_add_unionCount_stage_closed_forward
    [LinearOrder α]
    [Fintype α] {γ : Type} [LinearOrder γ] [Fintype γ]
    (E : SurvivingLabel α i j ≃o γ)
    (κ : (FlT).RelTransitionSystem) (o : κ.Orientation)
    (o' : (RelTransitionSystem.glueClosed hclosed true s' hc'
      hcT κ).Orientation)
    (o₀ : (RelTransitionSystem.unglueClosed hclosed true s' hc' hcT
      (RelTransitionSystem.glueClosed hclosed true s' hc'
        hcT κ)).Orientation)
    (hbi : W.boundaryFlag i ∈ (FlT).boundaryFlags)
    (hbj : W.boundaryFlag j ∈ (FlT).boundaryFlags)
    {N : DirMatching
      {a : α // W.boundaryFlag a ∈ (FlT).boundaryFlags}}
    (hNij : N.edge ⟨i, hbi⟩ = ⟨j, hbj⟩)
    {Ng : DirMatching
      {l : SurvivingLabel α i j //
        (W.gluePairClosed i j hclosed).boundaryFlag l ∈
          (FgT).boundaryFlags}}
    (hNg : (Ng.map (usedLabelGlueClosedEquiv hclosed s' hc' hcT
        hbi hbj)).edge = (N.restrict hNij).edge)
    {Mr Nr : DirMatching {b : γ //
      ((W.gluePairClosed i j hclosed).relabel E.toEquiv).boundaryFlag b
        ∈ ((FgT).relabelUp E.toEquiv).boundaryFlags}}
    (heM : (Mr.map (usedLabRelabelEquiv E (FgT))).edge
      = (cutMatching (FgT)
          (RelTransitionSystem.glueClosed hclosed true s' hc'
            hcT κ) o').edge)
    (heN : (Nr.map (usedLabRelabelEquiv E (FgT))).edge = Ng.edge) :
    (relabelTransUp E.toEquiv (FgT)
          (RelTransitionSystem.glueClosed hclosed true s' hc'
            hcT κ)).openCircuitCount
        + DirMatching.unionCount Mr Nr + 1
      = κ.openCircuitCount
        + DirMatching.unionCount (cutMatching (FlT) κ o) N := by
  rw [openCircuitCount_add_unionCount_relabel E (FgT)
    (RelTransitionSystem.glueClosed hclosed true s' hc' hcT κ)
    heM heN]
  exact openCircuitCount_add_unionCount_glueClosed_forward hclosed s'
    hc' hcT κ o o' o₀ hbi hbj hNij hNg

end GlueClosedForwardTrue

section GlueClosedForwardFalse

variable {α : Type} {W : Fragment α} {i j : α}
  (hij : i ≠ j)
  (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
  (s' : Finset (SurvivingFlag W i j))
  (hc' : ∀ f ∈ s', (W.gluePairClosed i j hclosed).pairing f ∈ s')
  (hcF : ∀ f ∈ liftSubsetClosed s' false,
    W.pairing f ∈ liftSubsetClosed s' false)

local notation "FgF" =>
  (EdgeSubset.mk s' hc' : EdgeSubset (W.gluePairClosed i j hclosed))

local notation "FlF" =>
  (EdgeSubset.mk (liftSubsetClosed s' false) hcF : EdgeSubset W)

include hij hc' hcF in
/-- **A closed glue whose edge the subset leaves out moves
nothing**, stated at the forward glue. -/
theorem openCircuitCount_add_unionCount_glueClosed_miss_forward
    [LinearOrder α]
    [Fintype α] (κ : (FlF).RelTransitionSystem) (o : κ.Orientation)
    (o' : (RelTransitionSystem.glueClosed hclosed false s' hc'
      hcF κ).Orientation)
    (o₀ : (RelTransitionSystem.unglueClosed hclosed false s' hc' hcF
      (RelTransitionSystem.glueClosed hclosed false s' hc'
        hcF κ)).Orientation)
    {N : DirMatching
      {a : α // W.boundaryFlag a ∈ (FlF).boundaryFlags}}
    {Ng : DirMatching
      {l : SurvivingLabel α i j //
        (W.gluePairClosed i j hclosed).boundaryFlag l ∈
          (FgF).boundaryFlags}}
    (hNg : (Ng.map
        (usedLabelGlueClosedMissEquiv hij hclosed s' hc' hcF)).edge
      = N.edge) :
    (RelTransitionSystem.glueClosed hclosed false s' hc'
          hcF κ).openCircuitCount
        + DirMatching.unionCount
            (cutMatching (FgF)
              (RelTransitionSystem.glueClosed hclosed false s' hc'
                hcF κ) o') Ng
      = κ.openCircuitCount
        + DirMatching.unionCount (cutMatching (FlF) κ o) N := by
  rw [← openCircuitCount_add_unionCount_unglue_glueClosed hclosed
    false s' hc' hcF κ o o₀ N]
  exact openCircuitCount_add_unionCount_glueClosed_miss hij hclosed s'
    hc' hcF (RelTransitionSystem.glueClosed hclosed false s' hc'
      hcF κ) o' o₀ hNg

include hij hc' hcF in
/-- **One stage of the interface recursion at a closed cut the subset
leaves out**, stated at the forward glue. -/
theorem openCircuitCount_add_unionCount_stage_closed_miss_forward
    [LinearOrder α]
    [Fintype α] {γ : Type} [LinearOrder γ] [Fintype γ]
    (E : SurvivingLabel α i j ≃o γ)
    (κ : (FlF).RelTransitionSystem) (o : κ.Orientation)
    (o' : (RelTransitionSystem.glueClosed hclosed false s' hc'
      hcF κ).Orientation)
    (o₀ : (RelTransitionSystem.unglueClosed hclosed false s' hc' hcF
      (RelTransitionSystem.glueClosed hclosed false s' hc'
        hcF κ)).Orientation)
    {N : DirMatching
      {a : α // W.boundaryFlag a ∈ (FlF).boundaryFlags}}
    {Ng : DirMatching
      {l : SurvivingLabel α i j //
        (W.gluePairClosed i j hclosed).boundaryFlag l ∈
          (FgF).boundaryFlags}}
    (hNg : (Ng.map
        (usedLabelGlueClosedMissEquiv hij hclosed s' hc' hcF)).edge
      = N.edge)
    {Mr Nr : DirMatching {b : γ //
      ((W.gluePairClosed i j hclosed).relabel E.toEquiv).boundaryFlag b
        ∈ ((FgF).relabelUp E.toEquiv).boundaryFlags}}
    (heM : (Mr.map (usedLabRelabelEquiv E (FgF))).edge
      = (cutMatching (FgF)
          (RelTransitionSystem.glueClosed hclosed false s' hc'
            hcF κ) o').edge)
    (heN : (Nr.map (usedLabRelabelEquiv E (FgF))).edge = Ng.edge) :
    (relabelTransUp E.toEquiv (FgF)
          (RelTransitionSystem.glueClosed hclosed false s' hc'
            hcF κ)).openCircuitCount
        + DirMatching.unionCount Mr Nr
      = κ.openCircuitCount
        + DirMatching.unionCount (cutMatching (FlF) κ o) N := by
  rw [openCircuitCount_add_unionCount_relabel E (FgF)
    (RelTransitionSystem.glueClosed hclosed false s' hc' hcF κ)
    heM heN]
  exact openCircuitCount_add_unionCount_glueClosed_miss_forward hij
    hclosed s' hc' hcF κ o o' o₀ hNg

end GlueClosedForwardFalse

end EdgeSubset

end RS
