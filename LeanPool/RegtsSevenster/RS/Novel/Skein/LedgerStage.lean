/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.InterfaceCut

/-!
# One stage of the interface recursion, with the matchings supplied

The per-glue ledgers ask for two matchings and a handful of equations
between their pairings.  In the recursion both matchings pair by an
involution of the labels — the chord matching by the subset's chords,
the interface matching by the swap — and the equations are then
automatic.  This file states each stage with the interface matching
given that way, so that a stage consumes only the involution and the
one equation saying the glued labels are partners.
-/

namespace RS

namespace EdgeSubset

open Fragment Equiv Classical

section StageOpen

variable {α : Type} {W : Fragment α}
  {i j : α} (hij : i ≠ j)
  (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
  (s' : Finset (SurvivingFlag W i j))
  (hc' : ∀ f ∈ s', (W.gluePairOpen i j hij hopen).pairing f ∈ s')
  (hc : ∀ f ∈ liftSubsetOpen hopen s',
    W.pairing f ∈ liftSubsetOpen hopen s')

local notation "Fg" =>
  (EdgeSubset.mk s' hc' :
    EdgeSubset (W.gluePairOpen i j hij hopen))

local notation "Fl" =>
  (EdgeSubset.mk (liftSubsetOpen hopen s') hc :
    EdgeSubset W)

/-- **One stage at an open cut the subset uses.**  The circuit count
and the number of components of the union move together. -/
theorem ledgerStage_open
    [LinearOrder α] [Fintype α]
    {γ : Type} [LinearOrder γ] [Fintype γ]
    (E : SurvivingLabel α i j ≃o γ)
    (κ : (Fl).RelTransitionSystem) (o : κ.Orientation)
    (o' : (RelTransitionSystem.glueOpen hij hopen s' hc'
      hc κ).Orientation)
    (o'' : (relabelTransUp E.toEquiv (Fg)
      (RelTransitionSystem.glueOpen hij hopen s' hc'
        hc κ)).Orientation)
    (hpi : partnerSurvI hopen ∈ s')
    (hbi : W.boundaryFlag i ∈ (Fl).boundaryFlags)
    (hbj : W.boundaryFlag j ∈ (Fl).boundaryFlags)
    (ι : α → α) (hcut : ι i = j)
    {N : DirMatching (UsedLab (Fl))}
    (hN : ∀ x : UsedLab (Fl), ((N.edge x).val : α) = ι x.val)
    {Nr : DirMatching (UsedLab ((Fg).relabelUp E.toEquiv))}
    (hNr : ∀ z : UsedLab (Fg),
      (((Nr.map (usedLabRelabelEquiv E (Fg))).edge z).val.val : α)
        = ι z.val.val) :
    (relabelTransUp E.toEquiv (Fg)
          (RelTransitionSystem.glueOpen hij hopen s' hc'
            hc κ)).openCircuitCount
        + DirMatching.unionCount
            (cutMatching ((Fg).relabelUp E.toEquiv)
              (relabelTransUp E.toEquiv (Fg)
                (RelTransitionSystem.glueOpen hij hopen s' hc'
                  hc κ)) o'') Nr
      = κ.openCircuitCount
        + DirMatching.unionCount (cutMatching (Fl) κ o) N := by
  have hNij : N.edge ⟨i, hbi⟩ = ⟨j, hbj⟩ :=
    edge_eq_of_swap (Fl) ι hN hbi hbj hcut
  refine openCircuitCount_add_unionCount_stage hij hopen s' hc' hc E
    κ o o' hpi hbi hbj hNij ?_ ?_ rfl
  · exact restrict_edge_of_swap (Fl) (Fg) Subtype.val ι hN hNr hNij
      (usedLabelGlueEquiv hij hopen s' hc' hc hbi hbj) (fun _ => rfl)
  · exact funext (fun a => Subtype.ext
      (cutMatching_relabelUp_edge E (Fg) _ o'' a))

/-- **One stage at an open cut the subset misses.**  Nothing moves:
the two glued labels are unused, so the chord matching and the
interface matching both simply transport. -/
theorem ledgerStage_open_miss
    [LinearOrder α] [Fintype α]
    {γ : Type} [LinearOrder γ] [Fintype γ]
    (hni : partnerSurvI hopen ∉ s')
    (E : SurvivingLabel α i j ≃o γ)
    (κ : (Fl).RelTransitionSystem) (o : κ.Orientation)
    (o' : (RelTransitionSystem.glueOpen hij hopen s' hc'
      hc κ).Orientation)
    (o'' : (relabelTransUp E.toEquiv (Fg)
      (RelTransitionSystem.glueOpen hij hopen s' hc'
        hc κ)).Orientation)
    (ι : α → α)
    {N : DirMatching (UsedLab (Fl))}
    (hN : ∀ x : UsedLab (Fl), ((N.edge x).val : α) = ι x.val)
    {Nr : DirMatching (UsedLab ((Fg).relabelUp E.toEquiv))}
    (hNr : ∀ z : UsedLab (Fg),
      (((Nr.map (usedLabRelabelEquiv E (Fg))).edge z).val.val : α)
        = ι z.val.val) :
    (relabelTransUp E.toEquiv (Fg)
          (RelTransitionSystem.glueOpen hij hopen s' hc'
            hc κ)).openCircuitCount
        + DirMatching.unionCount
            (cutMatching ((Fg).relabelUp E.toEquiv)
              (relabelTransUp E.toEquiv (Fg)
                (RelTransitionSystem.glueOpen hij hopen s' hc'
                  hc κ)) o'') Nr
      = κ.openCircuitCount
        + DirMatching.unionCount (cutMatching (Fl) κ o) N := by
  refine openCircuitCount_add_unionCount_stage_miss hij hopen s' hc'
    hc hni E κ o o' ?_ ?_ rfl
  · funext y
    refine Subtype.ext ?_
    exact (hNr ((usedLabelGlueMissEquiv hij hopen s' hc' hc
      hni).symm y)).trans (hN y).symm
  · exact funext (fun a => Subtype.ext
      (cutMatching_relabelUp_edge E (Fg) _ o'' a))

end StageOpen

section StageClosed

variable {α : Type} {W : Fragment α}
  {i j : α}
  (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
  (s' : Finset (SurvivingFlag W i j))
  (hc' : ∀ f ∈ s', (W.gluePairClosed i j hclosed).pairing f ∈ s')
  (hcT : ∀ f ∈ liftSubsetClosed s' true,
    W.pairing f ∈ liftSubsetClosed s' true)

local notation "FgT" =>
  (EdgeSubset.mk s' hc' : EdgeSubset (W.gluePairClosed i j hclosed))

local notation "FlT" =>
  (EdgeSubset.mk (liftSubsetClosed s' true) hcT : EdgeSubset W)

/-- **One stage at a closed cut the subset carries.**  One component
of the union disappears, into the free circle the glue creates. -/
theorem ledgerStage_closed
    [LinearOrder α] [Fintype α]
    {γ : Type} [LinearOrder γ] [Fintype γ]
    (E : SurvivingLabel α i j ≃o γ)
    (κ : (FlT).RelTransitionSystem) (o : κ.Orientation)
    (o' : (RelTransitionSystem.glueClosed hclosed true s' hc'
      hcT κ).Orientation)
    (o₀ : (RelTransitionSystem.unglueClosed hclosed true s' hc' hcT
      (RelTransitionSystem.glueClosed hclosed true s' hc'
        hcT κ)).Orientation)
    (o'' : (relabelTransUp E.toEquiv (FgT)
      (RelTransitionSystem.glueClosed hclosed true s' hc'
        hcT κ)).Orientation)
    (hbi : W.boundaryFlag i ∈ (FlT).boundaryFlags)
    (hbj : W.boundaryFlag j ∈ (FlT).boundaryFlags)
    (ι : α → α) (hcut : ι i = j)
    {N : DirMatching (UsedLab (FlT))}
    (hN : ∀ x : UsedLab (FlT), ((N.edge x).val : α) = ι x.val)
    {Nr : DirMatching (UsedLab ((FgT).relabelUp E.toEquiv))}
    (hNr : ∀ z : UsedLab (FgT),
      (((Nr.map (usedLabRelabelEquiv E (FgT))).edge z).val.val : α)
        = ι z.val.val) :
    (relabelTransUp E.toEquiv (FgT)
          (RelTransitionSystem.glueClosed hclosed true s' hc'
            hcT κ)).openCircuitCount
        + DirMatching.unionCount
            (cutMatching ((FgT).relabelUp E.toEquiv)
              (relabelTransUp E.toEquiv (FgT)
                (RelTransitionSystem.glueClosed hclosed true s' hc'
                  hcT κ)) o'') Nr
        + 1
      = κ.openCircuitCount
        + DirMatching.unionCount (cutMatching (FlT) κ o) N := by
  have hNij : N.edge ⟨i, hbi⟩ = ⟨j, hbj⟩ :=
    edge_eq_of_swap (FlT) ι hN hbi hbj hcut
  refine openCircuitCount_add_unionCount_stage_closed_forward hclosed
    s' hc' hcT E κ o o' o₀ hbi hbj hNij ?_ ?_ rfl
  · exact restrict_edge_of_swap (FlT) (FgT) Subtype.val ι hN hNr hNij
      (usedLabelGlueClosedEquiv hclosed s' hc' hcT hbi hbj)
      (fun _ => rfl)
  · exact funext (fun a => Subtype.ext
      (cutMatching_relabelUp_edge E (FgT) _ o'' a))

end StageClosed

section StageClosedMiss

variable {α : Type} {W : Fragment α}
  {i j : α} (hij : i ≠ j)
  (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
  (s' : Finset (SurvivingFlag W i j))
  (hc' : ∀ f ∈ s', (W.gluePairClosed i j hclosed).pairing f ∈ s')
  (hcF : ∀ f ∈ liftSubsetClosed s' false,
    W.pairing f ∈ liftSubsetClosed s' false)

local notation "FgF" =>
  (EdgeSubset.mk s' hc' : EdgeSubset (W.gluePairClosed i j hclosed))

local notation "FlF" =>
  (EdgeSubset.mk (liftSubsetClosed s' false) hcF : EdgeSubset W)

include hij in
/-- **One stage at a closed cut the subset leaves out.**  Nothing
moves; the free circle the glue creates carries no chord. -/
theorem ledgerStage_closed_miss
    [LinearOrder α] [Fintype α]
    {γ : Type} [LinearOrder γ]
    [Fintype γ] (E : SurvivingLabel α i j ≃o γ)
    (κ : (FlF).RelTransitionSystem) (o : κ.Orientation)
    (o' : (RelTransitionSystem.glueClosed hclosed false s' hc'
      hcF κ).Orientation)
    (o₀ : (RelTransitionSystem.unglueClosed hclosed false s' hc' hcF
      (RelTransitionSystem.glueClosed hclosed false s' hc'
        hcF κ)).Orientation)
    (o'' : (relabelTransUp E.toEquiv (FgF)
      (RelTransitionSystem.glueClosed hclosed false s' hc'
        hcF κ)).Orientation)
    (ι : α → α)
    {N : DirMatching (UsedLab (FlF))}
    (hN : ∀ x : UsedLab (FlF), ((N.edge x).val : α) = ι x.val)
    {Nr : DirMatching (UsedLab ((FgF).relabelUp E.toEquiv))}
    (hNr : ∀ z : UsedLab (FgF),
      (((Nr.map (usedLabRelabelEquiv E (FgF))).edge z).val.val : α)
        = ι z.val.val) :
    (relabelTransUp E.toEquiv (FgF)
          (RelTransitionSystem.glueClosed hclosed false s' hc'
            hcF κ)).openCircuitCount
        + DirMatching.unionCount
            (cutMatching ((FgF).relabelUp E.toEquiv)
              (relabelTransUp E.toEquiv (FgF)
                (RelTransitionSystem.glueClosed hclosed false s' hc'
                  hcF κ)) o'') Nr
      = κ.openCircuitCount
        + DirMatching.unionCount (cutMatching (FlF) κ o) N := by
  refine openCircuitCount_add_unionCount_stage_closed_miss_forward
    hij hclosed s' hc' hcF E κ o o' o₀ ?_ ?_ rfl
  · funext y
    refine Subtype.ext ?_
    exact (hNr ((usedLabelGlueClosedMissEquiv hij hclosed s' hc'
      hcF).symm y)).trans (hN y).symm
  · exact funext (fun a => Subtype.ext
      (cutMatching_relabelUp_edge E (FgF) _ o'' a))

end StageClosedMiss

/-! ## The two cut kinds, each in one statement

Whether the subset uses a cut is decided by the data, not by the
caller, so each kind of cut is better stated once: an open cut moves
nothing either way, and a closed one drops a component exactly when
the subset carries its edge.
-/

section StageOpenAny

variable {α : Type} {W : Fragment α}
  {i j : α} (hij : i ≠ j)
  (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
  (s' : Finset (SurvivingFlag W i j))
  (hc' : ∀ f ∈ s', (W.gluePairOpen i j hij hopen).pairing f ∈ s')
  (hc : ∀ f ∈ liftSubsetOpen hopen s',
    W.pairing f ∈ liftSubsetOpen hopen s')

local notation "Fg" =>
  (EdgeSubset.mk s' hc' :
    EdgeSubset (W.gluePairOpen i j hij hopen))

local notation "Fl" =>
  (EdgeSubset.mk (liftSubsetOpen hopen s') hc :
    EdgeSubset W)

/-- **One stage at an open cut.**  Nothing moves, whether or not the
subset uses the cut. -/
theorem ledgerStage_open_any
    [LinearOrder α] [Fintype α]
    {γ : Type} [LinearOrder γ] [Fintype γ]
    (E : SurvivingLabel α i j ≃o γ)
    (κ : (Fl).RelTransitionSystem) (o : κ.Orientation)
    (o' : (RelTransitionSystem.glueOpen hij hopen s' hc'
      hc κ).Orientation)
    (o'' : (relabelTransUp E.toEquiv (Fg)
      (RelTransitionSystem.glueOpen hij hopen s' hc'
        hc κ)).Orientation)
    (ι : α → α) (hcut : ι i = j)
    {N : DirMatching (UsedLab (Fl))}
    (hN : ∀ x : UsedLab (Fl), ((N.edge x).val : α) = ι x.val)
    {Nr : DirMatching (UsedLab ((Fg).relabelUp E.toEquiv))}
    (hNr : ∀ z : UsedLab (Fg),
      (((Nr.map (usedLabRelabelEquiv E (Fg))).edge z).val.val : α)
        = ι z.val.val) :
    (relabelTransUp E.toEquiv (Fg)
          (RelTransitionSystem.glueOpen hij hopen s' hc'
            hc κ)).openCircuitCount
        + DirMatching.unionCount
            (cutMatching ((Fg).relabelUp E.toEquiv)
              (relabelTransUp E.toEquiv (Fg)
                (RelTransitionSystem.glueOpen hij hopen s' hc'
                  hc κ)) o'') Nr
      = κ.openCircuitCount
        + DirMatching.unionCount (cutMatching (Fl) κ o) N := by
  by_cases hpi : partnerSurvI hopen ∈ s'
  · exact ledgerStage_open hij hopen s' hc' hc E κ o o' o'' hpi
      (boundaryFlagI_mem_boundaryFlags hij hopen s' hc hpi)
      (boundaryFlagJ_mem_boundaryFlags hij hopen s' hc' hc hpi)
      ι hcut hN hNr
  · exact ledgerStage_open_miss hij hopen s' hc' hc hpi E κ o o' o'' ι
      hN hNr

end StageOpenAny

section StageClosedBit

variable {α : Type} {W : Fragment α}
  {i j : α} (hij : i ≠ j)
  (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
  (s' : Finset (SurvivingFlag W i j)) (b : Bool)
  (hc' : ∀ f ∈ s', (W.gluePairClosed i j hclosed).pairing f ∈ s')
  (hcb : ∀ f ∈ liftSubsetClosed s' b,
    W.pairing f ∈ liftSubsetClosed s' b)

local notation "Fgb" =>
  (EdgeSubset.mk s' hc' : EdgeSubset (W.gluePairClosed i j hclosed))

local notation "Flb" =>
  (EdgeSubset.mk (liftSubsetClosed s' b) hcb : EdgeSubset W)

include hij in
/-- **One stage at a closed cut.**  A component of the union
disappears exactly when the subset carries the cut's own edge. -/
theorem ledgerStage_closed_bit
    [LinearOrder α] [Fintype α]
    {γ : Type} [LinearOrder γ] [Fintype γ]
    (E : SurvivingLabel α i j ≃o γ)
    (κ : (Flb).RelTransitionSystem) (o : κ.Orientation)
    (o' : (RelTransitionSystem.glueClosed hclosed b s' hc'
      hcb κ).Orientation)
    (o₀ : (RelTransitionSystem.unglueClosed hclosed b s' hc' hcb
      (RelTransitionSystem.glueClosed hclosed b s' hc'
        hcb κ)).Orientation)
    (o'' : (relabelTransUp E.toEquiv (Fgb)
      (RelTransitionSystem.glueClosed hclosed b s' hc'
        hcb κ)).Orientation)
    (ι : α → α) (hcut : ι i = j)
    {N : DirMatching (UsedLab (Flb))}
    (hN : ∀ x : UsedLab (Flb), ((N.edge x).val : α) = ι x.val)
    {Nr : DirMatching (UsedLab ((Fgb).relabelUp E.toEquiv))}
    (hNr : ∀ z : UsedLab (Fgb),
      (((Nr.map (usedLabRelabelEquiv E (Fgb))).edge z).val.val : α)
        = ι z.val.val) :
    (relabelTransUp E.toEquiv (Fgb)
          (RelTransitionSystem.glueClosed hclosed b s' hc'
            hcb κ)).openCircuitCount
        + DirMatching.unionCount
            (cutMatching ((Fgb).relabelUp E.toEquiv)
              (relabelTransUp E.toEquiv (Fgb)
                (RelTransitionSystem.glueClosed hclosed b s' hc'
                  hcb κ)) o'') Nr
        + (if b = true then 1 else 0)
      = κ.openCircuitCount
        + DirMatching.unionCount (cutMatching (Flb) κ o) N := by
  cases b with
  | false =>
    rw [if_neg (by decide : ¬ (false = true)), Nat.add_zero]
    exact ledgerStage_closed_miss hij hclosed s' hc' hcb E κ o o' o₀
      o'' ι hN hNr
  | true =>
    rw [if_pos rfl]
    exact ledgerStage_closed hclosed s' hc' hcb E κ o o' o₀ o''
      (boundaryFlag_mem_boundaryFlags
        ((boundaryFlagI_mem_liftClosed_iff hij s' true).mpr rfl))
      (boundaryFlag_mem_boundaryFlags
        ((boundaryFlagJ_mem_liftClosed_iff hij s' true).mpr rfl))
      ι hcut hN hNr

end StageClosedBit

/-! ## Pairing across a glue

Both glues read a surviving label as a label, so the pairing record
transports as soon as the glued swap does — one equation between
label maps, with the subset's own data nowhere in it.
-/

section PairedGlue

variable {α : Type} {W : Fragment α} {i j : α}

/-- **Pairing across a closed glue.** -/
theorem swapPaired_glueClosed
    (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
    (b : Bool) (s' : Finset (SurvivingFlag W i j))
    (hc' : ∀ f ∈ s', (W.gluePairClosed i j hclosed).pairing f ∈ s')
    (hc : ∀ f ∈ liftSubsetClosed s' b,
      W.pairing f ∈ liftSubsetClosed s' b)
    (ι : α → α) (ιg : SurvivingLabel α i j → SurvivingLabel α i j)
    (hcomp : ∀ x, ((ιg x).val : α) = ι x.val)
    (hp : SwapPaired
      (EdgeSubset.mk (liftSubsetClosed s' b) hc) ι) :
    SwapPaired (EdgeSubset.mk s' hc' :
      EdgeSubset (W.gluePairClosed i j hclosed)) ιg :=
  swapPaired_of_mem_iff _ _ ι ιg Subtype.val
    (fun _ => mem_boundaryFlags_glueClosed hclosed b s' hc' hc)
    hcomp hp

/-- **Pairing across an open glue.** -/
theorem swapPaired_glueOpen
    [LinearOrder α]
    (hij : i ≠ j)
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (s' : Finset (SurvivingFlag W i j))
    (hc' : ∀ f ∈ s', (W.gluePairOpen i j hij hopen).pairing f ∈ s')
    (hc : ∀ f ∈ liftSubsetOpen hopen s',
      W.pairing f ∈ liftSubsetOpen hopen s')
    (ι : α → α) (ιg : SurvivingLabel α i j → SurvivingLabel α i j)
    (hcomp : ∀ x, ((ιg x).val : α) = ι x.val)
    (hp : SwapPaired
      (EdgeSubset.mk (liftSubsetOpen hopen s') hc) ι) :
    SwapPaired (EdgeSubset.mk s' hc' :
      EdgeSubset (W.gluePairOpen i j hij hopen)) ιg :=
  swapPaired_of_mem_iff _ _ ι ιg Subtype.val
    (fun x => glued_participation_iff hij hopen s' hc' hc x)
    hcomp hp

end PairedGlue

end EdgeSubset

end RS
