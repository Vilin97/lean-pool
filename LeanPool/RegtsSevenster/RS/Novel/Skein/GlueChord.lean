/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.CutMatching
import LeanPool.RegtsSevenster.RS.Novel.Skein.ClosedCutDispatch

/-!
# The chord matching across one glue

Gluing an interface pair identifies two labels.  On the subset's
chord matching — the involution carrying a used label to the far end
of its chain — that identification is a contraction: the two labels
are removed and the far ends of their chains become each other's
partners.

This file carries the label bookkeeping across the glue.  The used
labels of the glued subset are the used labels of the lifted one
with the two glued labels removed, and the glued chord matching is
the contraction of the lifted one at those two labels.
-/

namespace RS

namespace EdgeSubset

open Fragment Equiv
/-! ## The relabel step

`glueInterface` relabels after every glue, so the invariant has to
survive a relabel.  It does: the circuit count is unchanged, and the
chord matching's pairing shifts along the relabel, so the number of
components is unchanged too.
-/

section RelabelStep

variable {α β : Type}
   {W : Fragment α}

/-- **The relabel preserves the circuit count and the number of
components.** -/
theorem openCircuitCount_add_unionCount_relabel
    [LinearOrder α] [LinearOrder β] [Fintype α] [Fintype β]
    (e : α ≃o β)
    (F : EdgeSubset W) (κ : F.RelTransitionSystem)
    {M N : DirMatching {a : α // W.boundaryFlag a ∈ F.boundaryFlags}}
    {M' N' : DirMatching {b : β //
      (W.relabel e.toEquiv).boundaryFlag b
        ∈ (F.relabelUp e.toEquiv).boundaryFlags}}
    (heM : (M'.map (usedLabRelabelEquiv e F)).edge = M.edge)
    (heN : (N'.map (usedLabRelabelEquiv e F)).edge = N.edge) :
    (relabelTransUp e.toEquiv F κ).openCircuitCount
        + DirMatching.unionCount M' N'
      = κ.openCircuitCount + DirMatching.unionCount M N := by
  rw [relabel_openCircuitCount e.toEquiv F κ,
    ← DirMatching.unionCount_map (usedLabRelabelEquiv e F) M' N',
    DirMatching.unionCount_congr heM heN]

end RelabelStep

section GlueChord

variable {α : Type} {W : Fragment α} {i j : α}
  (hij : i ≠ j)
  (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
  (s' : Finset (SurvivingFlag W i j))
  (hc' : ∀ f ∈ s',
    (W.gluePairOpen i j hij hopen).pairing f ∈ s')
  (hc : ∀ f ∈ liftSubsetOpen hopen s',
    W.pairing f ∈ liftSubsetOpen hopen s')

local notation "Fg" =>
  (EdgeSubset.mk s' hc' :
    EdgeSubset (W.gluePairOpen i j hij hopen))

local notation "Fl" =>
  (EdgeSubset.mk (liftSubsetOpen hopen s') hc :
    EdgeSubset W)

/-- **The glued subset's used labels** are the lifted subset's, less
the two glued ones. -/
noncomputable def usedLabelGlueEquiv
    [LinearOrder α]
    (hbi : W.boundaryFlag i ∈ (Fl).boundaryFlags)
    (hbj : W.boundaryFlag j ∈ (Fl).boundaryFlags) :
    {l : SurvivingLabel α i j //
        (W.gluePairOpen i j hij hopen).boundaryFlag l ∈
          (Fg).boundaryFlags}
      ≃ DirMatching.Surviving
          (⟨i, hbi⟩ : {a : α // W.boundaryFlag a ∈ (Fl).boundaryFlags})
          ⟨j, hbj⟩ where
  toFun x :=
    ⟨⟨x.val.val,
        (glued_participation_iff hij hopen s' hc' hc x.val).mp x.prop⟩,
      fun hx => x.val.prop.1 (congrArg Subtype.val hx),
      fun hx => x.val.prop.2 (congrArg Subtype.val hx)⟩
  invFun y :=
    ⟨⟨y.val.val,
        fun hx => y.prop.1 (Subtype.ext hx),
        fun hx => y.prop.2 (Subtype.ext hx)⟩,
      (glued_participation_iff hij hopen s' hc' hc _).mpr y.val.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The glued chord matching is the lifted one, contracted.**  A
chain of the glued subset that avoids the cut is a chain of the
lifted subset; one that reaches the cut continues out of the other
glued label. -/
theorem chordInv_glueOpen
    [LinearOrder α]
    (κ : (Fl).RelTransitionSystem)
    (l : SurvivingLabel α i j)
    (hlg : (W.gluePairOpen i j hij hopen).boundaryFlag l ∈
      (Fg).boundaryFlags)
    (hbi : W.boundaryFlag i ∈ (Fl).boundaryFlags)
    (hbj : W.boundaryFlag j ∈ (Fl).boundaryFlags) :
    (chordInv (Fg) (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)
        l).val
      = if chordInv (Fl) κ l.val = i then chordInv (Fl) κ j
        else if chordInv (Fl) κ l.val = j then chordInv (Fl) κ i
        else chordInv (Fl) κ l.val := by
  have hll : W.boundaryFlag l.val ∈ (Fl).boundaryFlags :=
    (glued_participation_iff hij hopen s' hc' hc l).mp hlg
  -- the glued chord, read as a flag
  have hgf := boundaryFlag_chordInv (Fg)
    (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) hlg
  have hlf := boundaryFlag_chordInv (Fl) κ hll
  have hLHS : W.boundaryFlag
      (chordInv (Fg) (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)
        l).val
      = ((RelTransitionSystem.glueOpen hij hopen s' hc' hc κ).pathMatch
          ((W.gluePairOpen i j hij hopen).boundaryFlag l) hlg).val :=
    congrArg Subtype.val hgf
  by_cases h1 : chordInv (Fl) κ l.val = i
  · rw [ite_eq_left h1]
    have hhit : κ.pathMatch (W.boundaryFlag l.val) hll
        = W.boundaryFlag i := by rw [← hlf, h1]
    have hpm := pathMatch_glueOpen_hit_i hij hopen s' hc' hc κ
      hlg hll hbj hhit
    refine W.boundaryFlag_injective ?_
    rw [hLHS, hpm]
    exact (boundaryFlag_chordInv (Fl) κ hbj).symm
  · by_cases h2 : chordInv (Fl) κ l.val = j
    · rw [ite_eq_right h1, ite_eq_left h2]
      have hhit : κ.pathMatch (W.boundaryFlag l.val) hll
          = W.boundaryFlag j := by rw [← hlf, h2]
      have hpm := pathMatch_glueOpen_hit_j hij hopen s' hc' hc κ
        hlg hll hbi hhit
      refine W.boundaryFlag_injective ?_
      rw [hLHS, hpm]
      exact (boundaryFlag_chordInv (Fl) κ hbi).symm
    · rw [ite_eq_right h1, ite_eq_right h2]
      have hni : κ.pathMatch (W.boundaryFlag l.val) hll
          ≠ W.boundaryFlag i := by
        rw [← hlf]
        exact fun hx => h1 (W.boundaryFlag_injective hx)
      have hnj : κ.pathMatch (W.boundaryFlag l.val) hll
          ≠ W.boundaryFlag j := by
        rw [← hlf]
        exact fun hx => h2 (W.boundaryFlag_injective hx)
      have hpm := pathMatch_glueOpen_of_ne hij hopen s' hc' hc κ
        hlg hll hni hnj
      refine W.boundaryFlag_injective ?_
      rw [hLHS, hpm]
      exact hlf.symm

/-- **The glued cut matching's pairing is the lifted one's,
contracted.**  Only the pairing is compared: the glued object fixes
its own directions, and the number of components does not see them. -/
theorem cutMatching_glueOpen_edge
    [LinearOrder α]
    (κ : (Fl).RelTransitionSystem)
    (o : κ.Orientation)
    (o' : (RelTransitionSystem.glueOpen hij hopen s' hc'
      hc κ).Orientation)
    (hbi : W.boundaryFlag i ∈ (Fl).boundaryFlags)
    (hbj : W.boundaryFlag j ∈ (Fl).boundaryFlags)
    (y : DirMatching.Surviving
      (⟨i, hbi⟩ : {a : α // W.boundaryFlag a ∈ (Fl).boundaryFlags})
      ⟨j, hbj⟩) :
    ((((cutMatching (Fg)
          (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) o').map
        (usedLabelGlueEquiv hij hopen s' hc' hc hbi hbj)).edge
      y).val).val
      = (((cutMatching (Fl) κ o).contractEdge ⟨i, hbi⟩ ⟨j, hbj⟩
          y.val)).val := by
  have hlg : (W.gluePairOpen i j hij hopen).boundaryFlag
      ⟨y.val.val, fun hx => y.prop.1 (Subtype.ext hx),
      fun hx => y.prop.2 (Subtype.ext hx)⟩
      ∈ (Fg).boundaryFlags :=
    (glued_participation_iff hij hopen s' hc' hc _).mpr y.val.prop
  have hkey := chordInv_glueOpen hij hopen s' hc' hc κ
    ⟨y.val.val, fun hx => y.prop.1 (Subtype.ext hx),
      fun hx => y.prop.2 (Subtype.ext hx)⟩
    hlg hbi hbj
  change (chordInv (Fg)
      (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)
      ⟨y.val.val, _⟩).val = _
  rw [hkey]
  change _ = ((if (cutMatching (Fl) κ o).edge y.val = ⟨i, hbi⟩ then
      (cutMatching (Fl) κ o).edge ⟨j, hbj⟩
    else if (cutMatching (Fl) κ o).edge y.val = ⟨j, hbj⟩ then
      (cutMatching (Fl) κ o).edge ⟨i, hbi⟩
    else (cutMatching (Fl) κ o).edge y.val) : {a : α // _}).val
  by_cases h1 : chordInv (Fl) κ y.val.val = i
  · rw [ite_eq_left h1, ite_eq_left (Subtype.ext h1 :
      (cutMatching (Fl) κ o).edge y.val = ⟨i, hbi⟩)]
    rfl
  · by_cases h2 : chordInv (Fl) κ y.val.val = j
    · rw [ite_eq_right h1, ite_eq_left h2,
        ite_eq_right (fun hx => h1 (congrArg Subtype.val hx)),
        ite_eq_left (Subtype.ext h2 :
          (cutMatching (Fl) κ o).edge y.val = ⟨j, hbj⟩)]
      rfl
    · rw [ite_eq_right h1, ite_eq_right h2,
        ite_eq_right (fun hx => h1 (congrArg Subtype.val hx)),
        ite_eq_right (fun hx => h2 (congrArg Subtype.val hx))]
      rfl

/-- **The interface is linked exactly when the two glued labels are
chord partners.**  This is the case split of the glue: linked means
the chain from one glued label ends at the other, so gluing closes
it into a circuit. -/
theorem interfaceLinked_iff_chordInv (κ : (Fl).RelTransitionSystem)
    (hpi : partnerSurvI hopen ∈ s')
    (hbi : W.boundaryFlag i ∈ (Fl).boundaryFlags) :
    InterfaceLinked hij hopen s' hc' hc
        (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) hpi
      ↔ chordInv (Fl) κ i = j := by
  have hmeq : (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
      (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)).MatchEq κ :=
    fun f hf => (unglueOpen_glueOpen_match hij hopen s' hc' hc κ hf)
  have hpm := pathMatch_matchEq hmeq
    (δ := W.boundaryFlag i) hbi
  rw [interfaceLinked_iff_pathMatch hij hopen s' hc' hc _ hpi]
  constructor
  · intro hL
    refine W.boundaryFlag_injective ?_
    rw [boundaryFlag_chordInv (Fl) κ hbi, hpm]
    exact hL
  · intro hC
    rw [← hpm, ← boundaryFlag_chordInv (Fl) κ hbi, hC]

/-! ### The invariant across one glue

The circuit count and the number of components of the union move
together: the interface is linked exactly when the two glued labels
are chord partners, and in that case gluing closes a circuit and
merges nothing, while otherwise it merges two chains and closes
nothing.  So their sum is unchanged.
-/

/-- **One glue step preserves `ĉ + c`** — RS21's circuit-count
bookkeeping, in the form that needs neither an ordering of the
interface nor the Eulerian position: only the two pairings. -/
theorem openCircuitCount_add_unionCount_glueOpen
    [LinearOrder α]
    [Fintype α]
    (κ : (Fl).RelTransitionSystem) (o : κ.Orientation)
    (o' : (RelTransitionSystem.glueOpen hij hopen s' hc'
      hc κ).Orientation)
    (hpi : partnerSurvI hopen ∈ s')
    (hbi : W.boundaryFlag i ∈ (Fl).boundaryFlags)
    (hbj : W.boundaryFlag j ∈ (Fl).boundaryFlags)
    {N : DirMatching
      {a : α // W.boundaryFlag a ∈ (Fl).boundaryFlags}}
    (hNij : N.edge ⟨i, hbi⟩ = ⟨j, hbj⟩)
    {Ng : DirMatching
      {l : SurvivingLabel α i j //
        (W.gluePairOpen i j hij hopen).boundaryFlag l ∈
          (Fg).boundaryFlags}}
    (hNg : (Ng.map
        (usedLabelGlueEquiv hij hopen s' hc' hc hbi hbj)).edge
      = (N.restrict hNij).edge) :
    (RelTransitionSystem.glueOpen hij hopen s' hc'
          hc κ).openCircuitCount
        + DirMatching.unionCount (cutMatching (Fg)
            (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) o') Ng
      = κ.openCircuitCount
        + DirMatching.unionCount (cutMatching (Fl) κ o) N := by
  classical
  obtain ⟨A, B, hAe, hBe, hAB⟩ := DirMatching.exists_alternating_repair
    (cutMatching (Fl) κ o) N
  obtain ⟨Ag, Bg, hAge, hBge, hABg⟩ :=
    DirMatching.exists_alternating_repair
      (cutMatching (Fg)
        (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) o') Ng
  rw [DirMatching.unionCount_eq_orbitCount hAB hAe hBe,
    DirMatching.unionCount_eq_orbitCount hABg hAge hBge,
    ← DirMatching.orbitCount_map
      (usedLabelGlueEquiv hij hopen s' hc' hc hbi hbj) hABg
      (DirMatching.alternating_map _ hABg)]
  have hδ := openCircuitCount_glueOpen_participating hij hopen s'
    hc' hc (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) hpi
  have hun : (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
      (RelTransitionSystem.glueOpen hij hopen s' hc'
        hc κ)).openCircuitCount = κ.openCircuitCount :=
    openCircuitCount_matchEq
      (fun f hf =>
        (unglueOpen_glueOpen_match hij hopen s' hc' hc κ hf).symm)
  have hlink := interfaceLinked_iff_chordInv hij hopen s' hc' hc κ
    hpi hbi
  have hedge : ∀ y, ((Ag.map
        (usedLabelGlueEquiv hij hopen s' hc' hc hbi hbj)).edge
      y).val.val
      = ((cutMatching (Fl) κ o).contractEdge ⟨i, hbi⟩ ⟨j, hbj⟩
          y.val).val := by
    intro y
    rw [DirMatching.map_edge_congr _ hAge]
    exact cutMatching_glueOpen_edge hij hopen s' hc' hc κ o o'
      hbi hbj y
  have hBij : B.edge ⟨i, hbi⟩ = ⟨j, hbj⟩ := by rw [hBe]; exact hNij
  have heN : (Bg.map
        (usedLabelGlueEquiv hij hopen s' hc' hc hbi hbj)).edge
      = (B.restrict hBij).edge := by
    rw [DirMatching.map_edge_congr _ hBge, hNg]
    funext y
    exact Subtype.ext (Subtype.ext (congrArg Subtype.val
      (congrFun hBe y.val)).symm)
  by_cases hcl : chordInv (Fl) κ i = j
  · have hMij : (cutMatching (Fl) κ o).edge ⟨i, hbi⟩ = ⟨j, hbj⟩ :=
      Subtype.ext hcl
    have hAij : A.edge ⟨i, hbi⟩ = ⟨j, hbj⟩ := by rw [hAe]; exact hMij
    have heM : (Ag.map
        (usedLabelGlueEquiv hij hopen s' hc' hc hbi hbj)).edge
        = (A.restrict hAij).edge := by
      funext y
      refine Subtype.ext (Subtype.ext ?_)
      rw [hedge y]
      refine Eq.trans (congrArg Subtype.val
        ((cutMatching (Fl) κ o).contractEdge_of_closed hMij y.val
          y.prop.1 y.prop.2)) ?_
      exact congrArg Subtype.val (congrFun hAe y.val).symm
    have hstep := DirMatching.orbitCount_restrict_closed_congr hAB
      hAij hBij (DirMatching.alternating_map _ hABg) heM heN
    have hc1 : (RelTransitionSystem.glueOpen hij hopen s' hc'
        hc κ).openCircuitCount = κ.openCircuitCount + 1 := by
      rw [hδ, hun, ite_eq_left (hlink.mpr hcl)]
    rw [hc1]
    omega
  · have hMij : (cutMatching (Fl) κ o).edge ⟨i, hbi⟩ ≠ ⟨j, hbj⟩ :=
      fun hx => hcl (congrArg Subtype.val hx)
    have hAij : A.edge ⟨i, hbi⟩ ≠ ⟨j, hbj⟩ := by rw [hAe]; exact hMij
    have hne : (⟨i, hbi⟩ :
        {a : α // W.boundaryFlag a ∈ (Fl).boundaryFlags})
        ≠ ⟨j, hbj⟩ := fun hx => hij (congrArg Subtype.val hx)
    have heM : (Ag.map
        (usedLabelGlueEquiv hij hopen s' hc' hc hbi hbj)).edge
        = (A.contract hne hAij
            (DirMatching.tail_ne_of_alternating hAB hBij)).edge := by
      funext y
      refine Subtype.ext (Subtype.ext ?_)
      rw [hedge y]
      exact congrArg Subtype.val
        (DirMatching.contractEdge_congr hAe ⟨i, hbi⟩ ⟨j, hbj⟩
          y.val).symm
    have hstep := DirMatching.orbitCount_contract_congr hAB hne
      hBij hAij (DirMatching.alternating_map _ hABg) heM heN
    have hc0 : (RelTransitionSystem.glueOpen hij hopen s' hc'
        hc κ).openCircuitCount = κ.openCircuitCount := by
      rw [hδ, hun, ite_eq_right (fun hL => hcl (hlink.mp hL)), add_zero]
    rw [hc0]
    omega

/-! ### One stage of the interface recursion

`glueInterface` glues the top pair and then relabels.  Composing the
two steps gives the recursion's stage: the circuit count plus the
number of components is unchanged across it.
-/

/-- **One stage of the interface recursion preserves `ĉ + c`.** -/
theorem openCircuitCount_add_unionCount_stage
    [LinearOrder α]
    [Fintype α]
    {γ : Type} [LinearOrder γ] [Fintype γ]
    (e : SurvivingLabel α i j ≃o γ)
    (κ : (Fl).RelTransitionSystem) (o : κ.Orientation)
    (o' : (RelTransitionSystem.glueOpen hij hopen s' hc'
      hc κ).Orientation)
    (hpi : partnerSurvI hopen ∈ s')
    (hbi : W.boundaryFlag i ∈ (Fl).boundaryFlags)
    (hbj : W.boundaryFlag j ∈ (Fl).boundaryFlags)
    {N : DirMatching
      {a : α // W.boundaryFlag a ∈ (Fl).boundaryFlags}}
    (hNij : N.edge ⟨i, hbi⟩ = ⟨j, hbj⟩)
    {Ng : DirMatching
      {l : SurvivingLabel α i j //
        (W.gluePairOpen i j hij hopen).boundaryFlag l ∈
          (Fg).boundaryFlags}}
    (hNg : (Ng.map
        (usedLabelGlueEquiv hij hopen s' hc' hc hbi hbj)).edge
      = (N.restrict hNij).edge)
    {Mr Nr : DirMatching {b : γ //
      ((W.gluePairOpen i j hij hopen).relabel e.toEquiv).boundaryFlag b
        ∈ ((Fg).relabelUp e.toEquiv).boundaryFlags}}
    (heM : (Mr.map (usedLabRelabelEquiv e (Fg))).edge
      = (cutMatching (Fg)
          (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)
          o').edge)
    (heN : (Nr.map (usedLabRelabelEquiv e (Fg))).edge = Ng.edge) :
    (relabelTransUp e.toEquiv (Fg)
          (RelTransitionSystem.glueOpen hij hopen s' hc'
            hc κ)).openCircuitCount
        + DirMatching.unionCount Mr Nr
      = κ.openCircuitCount
        + DirMatching.unionCount (cutMatching (Fl) κ o) N := by
  rw [openCircuitCount_add_unionCount_relabel e (Fg)
    (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ) heM heN]
  exact openCircuitCount_add_unionCount_glueOpen hij hopen s' hc' hc
    κ o o' hpi hbi hbj hNij hNg

/-! ### Which of the base's subsets the glue reaches

The lift and the drop are mutually inverse where they are used, but
the two closure conditions do not match: the drop of a
pairing-closed subset need not be closed under the rewire.  It is
closed exactly when the two glued boundary flags are used together,
which is the condition that the glued edge is either in the subset
or out of it.  So the glued fragment's subsets correspond to that
subfamily of the base's, not to all of them.
-/

/-- **The base's subsets the glue reaches**: pairing-closed, and
using the two glued boundary flags together. -/
def AgreeingSubset (i j : α) (s : Finset W.Flag) : Prop :=
  (∀ f ∈ s, W.pairing f ∈ s)
    ∧ (W.boundaryFlag i ∈ s ↔ W.boundaryFlag j ∈ s)

/-- **The drop of a subfamily member is closed under the
rewire.** -/
theorem dropSubset_rewire_closed (s : Finset W.Flag)
    (hs : AgreeingSubset i j s) :
    ∀ f ∈ W.dropSubset i j s, rewire hopen f ∈ W.dropSubset i j s := by
  intro f hf
  rw [mem_dropSubset] at hf ⊢
  by_cases h1 : W.pairing f.val = W.boundaryFlag i
  · have hbi : W.boundaryFlag i ∈ s := h1 ▸ hs.1 _ hf
    have hbj : W.boundaryFlag j ∈ s := hs.2.mp hbi
    change (rewire hopen f).val ∈ s
    rw [show (rewire hopen f).val = W.pairing (W.boundaryFlag j)
      from by unfold rewire; rw [dite_eq_left h1]]
    exact hs.1 _ hbj
  · by_cases h2 : W.pairing f.val = W.boundaryFlag j
    · have hbj : W.boundaryFlag j ∈ s := h2 ▸ hs.1 _ hf
      have hbi : W.boundaryFlag i ∈ s := hs.2.mpr hbj
      change (rewire hopen f).val ∈ s
      rw [show (rewire hopen f).val = W.pairing (W.boundaryFlag i)
        from by unfold rewire; rw [dite_eq_right h1, dite_eq_left h2]]
      exact hs.1 _ hbi
    · show (rewire hopen f).val ∈ s
      rw [show (rewire hopen f).val = W.pairing f.val from by
        unfold rewire; rw [dite_eq_right h1, dite_eq_right h2]]
      exact hs.1 _ hf

end GlueChord

/-! ## The closed glue

When the two glued labels bound a common edge, gluing closes that
edge into a free circle.  No chain of a surviving label reaches the
cut, so the chord matching simply restricts; and when the closed-off
edge is in the subset, its two labels were chord partners, so a
component of the union disappears — into the free circle rather than
into a circuit.
-/

section GlueChordClosed

variable {α : Type} {W : Fragment α} {i j : α}
  (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
  (b : Bool)
  (s' : Finset (SurvivingFlag W i j))
  (hc' : ∀ f ∈ s', (W.gluePairClosed i j hclosed).pairing f ∈ s')
  (hc : ∀ f ∈ liftSubsetClosed s' b,
    W.pairing f ∈ liftSubsetClosed s' b)

local notation "Fgc" =>
  (EdgeSubset.mk s' hc' : EdgeSubset (W.gluePairClosed i j hclosed))

local notation "Flc" =>
  (EdgeSubset.mk (liftSubsetClosed s' b) hc : EdgeSubset W)

/-- **The chord matching restricts across a closed glue.** -/
theorem chordInv_glueClosed
    (κ' : (Fgc).RelTransitionSystem) (l : SurvivingLabel α i j)
    (hlg : (W.gluePairClosed i j hclosed).boundaryFlag l ∈
      (Fgc).boundaryFlags) :
    (chordInv (Fgc) κ' l).val
      = chordInv (Flc)
          (RelTransitionSystem.unglueClosed hclosed b s' hc' hc κ')
          l.val := by
  have hll : W.boundaryFlag l.val ∈ (Flc).boundaryFlags :=
    (mem_boundaryFlags_glueClosed hclosed b s' hc' hc).mp hlg
  have hgf := boundaryFlag_chordInv (Fgc) κ' hlg
  have hlf := boundaryFlag_chordInv (Flc)
    (RelTransitionSystem.unglueClosed hclosed b s' hc' hc κ') hll
  have hpm := pathMatch_unglueClosed hclosed b s' hc' hc κ' hlg hll
  refine W.boundaryFlag_injective ?_
  calc W.boundaryFlag (chordInv (Fgc) κ' l).val
      = ((W.gluePairClosed i j hclosed).boundaryFlag
          (chordInv (Fgc) κ' l)).val := rfl
    _ = (κ'.pathMatch
          ((W.gluePairClosed i j hclosed).boundaryFlag l) hlg).val :=
        congrArg Subtype.val hgf
    _ = (RelTransitionSystem.unglueClosed hclosed b s' hc'
          hc κ').pathMatch (W.boundaryFlag l.val) hll := hpm.symm
    _ = W.boundaryFlag (chordInv (Flc)
          (RelTransitionSystem.unglueClosed hclosed b s' hc'
            hc κ') l.val) := hlf.symm

end GlueChordClosed

section GlueChordClosedPair

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

include hclosed in
/-- **The two glued labels are chord partners** when the closed-off
edge lies in the subset: the chain from one is the edge itself. -/
theorem chordInv_closed_pair
    [LinearOrder α]
    (κ : (EdgeSubset.mk (liftSubsetClosed s' true) hcT :
      EdgeSubset W).RelTransitionSystem)
    (hbi : W.boundaryFlag i ∈ (EdgeSubset.mk
      (liftSubsetClosed s' true) hcT : EdgeSubset W).boundaryFlags) :
    chordInv (EdgeSubset.mk (liftSubsetClosed s' true) hcT :
      EdgeSubset W) κ i = j := by
  have hbj : W.pairing (W.boundaryFlag i) ∈ (EdgeSubset.mk
      (liftSubsetClosed s' true) hcT :
        EdgeSubset W).boundaryFlags := by
    rw [hclosed]
    refine Finset.mem_filter.mpr ⟨?_, ⟨j, W.attach_boundaryFlag j⟩⟩
    refine Finset.mem_union_right _ ?_
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hpm : κ.pathMatch (W.boundaryFlag i) hbi
      = W.pairing (W.boundaryFlag i) :=
    pathMatch_exit_unique κ hbi 0 (fun t ht => absurd ht (by omega))
      hbj
  refine W.boundaryFlag_injective ?_
  rw [boundaryFlag_chordInv _ κ hbi, hpm, hclosed]

/-- **The glued subset's used labels** across a closed glue whose
edge lies in the subset: the lifted ones, less the two glued. -/
noncomputable def usedLabelGlueClosedEquiv
    (hbi : W.boundaryFlag i ∈ (FlT).boundaryFlags)
    (hbj : W.boundaryFlag j ∈ (FlT).boundaryFlags) :
    {l : SurvivingLabel α i j //
        (W.gluePairClosed i j hclosed).boundaryFlag l ∈
          (FgT).boundaryFlags}
      ≃ DirMatching.Surviving
          (⟨i, hbi⟩ : {a : α // W.boundaryFlag a ∈ (FlT).boundaryFlags})
          ⟨j, hbj⟩ where
  toFun x :=
    ⟨⟨x.val.val,
        (mem_boundaryFlags_glueClosed hclosed true s' hc' hcT).mp
          x.prop⟩,
      fun hx => x.val.prop.1 (congrArg Subtype.val hx),
      fun hx => x.val.prop.2 (congrArg Subtype.val hx)⟩
  invFun y :=
    ⟨⟨y.val.val,
        fun hx => y.prop.1 (Subtype.ext hx),
        fun hx => y.prop.2 (Subtype.ext hx)⟩,
      (mem_boundaryFlags_glueClosed hclosed true s' hc' hcT).mpr
        y.val.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **A closed glue drops one component.**  The chord matching
restricts, and the two glued labels were partners, so the component
they formed disappears — into the free circle the glue creates. -/
theorem unionCount_glueClosed
    [LinearOrder α]
    [Fintype α]
    (κ' : (FgT).RelTransitionSystem) (o' : κ'.Orientation)
    (o : (RelTransitionSystem.unglueClosed hclosed true s' hc'
      hcT κ').Orientation)
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
    DirMatching.unionCount (cutMatching (FgT) κ' o') Ng + 1
      = DirMatching.unionCount (cutMatching (FlT)
          (RelTransitionSystem.unglueClosed hclosed true s' hc'
            hcT κ') o) N := by
  classical
  obtain ⟨A, B, hAe, hBe, hAB⟩ := DirMatching.exists_alternating_repair
    (cutMatching (FlT)
      (RelTransitionSystem.unglueClosed hclosed true s' hc' hcT κ') o)
    N
  obtain ⟨Ag, Bg, hAge, hBge, hABg⟩ :=
    DirMatching.exists_alternating_repair (cutMatching (FgT) κ' o') Ng
  rw [DirMatching.unionCount_eq_orbitCount hAB hAe hBe,
    DirMatching.unionCount_eq_orbitCount hABg hAge hBge,
    ← DirMatching.orbitCount_map
      (usedLabelGlueClosedEquiv hclosed s' hc' hcT hbi hbj) hABg
      (DirMatching.alternating_map _ hABg)]
  have hMij : (cutMatching (FlT)
      (RelTransitionSystem.unglueClosed hclosed true s' hc' hcT κ')
      o).edge ⟨i, hbi⟩ = ⟨j, hbj⟩ :=
    Subtype.ext (chordInv_closed_pair hclosed s' hcT _ hbi)
  have hAij : A.edge ⟨i, hbi⟩ = ⟨j, hbj⟩ := by rw [hAe]; exact hMij
  have hBij : B.edge ⟨i, hbi⟩ = ⟨j, hbj⟩ := by rw [hBe]; exact hNij
  have heM : (Ag.map
      (usedLabelGlueClosedEquiv hclosed s' hc' hcT hbi hbj)).edge
      = (A.restrict hAij).edge := by
    rw [DirMatching.map_edge_congr _ hAge]
    funext y
    refine Subtype.ext (Subtype.ext ?_)
    refine Eq.trans (chordInv_glueClosed hclosed true s' hc' hcT κ'
      ((usedLabelGlueClosedEquiv hclosed s' hc' hcT hbi hbj).symm
        y).val
      ((usedLabelGlueClosedEquiv hclosed s' hc' hcT hbi hbj).symm
        y).prop) ?_
    exact congrArg Subtype.val (congrFun hAe y.val).symm
  have heN : (Bg.map
      (usedLabelGlueClosedEquiv hclosed s' hc' hcT hbi hbj)).edge
      = (B.restrict hBij).edge := by
    rw [DirMatching.map_edge_congr _ hBge, hNg]
    funext y
    exact Subtype.ext (Subtype.ext (congrArg Subtype.val
      (congrFun hBe y.val)).symm)
  exact DirMatching.orbitCount_restrict_closed_congr hAB hAij hBij
    (DirMatching.alternating_map _ hABg) heM heN

/-- **The closed glue's ledger**: the circuit count is unchanged and
one component disappears, the free circle the glue creates taking
its place. -/
theorem openCircuitCount_add_unionCount_glueClosed
    [LinearOrder α]
    [Fintype α]
    (κ' : (FgT).RelTransitionSystem) (o' : κ'.Orientation)
    (o : (RelTransitionSystem.unglueClosed hclosed true s' hc'
      hcT κ').Orientation)
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
    κ'.openCircuitCount
        + DirMatching.unionCount (cutMatching (FgT) κ' o') Ng
        + 1
      = (RelTransitionSystem.unglueClosed hclosed true s' hc'
            hcT κ').openCircuitCount
        + DirMatching.unionCount (cutMatching (FlT)
            (RelTransitionSystem.unglueClosed hclosed true s' hc'
              hcT κ') o) N := by
  have hc1 := openCircuitCount_unglueClosed hclosed true s' hc' hcT κ'
  have hc2 := unionCount_glueClosed hclosed s' hc' hcT κ' o' o hbi
    hbj hNij hNg
  omega

end GlueChordClosedPair

end EdgeSubset

end RS
