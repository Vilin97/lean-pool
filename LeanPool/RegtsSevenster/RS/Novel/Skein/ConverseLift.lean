/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.ConverseAssembly
public import LeanPool.RegtsSevenster.RS.Novel.Skein.InterfaceAlternate

/-!
# The lift's round trip, and the identity at no cuts

The second half of the converse assembly: a stage of the lift
followed by a stage of the push, the congruences that let that
iterate over the interface, and the identity when the interface is
empty.
-/

@[expose] public section

namespace RS

namespace EdgeSubset

open Fragment
/-- The lexicographic order on the interface's label type. -/
@[reducible] local instance liftBaseOrder (n : ℕ) :
    LinearOrder (Fin (0 + n) ⊕ Fin (n + 0)) :=
  sumLexLinearOrder _ _

/-- The same order one stage up. -/
@[reducible] local instance liftOrderSucc (n : ℕ) :
    LinearOrder (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) :=
  sumLexLinearOrder _ _

/-- The order a stage's surviving labels carry. -/
@[reducible] local instance liftSurvOrder (n : ℕ) :
    LinearOrder (SurvivingLabel
      (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) (cutL n) (cutR n)) :=
  sumLexSubtypeLinearOrder _ _ _

/-- The order the composition's own label type carries. -/
@[reducible] local instance liftTopOrder :
    LinearOrder (Fin 0 ⊕ Fin 0) :=
  sumLexLinearOrder _ _

/-! ## The stage round trip

The relabel and the transport cancel outright at the level of
families, so a stage of the lift followed by a stage of the push is
the single-cut round trip and nothing more.
-/

open Classical in
/-- **A stage of the lift, pushed back — at an open cut.** -/
theorem stepData_roundTrip_open (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n)) (b : Bool) (𝒟 : DataFamily V) :
    stepDataDown n V (stepDataUp n V b 𝒟)
      = unglueDataOpen (cutL_ne_cutR n) hop
        (glueDataOpen (cutL_ne_cutR n) hop 𝒟) := by
  unfold stepDataDown stepDataUp stepDataGlued
  rw [dite_eq_right hop, dite_eq_right hop, relabelData_roundTrip,
    dataOfEq_roundTrip]

open Classical in
/-- **A stage of the lift, pushed back — at a closing cut.** -/
theorem stepData_roundTrip_closed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n)) (b : Bool) (𝒟 : DataFamily V) :
    stepDataDown n V (stepDataUp n V b 𝒟)
      = unglueDataClosed (cutL_ne_cutR n) hcl
        (glueDataClosed hcl b 𝒟) := by
  unfold stepDataDown stepDataUp stepDataGlued
  rw [dite_eq_left hcl, dite_eq_left hcl, relabelData_roundTrip,
    dataOfEq_roundTrip]

/-! ## Ungluing sees the system only through its partners

So a stage of the push is insensitive to replacing the family it
consumes by a matching-equal one — which is what the round trip
delivers.
-/

open Classical in
/-- **Ungluing respects matching equality, at an open cut.** -/
theorem match_unglueOpen_matchEq {α : Type} [LinearOrder α]
    {V : Fragment α} {i j : α} (hij : i ≠ j)
    (hopen : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j)
    (s' : Finset (SurvivingFlag V i j))
    (hc' : ∀ f ∈ s', (V.gluePairOpen i j hij hopen).pairing f ∈ s')
    (hcL : ∀ f ∈ liftSubsetOpen hopen s',
      V.pairing f ∈ liftSubsetOpen hopen s')
    {κ₁ κ₂ : (EdgeSubset.mk s' hc' :
      EdgeSubset (V.gluePairOpen i j hij hopen)).RelTransitionSystem}
    (hm : κ₁.MatchEq κ₂) {f : V.Flag}
    (hf : f ∈ (EdgeSubset.mk (liftSubsetOpen hopen s') hcL :
      EdgeSubset V).internalFlags) :
    (RelTransitionSystem.unglueOpen hij hopen s' hc' hcL κ₁).match_ f
      = (RelTransitionSystem.unglueOpen hij hopen s' hc' hcL
        κ₂).match_ f := by
  obtain ⟨h1, h2⟩ := internal_surviving i j hf
  have hg := internal_mk_of_glueOpen hij hopen s' hc' hcL hf h1 h2
  change unglueMatch κ₁.match_ f = unglueMatch κ₂.match_ f
  unfold unglueMatch
  rw [dite_eq_left ⟨h1, h2⟩, dite_eq_left ⟨h1, h2⟩, hm _ hg]

open Classical in
/-- **Ungluing respects matching equality, at a closing cut.** -/
theorem match_unglueClosed_matchEq {α : Type} [LinearOrder α]
    {V : Fragment α} {i j : α}
    (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
    (b : Bool) (s' : Finset (SurvivingFlag V i j))
    (hc' : ∀ f ∈ s', (V.gluePairClosed i j hclosed).pairing f ∈ s')
    (hcL : ∀ f ∈ liftSubsetClosed s' b,
      V.pairing f ∈ liftSubsetClosed s' b)
    {κ₁ κ₂ : (EdgeSubset.mk s' hc' :
      EdgeSubset (V.gluePairClosed i j hclosed)).RelTransitionSystem}
    (hm : κ₁.MatchEq κ₂) {f : V.Flag}
    (hf : f ∈ (EdgeSubset.mk (liftSubsetClosed s' b) hcL :
      EdgeSubset V).internalFlags) :
    (RelTransitionSystem.unglueClosed hclosed b s' hc' hcL
        κ₁).match_ f
      = (RelTransitionSystem.unglueClosed hclosed b s' hc' hcL
        κ₂).match_ f := by
  obtain ⟨h1, h2⟩ := internal_surviving i j hf
  have hg := (mem_internalFlags_glueClosed hclosed b s' hc' hcL
    (f' := ⟨f, h1, h2⟩)).mpr hf
  change unglueMatch κ₁.match_ f = unglueMatch κ₂.match_ f
  unfold unglueMatch
  rw [dite_eq_left ⟨h1, h2⟩, dite_eq_left ⟨h1, h2⟩, hm _ hg]

open Classical in
/-- **One subset is enough**, at an open cut: the ungluing at `s`
reads the family only at `s`'s own drop. -/
theorem match_unglueDataOpen_congr_at {α : Type} [LinearOrder α]
    {V : Fragment α} {i j : α} (hij : i ≠ j)
    (hopen : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j)
    (𝒟₁ 𝒟₂ : DataFamily (V.gluePairOpen i j hij hopen))
    {s : Finset V.Flag}
    (hm : ∀ (hct : ∀ f ∈ V.dropSubset i j s,
        (V.gluePairOpen i j hij hopen).pairing f
          ∈ V.dropSubset i j s)
      (hEt : (EdgeSubset.mk (V.dropSubset i j s) hct :
        EdgeSubset (V.gluePairOpen i j hij hopen)).Eulerian)
      (hnet : Nonempty (EdgeSubset.mk (V.dropSubset i j s) hct :
        EdgeSubset (V.gluePairOpen i j hij hopen)).CanonData),
      (𝒟₁ _ hct hEt hnet).1.MatchEq (𝒟₂ _ hct hEt hnet).1)
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc : EdgeSubset V).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc : EdgeSubset V).CanonData) :
    (unglueDataOpen hij hopen 𝒟₁ s hc hE hne).1.MatchEq
      (unglueDataOpen hij hopen 𝒟₂ s hc hE hne).1 := by
  intro f hf
  have hlift : liftSubsetOpen hopen (V.dropSubset i j s) = s :=
    liftSubsetOpen_dropSubset hij hopen s hc
  unfold unglueDataOpen
  by_cases hag : ∀ f ∈ V.dropSubset i j s,
      (V.gluePairOpen i j hij hopen).pairing f
        ∈ V.dropSubset i j s
  · rw [dite_eq_left hag, dite_eq_left hag, match_relOfEq, match_relOfEq]
    have hcL := liftSubsetOpen_pairing_closed hij hopen
      (V.dropSubset i j s) hag
    refine match_unglueOpen_matchEq hij hopen
      (V.dropSubset i j s) hag hcL (hm _ _ _) ?_
    have hF : (EdgeSubset.mk (liftSubsetOpen hopen
          (V.dropSubset i j s)) hcL : EdgeSubset V)
        = EdgeSubset.mk s hc := EdgeSubset.ext hlift
    rw [hF]
    exact hf
  · rw [dite_eq_right hag, dite_eq_right hag]

open Classical in
/-- **One subset is enough**, under a transport. -/
theorem match_dataOfEq_congr_at {L : Type} [LinearOrder L]
    {V₁ V₂ : Fragment L} (h : V₁ = V₂) (𝒟₁ 𝒟₂ : DataFamily V₂)
    (s : Finset V₁.Flag)
    (hm : ∀ (hc' : ∀ f ∈ flagsOfEq V₁ V₂ h s,
        V₂.pairing f ∈ flagsOfEq V₁ V₂ h s)
      (hE' : (EdgeSubset.mk (flagsOfEq V₁ V₂ h s) hc').Eulerian)
      (hne' : Nonempty
        (EdgeSubset.mk (flagsOfEq V₁ V₂ h s) hc').CanonData),
      (𝒟₁ _ hc' hE' hne').1.MatchEq (𝒟₂ _ hc' hE' hne').1)
    (hc : ∀ f ∈ s, V₁.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData) :
    (dataOfEq h 𝒟₁ s hc hE hne).1.MatchEq
      (dataOfEq h 𝒟₂ s hc hE hne).1 := by
  subst h
  exact hm hc hE hne

open Classical in
/-- **One subset is enough**, under a relabel. -/
theorem match_relabelDataDown_congr_at {α' β' : Type}
    [LinearOrder α'] [LinearOrder β'] (e : α' ≃o β')
    {W' : Fragment α'} (𝒟₁ 𝒟₂ : DataFamily (W'.relabel e.toEquiv))
    (s : Finset W'.Flag)
    (hm : ∀ (hc' : ∀ f ∈ s, (W'.relabel e.toEquiv).pairing f ∈ s)
      (hE' : (EdgeSubset.mk s hc' :
        EdgeSubset (W'.relabel e.toEquiv)).Eulerian)
      (hne' : Nonempty (EdgeSubset.mk s hc' :
        EdgeSubset (W'.relabel e.toEquiv)).CanonData),
      (𝒟₁ s hc' hE' hne').1.MatchEq (𝒟₂ s hc' hE' hne').1)
    (hc : ∀ f ∈ s, W'.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData) :
    (relabelDataDown e 𝒟₁ s hc hE hne).1.MatchEq
      (relabelDataDown e 𝒟₂ s hc hE hne).1 := by
  intro f hf
  refine hm hc _ _ f ?_
  exact (relabelUp_internalFlags e.toEquiv
    (EdgeSubset.mk s hc)).symm ▸ hf

open Classical in
/-- **One subset is enough**, for a whole stage of the push at an
open cut: the stage reads the family only at the stage subset the
drop makes. -/
theorem match_stepDataDown_congr_at_open (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (𝒟₁ 𝒟₂ : DataFamily (stepFragment n V)) {s : Finset V.Flag}
    (hm : ∀ (t : Finset (stepFragment n V).Flag),
      t = flagsOfEq
          (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
          (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
          (gluePair_eq_open n V hop)
          (V.dropSubset (cutL n) (cutR n) s) →
      ∀ (hct : ∀ f ∈ t, (stepFragment n V).pairing f ∈ t)
        (hEt : (EdgeSubset.mk t hct).Eulerian)
        (hnet : Nonempty (EdgeSubset.mk t hct).CanonData),
      (𝒟₁ t hct hEt hnet).1.MatchEq (𝒟₂ t hct hEt hnet).1)
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData) :
    (stepDataDown n V 𝒟₁ s hc hE hne).1.MatchEq
      (stepDataDown n V 𝒟₂ s hc hE hne).1 := by
  unfold stepDataDown
  rw [dite_eq_right hop, dite_eq_right hop]
  refine match_unglueDataOpen_congr_at (cutL_ne_cutR n) hop _ _
    ?_ hc hE hne
  intro hct hEt hnet
  refine match_dataOfEq_congr_at (gluePair_eq_open n V hop) _ _
    (V.dropSubset (cutL n) (cutR n) s) ?_ hct hEt hnet
  intro hc' hE' hne'
  exact match_relabelDataDown_congr_at (stepIso n) 𝒟₁ 𝒟₂ _
    (hm _ rfl) hc' hE' hne'

open Classical in
/-- **One subset is enough**, at a closing cut: the push reads the
glued family only at the subset the drop makes. -/
theorem match_unglueDataClosed_congr_at {α : Type} [LinearOrder α]
    {V : Fragment α} {i j : α} (hij : i ≠ j)
    (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
    (𝒟₁ 𝒟₂ : DataFamily (V.gluePairClosed i j hclosed))
    {s : Finset V.Flag}
    (hm : ∀ (hct : ∀ f ∈ V.dropSubset i j s,
        (V.gluePairClosed i j hclosed).pairing f
          ∈ V.dropSubset i j s)
      (hEt : (EdgeSubset.mk (V.dropSubset i j s) hct :
        EdgeSubset (V.gluePairClosed i j hclosed)).Eulerian)
      (hnet : Nonempty (EdgeSubset.mk (V.dropSubset i j s) hct :
        EdgeSubset (V.gluePairClosed i j hclosed)).CanonData),
      (𝒟₁ _ hct hEt hnet).1.MatchEq (𝒟₂ _ hct hEt hnet).1)
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc : EdgeSubset V).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc : EdgeSubset V).CanonData) :
    (unglueDataClosed hij hclosed 𝒟₁ s hc hE hne).1.MatchEq
      (unglueDataClosed hij hclosed 𝒟₂ s hc hE hne).1 := by
  intro f hf
  have hlift : liftSubsetClosed (V.dropSubset i j s)
      (decide (V.boundaryFlag i ∈ s)) = s :=
    liftSubsetClosed_dropSubset hij hclosed s hc
  have hct := dropSubset_pairing_closed_of_closed hclosed s hc
  have hcL := liftSubsetClosed_pairing_closed hclosed
    (V.dropSubset i j s) (decide (V.boundaryFlag i ∈ s)) hct
  unfold unglueDataClosed
  rw [match_relOfEq, match_relOfEq]
  refine match_unglueClosed_matchEq hclosed
    (decide (V.boundaryFlag i ∈ s)) (V.dropSubset i j s) hct hcL
    (hm _ _ _) ?_
  have hF : (EdgeSubset.mk (liftSubsetClosed (V.dropSubset i j s)
        (decide (V.boundaryFlag i ∈ s))) hcL : EdgeSubset V)
      = EdgeSubset.mk s hc := EdgeSubset.ext hlift
  rw [hF]
  exact hf

open Classical in
/-- **One subset is enough**, for a whole stage of the push at a
closing cut. -/
theorem match_stepDataDown_congr_at_closed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (𝒟₁ 𝒟₂ : DataFamily (stepFragment n V)) {s : Finset V.Flag}
    (hm : ∀ (t : Finset (stepFragment n V).Flag),
      t = flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
          (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
          (gluePair_eq_closed n V hcl)
          (V.dropSubset (cutL n) (cutR n) s) →
      ∀ (hct : ∀ f ∈ t, (stepFragment n V).pairing f ∈ t)
        (hEt : (EdgeSubset.mk t hct).Eulerian)
        (hnet : Nonempty (EdgeSubset.mk t hct).CanonData),
      (𝒟₁ t hct hEt hnet).1.MatchEq (𝒟₂ t hct hEt hnet).1)
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData) :
    (stepDataDown n V 𝒟₁ s hc hE hne).1.MatchEq
      (stepDataDown n V 𝒟₂ s hc hE hne).1 := by
  unfold stepDataDown
  rw [dite_eq_left hcl, dite_eq_left hcl]
  refine match_unglueDataClosed_congr_at (cutL_ne_cutR n) hcl _ _
    ?_ hc hE hne
  intro hct hEt hnet
  refine match_dataOfEq_congr_at (gluePair_eq_closed n V hcl) _ _
    (V.dropSubset (cutL n) (cutR n) s) ?_ hct hEt hnet
  intro hc' hE' hne'
  exact match_relabelDataDown_congr_at (stepIso n) 𝒟₁ 𝒟₂ _
    (hm _ rfl) hc' hE' hne'

open Classical in
/-- **The interface round trip, at no cuts.**  The lift and the push
are inverse outright. -/
theorem match_pushData_liftData_zero (V : Fragment (Fin (0 + 0) ⊕ Fin (0 + 0)))
    (bits : Fin 0 → Bool) (𝒟 : DataFamily V) (s : Finset V.Flag)
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData) :
    (pushData 0 V (liftData 0 V bits 𝒟) s hc hE hne).1.MatchEq
      (𝒟 s hc hE hne).1 := by
  change (relabelDataDown baseIso (relabelDataUp baseIso 𝒟) s hc hE
    hne).1.MatchEq _
  rw [relabelData_roundTrip]
  exact fun _f _hf => rfl

open Classical in
/-- **The interface round trip, one stage on — at an open cut**,
reading the family at the one stage subset the drop makes. -/
theorem match_pushData_liftData_succ_open_at (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (bits : Fin (n + 1) → Bool) (𝒟 : DataFamily V)
    {s : Finset V.Flag} (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc : EdgeSubset V).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc : EdgeSubset V).CanonData)
    (hIH : ∀ (t : Finset (stepFragment n V).Flag),
      t = flagsOfEq
          (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
          (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
          (gluePair_eq_open n V hop)
          (V.dropSubset (cutL n) (cutR n) s) →
      ∀ (hct : ∀ f ∈ t, (stepFragment n V).pairing f ∈ t)
        (hEt : (EdgeSubset.mk t hct).Eulerian)
        (hnet : Nonempty (EdgeSubset.mk t hct).CanonData),
      (pushData n (stepFragment n V)
          (liftData n (stepFragment n V)
            (fun a => bits a.castSucc)
            (stepDataUp n V (bits (Fin.last n)) 𝒟))
          t hct hEt hnet).1.MatchEq
        (stepDataUp n V (bits (Fin.last n)) 𝒟 t hct hEt hnet).1)
    (hdc : ∀ f ∈ V.dropSubset (cutL n) (cutR n) s,
      (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n)
        hop).pairing f ∈ V.dropSubset (cutL n) (cutR n) s)
    (hcL : ∀ f ∈ liftSubsetOpen hop
        (V.dropSubset (cutL n) (cutR n) s),
      V.pairing f ∈ liftSubsetOpen hop
        (V.dropSubset (cutL n) (cutR n) s))
    (hEL : (EdgeSubset.mk (liftSubsetOpen hop
      (V.dropSubset (cutL n) (cutR n) s)) hcL :
      EdgeSubset V).Eulerian)
    (hneL : Nonempty (EdgeSubset.mk
      (liftSubsetOpen hop
        (V.dropSubset (cutL n) (cutR n) s)) hcL :
      EdgeSubset V).CanonData)
    (hag : (𝒟 (liftSubsetOpen hop
          (V.dropSubset (cutL n) (cutR n) s)) hcL hEL hneL).2.isOut
        (V.pairing (V.boundaryFlag (cutR n)))
      = !(𝒟 (liftSubsetOpen hop
          (V.dropSubset (cutL n) (cutR n) s)) hcL hEL
          hneL).2.isOut (V.pairing (V.boundaryFlag (cutL n)))) :
    (pushData (n + 1) V (liftData (n + 1) V bits 𝒟) s hc hE
        hne).1.MatchEq (𝒟 s hc hE hne).1 := by
  have h1 := match_stepDataDown_congr_at_open n V hop
    (pushData n (stepFragment n V)
      (liftData n (stepFragment n V) (fun a => bits a.castSucc)
        (stepDataUp n V (bits (Fin.last n)) 𝒟)))
    (stepDataUp n V (bits (Fin.last n)) 𝒟) hIH hc hE hne
  rw [stepData_roundTrip_open n V hop (bits (Fin.last n)) 𝒟] at h1
  exact fun f hf => (h1 f hf).trans
    (match_unglue_glueDataOpen (cutL_ne_cutR n) hop 𝒟 hc hE hne
      hdc hcL hEL hneL hag f hf)

-- Raised budget: as for the directions, on the matching.
open Classical in
/-- **The interface round trip, one stage on, at a closing cut, at
one subset.**  The stage reads the family only at the subset the
drop makes, and the stage's bit is the one the subset itself
determines. -/
theorem match_pushData_liftData_succ_closed_at (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (bits : Fin (n + 1) → Bool) (𝒟 : DataFamily V)
    {s : Finset V.Flag} (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc : EdgeSubset V).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc : EdgeSubset V).CanonData)
    (hbit : bits (Fin.last n)
      = decide (V.boundaryFlag (cutL n) ∈ s))
    (hIH : ∀ (t : Finset (stepFragment n V).Flag),
      t = flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
          (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
          (gluePair_eq_closed n V hcl)
          (V.dropSubset (cutL n) (cutR n) s) →
      ∀ (hct : ∀ f ∈ t, (stepFragment n V).pairing f ∈ t)
        (hEt : (EdgeSubset.mk t hct).Eulerian)
        (hnet : Nonempty (EdgeSubset.mk t hct).CanonData),
      (pushData n (stepFragment n V)
          (liftData n (stepFragment n V)
            (fun a => bits a.castSucc)
            (stepDataUp n V (bits (Fin.last n)) 𝒟))
          t hct hEt hnet).1.MatchEq
        (stepDataUp n V (bits (Fin.last n)) 𝒟 t hct hEt hnet).1)
    (hcL : ∀ f ∈ liftSubsetClosed
        (V.dropSubset (cutL n) (cutR n) s)
        (decide (V.boundaryFlag (cutL n) ∈ s)),
      V.pairing f ∈ liftSubsetClosed
        (V.dropSubset (cutL n) (cutR n) s)
        (decide (V.boundaryFlag (cutL n) ∈ s)))
    (hEL : (EdgeSubset.mk (liftSubsetClosed
      (V.dropSubset (cutL n) (cutR n) s)
      (decide (V.boundaryFlag (cutL n) ∈ s))) hcL :
      EdgeSubset V).Eulerian)
    (hneL : Nonempty (EdgeSubset.mk (liftSubsetClosed
      (V.dropSubset (cutL n) (cutR n) s)
      (decide (V.boundaryFlag (cutL n) ∈ s))) hcL :
      EdgeSubset V).CanonData) :
    (pushData (n + 1) V (liftData (n + 1) V bits 𝒟) s hc hE
        hne).1.MatchEq (𝒟 s hc hE hne).1 := by
  have h1 := match_stepDataDown_congr_at_closed n V hcl
    (pushData n (stepFragment n V)
      (liftData n (stepFragment n V) (fun a => bits a.castSucc)
        (stepDataUp n V (bits (Fin.last n)) 𝒟)))
    (stepDataUp n V (bits (Fin.last n)) 𝒟) hIH hc hE hne
  rw [stepData_roundTrip_closed n V hcl (bits (Fin.last n)) 𝒟] at h1
  have h2 := match_unglue_glueDataClosed (cutL_ne_cutR n) hcl 𝒟 hc
    hE hne hcL hEL hneL
  rw [← hbit] at h2
  exact fun f hf => (h1 f hf).trans (h2 f hf)

/-! ## The summand factorizes over a disjoint union of closed
fragments

At empty label types the chord sign is one and every orientation is
path-canonical, so the pinned disjoint-union factorization reads
directly on the summand.
-/

open Classical in
/-- **The base subset's left half, brought down to the first
fragment, is the first subset.**  This is the form
`edgeSum_closeBase_eq_pairAgreeValue` reads its data at. -/
theorem relabelDown_leftSub_closeJoin {t : ℕ}
    {F G : Fragment (Fin t)} {s₁ : Finset F.Flag}
    {s₂ : Finset G.Flag}
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁) :
    EdgeSubset.relabelDown (finCongr (by omega : t = 0 + t))
        (leftSub (EdgeSubset.mk (closeJoin s₁ s₂) hc))
      = EdgeSubset.mk s₁ hc₁ :=
  EdgeSubset.ext (leftPart_joinParts
    (W₁ := F.relabel (finCongr (by omega : t = 0 + t)))
    (W₂ := G.relabel (finCongr (by omega : t = t + 0))) s₁ s₂)

open Classical in
/-- **The base subset's right half, brought down to the second
fragment, is the second subset.** -/
theorem relabelDown_rightSub_closeJoin {t : ℕ}
    {F G : Fragment (Fin t)} {s₁ : Finset F.Flag}
    {s₂ : Finset G.Flag}
    (hc : ∀ f ∈ closeJoin s₁ s₂,
      (closeBase F G).pairing f ∈ closeJoin s₁ s₂)
    (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂) :
    EdgeSubset.relabelDown (finCongr (by omega : t = t + 0))
        (rightSub (EdgeSubset.mk (closeJoin s₁ s₂) hc))
      = EdgeSubset.mk s₂ hc₂ :=
  EdgeSubset.ext (rightPart_joinParts
    (W₁ := F.relabel (finCongr (by omega : t = 0 + t)))
    (W₂ := G.relabel (finCongr (by omega : t = t + 0))) s₁ s₂)

open Classical in
/-- **The agreement value transports along equalities of the two
subsets.**  This is what lets (13)'s orientations, which live on the
fragments' own subsets, be read on the base subset's halves. -/
theorem pairAgreeValue_congr_subset {t : ℕ}
    {W₁ W₂ : Fragment (Fin t)} {F₁ F₁' : EdgeSubset W₁}
    (h₁ : F₁ = F₁') {F₂ F₂' : EdgeSubset W₂} (h₂ : F₂ = F₂')
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    {κ₁ : F₁.RelTransitionSystem} (o₁ : κ₁.Orientation)
    {κ₂ : F₂.RelTransitionSystem} (o₂ : κ₂.Orientation)
    (st : GenBoundaryState k ℓ (Fin t)) :
    pairAgreeValue F₁ F₂ h o₁ o₂ st
      = pairAgreeValue F₁' F₂' h (orientOfEq h₁ o₁)
        (orientOfEq h₂ o₂) st := by
  subst h₁
  subst h₂
  rfl

open Classical in
/-- **The pair's agreement value is the base subset's colouring
sum.**  RS21's (13) produces its orientations on the fragments' own
subsets; this reads the resulting agreement value on the base. -/
theorem pairAgreeValue_eq_edgeSum_closeJoin {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (t : ℕ) (F G : Fragment (Fin t))
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    {κ₁ : (EdgeSubset.mk s₁ hc₁).RelTransitionSystem}
    (o₁ : κ₁.Orientation)
    {κ₂ : (EdgeSubset.mk s₂ hc₂).RelTransitionSystem}
    (o₂ : κ₂.Orientation) (x : GenBoundaryState k ℓ (Fin t))
    (hbnd : genBoundarySubsetMatches (closeBase F G)
      (closeJoin s₁ s₂) (diagOf t x))
    (hbnd₁ : genBoundarySubsetMatches F
      (leftSub (EdgeSubset.mk (closeJoin s₁ s₂)
        (closeJoin_pairing_mem hc₁ hc₂))).flags x)
    (hbnd₂ : genBoundarySubsetMatches G
      (rightSub (EdgeSubset.mk (closeJoin s₁ s₂)
        (closeJoin_pairing_mem hc₁ hc₂))).flags x) :
    pairAgreeValue (EdgeSubset.mk s₁ hc₁) (EdgeSubset.mk s₂ hc₂) h
        o₁ o₂ x
      = (EdgeSubset.mk (closeJoin s₁ s₂)
          (closeJoin_pairing_mem hc₁ hc₂)).edgeSum h (diagOf t x)
          hbnd
          (prodOrient
            (relabelOrientUp (finCongr (by omega : t = 0 + t))
              (EdgeSubset.relabelDown
                (finCongr (by omega : t = 0 + t))
                (leftSub (EdgeSubset.mk (closeJoin s₁ s₂)
                  (closeJoin_pairing_mem hc₁ hc₂))))
              (orientOfEq (relabelDown_leftSub_closeJoin
                (closeJoin_pairing_mem hc₁ hc₂) hc₁).symm o₁))
            (relabelOrientUp (finCongr (by omega : t = t + 0))
              (EdgeSubset.relabelDown
                (finCongr (by omega : t = t + 0))
                (rightSub (EdgeSubset.mk (closeJoin s₁ s₂)
                  (closeJoin_pairing_mem hc₁ hc₂))))
              (orientOfEq (relabelDown_rightSub_closeJoin
                (closeJoin_pairing_mem hc₁ hc₂) hc₂).symm o₂))) := by
  rw [pairAgreeValue_congr_subset
    (relabelDown_leftSub_closeJoin
      (closeJoin_pairing_mem hc₁ hc₂) hc₁).symm
    (relabelDown_rightSub_closeJoin
      (closeJoin_pairing_mem hc₁ hc₂) hc₂).symm h o₁ o₂ x]
  exact (edgeSum_closeBase_eq_pairAgreeValue h t F G x
    (EdgeSubset.mk (closeJoin s₁ s₂)
      (closeJoin_pairing_mem hc₁ hc₂)) hbnd hbnd₁ hbnd₂ _ _).symm

/-- An internal flag is not a boundary flag: it is attached to a
vertex. -/
theorem ne_boundaryFlag_of_mem_internalFlags {L : Type}
    {V : Fragment L} (F : EdgeSubset V) {f : V.Flag}
    (hf : f ∈ F.internalFlags) (a : L) : f ≠ V.boundaryFlag a := by
  intro hx
  obtain ⟨_, v, hv⟩ := EdgeSubset.mem_internalFlags_iff.mp hf
  rw [hx, V.attach_boundaryFlag] at hv
  cases hv

open Classical in
/-- **A subset's term is its colouring sum at any data of the same
shape**, needing the directions only where the sum reads them. -/
theorem edgeTermAt_eq_signed_edgeSum_internal {k ℓ : ℕ} {L : Type}
    [LinearOrder L] {V : Fragment L} (h : MixedFunctional k ℓ)
    (𝒟 : DataFamily V) (st : GenBoundaryState k ℓ L)
    {s : Finset V.Flag} (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hbnd : genBoundarySubsetMatches V s st)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData) (C : ℕ)
    {κ : (EdgeSubset.mk s hc).RelTransitionSystem}
    (O : κ.Orientation)
    (hm : (𝒟 s hc hE hne).1.MatchEq κ)
    (hio : ∀ f ∈ (EdgeSubset.mk s hc).internalFlags,
      (𝒟 s hc hE hne).2.isOut f = O.isOut f) :
    edgeTermAt h 𝒟 st s C
      = ((-1 : ℂ) ^ C)
        * (EdgeSubset.mk s hc).edgeSum h st hbnd O := by
  rw [edgeTermAt_pos h 𝒟 st hc hbnd hE hne C]
  exact congrArg (fun z => ((-1 : ℂ) ^ C) * z)
    (edgeSum_matchEq_internal hm h st hbnd _ O hio)

/-- The left interface partner, read on the disjoint union. -/
theorem pairing_boundaryFlag_intL {t : ℕ} (F G : Fragment (Fin t))
    (m : Fin t) :
    (closeBase F G).pairing ((closeBase F G).boundaryFlag
        (intL t m))
      = Sum.inl ((F.relabel (finCongr (by omega : t = 0 + t))).pairing
        ((F.relabel (finCongr (by omega : t = 0 + t))).boundaryFlag
          (Fin.cast (by omega) m))) := rfl

/-- The right interface partner, read on the disjoint union. -/
theorem pairing_boundaryFlag_intR {t : ℕ} (F G : Fragment (Fin t))
    (m : Fin t) :
    (closeBase F G).pairing ((closeBase F G).boundaryFlag
        (intR t m))
      = Sum.inr ((G.relabel (finCongr (by omega : t = t + 0))).pairing
        ((G.relabel (finCongr (by omega : t = t + 0))).boundaryFlag
          (Fin.cast (by omega) m))) := rfl

/-- The flag the left half of the `m`-th cut points at. -/
noncomputable abbrev cutFlagL {t : ℕ} (F G : Fragment (Fin t))
    (m : Fin t) : (closeBase F G).Flag :=
  (closeBase F G).pairing ((closeBase F G).boundaryFlag (intL t m))

/-- The flag the right half of the `m`-th cut points at. -/
noncomputable abbrev cutFlagR {t : ℕ} (F G : Fragment (Fin t))
    (m : Fin t) : (closeBase F G).Flag :=
  (closeBase F G).pairing ((closeBase F G).boundaryFlag (intR t m))

/-- **A used, non-through left label has an internal cut flag.** -/
theorem internal_cutFlagL {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (m : Fin t)
    (hm : F.boundaryFlag m ∈ (EdgeSubset.mk s₁ hc₁).boundaryFlags)
    (hnt : ¬ IsThroughLabel (EdgeSubset.mk s₁ hc₁) m) :
    cutFlagL F G m ∈ (EdgeSubset.mk (closeJoin s₁ s₂)
      (closeJoin_pairing_mem hc₁ hc₂)).internalFlags := by
  refine inl_mem_internal.mpr ?_
  rw [leftSub_closeJoin (closeJoin_pairing_mem hc₁ hc₂) hc₁]
  have h := pairing_internal_of_not_through
    (EdgeSubset.mk s₁ hc₁) hm hnt
  rwa [← relabelUp_internalFlags (finCongr (Nat.zero_add t).symm)
    (EdgeSubset.mk s₁ hc₁)] at h

/-- **A used, non-through right label has an internal cut flag.** -/
theorem internal_cutFlagR {t : ℕ} {F G : Fragment (Fin t)}
    {s₁ : Finset F.Flag} (hc₁ : ∀ f ∈ s₁, F.pairing f ∈ s₁)
    {s₂ : Finset G.Flag} (hc₂ : ∀ f ∈ s₂, G.pairing f ∈ s₂)
    (m : Fin t)
    (hm : G.boundaryFlag m ∈ (EdgeSubset.mk s₂ hc₂).boundaryFlags)
    (hnt : ¬ IsThroughLabel (EdgeSubset.mk s₂ hc₂) m) :
    cutFlagR F G m ∈ (EdgeSubset.mk (closeJoin s₁ s₂)
      (closeJoin_pairing_mem hc₁ hc₂)).internalFlags := by
  refine inr_mem_internal.mpr ?_
  rw [rightSub_closeJoin (closeJoin_pairing_mem hc₁ hc₂) hc₂]
  have h := pairing_internal_of_not_through
    (EdgeSubset.mk s₂ hc₂) hm hnt
  rwa [← relabelUp_internalFlags (finCongr (Nat.add_zero t).symm)
    (EdgeSubset.mk s₂ hc₂)] at h

/-! ## The composition's weighted term is family-free

At an empty label type the circuit weight times the summand does not
depend on which data compute it.  This is what makes the
composition's side of the identity independent of the family, one
subset at a time.
-/

section WeightIndep

variable {L : Type}

open Classical in
/-- **The weighted summand at the composition is family-free.** -/
theorem circuitWeight_mul_edgeTermAt_indep
    [LinearOrder L] [IsEmpty L] {V : Fragment L}
    {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ L)
    (u : Finset V.Flag) (C : ℕ) (𝒟 𝒟' : DataFamily V) :
    circuitWeight 𝒟 u * edgeTermAt h 𝒟 st u C
      = circuitWeight 𝒟' u * edgeTermAt h 𝒟' st u C := by
  by_cases hc : ∀ f ∈ u, V.pairing f ∈ u
  · by_cases hbnd : genBoundarySubsetMatches V u st
    · by_cases hE : (EdgeSubset.mk u hc).Eulerian
      · by_cases hne : Nonempty (EdgeSubset.mk u hc).CanonData
        · rw [circuitWeight_pos 𝒟 hc hE hne,
            circuitWeight_pos 𝒟' hc hE hne,
            edgeTermAt_pos h 𝒟 st hc hbnd hE hne C,
            edgeTermAt_pos h 𝒟' st hc hbnd hE hne C]
          have hkey : ((-1 : ℂ) ^ (𝒟 u hc hE hne).1.openCircuitCount)
              * (EdgeSubset.mk u hc).edgeSum h st hbnd
                (𝒟 u hc hE hne).2
              = ((-1 : ℂ) ^ (𝒟' u hc hE hne).1.openCircuitCount)
                * (EdgeSubset.mk u hc).edgeSum h st hbnd
                  (𝒟' u hc hE hne).2 := by
            rw [← throughSummand_eq_edgeSum (EdgeSubset.mk u hc) h
                st hbnd _ _,
              ← throughSummand_eq_edgeSum (EdgeSubset.mk u hc) h st
                hbnd _ _]
            exact throughSummand_canon_indep (EdgeSubset.mk u hc) h
              st hbnd ⟨_, _, pathCanonical_isEmpty _ _⟩
              ⟨_, _, pathCanonical_isEmpty _ _⟩
          calc ((-1 : ℂ) ^ (𝒟 u hc hE hne).1.openCircuitCount)
                * (((-1 : ℂ) ^ C) *
                  (EdgeSubset.mk u hc).edgeSum h st hbnd
                    (𝒟 u hc hE hne).2)
              = ((-1 : ℂ) ^ C) *
                (((-1 : ℂ) ^ (𝒟 u hc hE hne).1.openCircuitCount) *
                  (EdgeSubset.mk u hc).edgeSum h st hbnd
                    (𝒟 u hc hE hne).2) := by ring
            _ = ((-1 : ℂ) ^ C) *
                (((-1 : ℂ) ^ (𝒟' u hc hE hne).1.openCircuitCount) *
                  (EdgeSubset.mk u hc).edgeSum h st hbnd
                    (𝒟' u hc hE hne).2) := by rw [hkey]
            _ = _ := by ring
        · rw [edgeTermAt_eq_zero_of_not_canon h 𝒟 st hc hne C,
            edgeTermAt_eq_zero_of_not_canon h 𝒟' st hc hne C,
            mul_zero, mul_zero]
      · rw [edgeTermAt_eq_zero_of_not_eulerian h 𝒟 st hc hE C,
          edgeTermAt_eq_zero_of_not_eulerian h 𝒟' st hc hE C,
          mul_zero, mul_zero]
    · rw [edgeTermAt_eq_zero_of_not_matches h 𝒟 st hbnd C,
        edgeTermAt_eq_zero_of_not_matches h 𝒟' st hbnd C,
        mul_zero, mul_zero]
  · rw [edgeTermAt_eq_zero_of_not_closed h 𝒟 st hc C,
      edgeTermAt_eq_zero_of_not_closed h 𝒟' st hc C,
      mul_zero, mul_zero]

end WeightIndep

end EdgeSubset

end RS
