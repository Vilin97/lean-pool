/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.ConverseLift

/-!
# The interface round trip

At an open cut the lift is a left inverse of the drop, and the family
pushed back down is the family itself.  Iterating over the interface
gives the composition's sum in terms of the base's own subsets.
-/

namespace RS

namespace EdgeSubset

open Fragment
/-- The lexicographic order on the interface's label type. -/
@[reducible] local instance tripBaseOrder (n : ℕ) :
    LinearOrder (Fin (0 + n) ⊕ Fin (n + 0)) :=
  sumLexLinearOrder _ _

/-- The same order one stage up. -/
@[reducible] local instance tripOrderSucc (n : ℕ) :
    LinearOrder (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) :=
  sumLexLinearOrder _ _

/-- The order a stage's surviving labels carry. -/
@[reducible] local instance tripSurvOrder (n : ℕ) :
    LinearOrder (SurvivingLabel
      (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) (cutL n) (cutR n)) :=
  sumLexSubtypeLinearOrder _ _ _

/-- The order the composition's own label type carries. -/
@[reducible] local instance tripTopOrder :
    LinearOrder (Fin 0 ⊕ Fin 0) :=
  sumLexLinearOrder _ _

/-! ## An open cut loses nothing

At an open cut the lift is a left inverse of the drop, so the drop is
injective on subsets closed under the pairing.  This is why a fibre
is a singleton when no cut on the way to it closes.
-/

open Classical in
/-- **A closed subset matching a diagonal state has a rewire-closed
drop.**  So the terms the identity reads are the reached ones, and
off them everything vanishes. -/
theorem dropSubset_rewire_closed_of_matches {k ℓ : ℕ} (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (s : Finset V.Flag) (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (x : Fin (n + 1) → (Fin k ⊕ Fin (2 * ℓ)))
    (hm : genBoundarySubsetMatches V s (diagOf (n + 1) x)) :
    ∀ f ∈ V.dropSubset (cutL n) (cutR n) s,
      (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n)
        hop).pairing f
        ∈ V.dropSubset (cutL n) (cutR n) s := by
  have hlift : liftSubsetOpen hop
      (V.dropSubset (cutL n) (cutR n) s) = s :=
    liftSubsetOpen_dropSubset (cutL_ne_cutR n) hop s hc
  have hcl : ∀ f ∈ liftSubsetOpen hop
      (V.dropSubset (cutL n) (cutR n) s),
      V.pairing f ∈ liftSubsetOpen hop
        (V.dropSubset (cutL n) (cutR n) s) := by
    rw [hlift]; exact hc
  refine rewire_closed_of_liftOpen_closed (cutL_ne_cutR n) hop
    (V.dropSubset (cutL n) (cutR n) s)
    (stageState n (diagOf n (fun a => x a.castSucc)))
    (x (Fin.last n)) hcl ?_
  rw [hlift, ← diagOf_succ n x]
  exact hm

open Classical in
/-- **The drop matches the stage's diagonal state.**  So the
boundary constraint descends the interface along with the subset. -/
theorem dropSubset_matches_of_matches {k ℓ : ℕ} (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (s : Finset V.Flag) (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (x : Fin (n + 1) → (Fin k ⊕ Fin (2 * ℓ)))
    (hm : genBoundarySubsetMatches V s (diagOf (n + 1) x)) :
    genBoundarySubsetMatches
      (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
      (V.dropSubset (cutL n) (cutR n) s)
      (stageState n (diagOf n (fun a => x a.castSucc))) := by
  refine genBoundarySubsetMatches_glued_of_liftOpen
    (cutL_ne_cutR n) hop (V.dropSubset (cutL n) (cutR n) s) _
    (x (Fin.last n)) (x (Fin.last n)) ?_
  rw [liftSubsetOpen_dropSubset (cutL_ne_cutR n) hop s hc,
    ← diagOf_succ n x]
  exact hm

/-- The boundary constraint transports along an equality of
fragments. -/
theorem genBoundarySubsetMatches_flagsOfEq {k ℓ : ℕ} {L : Type}
    {V₁ V₂ : Fragment L} (hV : V₁ = V₂) (s : Finset V₁.Flag)
    (st : GenBoundaryState k ℓ L)
    (h : genBoundarySubsetMatches V₁ s st) :
    genBoundarySubsetMatches V₂ (flagsOfEq V₁ V₂ hV s) st := by
  subst hV; exact h

open Classical in
/-- **The stage subset matches the stage's diagonal state.**  This is
`dropSubset_matches_of_matches` read at the stage fragment, across the
relabel that renumbers the surviving labels. -/
theorem stage_matches_of_matches {k ℓ : ℕ} (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (s : Finset V.Flag) (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (x : Fin (n + 1) → (Fin k ⊕ Fin (2 * ℓ)))
    (hm : genBoundarySubsetMatches V s (diagOf (n + 1) x)) :
    genBoundarySubsetMatches (stepFragment n V)
      (flagsOfEq
        (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
        (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
        (gluePair_eq_open n V hop)
        (V.dropSubset (cutL n) (cutR n) s))
      (diagOf n (fun a => x a.castSucc)) := by
  refine (relabel_genBoundarySubsetMatches_iff
    (interfaceStepEquiv 0 n 0) _
    (diagOf n (fun a => x a.castSucc))).mpr ?_
  exact genBoundarySubsetMatches_flagsOfEq
    (gluePair_eq_open n V hop) _ _
    (dropSubset_matches_of_matches n V hop s hc x hm)

open Classical in
/-- **One subset is enough for the directions**, at an open cut. -/
theorem isOut_unglueDataOpen_congr_at {α : Type} [LinearOrder α]
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
        EdgeSubset (V.gluePairOpen i j hij hopen)).CanonData)
      (g : SurvivingFlag V i j),
      (∀ ℓ, g ≠ (V.gluePairOpen i j hij hopen).boundaryFlag ℓ) →
      (𝒟₁ _ hct hEt hnet).2.isOut g = (𝒟₂ _ hct hEt hnet).2.isOut g)
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc : EdgeSubset V).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc : EdgeSubset V).CanonData)
    (f : V.Flag) (hfb : ∀ a, f ≠ V.boundaryFlag a) :
    (unglueDataOpen hij hopen 𝒟₁ s hc hE hne).2.isOut f
      = (unglueDataOpen hij hopen 𝒟₂ s hc hE hne).2.isOut f := by
  have h1 : f ≠ V.boundaryFlag i := hfb i
  have h2 : f ≠ V.boundaryFlag j := hfb j
  unfold unglueDataOpen
  by_cases hag : ∀ f ∈ V.dropSubset i j s,
      (V.gluePairOpen i j hij hopen).pairing f
        ∈ V.dropSubset i j s
  · rw [dite_eq_left hag, dite_eq_left hag, isOut_orientOfEq, isOut_orientOfEq]
    refine Eq.trans (unglueIsOut_of_surviving _ f ⟨h1, h2⟩) ?_
    refine Eq.trans ?_ (unglueIsOut_of_surviving _ f ⟨h1, h2⟩).symm
    exact hm _ _ _ _ (fun ℓ hx => hfb ℓ.val (congrArg Subtype.val hx))
  · rw [dite_eq_right hag, dite_eq_right hag]

open Classical in
/-- **One subset is enough for the directions**, at a closing
cut. -/
theorem isOut_unglueDataClosed_congr_at {α : Type} [LinearOrder α]
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
        EdgeSubset (V.gluePairClosed i j hclosed)).CanonData)
      (g : SurvivingFlag V i j),
      (∀ ℓ, g ≠ (V.gluePairClosed i j hclosed).boundaryFlag ℓ) →
      (𝒟₁ _ hct hEt hnet).2.isOut g = (𝒟₂ _ hct hEt hnet).2.isOut g)
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc : EdgeSubset V).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc : EdgeSubset V).CanonData)
    (f : V.Flag) (hfb : ∀ a, f ≠ V.boundaryFlag a) :
    (unglueDataClosed hij hclosed 𝒟₁ s hc hE hne).2.isOut f
      = (unglueDataClosed hij hclosed 𝒟₂ s hc hE hne).2.isOut f := by
  have h1 : f ≠ V.boundaryFlag i := hfb i
  have h2 : f ≠ V.boundaryFlag j := hfb j
  unfold unglueDataClosed
  rw [isOut_orientOfEq, isOut_orientOfEq]
  refine Eq.trans (unglueIsOut_of_surviving _ f ⟨h1, h2⟩) ?_
  refine Eq.trans ?_ (unglueIsOut_of_surviving _ f ⟨h1, h2⟩).symm
  exact hm _ _ _ _ (fun ℓ hx => hfb ℓ.val (congrArg Subtype.val hx))

open Classical in
/-- **One subset is enough for the directions**, under a
transport. -/
theorem isOut_dataOfEq_congr_at {L : Type} [LinearOrder L]
    {V₁ V₂ : Fragment L} (h : V₁ = V₂) (𝒟₁ 𝒟₂ : DataFamily V₂)
    (s : Finset V₁.Flag)
    (hm : ∀ (hc' : ∀ f ∈ flagsOfEq V₁ V₂ h s,
        V₂.pairing f ∈ flagsOfEq V₁ V₂ h s)
      (hE' : (EdgeSubset.mk (flagsOfEq V₁ V₂ h s) hc').Eulerian)
      (hne' : Nonempty
        (EdgeSubset.mk (flagsOfEq V₁ V₂ h s) hc').CanonData)
      (g : V₂.Flag), (∀ ℓ, g ≠ V₂.boundaryFlag ℓ) →
      (𝒟₁ _ hc' hE' hne').2.isOut g = (𝒟₂ _ hc' hE' hne').2.isOut g)
    (hc : ∀ f ∈ s, V₁.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData) (f : V₁.Flag)
    (hfb : ∀ ℓ, f ≠ V₁.boundaryFlag ℓ) :
    (dataOfEq h 𝒟₁ s hc hE hne).2.isOut f
      = (dataOfEq h 𝒟₂ s hc hE hne).2.isOut f := by
  subst h
  exact hm hc hE hne f hfb

open Classical in
/-- **One subset is enough for the directions**, under a relabel. -/
theorem isOut_relabelDataDown_congr_at {α' β' : Type}
    [LinearOrder α'] [LinearOrder β'] (e : α' ≃o β')
    {W' : Fragment α'} (𝒟₁ 𝒟₂ : DataFamily (W'.relabel e.toEquiv))
    (s : Finset W'.Flag)
    (hm : ∀ (hc' : ∀ f ∈ s, (W'.relabel e.toEquiv).pairing f ∈ s)
      (hE' : (EdgeSubset.mk s hc' :
        EdgeSubset (W'.relabel e.toEquiv)).Eulerian)
      (hne' : Nonempty (EdgeSubset.mk s hc' :
        EdgeSubset (W'.relabel e.toEquiv)).CanonData)
      (g : W'.Flag),
      (∀ b, g ≠ (W'.relabel e.toEquiv).boundaryFlag b) →
      (𝒟₁ s hc' hE' hne').2.isOut g = (𝒟₂ s hc' hE' hne').2.isOut g)
    (hc : ∀ f ∈ s, W'.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData) (f : W'.Flag)
    (hfb : ∀ a, f ≠ W'.boundaryFlag a) :
    (relabelDataDown e 𝒟₁ s hc hE hne).2.isOut f
      = (relabelDataDown e 𝒟₂ s hc hE hne).2.isOut f :=
  hm hc _ _ f (fun b hx => hfb (e.symm b) (by
    rw [hx, ← relabel_boundaryFlag_apply e.toEquiv (e.symm b)]
    exact congrArg (W'.relabel e.toEquiv).boundaryFlag
      (e.apply_symm_apply b).symm))

open Classical in
/-- **One subset is enough for the directions**, for a whole stage of
the push at an open cut. -/
theorem isOut_stepDataDown_congr_at_open (n : ℕ)
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
        (hnet : Nonempty (EdgeSubset.mk t hct).CanonData)
        (g : (stepFragment n V).Flag),
      (∀ b, g ≠ (stepFragment n V).boundaryFlag b) →
      (𝒟₁ t hct hEt hnet).2.isOut g = (𝒟₂ t hct hEt hnet).2.isOut g)
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData) (f : V.Flag)
    (hfb : ∀ a, f ≠ V.boundaryFlag a) :
    (stepDataDown n V 𝒟₁ s hc hE hne).2.isOut f
      = (stepDataDown n V 𝒟₂ s hc hE hne).2.isOut f := by
  unfold stepDataDown
  rw [dite_eq_right hop, dite_eq_right hop]
  refine isOut_unglueDataOpen_congr_at (cutL_ne_cutR n) hop _ _
    ?_ hc hE hne f hfb
  intro hct hEt hnet g hgb
  refine isOut_dataOfEq_congr_at (gluePair_eq_open n V hop) _ _
    (V.dropSubset (cutL n) (cutR n) s) ?_ hct hEt hnet g hgb
  intro hc' hE' hne' g' hgb'
  exact isOut_relabelDataDown_congr_at (stepIso n) 𝒟₁ 𝒟₂ _
    (hm _ rfl) hc' hE' hne' g' hgb'

open Classical in
/-- **One subset is enough for the directions**, for a whole stage of
the push at a closing cut. -/
theorem isOut_stepDataDown_congr_at_closed (n : ℕ)
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
        (hnet : Nonempty (EdgeSubset.mk t hct).CanonData)
        (g : (stepFragment n V).Flag),
      (∀ b, g ≠ (stepFragment n V).boundaryFlag b) →
      (𝒟₁ t hct hEt hnet).2.isOut g = (𝒟₂ t hct hEt hnet).2.isOut g)
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData) (f : V.Flag)
    (hfb : ∀ a, f ≠ V.boundaryFlag a) :
    (stepDataDown n V 𝒟₁ s hc hE hne).2.isOut f
      = (stepDataDown n V 𝒟₂ s hc hE hne).2.isOut f := by
  unfold stepDataDown
  rw [dite_eq_left hcl, dite_eq_left hcl]
  refine isOut_unglueDataClosed_congr_at (cutL_ne_cutR n) hcl _ _
    ?_ hc hE hne f hfb
  intro hct hEt hnet g hgb
  refine isOut_dataOfEq_congr_at (gluePair_eq_closed n V hcl) _ _
    (V.dropSubset (cutL n) (cutR n) s) ?_ hct hEt hnet g hgb
  intro hc' hE' hne' g' hgb'
  exact isOut_relabelDataDown_congr_at (stepIso n) 𝒟₁ 𝒟₂ _
    (hm _ rfl) hc' hE' hne' g' hgb'

open Classical in
/-- **The interface round trip on directions, at no cuts.** -/
theorem isOut_pushData_liftData_zero
    (V : Fragment (Fin (0 + 0) ⊕ Fin (0 + 0)))
    (bits : Fin 0 → Bool) (𝒟 : DataFamily V) (s : Finset V.Flag)
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData) (f : V.Flag) :
    (pushData 0 V (liftData 0 V bits 𝒟) s hc hE hne).2.isOut f
      = (𝒟 s hc hE hne).2.isOut f := rfl

open Classical in
/-- **The interface round trip on directions, one stage on — at an
open cut.**  Away from the cut's own two flags the directions come
back on the nose. -/
theorem isOut_pushData_liftData_succ_open_at (n : ℕ)
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
        (hnet : Nonempty (EdgeSubset.mk t hct).CanonData)
        (g : (stepFragment n V).Flag),
      (∀ b, g ≠ (stepFragment n V).boundaryFlag b) →
      (pushData n (stepFragment n V)
          (liftData n (stepFragment n V)
            (fun a => bits a.castSucc)
            (stepDataUp n V (bits (Fin.last n)) 𝒟))
          t hct hEt hnet).2.isOut g
        = (stepDataUp n V (bits (Fin.last n)) 𝒟
            t hct hEt hnet).2.isOut g)
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
          hneL).2.isOut (V.pairing (V.boundaryFlag (cutL n))))
    (f : V.Flag) (hfb : ∀ a, f ≠ V.boundaryFlag a) :
    (pushData (n + 1) V (liftData (n + 1) V bits 𝒟) s hc hE
        hne).2.isOut f = (𝒟 s hc hE hne).2.isOut f := by
  have h1 : f ≠ V.boundaryFlag (cutL n) := hfb _
  have h2 : f ≠ V.boundaryFlag (cutR n) := hfb _
  have h3 := isOut_stepDataDown_congr_at_open n V hop
    (pushData n (stepFragment n V)
      (liftData n (stepFragment n V) (fun a => bits a.castSucc)
        (stepDataUp n V (bits (Fin.last n)) 𝒟)))
    (stepDataUp n V (bits (Fin.last n)) 𝒟) hIH hc hE hne f hfb
  rw [stepData_roundTrip_open n V hop (bits (Fin.last n)) 𝒟] at h3
  exact h3.trans (isOut_unglue_glueDataOpen (cutL_ne_cutR n) hop 𝒟
    hc hE hne hdc hcL hEL hneL hag f h1 h2)

open Classical in
/-- **The upward glue respects matching equality.**  At an internal
flag the glued system's partner is the base system's, so two systems
that agree there glue to systems that agree. -/
theorem glueOpen_matchEq {α : Type} {W : Fragment α}
    {i j : α} (hij : i ≠ j)
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (s' : Finset (SurvivingFlag W i j))
    (hc' : ∀ f ∈ s', (W.gluePairOpen i j hij hopen).pairing f ∈ s')
    (hc : ∀ f ∈ liftSubsetOpen hopen s',
      W.pairing f ∈ liftSubsetOpen hopen s')
    {κ₁ κ₂ : (EdgeSubset.mk (liftSubsetOpen hopen s') hc :
      EdgeSubset W).RelTransitionSystem} (hm : κ₁.MatchEq κ₂) :
    (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ₁).MatchEq
      (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ₂) := by
  intro f' hf'
  refine Subtype.ext ?_
  rw [glueOpen_match_val hij hopen s' hc' hc κ₁ hf',
    glueOpen_match_val hij hopen s' hc' hc κ₂ hf']
  exact hm f'.val (internal_val_of_glueOpen hij hopen s' hc' hc hf')

open Classical in
/-- **The closing glue respects matching equality.**  It keeps every
internal flag's partner, so two systems that agree there glue to
systems that agree. -/
theorem glueClosed_matchEq {α : Type}
    {W : Fragment α} {i j : α}
    (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
    (b : Bool) (s' : Finset (SurvivingFlag W i j))
    (hc' : ∀ f ∈ s', (W.gluePairClosed i j hclosed).pairing f ∈ s')
    (hc : ∀ f ∈ liftSubsetClosed s' b,
      W.pairing f ∈ liftSubsetClosed s' b)
    {κ₁ κ₂ : (EdgeSubset.mk (liftSubsetClosed s' b) hc :
      EdgeSubset W).RelTransitionSystem} (hm : κ₁.MatchEq κ₂) :
    (RelTransitionSystem.glueClosed hclosed b s' hc' hc κ₁).MatchEq
      (RelTransitionSystem.glueClosed hclosed b s' hc' hc κ₂) := by
  intro f' hf'
  refine Subtype.ext ?_
  rw [glueClosed_match_val hclosed b s' hc' hc κ₁ hf',
    glueClosed_match_val hclosed b s' hc' hc κ₂ hf']
  exact hm f'.val
    (internal_val_of_glueClosed hclosed b s' hc' hc hf')

/-- **The upward relabel respects matching equality.**  It keeps the
partner map and only renames the labels. -/
theorem relabelTransUp_matchEq {α' β' : Type}
    (ee : α' ≃ β') {W' : Fragment α'}
    (F : EdgeSubset W') {κ₁ κ₂ : F.RelTransitionSystem}
    (hm : κ₁.MatchEq κ₂) :
    (relabelTransUp ee F κ₁).MatchEq (relabelTransUp ee F κ₂) :=
  fun f hf => hm f (by rwa [relabelUp_internalFlags ee F] at hf)

open Classical in
/-- **The family's upward glue is the ledger's**, at an open cut: a
family whose data at the stage's subset match the stage's system
glues to a system matching the ledger's glue. -/
theorem match_glueDataOpen_stepDataOpen (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (𝒟 : DataFamily V) (D : StageData (n + 1) V)
    (hcompat : ∀ hc hE hne,
      (𝒟 D.sub.flags hc hE hne).1.MatchEq D.rel)
    (hag : ∀ hcL hEL hneL,
      (𝒟 (liftSubsetOpen hop
            (stepFlags n V D)) hcL hEL hneL).2.isOut
          (V.pairing (V.boundaryFlag (cutR n)))
        = !(𝒟 (liftSubsetOpen hop
            (stepFlags n V D)) hcL hEL hneL).2.isOut
          (V.pairing (V.boundaryFlag (cutL n))))
    (hct : ∀ f ∈ stepFlags n V D,
      (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n)
        hop).pairing f ∈ stepFlags n V D)
    (hEt : (EdgeSubset.mk (stepFlags n V D) hct :
      EdgeSubset (V.gluePairOpen (cutL n) (cutR n)
        (cutL_ne_cutR n) hop)).Eulerian)
    (hnet : Nonempty (EdgeSubset.mk (stepFlags n V D) hct :
      EdgeSubset (V.gluePairOpen (cutL n) (cutR n)
        (cutL_ne_cutR n) hop)).CanonData) :
    (glueDataOpen (cutL_ne_cutR n) hop 𝒟 (stepFlags n V D) hct hEt
        hnet).1.MatchEq
      (RelTransitionSystem.glueOpen (cutL_ne_cutR n) hop
        (stepFlags n V D) hct
        (liftSubsetOpen_stepFlags_pairing_mem n V D hop)
        (relOfEq (sub_eq_liftSubsetOpen n V D hop) D.rel)) := by
  unfold glueDataOpen
  rw [dite_eq_left (hag _ _ _)]
  refine glueOpen_matchEq (cutL_ne_cutR n) hop (stepFlags n V D) hct
    (liftSubsetOpen_stepFlags_pairing_mem n V D hop) ?_
  intro f hf
  have hEq : (EdgeSubset.mk (liftSubsetOpen hop
        (stepFlags n V D))
      (liftSubsetOpen_stepFlags_pairing_mem n V D hop) :
      EdgeSubset V)
      = EdgeSubset.mk D.sub.flags D.sub.pairing_mem :=
    EdgeSubset.ext (liftSubsetOpen_stepFlags n V D hop)
  have hcL := liftSubsetOpen_pairing_closed (cutL_ne_cutR n) hop
    (stepFlags n V D) hct
  have hEL := (eulerian_lift_open_iff (cutL_ne_cutR n) hop
    (stepFlags n V D) hct hcL).mpr hEt
  have hneL := nonempty_canonData_unglueOpen (cutL_ne_cutR n) hop
    (stepFlags n V D) hct hcL hnet
  have hED : (EdgeSubset.mk D.sub.flags D.sub.pairing_mem :
      EdgeSubset V).Eulerian := hEq ▸ hEL
  have hneD : Nonempty (EdgeSubset.mk D.sub.flags D.sub.pairing_mem :
      EdgeSubset V).CanonData := hEq ▸ hneL
  refine Eq.trans ?_ (match_relOfEq (sub_eq_liftSubsetOpen n V D hop)
    D.rel f).symm
  exact (match_dataFamily_congr 𝒟
      (liftSubsetOpen_stepFlags n V D hop) hcL hEL hneL
      D.sub.pairing_mem hED hneD f).trans
    (hcompat D.sub.pairing_mem hED hneD f (hEq ▸ hf))

/-- The transport of a subset, undone. -/
theorem flagsOfEq_symm {L : Type} {V₁ V₂ : Fragment L} (h : V₁ = V₂)
    (t : Finset V₁.Flag) :
    flagsOfEq V₂ V₁ h.symm (flagsOfEq V₁ V₂ h t) = t := by
  subst h
  rfl

/-- The upward relabel and a transport commute. -/
theorem relabelDataUp_dataOfEq {L L' : Type} [LinearOrder L]
    [LinearOrder L'] (e : L ≃o L') {W₁ W₂ : Fragment L}
    (hW : W₁ = W₂) (𝒳 : DataFamily W₂) :
    relabelDataUp e (dataOfEq hW 𝒳)
      = dataOfEq (congrArg (fun X => X.relabel e.toEquiv) hW)
        (relabelDataUp e 𝒳) := by
  subst hW
  rfl

/-- **Both sides transported alike.**  A family that matches a stage
datum still matches it after both are carried along an equality of
fragments. -/
theorem match_dataOfEq_stageDataOfEq {m : ℕ}
    {V₁ V₂ : Fragment (Fin (0 + m) ⊕ Fin (m + 0))} (hV : V₁ = V₂)
    (Dm : StageData m V₁) (𝒴 : DataFamily V₁)
    (hm : ∀ hc hE hne, (𝒴 Dm.sub.flags hc hE hne).1.MatchEq Dm.rel)
    (hc : ∀ f ∈ (stageDataOfEq hV Dm).sub.flags,
      V₂.pairing f ∈ (stageDataOfEq hV Dm).sub.flags)
    (hE : (EdgeSubset.mk (stageDataOfEq hV Dm).sub.flags hc).Eulerian)
    (hne : Nonempty
      (EdgeSubset.mk (stageDataOfEq hV Dm).sub.flags hc).CanonData) :
    (dataOfEq hV.symm 𝒴 (stageDataOfEq hV Dm).sub.flags hc hE
        hne).1.MatchEq (stageDataOfEq hV Dm).rel := by
  subst hV
  exact hm hc hE hne

open Classical in
/-- **The lifted family matches the ledger's step**, before the
transport that the dispatch on the cut demands. -/
theorem match_relabelDataUp_stepDataOpen (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (𝒟 : DataFamily V) (D : StageData (n + 1) V)
    (hcompat : ∀ hc hE hne,
      (𝒟 D.sub.flags hc hE hne).1.MatchEq D.rel)
    (hag : ∀ hcL hEL hneL,
      (𝒟 (liftSubsetOpen hop
            (stepFlags n V D)) hcL hEL hneL).2.isOut
          (V.pairing (V.boundaryFlag (cutR n)))
        = !(𝒟 (liftSubsetOpen hop
            (stepFlags n V D)) hcL hEL hneL).2.isOut
          (V.pairing (V.boundaryFlag (cutL n))))
    (hc : ∀ f ∈ (stepDataOpen n V D hop).sub.flags,
      ((V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n)
        hop).relabel (interfaceStepEquiv 0 n 0)).pairing f
        ∈ (stepDataOpen n V D hop).sub.flags)
    (hE : (EdgeSubset.mk (stepDataOpen n V D hop).sub.flags
      hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk (stepDataOpen n V D hop).sub.flags
      hc).CanonData) :
    (relabelDataUp (stepIso n)
        (glueDataOpen (cutL_ne_cutR n) hop 𝒟)
        (stepDataOpen n V D hop).sub.flags hc hE
        hne).1.MatchEq (stepDataOpen n V D hop).rel :=
  relabelTransUp_matchEq (stepIso n).toEquiv _
    (match_glueDataOpen_stepDataOpen n V hop 𝒟 D hcompat hag _ _ _)

open Classical in
/-- **One stage of the lift matches one stage of the ledger.**  At an
open cut the family's glue and the ledger's step are the same system
up to its partner map, transports and relabel included. -/
theorem match_stepDataUp_stepData_open (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (b : Bool) (𝒟 : DataFamily V) (D : StageData (n + 1) V)
    (hcompat : ∀ hc hE hne,
      (𝒟 D.sub.flags hc hE hne).1.MatchEq D.rel)
    (hag : ∀ hcL hEL hneL,
      (𝒟 (liftSubsetOpen hop
            (stepFlags n V D)) hcL hEL hneL).2.isOut
          (V.pairing (V.boundaryFlag (cutR n)))
        = !(𝒟 (liftSubsetOpen hop
            (stepFlags n V D)) hcL hEL hneL).2.isOut
          (V.pairing (V.boundaryFlag (cutL n))))
    (hct : ∀ f ∈ (stepData n V D).sub.flags,
      (stepFragment n V).pairing f ∈ (stepData n V D).sub.flags)
    (hEt : (EdgeSubset.mk (stepData n V D).sub.flags hct).Eulerian)
    (hnet : Nonempty
      (EdgeSubset.mk (stepData n V D).sub.flags hct).CanonData) :
    (stepDataUp n V b 𝒟 (stepData n V D).sub.flags hct hEt
        hnet).1.MatchEq (stepData n V D).rel := by
  have hup : stepDataUp n V b 𝒟
      = dataOfEq (congrArg (fun X => X.relabel
            (interfaceStepEquiv 0 n 0))
          (gluePair_eq_open n V hop).symm)
        (relabelDataUp (stepIso n)
          (glueDataOpen (cutL_ne_cutR n) hop 𝒟)) := by
    unfold stepDataUp
    rw [dite_eq_right hop, relabelDataUp_dataOfEq]
    rfl
  revert hct hEt hnet
  rw [show stepData n V D = _ from dite_eq_right hop, hup]
  intro hct hEt hnet
  exact match_dataOfEq_stageDataOfEq
    (congrArg (fun X => X.relabel (interfaceStepEquiv 0 n 0))
      (gluePair_eq_open n V hop))
    (stepDataOpen n V D hop)
    (relabelDataUp (stepIso n)
      (glueDataOpen (cutL_ne_cutR n) hop 𝒟))
    (fun hc hE hne => match_relabelDataUp_stepDataOpen n V hop 𝒟 D
      hcompat hag hc hE hne) hct hEt hnet

open Classical in
/-- **The family's upward glue is the ledger's**, at a closing cut.
The ledger's own bit is the one the subset determines, and with it
the glue reads the family at exactly the ledger's subset. -/
theorem match_glueDataClosed_stepDataClosed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (𝒟 : DataFamily V) (D : StageData (n + 1) V)
    (hcompat : ∀ hc hE hne,
      (𝒟 D.sub.flags hc hE hne).1.MatchEq D.rel)
    (hct : ∀ f ∈ stepFlags n V D,
      (V.gluePairClosed (cutL n) (cutR n) hcl).pairing f
        ∈ stepFlags n V D)
    (hEt : (EdgeSubset.mk (stepFlags n V D) hct :
      EdgeSubset (V.gluePairClosed (cutL n) (cutR n)
        hcl)).Eulerian)
    (hnet : Nonempty (EdgeSubset.mk (stepFlags n V D) hct :
      EdgeSubset (V.gluePairClosed (cutL n) (cutR n)
        hcl)).CanonData) :
    (glueDataClosed hcl (stepBit n V D) 𝒟 (stepFlags n V D) hct hEt
        hnet).1.MatchEq
      (RelTransitionSystem.glueClosed hcl (stepBit n V D)
        (stepFlags n V D) hct
        (liftSubsetClosed_stepFlags_pairing_mem n V D hcl)
        (relOfEq (sub_eq_liftSubsetClosed n V D hcl) D.rel)) := by
  refine glueClosed_matchEq hcl (stepBit n V D) (stepFlags n V D)
    hct (liftSubsetClosed_stepFlags_pairing_mem n V D hcl) ?_
  intro f hf
  have hEq : (EdgeSubset.mk (liftSubsetClosed (stepFlags n V D)
        (stepBit n V D))
      (liftSubsetClosed_stepFlags_pairing_mem n V D hcl) :
      EdgeSubset V)
      = EdgeSubset.mk D.sub.flags D.sub.pairing_mem :=
    EdgeSubset.ext (liftSubsetClosed_stepFlags n V D hcl)
  have hcL := liftSubsetClosed_stepFlags_pairing_mem n V D hcl
  have hEL := (eulerian_liftClosed_iff' hcl (stepBit n V D)
    (stepFlags n V D) hct hcL).mpr hEt
  have hneL := nonempty_canonData_unglueClosed hcl
    (stepFlags n V D) hct (stepBit n V D) hcL hnet
  have hED : (EdgeSubset.mk D.sub.flags D.sub.pairing_mem :
      EdgeSubset V).Eulerian := hEq ▸ hEL
  have hneD : Nonempty (EdgeSubset.mk D.sub.flags D.sub.pairing_mem :
      EdgeSubset V).CanonData := hEq ▸ hneL
  refine Eq.trans ?_ (match_relOfEq
    (sub_eq_liftSubsetClosed n V D hcl) D.rel f).symm
  exact (match_dataFamily_congr 𝒟
      (liftSubsetClosed_stepFlags n V D hcl) hcL hEL hneL
      D.sub.pairing_mem hED hneD f).trans
    (hcompat D.sub.pairing_mem hED hneD f (hEq ▸ hf))

open Classical in
/-- **The lifted family matches the ledger's step**, at a closing
cut, before the transport the dispatch demands. -/
theorem match_relabelDataUp_stepDataClosed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (𝒟 : DataFamily V) (D : StageData (n + 1) V)
    (hcompat : ∀ hc hE hne,
      (𝒟 D.sub.flags hc hE hne).1.MatchEq D.rel)
    (hc : ∀ f ∈ (stepDataClosed n V D hcl).sub.flags,
      ((V.gluePairClosed (cutL n) (cutR n) hcl).relabel
        (interfaceStepEquiv 0 n 0)).pairing f
        ∈ (stepDataClosed n V D hcl).sub.flags)
    (hE : (EdgeSubset.mk (stepDataClosed n V D hcl).sub.flags
      hc).Eulerian)
    (hne : Nonempty
      (EdgeSubset.mk (stepDataClosed n V D hcl).sub.flags
        hc).CanonData) :
    (relabelDataUp (stepIso n)
        (glueDataClosed hcl (stepBit n V D) 𝒟)
        (stepDataClosed n V D hcl).sub.flags hc hE
        hne).1.MatchEq (stepDataClosed n V D hcl).rel :=
  relabelTransUp_matchEq (stepIso n).toEquiv _
    (match_glueDataClosed_stepDataClosed n V hcl 𝒟 D hcompat _ _ _)

open Classical in
/-- **One stage of the lift matches one stage of the ledger**, at a
closing cut: with the subset's own bit the family's glue and the
ledger's step are the same system up to its partner map. -/
theorem match_stepDataUp_stepData_closed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (𝒟 : DataFamily V) (D : StageData (n + 1) V)
    (hcompat : ∀ hc hE hne,
      (𝒟 D.sub.flags hc hE hne).1.MatchEq D.rel)
    (hct : ∀ f ∈ (stepData n V D).sub.flags,
      (stepFragment n V).pairing f ∈ (stepData n V D).sub.flags)
    (hEt : (EdgeSubset.mk (stepData n V D).sub.flags hct).Eulerian)
    (hnet : Nonempty
      (EdgeSubset.mk (stepData n V D).sub.flags hct).CanonData) :
    (stepDataUp n V (stepBit n V D) 𝒟 (stepData n V D).sub.flags
        hct hEt hnet).1.MatchEq (stepData n V D).rel := by
  have hup : stepDataUp n V (stepBit n V D) 𝒟
      = dataOfEq (congrArg (fun X => X.relabel
            (interfaceStepEquiv 0 n 0))
          (gluePair_eq_closed n V hcl).symm)
        (relabelDataUp (stepIso n)
          (glueDataClosed hcl (stepBit n V D) 𝒟)) := by
    unfold stepDataUp
    rw [dite_eq_left hcl, relabelDataUp_dataOfEq]
    rfl
  revert hct hEt hnet
  rw [show stepData n V D = _ from dite_eq_left hcl, hup]
  intro hct hEt hnet
  exact match_dataOfEq_stageDataOfEq
    (congrArg (fun X => X.relabel (interfaceStepEquiv 0 n 0))
      (gluePair_eq_closed n V hcl))
    (stepDataClosed n V D hcl)
    (relabelDataUp (stepIso n)
      (glueDataClosed hcl (stepBit n V D) 𝒟))
    (fun hc hE hne => match_relabelDataUp_stepDataClosed n V hcl 𝒟 D
      hcompat hc hE hne) hct hEt hnet

/-- The transport of a flag, undone. -/
theorem flagOfEq_symm {L : Type} {V₁ V₂ : Fragment L} (h : V₁ = V₂)
    (f : V₁.Flag) : flagOfEq h.symm (flagOfEq h f) = f := by
  subst h
  rfl

/-- The transport commutes with the pairing. -/
theorem flagOfEq_pairing {L : Type} {V₁ V₂ : Fragment L}
    (h : V₁ = V₂) (f : V₁.Flag) :
    flagOfEq h (V₁.pairing f) = V₂.pairing (flagOfEq h f) := by
  subst h
  rfl

/-- A transported family's directions, evaluated. -/
theorem isOut_dataOfEq_apply {L : Type} [LinearOrder L]
    {V₁ V₂ : Fragment L} (h : V₁ = V₂) (𝒟 : DataFamily V₂)
    (s : Finset V₁.Flag) (hc : ∀ f ∈ s, V₁.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData)
    (hc' : ∀ f ∈ flagsOfEq V₁ V₂ h s,
      V₂.pairing f ∈ flagsOfEq V₁ V₂ h s)
    (hE' : (EdgeSubset.mk (flagsOfEq V₁ V₂ h s) hc').Eulerian)
    (hne' : Nonempty
      (EdgeSubset.mk (flagsOfEq V₁ V₂ h s) hc').CanonData)
    (f : V₁.Flag) :
    (dataOfEq h 𝒟 s hc hE hne).2.isOut f
      = (𝒟 (flagsOfEq V₁ V₂ h s) hc' hE' hne').2.isOut
        (flagOfEq h f) := by
  subst h
  rfl

open Classical in
/-- **A stage of the lift keeps the base's directions.**  At a
surviving flag the glued family reads the direction the base family
gave it, so the alignment at deeper cuts is the base's own. -/
theorem isOut_stepDataUp_open (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (b : Bool) (𝒟 : DataFamily V)
    (u : Finset (SurvivingFlag V (cutL n) (cutR n)))
    (t : Finset (stepFragment n V).Flag)
    (ht : t = flagsOfEq
      (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
      (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
      (gluePair_eq_open n V hop) u)
    (hct : ∀ f ∈ t, (stepFragment n V).pairing f ∈ t)
    (hEt : (EdgeSubset.mk t hct).Eulerian)
    (hnet : Nonempty (EdgeSubset.mk t hct).CanonData)
    (hcL : ∀ f ∈ liftSubsetOpen hop u,
      V.pairing f ∈ liftSubsetOpen hop u)
    (hEL : (EdgeSubset.mk (liftSubsetOpen hop u)
      hcL : EdgeSubset V).Eulerian)
    (hneL : Nonempty (EdgeSubset.mk
      (liftSubsetOpen hop u) hcL :
      EdgeSubset V).CanonData)
    (hag : (𝒟 (liftSubsetOpen hop u) hcL hEL
          hneL).2.isOut (V.pairing (V.boundaryFlag (cutR n)))
      = !(𝒟 (liftSubsetOpen hop u) hcL hEL
          hneL).2.isOut (V.pairing (V.boundaryFlag (cutL n))))
    (f' : SurvivingFlag V (cutL n) (cutR n))
    (g : (stepFragment n V).Flag)
    (hg : g = flagOfEq (gluePair_eq_open n V hop) f') :
    (stepDataUp n V b 𝒟 t hct hEt hnet).2.isOut g
      = (𝒟 (liftSubsetOpen hop u) hcL hEL
          hneL).2.isOut f'.val := by
  subst ht
  subst hg
  have hup : stepDataUp n V b 𝒟
      = relabelDataUp (stepIso n)
        (dataOfEq (gluePair_eq_open n V hop).symm
          (glueDataOpen (cutL_ne_cutR n) hop 𝒟)) := by
    unfold stepDataUp
    rw [dite_eq_right hop]
  have hEg : (EdgeSubset.mk (flagsOfEq _ _
      (gluePair_eq_open n V hop) u) hct :
      EdgeSubset (V.gluePair (cutL n) (cutR n)
        (cutL_ne_cutR n))).Eulerian :=
    (relabelUp_eulerian (stepIso n).toEquiv
      (EdgeSubset.mk _ hct)).mp hEt
  have hneg : Nonempty (EdgeSubset.mk (flagsOfEq _ _
      (gluePair_eq_open n V hop) u) hct :
      EdgeSubset (V.gluePair (cutL n) (cutR n)
        (cutL_ne_cutR n))).CanonData :=
    (nonempty_canonData_relabelUp (stepIso n)
      (EdgeSubset.mk _ hct)).mp hnet
  have hc' := flagsOfEq_pairing_mem (gluePair_eq_open n V hop).symm
    _ hct
  have hE' := flagsOfEq_eulerian (gluePair_eq_open n V hop).symm
    _ hct hEg
  have hne' := flagsOfEq_canon (gluePair_eq_open n V hop).symm
    _ hct hneg
  have hsub : (EdgeSubset.mk (flagsOfEq _ _
        (gluePair_eq_open n V hop).symm (flagsOfEq _ _
          (gluePair_eq_open n V hop) u)) hc' :
      EdgeSubset (V.gluePairOpen (cutL n) (cutR n)
        (cutL_ne_cutR n) hop))
      = EdgeSubset.mk u (flagsOfEq_symm (gluePair_eq_open n V hop) u
        ▸ hc') :=
    EdgeSubset.ext (flagsOfEq_symm (gluePair_eq_open n V hop) u)
  rw [hup]
  refine Eq.trans (isOut_dataOfEq_apply
    (gluePair_eq_open n V hop).symm
    (glueDataOpen (cutL_ne_cutR n) hop 𝒟) _ hct hEg hneg hc' hE'
    hne' _) ?_
  rw [flagOfEq_symm (gluePair_eq_open n V hop) f']
  refine Eq.trans (isOut_dataFamily_congr
    (glueDataOpen (cutL_ne_cutR n) hop 𝒟)
    (flagsOfEq_symm (gluePair_eq_open n V hop) u) hc' hE' hne'
    (flagsOfEq_symm (gluePair_eq_open n V hop) u ▸ hc')
    (hsub ▸ hE') (hsub ▸ hne') f') ?_
  exact isOut_glueDataOpen_pos (cutL_ne_cutR n) hop 𝒟 u _ _ _ hcL
    hEL hneL hag f'

open Classical in
/-- **The stage's directions at a closing cut** are the base
family's, read at the lift with the stage's bit.  Nothing is
rewired, so no alternation is asked for. -/
theorem isOut_stepDataUp_closed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (b : Bool) (𝒟 : DataFamily V)
    (u : Finset (SurvivingFlag V (cutL n) (cutR n)))
    (t : Finset (stepFragment n V).Flag)
    (ht : t = flagsOfEq
      (V.gluePairClosed (cutL n) (cutR n) hcl)
      (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
      (gluePair_eq_closed n V hcl) u)
    (hct : ∀ f ∈ t, (stepFragment n V).pairing f ∈ t)
    (hEt : (EdgeSubset.mk t hct).Eulerian)
    (hnet : Nonempty (EdgeSubset.mk t hct).CanonData)
    (hcL : ∀ f ∈ liftSubsetClosed u b,
      V.pairing f ∈ liftSubsetClosed u b)
    (hEL : (EdgeSubset.mk (liftSubsetClosed u b)
      hcL : EdgeSubset V).Eulerian)
    (hneL : Nonempty (EdgeSubset.mk (liftSubsetClosed u b) hcL :
      EdgeSubset V).CanonData)
    (f' : SurvivingFlag V (cutL n) (cutR n))
    (g : (stepFragment n V).Flag)
    (hg : g = flagOfEq (gluePair_eq_closed n V hcl) f') :
    (stepDataUp n V b 𝒟 t hct hEt hnet).2.isOut g
      = (𝒟 (liftSubsetClosed u b) hcL hEL hneL).2.isOut f'.val := by
  subst ht
  subst hg
  have hup : stepDataUp n V b 𝒟
      = relabelDataUp (stepIso n)
        (dataOfEq (gluePair_eq_closed n V hcl).symm
          (glueDataClosed hcl b 𝒟)) := by
    unfold stepDataUp
    rw [dite_eq_left hcl]
  have hEg : (EdgeSubset.mk (flagsOfEq _ _
      (gluePair_eq_closed n V hcl) u) hct :
      EdgeSubset (V.gluePair (cutL n) (cutR n)
        (cutL_ne_cutR n))).Eulerian :=
    (relabelUp_eulerian (stepIso n).toEquiv
      (EdgeSubset.mk _ hct)).mp hEt
  have hneg : Nonempty (EdgeSubset.mk (flagsOfEq _ _
      (gluePair_eq_closed n V hcl) u) hct :
      EdgeSubset (V.gluePair (cutL n) (cutR n)
        (cutL_ne_cutR n))).CanonData :=
    (nonempty_canonData_relabelUp (stepIso n)
      (EdgeSubset.mk _ hct)).mp hnet
  have hc' := flagsOfEq_pairing_mem (gluePair_eq_closed n V hcl).symm
    _ hct
  have hE' := flagsOfEq_eulerian (gluePair_eq_closed n V hcl).symm
    _ hct hEg
  have hne' := flagsOfEq_canon (gluePair_eq_closed n V hcl).symm
    _ hct hneg
  have hsub : (EdgeSubset.mk (flagsOfEq _ _
        (gluePair_eq_closed n V hcl).symm (flagsOfEq _ _
          (gluePair_eq_closed n V hcl) u)) hc' :
      EdgeSubset (V.gluePairClosed (cutL n) (cutR n) hcl))
      = EdgeSubset.mk u (flagsOfEq_symm (gluePair_eq_closed n V hcl)
        u ▸ hc') :=
    EdgeSubset.ext (flagsOfEq_symm (gluePair_eq_closed n V hcl) u)
  rw [hup]
  refine Eq.trans (isOut_dataOfEq_apply
    (gluePair_eq_closed n V hcl).symm
    (glueDataClosed hcl b 𝒟) _ hct hEg hneg hc' hE'
    hne' _) ?_
  rw [flagOfEq_symm (gluePair_eq_closed n V hcl) f']
  refine Eq.trans (isOut_dataFamily_congr
    (glueDataClosed hcl b 𝒟)
    (flagsOfEq_symm (gluePair_eq_closed n V hcl) u) hc' hE' hne'
    (flagsOfEq_symm (gluePair_eq_closed n V hcl) u ▸ hc')
    (hsub ▸ hE') (hsub ▸ hne') f') ?_
  exact isOut_glueDataClosed_pos hcl b 𝒟 u _ _ _ hcL
    hEL hneL f'

/-- **The stage's boundary flag is the base's**, carried across the
transport the dispatch on the cut demands. -/
theorem boundaryFlag_stepFragment_open (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n)) (bl : Fin (0 + n) ⊕ Fin (n + 0)) :
    (stepFragment n V).boundaryFlag bl
      = flagOfEq (gluePair_eq_open n V hop)
        ((V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n)
          hop).boundaryFlag ((interfaceStepEquiv 0 n 0).symm bl)) :=
  (stepFragment_boundaryFlag n V bl).trans
    (flagOfEq_boundaryFlag (gluePair_eq_open n V hop) _).symm

/-- **The glue does not move the chain directions.**  With the
pairing flipping at every boundary flag and the cut's own two ends
oppositely directed, the rewired partner of a surviving label carries
the direction the base's partner carried: crossing the cut costs two
flips, and two flips are none. -/
theorem isOut_rewire_eq {α : Type} {W : Fragment α}
    {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    (o : κ.Orientation) {i j : α}
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hflip : ∀ ℓ : α, o.isOut (W.pairing (W.boundaryFlag ℓ))
      = !o.isOut (W.boundaryFlag ℓ))
    (halign : o.isOut (W.pairing (W.boundaryFlag j))
      = !o.isOut (W.pairing (W.boundaryFlag i)))
    (ℓ : α) (h1 : W.boundaryFlag ℓ ≠ W.boundaryFlag i)
    (h2 : W.boundaryFlag ℓ ≠ W.boundaryFlag j) :
    o.isOut (Fragment.rewire hopen ⟨W.boundaryFlag ℓ, h1, h2⟩).val
      = o.isOut (W.pairing (W.boundaryFlag ℓ)) := by
  by_cases hi : W.pairing (W.boundaryFlag ℓ) = W.boundaryFlag i
  · rw [Fragment.rewire_eq_partnerSurvJ hopen _ hi]
    change o.isOut (W.pairing (W.boundaryFlag j)) = _
    rw [halign, hi, hflip i, Bool.not_not]
  · by_cases hj : W.pairing (W.boundaryFlag ℓ) = W.boundaryFlag j
    · have h3 : o.isOut (W.pairing (W.boundaryFlag i))
          = o.isOut (W.boundaryFlag j) := by
        rw [← Bool.not_not (o.isOut (W.pairing (W.boundaryFlag i))),
          ← halign, hflip j, Bool.not_not]
      rw [Fragment.rewire_eq_partnerSurvI hopen _ hi hj]
      change o.isOut (W.pairing (W.boundaryFlag i)) = _
      rw [hj, h3]
    · rw [Fragment.rewire_val_of_ne hopen _ hi hj]

/-- **The stage's boundary partner is the rewired one.**  The glue
sends a surviving boundary flag to its rewired partner, which is the
base's partner except across the cut's own edge. -/
theorem pairing_boundaryFlag_stepFragment (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n)) (bl : Fin (0 + n) ⊕ Fin (n + 0)) :
    (stepFragment n V).pairing ((stepFragment n V).boundaryFlag bl)
      = flagOfEq (gluePair_eq_open n V hop)
        (Fragment.rewire hop
          ⟨V.boundaryFlag ((interfaceStepEquiv 0 n 0).symm bl).val,
            fun hx => ((interfaceStepEquiv 0 n 0).symm bl).prop.1
              (V.boundaryFlag_injective hx),
            fun hx => ((interfaceStepEquiv 0 n 0).symm bl).prop.2
              (V.boundaryFlag_injective hx)⟩) := by
  rw [boundaryFlag_stepFragment_open n V hop bl]
  exact (flagOfEq_pairing (gluePair_eq_open n V hop) _).symm

open Classical in
/-- **A stage of the lift keeps the base's chain directions.**  The
stage's boundary partner is the rewired one, the glue does not move
the directions, and the lifted family reads the base's own — so the
alternation the next cut needs is the base's at the same label. -/
theorem chainDir_stepDataUp_eq (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (b : Bool) (𝒟 : DataFamily V)
    (u : Finset (SurvivingFlag V (cutL n) (cutR n)))
    (t : Finset (stepFragment n V).Flag)
    (ht : t = flagsOfEq
      (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
      (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
      (gluePair_eq_open n V hop) u)
    (hct : ∀ f ∈ t, (stepFragment n V).pairing f ∈ t)
    (hEt : (EdgeSubset.mk t hct).Eulerian)
    (hnet : Nonempty (EdgeSubset.mk t hct).CanonData)
    (hcL : ∀ f ∈ liftSubsetOpen hop u,
      V.pairing f ∈ liftSubsetOpen hop u)
    (hEL : (EdgeSubset.mk (liftSubsetOpen hop u)
      hcL : EdgeSubset V).Eulerian)
    (hneL : Nonempty (EdgeSubset.mk
      (liftSubsetOpen hop u) hcL :
      EdgeSubset V).CanonData)
    (hag : (𝒟 (liftSubsetOpen hop u) hcL hEL
          hneL).2.isOut (V.pairing (V.boundaryFlag (cutR n)))
      = !(𝒟 (liftSubsetOpen hop u) hcL hEL
          hneL).2.isOut (V.pairing (V.boundaryFlag (cutL n))))
    (hflip : ∀ ℓ, (𝒟 (liftSubsetOpen hop u) hcL
          hEL hneL).2.isOut (V.pairing (V.boundaryFlag ℓ))
      = !(𝒟 (liftSubsetOpen hop u) hcL hEL
          hneL).2.isOut (V.boundaryFlag ℓ))
    (bl : Fin (0 + n) ⊕ Fin (n + 0)) :
    (stepDataUp n V b 𝒟 t hct hEt hnet).2.isOut
        ((stepFragment n V).pairing
          ((stepFragment n V).boundaryFlag bl))
      = (𝒟 (liftSubsetOpen hop u) hcL hEL
          hneL).2.isOut (V.pairing (V.boundaryFlag
            ((interfaceStepEquiv 0 n 0).symm bl).val)) := by
  rw [pairing_boundaryFlag_stepFragment n V hop bl,
    isOut_stepDataUp_open n V hop b 𝒟 u t ht hct hEt hnet hcL hEL
      hneL hag _ _ rfl]
  exact isOut_rewire_eq _ hop hflip hag
    ((interfaceStepEquiv 0 n 0).symm bl).val
    (fun hx => ((interfaceStepEquiv 0 n 0).symm bl).prop.1
      (V.boundaryFlag_injective hx))
    (fun hx => ((interfaceStepEquiv 0 n 0).symm bl).prop.2
      (V.boundaryFlag_injective hx))

/-- The stage's `m`-th left label is the base's. -/
theorem interfaceStepEquiv_symm_intL (n : ℕ) (m : Fin n) :
    ((interfaceStepEquiv 0 n 0).symm (intL n m)).val
      = intL (n + 1) m.castSucc := by
  have h : intL n m = Sum.inl ⟨0 + m.val, by omega⟩ :=
    congrArg Sum.inl (Fin.ext (by simp))
  rw [h, interfaceStepEquiv_symm_inl 0 n 0 m.val m.isLt]
  exact congrArg Sum.inl (Fin.ext (by simp))

/-- The stage's `m`-th right label is the base's. -/
theorem interfaceStepEquiv_symm_intR (n : ℕ) (m : Fin n) :
    ((interfaceStepEquiv 0 n 0).symm (intR n m)).val
      = intR (n + 1) m.castSucc := by
  have h : intR n m = Sum.inr ⟨m.val, by omega⟩ :=
    congrArg Sum.inr (Fin.ext (by simp))
  rw [h, interfaceStepEquiv_symm_inr 0 n 0 m.val m.isLt]
  exact congrArg Sum.inr (Fin.ext (by simp))

open Classical in
/-- **A stage of the lift keeps the base's boundary directions.** -/
theorem isOut_stepDataUp_boundaryFlag (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (b : Bool) (𝒟 : DataFamily V)
    (u : Finset (SurvivingFlag V (cutL n) (cutR n)))
    (t : Finset (stepFragment n V).Flag)
    (ht : t = flagsOfEq
      (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
      (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
      (gluePair_eq_open n V hop) u)
    (hct : ∀ f ∈ t, (stepFragment n V).pairing f ∈ t)
    (hEt : (EdgeSubset.mk t hct).Eulerian)
    (hnet : Nonempty (EdgeSubset.mk t hct).CanonData)
    (hcL : ∀ f ∈ liftSubsetOpen hop u,
      V.pairing f ∈ liftSubsetOpen hop u)
    (hEL : (EdgeSubset.mk (liftSubsetOpen hop u)
      hcL : EdgeSubset V).Eulerian)
    (hneL : Nonempty (EdgeSubset.mk
      (liftSubsetOpen hop u) hcL :
      EdgeSubset V).CanonData)
    (hag : (𝒟 (liftSubsetOpen hop u) hcL hEL
          hneL).2.isOut (V.pairing (V.boundaryFlag (cutR n)))
      = !(𝒟 (liftSubsetOpen hop u) hcL hEL
          hneL).2.isOut (V.pairing (V.boundaryFlag (cutL n))))
    (bl : Fin (0 + n) ⊕ Fin (n + 0)) :
    (stepDataUp n V b 𝒟 t hct hEt hnet).2.isOut
        ((stepFragment n V).boundaryFlag bl)
      = (𝒟 (liftSubsetOpen hop u) hcL hEL
          hneL).2.isOut (V.boundaryFlag
            ((interfaceStepEquiv 0 n 0).symm bl).val) := by
  rw [boundaryFlag_stepFragment_open n V hop bl]
  exact isOut_stepDataUp_open n V hop b 𝒟 u t ht hct hEt hnet hcL
    hEL hneL hag
    ((V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n)
      hop).boundaryFlag ((interfaceStepEquiv 0 n 0).symm bl)) _ rfl

/-- **The cut alternation, read at the cut's own flags.**  Once the
pairing flips at every boundary flag, the two ends of a cut are
oppositely directed exactly when the cut's two boundary flags
are — one flip on each side. -/
theorem isOut_cut_iff_boundary {n : ℕ}
    {V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))} {B : EdgeSubset V}
    {κ : B.RelTransitionSystem} (o : κ.Orientation)
    (hflip : ∀ ℓ, o.isOut (V.pairing (V.boundaryFlag ℓ))
      = !o.isOut (V.boundaryFlag ℓ)) (m : Fin n) :
    (o.isOut (V.pairing (V.boundaryFlag (intR n m)))
        = !o.isOut (V.pairing (V.boundaryFlag (intL n m))))
      ↔ (o.isOut (V.boundaryFlag (intR n m))
        = !o.isOut (V.boundaryFlag (intL n m))) := by
  rw [hflip, hflip]
  constructor
  · intro h
    exact Bool.not_inj (by rw [h, Bool.not_not])
  · intro h
    rw [h, Bool.not_not]

open Classical in
/-- **A subset is cut-balanced** when it uses the two labels of each
interface pair together. -/
def CutBalanced {n : ℕ} (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0)))
    (u : Finset V.Flag) : Prop :=
  ∀ m : Fin n, V.boundaryFlag (intL n m) ∈ u
    ↔ V.boundaryFlag (intR n m) ∈ u

/-- **A subset matching a diagonal state is cut-balanced.**  The
diagonal gives a pair's two labels the same colour, so the subset
uses both or neither. -/
theorem cutBalanced_of_matches_diag {k ℓ : ℕ} {n : ℕ}
    {V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))} {u : Finset V.Flag}
    (x : Fin n → (Fin k ⊕ Fin (2 * ℓ)))
    (hbnd : genBoundarySubsetMatches V u (diagOf n x)) :
    CutBalanced V u := by
  intro m
  rw [hbnd (intL n m), hbnd (intR n m)]
  exact Iff.rfl

/-- **The base's directions, as the lift consumes them.**  The
pairing flips at every boundary flag, and the two ends of every
interface pair are oppositely directed. -/
def BaseDirections {n : ℕ}
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))) (𝒟 : DataFamily V) :
    Prop :=
  ∀ (u : Finset V.Flag) (hc : ∀ f ∈ u, V.pairing f ∈ u)
    (hE : (EdgeSubset.mk u hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk u hc).CanonData),
    CutBalanced V u →
    (∀ ℓ, (𝒟 u hc hE hne).2.isOut (V.pairing (V.boundaryFlag ℓ))
      = !(𝒟 u hc hE hne).2.isOut (V.boundaryFlag ℓ))
    ∧ ∀ m : Fin n,
      (𝒟 u hc hE hne).2.isOut
          (V.pairing (V.boundaryFlag (intR n m)))
        = !(𝒟 u hc hE hne).2.isOut
          (V.pairing (V.boundaryFlag (intL n m)))

/-- **Every fragment's edges can be two-coloured.**  The pairing is a
fixed-point-free involution, so comparing a flag's index with its
partner's orients every edge. -/
theorem exists_edge_colouring {α : Type} (V : Fragment α) :
    ∃ c : V.Flag → Bool, ∀ f, c (V.pairing f) = !c f := by
  classical
  refine ⟨fun f => decide (((Fintype.equivFin V.Flag) f : ℕ)
    < ((Fintype.equivFin V.Flag) (V.pairing f) : ℕ)), fun f => ?_⟩
  have hne : ((Fintype.equivFin V.Flag) (V.pairing f) : ℕ)
      ≠ ((Fintype.equivFin V.Flag) f : ℕ) := by
    intro hx
    exact V.pairing_ne f
      ((Fintype.equivFin V.Flag).injective (Fin.ext hx))
  simp only [V.pairing_invol]
  by_cases hlt : ((Fintype.equivFin V.Flag) f : ℕ)
      < ((Fintype.equivFin V.Flag) (V.pairing f) : ℕ)
  · simp only [decide_eq_true hlt, Bool.not_true,
      decide_eq_false_iff_not]
    omega
  · simp only [decide_eq_false hlt, Bool.not_false,
      decide_eq_true_eq]
    omega

/-! ## The stage at a closing cut

A closing cut rewires nothing: its two flags bound one edge, which
the glue turns into a free circle, and every other flag keeps the
partner it had.  So a flag survives the cut exactly when its partner
does, and the stage's pairing is the base's.
-/

/-- **A survivor's partner survives**, at the cut's left flag.  The
two cut flags are each other's partners, so nothing else can pair to
either. -/
theorem pairing_ne_cutL_of_closed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n)) (f : V.Flag)
    (h2 : f ≠ V.boundaryFlag (cutR n)) :
    V.pairing f ≠ V.boundaryFlag (cutL n) := by
  intro hx
  refine h2 ?_
  rw [← hcl, ← hx, V.pairing_invol]

/-- **A survivor's partner survives**, at the cut's right flag. -/
theorem pairing_ne_cutR_of_closed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n)) (f : V.Flag)
    (h1 : f ≠ V.boundaryFlag (cutL n)) :
    V.pairing f ≠ V.boundaryFlag (cutR n) := by
  intro hx
  refine h1 ?_
  rw [← V.pairing_invol f, hx, ← hcl, V.pairing_invol]

/-- A surviving flag, read at the stage fragment, at a closing
cut. -/
noncomputable def stageFlagClosed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n)) (f : V.Flag)
    (h1 : f ≠ V.boundaryFlag (cutL n))
    (h2 : f ≠ V.boundaryFlag (cutR n)) :
    (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n)).Flag :=
  flagOfEq (gluePair_eq_closed n V hcl)
    (⟨f, h1, h2⟩ : SurvivingFlag V (cutL n) (cutR n))

/-- **At a closing cut the stage's partner is the base's.** -/
theorem pairing_stageFlagClosed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n)) (f : V.Flag)
    (h1 : f ≠ V.boundaryFlag (cutL n))
    (h2 : f ≠ V.boundaryFlag (cutR n))
    (k1 : V.pairing f ≠ V.boundaryFlag (cutL n))
    (k2 : V.pairing f ≠ V.boundaryFlag (cutR n)) :
    (stepFragment n V).pairing (stageFlagClosed n V hcl f h1 h2)
      = stageFlagClosed n V hcl (V.pairing f) k1 k2 :=
  (flagOfEq_pairing (gluePair_eq_closed n V hcl) _).symm

/-- **The stage's boundary flag is the base's**, at a closing cut. -/
theorem boundaryFlag_stepFragment_closed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (bl : Fin (0 + n) ⊕ Fin (n + 0)) :
    (stepFragment n V).boundaryFlag bl
      = flagOfEq (gluePair_eq_closed n V hcl)
        ((V.gluePairClosed (cutL n) (cutR n) hcl).boundaryFlag
          ((interfaceStepEquiv 0 n 0).symm bl)) :=
  (stepFragment_boundaryFlag n V bl).trans
    (flagOfEq_boundaryFlag (gluePair_eq_closed n V hcl) _).symm

/-- **A surviving boundary flag is the stage's own**, at a closing
cut. -/
theorem stageFlagClosed_boundaryFlag (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n)) (bl : Fin (0 + n) ⊕ Fin (n + 0))
    (h1 : V.boundaryFlag ((interfaceStepEquiv 0 n 0).symm bl).val
      ≠ V.boundaryFlag (cutL n))
    (h2 : V.boundaryFlag ((interfaceStepEquiv 0 n 0).symm bl).val
      ≠ V.boundaryFlag (cutR n)) :
    stageFlagClosed n V hcl
        (V.boundaryFlag ((interfaceStepEquiv 0 n 0).symm bl).val)
        h1 h2
      = (stepFragment n V).boundaryFlag bl :=
  (boundaryFlag_stepFragment_closed n V hcl bl).symm

/-- A surviving flag, read at the stage fragment. -/
noncomputable def stageFlag (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n)) (f : V.Flag)
    (h1 : f ≠ V.boundaryFlag (cutL n))
    (h2 : f ≠ V.boundaryFlag (cutR n)) :
    (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n)).Flag :=
  flagOfEq (gluePair_eq_open n V hop)
    (⟨f, h1, h2⟩ : SurvivingFlag V (cutL n) (cutR n))

/-- The stage's partner of a surviving flag is its rewired one. -/
theorem pairing_stageFlag (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n)) (f : V.Flag)
    (h1 : f ≠ V.boundaryFlag (cutL n))
    (h2 : f ≠ V.boundaryFlag (cutR n)) :
    (stepFragment n V).pairing (stageFlag n V hop f h1 h2)
      = flagOfEq (gluePair_eq_open n V hop)
        (Fragment.rewire hop ⟨f, h1, h2⟩) :=
  (flagOfEq_pairing (gluePair_eq_open n V hop) _).symm

/-- Away from the cut, the stage's partner is the base's. -/
theorem pairing_stageFlag_of_ne (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n)) (f : V.Flag)
    (h1 : f ≠ V.boundaryFlag (cutL n))
    (h2 : f ≠ V.boundaryFlag (cutR n))
    (k1 : V.pairing f ≠ V.boundaryFlag (cutL n))
    (k2 : V.pairing f ≠ V.boundaryFlag (cutR n)) :
    (stepFragment n V).pairing (stageFlag n V hop f h1 h2)
      = stageFlag n V hop (V.pairing f) k1 k2 := by
  rw [pairing_stageFlag n V hop f h1 h2]
  exact congrArg (flagOfEq (gluePair_eq_open n V hop))
    (Subtype.ext (Fragment.rewire_val_of_ne hop _ k1 k2))

/-- At the cut's right edge the stage's partner is the far end of the
left edge. -/
theorem pairing_stageFlag_cutR (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (k1 : V.pairing (V.boundaryFlag (cutR n))
      ≠ V.boundaryFlag (cutL n))
    (k2 : V.pairing (V.boundaryFlag (cutR n))
      ≠ V.boundaryFlag (cutR n))
    (h1 : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutL n))
    (h2 : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n)) :
    (stepFragment n V).pairing (stageFlag n V hop
        (V.pairing (V.boundaryFlag (cutR n))) k1 k2)
      = stageFlag n V hop (V.pairing (V.boundaryFlag (cutL n)))
        h1 h2 := by
  have hne : V.pairing (V.pairing (V.boundaryFlag (cutR n)))
      ≠ V.boundaryFlag (cutL n) := by
    rw [V.pairing_invol]
    exact fun hx =>
      cutL_ne_cutR n (V.boundaryFlag_injective hx).symm
  rw [pairing_stageFlag n V hop _ k1 k2,
    Fragment.rewire_eq_partnerSurvI hop _ hne (V.pairing_invol _)]
  rfl

/-- The stage's boundary flag is the base's, read as a stage
flag. -/
theorem stageFlag_boundaryFlag (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n)) (bl : Fin (0 + n) ⊕ Fin (n + 0))
    (h1 : V.boundaryFlag ((interfaceStepEquiv 0 n 0).symm bl).val
      ≠ V.boundaryFlag (cutL n))
    (h2 : V.boundaryFlag ((interfaceStepEquiv 0 n 0).symm bl).val
      ≠ V.boundaryFlag (cutR n)) :
    stageFlag n V hop
        (V.boundaryFlag ((interfaceStepEquiv 0 n 0).symm bl).val)
        h1 h2
      = (stepFragment n V).boundaryFlag bl :=
  (boundaryFlag_stepFragment_open n V hop bl).symm

/-- A lower interface pair's left label is not the top cut's. -/
theorem intL_ne_cutL (n : ℕ) (b : Fin n) :
    intL (n + 1) b.castSucc ≠ cutL n := by
  intro hx
  have h := congrArg Fin.val (Sum.inl.inj hx)
  simp only [Fin.val_cast, Fin.val_castSucc] at h
  omega

/-- A lower interface pair's right label is not the top cut's. -/
theorem intR_ne_cutR (n : ℕ) (b : Fin n) :
    intR (n + 1) b.castSucc ≠ cutR n := by
  intro hx
  have h := congrArg Fin.val (Sum.inr.inj hx)
  simp only [Fin.val_cast, Fin.val_castSucc] at h
  omega

/-- A left label is never a right one. -/
theorem intL_ne_cutR (n : ℕ) (b : Fin n) :
    intL (n + 1) b.castSucc ≠ cutR n := Sum.inl_ne_inr

/-- A right label is never a left one. -/
theorem intR_ne_cutL (n : ℕ) (b : Fin n) :
    intR (n + 1) b.castSucc ≠ cutL n := Sum.inr_ne_inl

open Classical in
/-- **Extending a colouring across a cut.**  The two cut flags take
the opposite colour to their partners, which survive the glue. -/
noncomputable def cutExtend (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (hL1 : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutL n))
    (hR1 : V.pairing (V.boundaryFlag (cutR n))
      ≠ V.boundaryFlag (cutL n))
    (hR2 : V.pairing (V.boundaryFlag (cutR n))
      ≠ V.boundaryFlag (cutR n))
    (c' : (stepFragment n V).Flag → Bool) : V.Flag → Bool :=
  fun f =>
    if h1 : f = V.boundaryFlag (cutL n) then
      !c' (stageFlag n V hop
        (V.pairing (V.boundaryFlag (cutL n))) hL1 hop)
    else if h2 : f = V.boundaryFlag (cutR n) then
      !c' (stageFlag n V hop
        (V.pairing (V.boundaryFlag (cutR n))) hR1 hR2)
    else c' (stageFlag n V hop f h1 h2)

open Classical in
/-- Away from the cut the extension is the stage's colouring. -/
theorem cutExtend_of_ne (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (hL1 : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutL n))
    (hR1 : V.pairing (V.boundaryFlag (cutR n))
      ≠ V.boundaryFlag (cutL n))
    (hR2 : V.pairing (V.boundaryFlag (cutR n))
      ≠ V.boundaryFlag (cutR n))
    (c' : (stepFragment n V).Flag → Bool) (f : V.Flag)
    (h1 : f ≠ V.boundaryFlag (cutL n))
    (h2 : f ≠ V.boundaryFlag (cutR n)) :
    cutExtend n V hop hL1 hR1 hR2 c' f
      = c' (stageFlag n V hop f h1 h2) := by
  unfold cutExtend
  rw [dite_eq_right h1, dite_eq_right h2]

open Classical in
/-- At the cut's left flag the extension is the opposite of its
partner's colour. -/
theorem cutExtend_cutL (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (hL1 : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutL n))
    (hR1 : V.pairing (V.boundaryFlag (cutR n))
      ≠ V.boundaryFlag (cutL n))
    (hR2 : V.pairing (V.boundaryFlag (cutR n))
      ≠ V.boundaryFlag (cutR n))
    (c' : (stepFragment n V).Flag → Bool) :
    cutExtend n V hop hL1 hR1 hR2 c' (V.boundaryFlag (cutL n))
      = !c' (stageFlag n V hop
        (V.pairing (V.boundaryFlag (cutL n))) hL1 hop) := by
  unfold cutExtend
  rw [dite_eq_left rfl]

open Classical in
/-- At the cut's right flag the extension is the opposite of its
partner's colour. -/
theorem cutExtend_cutR (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (hL1 : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutL n))
    (hR1 : V.pairing (V.boundaryFlag (cutR n))
      ≠ V.boundaryFlag (cutL n))
    (hR2 : V.pairing (V.boundaryFlag (cutR n))
      ≠ V.boundaryFlag (cutR n))
    (c' : (stepFragment n V).Flag → Bool) :
    cutExtend n V hop hL1 hR1 hR2 c' (V.boundaryFlag (cutR n))
      = !c' (stageFlag n V hop
        (V.pairing (V.boundaryFlag (cutR n))) hR1 hR2) := by
  unfold cutExtend
  rw [dite_eq_right (fun hx => cutL_ne_cutR n
      (V.boundaryFlag_injective hx).symm), dite_eq_left rfl]

/-- Stage flags at equal base flags agree. -/
theorem stageFlagClosed_congr (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n)) {f g : V.Flag} (hfg : f = g)
    (h1 : f ≠ V.boundaryFlag (cutL n))
    (h2 : f ≠ V.boundaryFlag (cutR n))
    (k1 : g ≠ V.boundaryFlag (cutL n))
    (k2 : g ≠ V.boundaryFlag (cutR n)) :
    stageFlagClosed n V hcl f h1 h2
      = stageFlagClosed n V hcl g k1 k2 := by
  subst hfg
  rfl

open Classical in
/-- **Extending a colouring across a closing cut.**  The cut's two
flags are each other's partners, and the glue takes both away, so
their colours are free: give the left one `true` and the right one
`false` and both the edge and the interface pair alternate at
once. -/
noncomputable def cutExtendClosed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (c' : (stepFragment n V).Flag → Bool) : V.Flag → Bool :=
  fun f =>
    if _h1 : f = V.boundaryFlag (cutL n) then true
    else if _h2 : f = V.boundaryFlag (cutR n) then false
    else c' (stageFlagClosed n V hcl f _h1 _h2)

open Classical in
/-- Away from the cut the extension is the stage's colouring. -/
theorem cutExtendClosed_of_ne (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (c' : (stepFragment n V).Flag → Bool) (f : V.Flag)
    (h1 : f ≠ V.boundaryFlag (cutL n))
    (h2 : f ≠ V.boundaryFlag (cutR n)) :
    cutExtendClosed n V hcl c' f
      = c' (stageFlagClosed n V hcl f h1 h2) := by
  unfold cutExtendClosed
  rw [dite_eq_right h1, dite_eq_right h2]

open Classical in
/-- At the cut's left flag the extension is `true`. -/
theorem cutExtendClosed_cutL (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (c' : (stepFragment n V).Flag → Bool) :
    cutExtendClosed n V hcl c' (V.boundaryFlag (cutL n)) = true := by
  unfold cutExtendClosed
  rw [dite_eq_left rfl]

open Classical in
/-- At the cut's right flag the extension is `false`. -/
theorem cutExtendClosed_cutR (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (c' : (stepFragment n V).Flag → Bool) :
    cutExtendClosed n V hcl c' (V.boundaryFlag (cutR n))
      = false := by
  unfold cutExtendClosed
  rw [dite_eq_right (fun hx => cutL_ne_cutR n
      (V.boundaryFlag_injective hx).symm), dite_eq_left rfl]

/-- The stage flag does not depend on which proof of survival it is
given. -/
theorem stageFlag_congr (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n)) {f g : V.Flag} (hfg : f = g)
    (h1 : f ≠ V.boundaryFlag (cutL n))
    (h2 : f ≠ V.boundaryFlag (cutR n))
    (k1 : g ≠ V.boundaryFlag (cutL n))
    (k2 : g ≠ V.boundaryFlag (cutR n)) :
    stageFlag n V hop f h1 h2 = stageFlag n V hop g k1 k2 := by
  subst hfg
  rfl

open Classical in
/-- **The stage's boundary direction at a closing cut** is the base
family's at the same label. -/
theorem isOut_stepDataUp_boundaryFlag_closed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (b : Bool) (𝒟 : DataFamily V)
    (u : Finset (SurvivingFlag V (cutL n) (cutR n)))
    (t : Finset (stepFragment n V).Flag)
    (ht : t = flagsOfEq
      (V.gluePairClosed (cutL n) (cutR n) hcl)
      (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
      (gluePair_eq_closed n V hcl) u)
    (hct : ∀ f ∈ t, (stepFragment n V).pairing f ∈ t)
    (hEt : (EdgeSubset.mk t hct).Eulerian)
    (hnet : Nonempty (EdgeSubset.mk t hct).CanonData)
    (hcL : ∀ f ∈ liftSubsetClosed u b,
      V.pairing f ∈ liftSubsetClosed u b)
    (hEL : (EdgeSubset.mk (liftSubsetClosed u b)
      hcL : EdgeSubset V).Eulerian)
    (hneL : Nonempty (EdgeSubset.mk (liftSubsetClosed u b) hcL :
      EdgeSubset V).CanonData)
    (bl : Fin (0 + n) ⊕ Fin (n + 0)) :
    (stepDataUp n V b 𝒟 t hct hEt hnet).2.isOut
        ((stepFragment n V).boundaryFlag bl)
      = (𝒟 (liftSubsetClosed u b) hcL hEL hneL).2.isOut
        (V.boundaryFlag ((interfaceStepEquiv 0 n 0).symm bl).val) :=
  isOut_stepDataUp_closed n V hcl b 𝒟 u t ht hct hEt hnet hcL hEL
    hneL _ _ (boundaryFlag_stepFragment_closed n V hcl bl)

open Classical in
/-- **The stage's boundary partner's direction at a closing cut** is
the base family's at the partner of the same label.  Nothing is
rewired, so no alternation is asked for. -/
theorem chainDir_stepDataUp_eq_closed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (b : Bool) (𝒟 : DataFamily V)
    (u : Finset (SurvivingFlag V (cutL n) (cutR n)))
    (t : Finset (stepFragment n V).Flag)
    (ht : t = flagsOfEq
      (V.gluePairClosed (cutL n) (cutR n) hcl)
      (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
      (gluePair_eq_closed n V hcl) u)
    (hct : ∀ f ∈ t, (stepFragment n V).pairing f ∈ t)
    (hEt : (EdgeSubset.mk t hct).Eulerian)
    (hnet : Nonempty (EdgeSubset.mk t hct).CanonData)
    (hcL : ∀ f ∈ liftSubsetClosed u b,
      V.pairing f ∈ liftSubsetClosed u b)
    (hEL : (EdgeSubset.mk (liftSubsetClosed u b)
      hcL : EdgeSubset V).Eulerian)
    (hneL : Nonempty (EdgeSubset.mk (liftSubsetClosed u b) hcL :
      EdgeSubset V).CanonData)
    (bl : Fin (0 + n) ⊕ Fin (n + 0)) :
    (stepDataUp n V b 𝒟 t hct hEt hnet).2.isOut
        ((stepFragment n V).pairing
          ((stepFragment n V).boundaryFlag bl))
      = (𝒟 (liftSubsetClosed u b) hcL hEL hneL).2.isOut
        (V.pairing (V.boundaryFlag
          ((interfaceStepEquiv 0 n 0).symm bl).val)) := by
  have h1 : V.boundaryFlag ((interfaceStepEquiv 0 n 0).symm bl).val
      ≠ V.boundaryFlag (cutL n) := fun hx =>
    ((interfaceStepEquiv 0 n 0).symm bl).prop.1
      (V.boundaryFlag_injective hx)
  have h2 : V.boundaryFlag ((interfaceStepEquiv 0 n 0).symm bl).val
      ≠ V.boundaryFlag (cutR n) := fun hx =>
    ((interfaceStepEquiv 0 n 0).symm bl).prop.2
      (V.boundaryFlag_injective hx)
  have k1 := pairing_ne_cutL_of_closed n V hcl _ h2
  have k2 := pairing_ne_cutR_of_closed n V hcl _ h1
  refine isOut_stepDataUp_closed n V hcl b 𝒟 u t ht hct hEt hnet
    hcL hEL hneL ⟨_, k1, k2⟩ _ ?_
  rw [← stageFlagClosed_boundaryFlag n V hcl bl h1 h2,
    pairing_stageFlagClosed n V hcl _ h1 h2 k1 k2]
  rfl

end EdgeSubset

end RS
