/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.ClosedTopSum

/-!
# The interface alternates

RS21's step 1 puts the two fragments' arc directions in Eulerian
position: at every used interface label one side's arc comes in and
the other's goes out.  For data the composition itself provides that
is automatic — the glued chain passes through the interface, so the
glued orientation makes one end incoming and the other outgoing, and
ungluing keeps both values.

The statement below is that fact at one cut: where both entry edges
are internal — that is, where the label is a chain label on both
sides — the unglued orientation's chain directions at the two glued
labels are opposite.
-/

@[expose] public section

namespace RS

namespace EdgeSubset

open Fragment
section OpenCut

variable {L : Type}

/-- The glued fragment pairs the two glued flags' partners. -/
theorem gluePairOpen_partnerSurvI {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hopen : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j) :
    (V.gluePairOpen i j hij hopen).pairing (partnerSurvI hopen)
      = partnerSurvJ hopen :=
  gluePairOpen_pairing_interface_i hij hopen (partnerSurvI hopen)
    (by rw [partnerSurvI_val hopen, V.pairing_invol])

/-- **The interface alternates.**  At a label whose entry edges are
internal on both sides, the unglued orientation's chain directions
are opposite. -/
theorem chainDir_unglueOpen_alternates
    {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hopen : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    (hct : ∀ f ∈ t, (V.gluePairOpen i j hij hopen).pairing f ∈ t)
    (hcL : ∀ f ∈ liftSubsetOpen hopen t, V.pairing f ∈ liftSubsetOpen hopen
      t)
    (κ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairOpen i j hij hopen)).RelTransitionSystem)
    (o' : κ'.Orientation)
    (hI : (partnerSurvI hopen).val
      ∈ (EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
        EdgeSubset V).internalFlags)
    (hJ : (partnerSurvJ hopen).val
      ∈ (EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
        EdgeSubset V).internalFlags) :
    chainDir (unglueOrientationOpen hij hopen t hct hcL κ' o')
        (V.boundaryFlag j)
      = !chainDir (unglueOrientationOpen hij hopen t hct hcL κ' o')
        (V.boundaryFlag i) := by
  have hIg : partnerSurvI hopen ∈ (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairOpen i j hij hopen)).internalFlags :=
    internal_mk_of_glueOpen hij hopen t hct hcL hI
      (partnerSurvI hopen).prop.1 (partnerSurvI hopen).prop.2
  have hJg : (V.gluePairOpen i j hij hopen).pairing
      (partnerSurvI hopen) ∈ (EdgeSubset.mk t hct :
        EdgeSubset (V.gluePairOpen i j hij hopen)).internalFlags := by
    rw [gluePairOpen_partnerSurvI hij hopen]
    exact internal_mk_of_glueOpen hij hopen t hct hcL hJ
      (partnerSurvJ hopen).prop.1
      (partnerSurvJ hopen).prop.2
  have hflip := o'.pairing_flip (partnerSurvI hopen) hIg hJg
  rw [gluePairOpen_partnerSurvI hij hopen] at hflip
  change unglueIsOut o'.isOut (V.pairing (V.boundaryFlag j))
    = !unglueIsOut o'.isOut (V.pairing (V.boundaryFlag i))
  rw [show V.pairing (V.boundaryFlag j)
      = (partnerSurvJ hopen).val from rfl,
    show V.pairing (V.boundaryFlag i)
      = (partnerSurvI hopen).val from rfl,
    unglueIsOut_val o'.isOut (partnerSurvJ hopen),
    unglueIsOut_val o'.isOut (partnerSurvI hopen)]
  exact hflip

/-- An internal flag is not a glued boundary flag. -/
theorem internal_ne_boundaryFlag {V : Fragment L} {i : L} {j : L}
    (hopen : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    (hcL : ∀ f ∈ liftSubsetOpen hopen t, V.pairing f ∈ liftSubsetOpen hopen
      t)
    {f : V.Flag} {b : L}
    (hint : f ∈ (EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
      EdgeSubset V).internalFlags) :
    f ≠ V.boundaryFlag b := by
  obtain ⟨-, v, hv⟩ := EdgeSubset.mem_internalFlags_iff.mp hint
  intro hx
  rw [hx, V.attach_boundaryFlag] at hv
  exact absurd hv (by simp)

/-- **The chain direction survives the glue.**  At a surviving label
whose entry edge is internal, the unglued orientation reads what the
glued one does. -/
theorem chainDir_unglueOpen_surviving
    {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hopen : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    (hct : ∀ f ∈ t, (V.gluePairOpen i j hij hopen).pairing f ∈ t)
    (hcL : ∀ f ∈ liftSubsetOpen hopen t, V.pairing f ∈ liftSubsetOpen hopen
      t)
    (κ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairOpen i j hij hopen)).RelTransitionSystem)
    (o' : κ'.Orientation) (b : SurvivingLabel L i j)
    (hint : V.pairing (V.boundaryFlag b.val)
      ∈ (EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
        EdgeSubset V).internalFlags) :
    chainDir (unglueOrientationOpen hij hopen t hct hcL κ' o')
        (V.boundaryFlag b.val)
      = chainDir o'
        ((V.gluePairOpen i j hij hopen).boundaryFlag b) := by
  have hne1 : V.pairing (V.boundaryFlag b.val) ≠ V.boundaryFlag i :=
    internal_ne_boundaryFlag hopen t hcL hint
  have hne2 : V.pairing (V.boundaryFlag b.val) ≠ V.boundaryFlag j :=
    internal_ne_boundaryFlag hopen t hcL hint
  have hval : ((V.gluePairOpen i j hij hopen).pairing
      (glueBoundaryFlag V i j b)).val
      = V.pairing (V.boundaryFlag b.val) :=
    gluePairOpen_pairing_val_of_ne hij hopen
      (glueBoundaryFlag V i j b) hne1 hne2
  change unglueIsOut o'.isOut (V.pairing (V.boundaryFlag b.val))
    = o'.isOut ((V.gluePairOpen i j hij hopen).pairing
        (glueBoundaryFlag V i j b))
  rw [show V.pairing (V.boundaryFlag b.val)
      = ((V.gluePairOpen i j hij hopen).pairing
          (glueBoundaryFlag V i j b)).val from hval.symm,
    unglueIsOut_val o'.isOut ((V.gluePairOpen i j hij hopen).pairing
      (glueBoundaryFlag V i j b))]

/-- **The alternation passes down an open glue.**  At a pair of
surviving labels whose entry edges are internal, the base inherits
the glued fragment's alternation. -/
theorem chainDir_alternates_unglueOpen
    {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hopen : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    (hct : ∀ f ∈ t, (V.gluePairOpen i j hij hopen).pairing f ∈ t)
    (hcL : ∀ f ∈ liftSubsetOpen hopen t, V.pairing f ∈ liftSubsetOpen hopen
      t)
    (κ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairOpen i j hij hopen)).RelTransitionSystem)
    (o' : κ'.Orientation) (bl br : SurvivingLabel L i j)
    (hIl : V.pairing (V.boundaryFlag bl.val)
      ∈ (EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
        EdgeSubset V).internalFlags)
    (hIr : V.pairing (V.boundaryFlag br.val)
      ∈ (EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
        EdgeSubset V).internalFlags)
    (halt : chainDir o'
        ((V.gluePairOpen i j hij hopen).boundaryFlag br)
      = !chainDir o'
        ((V.gluePairOpen i j hij hopen).boundaryFlag bl)) :
    chainDir (unglueOrientationOpen hij hopen t hct hcL κ' o')
        (V.boundaryFlag br.val)
      = !chainDir (unglueOrientationOpen hij hopen t hct hcL κ' o')
        (V.boundaryFlag bl.val) := by
  rw [chainDir_unglueOpen_surviving hij hopen t hct hcL κ' o' br hIr,
    chainDir_unglueOpen_surviving hij hopen t hct hcL κ' o' bl hIl]
  exact halt

/-! ## Across a through-edge into the cut

Where the entry edge at a surviving label is the cut's own flag —
that is, where the label is joined to the cut by a single edge — the
glue absorbs that edge and the label's new entry edge is the *other*
side's.  The chain direction there is therefore the base's at the
other glued label, and this is what carries the interface's
alternation along a chain of through-edges.
-/

end OpenCut

/-! ## The closing cut

A closing cut takes its own edge away and touches nothing else: no
surviving label's entry edge is one of its flags, and every direction
reads through unchanged.
-/

section ClosedCut

variable {L : Type}

/-- **The chain direction survives a closing glue.** -/
theorem chainDir_unglueClosed_surviving {V : Fragment L} {i : L} {j : L}
    (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    (hct : ∀ f ∈ t, (V.gluePairClosed i j hclosed).pairing f ∈ t) (b : Bool)
    (hcL : ∀ f ∈ liftSubsetClosed t b, V.pairing f ∈ liftSubsetClosed t b)
    (κ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).RelTransitionSystem)
    (o' : κ'.Orientation) (bl : SurvivingLabel L i j) :
    chainDir (unglueOrientationClosed hclosed b t hct hcL κ' o')
        (V.boundaryFlag bl.val)
      = chainDir o'
        ((V.gluePairClosed i j hclosed).boundaryFlag bl) := by
  change unglueIsOut o'.isOut (V.pairing (V.boundaryFlag bl.val))
    = o'.isOut ((V.gluePairClosed i j hclosed).pairing
        (glueBoundaryFlag V i j bl))
  rw [show V.pairing (V.boundaryFlag bl.val)
      = ((V.gluePairClosed i j hclosed).pairing
          (glueBoundaryFlag V i j bl)).val
    from (gluePairClosed_pairing_val hclosed
      (glueBoundaryFlag V i j bl)).symm,
    unglueIsOut_val o'.isOut ((V.gluePairClosed i j hclosed).pairing
      (glueBoundaryFlag V i j bl))]

/-- **The alternation passes down a closing glue.** -/
theorem chainDir_alternates_unglueClosed {V : Fragment L} {i : L} {j : L}
    (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
    (t : Finset (SurvivingFlag V i j))
    (hct : ∀ f ∈ t, (V.gluePairClosed i j hclosed).pairing f ∈ t) (b : Bool)
    (hcL : ∀ f ∈ liftSubsetClosed t b, V.pairing f ∈ liftSubsetClosed t b)
    (κ' : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).RelTransitionSystem)
    (o' : κ'.Orientation) (bl br : SurvivingLabel L i j)
    (halt : chainDir o'
        ((V.gluePairClosed i j hclosed).boundaryFlag br)
      = !chainDir o'
        ((V.gluePairClosed i j hclosed).boundaryFlag bl)) :
    chainDir (unglueOrientationClosed hclosed b t hct hcL κ' o')
        (V.boundaryFlag br.val)
      = !chainDir (unglueOrientationClosed hclosed b t hct hcL κ' o')
        (V.boundaryFlag bl.val) := by
  rw [chainDir_unglueClosed_surviving hclosed t hct b hcL κ' o' br,
    chainDir_unglueClosed_surviving hclosed t hct b hcL κ' o' bl]
  exact halt

end ClosedCut

/-! ## Reading the direction through the transports

The stage's data reaches the base through a relabel and, at the
`gluePair` dispatch, an equality of fragments.  Neither touches the
orientation's values, so neither touches the chain direction.
-/

section Transports

variable {L : Type}

/-- Transporting a subset does not move a direction. -/
theorem chainDir_orientOfEq {V : Fragment L}
    {F F' : EdgeSubset V} (hF : F = F')
    {κ : F.RelTransitionSystem} (o : κ.Orientation) (f : V.Flag) :
    chainDir (orientOfEq hF o) f = chainDir o f := by
  subst hF
  rfl

/-- Transport a flag along an equality of fragments. -/
noncomputable def flagOfEq {V₁ V₂ : Fragment L} (hV : V₁ = V₂)
    (f : V₁.Flag) : V₂.Flag := by
  subst hV; exact f

/-- The direction reads through a transport of the family along an
equality of fragments. -/
theorem chainDir_dataOfEq [LinearOrder L]
    {V₁ V₂ : Fragment L} (hV : V₁ = V₂)
    (𝒟 : DataFamily V₂) (s : Finset V₁.Flag)
    (hc : ∀ f ∈ s, V₁.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData)
    (hc' : ∀ f ∈ flagsOfEq V₁ V₂ hV s,
      V₂.pairing f ∈ flagsOfEq V₁ V₂ hV s)
    (hE' : (EdgeSubset.mk (flagsOfEq V₁ V₂ hV s) hc').Eulerian)
    (hne' : Nonempty
      (EdgeSubset.mk (flagsOfEq V₁ V₂ hV s) hc').CanonData)
    (f : V₁.Flag) :
    chainDir (dataOfEq hV 𝒟 s hc hE hne).2 f
      = chainDir (𝒟 (flagsOfEq V₁ V₂ hV s) hc' hE' hne').2
        (flagOfEq hV f) := by
  subst hV
  rfl

/-- The direction reads through a transport of the family along a
relabel. -/
theorem chainDir_relabelDataDown [LinearOrder L] {V : Fragment L}
    {β : Type} [LinearOrder β]
    (e : L ≃o β) (𝒟 : DataFamily (V.relabel e.toEquiv))
    (s : Finset V.Flag) (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData)
    (hc' : ∀ f ∈ s, (V.relabel e.toEquiv).pairing f ∈ s)
    (hE' : (EdgeSubset.mk s hc' :
      EdgeSubset (V.relabel e.toEquiv)).Eulerian)
    (hne' : Nonempty (EdgeSubset.mk s hc' :
      EdgeSubset (V.relabel e.toEquiv)).CanonData)
    (f : V.Flag) :
    chainDir (relabelDataDown e 𝒟 s hc hE hne).2 f
      = chainDir (𝒟 s hc' hE' hne').2 f := rfl

end Transports

/-! ## The interface pairs of a stage

The composition glues the pair `(inl a, inr a)` at each `a`.  Naming
those labels lets the alternation be stated for a whole stage, and
the two lemmas below are the identifications the iteration needs: the
top pair is the stage's own cut, and a lower pair survives it
unchanged.
-/

section InterfacePairs

/-- The left label of the `a`-th interface pair. -/
def intL (n : ℕ) (a : Fin n) : Fin (0 + n) ⊕ Fin (n + 0) :=
  Sum.inl (Fin.cast (by omega) a)

/-- The right label of the `a`-th interface pair. -/
def intR (n : ℕ) (a : Fin n) : Fin (0 + n) ⊕ Fin (n + 0) :=
  Sum.inr (Fin.cast (by omega) a)

/-- The top pair is the stage's own cut. -/
theorem intL_last (n : ℕ) : intL (n + 1) (Fin.last n) = cutL n :=
  congrArg Sum.inl (Fin.ext (by simp))

/-- The top pair is the stage's own cut. -/
theorem intR_last (n : ℕ) : intR (n + 1) (Fin.last n) = cutR n :=
  congrArg Sum.inr (Fin.ext (by simp))

/-- A lower pair survives the stage's cut. -/
theorem intL_castSucc_ne (n : ℕ) (b : Fin n) :
    intL (n + 1) b.castSucc ≠ cutL n ∧
      intL (n + 1) b.castSucc ≠ cutR n := by
  refine ⟨fun hx => ?_, fun hx => absurd hx (by simp [intL, cutR])⟩
  have hv := congrArg Fin.val (Sum.inl.inj hx)
  have := b.isLt
  simp only [Fin.val_cast, Fin.val_castSucc] at hv
  omega

/-- A lower pair survives the stage's cut. -/
theorem intR_castSucc_ne (n : ℕ) (b : Fin n) :
    intR (n + 1) b.castSucc ≠ cutL n ∧
      intR (n + 1) b.castSucc ≠ cutR n := by
  refine ⟨fun hx => absurd hx (by simp [intR, cutL]), fun hx => ?_⟩
  have hv := congrArg Fin.val (Sum.inr.inj hx)
  have := b.isLt
  simp only [Fin.val_cast, Fin.val_castSucc] at hv
  omega

/-- The step reads a lower left label as the next stage's. -/
theorem interfaceStepEquiv_intL (n : ℕ) (b : Fin n) :
    interfaceStepEquiv 0 n 0
        ⟨intL (n + 1) b.castSucc, intL_castSucc_ne n b⟩
      = intL n b := by
  change interfaceStepEquiv 0 n 0
      ⟨Sum.inl (Fin.cast (by omega) b.castSucc),
        intL_castSucc_ne n b⟩ = _
  rw [interfaceStepEquiv_apply_inl 0 n 0 _ (intL_castSucc_ne n b)]
  refine congrArg Sum.inl (Fin.ext ?_)
  rw [finRemoveEquiv_top_val (n := 0 + n)]
  simp

/-- The step reads a lower right label as the next stage's. -/
theorem interfaceStepEquiv_intR (n : ℕ) (b : Fin n) :
    interfaceStepEquiv 0 n 0
        ⟨intR (n + 1) b.castSucc, intR_castSucc_ne n b⟩
      = intR n b := by
  change interfaceStepEquiv 0 n 0
      ⟨Sum.inr (Fin.cast (by omega) b.castSucc),
        intR_castSucc_ne n b⟩ = _
  rw [interfaceStepEquiv_apply_inr 0 n 0 _ (intR_castSucc_ne n b)]
  refine congrArg Sum.inr (Fin.ext ?_)
  rw [rightRemoveEquiv_val]
  have := b.isLt
  simp only [Fin.val_cast, Fin.val_castSucc]
  rw [ite_eq_left (by omega)]

/-! ## The subsets the composition reaches

The glue's own subsets are the base's whose drop is closed under the
rewire at every stage.  Off those the base's summand vanishes on a
diagonal state (`rewire_closed_of_liftOpen_closed`), so the
alternation is only ever wanted on them.
-/

/-- The lexicographic order on the stage's label type. -/
@[reducible] local instance reachOrder (n : ℕ) :
    LinearOrder (Fin (0 + n) ⊕ Fin (n + 0)) :=
  sumLexLinearOrder _ _

/-- The order the composition's own (empty) label type carries. -/
@[reducible] local instance reachOrderTop :
    LinearOrder (Fin 0 ⊕ Fin 0) :=
  sumLexLinearOrder _ _

/-- The same order one stage up. -/
@[reducible] local instance reachOrderSucc (n : ℕ) :
    LinearOrder (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) :=
  sumLexLinearOrder _ _

open Classical in
/-- **The subsets the composition reaches.** -/
def Reachable : (n : ℕ) →
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0))) →
    Finset V.Flag → Prop
  | 0, _, _ => True
  | n + 1, V, s =>
      if hcl : V.pairing (V.boundaryFlag (cutL n))
          = V.boundaryFlag (cutR n) then
        Reachable n (stepFragment n V)
          (flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
            (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
            (gluePair_eq_closed n V hcl)
            (V.dropSubset (cutL n) (cutR n) s))
      else
        (∀ f ∈ V.dropSubset (cutL n) (cutR n) s,
            (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n)
              hcl).pairing f
              ∈ V.dropSubset (cutL n) (cutR n) s)
          ∧ Reachable n (stepFragment n V)
            (flagsOfEq
              (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hcl)
              (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
              (gluePair_eq_open n V hcl)
              (V.dropSubset (cutL n) (cutR n) s))

open Classical in
/-- The reach, one stage down, at an open cut. -/
theorem reachable_succ_open (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n)) (s : Finset V.Flag)
    (hr : Reachable (n + 1) V s) :
    (∀ f ∈ V.dropSubset (cutL n) (cutR n) s,
        (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n)
          hop).pairing f ∈ V.dropSubset (cutL n) (cutR n) s)
      ∧ Reachable n (stepFragment n V)
        (flagsOfEq
          (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n) hop)
          (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
          (gluePair_eq_open n V hop)
          (V.dropSubset (cutL n) (cutR n) s)) := by
  have hr' : (if hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n) then _ else _) := hr
  rwa [dite_eq_right hop] at hr'

open Classical in
/-- The reach, one stage down, at a closing cut. -/
theorem reachable_succ_closed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n)) (s : Finset V.Flag)
    (hr : Reachable (n + 1) V s) :
    Reachable n (stepFragment n V)
      (flagsOfEq (V.gluePairClosed (cutL n) (cutR n) hcl)
        (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
        (gluePair_eq_closed n V hcl)
        (V.dropSubset (cutL n) (cutR n) s)) := by
  have hr' : (if hc : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n) then _ else _) := hr
  rwa [dite_eq_left hcl] at hr'

open Classical in
/-- **The stage's own cut alternates.**  For a reached subset the
pushed-back data is the glued fragment's, unglued, and there the two
glued labels' directions are opposite. -/
theorem chainDir_stepDataDown_top (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (𝒟step : DataFamily (stepFragment n V)) (s : Finset V.Flag)
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData)
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (hdc : ∀ f ∈ V.dropSubset (cutL n) (cutR n) s,
      (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n)
        hop).pairing f ∈ V.dropSubset (cutL n) (cutR n) s)
    (hIl : V.pairing (V.boundaryFlag (cutL n))
      ∈ (EdgeSubset.mk s hc).internalFlags)
    (hIr : V.pairing (V.boundaryFlag (cutR n))
      ∈ (EdgeSubset.mk s hc).internalFlags) :
    chainDir (stepDataDown n V 𝒟step s hc hE hne).2
        (V.boundaryFlag (cutR n))
      = !chainDir (stepDataDown n V 𝒟step s hc hE hne).2
        (V.boundaryFlag (cutL n)) := by
  have hlift : liftSubsetOpen hop
      (V.dropSubset (cutL n) (cutR n) s) = s :=
    liftSubsetOpen_dropSubset (cutL_ne_cutR n) hop s hc
  have hcL : ∀ f ∈ liftSubsetOpen hop
      (V.dropSubset (cutL n) (cutR n) s),
      V.pairing f ∈ liftSubsetOpen hop
        (V.dropSubset (cutL n) (cutR n) s) := by
    rw [hlift]; exact hc
  have hF : (EdgeSubset.mk (liftSubsetOpen hop
        (V.dropSubset (cutL n) (cutR n) s)) hcL : EdgeSubset V)
      = EdgeSubset.mk s hc := EdgeSubset.ext hlift
  have hEt : (EdgeSubset.mk (V.dropSubset (cutL n) (cutR n) s) hdc :
      EdgeSubset (V.gluePairOpen (cutL n) (cutR n)
        (cutL_ne_cutR n) hop)).Eulerian :=
    (eulerian_lift_open_iff (cutL_ne_cutR n) hop _ hdc hcL).mp
      (by rw [hF]; exact hE)
  have hnet : Nonempty (EdgeSubset.mk
      (V.dropSubset (cutL n) (cutR n) s) hdc :
      EdgeSubset (V.gluePairOpen (cutL n) (cutR n)
        (cutL_ne_cutR n) hop)).CanonData :=
    nonempty_canonData_glueOpen (cutL_ne_cutR n) hop _ hdc hcL
      (by rw [hF]; exact hne)
  have hstep : stepDataDown n V 𝒟step
      = unglueDataOpen (cutL_ne_cutR n) hop
        (dataOfEq (gluePair_eq_open n V hop)
          (stepDataGlued n V 𝒟step)) := by
    unfold stepDataDown
    rw [dite_eq_right hop]
  have hIl' : (partnerSurvI hop).val
      ∈ (EdgeSubset.mk (liftSubsetOpen hop
        (V.dropSubset (cutL n) (cutR n) s)) hcL :
        EdgeSubset V).internalFlags := by
    rw [hF]; exact hIl
  have hIr' : (partnerSurvJ hop).val
      ∈ (EdgeSubset.mk (liftSubsetOpen hop
        (V.dropSubset (cutL n) (cutR n) s)) hcL :
        EdgeSubset V).internalFlags := by
    rw [hF]; exact hIr
  rw [hstep, unglueDataOpen_apply (cutL_ne_cutR n) hop _ s hc hE hne
      (V.dropSubset (cutL n) (cutR n) s) rfl hdc hcL hF hEt hnet,
    chainDir_orientOfEq, chainDir_orientOfEq]
  exact chainDir_unglueOpen_alternates (cutL_ne_cutR n) hop _ hdc
    hcL _ _ hIl' hIr'

open Classical in
/-- **A lower pair's alternation passes down an open stage.** -/
theorem chainDir_stepDataDown_lower_open (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (𝒟step : DataFamily (stepFragment n V)) (s : Finset V.Flag)
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData)
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (hdc : ∀ f ∈ V.dropSubset (cutL n) (cutR n) s,
      (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n)
        hop).pairing f ∈ V.dropSubset (cutL n) (cutR n) s)
    (bl br : SurvivingLabel
      (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)) (cutL n) (cutR n))
    (hIl : V.pairing (V.boundaryFlag bl.val)
      ∈ (EdgeSubset.mk s hc).internalFlags)
    (hIr : V.pairing (V.boundaryFlag br.val)
      ∈ (EdgeSubset.mk s hc).internalFlags)
    (hEt : (EdgeSubset.mk (V.dropSubset (cutL n) (cutR n) s) hdc :
      EdgeSubset (V.gluePairOpen (cutL n) (cutR n)
        (cutL_ne_cutR n) hop)).Eulerian)
    (hnet : Nonempty (EdgeSubset.mk
      (V.dropSubset (cutL n) (cutR n) s) hdc :
      EdgeSubset (V.gluePairOpen (cutL n) (cutR n)
        (cutL_ne_cutR n) hop)).CanonData)
    (halt : chainDir
        ((dataOfEq (gluePair_eq_open n V hop)
          (stepDataGlued n V 𝒟step))
          (V.dropSubset (cutL n) (cutR n) s) hdc hEt hnet).2
        ((V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n)
          hop).boundaryFlag br)
      = !chainDir
        ((dataOfEq (gluePair_eq_open n V hop)
          (stepDataGlued n V 𝒟step))
          (V.dropSubset (cutL n) (cutR n) s) hdc hEt hnet).2
        ((V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n)
          hop).boundaryFlag bl)) :
    chainDir (stepDataDown n V 𝒟step s hc hE hne).2
        (V.boundaryFlag br.val)
      = !chainDir (stepDataDown n V 𝒟step s hc hE hne).2
        (V.boundaryFlag bl.val) := by
  have hlift : liftSubsetOpen hop
      (V.dropSubset (cutL n) (cutR n) s) = s :=
    liftSubsetOpen_dropSubset (cutL_ne_cutR n) hop s hc
  have hcL : ∀ f ∈ liftSubsetOpen hop
      (V.dropSubset (cutL n) (cutR n) s),
      V.pairing f ∈ liftSubsetOpen hop
        (V.dropSubset (cutL n) (cutR n) s) := by
    rw [hlift]; exact hc
  have hF : (EdgeSubset.mk (liftSubsetOpen hop
        (V.dropSubset (cutL n) (cutR n) s)) hcL : EdgeSubset V)
      = EdgeSubset.mk s hc := EdgeSubset.ext hlift
  have hIl' : V.pairing (V.boundaryFlag bl.val)
      ∈ (EdgeSubset.mk (liftSubsetOpen hop
        (V.dropSubset (cutL n) (cutR n) s)) hcL :
        EdgeSubset V).internalFlags := by
    rw [hF]; exact hIl
  have hIr' : V.pairing (V.boundaryFlag br.val)
      ∈ (EdgeSubset.mk (liftSubsetOpen hop
        (V.dropSubset (cutL n) (cutR n) s)) hcL :
        EdgeSubset V).internalFlags := by
    rw [hF]; exact hIr
  have hstep : stepDataDown n V 𝒟step
      = unglueDataOpen (cutL_ne_cutR n) hop
        (dataOfEq (gluePair_eq_open n V hop)
          (stepDataGlued n V 𝒟step)) := by
    unfold stepDataDown
    rw [dite_eq_right hop]
  rw [hstep, unglueDataOpen_apply (cutL_ne_cutR n) hop _ s hc hE hne
      (V.dropSubset (cutL n) (cutR n) s) rfl hdc hcL hF hEt hnet,
    chainDir_orientOfEq, chainDir_orientOfEq]
  exact chainDir_alternates_unglueOpen (cutL_ne_cutR n) hop _ hdc
    hcL _ _ bl br hIl' hIr' halt

open Classical in
/-- **A pair's alternation passes down a closing stage.** -/
theorem chainDir_stepDataDown_lower_closed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (𝒟step : DataFamily (stepFragment n V)) (s : Finset V.Flag)
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData)
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (bl br : SurvivingLabel
      (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)) (cutL n) (cutR n))
    (hEt : (EdgeSubset.mk (V.dropSubset (cutL n) (cutR n) s)
      (dropSubset_pairing_closed_of_closed hcl s hc) :
      EdgeSubset (V.gluePairClosed (cutL n) (cutR n)
        hcl)).Eulerian)
    (hnet : Nonempty (EdgeSubset.mk
      (V.dropSubset (cutL n) (cutR n) s)
      (dropSubset_pairing_closed_of_closed hcl s hc) :
      EdgeSubset (V.gluePairClosed (cutL n) (cutR n)
        hcl)).CanonData)
    (halt : chainDir
        ((dataOfEq (gluePair_eq_closed n V hcl)
          (stepDataGlued n V 𝒟step))
          (V.dropSubset (cutL n) (cutR n) s)
          (dropSubset_pairing_closed_of_closed hcl s hc) hEt
          hnet).2
        ((V.gluePairClosed (cutL n) (cutR n) hcl).boundaryFlag br)
      = !chainDir
        ((dataOfEq (gluePair_eq_closed n V hcl)
          (stepDataGlued n V 𝒟step))
          (V.dropSubset (cutL n) (cutR n) s)
          (dropSubset_pairing_closed_of_closed hcl s hc) hEt
          hnet).2
        ((V.gluePairClosed (cutL n) (cutR n) hcl).boundaryFlag bl)) :
    chainDir (stepDataDown n V 𝒟step s hc hE hne).2
        (V.boundaryFlag br.val)
      = !chainDir (stepDataDown n V 𝒟step s hc hE hne).2
        (V.boundaryFlag bl.val) := by
  have hct := dropSubset_pairing_closed_of_closed hcl s hc
  have hlift : liftSubsetClosed (V.dropSubset (cutL n) (cutR n) s)
      (decide (V.boundaryFlag (cutL n) ∈ s)) = s :=
    liftSubsetClosed_dropSubset (cutL_ne_cutR n) hcl s hc
  have hcL : ∀ f ∈ liftSubsetClosed
      (V.dropSubset (cutL n) (cutR n) s)
      (decide (V.boundaryFlag (cutL n) ∈ s)),
      V.pairing f ∈ liftSubsetClosed
        (V.dropSubset (cutL n) (cutR n) s)
        (decide (V.boundaryFlag (cutL n) ∈ s)) := by
    rw [hlift]; exact hc
  have hF : (EdgeSubset.mk (liftSubsetClosed
        (V.dropSubset (cutL n) (cutR n) s)
        (decide (V.boundaryFlag (cutL n) ∈ s))) hcL :
      EdgeSubset V) = EdgeSubset.mk s hc := EdgeSubset.ext hlift
  have hstep : stepDataDown n V 𝒟step
      = unglueDataClosed (cutL_ne_cutR n) hcl
        (dataOfEq (gluePair_eq_closed n V hcl)
          (stepDataGlued n V 𝒟step)) := by
    unfold stepDataDown
    rw [dite_eq_left hcl]
  rw [hstep, unglueDataClosed_apply (cutL_ne_cutR n) hcl _ s hc hE
      hne (V.dropSubset (cutL n) (cutR n) s)
      (decide (V.boundaryFlag (cutL n) ∈ s)) rfl rfl hct hcL hF hEt
      hnet,
    chainDir_orientOfEq, chainDir_orientOfEq]
  exact chainDir_alternates_unglueClosed hcl _ hct _ hcL _ _ bl br
    halt

/-- A boundary flag is never internal. -/
theorem boundaryFlag_not_internal {L' : Type}
    {W : Fragment L'} (F : EdgeSubset W) (b : L') :
    W.boundaryFlag b ∉ F.internalFlags := by
  intro hx
  obtain ⟨-, v, hv⟩ := EdgeSubset.mem_internalFlags_iff.mp hx
  rw [W.attach_boundaryFlag] at hv
  exact absurd hv (by simp)

/-- Transporting a boundary flag along an equality of fragments. -/
theorem flagOfEq_boundaryFlag {L' : Type} {V₁ V₂ : Fragment L'}
    (hV : V₁ = V₂) (b : L') :
    flagOfEq hV (V₁.boundaryFlag b) = V₂.boundaryFlag b := by
  subst hV
  rfl

/-- Closure transports along an equality of fragments. -/
theorem flagsOfEq_pairing_mem {L : Type} {V₁ V₂ : Fragment L}
    (hV : V₁ = V₂)
    (t : Finset V₁.Flag) (h : ∀ f ∈ t, V₁.pairing f ∈ t) :
    ∀ f ∈ flagsOfEq V₁ V₂ hV t,
      V₂.pairing f ∈ flagsOfEq V₁ V₂ hV t := by
  subst hV
  exact h

/-- Being Eulerian transports along an equality of fragments. -/
theorem flagsOfEq_eulerian {L : Type} {V₁ V₂ : Fragment L}
    (hV : V₁ = V₂)
    (t : Finset V₁.Flag) (h : ∀ f ∈ t, V₁.pairing f ∈ t)
    (hEt : (EdgeSubset.mk t h).Eulerian) :
    (EdgeSubset.mk (flagsOfEq V₁ V₂ hV t)
      (flagsOfEq_pairing_mem hV t h)).Eulerian := by
  subst hV
  exact hEt

/-- Canonical data transport along an equality of fragments. -/
theorem flagsOfEq_canon {L : Type} [LinearOrder L]
    {V₁ V₂ : Fragment L} (hV : V₁ = V₂)
    (t : Finset V₁.Flag) (h : ∀ f ∈ t, V₁.pairing f ∈ t)
    (hnet : Nonempty (EdgeSubset.mk t h).CanonData) :
    Nonempty (EdgeSubset.mk (flagsOfEq V₁ V₂ hV t)
      (flagsOfEq_pairing_mem hV t h)).CanonData := by
  subst hV
  exact hnet

/-- The stage's boundary flag, read on the glued fragment. -/
theorem stepFragment_boundaryFlag (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (b : Fin (0 + n) ⊕ Fin (n + 0)) :
    (stepFragment n V).boundaryFlag b
      = (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n)).boundaryFlag
        ((interfaceStepEquiv 0 n 0).symm b) := rfl

open Classical in
/-- The dropped subset is Eulerian at an open stage. -/
theorem eulerian_drop_open (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (s : Finset V.Flag) (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (hdc : ∀ f ∈ V.dropSubset (cutL n) (cutR n) s,
      (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n)
        hop).pairing f ∈ V.dropSubset (cutL n) (cutR n) s) :
    (EdgeSubset.mk (V.dropSubset (cutL n) (cutR n) s) hdc :
      EdgeSubset (V.gluePairOpen (cutL n) (cutR n)
        (cutL_ne_cutR n) hop)).Eulerian := by
  have hlift := liftSubsetOpen_dropSubset (cutL_ne_cutR n) hop s hc
  have hcL : ∀ f ∈ liftSubsetOpen hop
      (V.dropSubset (cutL n) (cutR n) s),
      V.pairing f ∈ liftSubsetOpen hop
        (V.dropSubset (cutL n) (cutR n) s) := by
    rw [hlift]; exact hc
  refine (eulerian_lift_open_iff (cutL_ne_cutR n) hop _ hdc hcL).mp
    ?_
  rw [show (EdgeSubset.mk (liftSubsetOpen hop
        (V.dropSubset (cutL n) (cutR n) s)) hcL : EdgeSubset V)
      = EdgeSubset.mk s hc from EdgeSubset.ext hlift]
  exact hE

open Classical in
/-- The dropped subset carries canonical data at an open stage. -/
theorem canon_drop_open (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (s : Finset V.Flag) (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData)
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (hdc : ∀ f ∈ V.dropSubset (cutL n) (cutR n) s,
      (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n)
        hop).pairing f ∈ V.dropSubset (cutL n) (cutR n) s) :
    Nonempty (EdgeSubset.mk (V.dropSubset (cutL n) (cutR n) s) hdc :
      EdgeSubset (V.gluePairOpen (cutL n) (cutR n)
        (cutL_ne_cutR n) hop)).CanonData := by
  have hlift := liftSubsetOpen_dropSubset (cutL_ne_cutR n) hop s hc
  have hcL : ∀ f ∈ liftSubsetOpen hop
      (V.dropSubset (cutL n) (cutR n) s),
      V.pairing f ∈ liftSubsetOpen hop
        (V.dropSubset (cutL n) (cutR n) s) := by
    rw [hlift]; exact hc
  refine nonempty_canonData_glueOpen (cutL_ne_cutR n) hop _ hdc hcL
    ?_
  rw [show (EdgeSubset.mk (liftSubsetOpen hop
        (V.dropSubset (cutL n) (cutR n) s)) hcL : EdgeSubset V)
      = EdgeSubset.mk s hc from EdgeSubset.ext hlift]
  exact hne

open Classical in
/-- The dropped subset is Eulerian at a closing stage. -/
theorem eulerian_drop_closed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (s : Finset V.Flag) (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n)) :
    (EdgeSubset.mk (V.dropSubset (cutL n) (cutR n) s)
      (dropSubset_pairing_closed_of_closed hcl s hc) :
      EdgeSubset (V.gluePairClosed (cutL n) (cutR n)
        hcl)).Eulerian := by
  have hlift := liftSubsetClosed_dropSubset (cutL_ne_cutR n) hcl s hc
  have hcL : ∀ f ∈ liftSubsetClosed
      (V.dropSubset (cutL n) (cutR n) s)
      (decide (V.boundaryFlag (cutL n) ∈ s)),
      V.pairing f ∈ liftSubsetClosed
        (V.dropSubset (cutL n) (cutR n) s)
        (decide (V.boundaryFlag (cutL n) ∈ s)) := by
    rw [hlift]; exact hc
  refine (eulerian_liftClosed_iff' hcl
    (decide (V.boundaryFlag (cutL n) ∈ s)) _
    (dropSubset_pairing_closed_of_closed hcl s hc) hcL).mp ?_
  rw [show (EdgeSubset.mk (liftSubsetClosed
        (V.dropSubset (cutL n) (cutR n) s)
        (decide (V.boundaryFlag (cutL n) ∈ s))) hcL :
      EdgeSubset V) = EdgeSubset.mk s hc from EdgeSubset.ext hlift]
  exact hE

open Classical in
/-- The dropped subset carries canonical data at a closing stage. -/
theorem canon_drop_closed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (s : Finset V.Flag) (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData)
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n)) :
    Nonempty (EdgeSubset.mk (V.dropSubset (cutL n) (cutR n) s)
      (dropSubset_pairing_closed_of_closed hcl s hc) :
      EdgeSubset (V.gluePairClosed (cutL n) (cutR n)
        hcl)).CanonData := by
  have hlift := liftSubsetClosed_dropSubset (cutL_ne_cutR n) hcl s hc
  have hcL : ∀ f ∈ liftSubsetClosed
      (V.dropSubset (cutL n) (cutR n) s)
      (decide (V.boundaryFlag (cutL n) ∈ s)),
      V.pairing f ∈ liftSubsetClosed
        (V.dropSubset (cutL n) (cutR n) s)
        (decide (V.boundaryFlag (cutL n) ∈ s)) := by
    rw [hlift]; exact hc
  refine nonempty_canonData_glueClosed hcl _
    (dropSubset_pairing_closed_of_closed hcl s hc)
    (decide (V.boundaryFlag (cutL n) ∈ s)) hcL ?_
  rw [show (EdgeSubset.mk (liftSubsetClosed
        (V.dropSubset (cutL n) (cutR n) s)
        (decide (V.boundaryFlag (cutL n) ∈ s))) hcL :
      EdgeSubset V) = EdgeSubset.mk s hc from EdgeSubset.ext hlift]
  exact hne

open Classical in
/-- The stage's subset, from the glued fragment's. -/
theorem stage_pairing_mem (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    {Vg : Fragment (SurvivingLabel
      (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)) (cutL n) (cutR n))}
    (hV : Vg = V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
    (t : Finset Vg.Flag) (hct : ∀ f ∈ t, Vg.pairing f ∈ t) :
    ∀ f ∈ flagsOfEq Vg _ hV t,
      (stepFragment n V).pairing f ∈ flagsOfEq Vg _ hV t :=
  flagsOfEq_pairing_mem hV t hct

open Classical in
/-- **The stage's data, read on the glued fragment.**  The dispatch's
identification and the stage's relabel both leave the direction
alone, so a direction at the glued fragment is the stage's at the
relabelled label. -/
theorem chainDir_stepDataGlued (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (𝒟step : DataFamily (stepFragment n V))
    {Vg : Fragment (SurvivingLabel
      (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)) (cutL n) (cutR n))}
    (hV : Vg = V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
    (t : Finset Vg.Flag) (hct : ∀ f ∈ t, Vg.pairing f ∈ t)
    (hEt : (EdgeSubset.mk t hct).Eulerian)
    (hnet : Nonempty (EdgeSubset.mk t hct).CanonData)
    (hES : (EdgeSubset.mk (flagsOfEq Vg _ hV t)
      (stage_pairing_mem n V hV t hct) :
        EdgeSubset (stepFragment n V)).Eulerian)
    (hneS : Nonempty (EdgeSubset.mk (flagsOfEq Vg _ hV t)
      (stage_pairing_mem n V hV t hct) :
        EdgeSubset (stepFragment n V)).CanonData)
    (bl : SurvivingLabel
      (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)) (cutL n) (cutR n)) :
    chainDir ((dataOfEq hV (stepDataGlued n V 𝒟step)) t hct hEt
        hnet).2 (Vg.boundaryFlag bl)
      = chainDir (𝒟step (flagsOfEq Vg _ hV t)
          (stage_pairing_mem n V hV t hct) hES hneS).2
        ((stepFragment n V).boundaryFlag
          (interfaceStepEquiv 0 n 0 bl)) := by
  rw [chainDir_dataOfEq hV (stepDataGlued n V 𝒟step) t hct hEt hnet
      (flagsOfEq_pairing_mem hV t hct)
      (flagsOfEq_eulerian hV t hct hEt)
      (flagsOfEq_canon hV t hct hnet) (Vg.boundaryFlag bl),
    flagOfEq_boundaryFlag hV bl]
  unfold stepDataGlued
  rw [chainDir_relabelDataDown (stepIso n) 𝒟step
      (flagsOfEq Vg _ hV t)
      (flagsOfEq_pairing_mem hV t hct)
      (flagsOfEq_eulerian hV t hct hEt)
      (flagsOfEq_canon hV t hct hnet)
      (stage_pairing_mem n V hV t hct) hES hneS _,
    stepFragment_boundaryFlag n V (interfaceStepEquiv 0 n 0 bl),
    Equiv.symm_apply_apply]
  rfl

open Classical in
/-- Internality passes from the base to the stage, at a closing
cut. -/
theorem internal_stage_closed (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hcl : V.pairing (V.boundaryFlag (cutL n))
      = V.boundaryFlag (cutR n))
    (s : Finset V.Flag) (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (bl : SurvivingLabel
      (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)) (cutL n) (cutR n))
    (hI : V.pairing (V.boundaryFlag bl.val)
      ∈ (EdgeSubset.mk s hc).internalFlags) :
    (V.gluePairClosed (cutL n) (cutR n) hcl).pairing
        ((V.gluePairClosed (cutL n) (cutR n) hcl).boundaryFlag bl)
      ∈ (EdgeSubset.mk (V.dropSubset (cutL n) (cutR n) s)
        (dropSubset_pairing_closed_of_closed hcl s hc) :
        EdgeSubset (V.gluePairClosed (cutL n) (cutR n)
          hcl)).internalFlags := by
  have hlift := liftSubsetClosed_dropSubset (cutL_ne_cutR n) hcl s hc
  have hcL : ∀ f ∈ liftSubsetClosed
      (V.dropSubset (cutL n) (cutR n) s)
      (decide (V.boundaryFlag (cutL n) ∈ s)),
      V.pairing f ∈ liftSubsetClosed
        (V.dropSubset (cutL n) (cutR n) s)
        (decide (V.boundaryFlag (cutL n) ∈ s)) := by
    rw [hlift]; exact hc
  refine (mem_internalFlags_glueClosed hcl
    (decide (V.boundaryFlag (cutL n) ∈ s)) _
    (dropSubset_pairing_closed_of_closed hcl s hc) hcL).mpr ?_
  rw [show ((V.gluePairClosed (cutL n) (cutR n) hcl).pairing
        ((V.gluePairClosed (cutL n) (cutR n) hcl).boundaryFlag
          bl)).val = V.pairing (V.boundaryFlag bl.val)
    from gluePairClosed_pairing_val hcl _,
    show (EdgeSubset.mk (liftSubsetClosed
        (V.dropSubset (cutL n) (cutR n) s)
        (decide (V.boundaryFlag (cutL n) ∈ s))) hcL :
      EdgeSubset V) = EdgeSubset.mk s hc from EdgeSubset.ext hlift]
  exact hI

open Classical in
/-- Internality passes from the base to the stage, at an open
cut. -/
theorem internal_stage_open (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    (hop : V.pairing (V.boundaryFlag (cutL n))
      ≠ V.boundaryFlag (cutR n))
    (s : Finset V.Flag) (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hdc : ∀ f ∈ V.dropSubset (cutL n) (cutR n) s,
      (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n)
        hop).pairing f ∈ V.dropSubset (cutL n) (cutR n) s)
    (bl : SurvivingLabel
      (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)) (cutL n) (cutR n))
    (hI : V.pairing (V.boundaryFlag bl.val)
      ∈ (EdgeSubset.mk s hc).internalFlags) :
    (V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n)
        hop).pairing
        ((V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n)
          hop).boundaryFlag bl)
      ∈ (EdgeSubset.mk (V.dropSubset (cutL n) (cutR n) s) hdc :
        EdgeSubset (V.gluePairOpen (cutL n) (cutR n)
          (cutL_ne_cutR n) hop)).internalFlags := by
  have hlift := liftSubsetOpen_dropSubset (cutL_ne_cutR n) hop s hc
  have hcL : ∀ f ∈ liftSubsetOpen hop
      (V.dropSubset (cutL n) (cutR n) s),
      V.pairing f ∈ liftSubsetOpen hop
        (V.dropSubset (cutL n) (cutR n) s) := by
    rw [hlift]; exact hc
  have hne1 : V.pairing (V.boundaryFlag bl.val)
      ≠ V.boundaryFlag (cutL n) :=
    internal_ne_boundaryFlag hop _ hcL
      (by
        rw [show (EdgeSubset.mk (liftSubsetOpen
              hop (V.dropSubset (cutL n) (cutR n) s)) hcL :
            EdgeSubset V) = EdgeSubset.mk s hc
          from EdgeSubset.ext hlift]
        exact hI)
  have hne2 : V.pairing (V.boundaryFlag bl.val)
      ≠ V.boundaryFlag (cutR n) :=
    internal_ne_boundaryFlag hop _ hcL
      (by
        rw [show (EdgeSubset.mk (liftSubsetOpen
              hop (V.dropSubset (cutL n) (cutR n) s)) hcL :
            EdgeSubset V) = EdgeSubset.mk s hc
          from EdgeSubset.ext hlift]
        exact hI)
  have hval : ((V.gluePairOpen (cutL n) (cutR n) (cutL_ne_cutR n)
      hop).pairing ((V.gluePairOpen (cutL n) (cutR n)
        (cutL_ne_cutR n) hop).boundaryFlag bl)).val
      = V.pairing (V.boundaryFlag bl.val) :=
    gluePairOpen_pairing_val_of_ne (cutL_ne_cutR n) hop _ hne1 hne2
  refine (mem_internalFlags_glueOpen (cutL_ne_cutR n) hop _ hdc
    hcL).mpr ?_
  rw [hval,
    show (EdgeSubset.mk (liftSubsetOpen hop
        (V.dropSubset (cutL n) (cutR n) s)) hcL : EdgeSubset V)
      = EdgeSubset.mk s hc from EdgeSubset.ext hlift]
  exact hI

open Classical in
/-- Being Eulerian passes to the stage. -/
theorem stage_eulerian (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    {Vg : Fragment (SurvivingLabel
      (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)) (cutL n) (cutR n))}
    (hV : Vg = V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
    (t : Finset Vg.Flag) (hct : ∀ f ∈ t, Vg.pairing f ∈ t)
    (hEt : (EdgeSubset.mk t hct).Eulerian) :
    (EdgeSubset.mk (flagsOfEq Vg _ hV t)
      (stage_pairing_mem n V hV t hct) :
      EdgeSubset (stepFragment n V)).Eulerian := by
  subst hV
  exact (relabelUp_eulerian (stepIso n).toEquiv
    (EdgeSubset.mk t hct)).mpr hEt

open Classical in
/-- Canonical data passes to the stage. -/
theorem stage_canon (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    {Vg : Fragment (SurvivingLabel
      (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)) (cutL n) (cutR n))}
    (hV : Vg = V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
    (t : Finset Vg.Flag) (hct : ∀ f ∈ t, Vg.pairing f ∈ t)
    (hnet : Nonempty (EdgeSubset.mk t hct).CanonData) :
    Nonempty (EdgeSubset.mk (flagsOfEq Vg _ hV t)
      (stage_pairing_mem n V hV t hct) :
      EdgeSubset (stepFragment n V)).CanonData := by
  subst hV
  exact (nonempty_canonData_relabelUp (stepIso n)
    (EdgeSubset.mk t hct)).mpr hnet

open Classical in
/-- Internality passes to the stage. -/
theorem stage_internal (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)))
    {Vg : Fragment (SurvivingLabel
      (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)) (cutL n) (cutR n))}
    (hV : Vg = V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n))
    (t : Finset Vg.Flag) (hct : ∀ f ∈ t, Vg.pairing f ∈ t)
    (bl : SurvivingLabel
      (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0)) (cutL n) (cutR n))
    (hf : Vg.pairing (Vg.boundaryFlag bl)
      ∈ (EdgeSubset.mk t hct).internalFlags) :
    (stepFragment n V).pairing ((stepFragment n V).boundaryFlag
        (interfaceStepEquiv 0 n 0 bl))
      ∈ (EdgeSubset.mk (flagsOfEq Vg _ hV t)
        (stage_pairing_mem n V hV t hct) :
        EdgeSubset (stepFragment n V)).internalFlags := by
  subst hV
  rw [stepFragment_boundaryFlag n V (interfaceStepEquiv 0 n 0 bl),
    Equiv.symm_apply_apply]
  exact (relabelUp_internalFlags (stepIso n).toEquiv
    (EdgeSubset.mk t hct)).symm ▸ hf

open Classical in
/-- **The interface alternates.**  At a reached subset, the data the
composition pushes back to the base gives opposite directions at the
two ends of every interface pair whose partners are both internal.

This is RS21's step 1: the composition's Eulerian orientation, read
on the base, enters at one end of each glued pair and leaves at the
other. -/
theorem chainDir_pushData_alternates : ∀ (n : ℕ)
    (V : Fragment (Fin (0 + n) ⊕ Fin (n + 0)))
    (𝒟 : DataFamily (glueInterface 0 n 0 V)) (s : Finset V.Flag)
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData)
    (_hr : Reachable n V s) (a : Fin n),
    V.pairing (V.boundaryFlag (intL n a))
        ∈ (EdgeSubset.mk s hc).internalFlags →
    V.pairing (V.boundaryFlag (intR n a))
        ∈ (EdgeSubset.mk s hc).internalFlags →
    chainDir (pushData n V 𝒟 s hc hE hne).2
        (V.boundaryFlag (intR n a))
      = !chainDir (pushData n V 𝒟 s hc hE hne).2
        (V.boundaryFlag (intL n a))
  | 0, _, _, _, _, _, _, _, a => a.elim0
  | n + 1, V, 𝒟, s, hc, hE, hne, hr, a => by
    refine Fin.lastCases ?_ ?_ a
    · intro hIl hIr
      rw [intL_last] at hIl
      rw [intR_last] at hIr
      rw [intL_last, intR_last]
      by_cases hcl : V.pairing (V.boundaryFlag (cutL n))
          = V.boundaryFlag (cutR n)
      · exact absurd (hcl ▸ hIl)
          (boundaryFlag_not_internal (EdgeSubset.mk s hc) (cutR n))
      · exact chainDir_stepDataDown_top n V
          (pushData n (stepFragment n V) 𝒟) s hc hE hne hcl
          (reachable_succ_open n V hcl s hr).1 hIl hIr
    · intro b hIl hIr
      by_cases hcl : V.pairing (V.boundaryFlag (cutL n))
          = V.boundaryFlag (cutR n)
      · have hct := dropSubset_pairing_closed_of_closed hcl s hc
        have hEt := eulerian_drop_closed n V s hc hE hcl
        have hnet := canon_drop_closed n V s hc hne hcl
        have hES := stage_eulerian n V (gluePair_eq_closed n V hcl)
          _ hct hEt
        have hneS := stage_canon n V (gluePair_eq_closed n V hcl)
          _ hct hnet
        refine chainDir_stepDataDown_lower_closed n V
          (pushData n (stepFragment n V) 𝒟) s hc hE hne hcl
          ⟨intL (n + 1) b.castSucc, intL_castSucc_ne n b⟩
          ⟨intR (n + 1) b.castSucc, intR_castSucc_ne n b⟩ hEt hnet
          ?_
        rw [chainDir_stepDataGlued n V
            (pushData n (stepFragment n V) 𝒟)
            (gluePair_eq_closed n V hcl) _ hct hEt hnet hES hneS _,
          chainDir_stepDataGlued n V
            (pushData n (stepFragment n V) 𝒟)
            (gluePair_eq_closed n V hcl) _ hct hEt hnet hES hneS _,
          interfaceStepEquiv_intL, interfaceStepEquiv_intR]
        refine chainDir_pushData_alternates n (stepFragment n V) 𝒟
          _ _ hES hneS (reachable_succ_closed n V hcl s hr) b ?_ ?_
        · rw [← interfaceStepEquiv_intL n b]
          exact stage_internal n V (gluePair_eq_closed n V hcl) _
            hct _ (internal_stage_closed n V hcl s hc _ hIl)
        · rw [← interfaceStepEquiv_intR n b]
          exact stage_internal n V (gluePair_eq_closed n V hcl) _
            hct _ (internal_stage_closed n V hcl s hc _ hIr)
      · obtain ⟨hdc, hrs⟩ := reachable_succ_open n V hcl s hr
        have hEt := eulerian_drop_open n V s hc hE hcl hdc
        have hnet := canon_drop_open n V s hc hne hcl hdc
        have hES := stage_eulerian n V (gluePair_eq_open n V hcl)
          _ hdc hEt
        have hneS := stage_canon n V (gluePair_eq_open n V hcl)
          _ hdc hnet
        refine chainDir_stepDataDown_lower_open n V
          (pushData n (stepFragment n V) 𝒟) s hc hE hne hcl hdc
          ⟨intL (n + 1) b.castSucc, intL_castSucc_ne n b⟩
          ⟨intR (n + 1) b.castSucc, intR_castSucc_ne n b⟩ hIl hIr
          hEt hnet ?_
        rw [chainDir_stepDataGlued n V
            (pushData n (stepFragment n V) 𝒟)
            (gluePair_eq_open n V hcl) _ hdc hEt hnet hES hneS _,
          chainDir_stepDataGlued n V
            (pushData n (stepFragment n V) 𝒟)
            (gluePair_eq_open n V hcl) _ hdc hEt hnet hES hneS _,
          interfaceStepEquiv_intL, interfaceStepEquiv_intR]
        refine chainDir_pushData_alternates n (stepFragment n V) 𝒟
          _ _ hES hneS hrs b ?_ ?_
        · rw [← interfaceStepEquiv_intL n b]
          exact stage_internal n V (gluePair_eq_open n V hcl) _
            hdc _ (internal_stage_open n V hcl s hc hdc _ hIl)
        · rw [← interfaceStepEquiv_intR n b]
          exact stage_internal n V (gluePair_eq_open n V hcl) _
            hdc _ (internal_stage_open n V hcl s hc hdc _ hIr)

end InterfacePairs

end EdgeSubset

end RS
