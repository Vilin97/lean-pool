/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.LedgerRecursion

/-!
# Contracting the interface

RS21's (13) contracts the two fragments' tensors with the super
form one leg at a time, and the closing display of Theorem 6's
proof sums the result over the Eulerian subsets.  In the flag
model the composition glues one interface pair at a time, and
each glue is exactly such a contraction: the glued
fragment's summand is the base's summed over the two glued labels'
colours against the cut's own kernel.

This file names the data that contraction carries — the fragment, the
subset and the state at each stage — and the accumulated weight.  The
per-cut kernels are the ones the dispatches deliver: the super form
at a closed cut, and at an open one the configuration's own kernel,
which is the same form read in the basis the tensor twists into.
-/

@[expose] public section

namespace RS

namespace EdgeSubset

open Fragment Equiv
/-- The lexicographic order on the recursion's label type. -/
@[reducible] local instance contractOrder (n : ℕ) :
    LinearOrder (Fin (0 + n) ⊕ Fin (n + 0)) :=
  sumLexLinearOrder _ _

/-- The same order one stage up. -/
@[reducible] local instance contractOrderSucc (n : ℕ) :
    LinearOrder (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) :=
  sumLexLinearOrder _ _

/-! ## The stage's fragment and state -/

/-- The fragment one stage down: glue the top interface pair, then
relabel. -/
noncomputable def stepFragment (n : ℕ)
    (V : Fragment (Fin (0 + (n + 1)) ⊕ Fin ((n + 1) + 0))) :
    Fragment (Fin (0 + n) ⊕ Fin (n + 0)) :=
  (V.gluePair (cutL n) (cutR n) (cutL_ne_cutR n)).relabel
    (interfaceStepEquiv 0 n 0)

/-! ## The data a subset carries, and its summand

RS21 chooses an Eulerian orientation and a compatible local pairing
for each Eulerian subset; the flag model's counterpart is a
transition system with an orientation.  A family of those — one per
good subset — is what the interface recursion pushes forward, and the
summand it names is RS21's `s_h`, with no chord sign in it.
-/

section DataFamily

variable {L : Type}

/-- **A choice of transition system and orientation at every good
subset.** -/
def DataFamily [LinearOrder L] (V : Fragment L) : Type :=
  ∀ (s : Finset V.Flag) (hc : ∀ f ∈ s, V.pairing f ∈ s),
    (EdgeSubset.mk s hc).Eulerian →
    Nonempty (EdgeSubset.mk s hc).CanonData →
      Σ κ : (EdgeSubset.mk s hc).RelTransitionSystem, κ.Orientation

end DataFamily

/-! ## The data pushed back across one glue

The dispatch reads the base's summand at the *unglued* data, and an
orientation only ever ungloues — building one across a glue is step 1
again.  So the choice is made at the glued fragment and pushed back,
which is the direction this construction runs.
-/

section UnglueData

variable {L : Type}

open Classical in
/-- **The glued fragment's data, read on the base.**  At a subset
whose drop is closed under the rewire the base's data are the unglue
of the glued fragment's; elsewhere any choice serves, the summand
vanishing there. -/
noncomputable def unglueDataOpen
    [LinearOrder L] {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hopen : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j)
    (𝒟' : DataFamily (V.gluePairOpen i j hij hopen)) : DataFamily V :=
  fun s hc hE hne =>
    if hag : ∀ f ∈ V.dropSubset i j s,
        (V.gluePairOpen i j hij hopen).pairing f
          ∈ V.dropSubset i j s then
      have hlift : liftSubsetOpen hopen (V.dropSubset i j s) = s :=
        liftSubsetOpen_dropSubset hij hopen s hc
      have hcL : ∀ f ∈ liftSubsetOpen hopen
          (V.dropSubset i j s),
          V.pairing f ∈ liftSubsetOpen hopen
            (V.dropSubset i j s) := by
        rw [hlift]; exact hc
      have hF : (EdgeSubset.mk (liftSubsetOpen hopen
            (V.dropSubset i j s)) hcL : EdgeSubset V)
          = EdgeSubset.mk s hc := EdgeSubset.ext hlift
      have hEL : (EdgeSubset.mk (liftSubsetOpen hopen
          (V.dropSubset i j s)) hcL : EdgeSubset V).Eulerian := by
        rw [hF]; exact hE
      have hneL : Nonempty (EdgeSubset.mk (liftSubsetOpen hopen
          (V.dropSubset i j s)) hcL : EdgeSubset V).CanonData := by
        rw [hF]; exact hne
      have hE' : (EdgeSubset.mk (V.dropSubset i j s) hag :
          EdgeSubset (V.gluePairOpen i j hij hopen)).Eulerian :=
        (eulerian_lift_open_iff hij hopen (V.dropSubset i j s) hag
          hcL).mp hEL
      have hne' : Nonempty (EdgeSubset.mk (V.dropSubset i j s) hag :
          EdgeSubset (V.gluePairOpen i j hij hopen)).CanonData :=
        nonempty_canonData_glueOpen hij hopen (V.dropSubset i j s)
          hag hcL hneL
      ⟨relOfEq hF (RelTransitionSystem.unglueOpen hij hopen
          (V.dropSubset i j s) hag hcL
          (𝒟' (V.dropSubset i j s) hag hE' hne').1),
        orientOfEq hF (unglueOrientationOpen hij hopen
          (V.dropSubset i j s) hag hcL
          (𝒟' (V.dropSubset i j s) hag hE' hne').1
          (𝒟' (V.dropSubset i j s) hag hE' hne').2)⟩
    else ⟨(Classical.choice hne).1, (Classical.choice hne).2.val⟩

open Classical in
/-- **The unglued data at an open cut, evaluated.**  As in the closed
case the drop is abstracted, so that the dependent proofs the
definition carries can be substituted rather than rewritten. -/
theorem unglueDataOpen_apply
    [LinearOrder L] {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hopen : V.pairing (V.boundaryFlag i) ≠ V.boundaryFlag j)
    (𝒟' : DataFamily (V.gluePairOpen i j hij hopen))
    (s : Finset V.Flag) (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc : EdgeSubset V).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc : EdgeSubset V).CanonData)
    (t : Finset (SurvivingFlag V i j))
    (hdrop : V.dropSubset i j s = t)
    (hct : ∀ f ∈ t, (V.gluePairOpen i j hij hopen).pairing f ∈ t)
    (hcL : ∀ f ∈ liftSubsetOpen hopen t,
      V.pairing f ∈ liftSubsetOpen hopen t)
    (hF : (EdgeSubset.mk (liftSubsetOpen hopen t) hcL :
        EdgeSubset V) = EdgeSubset.mk s hc)
    (hEt : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairOpen i j hij hopen)).Eulerian)
    (hnet : Nonempty (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairOpen i j hij hopen)).CanonData) :
    unglueDataOpen hij hopen 𝒟' s hc hE hne
      = ⟨relOfEq hF (RelTransitionSystem.unglueOpen hij hopen t hct
            hcL (𝒟' t hct hEt hnet).1),
          orientOfEq hF (unglueOrientationOpen hij hopen t hct hcL
            (𝒟' t hct hEt hnet).1 (𝒟' t hct hEt hnet).2)⟩ := by
  subst hdrop
  unfold unglueDataOpen
  rw [dite_eq_left hct]

end UnglueData

section UnglueDataClosed

variable {L : Type}

/-- A closed glue does not change any vertex's degree, so the lift is
Eulerian exactly when the glued subset is. -/
theorem eulerian_liftClosed_iff' {V : Fragment L} {i : L} {j : L}
    (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
    (b : Bool)
    (s' : Finset (SurvivingFlag V i j))
    (hc' : ∀ f ∈ s', (V.gluePairClosed i j hclosed).pairing f ∈ s')
    (hc : ∀ f ∈ liftSubsetClosed s' b,
      V.pairing f ∈ liftSubsetClosed s' b) :
    (EdgeSubset.mk (liftSubsetClosed s' b) hc : EdgeSubset V).Eulerian
      ↔ (EdgeSubset.mk s' hc' :
          EdgeSubset (V.gluePairClosed i j hclosed)).Eulerian := by
  have hdeg : ∀ v : V.Vertex,
      (EdgeSubset.mk (liftSubsetClosed s' b) hc :
          EdgeSubset V).deg v
        = (EdgeSubset.mk s' hc' :
            EdgeSubset (V.gluePairClosed i j hclosed)).deg v :=
    fun v => deg_liftSubsetClosed_eq s' b v
  constructor <;> intro hE v
  · rw [← hdeg v]; exact hE v
  · rw [hdeg v]; exact hE v

open Classical in
/-- **The glued fragment's data at a closed cut, read on the base.**
Here no agreement is needed: a closed subset's drop is always closed
under the glued pairing, the two cut flags being partners. -/
noncomputable def unglueDataClosed
    [LinearOrder L] {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
    (𝒟' : DataFamily (V.gluePairClosed i j hclosed)) : DataFamily V :=
  fun s hc hE hne =>
    have hc' : ∀ f ∈ V.dropSubset i j s,
        (V.gluePairClosed i j hclosed).pairing f
          ∈ V.dropSubset i j s :=
      dropSubset_pairing_closed_of_closed hclosed s hc
    have hlift : liftSubsetClosed (V.dropSubset i j s)
        (decide (V.boundaryFlag i ∈ s)) = s :=
      liftSubsetClosed_dropSubset hij hclosed s hc
    have hcL : ∀ f ∈ liftSubsetClosed (V.dropSubset i j s)
        (decide (V.boundaryFlag i ∈ s)),
        V.pairing f ∈ liftSubsetClosed (V.dropSubset i j s)
          (decide (V.boundaryFlag i ∈ s)) := by
      rw [hlift]; exact hc
    have hF : (EdgeSubset.mk (liftSubsetClosed (V.dropSubset i j s)
          (decide (V.boundaryFlag i ∈ s))) hcL : EdgeSubset V)
        = EdgeSubset.mk s hc := EdgeSubset.ext hlift
    have hEL : (EdgeSubset.mk (liftSubsetClosed (V.dropSubset i j s)
        (decide (V.boundaryFlag i ∈ s))) hcL :
          EdgeSubset V).Eulerian := by
      rw [hF]; exact hE
    have hneL : Nonempty (EdgeSubset.mk
        (liftSubsetClosed (V.dropSubset i j s)
          (decide (V.boundaryFlag i ∈ s))) hcL :
        EdgeSubset V).CanonData := by
      rw [hF]; exact hne
    have hE' : (EdgeSubset.mk (V.dropSubset i j s) hc' :
        EdgeSubset (V.gluePairClosed i j hclosed)).Eulerian :=
      (eulerian_liftClosed_iff' hclosed _ (V.dropSubset i j s) hc'
        hcL).mp hEL
    have hne' : Nonempty (EdgeSubset.mk (V.dropSubset i j s) hc' :
        EdgeSubset (V.gluePairClosed i j hclosed)).CanonData :=
      nonempty_canonData_glueClosed hclosed (V.dropSubset i j s) hc' _
        hcL hneL
    ⟨relOfEq hF (RelTransitionSystem.unglueClosed hclosed _
        (V.dropSubset i j s) hc' hcL
        (𝒟' (V.dropSubset i j s) hc' hE' hne').1),
      orientOfEq hF (unglueOrientationClosed hclosed _
        (V.dropSubset i j s) hc' hcL
        (𝒟' (V.dropSubset i j s) hc' hE' hne').1
        (𝒟' (V.dropSubset i j s) hc' hE' hne').2)⟩

open Classical in
/-- **The unglued data, evaluated.**  The drop and the bit are
abstracted so that the dependent proofs the definition carries can be
substituted rather than rewritten: rewriting them in place is not
type correct, every one of them mentioning the drop. -/
theorem unglueDataClosed_apply
    [LinearOrder L] {V : Fragment L} {i : L} {j : L} (hij : i ≠ j)
    (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
    (𝒟' : DataFamily (V.gluePairClosed i j hclosed))
    (s : Finset V.Flag) (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc : EdgeSubset V).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc : EdgeSubset V).CanonData)
    (t : Finset (SurvivingFlag V i j)) (b : Bool)
    (hdrop : V.dropSubset i j s = t)
    (hb : decide (V.boundaryFlag i ∈ s) = b)
    (hct : ∀ f ∈ t, (V.gluePairClosed i j hclosed).pairing f ∈ t)
    (hcL : ∀ f ∈ liftSubsetClosed t b,
      V.pairing f ∈ liftSubsetClosed t b)
    (hF : (EdgeSubset.mk (liftSubsetClosed t b) hcL : EdgeSubset V)
      = EdgeSubset.mk s hc)
    (hEt : (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).Eulerian)
    (hnet : Nonempty (EdgeSubset.mk t hct :
      EdgeSubset (V.gluePairClosed i j hclosed)).CanonData) :
    unglueDataClosed hij hclosed 𝒟' s hc hE hne
      = ⟨relOfEq hF (RelTransitionSystem.unglueClosed hclosed b t hct
            hcL (𝒟' t hct hEt hnet).1),
          orientOfEq hF (unglueOrientationClosed hclosed b t hct hcL
            (𝒟' t hct hEt hnet).1 (𝒟' t hct hEt hnet).2)⟩ := by
  subst hdrop
  subst hb
  rfl

end UnglueDataClosed

end EdgeSubset

end RS
