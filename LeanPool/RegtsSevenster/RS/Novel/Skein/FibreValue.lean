/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.LabelChords
import LeanPool.RegtsSevenster.RS.Novel.Skein.LedgerValue

/-!
# The fibre value: the open-sector value indexed by chord diagrams

The signed canonical value as a function of the boundary pairing's
chord diagram: choose any system realizing the diagram (with a
path-canonical orientation) and take its signed value.  Given the
paired step in value form, the choice is immaterial
(`signedValueAt_samePairing_of_value` through the faithfulness of
the diagram), and the fibre value evaluates at every realizing
system.  Independence holds *within* a chord diagram, not across
diagrams: `not_throughIndependenceC` exhibits two path-canonical
data with different boundary pairings whose signed values differ.
-/

namespace RS



variable {α : Type}

namespace EdgeSubset

/-- Two realizing systems of one diagram share the signed value
(the fibre form of the within-pairing independence). -/
theorem signedValueAt_of_labelChords_eq
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    (HPaired : PairedValueLedger) {k ℓ : ℕ}
    (hM : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ κ' : F.RelTransitionSystem}
    (h : labelChords κ = labelChords κ') :
    F.signedValueAt hM st hbnd κ =
      F.signedValueAt hM st hbnd κ' :=
  signedValueAt_samePairing_of_value HPaired hM st hbnd
    (samePairing_of_labelChords h)

open Classical in
/-- **The instantiation bridge**: the canonical choice value is the
signed value at the chosen system — the factorization interfaces
over choice values follow from their universal concrete-data forms
by instantiation. -/
theorem throughValueC_eq_signedValueAt
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {k ℓ : ℕ}
    (hM : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (hne : Nonempty F.CanonData) :
    F.throughValueC hM st hbnd =
      F.signedValueAt hM st hbnd (Classical.choice hne).1 := by
  rw [throughValueC, dite_eq_left hne,
    signedValueAt_eq hM st hbnd (Classical.choice hne).2.val
      (Classical.choice hne).2.prop]

end EdgeSubset

end RS
