/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.PairedAssembly
import LeanPool.RegtsSevenster.RS.Novel.Skein.RelabelChords

/-!
# Proposition 3 for open fragments

The paired step is a theorem (`pairedLedger`), so the whole chain
follows with no hypothesis: the pairing-preserving move ledger, the
within-pairing independence of the signed canonical value, and the
well-definedness of the value over chord diagrams.  With
independence across pairings refuted (`not_throughIndependenceC`),
this is the open-sector Proposition 3 in its exact form: the
constrained value is a function of the boundary pairing, and of
nothing else.
-/

namespace RS



/-- The paired step in value form, unconditionally. -/
theorem pairedValueLedger : PairedValueLedger :=
  EdgeSubset.pairedLedger_iff_value.mp pairedLedger

namespace EdgeSubset

variable {α : Type}

/-- Signed values agree across equal chord diagrams,
unconditionally. -/
theorem signedValueAt_of_labelChords_eq_pairing
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {k ℓ : ℕ}
    (hM : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ κ' : F.RelTransitionSystem}
    (h : labelChords κ = labelChords κ') :
    F.signedValueAt hM st hbnd κ =
      F.signedValueAt hM st hbnd κ' :=
  signedValueAt_of_labelChords_eq pairedValueLedger
    hM st hbnd h

end EdgeSubset

end RS
