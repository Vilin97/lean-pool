/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.ThroughValue

/-!
# The gluing-splitting interface

The through-independence input (choice elimination for the
corrected constrained value) and the single-pair gluing
decomposition, stated as named interfaces: gluing two boundary
labels decomposes the corrected state-constrained value as a state
sum over the glued interface, weighted by the through-state factor.
The unsigned through-independence is refuted in
`ThroughIndCFalse.lean`; what the development uses in its place is
the signed path-canonical value of `PathCanon.lean`, whose
within-pairing independence is `PropThreeOpen.lean`.
-/

@[expose] public section

namespace RS

/-- Extension of a boundary state on the surviving labels to the
full label type, prescribing the two glued ends. -/
noncomputable def GenBoundaryState.extendPair {k ℓ : ℕ} {α : Type}
    (i j : α)
    (st : GenBoundaryState k ℓ (Fragment.SurvivingLabel α i j))
    (c c' : Fin k ⊕ Fin (2 * ℓ)) : GenBoundaryState k ℓ α :=
  fun a =>
    letI := Classical.dec (a = i)
    letI := Classical.dec (a = j)
    if hi : a = i then c
    else if hj : a = j then c'
    else st ⟨a, hi, hj⟩

end RS
