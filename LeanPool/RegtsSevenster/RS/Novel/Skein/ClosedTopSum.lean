/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.ColourRecursion

/-!
# The composition's own sum

At the composition there are no labels left: the through-edge product
is one and the agreement is vacuous, so the flag model's summand is
RS21's colouring sum times the circuit sign.  This file names that
sign as a weight on the composition's subsets and reads the
constrained partition value as the weighted sum the iteration
carries.
-/

namespace RS

namespace EdgeSubset

open Fragment Classical

variable {L : Type}

open Classical in
/-- **The circuit sign of a subset**, off the family. -/
noncomputable def circuitWeight [LinearOrder L] {V : Fragment L}
    (𝒟 : DataFamily V)
    (s : Finset V.Flag) : ℂ :=
  if hc : ∀ f ∈ s, V.pairing f ∈ s then
    if hE : (EdgeSubset.mk s hc).Eulerian then
      if hne : Nonempty (EdgeSubset.mk s hc).CanonData then
        ((-1 : ℂ) ^ (𝒟 s hc hE hne).1.openCircuitCount)
      else 1
    else 1
  else 1

open Classical in
/-- At a good subset the circuit weight is the sign of the datum's
own circuit count. -/
theorem circuitWeight_pos [LinearOrder L] {V : Fragment L}
    (𝒟 : DataFamily V) {s : Finset V.Flag}
    (hc : ∀ f ∈ s, V.pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData) :
    circuitWeight 𝒟 s
      = ((-1 : ℂ) ^ (𝒟 s hc hE hne).1.openCircuitCount) := by
  unfold circuitWeight
  rw [dif_pos hc, dif_pos hE, dif_pos hne]

section ClosedTop

/-- At the composition the agreement is vacuous: there are no
labelled ends. -/
theorem throughAgree_isEmpty {V : Fragment L} [IsEmpty L]
    {k ℓ : ℕ} (F : EdgeSubset V)
    (st : GenBoundaryState k ℓ L)
    (hbnd : genBoundarySubsetMatches V F.flags st) :
    ThroughAgree F st hbnd := by
  intro f hb _
  exact absurd (Finset.mem_filter.mp hb).2 (fun hx =>
    isEmptyElim hx.choose)

/-- **At the composition the summand is the colouring sum, signed.**
-/
theorem throughSummand_eq_edgeSum [LinearOrder L] {V : Fragment L} [IsEmpty L]
    {k ℓ : ℕ} (F : EdgeSubset V)
    (h : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ L)
    (hbnd : genBoundarySubsetMatches V F.flags st)
    {κ : F.RelTransitionSystem} (o : κ.Orientation) (C : ℕ) :
    F.throughSummand h st hbnd o C
      = ((-1 : ℂ) ^ C) * F.edgeSum h st hbnd o := by
  rw [throughSummand_eq_vertexSum F h st hbnd o C,
    throughProduct_isEmpty F st, mul_one,
    ← edgeSum_eq_vertexSum F h st hbnd o
      (throughAgree_isEmpty F st hbnd)]

end ClosedTop

/-! ## The composition's value, read on the base

Putting the composition's own sum together with the iteration: the
constrained value of a composition is the base's summands, summed
over its subsets and over the interface colours, with the two
fragments' own free circles in front.  The composition's extra
circles — one for each closing cut — are exactly the iteration's
factor.
-/

/-- The lexicographic order on the interface's label type. -/
@[reducible] local instance baseOrder (n : ℕ) :
    LinearOrder (Fin (0 + n) ⊕ Fin (n + 0)) :=
  sumLexLinearOrder _ _

/-- The order the composition's own (empty) label type carries. -/
@[reducible] local instance topOrder :
    LinearOrder (Fin 0 ⊕ Fin 0) :=
  sumLexLinearOrder _ _

end EdgeSubset

end RS
