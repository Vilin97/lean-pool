/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.ThroughValue

/-!
# The vertex sum

RS21's tensor is built from a sum over colourings extending the
boundary data of a product of the functional's vertex values:

    Σ_{ψ ∼ χ₀, φ ∼ χ₁} ∏_{v ∈ V′(F)} h_v( … ).

That sum is named here, and the mixed partition function's own
summand is shown to be it, times the circuit sign and the
through-edge product.  Naming it separates the part of the summand
that is RS21's from the part the flag model adds — the through-edge
product, which the graph model instead carries inside the boundary
vectors.
-/

namespace RS

namespace EdgeSubset

open Classical

variable {α : Type}

/-- **The vertex sum**: over colourings extending the boundary
state, the product of the functional's vertex values. -/
noncomputable def vertexSum {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ : F.RelTransitionSystem} (o : κ.Orientation) : ℂ :=
  ∑ ψ : F.EvenColouring k,
    if genEvenBoundaryMatch F st hbnd ψ then
      ∑ φ : F.CoreOddColouring ℓ,
        if F.coreOddBoundaryMatch st φ then
          ∏ v : W.Vertex,
            ((F.coreOddSignAt o φ v : ℂ) *
              h.evalOdd (F.evenColoursAt ψ v)
                (F.coreOddListAt o φ v))
        else 0
    else 0

/-- **The summand is the vertex sum, weighted.**  The circuit sign
and the through-edge product are the flag model's own factors; what
is left is RS21's sum over colourings. -/
theorem throughSummand_eq_vertexSum [LinearOrder α] {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ : F.RelTransitionSystem} (o : κ.Orientation) (c : ℕ) :
    F.throughSummand h st hbnd o c
      = ((-1 : ℂ) ^ c) * F.throughProduct st
        * F.vertexSum h st hbnd o :=
  rfl

end EdgeSubset

end RS
