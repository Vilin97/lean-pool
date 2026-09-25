/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.EdgeColouring

/-!
# RS21's colouring sum

RS21 writes the tensor's colouring sum as

    Σ_{ψ ∼ χ₀, φ ∼ χ₁} ∏_{v ∈ V′(F)} h_v( … ),

where `ψ` colours the edges outside `H` and `φ` colours the edges of
`H` — one colour per edge, both of them constrained at the labelled
ends by `χ`.  That is the sum named here.

The flag model's `vertexSum` instead colours the *core* edges only,
leaving the through-edges to the through-edge product.  The two
agree exactly on the states whose two legs at a through-edge carry
one colour, and off those RS21's sum is empty: a colouring gives the
through-edge one colour and `φ ∼ χ₁` pins it at both ends.  So
RS21's sum is the flag model's, cut down to the agreeing states —
which is what the pairing of two tensors computes.
-/

@[expose] public section

namespace RS

namespace EdgeSubset



variable {α : Type}

open scoped Classical in
/-- **RS21's colouring sum** over the colourings of the whole
subset. -/
noncomputable def edgeSum {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ : F.RelTransitionSystem} (o : κ.Orientation) : ℂ :=
  ∑ ψ : F.EvenColouring k,
    if genEvenBoundaryMatch F st hbnd ψ then
      ∑ φ : F.EdgeOddColouring ℓ,
        if edgeOddBoundaryMatch F st φ then
          ∏ v : W.Vertex,
            ((F.coreOddSignAt o φ.core v : ℂ) *
              h.evalOdd (F.evenColoursAt ψ v)
                (F.coreOddListAt o φ.core v))
        else 0
    else 0

/-- **On an agreeing state RS21's sum is the flag model's.** -/
theorem edgeSum_eq_vertexSum {W : Fragment α}
    (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ : F.RelTransitionSystem} (o : κ.Orientation)
    (hag : ThroughAgree F st hbnd) :
    F.edgeSum h st hbnd o = F.vertexSum h st hbnd o := by
  unfold edgeSum vertexSum
  refine Finset.sum_congr rfl (fun ψ _ => ?_)
  by_cases hev : genEvenBoundaryMatch F st hbnd ψ
  · rw [ite_eq_left hev, ite_eq_left hev]
    exact sum_edgeOddColouring hbnd hag
      (fun φ' => ∏ v : W.Vertex,
        ((F.coreOddSignAt o φ' v : ℂ) *
          h.evalOdd (F.evenColoursAt ψ v)
            (F.coreOddListAt o φ' v)))
  · rw [ite_eq_right hev, ite_eq_right hev]

/-- **A disagreeing state is coloured by nothing.** -/
theorem edgeSum_eq_zero_of_not_throughAgree {W : Fragment α}
    (F : EdgeSubset W)
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ : F.RelTransitionSystem} (o : κ.Orientation)
    (hag : ¬ ThroughAgree F st hbnd) :
    F.edgeSum h st hbnd o = 0 := by
  unfold edgeSum
  refine Finset.sum_eq_zero (fun ψ _ => ?_)
  by_cases hev : genEvenBoundaryMatch F st hbnd ψ
  · rw [ite_eq_left hev]
    exact Finset.sum_eq_zero (fun φ _ => ite_eq_right (fun hφ =>
      hag (throughAgree_of_edgeOddBoundaryMatch hbnd hφ)))
  · rw [ite_eq_right hev]

end EdgeSubset

end RS
