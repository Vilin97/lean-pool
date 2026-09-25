/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.RSTensor
import LeanPool.RegtsSevenster.RS.StatementConverse

/-!
# The converse from a super-Gram factorization

The converse asks every mixed partition function to be an
edge-rank-bounded parameter.  The rank bound follows from writing the
connection pairing as the super form evaluated at vectors attached to
the two fragments, so the converse rests on one displayed identity:
the closure of two fragments, evaluated by the mixed partition
function, is the super form of their two tensors.  That identity is
`EdgeSubset.superGramIdentity` in `ConverseIdentity.lean`, and
the converse it gives is `regts_sevenster_converse` in
`RS/TheoremConverse.lean`.
-/

namespace RS



/-- **THE CONVERSE FROM A SUPER-GRAM FACTORIZATION**: a
state-indexed factorization of the connection pairing through the
super form bounds the edge rank, and with it the converse. -/
theorem converse_of_superGram
    (T : ∀ (k ℓ : ℕ), MixedFunctional k ℓ → ∀ t : ℕ,
      Fragment (Fin t) → GenBoundaryState k ℓ (Fin t) → ℂ)
    (hgram : ∀ (k ℓ : ℕ) (h : MixedFunctional k ℓ) (t : ℕ)
      (F G : Fragment (Fin t)),
      connectionPairing (fun W => mixedPartition h W) t F G
        = ∑ x : GenBoundaryState k ℓ (Fin t),
            ∑ y : GenBoundaryState k ℓ (Fin t),
              superForm t x y * T k ℓ h t F x * T k ℓ h t G y) :
    RegtsSevensterConverseStatement :=
  converseStatement_of_rank_bounded eulerianIndependence
    (fun k ℓ hf =>
      edgeRankBounded_of_superGram (T k ℓ hf) (hgram k ℓ hf))

/-! ### The fragment tensor, and the identity the converse rests on

A subset's canonical data carry a transition system, so choosing one
at every guarded subset is a pinned family with no further input.
The fragment's tensor is its pinned sum at that family, normalised
by the state's fourth root.  With the tensor fixed, the converse
rests on one closed identity.
-/

/-- **The fragment tensor**: RS21's `Σ_H t_h(F,H,ω_H,κ_H)`, with
the fragment's own free circles riding along.  The flag model
carries vertex-free loops the graph model has no room for, and the
partition function weights each by `k - 2ℓ`; the circles the closure
creates come out of the contraction instead. -/
noncomputable def fragmentTensor {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (t : ℕ) (F : Fragment (Fin t))
    (x : GenBoundaryState k ℓ (Fin t)) : ℂ :=
  ((k : ℂ) - 2 * ℓ) ^ F.circles * tensorSum F h x

/-- **The super-Gram identity** (statement): the closure of two
fragments, evaluated by the mixed partition function, is the super
form of their two tensors. -/
def SuperGramIdentity : Prop :=
  ∀ {k ℓ : ℕ} (h : MixedFunctional k ℓ) (t : ℕ)
    (F G : Fragment (Fin t)),
    connectionPairing (fun W => mixedPartition h W) t F G
      = ∑ x : GenBoundaryState k ℓ (Fin t),
          ∑ y : GenBoundaryState k ℓ (Fin t),
            superForm t x y * fragmentTensor h t F x
              * fragmentTensor h t G y

/-- **THE CONVERSE FROM THE SUPER-GRAM IDENTITY.** -/
theorem converse_of_superGramIdentity (H : SuperGramIdentity) :
    RegtsSevensterConverseStatement :=
  converse_of_superGram (fun _k _ℓ h t => fragmentTensor h t)
    (fun _k _ℓ h t F G => H h t F G)

end RS
