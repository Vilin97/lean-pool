/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.ConverseFamily
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ConverseGram

/-!
# The super-Gram identity

The closing display of the proof of RS21's Theorem 6, in the form
the converse consumes: the composition's mixed partition function
is the superform pairing of the two fragments' tensors.  The base
sum the composition's own total equals is
`EdgeSubset.baseSumBitsOf_all` of `ConverseFamily.lean`, read with
the bits each subset itself determines, and the tensor side of that
sum is `EdgeSubset.base_sum_eq_superForm_pairing_bitsOf`.
-/

@[expose] public section

namespace RS



namespace EdgeSubset

/-- The order the base's labels carry. -/
@[reducible] local instance idBaseOrder (n : ℕ) :
    LinearOrder (Fin (0 + n) ⊕ Fin (n + 0)) :=
  sumLexLinearOrder _ _

/-- The order the composition's own label type carries. -/
@[reducible] local instance idTopOrder :
    LinearOrder (Fin 0 ⊕ Fin 0) :=
  sumLexLinearOrder _ _

open Classical in
/-- **The closure, read on the base with each subset's own bits.**
The composition's own value is the sum, over the base's subsets, of
the ledger-weighted term the pair family gives — each subset read
with the bits it itself determines, which is the reading at which a
closing cut's two lifts are each other's. -/
def BaseSumIsClosure : Prop :=
  ∀ {k ℓ : ℕ} (h : MixedFunctional k ℓ) (t : ℕ)
    (F G : Fragment (Fin t)),
    mixedPartition h (pairClose F G)
      = ((k : ℂ) - 2 * ℓ) ^ (closeBase F G).circles *
        ∑ s : Finset (closeBase F G).Flag,
          ∑ x : GenBoundaryState k ℓ (Fin t),
            circuitWeight (liftData t (closeBase F G)
                (bitsOf t (closeBase F G) s) (pairFamily h t F G))
                (imageOf t (closeBase F G) s)
              * edgeTermAt h (pairFamily h t F G) (diagOf t x) s
                (carried t (closeBase F G) s)

open Classical in
/-- **The base sum from the bit-varying sum.**  The composition's own
total is the base sum read with each subset's own bits, once that sum
is known; the round trip then replaces the pushed lift by the pair
family itself. -/
theorem baseSumIsClosure_of_baseSumBitsOf
    (H : ∀ {k ℓ : ℕ} (h : MixedFunctional k ℓ) (t : ℕ)
      (F G : Fragment (Fin t)),
      BaseSumBitsOf h t (closeBase F G) (pairFamily h t F G) 0) :
    BaseSumIsClosure := by
  intro k ℓ h t F G
  rw [mixedPartition_pairClose h t F G,
    throughMixedPartitionC_eq_edgeTermAt_any h emptyState
      (liftData t (closeBase F G) (fun _ => false)
        (pairFamily h t F G)),
    circles_glueInterface t (closeBase F G), pow_add, mul_assoc]
  refine congrArg (fun z => ((k : ℂ) - 2 * ℓ) ^
    (closeBase F G).circles * z) ?_
  refine (H h t F G).trans (Finset.sum_congr rfl (fun s _ =>
    Finset.sum_congr rfl (fun x _ => ?_)))
  refine congrArg (fun z => circuitWeight (liftData t (closeBase F G)
      (bitsOf t (closeBase F G) s) (pairFamily h t F G))
      (imageOf t (closeBase F G) s) * z) ?_
  refine Eq.trans (edgeTermAt_pushData_liftData_all_bitsOf h t
    (closeBase F G) (pairFamily h t F G)
    (fun s' => aligned_of_baseDirections t (closeBase F G) _ _
      (baseDirections_pairFamily h t F G)) x s
    (0 + carried t (closeBase F G) s)) ?_
  exact congrArg (fun c => edgeTermAt h (pairFamily h t F G)
    (diagOf t x) s c) (zero_add (carried t (closeBase F G) s))

open Classical in
/-- **The closing identity of RS21's Theorem 6, from the base
sum.**  The closure's value is the superform pairing of the two
fragment tensors, at every interface. -/
theorem mixedPartition_pairClose_eq_superForm_of_baseSum
    (H : BaseSumIsClosure) {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (t : ℕ) (F G : Fragment (Fin t)) :
    mixedPartition h (pairClose F G)
      = ((k : ℂ) - 2 * ℓ) ^ (closeBase F G).circles *
        ∑ x : GenBoundaryState k ℓ (Fin t),
          ∑ y : GenBoundaryState k ℓ (Fin t),
            superForm t x y
              * (∑ s₁ : Finset F.Flag, tensorTermAt F h s₁ x)
              * (∑ s₂ : Finset G.Flag, tensorTermAt G h s₂ y) :=
  (H h t F G).trans (congrArg (fun z => _ * z)
    (base_sum_eq_superForm_pairing_bitsOf h t F G))

open Classical in
/-- **THE SUPER-GRAM IDENTITY FROM THE BASE SUM.**  With the base
sum, the closing identity of RS21's Theorem 6 holds at every
interface, and with it the converse:
the closure's value is the superform pairing of the two fragments'
tensors. -/
theorem superGramIdentity_of_baseSum (H : BaseSumIsClosure) :
    SuperGramIdentity := by
  intro k ℓ h t F G
  change mixedPartition h (pairClose F G) = _
  rw [mixedPartition_pairClose_eq_superForm_of_baseSum H h t F G,
    circles_closeBase, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  unfold fragmentTensor
  rw [tensorSum_eq_sum, tensorSum_eq_sum, pow_add]
  ring

open Classical in
/-- **THE BASE SUM IS THE CLOSURE.**  The composition's own value is
the base sum read with each subset's own bits — the reading at which
a closing cut's two lifts are each other's.  Nothing is assumed: the
summand does not read the lift's bits at all
(`summandSum_bits_indep`). -/
theorem baseSumIsClosure_all : BaseSumIsClosure :=
  baseSumIsClosure_of_baseSumBitsOf
    (fun h t F G => baseSumBitsOf_all h t (closeBase F G)
      (pairFamily h t F G) 0)

open Classical in
/-- **THE SUPER-GRAM IDENTITY.**  The closing display of the proof
of RS21's Theorem 6: the closure of two fragments, evaluated by
the mixed partition function, is the super form of their two
tensors — at every interface, closing cuts included. -/
theorem superGramIdentity : SuperGramIdentity :=
  superGramIdentity_of_baseSum baseSumIsClosure_all

open Classical in
/-- **THE REGTS–SEVENSTER CONVERSE.**  Every mixed partition function
is an edge-rank-bounded parameter. -/
theorem regtsSevensterConverse : RegtsSevensterConverseStatement :=
  converse_of_superGramIdentity superGramIdentity

end EdgeSubset

end RS
