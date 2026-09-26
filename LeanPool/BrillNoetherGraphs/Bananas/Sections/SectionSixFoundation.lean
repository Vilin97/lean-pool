/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.ChainGluing
public import LeanPool.BrillNoetherGraphs.Utilities.Transmission.DemazureFactorization

/-!
# Unconditional transmission gluing for Section 6

`ChainGluing.lean` predates the proof of bounded Demazure factorizations and
therefore exposes its chain result with an explicit factorization hypothesis.
`DemazureFactorization.lean` now proves precisely that input for all
nonnegative genus budgets.  This file records the resulting unconditional
version, which is the transmission-existence backbone of the Section 6 chain
arguments.
-/

@[expose] public section

namespace Bananas

open Utilities

universe u

/-- The outer marks of an iterated vertex-gluing chain have transmission
existence whenever every factor does.  No additional Demazure-factorization
hypothesis remains: it is discharged by
`transmissionExistence_vertexWedge_opposite`. -/
theorem chainTransmissionExistence_unconditional
    (M : MarkedGraph.{u}) (L : List MarkedGraph.{u})
    (hM : TransmissionExistence M.graph M.left M.right)
    (hL : ∀ N ∈ L, TransmissionExistence N.graph N.left N.right)
    (hGenus : ∀ N ∈ M :: L, 0 ≤ genus N.graph) :
    TransmissionExistence (M.chain L).graph (M.chain L).left
      (M.chain L).right := by
  induction L generalizing M with
  | nil => simpa using hM
  | cons N rest ih =>
      rw [MarkedGraph.chain_cons]
      apply ih (M.wedge N)
      · exact transmissionExistence_vertexWedge_opposite
          M.graph N.graph M.right N.left M.left N.right hM
          (hL N (by simp)) (hGenus M (by simp)) (hGenus N (by simp))
      · intro P hP
        exact hL P (by simp [hP])
      · intro P hP
        simp only [List.mem_cons] at hP
        rcases hP with hP | hP
        · subst P
          rw [MarkedGraph.genus_wedge]
          exact add_nonneg (hGenus M (by simp)) (hGenus N (by simp))
        · exact hGenus P (by simp [hP])

/-- The once-marked existence consequence of the unconditional chain gluing.
This is the currently formal transmission counterpart of the first conclusion
of the paper's chain theorem; the remaining Section 6 work is to prove the
paper's *upper* Weierstrass-size Brill--Noether generality conclusions. -/
theorem onceMarkedBNExists_chain_unconditional
    (M : MarkedGraph.{u}) (L : List MarkedGraph.{u})
    (hM : TransmissionExistence M.graph M.left M.right)
    (hL : ∀ N ∈ L, TransmissionExistence N.graph N.left N.right)
    (hGenus : ∀ N ∈ M :: L, 0 ≤ genus N.graph)
    (hconn : graphConnected (M.chain L).graph)
    (tau : AspPerm) (lambda : YoungDiagram)
    (hProfile : GrassmannianPartitionProfile tau lambda)
    (hFinite : FiniteTransmissionPerm tau)
    (hLength : ((invSet tau).ncard : ℤ) ≤ genus (M.chain L).graph) :
    OnceMarkedBNExists (M.chain L).graph (M.chain L).left lambda := by
  refine (transmissionExists_iff_onceMarkedBNExists hconn (M.chain L).left
    (M.chain L).right tau lambda hProfile).mp ?_
  exact chainTransmissionExistence_unconditional M L hM hL hGenus
    tau hFinite hLength

end Bananas
