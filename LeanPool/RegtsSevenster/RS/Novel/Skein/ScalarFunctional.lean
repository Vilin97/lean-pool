/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.HomTraceNondegenerate

/-!
# The scalar functional

The descended trace at arity zero evaluates a closed fragment's
class to its parameter value: closing against the empty strand
bundle is the identity, so the arity-zero trace is evaluation
of `f` itself.  This is the numerical endpoint of the extraction:
every identity of Hom-classes at arity zero becomes an identity
of parameter values through this functional.
-/

@[expose] public section

namespace RS

variable {R : ℕ} (f : EdgeRankParameter R)

/-- Closing a closed fragment against the empty bundle is the
fragment. -/
noncomputable def pairCloseStrandBundleZero
    (W : Fragment (Fin (0 + 0))) :
    (pairClose W (strandBundle 0)).Equiv W := by
  refine (Fragment.composeCongr (Fragment.Equiv.refl _)
    ((Fragment.Equiv.relabelEq (strandBundle 0)
      (_root_.Equiv.ext (fun i => i.elim0))).trans
      (Fragment.Equiv.relabelRefl (strandBundle 0)))).trans ?_
  refine (composeStrandBundleRight 0 0 _).trans ?_
  exact (Fragment.Equiv.relabelEq W
    (_root_.Equiv.ext (fun i => i.elim0))).trans
    (Fragment.Equiv.relabelRefl W)

/-- **The scalar functional**: the arity-zero descended trace of
a closed fragment's class is its parameter value. -/
theorem traceMap_zero_ofFragment (W : Fragment (Fin (0 + 0))) :
    HomSpace.traceMap f.val 0
        (HomSpace.ofFragment f.val W) = f.val W := by
  rw [HomSpace.traceMap_ofFragment]
  exact f.iso_invariant _ _ (pairCloseStrandBundleZero W)

end RS
