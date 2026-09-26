/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.BundleClose

/-!
# The star trace identity

The accompanying paper's (★): the trace of the star union is the parameter
value of the closed fragment.  Closing the star union against the
strand bundle self-glues its straight matching
(`pairCloseStrandBundle`), and regluing the straight matching in
the star union restores the fragment (`starUnion_reglue`).  On Hom
classes: the descended trace of the star-union class is the value.
-/

@[expose] public section

namespace RS

/-- The star union reassembles under the bundle closure. -/
noncomputable def starUnionPairClose (W : ClosedFragment) :
    (pairClose (starUnion W) (strandBundle (edgeCount W))).Equiv
      W := by
  have E := (starUnion_reglue W).some
  refine (pairCloseStrandBundle (edgeCount W)
    (starUnion W)).trans ?_
  refine (Fragment.Equiv.relabelCongr
    ((Fragment.glueListProofIrrel (starUnion W)
      (matchPairs (edgeCount W)) _ (matchPairs_wf_star W)).trans
      E) _).trans ?_
  refine (Fragment.Equiv.relabelTrans W _ _).trans ?_
  exact (Fragment.Equiv.relabelEq W
    (_root_.Equiv.ext (fun i => i.elim0))).trans
    (Fragment.Equiv.relabelRefl W)

end RS
