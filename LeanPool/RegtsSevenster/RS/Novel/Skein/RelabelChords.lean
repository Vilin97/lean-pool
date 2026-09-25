/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.RelabelInvariance
public import LeanPool.RegtsSevenster.RS.Novel.Skein.FibreValue

/-!
# Chord diagrams transport along monotone relabels

The label chord diagram of a relabeled system is the image of the
original diagram under the order isomorphism, entrywise: the flags
and the path matching are untouched, the labels shift through `e`,
and `e` preserves the sorting.
-/

@[expose] public section

namespace RS



open EdgeSubset

variable {α β : Type}

/-- The boundary label shifts through the relabel. -/
theorem relabel_boundaryLabel
    [LinearOrder α] [LinearOrder β] (e : α ≃o β) {W : Fragment α}
    (F : EdgeSubset W) {b : W.Flag}
    (hb : b ∈ (F.relabelUp e.toEquiv).boundaryFlags)
    (hb' : b ∈ F.boundaryFlags) :
    (F.relabelUp e.toEquiv).boundaryLabel hb =
      e (F.boundaryLabel hb') :=
  boundaryLabel_eq_of_attach hb
    ((relabel_attach_inr_iff e.toEquiv b (F.boundaryLabel hb')).mpr
      (attach_boundaryLabel hb'))

end RS
