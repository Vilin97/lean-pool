/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Separator.SignedDistance
import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Operations

/-!
# `NRR.Multivalued.Separator.ToNiceMV` — separators as nice multivalued functions

Every top–bottom separator `S` over a nonempty metric base `X` gives a nice multivalued function
`S.toNiceMV`, whose scalar observable is the signed distance to the carrier. Its zero set is
exactly the carrier: the graph of the separating multifunction is recovered as the zero set of a
single continuous scalar function, with the required strict endpoint signs coming from the signed
distance being negative at the bottom boundary and positive at the top boundary.

Separators also pull back along a continuous base map `f : Y → X` through the product map
`(y, t) ↦ (f y, t)`: carrier, lower, and upper regions are pulled back by preimage, which preserves
closedness, openness, disjointness, complements, and the boundary placement. The pulled-back
separator's nice multivalued function has the same zero set as the pullback of the original nice
multivalued function, even though the two signed distances are computed in different product metrics
and need not agree pointwise.
-/

namespace NRR

namespace TopBottomSeparator

section ToNiceMV

variable {X : Type*} [MetricSpace X] [Nonempty X]

/-- The nice multivalued function attached to a top–bottom separator: its scalar observable is the
signed distance to the carrier, so its zero set is exactly the carrier. -/
noncomputable def toNiceMV
    (S : TopBottomSeparator X) :
    NiceMV X where
  evalMap := S.signedDistanceMap
  left_neg := S.signedDistance_left_neg
  right_pos := S.signedDistance_right_pos

theorem toNiceMV_eval
    (S : TopBottomSeparator X)
    (x : X) (t : SignedInterval) :
    S.toNiceMV.eval x t = S.signedDistance (x, t) :=
  rfl

theorem zero_toNiceMV_iff
    (S : TopBottomSeparator X)
    (x : X) (t : SignedInterval) :
    S.toNiceMV.Zero x t ↔ (x, t) ∈ S.carrier := by
  rw [NiceMV.zero_iff, toNiceMV_eval]
  exact S.signedDistance_eq_zero_iff (x, t)

theorem zeroSet_toNiceMV
    (S : TopBottomSeparator X) :
    S.toNiceMV.zeroSet = S.carrier := by
  ext z
  simp only [NiceMV.zeroSet, Set.mem_ofPred_eq, NiceMV.zero_iff, toNiceMV_eval]
  exact S.signedDistance_eq_zero_iff z

end ToNiceMV

section Pullback

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Pull back a top–bottom separator `S` on `X` along a continuous base map `f : Y → X` through the
product map `(y, t) ↦ (f y, t)`. Carrier, lower, and upper regions are pulled back by preimage. -/
def pullback
    (S : TopBottomSeparator X) (f : C(Y, X)) :
    TopBottomSeparator Y where
  carrier := (fun z : Y × SignedInterval => (f z.1, z.2)) ⁻¹' S.carrier
  isClosed_carrier :=
    S.isClosed_carrier.preimage ((f.continuous.comp continuous_fst).prodMk continuous_snd)
  lower := (fun z : Y × SignedInterval => (f z.1, z.2)) ⁻¹' S.lower
  upper := (fun z : Y × SignedInterval => (f z.1, z.2)) ⁻¹' S.upper
  isOpen_lower :=
    S.isOpen_lower.preimage ((f.continuous.comp continuous_fst).prodMk continuous_snd)
  isOpen_upper :=
    S.isOpen_upper.preimage ((f.continuous.comp continuous_fst).prodMk continuous_snd)
  disjoint_lower_upper := S.disjoint_lower_upper.preimage _
  compl_eq := by
    rw [← Set.preimage_compl, S.compl_eq, Set.preimage_union]
  bottom_subset_lower := fun z hz => S.bottom_subset_lower hz
  top_subset_upper := fun z hz => S.top_subset_upper hz

theorem pullback_carrier
    (S : TopBottomSeparator X) (f : C(Y, X)) :
    (S.pullback f).carrier =
      (fun z : Y × SignedInterval => (f z.1, z.2)) ⁻¹' S.carrier :=
  rfl

end Pullback

theorem pullback_toNiceMV_zeroSet
    {X Y : Type*}
    [MetricSpace X] [MetricSpace Y]
    [Nonempty X] [Nonempty Y]
    (S : TopBottomSeparator X) (f : C(Y, X)) :
    (S.pullback f).toNiceMV.zeroSet =
      (S.toNiceMV.pullback f).zeroSet := by
  rw [zeroSet_toNiceMV, pullback_carrier, NiceMV.pullback_zeroSet, zeroSet_toNiceMV]

end TopBottomSeparator

end NRR
