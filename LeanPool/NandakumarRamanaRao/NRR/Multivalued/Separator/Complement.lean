/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Separator.Basic

/-!
# Complement data for a prescribed top--bottom carrier

This module separates the closedness of a proposed carrier from the topological assertion that its
complement has lower and upper components joining the two endpoint boundaries.  It is useful when
the carrier is obtained independently as the projection of a compact zero set: compactness proves
closedness, while a cobordism or intersection-number argument supplies the complement data.
-/

namespace NRR

/-- Complement-separation data for a prescribed carrier in `X × SignedInterval`.

Unlike `TopBottomSeparator`, closedness is not a field: it can be supplied afterwards from the
construction of the carrier. -/
structure TopBottomComplement
    (X : Type*) [TopologicalSpace X]
    (carrier : Set (X × SignedInterval)) where
  /-- The open lower region of the complement. -/
  lower : Set (X × SignedInterval)
  /-- The open upper region of the complement. -/
  upper : Set (X × SignedInterval)
  /-- The lower region is open. -/
  isOpen_lower : IsOpen lower
  /-- The upper region is open. -/
  isOpen_upper : IsOpen upper
  /-- The two regions are disjoint. -/
  disjoint_lower_upper : Disjoint lower upper
  /-- The complement of the prescribed carrier is exactly the union of the two regions. -/
  compl_eq : carrierᶜ = lower ∪ upper
  /-- The bottom boundary lies in the lower region. -/
  bottom_subset_lower : signedBottom X ⊆ lower
  /-- The top boundary lies in the upper region. -/
  top_subset_upper : signedTop X ⊆ upper

namespace TopBottomComplement

variable {X : Type*} [TopologicalSpace X]
variable {carrier : Set (X × SignedInterval)}

/-- Add a closedness proof to complement data, obtaining a top--bottom separator. -/
def toSeparator
    (D : TopBottomComplement X carrier)
    (hcarrier : IsClosed carrier) :
    TopBottomSeparator X where
  carrier := carrier
  isClosed_carrier := hcarrier
  lower := D.lower
  upper := D.upper
  isOpen_lower := D.isOpen_lower
  isOpen_upper := D.isOpen_upper
  disjoint_lower_upper := D.disjoint_lower_upper
  compl_eq := D.compl_eq
  bottom_subset_lower := D.bottom_subset_lower
  top_subset_upper := D.top_subset_upper

@[simp] theorem toSeparator_carrier
    (D : TopBottomComplement X carrier)
    (hcarrier : IsClosed carrier) :
    (D.toSeparator hcarrier).carrier = carrier :=
  rfl

@[simp] theorem toSeparator_lower
    (D : TopBottomComplement X carrier)
    (hcarrier : IsClosed carrier) :
    (D.toSeparator hcarrier).lower = D.lower :=
  rfl

@[simp] theorem toSeparator_upper
    (D : TopBottomComplement X carrier)
    (hcarrier : IsClosed carrier) :
    (D.toSeparator hcarrier).upper = D.upper :=
  rfl

end TopBottomComplement

end NRR
