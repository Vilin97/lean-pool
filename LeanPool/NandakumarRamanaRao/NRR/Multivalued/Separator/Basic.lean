/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.Multivalued.SignedInterval

/-!
# `NRR.Multivalued.Separator.Basic` — top–bottom separator structure

A top–bottom separator over a space `X` is a closed carrier in `X × SignedInterval` whose
complement splits into two disjoint open regions, a `lower` region and an `upper` region, with the
bottom boundary `signedBottom X` (points with interval coordinate `-1`) contained in `lower` and the
top boundary `signedTop X` (points with interval coordinate `1`) contained in `upper`.

This is the abstract separation datum used in the Akopyan–Avvakumov–Karasev prime-refinement
argument. It records only the complement decomposition and the boundary placement; no signed
distance function is stored, and `X` is not required to be compact or metric.

The elementary side API derives, from these fields, that each side lies in the carrier complement,
that membership in a side excludes membership in the carrier, that a point outside the carrier lies
in exactly one side, and that the two boundaries never meet the carrier.
-/

@[expose] public section

namespace NRR

/-- The bottom boundary: points of `X × SignedInterval` whose interval coordinate is the left
endpoint `-1`. -/
def signedBottom (X : Type*) :
    Set (X × SignedInterval) :=
  {z | z.2 = SignedInterval.left}

/-- The top boundary: points of `X × SignedInterval` whose interval coordinate is the right
endpoint `1`. -/
def signedTop (X : Type*) :
    Set (X × SignedInterval) :=
  {z | z.2 = SignedInterval.right}

/-- A **top–bottom separator** over `X`: a closed carrier in `X × SignedInterval` whose complement
is partitioned into disjoint open `lower` and `upper` regions, with the bottom boundary in `lower`
and the top boundary in `upper`. -/
structure TopBottomSeparator
    (X : Type*) [TopologicalSpace X] where
  /-- The closed carrier: the graph of the separating multifunction. -/
  carrier : Set (X × SignedInterval)
  /-- The carrier is closed. -/
  isClosed_carrier : IsClosed carrier
  /-- The open lower region of the complement. -/
  lower : Set (X × SignedInterval)
  /-- The open upper region of the complement. -/
  upper : Set (X × SignedInterval)
  /-- The lower region is open. -/
  isOpen_lower : IsOpen lower
  /-- The upper region is open. -/
  isOpen_upper : IsOpen upper
  /-- The lower and upper regions are disjoint. -/
  disjoint_lower_upper : Disjoint lower upper
  /-- The complement of the carrier is the union of the two regions. -/
  compl_eq : carrierᶜ = lower ∪ upper
  /-- The bottom boundary lies in the lower region. -/
  bottom_subset_lower : signedBottom X ⊆ lower
  /-- The top boundary lies in the upper region. -/
  top_subset_upper : signedTop X ⊆ upper

namespace TopBottomSeparator

variable {X : Type*} [TopologicalSpace X]

/-- The lower region is contained in the carrier complement. -/
theorem lower_subset_compl
    (S : TopBottomSeparator X) :
    S.lower ⊆ S.carrierᶜ := by
  rw [S.compl_eq]
  exact Set.subset_union_left

/-- The upper region is contained in the carrier complement. -/
theorem upper_subset_compl
    (S : TopBottomSeparator X) :
    S.upper ⊆ S.carrierᶜ := by
  rw [S.compl_eq]
  exact Set.subset_union_right

/-- A point of the lower region is not in the carrier. -/
theorem not_mem_carrier_of_mem_lower
    (S : TopBottomSeparator X) {z}
    (hz : z ∈ S.lower) :
    z ∉ S.carrier :=
  S.lower_subset_compl hz

/-- A point of the upper region is not in the carrier. -/
theorem not_mem_carrier_of_mem_upper
    (S : TopBottomSeparator X) {z}
    (hz : z ∈ S.upper) :
    z ∉ S.carrier :=
  S.upper_subset_compl hz

/-- A point outside the carrier lies in the lower or the upper region. -/
theorem mem_lower_or_upper_of_not_mem
    (S : TopBottomSeparator X) {z}
    (hz : z ∉ S.carrier) :
    z ∈ S.lower ∨ z ∈ S.upper := by
  have : z ∈ S.carrierᶜ := hz
  rw [S.compl_eq] at this
  exact this

/-- For a point outside the carrier, being in the lower region is equivalent to not being in the
upper region. -/
theorem mem_lower_iff_not_mem_upper_of_not_mem
    (S : TopBottomSeparator X) {z}
    (hz : z ∉ S.carrier) :
    (z ∈ S.lower ↔ z ∉ S.upper) := by
  constructor
  · intro hl hu
    exact S.disjoint_lower_upper.le_bot ⟨hl, hu⟩
  · intro hu
    rcases S.mem_lower_or_upper_of_not_mem hz with hl | hu'
    · exact hl
    · exact absurd hu' hu

/-- The bottom boundary point at `x` lies in the lower region. -/
theorem bottom_mem_lower
    (S : TopBottomSeparator X) (x : X) :
    (x, SignedInterval.left) ∈ S.lower :=
  S.bottom_subset_lower rfl

/-- The top boundary point at `x` lies in the upper region. -/
theorem top_mem_upper
    (S : TopBottomSeparator X) (x : X) :
    (x, SignedInterval.right) ∈ S.upper :=
  S.top_subset_upper rfl

/-- The bottom boundary point at `x` is not in the carrier. -/
theorem bottom_not_mem_carrier
    (S : TopBottomSeparator X) (x : X) :
    (x, SignedInterval.left) ∉ S.carrier :=
  S.not_mem_carrier_of_mem_lower (S.bottom_mem_lower x)

/-- The top boundary point at `x` is not in the carrier. -/
theorem top_not_mem_carrier
    (S : TopBottomSeparator X) (x : X) :
    (x, SignedInterval.right) ∉ S.carrier :=
  S.not_mem_carrier_of_mem_upper (S.top_mem_upper x)

end TopBottomSeparator

end NRR
