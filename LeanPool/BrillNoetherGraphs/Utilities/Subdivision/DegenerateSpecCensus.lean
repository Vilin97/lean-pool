/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ContractionForestCensusGeneral
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateSeparator

/-!
# The `DegSpec` face datum, emitted by the contraction census

`Certificate/DegenerateSeparator.lean` and `Certificate/DegenerateRankOne.lean`
take `rep`, `rep_idem`, `rep_zero`, `rep_loopless`, `forest` — and, for the
interpolated layer, a `ZeroReach` witness — as **inputs** that a row supplies
by hand (see `Certificate/Examples/GenusFourCore100Face.lean`'s `faceRep`,
proved by five separate `decide`s). This file makes them **outputs** of the
generalized contraction census
(`Certificate/ContractionForestCensusGeneral.lean`): name the set of slots
that vanish at a point, check once that it is a forest with no semantic loop,
and every one of those five obligations — the four `DegSpec` fields plus the
`ZeroReach` witness the interpolated layer needs — falls out.

## The bridge, in one picture

A `Certificate m n p` fixes a core and a point `point : Fin m → ℤ` fixes a
length vector `certificate.segmentNat point : Fin p → ℕ`. Write
`zeroSlots certificate point` for the `Finset (Fin p)` of vanishing slots.
Then:

* `censusRep := ContractionForestCensusGeneral.compFold certificate.core
  (zeroSlots certificate point)` is a legal `DegSpec.rep`;
* `censusRep_idem` is `compFold_idem`, generically, no `decide`;
* `censusRep_zero` is `compFold_tail_eq_head_of_mem`, applied to slots in
  `zeroSlots`, which are exactly the ones membership needs;
* `censusRep_loopless` is `rep_loopless_of_not_isLoopy`, given the one
  census fact `¬ IsLoopy certificate.core (zeroSlots certificate point)`;
* `censusRep_forest` is `forest_image_add_card_eq`, given the one census fact
  `IsForest certificate.core (zeroSlots certificate point)`; and
* `censusRep_zeroReach` upgrades `reachIn_self_compFold` — the *same*
  spanning-forest fact `rep` is built from — into the `ZeroReach` witness
  `bnExists_..._of_zeroReach` asks for, by matching `AdjInList`
  along `zeroSlots` with `ZeroLink` pointwise
  (`adjInList_edgeList_zeroSlots_iff_zeroLink`).

So the only two facts a row ever supplies are `IsForest` and `¬ IsLoopy` of
the concrete Finset `zeroSlots certificate point` — both decidable, both
already what a census enumerates.
`bnExists_on_degenerate_subdivision_of_validClosed_of_forestCensus`
below is the resulting one-call wrapper, shaped to exactly match
`ExplicitPotential.CertificateData.bnExists_on_degenerate_subdivision_of_validClosed_of_zeroReach`'s
conclusion.
-/

@[expose] public section

namespace Utilities.Certificate
open Utilities.Certificate

open Utilities

open Finset ExplicitPotential ContractionForestCensusGeneral

end Utilities.Certificate

namespace Utilities.Certificate.ExplicitPotential.CertificateData
open Utilities
open Utilities.Certificate

open Utilities.Certificate
open Utilities
open Finset ExplicitPotential ContractionForestCensusGeneral
open Utilities.Certificate.ExplicitPotential
open Utilities.Certificate.ExplicitPotential.CertificateData

variable {m n p : ℕ}

/-! ## The vanishing-slot set at a point -/

/-- The slots that vanish at `point`: exactly the `Finset` a contraction
census classifies. -/
def zeroSlots (certificate : CertificateData m n p) (point : Fin m → ℤ) : Finset (Fin p) :=
  Finset.univ.filter (fun edge => certificate.segmentNat point edge = 0)

@[simp] theorem mem_zeroSlots (certificate : CertificateData m n p) (point : Fin m → ℤ)
    (edge : Fin p) :
    edge ∈ certificate.zeroSlots point ↔ certificate.segmentNat point edge = 0 := by
  simp [zeroSlots]

theorem not_mem_zeroSlots_of_pos (certificate : CertificateData m n p) (point : Fin m → ℤ)
    {edge : Fin p} (hpos : 0 < certificate.segmentNat point edge) :
    edge ∉ certificate.zeroSlots point := by
  simp only [mem_zeroSlots]; omega

/-! ## The face datum, produced from the census's two facts -/

/-- **The census-produced `rep`.** No row ever writes this by hand: it is the
union-find component map of the vanishing-slot set. -/
def censusRep (certificate : CertificateData m n p) (point : Fin m → ℤ) : Fin n → Fin n :=
  compFold certificate.core (certificate.zeroSlots point)

theorem censusRep_idem (certificate : CertificateData m n p) (point : Fin m → ℤ) :
    ∀ v : Fin n, certificate.censusRep point (certificate.censusRep point v)
      = certificate.censusRep point v :=
  compFold_idem certificate.core (certificate.zeroSlots point)

theorem censusRep_zero (certificate : CertificateData m n p) (point : Fin m → ℤ) :
    ∀ edge : Fin p, certificate.segmentNat point edge = 0 →
      certificate.censusRep point (certificate.core.tail edge) =
        certificate.censusRep point (certificate.core.head edge) :=
  fun edge hzero =>
    compFold_tail_eq_head_of_mem certificate.core
      ((certificate.mem_zeroSlots point edge).mpr hzero)

theorem censusRep_loopless (certificate : CertificateData m n p) (point : Fin m → ℤ)
    (hNotLoopy : ¬ IsLoopy certificate.core (certificate.zeroSlots point)) :
    ∀ edge : Fin p, 0 < certificate.segmentNat point edge →
      certificate.censusRep point (certificate.core.tail edge) ≠
        certificate.censusRep point (certificate.core.head edge) :=
  fun edge hpos =>
    rep_loopless_of_not_isLoopy certificate.core hNotLoopy edge
      (certificate.not_mem_zeroSlots_of_pos point hpos)

theorem censusRep_forest (certificate : CertificateData m n p) (point : Fin m → ℤ)
    (hForest : IsForest certificate.core (certificate.zeroSlots point)) :
    (Finset.univ.image (certificate.censusRep point)).card
      + (Finset.univ.filter
          (fun edge : Fin p => certificate.segmentNat point edge = 0)).card = n :=
  forest_image_add_card_eq certificate.core hForest

/-! ## The `ZeroReach` witness, from the same spanning-forest structure -/

/-- Direct adjacency along `zeroSlots` is exactly `ZeroLink`, pointwise: both
say "some vanishing slot joins `u` and `v`, in either reading direction". -/
theorem adjInList_edgeList_zeroSlots_iff_zeroLink (certificate : CertificateData m n p)
    (point : Fin m → ℤ) (u v : Fin n) :
    AdjInList certificate.core (edgeList (certificate.zeroSlots point)) u v ↔
      certificate.ZeroLink point u v := by
  unfold AdjInList ZeroLink
  constructor
  · rintro ⟨e, he, hcase⟩
    rw [mem_edgeList, certificate.mem_zeroSlots] at he
    exact ⟨e, he, hcase.imp id (fun h => ⟨h.2, h.1⟩)⟩
  · rintro ⟨e, hzero, hcase⟩
    exact ⟨e, (mem_edgeList _ e).mpr ((certificate.mem_zeroSlots point e).mpr hzero),
      hcase.imp id (fun h => ⟨h.2, h.1⟩)⟩

/-- Reachability along `zeroSlots` is exactly `ZeroReach`: the
reflexive-transitive closures of the two pointwise-equal relations above
agree, by `Relation.ReflTransGen.mono` in both directions. -/
theorem reachIn_zeroSlots_iff_zeroReach (certificate : CertificateData m n p)
    (point : Fin m → ℤ) (u v : Fin n) :
    ReachIn certificate.core (certificate.zeroSlots point) u v ↔
      certificate.ZeroReach point u v := by
  unfold ReachIn ReachInList ZeroReach
  constructor
  · -- v4.33 note: `Relation.ReflTransGen.mono` now concludes `≤` between whole
    -- relations, so it must be applied to the two explicit points (`u v`)
    -- before it can be used as an implication.
    exact Relation.ReflTransGen.mono
      (fun a b h => (certificate.adjInList_edgeList_zeroSlots_iff_zeroLink point a b).mp h) u v
  · exact Relation.ReflTransGen.mono
      (fun a b h => (certificate.adjInList_edgeList_zeroSlots_iff_zeroLink point a b).mpr h) u v

/-- **The `ZeroReach` witness the interpolated layer needs, emitted by the
census.** Every vertex reaches its own `censusRep` image along a chain of
vanishing slots — the same spanning-forest fact `censusRep` is defined from,
via `reachIn_self_compFold`, read through
`reachIn_zeroSlots_iff_zeroReach`. No separate search: it falls out of
`rep`'s own construction. -/
theorem censusRep_zeroReach (certificate : CertificateData m n p) (point : Fin m → ℤ) :
    ∀ v : Fin n, certificate.ZeroReach point v (certificate.censusRep point v) :=
  fun v =>
    (certificate.reachIn_zeroSlots_iff_zeroReach point v (certificate.censusRep point v)).mp
      (reachIn_self_compFold certificate.core (certificate.zeroSlots point) v)

/-! ## The one-call wrapper, shaped to `bnExists_..._of_zeroReach` exactly -/

/-- **The acceptance-test wrapper.** Everything
`bnExists_on_degenerate_subdivision_of_validClosed_of_zeroReach`
needs beyond `ValidClosed`/`FormsHold`/core connectivity is produced from a
single decidable pair of census facts about `zeroSlots certificate point`:
that it is a forest (`IsForest`) and carries no semantic loop (`¬ IsLoopy`).
No `rep`, no `ZeroReach` witness, and no `forest` cardinality proof is ever
written by a row again. -/
theorem bnExists_on_degenerate_subdivision_of_validClosed_of_forestCensus
    (certificate : CertificateData m n p) (point : Fin m → ℤ) (core_nonempty : 0 < n)
    (degree : ℤ) (hValid : certificate.ValidClosed degree)
    (hCone : FormsHold certificate.cone point)
    (hForest : IsForest certificate.core (certificate.zeroSlots point))
    (hNotLoopy : ¬ IsLoopy certificate.core (certificate.zeroSlots point))
    (hCoreConnected : certificate.core.Connected) :
    BNExists
      (certificate.degenerateSpec point core_nonempty (certificate.censusRep point)
        (certificate.censusRep_idem point) (certificate.censusRep_zero point)
        (certificate.censusRep_loopless point hNotLoopy)
        (certificate.censusRep_forest point hForest)).graph 1 degree :=
  certificate.bnExists_on_degenerate_subdivision_of_validClosed_of_zeroReach point
    core_nonempty (certificate.censusRep point) (certificate.censusRep_idem point)
    (certificate.censusRep_zero point) (certificate.censusRep_loopless point hNotLoopy)
    (certificate.censusRep_forest point hForest) degree hValid hCone
    (certificate.censusRep_zeroReach point) hCoreConnected

end Utilities.Certificate.ExplicitPotential.CertificateData

namespace Utilities.Certificate
open Utilities.Certificate
open Utilities
open Finset ExplicitPotential ContractionForestCensusGeneral

end Utilities.Certificate
