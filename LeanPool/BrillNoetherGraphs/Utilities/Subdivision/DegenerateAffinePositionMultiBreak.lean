/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateAffinePosition
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateMultiBreakScript

/-!
# Affine-positioned chips and break lists on a closed face

This is the closed-orthant companion to the affine-positioned portion of
`AffinePositionMultiBreak.lean`.  It deliberately takes a `DegSpec` and a
proof that its numerical lengths agree with the affine certificate, rather
than rebuilding a particular `DegSpec` from the certificate.  This is the
form needed by a row leaf: the contraction census chooses the representative
map, while the leaf merely names positions and slopes.

There are two small, independent carriers.

* `WeightedChip` is one affine position with an integral coefficient.  In
  contrast to the positive `MultiCode` format, a row witness may use an
  arbitrary integral coefficient before its residual checks prove
  effectiveness.
* `BreakList` is a per-slot ordered list of affine positions and their
  post-break slopes.  The concrete list is fed directly to
  `DegSpec.breakScript`; its exact interior and core Laplacian formulae are
  consequently available on collapsed faces as well.

The only geometry carried by these definitions is `LengthCompatible`.  Bound
certificates remain the existing `Code.BoundsCertified` facts, so all affine
arithmetic is shared with the positive decoder.
-/

@[expose] public section

namespace MarkedGraphs.Certificate.AffinePosition
open Utilities.Certificate

open Utilities

open Finset ExplicitPotential
open Utilities.Certificate.DegenerateSpec

namespace Closed

variable {m n p : ℕ}

/-- The affine certificate and a closed-face `DegSpec` read the same concrete
slot lengths at this point. -/
def LengthCompatible (d : DegSpec n p)
    (certificate : ExplicitPotential.CertificateData m n p) (point : Fin m → ℤ) : Prop :=
  ∀ edge : Fin p, d.length edge = certificate.segmentNat point edge

/-- Decode a cone-certified affine code into an arbitrary compatible closed
face.  Unlike `Code.decodeDegenerateVertex`, this does not require the face's
representative map to have been constructed by the certificate census. -/
def Code.decodeClosedVertex (d : DegSpec n p)
    (certificate : ExplicitPotential.CertificateData m n p) (code : Code m p)
    (point : Fin m → ℤ) {degree : ℤ}
    (hValid : certificate.ValidClosed degree)
    (hLength : LengthCompatible d certificate point)
    (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) : d.Vertex :=
  d.pathVertex code.edge ⟨code.coordinate certificate point, by
    rw [hLength code.edge]
    have h := code.coordinate_le_segmentNat_of_validClosed certificate point hValid hBounds hCone
    omega⟩

/-- A possibly signed chip at an affine-described slot position. -/
structure WeightedChip (m p : ℕ) where
  /-- The affine code naming the chip’s slot and position on that slot. -/
  position : Code m p
  /-- The signed integer multiplicity of the chip; negative coefficients are permitted. -/
  coefficient : ℤ

namespace WeightedChip

/-- Every named chip position has its two bounds certified by the local cone. -/
def BoundsCertified (certificate : ExplicitPotential.CertificateData m n p)
    (chips : List (WeightedChip m p)) : Prop :=
  ∀ chip ∈ chips, chip.position.BoundsCertified certificate

/-- The divisor denoted by a list of weighted affine chips on a compatible
closed face. -/
def divisorOf (d : DegSpec n p) (certificate : ExplicitPotential.CertificateData m n p)
    (chips : List (WeightedChip m p)) (point : Fin m → ℤ) {degree : ℤ}
    (hValid : certificate.ValidClosed degree)
    (hLength : LengthCompatible d certificate point)
    (hBounds : BoundsCertified certificate chips)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) : CFDiv d.graph :=
  (chips.attach.map fun chip => chip.1.coefficient • oneChip
    (G := d.graph)
    (Code.decodeClosedVertex d certificate chip.1.position point hValid hLength
      (hBounds chip.1 chip.2) hCone)).sum

/-- The degree of a weighted affine-chip divisor is the sum of its declared
coefficients, including negative coefficients. -/
theorem deg_divisorOf (d : DegSpec n p) (certificate : ExplicitPotential.CertificateData m n p)
    (chips : List (WeightedChip m p)) (point : Fin m → ℤ) {degree : ℤ}
    (hValid : certificate.ValidClosed degree)
    (hLength : LengthCompatible d certificate point)
    (hBounds : BoundsCertified certificate chips)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) :
    deg (divisorOf d certificate chips point hValid hLength hBounds hCone) =
      (chips.map WeightedChip.coefficient).sum := by
  have hsum : ∀ entries : List {chip // chip ∈ chips},
      deg (entries.map fun chip => chip.1.coefficient • oneChip
        (G := d.graph)
        (Code.decodeClosedVertex d certificate chip.1.position point hValid hLength
          (hBounds chip.1 chip.2) hCone)).sum =
        (entries.map fun chip => chip.1.coefficient).sum := by
    intro entries
    induction entries with
    | nil => simp
    | cons entry entries ih =>
        simp only [List.map_cons, List.sum_cons, map_add, ih, map_zsmul,
          deg_one_chip, smul_eq_mul, mul_one]
  rw [← show (chips.attach.map fun chip => chip.1.coefficient).sum =
      (chips.map WeightedChip.coefficient).sum by simp]
  exact hsum chips.attach

end WeightedChip

/-- One entry of a per-slot affine break list: its slope is in force beginning
at `position`.  List order is preserved, matching the C checker's override
semantics and `SubdivisionGraph.Spec.breakSlope`. -/
structure Break (m p : ℕ) where
  /-- The affine slot-position code at which this break entry begins to prescribe a slope. -/
  position : Code m p
  /-- The integer slope in force from this break position, subject to the ordered list’s later
  overrides. -/
  slope : ℤ

/-- Ordered break data, grouped by slot.  `WellFormed` prevents a code whose
own slot differs from the list slot from silently being interpreted with the
wrong length. -/
abbrev BreakList (m p : ℕ) := Fin p → List (Break m p)

namespace BreakList

/-- Every entry in a slot list genuinely names that slot. -/
def WellFormed (script : BreakList m p) : Prop :=
  ∀ edge entry, entry ∈ script edge → entry.position.edge = edge

/-- All affine positions in the break lists have certified bounds. -/
def BoundsCertified (certificate : ExplicitPotential.CertificateData m n p)
    (script : BreakList m p) : Prop :=
  ∀ edge entry, entry ∈ script edge → entry.position.BoundsCertified certificate

/-- Evaluate the ordered affine break list for one slot. -/
def breaks (certificate : ExplicitPotential.CertificateData m n p)
    (script : BreakList m p) (point : Fin m → ℤ) (edge : Fin p) : List (ℕ × ℤ) :=
  (script edge).map fun entry => (entry.position.coordinate certificate point, entry.slope)

/-- A concrete closed-face firing script from affine break lists. -/
def firingScript (d : DegSpec n p) (certificate : ExplicitPotential.CertificateData m n p)
    (script : BreakList m p) (potential : Fin n → ℤ) (point : Fin m → ℤ) :
    firingScript d.graph :=
  d.breakScript potential (script.breaks certificate point)

/-- The sole closing condition for an affine break-list script on a closed
face.  In particular it forces equality of endpoint potentials on a collapsed
slot. -/
def Balanced (d : DegSpec n p) (certificate : ExplicitPotential.CertificateData m n p)
    (script : BreakList m p) (potential : Fin n → ℤ) (point : Fin m → ℤ) : Prop :=
  d.BreakData potential (script.breaks certificate point)

/-- The interior Laplacian is the jump of the evaluated ordered break list. -/
theorem prin_firingScript_interiorVertex (d : DegSpec n p)
    (certificate : ExplicitPotential.CertificateData m n p) (script : BreakList m p)
    (potential : Fin n → ℤ) (point : Fin m → ℤ) (hInv : d.RepInvariant potential)
    (hBalanced : script.Balanced d certificate potential point)
    (edge : Fin p) (offset : Fin (d.length edge - 1)) :
    prin d.graph (script.firingScript d certificate potential point)
        (d.interiorVertex edge offset) =
      SubdivisionGraph.Spec.breakSlope (script.breaks certificate point edge)
          (offset.val + 1) -
        SubdivisionGraph.Spec.breakSlope (script.breaks certificate point edge) offset.val :=
  d.prin_breakScript_interiorVertex hInv hBalanced edge offset

/-- Away from every named affine break, the interior Laplacian vanishes. -/
theorem prin_firingScript_interiorVertex_eq_zero (d : DegSpec n p)
    (certificate : ExplicitPotential.CertificateData m n p) (script : BreakList m p)
    (potential : Fin n → ℤ) (point : Fin m → ℤ) (hInv : d.RepInvariant potential)
    (hBalanced : script.Balanced d certificate potential point)
    (edge : Fin p) (offset : Fin (d.length edge - 1))
    (hAvoid : ∀ entry ∈ script edge,
      entry.position.coordinate certificate point ≠ offset.val + 1) :
    prin d.graph (script.firingScript d certificate potential point)
        (d.interiorVertex edge offset) = 0 := by
  apply d.prin_breakScript_interiorVertex_eq_zero hInv hBalanced edge offset
  intro pair hPair
  obtain ⟨entry, hEntry, hEq⟩ := List.mem_map.mp hPair
  rw [← hEq]
  exact hAvoid entry hEntry

/-- The core Laplacian is the usual endpoint-slope sum over the contracted
classes, including zero slots. -/
theorem prin_firingScript_coreVertex (d : DegSpec n p)
    (certificate : ExplicitPotential.CertificateData m n p) (script : BreakList m p)
    (potential : Fin n → ℤ) (point : Fin m → ℤ) (hInv : d.RepInvariant potential)
    (hBalanced : script.Balanced d certificate potential point) (vertex : Fin n) :
    prin d.graph (script.firingScript d certificate potential point) (d.coreVertex vertex) =
      ∑ edge : Fin p,
        ((if d.rep (d.core.tail edge) = d.rep vertex then
            SubdivisionGraph.Spec.breakSlope (script.breaks certificate point edge) 0 else 0) +
          (if d.rep (d.core.head edge) = d.rep vertex then
            -SubdivisionGraph.Spec.breakSlope
              (script.breaks certificate point edge) (d.length edge - 1) else 0)) :=
  d.prin_breakScript_coreVertex hInv hBalanced vertex

end BreakList

end Closed

end MarkedGraphs.Certificate.AffinePosition
