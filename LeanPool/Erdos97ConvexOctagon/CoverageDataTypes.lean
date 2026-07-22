/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.Certificates

/-! # Erdős 97 convex-octagon formalization: Coverage Data Types -/

namespace Erdos97Octagon.RawIncidence

/-- A monotone obstruction pattern paired with its checked witness. -/
structure PatternEntry where
  /-- Identifier of the source classifier record. -/
  origin : ℕ
  /-- Packed incidences required by this monotone obstruction. -/
  mask : UInt64
  /-- The obstruction witness attached to the mask. -/
  certificate : PrefixCertificate
  /-- Kernel-checked validity of the witness on the decoded mask. -/
  valid : certificate.toCertificate.Valid (packedIncidence mask)

/-- An exact complete table paired with its checked witness. -/
structure HardEntry where
  /-- Identifier of the source classifier record. -/
  origin : ℕ
  /-- Packed code for the complete incidence table. -/
  code : UInt64
  /-- The obstruction witness attached to the exact table. -/
  certificate : Certificate
  /-- Kernel-checked validity of the witness on the decoded table. -/
  valid : certificate.Valid (packedIncidence code)

/-- Validate a pattern witness against precisely its required incidences. -/
def PatternEntry.validB (entry : PatternEntry) : Bool :=
  entry.certificate.toCertificate.validB (packedIncidence entry.mask)

/-- Validate an exact-table witness against its decoded incidence table. -/
def HardEntry.validB (entry : HardEntry) : Bool :=
  entry.certificate.validB (packedIncidence entry.code)

/-- A successful pattern audit supplies its mathematical witness. -/
theorem PatternEntry.valid_of_validB
    {entry : PatternEntry} (hvalid : entry.validB = true) :
    entry.certificate.toCertificate.Valid (packedIncidence entry.mask) :=
  Certificate.valid_of_validB hvalid

/-- A successful exact-table audit supplies its mathematical witness. -/
theorem HardEntry.valid_of_validB
    {entry : HardEntry} (hvalid : entry.validB = true) :
    entry.certificate.Valid (packedIncidence entry.code) :=
  Certificate.valid_of_validB hvalid

end Erdos97Octagon.RawIncidence
