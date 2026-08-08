/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateChecker
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateLookup

/-! # Canonical validity of dense certificate summary identifiers -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Check that a dense pattern summary agrees with its canonical source lookup. -/
def patternSummaryCanonicalB (summary : PatternSummary) : Bool :=
  match patternSummaryForOriginLookup summary.origin with
  | none => false
  | some canonical =>
      (canonical.origin == summary.origin) && (canonical.mask == summary.mask)

/-- Check that a dense exact summary agrees with its canonical source lookup. -/
def hardSummaryCanonicalB (summary : HardSummary) : Bool :=
  match hardSummaryForOriginLookup summary.origin with
  | none => false
  | some canonical =>
      (canonical.origin == summary.origin) && (canonical.code == summary.code)

/-- A successful canonical comparison supplies pattern-summary validity. -/
theorem PatternSummary.valid_of_canonicalB
    {summary : PatternSummary}
    (hcanonical : patternSummaryCanonicalB summary = true) :
    summary.Valid := by
  unfold patternSummaryCanonicalB at hcanonical
  generalize hlookup : patternSummaryForOriginLookup summary.origin = found
    at hcanonical
  cases found with
  | none => simp at hcanonical
  | some canonical =>
      have hfields : canonical.origin = summary.origin ∧
          canonical.mask = summary.mask := by
        simpa only [Bool.and_eq_true, beq_iff_eq] using hcanonical
      obtain ⟨entry, horigin, hmask, hvalid⟩ :=
        patternSummaryForOriginLookup_valid hlookup
      exact ⟨entry, horigin.trans hfields.1, hmask.trans hfields.2, hvalid⟩

/-- A successful canonical comparison supplies exact-summary validity. -/
theorem HardSummary.valid_of_canonicalB
    {summary : HardSummary}
    (hcanonical : hardSummaryCanonicalB summary = true) :
    summary.Valid := by
  unfold hardSummaryCanonicalB at hcanonical
  generalize hlookup : hardSummaryForOriginLookup summary.origin = found
    at hcanonical
  cases found with
  | none => simp at hcanonical
  | some canonical =>
      have hfields : canonical.origin = summary.origin ∧
          canonical.code = summary.code := by
        simpa only [Bool.and_eq_true, beq_iff_eq] using hcanonical
      obtain ⟨entry, horigin, hcode, hvalid⟩ :=
        hardSummaryForOriginLookup_valid hlookup
      exact ⟨entry, horigin.trans hfields.1, hcode.trans hfields.2, hvalid⟩

/-- A table-wide canonical audit validates every successful dense pattern lookup. -/
theorem densePatternSummaryLookup_valid_of_audit
    {identifier : Nat} {summary : PatternSummary}
    (haudit : ∀ group ∈ densePatternSummaryGroups, ∀ entry ∈ group,
      patternSummaryCanonicalB entry = true)
    (hlookup : densePatternSummaryLookup identifier = some summary) :
    summary.Valid := by
  unfold densePatternSummaryLookup at hlookup
  generalize hgroupLookup : densePatternSummaryGroups[identifier / 64]? =
    groupOption at hlookup
  cases groupOption with
  | none => simp at hlookup
  | some group =>
      have hgroupMember : group ∈ densePatternSummaryGroups :=
        Array.mem_of_getElem? hgroupLookup
      have hsummaryMember : summary ∈ group := Array.mem_of_getElem? hlookup
      exact PatternSummary.valid_of_canonicalB
        (haudit group hgroupMember summary hsummaryMember)

/-- A table-wide canonical audit validates every successful dense exact lookup. -/
theorem denseHardSummaryLookup_valid_of_audit
    {identifier : Nat} {summary : HardSummary}
    (haudit : ∀ group ∈ denseHardSummaryGroups, ∀ entry ∈ group,
      hardSummaryCanonicalB entry = true)
    (hlookup : denseHardSummaryLookup identifier = some summary) :
    summary.Valid := by
  unfold denseHardSummaryLookup at hlookup
  generalize hgroupLookup : denseHardSummaryGroups[identifier / 64]? =
    groupOption at hlookup
  cases groupOption with
  | none => simp at hlookup
  | some group =>
      have hgroupMember : group ∈ denseHardSummaryGroups :=
        Array.mem_of_getElem? hgroupLookup
      have hsummaryMember : summary ∈ group := Array.mem_of_getElem? hlookup
      exact HardSummary.valid_of_canonicalB
        (haudit group hgroupMember summary hsummaryMember)

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
