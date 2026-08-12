/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageSummaryValidity

/-! # Canonical lookup and validity of coverage summaries -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Retrieve the generated pattern summary having one source origin. -/
def patternSummaryForOriginLookup (origin : Nat) : Option PatternSummary :=
  let group := patternSummaryBucketGroups.getD (origin % 256 / 8) #[]
  (group.getD (origin % 8) []).find? fun summary => summary.origin == origin

/-- Retrieve the generated hard summary having one source origin. -/
def hardSummaryForOriginLookup (origin : Nat) : Option HardSummary :=
  let group := hardSummaryBucketGroups.getD (origin % 256 / 8) #[]
  (group.getD (origin % 8) []).find? fun summary => summary.origin == origin

/-- Every pattern returned by the canonical origin lookup is globally audited. -/
theorem patternSummaryForOriginLookup_valid
    {origin : Nat} {summary : PatternSummary}
    (hlookup : patternSummaryForOriginLookup origin = some summary) : summary.Valid := by
  let groupIndex := origin % 256 / 8
  have hgroupIndex : groupIndex < patternSummaryBucketGroups.size := by
    change origin % 256 / 8 < 32
    omega
  let group := patternSummaryBucketGroups[groupIndex]'hgroupIndex
  have hgroup : group ∈ patternSummaryBucketGroups.toList :=
    Array.getElem_mem_toList hgroupIndex
  have hgroupGetD : patternSummaryBucketGroups.getD groupIndex #[] = group := by
    simp only [Array.getD, dite_eq_left hgroupIndex, Array.getInternal_eq_getElem,
      group]
  rw [patternSummaryForOriginLookup, hgroupGetD] at hlookup
  by_cases hbucketIndex : origin % 8 < group.size
  · let bucket := group[origin % 8]'hbucketIndex
    have hbucket : bucket ∈ group.toList :=
      Array.getElem_mem_toList hbucketIndex
    have hbucketGetD : group.getD (origin % 8) [] = bucket := by
      simp only [Array.getD, dite_eq_left hbucketIndex, Array.getInternal_eq_getElem,
        bucket]
    rw [hbucketGetD] at hlookup
    apply PatternSummary.valid_of_data
    exact ⟨group, hgroup, bucket, hbucket,
      List.mem_of_find?_eq_some hlookup⟩
  · simp [Array.getD, hbucketIndex] at hlookup

/-- Every exact summary returned by the canonical origin lookup is globally audited. -/
theorem hardSummaryForOriginLookup_valid
    {origin : Nat} {summary : HardSummary}
    (hlookup : hardSummaryForOriginLookup origin = some summary) : summary.Valid := by
  let groupIndex := origin % 256 / 8
  have hgroupIndex : groupIndex < hardSummaryBucketGroups.size := by
    change origin % 256 / 8 < 32
    omega
  let group := hardSummaryBucketGroups[groupIndex]'hgroupIndex
  have hgroup : group ∈ hardSummaryBucketGroups.toList :=
    Array.getElem_mem_toList hgroupIndex
  have hgroupGetD : hardSummaryBucketGroups.getD groupIndex #[] = group := by
    simp only [Array.getD, dite_eq_left hgroupIndex, Array.getInternal_eq_getElem,
      group]
  rw [hardSummaryForOriginLookup, hgroupGetD] at hlookup
  by_cases hbucketIndex : origin % 8 < group.size
  · let bucket := group[origin % 8]'hbucketIndex
    have hbucket : bucket ∈ group.toList :=
      Array.getElem_mem_toList hbucketIndex
    have hbucketGetD : group.getD (origin % 8) [] = bucket := by
      simp only [Array.getD, dite_eq_left hbucketIndex, Array.getInternal_eq_getElem,
        bucket]
    rw [hbucketGetD] at hlookup
    apply HardSummary.valid_of_data
    exact ⟨group, hgroup, bucket, hbucket,
      List.mem_of_find?_eq_some hlookup⟩
  · simp [Array.getD, hbucketIndex] at hlookup

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
