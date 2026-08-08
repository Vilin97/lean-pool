/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData

/-! # Soundness of lightweight coverage-summary audits -/

namespace Erdos97Octagon.RawIncidence

/-- A pattern summary denotes a checked obstruction with the advertised fields. -/
def PatternSummary.Valid (summary : PatternSummary) : Prop :=
  ∃ entry : PatternEntry, entry.origin = summary.origin ∧
    entry.mask = summary.mask ∧ entry.validB = true

/-- An exact-table summary denotes a checked obstruction with the advertised fields. -/
def HardSummary.Valid (summary : HardSummary) : Prop :=
  ∃ entry : HardEntry, entry.origin = summary.origin ∧
    entry.code = summary.code ∧ entry.validB = true

/-- A successful Boolean lookup gives the obstruction denoted by a pattern summary. -/
theorem PatternSummary.valid_of_validAgainstB
    {buckets : Array (List PatternEntry)} {summary : PatternSummary}
    (hvalid : summary.validAgainstB buckets = true) : summary.Valid := by
  unfold PatternSummary.validAgainstB at hvalid
  generalize hfind : (buckets.getD (summary.origin % 8) []).find?
      (fun entry => entry.origin == summary.origin) = found at hvalid
  cases found with
  | none => simp at hvalid
  | some entry =>
      have hchecks : entry.mask = summary.mask ∧ entry.validB = true := by
        simpa only [Bool.and_eq_true, beq_iff_eq] using hvalid
      have horigin : entry.origin = summary.origin := by
        simpa only [beq_iff_eq] using List.find?_some hfind
      exact ⟨entry, horigin, hchecks⟩

/-- A successful Boolean lookup gives the obstruction denoted by an exact summary. -/
theorem HardSummary.valid_of_validAgainstB
    {buckets : Array (List HardEntry)} {summary : HardSummary}
    (hvalid : summary.validAgainstB buckets = true) : summary.Valid := by
  unfold HardSummary.validAgainstB at hvalid
  generalize hfind : (buckets.getD (summary.origin % 8) []).find?
      (fun entry => entry.origin == summary.origin) = found at hvalid
  cases found with
  | none => simp at hvalid
  | some entry =>
      have hchecks : entry.code = summary.code ∧ entry.validB = true := by
        simpa only [Bool.and_eq_true, beq_iff_eq] using hvalid
      have horigin : entry.origin = summary.origin := by
        simpa only [beq_iff_eq] using List.find?_some hfind
      exact ⟨entry, horigin, hchecks⟩

private theorem PatternSummary.valid_of_shardAudit
    {buckets : Array (List PatternEntry)}
    {summaries : Array (List PatternSummary)} {summary : PatternSummary}
    (haudit : summaries.toList.all (fun bucket =>
      bucket.all (PatternSummary.validAgainstB buckets)) = true)
    (hmember : ∃ bucket ∈ summaries.toList, summary ∈ bucket) : summary.Valid := by
  obtain ⟨bucket, hbucket, hsummary⟩ := hmember
  have hbucketAudit := (List.all_eq_true.mp haudit) bucket hbucket
  exact PatternSummary.valid_of_validAgainstB
    ((List.all_eq_true.mp hbucketAudit) summary hsummary)

private theorem HardSummary.valid_of_shardAudit
    {buckets : Array (List HardEntry)}
    {summaries : Array (List HardSummary)} {summary : HardSummary}
    (haudit : summaries.toList.all (fun bucket =>
      bucket.all (HardSummary.validAgainstB buckets)) = true)
    (hmember : ∃ bucket ∈ summaries.toList, summary ∈ bucket) : summary.Valid := by
  obtain ⟨bucket, hbucket, hsummary⟩ := hmember
  have hbucketAudit := (List.all_eq_true.mp haudit) bucket hbucket
  exact HardSummary.valid_of_validAgainstB
    ((List.all_eq_true.mp hbucketAudit) summary hsummary)

private structure ValidPatternShard where
  summaries : Array (List PatternSummary)
  entries : Array (List PatternEntry)
  audit : summaries.toList.all (fun bucket =>
    bucket.all (PatternSummary.validAgainstB entries)) = true

private structure ValidHardShard where
  summaries : Array (List HardSummary)
  entries : Array (List HardEntry)
  audit : summaries.toList.all (fun bucket =>
    bucket.all (HardSummary.validAgainstB entries)) = true

private def validPatternShards : List ValidPatternShard := [
  ⟨patternSummaryBuckets00, patternBuckets00, patternSummaryBuckets00_valid⟩,
  ⟨patternSummaryBuckets01, patternBuckets01, patternSummaryBuckets01_valid⟩,
  ⟨patternSummaryBuckets02, patternBuckets02, patternSummaryBuckets02_valid⟩,
  ⟨patternSummaryBuckets03, patternBuckets03, patternSummaryBuckets03_valid⟩,
  ⟨patternSummaryBuckets04, patternBuckets04, patternSummaryBuckets04_valid⟩,
  ⟨patternSummaryBuckets05, patternBuckets05, patternSummaryBuckets05_valid⟩,
  ⟨patternSummaryBuckets06, patternBuckets06, patternSummaryBuckets06_valid⟩,
  ⟨patternSummaryBuckets07, patternBuckets07, patternSummaryBuckets07_valid⟩,
  ⟨patternSummaryBuckets08, patternBuckets08, patternSummaryBuckets08_valid⟩,
  ⟨patternSummaryBuckets09, patternBuckets09, patternSummaryBuckets09_valid⟩,
  ⟨patternSummaryBuckets10, patternBuckets10, patternSummaryBuckets10_valid⟩,
  ⟨patternSummaryBuckets11, patternBuckets11, patternSummaryBuckets11_valid⟩,
  ⟨patternSummaryBuckets12, patternBuckets12, patternSummaryBuckets12_valid⟩,
  ⟨patternSummaryBuckets13, patternBuckets13, patternSummaryBuckets13_valid⟩,
  ⟨patternSummaryBuckets14, patternBuckets14, patternSummaryBuckets14_valid⟩,
  ⟨patternSummaryBuckets15, patternBuckets15, patternSummaryBuckets15_valid⟩,
  ⟨patternSummaryBuckets16, patternBuckets16, patternSummaryBuckets16_valid⟩,
  ⟨patternSummaryBuckets17, patternBuckets17, patternSummaryBuckets17_valid⟩,
  ⟨patternSummaryBuckets18, patternBuckets18, patternSummaryBuckets18_valid⟩,
  ⟨patternSummaryBuckets19, patternBuckets19, patternSummaryBuckets19_valid⟩,
  ⟨patternSummaryBuckets20, patternBuckets20, patternSummaryBuckets20_valid⟩,
  ⟨patternSummaryBuckets21, patternBuckets21, patternSummaryBuckets21_valid⟩,
  ⟨patternSummaryBuckets22, patternBuckets22, patternSummaryBuckets22_valid⟩,
  ⟨patternSummaryBuckets23, patternBuckets23, patternSummaryBuckets23_valid⟩,
  ⟨patternSummaryBuckets24, patternBuckets24, patternSummaryBuckets24_valid⟩,
  ⟨patternSummaryBuckets25, patternBuckets25, patternSummaryBuckets25_valid⟩,
  ⟨patternSummaryBuckets26, patternBuckets26, patternSummaryBuckets26_valid⟩,
  ⟨patternSummaryBuckets27, patternBuckets27, patternSummaryBuckets27_valid⟩,
  ⟨patternSummaryBuckets28, patternBuckets28, patternSummaryBuckets28_valid⟩,
  ⟨patternSummaryBuckets29, patternBuckets29, patternSummaryBuckets29_valid⟩,
  ⟨patternSummaryBuckets30, patternBuckets30, patternSummaryBuckets30_valid⟩,
  ⟨patternSummaryBuckets31, patternBuckets31, patternSummaryBuckets31_valid⟩
]

private def validHardShards : List ValidHardShard := [
  ⟨hardSummaryBuckets00, hardBuckets00, hardSummaryBuckets00_valid⟩,
  ⟨hardSummaryBuckets01, hardBuckets01, hardSummaryBuckets01_valid⟩,
  ⟨hardSummaryBuckets02, hardBuckets02, hardSummaryBuckets02_valid⟩,
  ⟨hardSummaryBuckets03, hardBuckets03, hardSummaryBuckets03_valid⟩,
  ⟨hardSummaryBuckets04, hardBuckets04, hardSummaryBuckets04_valid⟩,
  ⟨hardSummaryBuckets05, hardBuckets05, hardSummaryBuckets05_valid⟩,
  ⟨hardSummaryBuckets06, hardBuckets06, hardSummaryBuckets06_valid⟩,
  ⟨hardSummaryBuckets07, hardBuckets07, hardSummaryBuckets07_valid⟩,
  ⟨hardSummaryBuckets08, hardBuckets08, hardSummaryBuckets08_valid⟩,
  ⟨hardSummaryBuckets09, hardBuckets09, hardSummaryBuckets09_valid⟩,
  ⟨hardSummaryBuckets10, hardBuckets10, hardSummaryBuckets10_valid⟩,
  ⟨hardSummaryBuckets11, hardBuckets11, hardSummaryBuckets11_valid⟩,
  ⟨hardSummaryBuckets12, hardBuckets12, hardSummaryBuckets12_valid⟩,
  ⟨hardSummaryBuckets13, hardBuckets13, hardSummaryBuckets13_valid⟩,
  ⟨hardSummaryBuckets14, hardBuckets14, hardSummaryBuckets14_valid⟩,
  ⟨hardSummaryBuckets15, hardBuckets15, hardSummaryBuckets15_valid⟩,
  ⟨hardSummaryBuckets16, hardBuckets16, hardSummaryBuckets16_valid⟩,
  ⟨hardSummaryBuckets17, hardBuckets17, hardSummaryBuckets17_valid⟩,
  ⟨hardSummaryBuckets18, hardBuckets18, hardSummaryBuckets18_valid⟩,
  ⟨hardSummaryBuckets19, hardBuckets19, hardSummaryBuckets19_valid⟩,
  ⟨hardSummaryBuckets20, hardBuckets20, hardSummaryBuckets20_valid⟩,
  ⟨hardSummaryBuckets21, hardBuckets21, hardSummaryBuckets21_valid⟩,
  ⟨hardSummaryBuckets22, hardBuckets22, hardSummaryBuckets22_valid⟩,
  ⟨hardSummaryBuckets23, hardBuckets23, hardSummaryBuckets23_valid⟩,
  ⟨hardSummaryBuckets24, hardBuckets24, hardSummaryBuckets24_valid⟩,
  ⟨hardSummaryBuckets25, hardBuckets25, hardSummaryBuckets25_valid⟩,
  ⟨hardSummaryBuckets26, hardBuckets26, hardSummaryBuckets26_valid⟩,
  ⟨hardSummaryBuckets27, hardBuckets27, hardSummaryBuckets27_valid⟩,
  ⟨hardSummaryBuckets28, hardBuckets28, hardSummaryBuckets28_valid⟩,
  ⟨hardSummaryBuckets29, hardBuckets29, hardSummaryBuckets29_valid⟩,
  ⟨hardSummaryBuckets30, hardBuckets30, hardSummaryBuckets30_valid⟩,
  ⟨hardSummaryBuckets31, hardBuckets31, hardSummaryBuckets31_valid⟩
]

private theorem patternGroups_eq :
    patternSummaryBucketGroups.toList =
      validPatternShards.map ValidPatternShard.summaries := by
  rfl

private theorem hardGroups_eq :
    hardSummaryBucketGroups.toList =
      validHardShards.map ValidHardShard.summaries := by
  rfl

/-- Every generated pattern summary has the obstruction certified by its source shard. -/
theorem PatternSummary.valid_of_data
    {summary : PatternSummary}
    (hmember : ∃ shard ∈ patternSummaryBucketGroups.toList,
      ∃ bucket ∈ shard.toList, summary ∈ bucket) : summary.Valid := by
  obtain ⟨summaries, hsummaries, bucket, hbucket, hsummary⟩ := hmember
  rw [patternGroups_eq, List.mem_map] at hsummaries
  obtain ⟨shard, hshard, rfl⟩ := hsummaries
  exact PatternSummary.valid_of_shardAudit shard.audit
    ⟨bucket, hbucket, hsummary⟩

/-- Every generated hard summary has the obstruction certified by its source shard. -/
theorem HardSummary.valid_of_data
    {summary : HardSummary}
    (hmember : ∃ shard ∈ hardSummaryBucketGroups.toList,
      ∃ bucket ∈ shard.toList, summary ∈ bucket) : summary.Valid := by
  obtain ⟨summaries, hsummaries, bucket, hbucket, hsummary⟩ := hmember
  rw [hardGroups_eq, List.mem_map] at hsummaries
  obtain ⟨shard, hshard, rfl⟩ := hsummaries
  exact HardSummary.valid_of_shardAudit shard.audit
    ⟨bucket, hbucket, hsummary⟩

/-- Membership in the generated pattern-summary table supplies its audited entry. -/
theorem PatternSummary.valid_of_memberB
    {summary : PatternSummary} (hmember : summary.memberB = true) : summary.Valid := by
  let groupIndex := summary.origin % 256 / 8
  have hgroupIndex : groupIndex < patternSummaryBucketGroups.size := by
    change summary.origin % 256 / 8 < 32
    omega
  let group := patternSummaryBucketGroups[groupIndex]'hgroupIndex
  have hgroup : group ∈ patternSummaryBucketGroups.toList := by
    exact Array.getElem_mem_toList hgroupIndex
  have hgroupGetD : patternSummaryBucketGroups.getD groupIndex #[] = group := by
    simp only [Array.getD, dif_pos hgroupIndex, Array.getInternal_eq_getElem, group]
  rw [PatternSummary.memberB, hgroupGetD] at hmember
  change (match (group.getD (summary.origin % 8) []).find?
      (fun candidate => candidate.origin == summary.origin) with
    | some candidate => candidate.mask == summary.mask
    | none => false) = true at hmember
  by_cases hbucketIndex : summary.origin % 8 < group.size
  · let bucket := group[summary.origin % 8]'hbucketIndex
    have hbucket : bucket ∈ group.toList := Array.getElem_mem_toList hbucketIndex
    have hbucketGetD : group.getD (summary.origin % 8) [] = bucket := by
      simp only [Array.getD, dif_pos hbucketIndex, Array.getInternal_eq_getElem,
        bucket]
    rw [hbucketGetD] at hmember
    generalize hfind : bucket.find?
        (fun candidate => candidate.origin == summary.origin) = found at hmember
    cases found with
    | none => simp at hmember
    | some candidate =>
        have horigin : candidate.origin = summary.origin := by
          simpa only [beq_iff_eq] using List.find?_some hfind
        have hmask : candidate.mask = summary.mask := by
          simpa only [beq_iff_eq] using hmember
        have hequal : candidate = summary := by
          cases candidate
          cases summary
          simp_all
        apply PatternSummary.valid_of_data
        refine ⟨group, hgroup, bucket, hbucket, ?_⟩
        simpa only [hequal] using List.mem_of_find?_eq_some hfind
  · simp [Array.getD, hbucketIndex] at hmember

/-- Membership in the generated exact-summary table supplies its audited entry. -/
theorem HardSummary.valid_of_memberB
    {summary : HardSummary} (hmember : summary.memberB = true) : summary.Valid := by
  let groupIndex := summary.origin % 256 / 8
  have hgroupIndex : groupIndex < hardSummaryBucketGroups.size := by
    change summary.origin % 256 / 8 < 32
    omega
  let group := hardSummaryBucketGroups[groupIndex]'hgroupIndex
  have hgroup : group ∈ hardSummaryBucketGroups.toList := by
    exact Array.getElem_mem_toList hgroupIndex
  have hgroupGetD : hardSummaryBucketGroups.getD groupIndex #[] = group := by
    simp only [Array.getD, dif_pos hgroupIndex, Array.getInternal_eq_getElem, group]
  rw [HardSummary.memberB, hgroupGetD] at hmember
  change (match (group.getD (summary.origin % 8) []).find?
      (fun candidate => candidate.origin == summary.origin) with
    | some candidate => candidate.code == summary.code
    | none => false) = true at hmember
  by_cases hbucketIndex : summary.origin % 8 < group.size
  · let bucket := group[summary.origin % 8]'hbucketIndex
    have hbucket : bucket ∈ group.toList := Array.getElem_mem_toList hbucketIndex
    have hbucketGetD : group.getD (summary.origin % 8) [] = bucket := by
      simp only [Array.getD, dif_pos hbucketIndex, Array.getInternal_eq_getElem,
        bucket]
    rw [hbucketGetD] at hmember
    generalize hfind : bucket.find?
        (fun candidate => candidate.origin == summary.origin) = found at hmember
    cases found with
    | none => simp at hmember
    | some candidate =>
        have horigin : candidate.origin = summary.origin := by
          simpa only [beq_iff_eq] using List.find?_some hfind
        have hcode : candidate.code = summary.code := by
          simpa only [beq_iff_eq] using hmember
        have hequal : candidate = summary := by
          cases candidate
          cases summary
          simp_all
        apply HardSummary.valid_of_data
        refine ⟨group, hgroup, bucket, hbucket, ?_⟩
        simpa only [hequal] using List.mem_of_find?_eq_some hfind
  · simp [Array.getD, hbucketIndex] at hmember

end Erdos97Octagon.RawIncidence
