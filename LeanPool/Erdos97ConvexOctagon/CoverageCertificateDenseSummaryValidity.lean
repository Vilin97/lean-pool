/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateDenseSummaryFacts00
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateDenseSummaryFacts01
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateDenseSummaryFacts02
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateDenseSummaryFacts03
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateDenseSummaryFacts04
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateDenseSummaryFacts05
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateDenseSummaryFacts06
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateDenseSummaryFacts07

/-! # Global validity of dense certificate summaries -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

private theorem densePatternSummaryGroups_size :
    densePatternSummaryGroups.size = 22 := by
  rfl

private theorem denseHardSummaryGroups_size :
    denseHardSummaryGroups.size = 17 := by
  rfl

private theorem densePatternSummaryGroup_canonical
    {group : Array PatternSummary} (hgroup : group ∈ densePatternSummaryGroups) :
    group.toList.all patternSummaryCanonicalB = true := by
  rw [Array.mem_iff_getElem] at hgroup
  obtain ⟨index, hindex, rfl⟩ := hgroup
  have hbound : index < 22 := by
    simpa only [densePatternSummaryGroups_size] using hindex
  interval_cases index
  · simpa [densePatternSummaryGroups] using
        densePatternSummaries00_canonical
  · simpa [densePatternSummaryGroups] using
        densePatternSummaries01_canonical
  · simpa [densePatternSummaryGroups] using
        densePatternSummaries02_canonical
  · simpa [densePatternSummaryGroups] using
        densePatternSummaries03_canonical
  · simpa [densePatternSummaryGroups] using
        densePatternSummaries04_canonical
  · simpa [densePatternSummaryGroups] using
        densePatternSummaries05_canonical
  · simpa [densePatternSummaryGroups] using
        densePatternSummaries06_canonical
  · simpa [densePatternSummaryGroups] using
        densePatternSummaries07_canonical
  · simpa [densePatternSummaryGroups] using
        densePatternSummaries08_canonical
  · simpa [densePatternSummaryGroups] using
        densePatternSummaries09_canonical
  · simpa [densePatternSummaryGroups] using
        densePatternSummaries10_canonical
  · simpa [densePatternSummaryGroups] using
        densePatternSummaries11_canonical
  · simpa [densePatternSummaryGroups] using
        densePatternSummaries12_canonical
  · simpa [densePatternSummaryGroups] using
        densePatternSummaries13_canonical
  · simpa [densePatternSummaryGroups] using
        densePatternSummaries14_canonical
  · simpa [densePatternSummaryGroups] using
        densePatternSummaries15_canonical
  · simpa [densePatternSummaryGroups] using
        densePatternSummaries16_canonical
  · simpa [densePatternSummaryGroups] using
        densePatternSummaries17_canonical
  · simpa [densePatternSummaryGroups] using
        densePatternSummaries18_canonical
  · simpa [densePatternSummaryGroups] using
        densePatternSummaries19_canonical
  · simpa [densePatternSummaryGroups] using
        densePatternSummaries20_canonical
  · simpa [densePatternSummaryGroups] using
        densePatternSummaries21_canonical

private theorem denseHardSummaryGroup_canonical
    {group : Array HardSummary} (hgroup : group ∈ denseHardSummaryGroups) :
    group.toList.all hardSummaryCanonicalB = true := by
  rw [Array.mem_iff_getElem] at hgroup
  obtain ⟨index, hindex, rfl⟩ := hgroup
  have hbound : index < 17 := by
    simpa only [denseHardSummaryGroups_size] using hindex
  interval_cases index
  · simpa [denseHardSummaryGroups] using
        denseHardSummaries00_canonical
  · simpa [denseHardSummaryGroups] using
        denseHardSummaries01_canonical
  · simpa [denseHardSummaryGroups] using
        denseHardSummaries02_canonical
  · simpa [denseHardSummaryGroups] using
        denseHardSummaries03_canonical
  · simpa [denseHardSummaryGroups] using
        denseHardSummaries04_canonical
  · simpa [denseHardSummaryGroups] using
        denseHardSummaries05_canonical
  · simpa [denseHardSummaryGroups] using
        denseHardSummaries06_canonical
  · simpa [denseHardSummaryGroups] using
        denseHardSummaries07_canonical
  · simpa [denseHardSummaryGroups] using
        denseHardSummaries08_canonical
  · simpa [denseHardSummaryGroups] using
        denseHardSummaries09_canonical
  · simpa [denseHardSummaryGroups] using
        denseHardSummaries10_canonical
  · simpa [denseHardSummaryGroups] using
        denseHardSummaries11_canonical
  · simpa [denseHardSummaryGroups] using
        denseHardSummaries12_canonical
  · simpa [denseHardSummaryGroups] using
        denseHardSummaries13_canonical
  · simpa [denseHardSummaryGroups] using
        denseHardSummaries14_canonical
  · simpa [denseHardSummaryGroups] using
        denseHardSummaries15_canonical
  · simpa [denseHardSummaryGroups] using
        denseHardSummaries16_canonical

/-- Every successful dense pattern-summary lookup is semantically valid. -/
theorem densePatternSummaryLookup_valid
    {identifier : Nat} {summary : PatternSummary}
    (hlookup : densePatternSummaryLookup identifier = some summary) :
    summary.Valid := by
  apply densePatternSummaryLookup_valid_of_audit _ hlookup
  intro group hgroup entry hentry
  apply (List.all_eq_true.mp (densePatternSummaryGroup_canonical hgroup)) entry
  rw [Array.mem_iff_getElem] at hentry
  obtain ⟨index, hindex, rfl⟩ := hentry
  exact Array.getElem_mem_toList hindex

/-- Every successful dense exact-summary lookup is semantically valid. -/
theorem denseHardSummaryLookup_valid
    {identifier : Nat} {summary : HardSummary}
    (hlookup : denseHardSummaryLookup identifier = some summary) : summary.Valid := by
  apply denseHardSummaryLookup_valid_of_audit _ hlookup
  intro group hgroup entry hentry
  apply (List.all_eq_true.mp (denseHardSummaryGroup_canonical hgroup)) entry
  rw [Array.mem_iff_getElem] at hentry
  obtain ⟨index, hindex, rfl⟩ := hentry
  exact Array.getElem_mem_toList hindex

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
