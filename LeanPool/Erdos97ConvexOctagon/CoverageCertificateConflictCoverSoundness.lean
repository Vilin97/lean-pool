/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageCertificateConflictCovers
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateSupportSoundness

/-! # Global validity of the generated conflict covers -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

private theorem conflictCoverGroup_valid
    {group : Array ConflictCover} (hgroup : group ∈ conflictCoverGroups) :
    group.toList.all ConflictCover.validB = true := by
  rw [Array.mem_iff_getElem] at hgroup
  obtain ⟨index, hindex, rfl⟩ := hgroup
  have hbound : index < 88 := by
    simpa only [conflictCoverGroups_size] using hindex
  interval_cases index
  · simpa [conflictCoverGroups] using conflictCovers00_valid
  · simpa [conflictCoverGroups] using conflictCovers01_valid
  · simpa [conflictCoverGroups] using conflictCovers02_valid
  · simpa [conflictCoverGroups] using conflictCovers03_valid
  · simpa [conflictCoverGroups] using conflictCovers04_valid
  · simpa [conflictCoverGroups] using conflictCovers05_valid
  · simpa [conflictCoverGroups] using conflictCovers06_valid
  · simpa [conflictCoverGroups] using conflictCovers07_valid
  · simpa [conflictCoverGroups] using conflictCovers08_valid
  · simpa [conflictCoverGroups] using conflictCovers09_valid
  · simpa [conflictCoverGroups] using conflictCovers10_valid
  · simpa [conflictCoverGroups] using conflictCovers11_valid
  · simpa [conflictCoverGroups] using conflictCovers12_valid
  · simpa [conflictCoverGroups] using conflictCovers13_valid
  · simpa [conflictCoverGroups] using conflictCovers14_valid
  · simpa [conflictCoverGroups] using conflictCovers15_valid
  · simpa [conflictCoverGroups] using conflictCovers16_valid
  · simpa [conflictCoverGroups] using conflictCovers17_valid
  · simpa [conflictCoverGroups] using conflictCovers18_valid
  · simpa [conflictCoverGroups] using conflictCovers19_valid
  · simpa [conflictCoverGroups] using conflictCovers20_valid
  · simpa [conflictCoverGroups] using conflictCovers21_valid
  · simpa [conflictCoverGroups] using conflictCovers22_valid
  · simpa [conflictCoverGroups] using conflictCovers23_valid
  · simpa [conflictCoverGroups] using conflictCovers24_valid
  · simpa [conflictCoverGroups] using conflictCovers25_valid
  · simpa [conflictCoverGroups] using conflictCovers26_valid
  · simpa [conflictCoverGroups] using conflictCovers27_valid
  · simpa [conflictCoverGroups] using conflictCovers28_valid
  · simpa [conflictCoverGroups] using conflictCovers29_valid
  · simpa [conflictCoverGroups] using conflictCovers30_valid
  · simpa [conflictCoverGroups] using conflictCovers31_valid
  · simpa [conflictCoverGroups] using conflictCovers32_valid
  · simpa [conflictCoverGroups] using conflictCovers33_valid
  · simpa [conflictCoverGroups] using conflictCovers34_valid
  · simpa [conflictCoverGroups] using conflictCovers35_valid
  · simpa [conflictCoverGroups] using conflictCovers36_valid
  · simpa [conflictCoverGroups] using conflictCovers37_valid
  · simpa [conflictCoverGroups] using conflictCovers38_valid
  · simpa [conflictCoverGroups] using conflictCovers39_valid
  · simpa [conflictCoverGroups] using conflictCovers40_valid
  · simpa [conflictCoverGroups] using conflictCovers41_valid
  · simpa [conflictCoverGroups] using conflictCovers42_valid
  · simpa [conflictCoverGroups] using conflictCovers43_valid
  · simpa [conflictCoverGroups] using conflictCovers44_valid
  · simpa [conflictCoverGroups] using conflictCovers45_valid
  · simpa [conflictCoverGroups] using conflictCovers46_valid
  · simpa [conflictCoverGroups] using conflictCovers47_valid
  · simpa [conflictCoverGroups] using conflictCovers48_valid
  · simpa [conflictCoverGroups] using conflictCovers49_valid
  · simpa [conflictCoverGroups] using conflictCovers50_valid
  · simpa [conflictCoverGroups] using conflictCovers51_valid
  · simpa [conflictCoverGroups] using conflictCovers52_valid
  · simpa [conflictCoverGroups] using conflictCovers53_valid
  · simpa [conflictCoverGroups] using conflictCovers54_valid
  · simpa [conflictCoverGroups] using conflictCovers55_valid
  · simpa [conflictCoverGroups] using conflictCovers56_valid
  · simpa [conflictCoverGroups] using conflictCovers57_valid
  · simpa [conflictCoverGroups] using conflictCovers58_valid
  · simpa [conflictCoverGroups] using conflictCovers59_valid
  · simpa [conflictCoverGroups] using conflictCovers60_valid
  · simpa [conflictCoverGroups] using conflictCovers61_valid
  · simpa [conflictCoverGroups] using conflictCovers62_valid
  · simpa [conflictCoverGroups] using conflictCovers63_valid
  · simpa [conflictCoverGroups] using conflictCovers64_valid
  · simpa [conflictCoverGroups] using conflictCovers65_valid
  · simpa [conflictCoverGroups] using conflictCovers66_valid
  · simpa [conflictCoverGroups] using conflictCovers67_valid
  · simpa [conflictCoverGroups] using conflictCovers68_valid
  · simpa [conflictCoverGroups] using conflictCovers69_valid
  · simpa [conflictCoverGroups] using conflictCovers70_valid
  · simpa [conflictCoverGroups] using conflictCovers71_valid
  · simpa [conflictCoverGroups] using conflictCovers72_valid
  · simpa [conflictCoverGroups] using conflictCovers73_valid
  · simpa [conflictCoverGroups] using conflictCovers74_valid
  · simpa [conflictCoverGroups] using conflictCovers75_valid
  · simpa [conflictCoverGroups] using conflictCovers76_valid
  · simpa [conflictCoverGroups] using conflictCovers77_valid
  · simpa [conflictCoverGroups] using conflictCovers78_valid
  · simpa [conflictCoverGroups] using conflictCovers79_valid
  · simpa [conflictCoverGroups] using conflictCovers80_valid
  · simpa [conflictCoverGroups] using conflictCovers81_valid
  · simpa [conflictCoverGroups] using conflictCovers82_valid
  · simpa [conflictCoverGroups] using conflictCovers83_valid
  · simpa [conflictCoverGroups] using conflictCovers84_valid
  · simpa [conflictCoverGroups] using conflictCovers85_valid
  · simpa [conflictCoverGroups] using conflictCovers86_valid
  · simpa [conflictCoverGroups] using conflictCovers87_valid

/-- Every entry in the complete generated conflict-cover table is valid. -/
theorem conflictCoverGroups_entry_valid
    (group : Array ConflictCover) (hgroup : group ∈ conflictCoverGroups)
    (cover : ConflictCover) (hcover : cover ∈ group) :
    cover.validB = true := by
  apply (List.all_eq_true.mp (conflictCoverGroup_valid hgroup)) cover
  rw [Array.mem_iff_getElem] at hcover
  obtain ⟨index, hindex, rfl⟩ := hcover
  exact Array.getElem_mem_toList hindex

/-- Every successful generated conflict-cover lookup is semantically sound. -/
theorem conflictCoverLookup_valid
    {identifier : Nat} {cover : ConflictCover}
    (hlookup : conflictCoverLookup identifier = some cover) : cover.Valid :=
  conflictCoverLookup_valid_of_audit
    (fun group hgroup entry hentry =>
      conflictCoverGroups_entry_valid group hgroup entry hentry)
    hlookup

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
