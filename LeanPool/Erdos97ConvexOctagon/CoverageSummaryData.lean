/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData00
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData01
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData02
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData03
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData04
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData05
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData06
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData07
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData08
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData09
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData10
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData11
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData12
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData13
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData14
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData15
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData16
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData17
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData18
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData19
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData20
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData21
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData22
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData23
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData24
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData25
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData26
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData27
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData28
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData29
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData30
import LeanPool.Erdos97ConvexOctagon.CoverageSummaryData31

/-! # Aggregated lightweight coverage summaries -/

namespace Erdos97Octagon.RawIncidence

/-- The 32 groups containing all lightweight pattern summaries. -/
def patternSummaryBucketGroups : Array (Array (List PatternSummary)) := #[
  patternSummaryBuckets00,
  patternSummaryBuckets01,
  patternSummaryBuckets02,
  patternSummaryBuckets03,
  patternSummaryBuckets04,
  patternSummaryBuckets05,
  patternSummaryBuckets06,
  patternSummaryBuckets07,
  patternSummaryBuckets08,
  patternSummaryBuckets09,
  patternSummaryBuckets10,
  patternSummaryBuckets11,
  patternSummaryBuckets12,
  patternSummaryBuckets13,
  patternSummaryBuckets14,
  patternSummaryBuckets15,
  patternSummaryBuckets16,
  patternSummaryBuckets17,
  patternSummaryBuckets18,
  patternSummaryBuckets19,
  patternSummaryBuckets20,
  patternSummaryBuckets21,
  patternSummaryBuckets22,
  patternSummaryBuckets23,
  patternSummaryBuckets24,
  patternSummaryBuckets25,
  patternSummaryBuckets26,
  patternSummaryBuckets27,
  patternSummaryBuckets28,
  patternSummaryBuckets29,
  patternSummaryBuckets30,
  patternSummaryBuckets31
]

/-- The 32 groups containing all lightweight exact-table summaries. -/
def hardSummaryBucketGroups : Array (Array (List HardSummary)) := #[
  hardSummaryBuckets00,
  hardSummaryBuckets01,
  hardSummaryBuckets02,
  hardSummaryBuckets03,
  hardSummaryBuckets04,
  hardSummaryBuckets05,
  hardSummaryBuckets06,
  hardSummaryBuckets07,
  hardSummaryBuckets08,
  hardSummaryBuckets09,
  hardSummaryBuckets10,
  hardSummaryBuckets11,
  hardSummaryBuckets12,
  hardSummaryBuckets13,
  hardSummaryBuckets14,
  hardSummaryBuckets15,
  hardSummaryBuckets16,
  hardSummaryBuckets17,
  hardSummaryBuckets18,
  hardSummaryBuckets19,
  hardSummaryBuckets20,
  hardSummaryBuckets21,
  hardSummaryBuckets22,
  hardSummaryBuckets23,
  hardSummaryBuckets24,
  hardSummaryBuckets25,
  hardSummaryBuckets26,
  hardSummaryBuckets27,
  hardSummaryBuckets28,
  hardSummaryBuckets29,
  hardSummaryBuckets30,
  hardSummaryBuckets31
]

/-- Check that a pattern summary occurs in the unique generated summary data. -/
def PatternSummary.memberB (summary : PatternSummary) : Bool :=
  let group := patternSummaryBucketGroups.getD (summary.origin % 256 / 8) #[]
  match (group.getD (summary.origin % 8) []).find?
      (fun candidate => candidate.origin == summary.origin) with
  | some candidate => candidate.mask == summary.mask
  | none => false

/-- Check that a hard summary occurs in the unique generated summary data. -/
def HardSummary.memberB (summary : HardSummary) : Bool :=
  let group := hardSummaryBucketGroups.getD (summary.origin % 256 / 8) #[]
  match (group.getD (summary.origin % 8) []).find?
      (fun candidate => candidate.origin == summary.origin) with
  | some candidate => candidate.code == summary.code
  | none => false

end Erdos97Octagon.RawIncidence
