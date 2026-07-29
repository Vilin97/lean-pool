/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageData00
import LeanPool.Erdos97ConvexOctagon.CoverageData01
import LeanPool.Erdos97ConvexOctagon.CoverageData02
import LeanPool.Erdos97ConvexOctagon.CoverageData03
import LeanPool.Erdos97ConvexOctagon.CoverageData04
import LeanPool.Erdos97ConvexOctagon.CoverageData05
import LeanPool.Erdos97ConvexOctagon.CoverageData06
import LeanPool.Erdos97ConvexOctagon.CoverageData07
import LeanPool.Erdos97ConvexOctagon.CoverageData08
import LeanPool.Erdos97ConvexOctagon.CoverageData09
import LeanPool.Erdos97ConvexOctagon.CoverageData10
import LeanPool.Erdos97ConvexOctagon.CoverageData11
import LeanPool.Erdos97ConvexOctagon.CoverageData12
import LeanPool.Erdos97ConvexOctagon.CoverageData13
import LeanPool.Erdos97ConvexOctagon.CoverageData14
import LeanPool.Erdos97ConvexOctagon.CoverageData15
import LeanPool.Erdos97ConvexOctagon.CoverageData16
import LeanPool.Erdos97ConvexOctagon.CoverageData17
import LeanPool.Erdos97ConvexOctagon.CoverageData18
import LeanPool.Erdos97ConvexOctagon.CoverageData19
import LeanPool.Erdos97ConvexOctagon.CoverageData20
import LeanPool.Erdos97ConvexOctagon.CoverageData21
import LeanPool.Erdos97ConvexOctagon.CoverageData22
import LeanPool.Erdos97ConvexOctagon.CoverageData23
import LeanPool.Erdos97ConvexOctagon.CoverageData24
import LeanPool.Erdos97ConvexOctagon.CoverageData25
import LeanPool.Erdos97ConvexOctagon.CoverageData26
import LeanPool.Erdos97ConvexOctagon.CoverageData27
import LeanPool.Erdos97ConvexOctagon.CoverageData28
import LeanPool.Erdos97ConvexOctagon.CoverageData29
import LeanPool.Erdos97ConvexOctagon.CoverageData30
import LeanPool.Erdos97ConvexOctagon.CoverageData31

/-! # Erdős 97 convex-octagon formalization: Coverage Data -/

namespace Erdos97Octagon.RawIncidence

/-- The 32 generated groups containing all 256 pattern hash buckets. -/
def patternBucketGroups : Array (Array (List PatternEntry)) := #[
  patternBuckets00,
  patternBuckets01,
  patternBuckets02,
  patternBuckets03,
  patternBuckets04,
  patternBuckets05,
  patternBuckets06,
  patternBuckets07,
  patternBuckets08,
  patternBuckets09,
  patternBuckets10,
  patternBuckets11,
  patternBuckets12,
  patternBuckets13,
  patternBuckets14,
  patternBuckets15,
  patternBuckets16,
  patternBuckets17,
  patternBuckets18,
  patternBuckets19,
  patternBuckets20,
  patternBuckets21,
  patternBuckets22,
  patternBuckets23,
  patternBuckets24,
  patternBuckets25,
  patternBuckets26,
  patternBuckets27,
  patternBuckets28,
  patternBuckets29,
  patternBuckets30,
  patternBuckets31
]

/-- The 32 generated groups containing all 256 exact-table hash buckets. -/
def hardBucketGroups : Array (Array (List HardEntry)) := #[
  hardBuckets00,
  hardBuckets01,
  hardBuckets02,
  hardBuckets03,
  hardBuckets04,
  hardBuckets05,
  hardBuckets06,
  hardBuckets07,
  hardBuckets08,
  hardBuckets09,
  hardBuckets10,
  hardBuckets11,
  hardBuckets12,
  hardBuckets13,
  hardBuckets14,
  hardBuckets15,
  hardBuckets16,
  hardBuckets17,
  hardBuckets18,
  hardBuckets19,
  hardBuckets20,
  hardBuckets21,
  hardBuckets22,
  hardBuckets23,
  hardBuckets24,
  hardBuckets25,
  hardBuckets26,
  hardBuckets27,
  hardBuckets28,
  hardBuckets29,
  hardBuckets30,
  hardBuckets31
]

/-- Retrieve one pattern hash bucket. -/
def patternBucket (index : Fin 256) : List PatternEntry :=
  let group := patternBucketGroups.getD (index.val / 8) #[]
  group.getD (index.val % 8) []

/-- Retrieve one exact-table hash bucket. -/
def hardBucket (index : Fin 256) : List HardEntry :=
  let group := hardBucketGroups.getD (index.val / 8) #[]
  group.getD (index.val % 8) []

/-- Look up a monotone obstruction entry by its source identifier. -/
def patternEntry (origin : ℕ) : Option PatternEntry :=
  (patternBucket (Fin.ofNat 256 origin)).find? (fun entry => entry.origin == origin)

/-- Look up an exact-table obstruction entry by its source identifier. -/
def hardEntry (origin : ℕ) : Option HardEntry :=
  (hardBucket (Fin.ofNat 256 origin)).find? (fun entry => entry.origin == origin)

theorem patternEntry_sound {origin : ℕ} {entry : PatternEntry}
    (hfind : patternEntry origin = some entry) :
    entry.origin = origin := by
  simpa using List.find?_some hfind

theorem hardEntry_sound {origin : ℕ} {entry : HardEntry}
    (hfind : hardEntry origin = some entry) :
    entry.origin = origin := by
  simpa using List.find?_some hfind

end Erdos97Octagon.RawIncidence
