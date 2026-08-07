/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageSummaryTypes

/-! # Static pattern-summary choices for one incidence row -/

namespace Erdos97Octagon.RawIncidence

private def patternSummaryChoice0_00 : SummaryRowChoice :=
  ⟨30, 270015488,
    [
    ]⟩

private def patternSummaryChoice0_01 : SummaryRowChoice :=
  ⟨46, 539503616,
    [
    ]⟩

private def patternSummaryChoice0_02 : SummaryRowChoice :=
  ⟨78, 1078479872,
    [
    ]⟩

private def patternSummaryChoice0_03 : SummaryRowChoice :=
  ⟨142, 2156432384,
    [
    ]⟩

private def patternSummaryChoice0_04 : SummaryRowChoice :=
  ⟨54, 137442112512,
    [
    ]⟩

private def patternSummaryChoice0_05 : SummaryRowChoice :=
  ⟨86, 274883171328,
    [
    ]⟩

private def patternSummaryChoice0_06 : SummaryRowChoice :=
  ⟨150, 549765288960,
    [
    ]⟩

private def patternSummaryChoice0_07 : SummaryRowChoice :=
  ⟨102, 70368750494720,
    [
    ]⟩

private def patternSummaryChoice0_08 : SummaryRowChoice :=
  ⟨166, 140737498883072,
    [
    ]⟩

private def patternSummaryChoice0_09 : SummaryRowChoice :=
  ⟨198, 36028797031597056,
    [
    ]⟩

private def patternSummaryChoice0_10 : SummaryRowChoice :=
  ⟨58, 138244274176,
    [
    ]⟩

private def patternSummaryChoice0_11 : SummaryRowChoice :=
  ⟨90, 276220106752,
    [
    ]⟩

private def patternSummaryChoice0_12 : SummaryRowChoice :=
  ⟨154, 552171771904,
    [
    ]⟩

private def patternSummaryChoice0_13 : SummaryRowChoice :=
  ⟨106, 70370354817024,
    [
    ]⟩

private def patternSummaryChoice0_14 : SummaryRowChoice :=
  ⟨170, 140740172752896,
    [
    ]⟩

private def patternSummaryChoice0_15 : SummaryRowChoice :=
  ⟨202, 36028800240240640,
    [
    ]⟩

private def patternSummaryChoice0_16 : SummaryRowChoice :=
  ⟨114, 70781061066752,
    [
    ]⟩

private def patternSummaryChoice0_17 : SummaryRowChoice :=
  ⟨178, 141424683167744,
    [
    ]⟩

private def patternSummaryChoice0_18 : SummaryRowChoice :=
  ⟨210, 36029621652738048,
    [
    ]⟩

private def patternSummaryChoice0_19 : SummaryRowChoice :=
  ⟨226, 36239903251554304,
    [
    ]⟩

private def patternSummaryChoice0_20 : SummaryRowChoice :=
  ⟨60, 138247929856,
    [
    ]⟩

private def patternSummaryChoice0_21 : SummaryRowChoice :=
  ⟨92, 276225851392,
    [
    ]⟩

private def patternSummaryChoice0_22 : SummaryRowChoice :=
  ⟨156, 552181694464,
    [
    ]⟩

private def patternSummaryChoice0_23 : SummaryRowChoice :=
  ⟨108, 70370361606144,
    [
    ]⟩

private def patternSummaryChoice0_24 : SummaryRowChoice :=
  ⟨172, 140740183719936,
    [
    ]⟩

private def patternSummaryChoice0_25 : SummaryRowChoice :=
  ⟨204, 36028800253296640,
    [
    ]⟩

private def patternSummaryChoice0_26 : SummaryRowChoice :=
  ⟨116, 70781068378112,
    [
    ]⟩

private def patternSummaryChoice0_27 : SummaryRowChoice :=
  ⟨180, 141424694657024,
    [
    ]⟩

private def patternSummaryChoice0_28 : SummaryRowChoice :=
  ⟨212, 36029621666316288,
    [
    ]⟩

private def patternSummaryChoice0_29 : SummaryRowChoice :=
  ⟨228, 36239903266177024,
    [
    ]⟩

private def patternSummaryChoice0_30 : SummaryRowChoice :=
  ⟨120, 70782940086272,
    [
    ]⟩

private def patternSummaryChoice0_31 : SummaryRowChoice :=
  ⟨184, 141427635912704,
    [
    ]⟩

private def patternSummaryChoice0_32 : SummaryRowChoice :=
  ⟨216, 36029625142345728,
    [
    ]⟩

private def patternSummaryChoice0_33 : SummaryRowChoice :=
  ⟨232, 36239907009593344,
    [
    ]⟩

private def patternSummaryChoice0_34 : SummaryRowChoice :=
  ⟨240, 36240865324171264,
    [
    ]⟩

/-- Row masks and compatible last-assigned pattern summaries for centre 0. -/
def patternSummaryChoices0 : List SummaryRowChoice := [
  patternSummaryChoice0_00,
  patternSummaryChoice0_01,
  patternSummaryChoice0_02,
  patternSummaryChoice0_03,
  patternSummaryChoice0_04,
  patternSummaryChoice0_05,
  patternSummaryChoice0_06,
  patternSummaryChoice0_07,
  patternSummaryChoice0_08,
  patternSummaryChoice0_09,
  patternSummaryChoice0_10,
  patternSummaryChoice0_11,
  patternSummaryChoice0_12,
  patternSummaryChoice0_13,
  patternSummaryChoice0_14,
  patternSummaryChoice0_15,
  patternSummaryChoice0_16,
  patternSummaryChoice0_17,
  patternSummaryChoice0_18,
  patternSummaryChoice0_19,
  patternSummaryChoice0_20,
  patternSummaryChoice0_21,
  patternSummaryChoice0_22,
  patternSummaryChoice0_23,
  patternSummaryChoice0_24,
  patternSummaryChoice0_25,
  patternSummaryChoice0_26,
  patternSummaryChoice0_27,
  patternSummaryChoice0_28,
  patternSummaryChoice0_29,
  patternSummaryChoice0_30,
  patternSummaryChoice0_31,
  patternSummaryChoice0_32,
  patternSummaryChoice0_33,
  patternSummaryChoice0_34
]

end Erdos97Octagon.RawIncidence
