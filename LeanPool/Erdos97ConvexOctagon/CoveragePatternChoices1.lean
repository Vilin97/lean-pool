/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageSummaryTypes

/-! # Static pattern-summary choices for one incidence row -/

namespace Erdos97Octagon.RawIncidence

private def patternSummaryChoice1_00 : SummaryRowChoice :=
  ⟨29, 270008348,
    [
      [
        ⟨0, 7196⟩
      ]
    ]⟩

private def patternSummaryChoice1_01 : SummaryRowChoice :=
  ⟨45, 539492396,
    [
    ]⟩

private def patternSummaryChoice1_02 : SummaryRowChoice :=
  ⟨77, 1078460492,
    [
    ]⟩

private def patternSummaryChoice1_03 : SummaryRowChoice :=
  ⟨141, 2156396684,
    [
    ]⟩

private def patternSummaryChoice1_04 : SummaryRowChoice :=
  ⟨53, 137442099252,
    [
    ]⟩

private def patternSummaryChoice1_05 : SummaryRowChoice :=
  ⟨85, 274883149908,
    [
    ]⟩

private def patternSummaryChoice1_06 : SummaryRowChoice :=
  ⟨149, 549765251220,
    [
    ]⟩

private def patternSummaryChoice1_07 : SummaryRowChoice :=
  ⟨101, 70368750469220,
    [
    ]⟩

private def patternSummaryChoice1_08 : SummaryRowChoice :=
  ⟨165, 140737498841252,
    [
    ]⟩

private def patternSummaryChoice1_09 : SummaryRowChoice :=
  ⟨197, 36028797031547076,
    [
    ]⟩

private def patternSummaryChoice1_10 : SummaryRowChoice :=
  ⟨57, 138244259896,
    [
    ]⟩

private def patternSummaryChoice1_11 : SummaryRowChoice :=
  ⟨89, 276220084312,
    [
    ]⟩

private def patternSummaryChoice1_12 : SummaryRowChoice :=
  ⟨153, 552171733144,
    [
    ]⟩

private def patternSummaryChoice1_13 : SummaryRowChoice :=
  ⟨105, 70370354790504,
    [
    ]⟩

private def patternSummaryChoice1_14 : SummaryRowChoice :=
  ⟨169, 140740172710056,
    [
    ]⟩

private def patternSummaryChoice1_15 : SummaryRowChoice :=
  ⟨201, 36028800240189640,
    [
    ]⟩

private def patternSummaryChoice1_16 : SummaryRowChoice :=
  ⟨113, 70781061038192,
    [
    ]⟩

private def patternSummaryChoice1_17 : SummaryRowChoice :=
  ⟨177, 141424683122864,
    [
    ]⟩

private def patternSummaryChoice1_18 : SummaryRowChoice :=
  ⟨209, 36029621652685008,
    [
    ]⟩

private def patternSummaryChoice1_19 : SummaryRowChoice :=
  ⟨225, 36239903251497184,
    [
    ]⟩

private def patternSummaryChoice1_20 : SummaryRowChoice :=
  ⟨60, 138247929856,
    [
      [
        ⟨0, 7196⟩
      ]
    ]⟩

private def patternSummaryChoice1_21 : SummaryRowChoice :=
  ⟨92, 276225851392,
    [
      [
        ⟨0, 7196⟩
      ]
    ]⟩

private def patternSummaryChoice1_22 : SummaryRowChoice :=
  ⟨156, 552181694464,
    [
      [
        ⟨0, 7196⟩
      ]
    ]⟩

private def patternSummaryChoice1_23 : SummaryRowChoice :=
  ⟨108, 70370361606144,
    [
    ]⟩

private def patternSummaryChoice1_24 : SummaryRowChoice :=
  ⟨172, 140740183719936,
    [
    ]⟩

private def patternSummaryChoice1_25 : SummaryRowChoice :=
  ⟨204, 36028800253296640,
    [
    ]⟩

private def patternSummaryChoice1_26 : SummaryRowChoice :=
  ⟨116, 70781068378112,
    [
    ]⟩

private def patternSummaryChoice1_27 : SummaryRowChoice :=
  ⟨180, 141424694657024,
    [
    ]⟩

private def patternSummaryChoice1_28 : SummaryRowChoice :=
  ⟨212, 36029621666316288,
    [
    ]⟩

private def patternSummaryChoice1_29 : SummaryRowChoice :=
  ⟨228, 36239903266177024,
    [
    ]⟩

private def patternSummaryChoice1_30 : SummaryRowChoice :=
  ⟨120, 70782940086272,
    [
    ]⟩

private def patternSummaryChoice1_31 : SummaryRowChoice :=
  ⟨184, 141427635912704,
    [
    ]⟩

private def patternSummaryChoice1_32 : SummaryRowChoice :=
  ⟨216, 36029625142345728,
    [
    ]⟩

private def patternSummaryChoice1_33 : SummaryRowChoice :=
  ⟨232, 36239907009593344,
    [
    ]⟩

private def patternSummaryChoice1_34 : SummaryRowChoice :=
  ⟨240, 36240865324171264,
    [
    ]⟩

/-- Row masks and compatible last-assigned pattern summaries for centre 1. -/
def patternSummaryChoices1 : List SummaryRowChoice := [
  patternSummaryChoice1_00,
  patternSummaryChoice1_01,
  patternSummaryChoice1_02,
  patternSummaryChoice1_03,
  patternSummaryChoice1_04,
  patternSummaryChoice1_05,
  patternSummaryChoice1_06,
  patternSummaryChoice1_07,
  patternSummaryChoice1_08,
  patternSummaryChoice1_09,
  patternSummaryChoice1_10,
  patternSummaryChoice1_11,
  patternSummaryChoice1_12,
  patternSummaryChoice1_13,
  patternSummaryChoice1_14,
  patternSummaryChoice1_15,
  patternSummaryChoice1_16,
  patternSummaryChoice1_17,
  patternSummaryChoice1_18,
  patternSummaryChoice1_19,
  patternSummaryChoice1_20,
  patternSummaryChoice1_21,
  patternSummaryChoice1_22,
  patternSummaryChoice1_23,
  patternSummaryChoice1_24,
  patternSummaryChoice1_25,
  patternSummaryChoice1_26,
  patternSummaryChoice1_27,
  patternSummaryChoice1_28,
  patternSummaryChoice1_29,
  patternSummaryChoice1_30,
  patternSummaryChoice1_31,
  patternSummaryChoice1_32,
  patternSummaryChoice1_33,
  patternSummaryChoice1_34
]

end Erdos97Octagon.RawIncidence
