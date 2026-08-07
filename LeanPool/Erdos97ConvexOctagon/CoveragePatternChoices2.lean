/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageSummaryTypes

/-! # Static pattern-summary choices for one incidence row -/

namespace Erdos97Octagon.RawIncidence

private def patternSummaryChoice2_00 : SummaryRowChoice :=
  ⟨27, 268441626,
    [
      [
        ⟨1, 1703962⟩,
        ⟨240, 593166⟩,
        ⟨241, 658702⟩,
        ⟨243, 723982⟩
      ]
    ]⟩

private def patternSummaryChoice2_01 : SummaryRowChoice :=
  ⟨43, 536881194,
    [
      [
        ⟨240, 593166⟩,
        ⟨241, 658702⟩,
        ⟨243, 723982⟩
      ]
    ]⟩

private def patternSummaryChoice2_02 : SummaryRowChoice :=
  ⟨75, 1073760330,
    [
      [
        ⟨240, 593166⟩,
        ⟨241, 658702⟩,
        ⟨243, 723982⟩
      ]
    ]⟩

private def patternSummaryChoice2_03 : SummaryRowChoice :=
  ⟨139, 2147518602,
    [
      [
        ⟨240, 593166⟩,
        ⟨241, 658702⟩,
        ⟨243, 723982⟩
      ]
    ]⟩

private def patternSummaryChoice2_04 : SummaryRowChoice :=
  ⟨51, 137438965810,
    [
    ]⟩

private def patternSummaryChoice2_05 : SummaryRowChoice :=
  ⟨83, 274877927506,
    [
    ]⟩

private def patternSummaryChoice2_06 : SummaryRowChoice :=
  ⟨147, 549755850898,
    [
    ]⟩

private def patternSummaryChoice2_07 : SummaryRowChoice :=
  ⟨99, 70368744202338,
    [
      [
        ⟨6, 6381824⟩
      ]
    ]⟩

private def patternSummaryChoice2_08 : SummaryRowChoice :=
  ⟨163, 140737488396450,
    [
      [
        ⟨11, 10592512⟩
      ]
    ]⟩

private def patternSummaryChoice2_09 : SummaryRowChoice :=
  ⟨195, 36028797019013314,
    [
      [
        ⟨14, 12697856⟩
      ]
    ]⟩

private def patternSummaryChoice2_10 : SummaryRowChoice :=
  ⟨57, 138244259896,
    [
      [
        ⟨240, 593166⟩
      ]
    ]⟩

private def patternSummaryChoice2_11 : SummaryRowChoice :=
  ⟨89, 276220084312,
    [
      [
        ⟨240, 593166⟩
      ]
    ]⟩

private def patternSummaryChoice2_12 : SummaryRowChoice :=
  ⟨153, 552171733144,
    [
      [
        ⟨240, 593166⟩
      ]
    ]⟩

private def patternSummaryChoice2_13 : SummaryRowChoice :=
  ⟨105, 70370354790504,
    [
      [
        ⟨6, 6381824⟩,
        ⟨7, 6842368⟩,
        ⟨240, 593166⟩
      ]
    ]⟩

private def patternSummaryChoice2_14 : SummaryRowChoice :=
  ⟨169, 140740172710056,
    [
      [
        ⟨11, 10592512⟩,
        ⟨240, 593166⟩
      ]
    ]⟩

private def patternSummaryChoice2_15 : SummaryRowChoice :=
  ⟨201, 36028800240189640,
    [
      [
        ⟨14, 12697856⟩,
        ⟨240, 593166⟩
      ]
    ]⟩

private def patternSummaryChoice2_16 : SummaryRowChoice :=
  ⟨113, 70781061038192,
    [
      [
        ⟨6, 6381824⟩
      ]
    ]⟩

private def patternSummaryChoice2_17 : SummaryRowChoice :=
  ⟨177, 141424683122864,
    [
      [
        ⟨11, 10592512⟩
      ]
    ]⟩

private def patternSummaryChoice2_18 : SummaryRowChoice :=
  ⟨209, 36029621652685008,
    [
      [
        ⟨14, 12697856⟩
      ]
    ]⟩

private def patternSummaryChoice2_19 : SummaryRowChoice :=
  ⟨225, 36239903251497184,
    [
      [
        ⟨6, 6381824⟩,
        ⟨11, 10592512⟩,
        ⟨14, 12697856⟩,
        ⟨17, 14737408⟩
      ]
    ]⟩

private def patternSummaryChoice2_20 : SummaryRowChoice :=
  ⟨58, 138244274176,
    [
      [
        ⟨1, 1703962⟩,
        ⟨241, 658702⟩
      ]
    ]⟩

private def patternSummaryChoice2_21 : SummaryRowChoice :=
  ⟨90, 276220106752,
    [
      [
        ⟨1, 1703962⟩,
        ⟨241, 658702⟩
      ]
    ]⟩

private def patternSummaryChoice2_22 : SummaryRowChoice :=
  ⟨154, 552171771904,
    [
      [
        ⟨1, 1703962⟩,
        ⟨241, 658702⟩
      ]
    ]⟩

private def patternSummaryChoice2_23 : SummaryRowChoice :=
  ⟨106, 70370354817024,
    [
      [
        ⟨7, 6842368⟩,
        ⟨241, 658702⟩
      ]
    ]⟩

private def patternSummaryChoice2_24 : SummaryRowChoice :=
  ⟨170, 140740172752896,
    [
      [
        ⟨241, 658702⟩
      ]
    ]⟩

private def patternSummaryChoice2_25 : SummaryRowChoice :=
  ⟨202, 36028800240240640,
    [
      [
        ⟨241, 658702⟩
      ]
    ]⟩

private def patternSummaryChoice2_26 : SummaryRowChoice :=
  ⟨114, 70781061066752,
    [
    ]⟩

private def patternSummaryChoice2_27 : SummaryRowChoice :=
  ⟨178, 141424683167744,
    [
    ]⟩

private def patternSummaryChoice2_28 : SummaryRowChoice :=
  ⟨210, 36029621652738048,
    [
    ]⟩

private def patternSummaryChoice2_29 : SummaryRowChoice :=
  ⟨226, 36239903251554304,
    [
      [
        ⟨17, 14737408⟩
      ]
    ]⟩

private def patternSummaryChoice2_30 : SummaryRowChoice :=
  ⟨120, 70782940086272,
    [
      [
        ⟨7, 6842368⟩
      ]
    ]⟩

private def patternSummaryChoice2_31 : SummaryRowChoice :=
  ⟨184, 141427635912704,
    [
    ]⟩

private def patternSummaryChoice2_32 : SummaryRowChoice :=
  ⟨216, 36029625142345728,
    [
    ]⟩

private def patternSummaryChoice2_33 : SummaryRowChoice :=
  ⟨232, 36239907009593344,
    [
      [
        ⟨7, 6842368⟩,
        ⟨17, 14737408⟩
      ]
    ]⟩

private def patternSummaryChoice2_34 : SummaryRowChoice :=
  ⟨240, 36240865324171264,
    [
      [
        ⟨17, 14737408⟩
      ]
    ]⟩

/-- Row masks and compatible last-assigned pattern summaries for centre 2. -/
def patternSummaryChoices2 : List SummaryRowChoice := [
  patternSummaryChoice2_00,
  patternSummaryChoice2_01,
  patternSummaryChoice2_02,
  patternSummaryChoice2_03,
  patternSummaryChoice2_04,
  patternSummaryChoice2_05,
  patternSummaryChoice2_06,
  patternSummaryChoice2_07,
  patternSummaryChoice2_08,
  patternSummaryChoice2_09,
  patternSummaryChoice2_10,
  patternSummaryChoice2_11,
  patternSummaryChoice2_12,
  patternSummaryChoice2_13,
  patternSummaryChoice2_14,
  patternSummaryChoice2_15,
  patternSummaryChoice2_16,
  patternSummaryChoice2_17,
  patternSummaryChoice2_18,
  patternSummaryChoice2_19,
  patternSummaryChoice2_20,
  patternSummaryChoice2_21,
  patternSummaryChoice2_22,
  patternSummaryChoice2_23,
  patternSummaryChoice2_24,
  patternSummaryChoice2_25,
  patternSummaryChoice2_26,
  patternSummaryChoice2_27,
  patternSummaryChoice2_28,
  patternSummaryChoice2_29,
  patternSummaryChoice2_30,
  patternSummaryChoice2_31,
  patternSummaryChoice2_32,
  patternSummaryChoice2_33,
  patternSummaryChoice2_34
]

end Erdos97Octagon.RawIncidence
