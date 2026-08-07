/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageSummaryTypes

/-! # Static pattern-summary choices for one incidence row -/

namespace Erdos97Octagon.RawIncidence

private def patternSummaryChoice3_00 : SummaryRowChoice :=
  ⟨23, 1053718,
    [
      [
        ⟨257, 286851100⟩,
        ⟨770, 50922766⟩,
        ⟨771, 50924558⟩,
        ⟨772, 50988302⟩,
        ⟨261, 337182748⟩,
        ⟨773, 50990094⟩,
        ⟨262, 353435676⟩,
        ⟨263, 353894428⟩
      ],
      [
        ⟨775, 84085774⟩,
        ⟨777, 84544526⟩,
        ⟨779, 100862990⟩,
        ⟨780, 101254414⟩,
        ⟨781, 101256206⟩,
        ⟨18, 369098774⟩,
        ⟨1401, 353502494⟩,
        ⟨248, 51052558⟩
      ],
      [
        ⟨249, 83889422⟩,
        ⟨250, 100666638⟩,
        ⟨251, 101384206⟩,
        ⟨252, 117441806⟩,
        ⟨253, 117443598⟩,
        ⟨254, 117637134⟩,
        ⟨255, 118095886⟩
      ]
    ]⟩

private def patternSummaryChoice3_01 : SummaryRowChoice :=
  ⟨39, 2106406,
    [
      [
        ⟨770, 50922766⟩,
        ⟨771, 50924558⟩,
        ⟨772, 50988302⟩,
        ⟨773, 50990094⟩,
        ⟨775, 84085774⟩,
        ⟨265, 606743552⟩,
        ⟨777, 84544526⟩,
        ⟨779, 100862990⟩
      ],
      [
        ⟨780, 101254414⟩,
        ⟨781, 101256206⟩,
        ⟨19, 589496320⟩,
        ⟨20, 620766464⟩,
        ⟨248, 51052558⟩,
        ⟨249, 83889422⟩,
        ⟨250, 100666638⟩,
        ⟨251, 101384206⟩
      ],
      [
        ⟨252, 117441806⟩,
        ⟨253, 117443598⟩,
        ⟨254, 117637134⟩,
        ⟨255, 118095886⟩
      ]
    ]⟩

private def patternSummaryChoice3_02 : SummaryRowChoice :=
  ⟨71, 4211782,
    [
      [
        ⟨770, 50922766⟩,
        ⟨771, 50924558⟩,
        ⟨772, 50988302⟩,
        ⟨773, 50990094⟩,
        ⟨775, 84085774⟩,
        ⟨777, 84544526⟩,
        ⟨779, 100862990⟩,
        ⟨780, 101254414⟩
      ],
      [
        ⟨781, 101256206⟩,
        ⟨270, 1112165376⟩,
        ⟨23, 1128464384⟩,
        ⟨24, 1157645568⟩,
        ⟨248, 51052558⟩,
        ⟨249, 83889422⟩,
        ⟨250, 100666638⟩,
        ⟨251, 101384206⟩
      ],
      [
        ⟨252, 117441806⟩,
        ⟨253, 117443598⟩,
        ⟨254, 117637134⟩,
        ⟨255, 118095886⟩
      ]
    ]⟩

private def patternSummaryChoice3_03 : SummaryRowChoice :=
  ⟨135, 8422534,
    [
      [
        ⟨770, 50922766⟩,
        ⟨771, 50924558⟩,
        ⟨772, 50988302⟩,
        ⟨773, 50990094⟩,
        ⟨775, 84085774⟩,
        ⟨777, 84544526⟩,
        ⟨779, 100862990⟩,
        ⟨780, 101254414⟩
      ],
      [
        ⟨781, 101256206⟩,
        ⟨33, 2206400512⟩,
        ⟨248, 51052558⟩,
        ⟨249, 83889422⟩,
        ⟨250, 100666638⟩,
        ⟨251, 101384206⟩,
        ⟨252, 117441806⟩,
        ⟨253, 117443598⟩
      ],
      [
        ⟨254, 117637134⟩,
        ⟨255, 118095886⟩
      ]
    ]⟩

private def patternSummaryChoice3_04 : SummaryRowChoice :=
  ⟨51, 137438965810,
    [
      [
        ⟨257, 286851100⟩,
        ⟨770, 50922766⟩,
        ⟨771, 50924558⟩,
        ⟨772, 50988302⟩,
        ⟨773, 50990094⟩,
        ⟨19, 589496320⟩,
        ⟨22, 825294848⟩,
        ⟨248, 51052558⟩
      ]
    ]⟩

private def patternSummaryChoice3_05 : SummaryRowChoice :=
  ⟨83, 274877927506,
    [
      [
        ⟨257, 286851100⟩,
        ⟨770, 50922766⟩,
        ⟨771, 50924558⟩,
        ⟨772, 50988302⟩,
        ⟨773, 50990094⟩,
        ⟨270, 1112165376⟩,
        ⟨23, 1128464384⟩,
        ⟨26, 1364262912⟩
      ],
      [
        ⟨248, 51052558⟩
      ]
    ]⟩

private def patternSummaryChoice3_06 : SummaryRowChoice :=
  ⟨147, 549755850898,
    [
      [
        ⟨257, 286851100⟩,
        ⟨770, 50922766⟩,
        ⟨771, 50924558⟩,
        ⟨772, 50988302⟩,
        ⟨773, 50990094⟩,
        ⟨33, 2206400512⟩,
        ⟨36, 2442199040⟩,
        ⟨248, 51052558⟩
      ]
    ]⟩

private def patternSummaryChoice3_07 : SummaryRowChoice :=
  ⟨99, 70368744202338,
    [
      [
        ⟨770, 50922766⟩,
        ⟨771, 50924558⟩,
        ⟨772, 50988302⟩,
        ⟨773, 50990094⟩,
        ⟨270, 1112165376⟩,
        ⟨19, 589496320⟩,
        ⟨23, 1128464384⟩,
        ⟨27, 1627414784⟩
      ],
      [
        ⟨29, 1650589696⟩,
        ⟨248, 51052558⟩
      ]
    ]⟩

private def patternSummaryChoice3_08 : SummaryRowChoice :=
  ⟨163, 140737488396450,
    [
      [
        ⟨770, 50922766⟩,
        ⟨771, 50924558⟩,
        ⟨772, 50988302⟩,
        ⟨773, 50990094⟩,
        ⟨19, 589496320⟩,
        ⟨33, 2206400512⟩,
        ⟨37, 2701172992⟩,
        ⟨38, 2711683072⟩
      ],
      [
        ⟨39, 2728525824⟩,
        ⟨248, 51052558⟩
      ]
    ]⟩

private def patternSummaryChoice3_09 : SummaryRowChoice :=
  ⟨195, 36028797019013314,
    [
      [
        ⟨770, 50922766⟩,
        ⟨771, 50924558⟩,
        ⟨772, 50988302⟩,
        ⟨773, 50990094⟩,
        ⟨270, 1112165376⟩,
        ⟨23, 1128464384⟩,
        ⟨33, 2206400512⟩,
        ⟨43, 3238052096⟩
      ],
      [
        ⟨44, 3250651136⟩,
        ⟨45, 3267493888⟩,
        ⟨248, 51052558⟩
      ]
    ]⟩

private def patternSummaryChoice3_10 : SummaryRowChoice :=
  ⟨53, 137442099252,
    [
      [
        ⟨257, 286851100⟩,
        ⟨261, 337182748⟩,
        ⟨262, 353435676⟩,
        ⟨263, 353894428⟩,
        ⟨775, 84085774⟩,
        ⟨265, 606743552⟩,
        ⟨777, 84544526⟩,
        ⟨20, 620766464⟩
      ],
      [
        ⟨22, 825294848⟩,
        ⟨1401, 353502494⟩,
        ⟨249, 83889422⟩
      ]
    ]⟩

private def patternSummaryChoice3_11 : SummaryRowChoice :=
  ⟨85, 274883149908,
    [
      [
        ⟨257, 286851100⟩,
        ⟨261, 337182748⟩,
        ⟨262, 353435676⟩,
        ⟨263, 353894428⟩,
        ⟨775, 84085774⟩,
        ⟨777, 84544526⟩,
        ⟨24, 1157645568⟩,
        ⟨26, 1364262912⟩
      ],
      [
        ⟨1401, 353502494⟩,
        ⟨249, 83889422⟩
      ]
    ]⟩

private def patternSummaryChoice3_12 : SummaryRowChoice :=
  ⟨149, 549765251220,
    [
      [
        ⟨257, 286851100⟩,
        ⟨261, 337182748⟩,
        ⟨262, 353435676⟩,
        ⟨263, 353894428⟩,
        ⟨775, 84085774⟩,
        ⟨777, 84544526⟩,
        ⟨36, 2442199040⟩,
        ⟨1401, 353502494⟩
      ],
      [
        ⟨249, 83889422⟩
      ]
    ]⟩

private def patternSummaryChoice3_13 : SummaryRowChoice :=
  ⟨101, 70368750469220,
    [
      [
        ⟨775, 84085774⟩,
        ⟨265, 606743552⟩,
        ⟨777, 84544526⟩,
        ⟨20, 620766464⟩,
        ⟨24, 1157645568⟩,
        ⟨27, 1627414784⟩,
        ⟨30, 1677747200⟩,
        ⟨249, 83889422⟩
      ]
    ]⟩

private def patternSummaryChoice3_14 : SummaryRowChoice :=
  ⟨165, 140737498841252,
    [
      [
        ⟨775, 84085774⟩,
        ⟨265, 606743552⟩,
        ⟨777, 84544526⟩,
        ⟨20, 620766464⟩,
        ⟨37, 2701172992⟩,
        ⟨38, 2711683072⟩,
        ⟨40, 2751505408⟩,
        ⟨249, 83889422⟩
      ]
    ]⟩

private def patternSummaryChoice3_15 : SummaryRowChoice :=
  ⟨197, 36028797031547076,
    [
      [
        ⟨775, 84085774⟩,
        ⟨777, 84544526⟩,
        ⟨24, 1157645568⟩,
        ⟨43, 3238052096⟩,
        ⟨44, 3250651136⟩,
        ⟨46, 3288384512⟩,
        ⟨249, 83889422⟩
      ]
    ]⟩

private def patternSummaryChoice3_16 : SummaryRowChoice :=
  ⟨113, 70781061038192,
    [
      [
        ⟨257, 286851100⟩,
        ⟨22, 825294848⟩,
        ⟨26, 1364262912⟩,
        ⟨27, 1627414784⟩,
        ⟨32, 1886388224⟩
      ]
    ]⟩

private def patternSummaryChoice3_17 : SummaryRowChoice :=
  ⟨177, 141424683122864,
    [
      [
        ⟨257, 286851100⟩,
        ⟨22, 825294848⟩,
        ⟨36, 2442199040⟩,
        ⟨37, 2701172992⟩,
        ⟨38, 2711683072⟩,
        ⟨42, 2964324352⟩
      ]
    ]⟩

private def patternSummaryChoice3_18 : SummaryRowChoice :=
  ⟨209, 36029621652685008,
    [
      [
        ⟨257, 286851100⟩,
        ⟨26, 1364262912⟩,
        ⟨36, 2442199040⟩,
        ⟨43, 3238052096⟩,
        ⟨44, 3250651136⟩,
        ⟨48, 3503292416⟩
      ]
    ]⟩

private def patternSummaryChoice3_19 : SummaryRowChoice :=
  ⟨225, 36239903251497184,
    [
      [
        ⟨27, 1627414784⟩,
        ⟨37, 2701172992⟩,
        ⟨38, 2711683072⟩,
        ⟨43, 3238052096⟩,
        ⟨44, 3250651136⟩,
        ⟨49, 3758153728⟩,
        ⟨50, 3772776448⟩
      ]
    ]⟩

private def patternSummaryChoice3_20 : SummaryRowChoice :=
  ⟨54, 137442112512,
    [
      [
        ⟨261, 337182748⟩,
        ⟨265, 606743552⟩,
        ⟨779, 100862990⟩,
        ⟨780, 101254414⟩,
        ⟨781, 101256206⟩,
        ⟨18, 369098774⟩,
        ⟨250, 100666638⟩,
        ⟨251, 101384206⟩
      ]
    ]⟩

private def patternSummaryChoice3_21 : SummaryRowChoice :=
  ⟨86, 274883171328,
    [
      [
        ⟨261, 337182748⟩,
        ⟨779, 100862990⟩,
        ⟨780, 101254414⟩,
        ⟨781, 101256206⟩,
        ⟨270, 1112165376⟩,
        ⟨18, 369098774⟩,
        ⟨250, 100666638⟩,
        ⟨251, 101384206⟩
      ]
    ]⟩

private def patternSummaryChoice3_22 : SummaryRowChoice :=
  ⟨150, 549765288960,
    [
      [
        ⟨261, 337182748⟩,
        ⟨779, 100862990⟩,
        ⟨780, 101254414⟩,
        ⟨781, 101256206⟩,
        ⟨18, 369098774⟩,
        ⟨250, 100666638⟩,
        ⟨251, 101384206⟩
      ]
    ]⟩

private def patternSummaryChoice3_23 : SummaryRowChoice :=
  ⟨102, 70368750494720,
    [
      [
        ⟨265, 606743552⟩,
        ⟨779, 100862990⟩,
        ⟨780, 101254414⟩,
        ⟨781, 101256206⟩,
        ⟨270, 1112165376⟩,
        ⟨29, 1650589696⟩,
        ⟨30, 1677747200⟩,
        ⟨250, 100666638⟩
      ],
      [
        ⟨251, 101384206⟩
      ]
    ]⟩

private def patternSummaryChoice3_24 : SummaryRowChoice :=
  ⟨166, 140737498883072,
    [
      [
        ⟨265, 606743552⟩,
        ⟨779, 100862990⟩,
        ⟨780, 101254414⟩,
        ⟨781, 101256206⟩,
        ⟨39, 2728525824⟩,
        ⟨40, 2751505408⟩,
        ⟨250, 100666638⟩,
        ⟨251, 101384206⟩
      ]
    ]⟩

private def patternSummaryChoice3_25 : SummaryRowChoice :=
  ⟨198, 36028797031597056,
    [
      [
        ⟨779, 100862990⟩,
        ⟨780, 101254414⟩,
        ⟨781, 101256206⟩,
        ⟨270, 1112165376⟩,
        ⟨45, 3267493888⟩,
        ⟨46, 3288384512⟩,
        ⟨250, 100666638⟩,
        ⟨251, 101384206⟩
      ]
    ]⟩

private def patternSummaryChoice3_26 : SummaryRowChoice :=
  ⟨114, 70781061066752,
    [
      [
        ⟨270, 1112165376⟩,
        ⟨29, 1650589696⟩,
        ⟨32, 1886388224⟩
      ]
    ]⟩

private def patternSummaryChoice3_27 : SummaryRowChoice :=
  ⟨178, 141424683167744,
    [
      [
        ⟨39, 2728525824⟩,
        ⟨42, 2964324352⟩
      ]
    ]⟩

private def patternSummaryChoice3_28 : SummaryRowChoice :=
  ⟨210, 36029621652738048,
    [
      [
        ⟨270, 1112165376⟩,
        ⟨45, 3267493888⟩,
        ⟨48, 3503292416⟩
      ]
    ]⟩

private def patternSummaryChoice3_29 : SummaryRowChoice :=
  ⟨226, 36239903251554304,
    [
      [
        ⟨270, 1112165376⟩,
        ⟨29, 1650589696⟩,
        ⟨39, 2728525824⟩,
        ⟨45, 3267493888⟩,
        ⟨49, 3758153728⟩,
        ⟨50, 3772776448⟩
      ]
    ]⟩

private def patternSummaryChoice3_30 : SummaryRowChoice :=
  ⟨116, 70781068378112,
    [
      [
        ⟨261, 337182748⟩,
        ⟨265, 606743552⟩,
        ⟨30, 1677747200⟩,
        ⟨32, 1886388224⟩
      ]
    ]⟩

private def patternSummaryChoice3_31 : SummaryRowChoice :=
  ⟨180, 141424694657024,
    [
      [
        ⟨261, 337182748⟩,
        ⟨265, 606743552⟩,
        ⟨40, 2751505408⟩,
        ⟨42, 2964324352⟩
      ]
    ]⟩

private def patternSummaryChoice3_32 : SummaryRowChoice :=
  ⟨212, 36029621666316288,
    [
      [
        ⟨261, 337182748⟩,
        ⟨46, 3288384512⟩,
        ⟨48, 3503292416⟩
      ]
    ]⟩

private def patternSummaryChoice3_33 : SummaryRowChoice :=
  ⟨228, 36239903266177024,
    [
      [
        ⟨265, 606743552⟩,
        ⟨30, 1677747200⟩,
        ⟨40, 2751505408⟩,
        ⟨46, 3288384512⟩,
        ⟨49, 3758153728⟩,
        ⟨50, 3772776448⟩
      ]
    ]⟩

private def patternSummaryChoice3_34 : SummaryRowChoice :=
  ⟨240, 36240865324171264,
    [
      [
        ⟨32, 1886388224⟩,
        ⟨42, 2964324352⟩,
        ⟨48, 3503292416⟩,
        ⟨49, 3758153728⟩,
        ⟨50, 3772776448⟩
      ]
    ]⟩

/-- Row masks and compatible last-assigned pattern summaries for centre 3. -/
def patternSummaryChoices3 : List SummaryRowChoice := [
  patternSummaryChoice3_00,
  patternSummaryChoice3_01,
  patternSummaryChoice3_02,
  patternSummaryChoice3_03,
  patternSummaryChoice3_04,
  patternSummaryChoice3_05,
  patternSummaryChoice3_06,
  patternSummaryChoice3_07,
  patternSummaryChoice3_08,
  patternSummaryChoice3_09,
  patternSummaryChoice3_10,
  patternSummaryChoice3_11,
  patternSummaryChoice3_12,
  patternSummaryChoice3_13,
  patternSummaryChoice3_14,
  patternSummaryChoice3_15,
  patternSummaryChoice3_16,
  patternSummaryChoice3_17,
  patternSummaryChoice3_18,
  patternSummaryChoice3_19,
  patternSummaryChoice3_20,
  patternSummaryChoice3_21,
  patternSummaryChoice3_22,
  patternSummaryChoice3_23,
  patternSummaryChoice3_24,
  patternSummaryChoice3_25,
  patternSummaryChoice3_26,
  patternSummaryChoice3_27,
  patternSummaryChoice3_28,
  patternSummaryChoice3_29,
  patternSummaryChoice3_30,
  patternSummaryChoice3_31,
  patternSummaryChoice3_32,
  patternSummaryChoice3_33,
  patternSummaryChoice3_34
]

end Erdos97Octagon.RawIncidence
