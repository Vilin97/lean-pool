/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132ConvexK3.Assembly
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Non-vacuity witnesses for indexed word realizations

Explicit real configurations inhabit each of the thirteen exceptional-word
realization predicates routed through the four shared closure families.
-/

namespace LeanPool.Erdos132ConvexK3.Witnesses

open LeanPool.Erdos132ConvexK3

/-! ## Non-vacuity witnesses for the exceptional-word realizations -/

/-- A rational terminal-cage pentagon in the intended cyclic order
`x, vertex, t, w, s`. -/
def terminalWordPoints : Fin 5 → Point ℝ :=
  fun i => match i.1 with
  | 0 => (0, 0)
  | 1 => (725, -29)
  | 2 => (2900, 0)
  | 3 => (1425, 2600)
  | _ => (725, 2900)

private theorem terminalWordPoints_injective : Function.Injective terminalWordPoints := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first | rfl | (exfalso; norm_num [terminalWordPoints] at hij)

private theorem terminalWordPoints_top_three :
    HasTopThreeDistanceClasses terminalWordPoints
      13140625 8935625 8790625 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · refine ⟨(2, 4), by decide, ?_⟩
    norm_num [terminalWordPoints, sqDist]
  · refine ⟨(0, 4), by decide, ?_⟩
    norm_num [terminalWordPoints, sqDist]
  · refine ⟨(0, 3), by decide, ?_⟩
    norm_num [terminalWordPoints, sqDist]
  · rintro ⟨i, j⟩ hij
    fin_cases i <;> fin_cases j
    all_goals norm_num [unorderedPairList, terminalWordPoints, sqDist] at *

private def terminalWordGeometry :
    Row1B32WordRealization terminalWordPoints
      13140625 8935625 8790625 := {
  pointsInjective := terminalWordPoints_injective
  classes := terminalWordPoints_top_three
  x := 0
  vertex := 1
  t := 2
  w := 3
  s := 4
  x_ne_vertex := by decide
  t_ne_vertex := by decide
  x_ne_t := by decide
  x_ne_w := by decide
  x_ne_s := by decide
  t_ne_w := by decide
  t_ne_s := by decide
  w_ne_s := by decide
  w_ne_vertex := by decide
  s_ne_vertex := by decide
  leftArc := {2}
  rightArc := {0}
  arcPartition := by
    intro j hj
    fin_cases j
    all_goals simp_all
  leftHalfPlane := by
    intro j hj
    fin_cases j
    all_goals simp_all
    all_goals norm_num [terminalWordPoints, InLeftOpenHalfPlane, turn]
  left_x_ne := by
    intro j hj
    fin_cases j
    all_goals simp_all
  rightHalfPlane := by
    intro j hj
    fin_cases j
    all_goals simp_all
    all_goals norm_num [terminalWordPoints, InLeftOpenHalfPlane, turn]
  right_t_ne := by
    intro j hj
    fin_cases j
    all_goals simp_all
  leftQuad := by
    intro j hj
    fin_cases j
    all_goals simp_all
    all_goals norm_num [terminalWordPoints, StrictConvexQuad, turn]
  rightQuad := by
    intro j hj
    fin_cases j
    all_goals simp_all
    all_goals norm_num [terminalWordPoints, StrictConvexQuad, turn]
  centralLeftQuad := by
    norm_num [terminalWordPoints, StrictConvexQuad, turn]
  centralRightQuad := by
    norm_num [terminalWordPoints, StrictConvexQuad, turn]
  terminalQuad := by
    norm_num [terminalWordPoints, StrictConvexQuad, turn]
  shortLeftQuad := by
    intro j hj
    fin_cases j
    all_goals simp_all
    all_goals norm_num [terminalWordPoints, StrictConvexQuad, turn]
  xw_le := by norm_num [terminalWordPoints, sqDist]
  xs := by norm_num [terminalWordPoints, sqDist]
  tw := by norm_num [terminalWordPoints, sqDist]
  ts := by norm_num [terminalWordPoints, sqDist]
}

/-- The terminal pentagon inhabits the row-1 `B:3→2` realization. -/
theorem row1_B32_realization_nonempty :
    WordRealization .row1_B32 terminalWordPoints 13140625 8935625 8790625 :=
  ⟨terminalWordGeometry⟩

/-- The terminal pentagon also inhabits the reflected row-4 `D:3→2` tag. -/
theorem row4_D32_realization_nonempty :
    WordRealization .row4_D32 terminalWordPoints 13140625 8935625 8790625 :=
  ⟨terminalWordGeometry⟩

/-- An integer-scaled rational shared-tip configuration in cyclic order
`e, vertex, t, w, s, r`. -/
def sharedTipPoints : Fin 6 → Point ℝ :=
  fun i => match i.1 with
  | 0 => (0, 0)
  | 1 => (559, -13)
  | 2 => (1300, 0)
  | 3 => (790, 1220)
  | 4 => (650, 1300)
  | _ => (510, 1220)

private theorem sharedTipPoints_injective : Function.Injective sharedTipPoints := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first | rfl | (exfalso; norm_num [sharedTipPoints] at hij)

private theorem sharedTipPoints_top_three :
    HasTopThreeDistanceClasses sharedTipPoints 2112500 1748500 1732250 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · refine ⟨(0, 4), by decide, ?_⟩
    norm_num [sharedTipPoints, sqDist]
  · refine ⟨(2, 3), by decide, ?_⟩
    norm_num [sharedTipPoints, sqDist]
  · refine ⟨(1, 4), by decide, ?_⟩
    norm_num [sharedTipPoints, sqDist]
  · rintro ⟨i, j⟩ hij
    fin_cases i <;> fin_cases j
    all_goals norm_num [unorderedPairList, sharedTipPoints, sqDist] at *

private def onePenultimateGeometry :
    OnePenultimateWordGeometry sharedTipPoints 2112500 1748500 1732250 := {
  pointsInjective := sharedTipPoints_injective
  classes := sharedTipPoints_top_three
  e := 0
  vertex := 1
  t := 2
  p := 3
  s := 4
  e_ne_vertex := by decide
  t_ne_vertex := by decide
  p_ne_vertex := by decide
  s_ne_vertex := by decide
  e_ne_t := by decide
  e_ne_s := by decide
  t_ne_p := by decide
  t_ne_s := by decide
  p_ne_s := by decide
  leftArc := {2, 3}
  rightArc := {0, 5}
  arcPartition := by
    intro j hj
    fin_cases j
    all_goals simp_all
  left_e_ne := by
    intro j hj
    fin_cases j
    all_goals simp_all
  right_t_ne := by
    intro j hj
    fin_cases j
    all_goals simp_all
  left_s_ne := by
    intro j hj
    fin_cases j
    all_goals simp_all
  right_s_ne := by
    intro j hj
    fin_cases j
    all_goals simp_all
  leftHalfPlane := by
    intro j hj
    fin_cases j
    all_goals simp_all
    all_goals norm_num [sharedTipPoints, InLeftOpenHalfPlane, turn]
  rightHalfPlane := by
    intro j hj
    fin_cases j
    all_goals simp_all
    all_goals norm_num [sharedTipPoints, InLeftOpenHalfPlane, turn]
  leftQuad := by
    intro j hj
    fin_cases j
    all_goals simp_all
    all_goals norm_num [sharedTipPoints, StrictConvexQuad, turn]
  rightQuad := by
    intro j hj
    fin_cases j
    all_goals simp_all
    all_goals norm_num [sharedTipPoints, StrictConvexQuad, turn]
  rungQuad := by norm_num [sharedTipPoints, StrictConvexQuad, turn]
  tipAbove := by norm_num [sharedTipPoints, turn]
  vertexBelow := by norm_num [sharedTipPoints, turn]
  es := by norm_num [sharedTipPoints, sqDist]
  ts := by norm_num [sharedTipPoints, sqDist]
  tp := by norm_num [sharedTipPoints, sqDist]
}

/-- The shared-tip hexagon inhabits the row-1 `B:3→1` realization. -/
theorem row1_B31_realization_nonempty :
    WordRealization .row1_B31 sharedTipPoints 2112500 1748500 1732250 :=
  ⟨onePenultimateGeometry⟩

/-- The shared-tip hexagon inhabits the row-2 `BA` realization. -/
theorem row2_BA_realization_nonempty :
    WordRealization .row2_BA sharedTipPoints 2112500 1748500 1732250 :=
  ⟨onePenultimateGeometry⟩

/-- The shared-tip hexagon inhabits the row-4 `D:3→1` realization. -/
theorem row4_D31_realization_nonempty :
    WordRealization .row4_D31 sharedTipPoints 2112500 1748500 1732250 :=
  ⟨onePenultimateGeometry⟩

/-- The shared-tip hexagon inhabits the row-4 `DC` realization. -/
theorem row4_DC_realization_nonempty :
    WordRealization .row4_DC sharedTipPoints 2112500 1748500 1732250 :=
  ⟨onePenultimateGeometry⟩

private def fullTwoRungGeometry :
    FullTwoRungGeometry sharedTipPoints 2112500 1748500 1732250 := {
  pointsInjective := sharedTipPoints_injective
  classes := sharedTipPoints_top_three
  e := 0
  t := 2
  s := 4
  w := 3
  r := 5
  vertex := 1
  endpoint := 0
  e_ne_t := by decide
  e_ne_s := by decide
  t_ne_s := by decide
  w_ne_s := by decide
  r_ne_s := by decide
  vertex_ne_e := by decide
  vertex_ne_t := by decide
  vertex_ne_s := by decide
  vertex_ne_w := by decide
  vertex_ne_r := by decide
  tipAbove := by norm_num [sharedTipPoints, turn]
  vertexBelow := by norm_num [sharedTipPoints, turn]
  wAbove := by norm_num [sharedTipPoints, turn]
  rAbove := by norm_num [sharedTipPoints, turn]
  wBelowTip := by norm_num [sharedTipPoints, turn]
  es := by norm_num [sharedTipPoints, sqDist]
  ts := by norm_num [sharedTipPoints, sqDist]
  ew := by norm_num [sharedTipPoints, sqDist]
  tw := by norm_num [sharedTipPoints, sqDist]
  er := by norm_num [sharedTipPoints, sqDist]
  tr := by norm_num [sharedTipPoints, sqDist]
  antiSaturationQuad := by norm_num [sharedTipPoints, StrictConvexQuad, turn]
  ePositiveArc := {2, 3}
  eNegativeArc := ∅
  tPositiveArc := ∅
  tNegativeArc := {5}
  arcPartition := by
    intro j hj
    fin_cases j
    all_goals simp_all
  ePositive_ne_tip := by
    intro j hj
    fin_cases j
    all_goals simp_all
  eNegative_ne_tip := by simp
  tPositive_ne_tip := by simp
  tNegative_ne_tip := by
    intro j hj
    fin_cases j
    all_goals simp_all
  ePositive_center_ne := by
    intro j hj
    fin_cases j
    all_goals simp_all
  eNegative_center_ne := by simp
  tPositive_center_ne := by simp
  tNegative_center_ne := by
    intro j hj
    fin_cases j
    all_goals simp_all
  ePositiveHalfPlane := by
    intro j hj
    fin_cases j
    all_goals simp_all
    all_goals norm_num [sharedTipPoints, InLeftOpenHalfPlane, turn]
  eNegativeHalfPlane := by simp
  tPositiveHalfPlane := by simp
  tNegativeHalfPlane := by
    intro j hj
    fin_cases j
    all_goals simp_all
    all_goals norm_num [sharedTipPoints, InLeftOpenHalfPlane, turn]
  ePositiveQuad := by
    intro j hj
    fin_cases j
    all_goals simp_all
    all_goals norm_num [sharedTipPoints, StrictConvexQuad, turn]
  eNegativeQuad := by simp
  tPositiveQuad := by simp
  tNegativeQuad := by
    intro j hj
    fin_cases j
    all_goals simp_all
    all_goals norm_num [sharedTipPoints, StrictConvexQuad, turn]
}

/-- The two-rung hexagon inhabits the row-1 `B:2→1` realization. -/
theorem row1_B21_realization_nonempty :
    WordRealization .row1_B21 sharedTipPoints 2112500 1748500 1732250 :=
  ⟨fullTwoRungGeometry⟩

/-- The two-rung hexagon inhabits the row-2 `AB` realization. -/
theorem row2_AB_realization_nonempty :
    WordRealization .row2_AB sharedTipPoints 2112500 1748500 1732250 :=
  ⟨fullTwoRungGeometry⟩

/-- The two-rung hexagon inhabits the row-3 `BB×DD` realization. -/
theorem row3_BB_DD_realization_nonempty :
    WordRealization .row3_BB_DD sharedTipPoints 2112500 1748500 1732250 :=
  ⟨fullTwoRungGeometry⟩

/-- The two-rung hexagon inhabits the row-4 `D:2→1` realization. -/
theorem row4_D21_realization_nonempty :
    WordRealization .row4_D21 sharedTipPoints 2112500 1748500 1732250 :=
  ⟨fullTwoRungGeometry⟩

/-- The two-rung hexagon inhabits the row-4 `CD` realization. -/
theorem row4_CD_realization_nonempty :
    WordRealization .row4_CD sharedTipPoints 2112500 1748500 1732250 :=
  ⟨fullTwoRungGeometry⟩

/-- The two-rung hexagon inhabits the row-5 `BB×DD` realization. -/
theorem row5_BB_DD_realization_nonempty :
    WordRealization .row5_BB_DD sharedTipPoints 2112500 1748500 1732250 :=
  ⟨fullTwoRungGeometry⟩

/-- A rational six-point four-edge cage with two distinct lower endpoints. -/
def fourEdgePoints : Fin 6 → Point ℝ :=
  fun i => match i.1 with
  | 0 => (0, 0)
  | 1 => (559, -13)
  | 2 => (741, -13)
  | 3 => (1300, 0)
  | 4 => (790, 1220)
  | _ => (510, 1220)

private theorem fourEdgePoints_injective : Function.Injective fourEdgePoints := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first | rfl | (exfalso; norm_num [fourEdgePoints] at hij)

private theorem fourEdgePoints_top_three :
    HasTopThreeDistanceClasses fourEdgePoints 2112500 1748500 1690000 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · refine ⟨(0, 4), by decide, ?_⟩
    norm_num [fourEdgePoints, sqDist]
  · refine ⟨(0, 5), by decide, ?_⟩
    norm_num [fourEdgePoints, sqDist]
  · refine ⟨(0, 3), by decide, ?_⟩
    norm_num [fourEdgePoints, sqDist]
  · rintro ⟨i, j⟩ hij
    fin_cases i <;> fin_cases j
    all_goals norm_num [unorderedPairList, fourEdgePoints, sqDist] at *

private def fourEdgeFirstLeft :
    FourEdgeBranchGeometry fourEdgePoints 2112500 1 0 4 := {
  arc := {2, 3}
  center_ne_vertex := by decide
  center_ne_arc := by
    intro j hj
    fin_cases j
    all_goals simp_all
  halfPlane := Or.inl (by
    intro j hj
    fin_cases j
    all_goals simp_all
    all_goals norm_num [fourEdgePoints, InLeftOpenHalfPlane, turn])
  quad := by
    intro j hj
    fin_cases j
    all_goals simp_all
    all_goals norm_num [fourEdgePoints, StrictConvexQuad, turn]
  diameterEdge := by norm_num [fourEdgePoints, sqDist]
}

private def fourEdgeFirstRight :
    FourEdgeBranchGeometry fourEdgePoints 2112500 1 3 5 := {
  arc := {0}
  center_ne_vertex := by decide
  center_ne_arc := by
    intro j hj
    fin_cases j
    all_goals simp_all
  halfPlane := Or.inr (by
    intro j hj
    fin_cases j
    all_goals simp_all
    all_goals norm_num [fourEdgePoints, InLeftOpenHalfPlane, turn])
  quad := by
    intro j hj
    fin_cases j
    all_goals simp_all
    all_goals norm_num [fourEdgePoints, StrictConvexQuad, turn]
  diameterEdge := by norm_num [fourEdgePoints, sqDist]
}

private def fourEdgeSecondLeft :
    FourEdgeBranchGeometry fourEdgePoints 2112500 2 0 4 := {
  arc := {3}
  center_ne_vertex := by decide
  center_ne_arc := by
    intro j hj
    fin_cases j
    all_goals simp_all
  halfPlane := Or.inl (by
    intro j hj
    fin_cases j
    all_goals simp_all
    all_goals norm_num [fourEdgePoints, InLeftOpenHalfPlane, turn])
  quad := by
    intro j hj
    fin_cases j
    all_goals simp_all
    all_goals norm_num [fourEdgePoints, StrictConvexQuad, turn]
  diameterEdge := by norm_num [fourEdgePoints, sqDist]
}

private def fourEdgeSecondRight :
    FourEdgeBranchGeometry fourEdgePoints 2112500 2 3 5 := {
  arc := {0, 1}
  center_ne_vertex := by decide
  center_ne_arc := by
    intro j hj
    fin_cases j
    all_goals simp_all
  halfPlane := Or.inr (by
    intro j hj
    fin_cases j
    all_goals simp_all
    all_goals norm_num [fourEdgePoints, InLeftOpenHalfPlane, turn])
  quad := by
    intro j hj
    fin_cases j
    all_goals simp_all
    all_goals norm_num [fourEdgePoints, StrictConvexQuad, turn]
  diameterEdge := by norm_num [fourEdgePoints, sqDist]
}

private def fourEdgeFirstEndpoint :
    FourEdgeEndpointGeometry fourEdgePoints 2112500 1748500 1690000 0 3 4 5 := {
  vertex := 1
  w_ne_vertex := by decide
  s_ne_vertex := by decide
  left := fourEdgeFirstLeft
  right := fourEdgeFirstRight
  arcPartition := by
    intro j hj
    fin_cases j
    all_goals simp_all [fourEdgeFirstLeft, fourEdgeFirstRight]
}

private def fourEdgeSecondEndpoint :
    FourEdgeEndpointGeometry fourEdgePoints 2112500 1748500 1690000 0 3 4 5 := {
  vertex := 2
  w_ne_vertex := by decide
  s_ne_vertex := by decide
  left := fourEdgeSecondLeft
  right := fourEdgeSecondRight
  arcPartition := by
    intro j hj
    fin_cases j
    all_goals simp_all [fourEdgeSecondLeft, fourEdgeSecondRight]
}

private def fourEdgeWordGeometry :
    Row4DDWordRealization fourEdgePoints 2112500 1748500 1690000 := {
  pointsInjective := fourEdgePoints_injective
  classes := fourEdgePoints_top_three
  x := 0
  t := 3
  w := 4
  s := 5
  w_ne_s := by decide
  x_ne_w := by decide
  x_ne_s := by decide
  t_ne_w := by decide
  t_ne_s := by decide
  first := fourEdgeFirstEndpoint
  second := fourEdgeSecondEndpoint
  first_ne_second := by decide
  xSide := by norm_num [fourEdgePoints, InLeftOpenHalfPlane, turn]
  tSide := by norm_num [fourEdgePoints, InLeftOpenHalfPlane, turn]
  firstSide := by norm_num [fourEdgeFirstEndpoint, fourEdgePoints,
    InLeftOpenHalfPlane, turn]
  secondSide := by norm_num [fourEdgeSecondEndpoint, fourEdgePoints,
    InLeftOpenHalfPlane, turn]
  xw := by norm_num [fourEdgePoints, sqDist]
  xs := by norm_num [fourEdgePoints, sqDist]
  tw := by norm_num [fourEdgePoints, sqDist]
  ts := by norm_num [fourEdgePoints, sqDist]
}

/-- The explicit four-edge cage inhabits the row-4 `DD` realization. -/
theorem row4_DD_realization_nonempty :
    WordRealization .row4_DD fourEdgePoints 2112500 1748500 1690000 :=
  ⟨fourEdgeWordGeometry⟩

end LeanPool.Erdos132ConvexK3.Witnesses
