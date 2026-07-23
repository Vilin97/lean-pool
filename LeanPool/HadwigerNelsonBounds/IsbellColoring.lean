/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.LatticeSeparation
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Isbell's seven-coloring

This module proves the numerical gap estimates, constructs the plane coloring,
and establishes the seven-color upper bound.
-/

namespace HadwigerNelsonBounds

open SimpleGraph

/-! ### Numerical inequalities -/

/-- `0 < √3`. -/
private lemma sqrt_three_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

/-- `0 < √7`. -/
private lemma sqrt_seven_pos : 0 < Real.sqrt 7 := Real.sqrt_pos.mpr (by norm_num)

/-- `√3 < 2`. -/
private lemma sqrt_three_lt_two : Real.sqrt 3 < 2 := by
  have h2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  nlinarith [h2, hpos]

/-- The within-tile diameter `2·(a/√3) = √3/2` is `< 1`. -/
lemma isbell_voronoi_diameter_lt_one :
    2 * (isbellLatticeStep / Real.sqrt 3) < 1 := by
  unfold isbellLatticeStep
  -- Reduce: 2·(3/4)/√3 = 3/(2·√3) = √3/2. Show √3/2 < 1, i.e. √3 < 2.
  have hs3 : 0 < Real.sqrt 3 := sqrt_three_pos
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt_three_mul_self
  have hlt : Real.sqrt 3 < 2 := sqrt_three_lt_two
  -- Rationalizing gives 2·(3/4)/√3 = √3/2, which is less than one.
  have key : 2 * (3 / 4 / Real.sqrt 3) = Real.sqrt 3 / 2 := by
    have : (3 : ℝ) / 4 / Real.sqrt 3 = 3 / (4 * Real.sqrt 3) := by ring
    rw [this]
    field_simp
    nlinarith [hsq]
  rw [key]
  linarith [hlt]

/-- The same-color spacing `a·(√7 − 2/√3) > 1` for `a = 3/4`. -/
lemma isbell_same_color_min_gt_one :
    isbellLatticeStep * (Real.sqrt 7 - 2 / Real.sqrt 3) > 1 := by
  unfold isbellLatticeStep
  -- It is enough to prove 3√7 > 4 + 2√3 after clearing denominators.
  -- Square both sides (both positive):
  --         (3√7)² > (4 + 2√3)²
  --         63 > 16 + 16√3 + 12 = 28 + 16√3
  --         35 > 16√3
  --         (35)² > (16√3)²
  --         1225 > 768                                              ✓
  have hs3 : 0 < Real.sqrt 3 := sqrt_three_pos
  have hs7 : 0 < Real.sqrt 7 := sqrt_seven_pos
  have hsq3 : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt_three_mul_self
  have hsq7 : Real.sqrt 7 * Real.sqrt 7 = 7 :=
    Real.mul_self_sqrt (by norm_num)
  -- Show 2/√3 = (2√3)/3
  have h2div3 : (2 : ℝ) / Real.sqrt 3 = 2 * Real.sqrt 3 / 3 := by
    field_simp
    nlinarith [hsq3]
  rw [h2div3]
  -- After substitution, multiplying by four reduces the goal to
  -- 3·√7 − 2·√3 > 4.
  -- We show 3√7 − 2√3 > 4 via:  35² > 768·1, i.e. (35)² > (16√3)²,
  -- i.e. 1225 > 768, hence 35 > 16√3, hence 63 - 28 > 16√3,
  -- i.e. 63 > 28 + 16√3 = (4 + 2√3)², so 3√7 = √63 > 4 + 2√3.
  -- Use nlinarith with all the sqrt facts.
  have hsq35 : (35 : ℝ)^2 = 1225 := by norm_num
  have h16s3 : (16 * Real.sqrt 3)^2 = 16^2 * 3 := by
    have : (16 * Real.sqrt 3)^2 = 16^2 * (Real.sqrt 3 * Real.sqrt 3) := by ring
    rw [this, hsq3]
  have h35_gt : 35 > 16 * Real.sqrt 3 := by
    have hsq_le : (16 * Real.sqrt 3)^2 < (35 : ℝ)^2 := by
      rw [h16s3, hsq35]; norm_num
    have h16s3_pos : 0 < 16 * Real.sqrt 3 := by positivity
    nlinarith [hsq_le, h16s3_pos]
  -- From 35 > 16√3, derive 3√7 > 4 + 2√3 by squaring once more.
  -- (3√7)² = 63, (4 + 2√3)² = 16 + 16√3 + 12 = 28 + 16√3.
  -- 63 - 28 = 35 > 16√3 ⟹ 63 > 28 + 16√3 = (4 + 2√3)².
  have hsq3_pos : 0 < 4 + 2 * Real.sqrt 3 := by positivity
  have hsq_4_2s3 : (4 + 2 * Real.sqrt 3)^2 = 28 + 16 * Real.sqrt 3 := by
    have : (4 + 2 * Real.sqrt 3)^2
        = 16 + 16 * Real.sqrt 3 + 4 * (Real.sqrt 3 * Real.sqrt 3) := by ring
    rw [this, hsq3]; ring
  have h_3s7_sq : (3 * Real.sqrt 7)^2 = 63 := by
    have : (3 * Real.sqrt 7)^2 = 9 * (Real.sqrt 7 * Real.sqrt 7) := by ring
    rw [this, hsq7]; norm_num
  have h_3s7_gt : 3 * Real.sqrt 7 > 4 + 2 * Real.sqrt 3 := by
    have hsq_lt : (4 + 2 * Real.sqrt 3)^2 < (3 * Real.sqrt 7)^2 := by
      rw [hsq_4_2s3, h_3s7_sq]; linarith [h35_gt]
    have h3s7_pos : 0 < 3 * Real.sqrt 7 := by positivity
    nlinarith [hsq_lt, hsq3_pos, h3s7_pos]
  -- Conclude from the cleared-denominator inequality.
  nlinarith [h_3s7_gt, hs3, hs7]

/-! ### The proper-coloring theorem -/

/-- **The Isbell coloring is proper.** Two points at unit distance receive
    different colors. -/
theorem isbell_isProperColoring :
    ∀ {p q : R2}, unitDistanceGraph.Adj p q → isbellColor p ≠ isbellColor q := by
  intro p q hadj hsame
  -- Unfold adjacency to `dist p q = 1`.
  rw [unitDistanceGraph_adj] at hadj
  obtain ⟨_hne, hdist⟩ := hadj
  have hpq : dist p q = 1 := by
    rcases hdist with h | h
    · exact h
    · simpa [dist_comm] using h
  -- Unpack lattice indices.
  set ip := (nearestLatticeIdx p).1 with hip_def
  set jp := (nearestLatticeIdx p).2 with hjp_def
  set iq := (nearestLatticeIdx q).1 with hiq_def
  set jq := (nearestLatticeIdx q).2 with hjq_def
  -- `isbellColor` equality lifts to ZMod 7 equality on `i + 3·j`.
  have hcolor : (((ip : ZMod 7)) + 3 * ((jp : ZMod 7))) =
                (((iq : ZMod 7)) + 3 * ((jq : ZMod 7))) := by
    have h' : ((ip + 3 * jp : ℤ) : ZMod 7) =
        ((iq + 3 * jq : ℤ) : ZMod 7) := by
      have transformed := congrArg (ZMod.finEquiv 7) hsame
      simpa [isbellColor, toFin7, hip_def, hjp_def, hiq_def, hjq_def] using
        transformed
    push_cast at h'
    exact h'
  -- Voronoi cell bounds for p and q.
  have hp_close : dist p (isbellLatticePoint ip jp)
      ≤ isbellLatticeStep / Real.sqrt 3 := dist_le_voronoi_circumradius p
  have hq_close : dist q (isbellLatticePoint iq jq)
      ≤ isbellLatticeStep / Real.sqrt 3 := dist_le_voronoi_circumradius q
  -- Case split: same cell vs different cells.
  by_cases hsame_cell : (ip, jp) = (iq, jq)
  · -- Case 1: same cell — within-cell diameter < 1 contradicts dist = 1.
    have hp_eq : isbellLatticePoint ip jp = isbellLatticePoint iq jq := by
      have h1 : ip = iq := by
        exact (Prod.mk.injEq _ _ _ _).mp hsame_cell |>.1
      have h2 : jp = jq := by
        exact (Prod.mk.injEq _ _ _ _).mp hsame_cell |>.2
      rw [h1, h2]
    have htri : dist p q
        ≤ dist p (isbellLatticePoint ip jp) + dist q (isbellLatticePoint iq jq) := by
      calc dist p q
          ≤ dist p (isbellLatticePoint iq jq) + dist (isbellLatticePoint iq jq) q :=
            dist_triangle _ _ _
        _ = dist p (isbellLatticePoint iq jq) + dist q (isbellLatticePoint iq jq) := by
            rw [dist_comm (isbellLatticePoint iq jq) q]
        _ = dist p (isbellLatticePoint ip jp) + dist q (isbellLatticePoint iq jq) := by
            rw [hp_eq]
    have hbound : dist p q ≤ 2 * (isbellLatticeStep / Real.sqrt 3) := by
      linarith [htri, hp_close, hq_close]
    have hlt : dist p q < 1 := lt_of_le_of_lt hbound isbell_voronoi_diameter_lt_one
    linarith [hlt, hpq]
  · -- Case 2: different cells, same color — same-color spacing contradicts dist = 1.
    have hne : (ip, jp) ≠ (iq, jq) := hsame_cell
    have hfar : dist (isbellLatticePoint ip jp) (isbellLatticePoint iq jq)
        ≥ isbellLatticeStep * Real.sqrt 7 :=
      dist_between_same_color_lattice_points hne hcolor
    -- Reverse triangle: dist(centerₚ, center_q) ≤ |centerₚ - p| + |p - q| + |q - center_q|
    have hrtri : dist (isbellLatticePoint ip jp) (isbellLatticePoint iq jq)
        ≤ dist (isbellLatticePoint ip jp) p
          + dist p q
          + dist q (isbellLatticePoint iq jq) := by
      have h1 : dist (isbellLatticePoint ip jp) (isbellLatticePoint iq jq)
          ≤ dist (isbellLatticePoint ip jp) p + dist p (isbellLatticePoint iq jq) :=
        dist_triangle _ _ _
      have h2 : dist p (isbellLatticePoint iq jq)
          ≤ dist p q + dist q (isbellLatticePoint iq jq) :=
        dist_triangle _ _ _
      linarith
    have hp_close' : dist (isbellLatticePoint ip jp) p
        ≤ isbellLatticeStep / Real.sqrt 3 := by
      rw [dist_comm]; exact hp_close
    have hbound : isbellLatticeStep * Real.sqrt 7
        ≤ 2 * (isbellLatticeStep / Real.sqrt 3) + dist p q := by
      linarith [hfar, hrtri, hp_close', hq_close]
    have hgap : isbellLatticeStep * Real.sqrt 7 - 2 * (isbellLatticeStep / Real.sqrt 3)
        = isbellLatticeStep * (Real.sqrt 7 - 2 / Real.sqrt 3) := by ring
    have hgt_one : isbellLatticeStep * Real.sqrt 7
        - 2 * (isbellLatticeStep / Real.sqrt 3) > 1 := by
      rw [hgap]; exact isbell_same_color_min_gt_one
    have hgt : dist p q > 1 := by linarith
    linarith [hgt, hpq]

/-- Bundle the Isbell witness into a `SimpleGraph.Coloring`. -/
noncomputable def isbellColoring : unitDistanceGraph.Coloring (Fin 7) :=
  Coloring.mk isbellColor isbell_isProperColoring

/-- **Upper bound — χ(R²) ≤ 7.** The unit-distance graph on R² is
    7-colorable. -/
theorem chromaticNumber_le_seven :
    unitDistanceGraph.Colorable 7 :=
  ⟨isbellColoring⟩

end HadwigerNelsonBounds
