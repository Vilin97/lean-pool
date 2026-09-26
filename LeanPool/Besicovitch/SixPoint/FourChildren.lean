/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.Packing

/-!
# The four-child packing

This file constructs the split-radius packing on the four child labels and records its elementary
routing algebra.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

/-- The packing on all four children with prescribed tangent radius splits. -/
def fourChildrenPacking (configuration : SixPointConfiguration) {L M x y : ℝ}
    (hLdist : dist (configuration .red .left) (configuration .red .right) = L)
    (hMdist : dist (configuration .blue .left) (configuration .blue .right) = M)
    (hL : 1 ≤ L) (hx_lower : L - 1 ≤ x) (hx_upper : x ≤ 1)
    (hM : 1 ≤ M) (hy_lower : M - 1 ≤ y) (hy_upper : y ≤ 1) :
    SixPointPacking configuration where
  support := {(.red, .left), (.red, .right), (.blue, .left), (.blue, .right)}
  meets_color color := by
    cases color
    · exact ⟨.left, by simp⟩
    · exact ⟨.left, by simp⟩
  radius i := by
    rcases i with ⟨⟨color, label⟩, hlabel⟩
    cases color <;> cases label
    · simp at hlabel
    · exact ⟨x, by nlinarith, hx_upper⟩
    · exact ⟨L - x, by nlinarith, by nlinarith⟩
    · simp at hlabel
    · exact ⟨y, by nlinarith, hy_upper⟩
    · exact ⟨M - y, by nlinarith, by nlinarith⟩
  same_color_disjoint i j hij hcolor := by
    rcases i with ⟨⟨ci, li⟩, hi⟩
    rcases j with ⟨⟨cj, lj⟩, hj⟩
    simp only at hcolor
    subst cj
    cases ci
    · cases li
      · simp at hi
      · cases lj
        · simp at hj
        · exact (hij (Subtype.ext rfl)).elim
        · dsimp
          nlinarith
      · cases lj
        · simp at hj
        · dsimp
          rw [dist_comm, hLdist]
          nlinarith
        · exact (hij (Subtype.ext rfl)).elim
    · cases li
      · simp at hi
      · cases lj
        · simp at hj
        · exact (hij (Subtype.ext rfl)).elim
        · dsimp
          nlinarith
      · cases lj
        · simp at hj
        · dsimp
          rw [dist_comm, hMdist]
          nlinarith
        · exact (hij (Subtype.ext rfl)).elim

/-- The largest cross-color diameter term for a four-child radius split. -/
def fourChildrenCrossMaximum (L M x y B11 B12 B21 B22 : ℝ) : ℝ :=
  max (B11 + x + y) <| max (B12 + x + (M - y)) <|
    max (B21 + (L - x) + y) (B22 + (L - x) + (M - y))

/-- The largest same-color or cross-color diameter term for a four-child split. -/
def fourChildrenSplitDiameter (L M x y B11 B12 B21 B22 : ℝ) : ℝ :=
  max (2 * L) (max (2 * M) (fourChildrenCrossMaximum L M x y B11 B12 B21 B22))

/-- The total radius of the four-child packing is the sum of the two sibling lengths. -/
theorem fourChildrenPacking_totalRadius
    (configuration : SixPointConfiguration) {L M x y : ℝ}
    (hLdist : dist (configuration .red .left) (configuration .red .right) = L)
    (hMdist : dist (configuration .blue .left) (configuration .blue .right) = M)
    (hL : 1 ≤ L) (hx_lower : L - 1 ≤ x) (hx_upper : x ≤ 1)
    (hM : 1 ≤ M) (hy_lower : M - 1 ≤ y) (hy_upper : y ≤ 1) :
    (fourChildrenPacking configuration hLdist hMdist hL hx_lower hx_upper hM hy_lower
      hy_upper).totalRadius = L + M := by
  let packing := fourChildrenPacking configuration hLdist hMdist hL hx_lower hx_upper hM
    hy_lower hy_upper
  let value : SixPointIndex → ℝ
    | (.red, .root) | (.blue, .root) => 0
    | (.red, .left) => x
    | (.red, .right) => L - x
    | (.blue, .left) => y
    | (.blue, .right) => M - y
  rw [SixPointPacking.totalRadius]
  calc
    _ = ∑ i ∈ packing.support.attach, value i := by
      apply Finset.sum_congr rfl
      rintro ⟨⟨color, label⟩, hi⟩ -
      cases color <;> cases label <;>
        simp [fourChildrenPacking, value] at hi ⊢
    _ = ∑ i ∈ packing.support, value i := Finset.sum_attach _ _
    _ = _ := by
      simp [packing, fourChildrenPacking, value]
      ring

private theorem fourChildren_sameColorPair_le
    {configuration : SixPointConfiguration} (packing : SixPointPacking configuration)
    (i j : packing.support) (hcolor : i.1.1 = j.1.1) {bound : ℝ}
    (hbound : 1 ≤ bound)
    (hdist : dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) ≤ bound) :
    dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) +
      packing.radius i + packing.radius j ≤ 2 * bound := by
  by_cases hij : i = j
  · subst j
    simp only [dist_self, zero_add]
    nlinarith [(packing.radius i).property.2]
  · nlinarith [packing.same_color_disjoint i j hij hcolor]

/-- The virtual diameter of the four-child packing is its explicit split minimax. -/
theorem fourChildrenPacking_virtualDiameter
    (configuration : SixPointConfiguration) {L M x y : ℝ}
    (hLdist : dist (configuration .red .left) (configuration .red .right) = L)
    (hMdist : dist (configuration .blue .left) (configuration .blue .right) = M)
    (hL : 1 ≤ L) (hx_lower : L - 1 ≤ x) (hx_upper : x ≤ 1)
    (hM : 1 ≤ M) (hy_lower : M - 1 ≤ y) (hy_upper : y ≤ 1) :
    (fourChildrenPacking configuration hLdist hMdist hL hx_lower hx_upper hM hy_lower
      hy_upper).virtualDiameter =
      fourChildrenSplitDiameter L M x y
        (dist (configuration .red .left) (configuration .blue .left))
        (dist (configuration .red .left) (configuration .blue .right))
        (dist (configuration .red .right) (configuration .blue .left))
        (dist (configuration .red .right) (configuration .blue .right)) := by
  let packing := fourChildrenPacking configuration hLdist hMdist hL hx_lower hx_upper hM
    hy_lower hy_upper
  let target := fourChildrenSplitDiameter L M x y
    (dist (configuration .red .left) (configuration .blue .left))
    (dist (configuration .red .left) (configuration .blue .right))
    (dist (configuration .red .right) (configuration .blue .left))
    (dist (configuration .red .right) (configuration .blue .right))
  have htwoL : 2 * L ≤ target := le_max_left _ _
  have htwoM : 2 * M ≤ target := le_max_of_le_right (le_max_left _ _)
  have h11 : dist (configuration .red .left) (configuration .blue .left) + x + y ≤
      target := le_max_of_le_right <| le_max_of_le_right <| le_max_left _ _
  have h12 :
      dist (configuration .red .left) (configuration .blue .right) + x + (M - y) ≤
        target := le_max_of_le_right <| le_max_of_le_right <| le_max_of_le_right <|
          le_max_left _ _
  have h21 :
      dist (configuration .red .right) (configuration .blue .left) + (L - x) + y ≤
        target := le_max_of_le_right <| le_max_of_le_right <| le_max_of_le_right <|
          le_max_of_le_right <| le_max_left _ _
  have h22 :
      dist (configuration .red .right) (configuration .blue .right) +
          (L - x) + (M - y) ≤ target :=
    le_max_of_le_right <| le_max_of_le_right <| le_max_of_le_right <|
      le_max_of_le_right <| le_max_right _ _
  have hredLeftRadius (hmem : (.red, .left) ∈ packing.support) :
      (packing.radius ⟨(.red, .left), hmem⟩ : ℝ) = x := by
    rfl
  have hredRightRadius (hmem : (.red, .right) ∈ packing.support) :
      (packing.radius ⟨(.red, .right), hmem⟩ : ℝ) = L - x := by
    rfl
  have hblueLeftRadius (hmem : (.blue, .left) ∈ packing.support) :
      (packing.radius ⟨(.blue, .left), hmem⟩ : ℝ) = y := by
    rfl
  have hblueRightRadius (hmem : (.blue, .right) ∈ packing.support) :
      (packing.radius ⟨(.blue, .right), hmem⟩ : ℝ) = M - y := by
    rfl
  have hpair (i j : packing.support) :
      dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) +
        packing.radius i + packing.radius j ≤ target := by
    rcases i with ⟨⟨leftColor, leftLabel⟩, hleft⟩
    rcases j with ⟨⟨rightColor, rightLabel⟩, hright⟩
    cases leftColor <;> cases rightColor
    · have hleftMem := hleft
      have hrightMem := hright
      cases leftLabel <;> cases rightLabel
      all_goals simp [packing, fourChildrenPacking] at hleft hright
      · exact (fourChildren_sameColorPair_le packing ⟨_, hleftMem⟩ ⟨_, hrightMem⟩ rfl
          hL (by simp; linarith)).trans htwoL
      · exact (fourChildren_sameColorPair_le packing ⟨_, hleftMem⟩ ⟨_, hrightMem⟩ rfl
          hL
          (by rw [hLdist])).trans htwoL
      · exact (fourChildren_sameColorPair_le packing ⟨_, hleftMem⟩ ⟨_, hrightMem⟩ rfl
          hL
          (by rw [dist_comm, hLdist])).trans htwoL
      · exact (fourChildren_sameColorPair_le packing ⟨_, hleftMem⟩ ⟨_, hrightMem⟩ rfl
          hL (by simp; linarith)).trans htwoL
    · have hleftMem := hleft
      have hrightMem := hright
      cases leftLabel <;> cases rightLabel
      all_goals simp [packing, fourChildrenPacking] at hleft hright
      · simpa [hredLeftRadius hleftMem, hblueLeftRadius hrightMem] using h11
      · simpa [hredLeftRadius hleftMem, hblueRightRadius hrightMem] using h12
      · simpa [hredRightRadius hleftMem, hblueLeftRadius hrightMem] using h21
      · simpa [hredRightRadius hleftMem, hblueRightRadius hrightMem] using h22
    · have hleftMem := hleft
      have hrightMem := hright
      cases leftLabel <;> cases rightLabel
      all_goals simp [packing, fourChildrenPacking] at hleft hright
      · rw [hblueLeftRadius hleftMem, hredLeftRadius hrightMem, dist_comm]
        linarith [h11]
      · rw [hblueLeftRadius hleftMem, hredRightRadius hrightMem, dist_comm]
        linarith [h21]
      · rw [hblueRightRadius hleftMem, hredLeftRadius hrightMem, dist_comm]
        linarith [h12]
      · rw [hblueRightRadius hleftMem, hredRightRadius hrightMem, dist_comm]
        linarith [h22]
    · have hleftMem := hleft
      have hrightMem := hright
      cases leftLabel <;> cases rightLabel
      all_goals simp [packing, fourChildrenPacking] at hleft hright
      · exact (fourChildren_sameColorPair_le packing ⟨_, hleftMem⟩ ⟨_, hrightMem⟩ rfl
          hM (by simp; linarith)).trans htwoM
      · exact (fourChildren_sameColorPair_le packing ⟨_, hleftMem⟩ ⟨_, hrightMem⟩ rfl
          hM
          (by rw [hMdist])).trans htwoM
      · exact (fourChildren_sameColorPair_le packing ⟨_, hleftMem⟩ ⟨_, hrightMem⟩ rfl
          hM
          (by rw [dist_comm, hMdist])).trans htwoM
      · exact (fourChildren_sameColorPair_le packing ⟨_, hleftMem⟩ ⟨_, hrightMem⟩ rfl
          hM (by simp; linarith)).trans htwoM
  apply le_antisymm
  · unfold SixPointPacking.virtualDiameter
    apply Finset.sup'_le
    intro i hi
    apply Finset.sup'_le
    intro j hj
    exact hpair i j
  · let redLeft : packing.support := ⟨(.red, .left), by
      simp [packing, fourChildrenPacking]⟩
    let redRight : packing.support := ⟨(.red, .right), by
      simp [packing, fourChildrenPacking]⟩
    let blueLeft : packing.support := ⟨(.blue, .left), by
      simp [packing, fourChildrenPacking]⟩
    let blueRight : packing.support := ⟨(.blue, .right), by
      simp [packing, fourChildrenPacking]⟩
    have hdiameterL : 2 * L ≤ packing.virtualDiameter := by
      have hp := packing.pair_le_virtualDiameter redLeft redRight
      rw [hredLeftRadius redLeft.property, hredRightRadius redRight.property,
        hLdist] at hp
      linarith
    have hdiameterM : 2 * M ≤ packing.virtualDiameter := by
      have hp := packing.pair_le_virtualDiameter blueLeft blueRight
      rw [hblueLeftRadius blueLeft.property, hblueRightRadius blueRight.property,
        hMdist] at hp
      linarith
    have hdiameter11 :
        dist (configuration .red .left) (configuration .blue .left) + x + y ≤
          packing.virtualDiameter := by
      have hp := packing.pair_le_virtualDiameter redLeft blueLeft
      change dist (configuration .red .left) (configuration .blue .left) +
        packing.radius redLeft + packing.radius blueLeft ≤ packing.virtualDiameter at hp
      rw [hredLeftRadius redLeft.property, hblueLeftRadius blueLeft.property] at hp
      exact hp
    have hdiameter12 :
        dist (configuration .red .left) (configuration .blue .right) + x + (M - y) ≤
          packing.virtualDiameter := by
      have hp := packing.pair_le_virtualDiameter redLeft blueRight
      change dist (configuration .red .left) (configuration .blue .right) +
        packing.radius redLeft + packing.radius blueRight ≤ packing.virtualDiameter at hp
      rw [hredLeftRadius redLeft.property, hblueRightRadius blueRight.property] at hp
      exact hp
    have hdiameter21 :
        dist (configuration .red .right) (configuration .blue .left) + (L - x) + y ≤
          packing.virtualDiameter := by
      have hp := packing.pair_le_virtualDiameter redRight blueLeft
      change dist (configuration .red .right) (configuration .blue .left) +
        packing.radius redRight + packing.radius blueLeft ≤ packing.virtualDiameter at hp
      rw [hredRightRadius redRight.property, hblueLeftRadius blueLeft.property] at hp
      exact hp
    have hdiameter22 :
        dist (configuration .red .right) (configuration .blue .right) +
            (L - x) + (M - y) ≤ packing.virtualDiameter := by
      have hp := packing.pair_le_virtualDiameter redRight blueRight
      change dist (configuration .red .right) (configuration .blue .right) +
        packing.radius redRight + packing.radius blueRight ≤ packing.virtualDiameter at hp
      rw [hredRightRadius redRight.property, hblueRightRadius blueRight.property] at hp
      exact hp
    simp only [fourChildrenSplitDiameter, fourChildrenCrossMaximum, max_le_iff]
    exact ⟨hdiameterL, hdiameterM, hdiameter11, hdiameter12, hdiameter21, hdiameter22⟩

/-- A split below `c(L+M)` gives the four-child packing nonnegative score at `c/2`. -/
theorem fourChildrenPacking_score_nonnegative
    (configuration : SixPointConfiguration) {c L M x y : ℝ}
    (hLdist : dist (configuration .red .left) (configuration .red .right) = L)
    (hMdist : dist (configuration .blue .left) (configuration .blue .right) = M)
    (hL : 1 ≤ L) (hx_lower : L - 1 ≤ x) (hx_upper : x ≤ 1)
    (hM : 1 ≤ M) (hy_lower : M - 1 ≤ y) (hy_upper : y ≤ 1)
    (hc : 0 < c)
    (hdiameter : fourChildrenSplitDiameter L M x y
      (dist (configuration .red .left) (configuration .blue .left))
      (dist (configuration .red .left) (configuration .blue .right))
      (dist (configuration .red .right) (configuration .blue .left))
      (dist (configuration .red .right) (configuration .blue .right)) ≤ c * (L + M)) :
    0 ≤ (fourChildrenPacking configuration hLdist hMdist hL hx_lower hx_upper hM
      hy_lower hy_upper).score (c / 2) := by
  rw [SixPointPacking.score,
    fourChildrenPacking_totalRadius configuration hLdist hMdist hL hx_lower hx_upper hM
      hy_lower hy_upper,
    fourChildrenPacking_virtualDiameter configuration hLdist hMdist hL hx_lower hx_upper hM
      hy_lower hy_upper,
    show 2 * (c / 2) = c by ring]
  exact sub_nonneg.mpr ((div_le_iff₀ hc).2 (by simpa [mul_comm] using hdiameter))

/-- The routing bounds give a split whose four cross terms are all below the target. -/
theorem exists_fourChildren_split_of_routing_bounds
    {L M T B11 B12 B21 B22 : ℝ} (hL : L ≤ 2) (hM : M ≤ 2)
    (h11 : L + M + B11 - 2 ≤ T) (h12 : L + M + B12 - 2 ≤ T)
    (h21 : L + M + B21 - 2 ≤ T) (h22 : L + M + B22 - 2 ≤ T)
    (hrow1 : L + M + L - 2 + B11 + B12 ≤ 2 * T)
    (hrow2 : L + M + L - 2 + B21 + B22 ≤ 2 * T)
    (hcolumn1 : L + M + M - 2 + B11 + B21 ≤ 2 * T)
    (hcolumn2 : L + M + M - 2 + B12 + B22 ≤ 2 * T)
    (hmatching1 : L + M + B11 + B22 ≤ 2 * T)
    (hmatching2 : L + M + B12 + B21 ≤ 2 * T) :
    ∃ x y : ℝ, L - 1 ≤ x ∧ x ≤ 1 ∧ M - 1 ≤ y ∧ y ≤ 1 ∧
      B11 + x + y ≤ T ∧ B12 + x + (M - y) ≤ T ∧
      B21 + (L - x) + y ≤ T ∧ B22 + (L - x) + (M - y) ≤ T := by
  let lower1 := M - 1 - T + B21 + L
  let lower2 := B22 + (L + M) - T - 1
  let lower3 := (B21 + B22 + (L + M) + L - 2 * T) / 2
  let x := max (L - 1) (max lower1 (max lower2 lower3))
  have hx_lower : L - 1 ≤ x := by
    exact le_max_left _ _
  have hlower1 : lower1 ≤ x := by
    exact le_max_of_le_right (le_max_left _ _)
  have hlower2 : lower2 ≤ x := by
    exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hlower3 : lower3 ≤ x := by
    exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  dsimp only [lower1] at hlower1
  dsimp only [lower2] at hlower2
  dsimp only [lower3] at hlower3
  have hx_upper : x ≤ 1 := by
    simp only [x, lower1, lower2, lower3, max_le_iff]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hx_upper1 : x ≤ T - B11 - M + 1 := by
    simp only [x, lower1, lower2, lower3, max_le_iff]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hx_upper2 : x ≤ T - B12 - M + 1 := by
    simp only [x, lower1, lower2, lower3, max_le_iff]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hx_upper3' : x ≤ (2 * T - B11 - B12 - M) / 2 := by
    simp only [x, lower1, lower2, lower3, max_le_iff]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hx_upper3 : 2 * x ≤ 2 * T - B11 - B12 - M := by
    linarith
  let lowerY1 := B12 + x + M - T
  let lowerY2 := B22 + (L + M) - x - T
  let y := max (M - 1) (max lowerY1 lowerY2)
  have hy_lower : M - 1 ≤ y := le_max_left _ _
  have hlowerY1 : lowerY1 ≤ y := le_max_of_le_right (le_max_left _ _)
  have hlowerY2 : lowerY2 ≤ y := le_max_of_le_right (le_max_right _ _)
  dsimp only [lowerY1] at hlowerY1
  dsimp only [lowerY2] at hlowerY2
  have hy_upper : y ≤ 1 := by
    simp only [y, lowerY1, lowerY2, max_le_iff]
    exact ⟨by linarith, by linarith, by linarith⟩
  have hy_upper1 : y ≤ T - B11 - x := by
    simp only [y, lowerY1, lowerY2, max_le_iff]
    exact ⟨by linarith, by linarith, by linarith⟩
  have hy_upper2 : y ≤ T - B21 - L + x := by
    simp only [y, lowerY1, lowerY2, max_le_iff]
    exact ⟨by linarith, by linarith, by linarith⟩
  exact ⟨x, y, hx_lower, hx_upper, hy_lower, hy_upper, by linarith, by linarith,
    by linarith, by linarith⟩

/-- Exact threshold form of the two-by-two split minimax formula. -/
theorem exists_fourChildren_split_iff_routing_bounds
    {L M T B11 B12 B21 B22 : ℝ} (hL : L ≤ 2) (hM : M ≤ 2) :
    (∃ x y : ℝ, L - 1 ≤ x ∧ x ≤ 1 ∧ M - 1 ≤ y ∧ y ≤ 1 ∧
      fourChildrenSplitDiameter L M x y B11 B12 B21 B22 ≤ T) ↔
      2 * L ≤ T ∧ 2 * M ≤ T ∧
      L + M + B11 - 2 ≤ T ∧ L + M + B12 - 2 ≤ T ∧
      L + M + B21 - 2 ≤ T ∧ L + M + B22 - 2 ≤ T ∧
      L + M + L - 2 + B11 + B12 ≤ 2 * T ∧
      L + M + L - 2 + B21 + B22 ≤ 2 * T ∧
      L + M + M - 2 + B11 + B21 ≤ 2 * T ∧
      L + M + M - 2 + B12 + B22 ≤ 2 * T ∧
      L + M + B11 + B22 ≤ 2 * T ∧ L + M + B12 + B21 ≤ 2 * T := by
  constructor
  · rintro ⟨x, y, hx_lower, hx_upper, hy_lower, hy_upper, hdiameter⟩
    simp only [fourChildrenSplitDiameter, fourChildrenCrossMaximum, max_le_iff]
      at hdiameter
    rcases hdiameter with ⟨hsameL, hsameM, hd11, hd12, hd21, hd22⟩
    exact ⟨hsameL, hsameM, by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨hsameL, hsameM, h11, h12, h21, h22, hrow1, hrow2, hcolumn1,
      hcolumn2, hmatching1, hmatching2⟩
    obtain ⟨x, y, hx_lower, hx_upper, hy_lower, hy_upper, hd11, hd12, hd21, hd22⟩ :=
      exists_fourChildren_split_of_routing_bounds hL hM h11 h12 h21 h22 hrow1 hrow2
        hcolumn1 hcolumn2 hmatching1 hmatching2
    refine ⟨x, y, hx_lower, hx_upper, hy_lower, hy_upper, ?_⟩
    simp only [fourChildrenSplitDiameter, fourChildrenCrossMaximum, max_le_iff]
    exact ⟨hsameL, hsameM, hd11, hd12, hd21, hd22⟩

/-- Failure of every split forces a single, row, column, or matching routing term. -/
theorem fourChildren_routing {L M T B11 B12 B21 B22 : ℝ}
    (hL : L ≤ 2) (hM : M ≤ 2) (hsameL : 2 * L ≤ T) (hsameM : 2 * M ≤ T)
    (hfail : ∀ x y : ℝ, L - 1 ≤ x → x ≤ 1 → M - 1 ≤ y → y ≤ 1 →
      T < fourChildrenSplitDiameter L M x y B11 B12 B21 B22) :
    T < L + M + B11 - 2 ∨ T < L + M + B12 - 2 ∨
      T < L + M + B21 - 2 ∨ T < L + M + B22 - 2 ∨
      2 * T < L + M + L - 2 + B11 + B12 ∨
      2 * T < L + M + L - 2 + B21 + B22 ∨
      2 * T < L + M + M - 2 + B11 + B21 ∨
      2 * T < L + M + M - 2 + B12 + B22 ∨
      2 * T < L + M + B11 + B22 ∨ 2 * T < L + M + B12 + B21 := by
  by_contra hroute
  simp only [not_or, not_lt] at hroute
  rcases hroute with ⟨h11, h12, h21, h22, hrow1, hrow2, hcolumn1, hcolumn2,
    hmatching1, hmatching2⟩
  obtain ⟨x, y, hx_lower, hx_upper, hy_lower, hy_upper, hd11, hd12, hd21, hd22⟩ :=
    exists_fourChildren_split_of_routing_bounds hL hM h11 h12 h21 h22 hrow1 hrow2
      hcolumn1 hcolumn2 hmatching1 hmatching2
  have hdiameter : fourChildrenSplitDiameter L M x y B11 B12 B21 B22 ≤ T := by
    simp only [fourChildrenSplitDiameter, fourChildrenCrossMaximum, max_le_iff]
    exact ⟨hsameL, hsameM, hd11, hd12, hd21, hd22⟩
  exact (not_lt_of_ge hdiameter) (hfail x y hx_lower hx_upper hy_lower hy_upper)

/-- In the endpoint range, four-child failure routes to a row, column, or matching. -/
theorem fourChildren_row_column_or_matching
    {c L M B11 B12 B21 B22 : ℝ} (hc_one : 1 < c) (hc_two : c ≤ 2)
    (hcL : c ≤ L) (hcM : c ≤ M) (hL : L ≤ 2) (hM : M ≤ 2)
    (hsame_gap : 0 < c * (c + 2) - 4) (hsingle_gap : 1 < 2 * c * (c - 1))
    (hB11 : B11 ≤ 3) (hB12 : B12 ≤ 3) (hB21 : B21 ≤ 3) (hB22 : B22 ≤ 3)
    (hfail : ∀ x y : ℝ, L - 1 ≤ x → x ≤ 1 → M - 1 ≤ y → y ≤ 1 →
      c * (L + M) < fourChildrenSplitDiameter L M x y B11 B12 B21 B22) :
    2 + 2 * (c - 1) * L + (2 * c - 1) * M ≤ B11 + B12 ∨
      2 + 2 * (c - 1) * L + (2 * c - 1) * M ≤ B21 + B22 ∨
      2 + (2 * c - 1) * L + 2 * (c - 1) * M ≤ B11 + B21 ∨
      2 + (2 * c - 1) * L + 2 * (c - 1) * M ≤ B12 + B22 ∨
      (2 * c - 1) * (L + M) ≤ B11 + B22 ∨
      (2 * c - 1) * (L + M) ≤ B12 + B21 := by
  have hc_nonneg : 0 ≤ c := by linarith
  have hc_sub_two : c - 2 ≤ 0 := sub_nonpos.mpr hc_two
  have hcM_mul : c * c ≤ c * M := mul_le_mul_of_nonneg_left hcM hc_nonneg
  have hcL_mul : c * c ≤ c * L := mul_le_mul_of_nonneg_left hcL hc_nonneg
  have hLpart : (c - 2) * 2 ≤ (c - 2) * L := mul_le_mul_of_nonpos_left hL hc_sub_two
  have hMpart : (c - 2) * 2 ≤ (c - 2) * M := mul_le_mul_of_nonpos_left hM hc_sub_two
  have hsameL : 2 * L < c * (L + M) := by nlinarith
  have hsameM : 2 * M < c * (L + M) := by nlinarith
  have hQ : 2 * c ≤ L + M := by linarith
  have hc_sub_one : 0 ≤ c - 1 := sub_nonneg.mpr hc_one.le
  have hQmul : (c - 1) * (2 * c) ≤ (c - 1) * (L + M) :=
    mul_le_mul_of_nonneg_left hQ hc_sub_one
  have hsingle : 1 < (c - 1) * (L + M) := by nlinarith
  have hs11 : L + M + B11 - 2 < c * (L + M) := by nlinarith
  have hs12 : L + M + B12 - 2 < c * (L + M) := by nlinarith
  have hs21 : L + M + B21 - 2 < c * (L + M) := by nlinarith
  have hs22 : L + M + B22 - 2 < c * (L + M) := by nlinarith
  rcases fourChildren_routing hL hM hsameL.le hsameM.le hfail with
    h11 | h12 | h21 | h22 | hrow1 | hrow2 | hcolumn1 | hcolumn2 | hmatching1 | hmatching2
  · linarith
  · linarith
  · linarith
  · linarith
  · exact Or.inl (by nlinarith)
  · exact Or.inr (Or.inl (by nlinarith))
  · exact Or.inr (Or.inr (Or.inl (by nlinarith)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by nlinarith))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by nlinarith)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by nlinarith)))))

end LeanPool.Besicovitch
