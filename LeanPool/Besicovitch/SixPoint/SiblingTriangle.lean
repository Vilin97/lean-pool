/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.CanonicalTriangle
public import LeanPool.Besicovitch.SixPoint.Packing

/-!
# Sibling-pair versus rooted-triangle packings

This file constructs supports `67` and `76` and proves their one-dimensional routing algebra.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

/-- The canonical triangle's total radius is its semiperimeter. -/
theorem canonicalTriangleRadius_sum {X : Type*} [PseudoMetricSpace X]
    (root left right : X) :
    canonicalTriangleRadius root left right .root +
      canonicalTriangleRadius root left right .left +
      canonicalTriangleRadius root left right .right =
      (dist root left + dist root right + dist left right) / 2 := by
  simp only [canonicalTriangleRadius]
  ring

/-- Support `67`: the red sibling pair against the canonical blue triangle. -/
def redSiblingBlueTrianglePacking (configuration : SixPointConfiguration) {L x : ℝ}
    (hLdist : dist (configuration .red .left) (configuration .red .right) = L)
    (hL : 1 ≤ L) (hx_lower : L - 1 ≤ x) (hx_upper : x ≤ 1)
    (hblueLeft : dist (configuration .blue .root) (configuration .blue .left) ≤ 1)
    (hblueRight : dist (configuration .blue .root) (configuration .blue .right) ≤ 1) :
    SixPointPacking configuration where
  support := {(.red, .left), (.red, .right), (.blue, .root), (.blue, .left),
    (.blue, .right)}
  meets_color color := by
    cases color
    · exact ⟨.left, by simp⟩
    · exact ⟨.root, by simp⟩
  radius i := by
    rcases i with ⟨⟨color, label⟩, hlabel⟩
    cases color <;> cases label
    · simp at hlabel
    · exact ⟨x, by nlinarith, hx_upper⟩
    · exact ⟨L - x, by nlinarith, by nlinarith⟩
    · exact ⟨_, canonicalTriangleRadius_nonneg _ _ _ .root,
        canonicalTriangleRadius_le_one _ _ _ hblueLeft hblueRight .root⟩
    · exact ⟨_, canonicalTriangleRadius_nonneg _ _ _ .left,
        canonicalTriangleRadius_le_one _ _ _ hblueLeft hblueRight .left⟩
    · exact ⟨_, canonicalTriangleRadius_nonneg _ _ _ .right,
        canonicalTriangleRadius_le_one _ _ _ hblueLeft hblueRight .right⟩
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
    · cases li <;> cases lj
      · exact (hij (Subtype.ext rfl)).elim
      · exact (canonicalTriangleRadius_root_add_left _ _ _).le
      · exact (canonicalTriangleRadius_root_add_right _ _ _).le
      · rw [add_comm, dist_comm]
        exact (canonicalTriangleRadius_root_add_left _ _ _).le
      · exact (hij (Subtype.ext rfl)).elim
      · exact (canonicalTriangleRadius_left_add_right _ _ _).le
      · rw [add_comm, dist_comm]
        exact (canonicalTriangleRadius_root_add_right _ _ _).le
      · rw [add_comm, dist_comm]
        exact (canonicalTriangleRadius_left_add_right _ _ _).le
      · exact (hij (Subtype.ext rfl)).elim

/-- The left red radius in support `67` is the split variable. -/
@[simp] theorem redSiblingBlueTrianglePacking_radius_left
    (configuration : SixPointConfiguration) {L x : ℝ}
    (hLdist : dist (configuration .red .left) (configuration .red .right) = L)
    (hL : 1 ≤ L) (hx_lower : L - 1 ≤ x) (hx_upper : x ≤ 1)
    (hblueLeft : dist (configuration .blue .root) (configuration .blue .left) ≤ 1)
    (hblueRight : dist (configuration .blue .root) (configuration .blue .right) ≤ 1)
    (hmem : (.red, .left) ∈ (redSiblingBlueTrianglePacking configuration hLdist hL
      hx_lower hx_upper hblueLeft hblueRight).support) :
    ((redSiblingBlueTrianglePacking configuration hLdist hL hx_lower hx_upper hblueLeft
      hblueRight).radius ⟨(.red, .left), hmem⟩ : ℝ) = x := by
  rfl

/-- The right red radius in support `67` is the complementary split. -/
@[simp] theorem redSiblingBlueTrianglePacking_radius_right
    (configuration : SixPointConfiguration) {L x : ℝ}
    (hLdist : dist (configuration .red .left) (configuration .red .right) = L)
    (hL : 1 ≤ L) (hx_lower : L - 1 ≤ x) (hx_upper : x ≤ 1)
    (hblueLeft : dist (configuration .blue .root) (configuration .blue .left) ≤ 1)
    (hblueRight : dist (configuration .blue .root) (configuration .blue .right) ≤ 1)
    (hmem : (.red, .right) ∈ (redSiblingBlueTrianglePacking configuration hLdist hL
      hx_lower hx_upper hblueLeft hblueRight).support) :
    ((redSiblingBlueTrianglePacking configuration hLdist hL hx_lower hx_upper hblueLeft
      hblueRight).radius ⟨(.red, .right), hmem⟩ : ℝ) = L - x := by
  rfl

/-- Blue radii in support `67` are the canonical triangle radii. -/
@[simp] theorem redSiblingBlueTrianglePacking_radius_blue
    (configuration : SixPointConfiguration) {L x : ℝ}
    (hLdist : dist (configuration .red .left) (configuration .red .right) = L)
    (hL : 1 ≤ L) (hx_lower : L - 1 ≤ x) (hx_upper : x ≤ 1)
    (hblueLeft : dist (configuration .blue .root) (configuration .blue .left) ≤ 1)
    (hblueRight : dist (configuration .blue .root) (configuration .blue .right) ≤ 1)
    (label : SixPointLabel)
    (hmem : (.blue, label) ∈ (redSiblingBlueTrianglePacking configuration hLdist hL
      hx_lower hx_upper hblueLeft hblueRight).support) :
    ((redSiblingBlueTrianglePacking configuration hLdist hL hx_lower hx_upper hblueLeft
      hblueRight).radius ⟨(.blue, label), hmem⟩ : ℝ) =
      canonicalTriangleRadius (configuration .blue .root) (configuration .blue .left)
        (configuration .blue .right) label := by
  cases label <;> rfl

/-- The total radius of support `67` is the sibling length plus blue semiperimeter. -/
theorem redSiblingBlueTrianglePacking_totalRadius
    (configuration : SixPointConfiguration) {L x : ℝ}
    (hLdist : dist (configuration .red .left) (configuration .red .right) = L)
    (hL : 1 ≤ L) (hx_lower : L - 1 ≤ x) (hx_upper : x ≤ 1)
    (hblueLeft : dist (configuration .blue .root) (configuration .blue .left) ≤ 1)
    (hblueRight : dist (configuration .blue .root) (configuration .blue .right) ≤ 1) :
    (redSiblingBlueTrianglePacking configuration hLdist hL hx_lower hx_upper hblueLeft
      hblueRight).totalRadius = L +
      (dist (configuration .blue .root) (configuration .blue .left) +
        dist (configuration .blue .root) (configuration .blue .right) +
        dist (configuration .blue .left) (configuration .blue .right)) / 2 := by
  let packing := redSiblingBlueTrianglePacking configuration hLdist hL hx_lower hx_upper
    hblueLeft hblueRight
  let value : SixPointIndex → ℝ
    | (.red, .root) => 0
    | (.red, .left) => x
    | (.red, .right) => L - x
    | (.blue, label) => canonicalTriangleRadius (configuration .blue .root)
        (configuration .blue .left) (configuration .blue .right) label
  rw [SixPointPacking.totalRadius]
  calc
    _ = ∑ i ∈ packing.support.attach, value i := by
      apply Finset.sum_congr rfl
      rintro ⟨⟨color, label⟩, hi⟩ -
      cases color <;> cases label <;>
        simp [redSiblingBlueTrianglePacking, value] at hi ⊢
    _ = ∑ i ∈ packing.support, value i := Finset.sum_attach _ _
    _ = _ := by
      simp [packing, redSiblingBlueTrianglePacking, value, canonicalTriangleRadius]
      ring

/-- Support `76`: the blue sibling pair against the canonical red triangle. -/
def blueSiblingRedTrianglePacking (configuration : SixPointConfiguration) {M y : ℝ}
    (hMdist : dist (configuration .blue .left) (configuration .blue .right) = M)
    (hM : 1 ≤ M) (hy_lower : M - 1 ≤ y) (hy_upper : y ≤ 1)
    (hredLeft : dist (configuration .red .root) (configuration .red .left) ≤ 1)
    (hredRight : dist (configuration .red .root) (configuration .red .right) ≤ 1) :
    SixPointPacking configuration where
  support := {(.red, .root), (.red, .left), (.red, .right), (.blue, .left),
    (.blue, .right)}
  meets_color color := by
    cases color
    · exact ⟨.root, by simp⟩
    · exact ⟨.left, by simp⟩
  radius i := by
    rcases i with ⟨⟨color, label⟩, hlabel⟩
    cases color <;> cases label
    · exact ⟨_, canonicalTriangleRadius_nonneg _ _ _ .root,
        canonicalTriangleRadius_le_one _ _ _ hredLeft hredRight .root⟩
    · exact ⟨_, canonicalTriangleRadius_nonneg _ _ _ .left,
        canonicalTriangleRadius_le_one _ _ _ hredLeft hredRight .left⟩
    · exact ⟨_, canonicalTriangleRadius_nonneg _ _ _ .right,
        canonicalTriangleRadius_le_one _ _ _ hredLeft hredRight .right⟩
    · simp at hlabel
    · exact ⟨y, by nlinarith, hy_upper⟩
    · exact ⟨M - y, by nlinarith, by nlinarith⟩
  same_color_disjoint i j hij hcolor := by
    rcases i with ⟨⟨ci, li⟩, hi⟩
    rcases j with ⟨⟨cj, lj⟩, hj⟩
    simp only at hcolor
    subst cj
    cases ci
    · cases li <;> cases lj
      · exact (hij (Subtype.ext rfl)).elim
      · exact (canonicalTriangleRadius_root_add_left _ _ _).le
      · exact (canonicalTriangleRadius_root_add_right _ _ _).le
      · rw [add_comm, dist_comm]
        exact (canonicalTriangleRadius_root_add_left _ _ _).le
      · exact (hij (Subtype.ext rfl)).elim
      · exact (canonicalTriangleRadius_left_add_right _ _ _).le
      · rw [add_comm, dist_comm]
        exact (canonicalTriangleRadius_root_add_right _ _ _).le
      · rw [add_comm, dist_comm]
        exact (canonicalTriangleRadius_left_add_right _ _ _).le
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

/-- The total radius of support `76` is the sibling length plus red semiperimeter. -/
theorem blueSiblingRedTrianglePacking_totalRadius
    (configuration : SixPointConfiguration) {M y : ℝ}
    (hMdist : dist (configuration .blue .left) (configuration .blue .right) = M)
    (hM : 1 ≤ M) (hy_lower : M - 1 ≤ y) (hy_upper : y ≤ 1)
    (hredLeft : dist (configuration .red .root) (configuration .red .left) ≤ 1)
    (hredRight : dist (configuration .red .root) (configuration .red .right) ≤ 1) :
    (blueSiblingRedTrianglePacking configuration hMdist hM hy_lower hy_upper hredLeft
      hredRight).totalRadius = M +
      (dist (configuration .red .root) (configuration .red .left) +
        dist (configuration .red .root) (configuration .red .right) +
        dist (configuration .red .left) (configuration .red .right)) / 2 := by
  let packing := blueSiblingRedTrianglePacking configuration hMdist hM hy_lower hy_upper
    hredLeft hredRight
  let value : SixPointIndex → ℝ
    | (.red, label) => canonicalTriangleRadius (configuration .red .root)
        (configuration .red .left) (configuration .red .right) label
    | (.blue, .root) => 0
    | (.blue, .left) => y
    | (.blue, .right) => M - y
  rw [SixPointPacking.totalRadius]
  calc
    _ = ∑ i ∈ packing.support.attach, value i := by
      apply Finset.sum_congr rfl
      rintro ⟨⟨color, label⟩, hi⟩ -
      cases color <;> cases label <;>
        simp [blueSiblingRedTrianglePacking, value] at hi ⊢
    _ = ∑ i ∈ packing.support, value i := Finset.sum_attach _ _
    _ = _ := by
      simp [packing, blueSiblingRedTrianglePacking, value, canonicalTriangleRadius]
      ring

/-- Cross reach from a red point to a blue point carrying its canonical radius. -/
def redSiblingBlueTriangleReach (configuration : SixPointConfiguration)
    (redLabel blueLabel : SixPointLabel) : ℝ :=
  dist (configuration .red redLabel) (configuration .blue blueLabel) +
    canonicalTriangleRadius (configuration .blue .root) (configuration .blue .left)
      (configuration .blue .right) blueLabel

/-- Cross reach from a blue point to a red point carrying its canonical radius. -/
def blueSiblingRedTriangleReach (configuration : SixPointConfiguration)
    (blueLabel redLabel : SixPointLabel) : ℝ :=
  dist (configuration .blue blueLabel) (configuration .red redLabel) +
    canonicalTriangleRadius (configuration .red .root) (configuration .red .left)
      (configuration .red .right) redLabel

/-- The largest of three labelled real values. -/
def triangleMaximum (value : SixPointLabel → ℝ) : ℝ :=
  max (value .root) (max (value .left) (value .right))

/-- Every labelled value is bounded by its triangle maximum. -/
theorem le_triangleMaximum (value : SixPointLabel → ℝ) (label : SixPointLabel) :
    value label ≤ triangleMaximum value := by
  cases label <;> simp [triangleMaximum]

/-- A triangle maximum is attained at one of its three labels. -/
theorem exists_triangleMaximum_eq (value : SixPointLabel → ℝ) :
    ∃ label, triangleMaximum value = value label := by
  rcases max_choice (value .root) (max (value .left) (value .right)) with h | h
  · exact ⟨.root, h⟩
  · rcases max_choice (value .left) (value .right) with h' | h'
    · exact ⟨.left, h.trans h'⟩
    · exact ⟨.right, h.trans h'⟩

/-- Diameter of a sibling split against a tangent triangle with fixed cross reaches. -/
def siblingTriangleSplitDiameter (L M x : ℝ)
    (leftReach rightReach : SixPointLabel → ℝ) : ℝ :=
  max (2 * L) <| max (2 * M) <|
    max (x + triangleMaximum leftReach) (L - x + triangleMaximum rightReach)

private theorem sameColorPair_le_twice_bound {configuration : SixPointConfiguration}
    (packing : SixPointPacking configuration) (i j : packing.support) (hcolor : i.1.1 = j.1.1)
    {bound : ℝ} (hbound : 1 ≤ bound)
    (hdist : dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) ≤ bound) :
    dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) +
      packing.radius i + packing.radius j ≤ 2 * bound := by
  by_cases hij : i = j
  · subst j
    simp only [dist_self, zero_add]
    nlinarith [(packing.radius i).property.2]
  · nlinarith [packing.same_color_disjoint i j hij hcolor]

/-- The virtual diameter of support `67` is its explicit one-dimensional diameter. -/
theorem redSiblingBlueTrianglePacking_virtualDiameter
    (configuration : SixPointConfiguration) {L M x : ℝ}
    (hLdist : dist (configuration .red .left) (configuration .red .right) = L)
    (hMdist : dist (configuration .blue .left) (configuration .blue .right) = M)
    (hL : 1 ≤ L) (hM : 1 ≤ M) (hx_lower : L - 1 ≤ x) (hx_upper : x ≤ 1)
    (hblueLeft : dist (configuration .blue .root) (configuration .blue .left) ≤ 1)
    (hblueRight : dist (configuration .blue .root) (configuration .blue .right) ≤ 1) :
    (redSiblingBlueTrianglePacking configuration hLdist hL hx_lower hx_upper hblueLeft
      hblueRight).virtualDiameter =
      siblingTriangleSplitDiameter L M x
        (redSiblingBlueTriangleReach configuration .left)
        (redSiblingBlueTriangleReach configuration .right) := by
  let packing := redSiblingBlueTrianglePacking configuration hLdist hL hx_lower hx_upper
    hblueLeft hblueRight
  let target := siblingTriangleSplitDiameter L M x
    (redSiblingBlueTriangleReach configuration .left)
    (redSiblingBlueTriangleReach configuration .right)
  have hredDist (leftLabel rightLabel : SixPointLabel)
      (hleft : (.red, leftLabel) ∈ packing.support)
      (hright : (.red, rightLabel) ∈ packing.support) :
      dist (configuration .red leftLabel) (configuration .red rightLabel) ≤ L := by
    cases leftLabel <;> cases rightLabel
    all_goals simp [packing, redSiblingBlueTrianglePacking] at hleft hright
    · simp
      linarith
    · rw [hLdist]
    · rw [dist_comm, hLdist]
    · simp
      linarith
  have hblueDist (leftLabel rightLabel : SixPointLabel) :
      dist (configuration .blue leftLabel) (configuration .blue rightLabel) ≤ M := by
    cases leftLabel <;> cases rightLabel
    · simp
      linarith
    · exact hblueLeft.trans hM
    · exact hblueRight.trans hM
    · simpa [dist_comm] using hblueLeft.trans hM
    · simp
      linarith
    · rw [hMdist]
    · simpa [dist_comm] using hblueRight.trans hM
    · rw [dist_comm, hMdist]
    · simp
      linarith
  have htwoL : 2 * L ≤ target := by
    exact le_max_left _ _
  have htwoM : 2 * M ≤ target := by
    exact le_max_of_le_right (le_max_left _ _)
  have hcrossLeft :
      x + triangleMaximum (redSiblingBlueTriangleReach configuration .left) ≤ target := by
    exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hcrossRight :
      L - x + triangleMaximum (redSiblingBlueTriangleReach configuration .right) ≤ target := by
    exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  have hredLeftRadius (hmem : (.red, .left) ∈ packing.support) :
      (packing.radius ⟨(.red, .left), hmem⟩ : ℝ) = x := by
    rfl
  have hredRightRadius (hmem : (.red, .right) ∈ packing.support) :
      (packing.radius ⟨(.red, .right), hmem⟩ : ℝ) = L - x := by
    rfl
  have hblueRadius (label : SixPointLabel) (hmem : (.blue, label) ∈ packing.support) :
      (packing.radius ⟨(.blue, label), hmem⟩ : ℝ) =
        canonicalTriangleRadius (configuration .blue .root) (configuration .blue .left)
          (configuration .blue .right) label := by
    cases label <;> rfl
  have hpair (i j : packing.support) :
      dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) +
        packing.radius i + packing.radius j ≤ target := by
    rcases i with ⟨⟨leftColor, leftLabel⟩, hleft⟩
    rcases j with ⟨⟨rightColor, rightLabel⟩, hright⟩
    cases leftColor <;> cases rightColor
    · exact (sameColorPair_le_twice_bound packing ⟨_, hleft⟩ ⟨_, hright⟩ rfl hL
        (hredDist leftLabel rightLabel hleft hright)).trans htwoL
    · cases leftLabel
      · simp [packing, redSiblingBlueTrianglePacking] at hleft
      · rw [hredLeftRadius hleft, hblueRadius rightLabel hright]
        have hreach := le_triangleMaximum
          (redSiblingBlueTriangleReach configuration .left) rightLabel
        simp only [redSiblingBlueTriangleReach] at hreach
        nlinarith
      · rw [hredRightRadius hleft, hblueRadius rightLabel hright]
        have hreach := le_triangleMaximum
          (redSiblingBlueTriangleReach configuration .right) rightLabel
        simp only [redSiblingBlueTriangleReach] at hreach
        nlinarith
    · cases rightLabel
      · simp [packing, redSiblingBlueTrianglePacking] at hright
      · rw [hblueRadius leftLabel hleft, hredLeftRadius hright, dist_comm]
        have hreach := le_triangleMaximum
          (redSiblingBlueTriangleReach configuration .left) leftLabel
        simp only [redSiblingBlueTriangleReach] at hreach
        nlinarith
      · rw [hblueRadius leftLabel hleft, hredRightRadius hright, dist_comm]
        have hreach := le_triangleMaximum
          (redSiblingBlueTriangleReach configuration .right) leftLabel
        simp only [redSiblingBlueTriangleReach] at hreach
        nlinarith
    · exact (sameColorPair_le_twice_bound packing ⟨_, hleft⟩ ⟨_, hright⟩ rfl hM
        (hblueDist leftLabel rightLabel)).trans htwoM
  apply le_antisymm
  · unfold SixPointPacking.virtualDiameter
    apply Finset.sup'_le
    intro i hi
    apply Finset.sup'_le
    intro j hj
    exact hpair i j
  · let redLeft : packing.support := ⟨(.red, .left), by
      simp [packing, redSiblingBlueTrianglePacking]⟩
    let redRight : packing.support := ⟨(.red, .right), by
      simp [packing, redSiblingBlueTrianglePacking]⟩
    let blueLeft : packing.support := ⟨(.blue, .left), by
      simp [packing, redSiblingBlueTrianglePacking]⟩
    let blueRight : packing.support := ⟨(.blue, .right), by
      simp [packing, redSiblingBlueTrianglePacking]⟩
    have hdiameterL : 2 * L ≤ packing.virtualDiameter := by
      have hpairL := packing.pair_le_virtualDiameter redLeft redRight
      rw [hredLeftRadius redLeft.property, hredRightRadius redRight.property,
        hLdist] at hpairL
      linarith
    have hdiameterM : 2 * M ≤ packing.virtualDiameter := by
      have hpairM := packing.pair_le_virtualDiameter blueLeft blueRight
      rw [hblueRadius .left blueLeft.property, hblueRadius .right blueRight.property,
        hMdist] at hpairM
      nlinarith [canonicalTriangleRadius_left_add_right (configuration .blue .root)
        (configuration .blue .left) (configuration .blue .right)]
    have hleftPoint (label : SixPointLabel) :
        redSiblingBlueTriangleReach configuration .left label + x ≤
          packing.virtualDiameter := by
      let blue : packing.support := ⟨(.blue, label), by
        cases label <;> simp [packing, redSiblingBlueTrianglePacking]⟩
      have hpairLeft := packing.pair_le_virtualDiameter redLeft blue
      rw [hredLeftRadius redLeft.property, hblueRadius label blue.property] at hpairLeft
      simp only [redSiblingBlueTriangleReach]
      linarith
    have hrightPoint (label : SixPointLabel) :
        redSiblingBlueTriangleReach configuration .right label + (L - x) ≤
          packing.virtualDiameter := by
      let blue : packing.support := ⟨(.blue, label), by
        cases label <;> simp [packing, redSiblingBlueTrianglePacking]⟩
      have hpairRight := packing.pair_le_virtualDiameter redRight blue
      rw [hredRightRadius redRight.property, hblueRadius label blue.property] at hpairRight
      simp only [redSiblingBlueTriangleReach]
      linarith
    have hdiameterLeft :
        x + triangleMaximum (redSiblingBlueTriangleReach configuration .left) ≤
          packing.virtualDiameter := by
      simp only [triangleMaximum, add_max, max_le_iff]
      exact ⟨by nlinarith [hleftPoint .root], by nlinarith [hleftPoint .left],
        by nlinarith [hleftPoint .right]⟩
    have hdiameterRight :
        L - x + triangleMaximum (redSiblingBlueTriangleReach configuration .right) ≤
          packing.virtualDiameter := by
      rw [show L - x + triangleMaximum (redSiblingBlueTriangleReach configuration .right) =
        triangleMaximum (redSiblingBlueTriangleReach configuration .right) + (L - x) by ring]
      simp only [triangleMaximum, max_add, max_le_iff]
      exact ⟨hrightPoint .root, hrightPoint .left, hrightPoint .right⟩
    simp only [siblingTriangleSplitDiameter, max_le_iff]
    exact ⟨hdiameterL, hdiameterM, hdiameterLeft, hdiameterRight⟩

/-- The virtual diameter of support `76` is its explicit one-dimensional diameter. -/
theorem blueSiblingRedTrianglePacking_virtualDiameter
    (configuration : SixPointConfiguration) {L M y : ℝ}
    (hLdist : dist (configuration .red .left) (configuration .red .right) = L)
    (hMdist : dist (configuration .blue .left) (configuration .blue .right) = M)
    (hL : 1 ≤ L) (hM : 1 ≤ M) (hy_lower : M - 1 ≤ y) (hy_upper : y ≤ 1)
    (hredLeft : dist (configuration .red .root) (configuration .red .left) ≤ 1)
    (hredRight : dist (configuration .red .root) (configuration .red .right) ≤ 1) :
    (blueSiblingRedTrianglePacking configuration hMdist hM hy_lower hy_upper hredLeft
      hredRight).virtualDiameter =
      siblingTriangleSplitDiameter M L y
        (blueSiblingRedTriangleReach configuration .left)
        (blueSiblingRedTriangleReach configuration .right) := by
  let packing := blueSiblingRedTrianglePacking configuration hMdist hM hy_lower hy_upper
    hredLeft hredRight
  let target := siblingTriangleSplitDiameter M L y
    (blueSiblingRedTriangleReach configuration .left)
    (blueSiblingRedTriangleReach configuration .right)
  have hblueDist (leftLabel rightLabel : SixPointLabel)
      (hleft : (.blue, leftLabel) ∈ packing.support)
      (hright : (.blue, rightLabel) ∈ packing.support) :
      dist (configuration .blue leftLabel) (configuration .blue rightLabel) ≤ M := by
    cases leftLabel <;> cases rightLabel
    all_goals simp [packing, blueSiblingRedTrianglePacking] at hleft hright
    · simp
      linarith
    · rw [hMdist]
    · rw [dist_comm, hMdist]
    · simp
      linarith
  have hredDist (leftLabel rightLabel : SixPointLabel) :
      dist (configuration .red leftLabel) (configuration .red rightLabel) ≤ L := by
    cases leftLabel <;> cases rightLabel
    · simp
      linarith
    · exact hredLeft.trans hL
    · exact hredRight.trans hL
    · simpa [dist_comm] using hredLeft.trans hL
    · simp
      linarith
    · rw [hLdist]
    · simpa [dist_comm] using hredRight.trans hL
    · rw [dist_comm, hLdist]
    · simp
      linarith
  have htwoM : 2 * M ≤ target := le_max_left _ _
  have htwoL : 2 * L ≤ target := le_max_of_le_right (le_max_left _ _)
  have hcrossLeft :
      y + triangleMaximum (blueSiblingRedTriangleReach configuration .left) ≤ target := by
    exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hcrossRight :
      M - y + triangleMaximum (blueSiblingRedTriangleReach configuration .right) ≤ target := by
    exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  have hblueLeftRadius (hmem : (.blue, .left) ∈ packing.support) :
      (packing.radius ⟨(.blue, .left), hmem⟩ : ℝ) = y := by
    rfl
  have hblueRightRadius (hmem : (.blue, .right) ∈ packing.support) :
      (packing.radius ⟨(.blue, .right), hmem⟩ : ℝ) = M - y := by
    rfl
  have hredRadius (label : SixPointLabel) (hmem : (.red, label) ∈ packing.support) :
      (packing.radius ⟨(.red, label), hmem⟩ : ℝ) =
        canonicalTriangleRadius (configuration .red .root) (configuration .red .left)
          (configuration .red .right) label := by
    cases label <;> rfl
  have hpair (i j : packing.support) :
      dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) +
        packing.radius i + packing.radius j ≤ target := by
    rcases i with ⟨⟨leftColor, leftLabel⟩, hleft⟩
    rcases j with ⟨⟨rightColor, rightLabel⟩, hright⟩
    cases leftColor <;> cases rightColor
    · exact (sameColorPair_le_twice_bound packing ⟨_, hleft⟩ ⟨_, hright⟩ rfl hL
        (hredDist leftLabel rightLabel)).trans htwoL
    · cases rightLabel
      · simp [packing, blueSiblingRedTrianglePacking] at hright
      · rw [hredRadius leftLabel hleft, hblueLeftRadius hright, dist_comm]
        have hreach := le_triangleMaximum
          (blueSiblingRedTriangleReach configuration .left) leftLabel
        simp only [blueSiblingRedTriangleReach] at hreach
        nlinarith
      · rw [hredRadius leftLabel hleft, hblueRightRadius hright, dist_comm]
        have hreach := le_triangleMaximum
          (blueSiblingRedTriangleReach configuration .right) leftLabel
        simp only [blueSiblingRedTriangleReach] at hreach
        nlinarith
    · cases leftLabel
      · simp [packing, blueSiblingRedTrianglePacking] at hleft
      · rw [hblueLeftRadius hleft, hredRadius rightLabel hright]
        have hreach := le_triangleMaximum
          (blueSiblingRedTriangleReach configuration .left) rightLabel
        simp only [blueSiblingRedTriangleReach] at hreach
        nlinarith
      · rw [hblueRightRadius hleft, hredRadius rightLabel hright]
        have hreach := le_triangleMaximum
          (blueSiblingRedTriangleReach configuration .right) rightLabel
        simp only [blueSiblingRedTriangleReach] at hreach
        nlinarith
    · exact (sameColorPair_le_twice_bound packing ⟨_, hleft⟩ ⟨_, hright⟩ rfl hM
        (hblueDist leftLabel rightLabel hleft hright)).trans htwoM
  apply le_antisymm
  · unfold SixPointPacking.virtualDiameter
    apply Finset.sup'_le
    intro i hi
    apply Finset.sup'_le
    intro j hj
    exact hpair i j
  · let redLeft : packing.support := ⟨(.red, .left), by
      simp [packing, blueSiblingRedTrianglePacking]⟩
    let redRight : packing.support := ⟨(.red, .right), by
      simp [packing, blueSiblingRedTrianglePacking]⟩
    let blueLeft : packing.support := ⟨(.blue, .left), by
      simp [packing, blueSiblingRedTrianglePacking]⟩
    let blueRight : packing.support := ⟨(.blue, .right), by
      simp [packing, blueSiblingRedTrianglePacking]⟩
    have hdiameterL : 2 * L ≤ packing.virtualDiameter := by
      have hpairL := packing.pair_le_virtualDiameter redLeft redRight
      rw [hredRadius .left redLeft.property, hredRadius .right redRight.property,
        hLdist] at hpairL
      nlinarith [canonicalTriangleRadius_left_add_right (configuration .red .root)
        (configuration .red .left) (configuration .red .right)]
    have hdiameterM : 2 * M ≤ packing.virtualDiameter := by
      have hpairM := packing.pair_le_virtualDiameter blueLeft blueRight
      rw [hblueLeftRadius blueLeft.property, hblueRightRadius blueRight.property,
        hMdist] at hpairM
      linarith
    have hleftPoint (label : SixPointLabel) :
        blueSiblingRedTriangleReach configuration .left label + y ≤
          packing.virtualDiameter := by
      let red : packing.support := ⟨(.red, label), by
        cases label <;> simp [packing, blueSiblingRedTrianglePacking]⟩
      have hpairLeft := packing.pair_le_virtualDiameter blueLeft red
      rw [hblueLeftRadius blueLeft.property, hredRadius label red.property] at hpairLeft
      simp only [blueSiblingRedTriangleReach]
      linarith
    have hrightPoint (label : SixPointLabel) :
        blueSiblingRedTriangleReach configuration .right label + (M - y) ≤
          packing.virtualDiameter := by
      let red : packing.support := ⟨(.red, label), by
        cases label <;> simp [packing, blueSiblingRedTrianglePacking]⟩
      have hpairRight := packing.pair_le_virtualDiameter blueRight red
      rw [hblueRightRadius blueRight.property, hredRadius label red.property] at hpairRight
      simp only [blueSiblingRedTriangleReach]
      linarith
    have hdiameterLeft :
        y + triangleMaximum (blueSiblingRedTriangleReach configuration .left) ≤
          packing.virtualDiameter := by
      simp only [triangleMaximum, add_max, max_le_iff]
      exact ⟨by nlinarith [hleftPoint .root], by nlinarith [hleftPoint .left],
        by nlinarith [hleftPoint .right]⟩
    have hdiameterRight :
        M - y + triangleMaximum (blueSiblingRedTriangleReach configuration .right) ≤
          packing.virtualDiameter := by
      rw [show M - y + triangleMaximum (blueSiblingRedTriangleReach configuration .right) =
        triangleMaximum (blueSiblingRedTriangleReach configuration .right) + (M - y) by ring]
      simp only [triangleMaximum, max_add, max_le_iff]
      exact ⟨hrightPoint .root, hrightPoint .left, hrightPoint .right⟩
    simp only [siblingTriangleSplitDiameter, max_le_iff]
    exact ⟨hdiameterM, hdiameterL, hdiameterLeft, hdiameterRight⟩

/-- Exact threshold form of the one-dimensional sibling-triangle minimax. -/
theorem exists_siblingTriangle_split_iff
    {L M T : ℝ} {leftReach rightReach : SixPointLabel → ℝ} (hL : L ≤ 2) :
    (∃ x : ℝ, L - 1 ≤ x ∧ x ≤ 1 ∧
      siblingTriangleSplitDiameter L M x leftReach rightReach ≤ T) ↔
      2 * L ≤ T ∧ 2 * M ≤ T ∧
      (∀ label, L - 1 + leftReach label ≤ T) ∧
      (∀ label, L - 1 + rightReach label ≤ T) ∧
      (∀ leftLabel rightLabel,
        L + leftReach leftLabel + rightReach rightLabel ≤ 2 * T) := by
  constructor
  · rintro ⟨x, hx_lower, hx_upper, hdiameter⟩
    simp only [siblingTriangleSplitDiameter, max_le_iff] at hdiameter
    rcases hdiameter with ⟨hsameL, hsameM, hleft, hright⟩
    refine ⟨hsameL, hsameM, ?_, ?_, ?_⟩
    · intro label
      nlinarith [le_triangleMaximum leftReach label]
    · intro label
      nlinarith [le_triangleMaximum rightReach label]
    · intro leftLabel rightLabel
      nlinarith [le_triangleMaximum leftReach leftLabel,
        le_triangleMaximum rightReach rightLabel]
  · rintro ⟨hsameL, hsameM, hleft, hright, hbalanced⟩
    obtain ⟨leftLabel, hleftLabel⟩ := exists_triangleMaximum_eq leftReach
    obtain ⟨rightLabel, hrightLabel⟩ := exists_triangleMaximum_eq rightReach
    have hleftMax : L - 1 + triangleMaximum leftReach ≤ T := by
      rw [hleftLabel]
      exact hleft leftLabel
    have hrightMax : L - 1 + triangleMaximum rightReach ≤ T := by
      rw [hrightLabel]
      exact hright rightLabel
    have hbalancedMax :
        L + triangleMaximum leftReach + triangleMaximum rightReach ≤ 2 * T := by
      rw [hleftLabel, hrightLabel]
      exact hbalanced leftLabel rightLabel
    let x := max (L - 1) (L + triangleMaximum rightReach - T)
    have hx_lower : L - 1 ≤ x := le_max_left _ _
    have hx_upper : x ≤ 1 := by
      simp only [x, max_le_iff]
      exact ⟨by linarith, by linarith⟩
    have hcrossLeft : x + triangleMaximum leftReach ≤ T := by
      simp only [x, max_add, max_le_iff]
      exact ⟨by linarith, by linarith⟩
    have hcrossRight : L - x + triangleMaximum rightReach ≤ T := by
      nlinarith [le_max_right (L - 1) (L + triangleMaximum rightReach - T)]
    refine ⟨x, hx_lower, hx_upper, ?_⟩
    simp only [siblingTriangleSplitDiameter, max_le_iff]
    exact ⟨hsameL, hsameM, hcrossLeft, hcrossRight⟩

/-- If every feasible split fails, an endpoint or balanced cross term exceeds the target. -/
theorem siblingTriangle_failure_routing
    {L M T : ℝ} {leftReach rightReach : SixPointLabel → ℝ}
    (hL : L ≤ 2) (hsameL : 2 * L ≤ T) (hsameM : 2 * M ≤ T)
    (hfail : ∀ x : ℝ, L - 1 ≤ x → x ≤ 1 →
      T < siblingTriangleSplitDiameter L M x leftReach rightReach) :
    (∃ label, T < L - 1 + leftReach label) ∨
      (∃ label, T < L - 1 + rightReach label) ∨
      ∃ leftLabel rightLabel,
        2 * T < L + leftReach leftLabel + rightReach rightLabel := by
  by_contra hrouting
  simp only [not_or, not_exists, not_lt] at hrouting
  rcases hrouting with ⟨hleft, hright, hbalanced⟩
  obtain ⟨x, hx_lower, hx_upper, hdiameter⟩ :=
    (exists_siblingTriangle_split_iff hL).2
      ⟨hsameL, hsameM, hleft, hright, hbalanced⟩
  exact (not_lt_of_ge hdiameter) (hfail x hx_lower hx_upper)

end LeanPool.Besicovitch
