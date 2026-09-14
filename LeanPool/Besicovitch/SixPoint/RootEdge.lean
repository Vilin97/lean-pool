/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.RationalChord
public import LeanPool.Besicovitch.Certificates.EndpointBridge
public import LeanPool.Besicovitch.SixPoint.EndpointGeometry
public import LeanPool.Besicovitch.SixPoint.SiblingTriangle

/-!
# Root--edge packings

This file develops the one-dimensional minimax for a root--child edge against the full opposite
triangle. It also proves the exact rational separator that excludes an internal triangle
primitive on the matching branch of the endpoint failure tree.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace LeanPool.Besicovitch

/-- The cross-color part of a root-edge split with edge length `R`. -/
def rootEdgeCrossMaximum (R x : ℝ) (rootReach childReach : SixPointLabel → ℝ) : ℝ :=
  max (x + triangleMaximum rootReach) (R - x + triangleMaximum childReach)

/-- The diameter of a root-edge split after its same-color terms are reduced to `2M`. -/
def rootEdgeSplitDiameter (R M x : ℝ)
    (rootReach childReach : SixPointLabel → ℝ) : ℝ :=
  max (2 * M) (rootEdgeCrossMaximum R x rootReach childReach)

/-- Exact threshold form of the sixteen-term root-edge minimax. -/
theorem exists_rootEdge_split_iff {R M T : ℝ}
    {rootReach childReach : SixPointLabel → ℝ} (hR : 0 ≤ R) :
    (∃ x : ℝ, 0 ≤ x ∧ x ≤ R ∧
      rootEdgeSplitDiameter R M x rootReach childReach ≤ T) ↔
      2 * M ≤ T ∧ ( ∀ label, rootReach label ≤ T) ∧
      (∀ label, childReach label ≤ T) ∧
      ∀ rootLabel childLabel,
        R + rootReach rootLabel + childReach childLabel ≤ 2 * T := by
  constructor
  · rintro ⟨x, hx_zero, hx_R, hdiameter⟩
    simp only [rootEdgeSplitDiameter, rootEdgeCrossMaximum, max_le_iff] at hdiameter
    rcases hdiameter with ⟨hsame, hroot, hchild⟩
    refine ⟨hsame, ?_, ?_, ?_⟩
    · intro label
      nlinarith [le_triangleMaximum rootReach label]
    · intro label
      nlinarith [le_triangleMaximum childReach label]
    · intro rootLabel childLabel
      nlinarith [le_triangleMaximum rootReach rootLabel,
        le_triangleMaximum childReach childLabel]
  · rintro ⟨hsame, hroot, hchild, hbalanced⟩
    obtain ⟨rootLabel, hrootLabel⟩ := exists_triangleMaximum_eq rootReach
    obtain ⟨childLabel, hchildLabel⟩ := exists_triangleMaximum_eq childReach
    have hrootMax : triangleMaximum rootReach ≤ T := by
      rw [hrootLabel]
      exact hroot rootLabel
    have hchildMax : triangleMaximum childReach ≤ T := by
      rw [hchildLabel]
      exact hchild childLabel
    have hbalancedMax :
        R + triangleMaximum rootReach + triangleMaximum childReach ≤ 2 * T := by
      rw [hrootLabel, hchildLabel]
      exact hbalanced rootLabel childLabel
    let x := max 0 (R + triangleMaximum childReach - T)
    have hx_zero : 0 ≤ x := le_max_left _ _
    have hx_R : x ≤ R := by
      simp only [x, max_le_iff]
      constructor <;> linarith
    have hrootCross : x + triangleMaximum rootReach ≤ T := by
      simp only [x, max_add, max_le_iff]
      constructor <;> linarith
    have hchildCross : R - x + triangleMaximum childReach ≤ T := by
      nlinarith [le_max_right 0 (R + triangleMaximum childReach - T)]
    refine ⟨x, hx_zero, hx_R, ?_⟩
    simp only [rootEdgeSplitDiameter, rootEdgeCrossMaximum, max_le_iff]
    exact ⟨hsame, hrootCross, hchildCross⟩

/-- Failure of every root-edge split selects one of its sixteen routing terms. -/
theorem rootEdge_failure_routing {R M T : ℝ}
    {rootReach childReach : SixPointLabel → ℝ} (hR : 0 ≤ R)
    (hfail : ∀ x : ℝ, 0 ≤ x → x ≤ R →
      T < rootEdgeSplitDiameter R M x rootReach childReach) :
    T < 2 * M ∨ (∃ label, T < rootReach label) ∨
      (∃ label, T < childReach label) ∨
      ∃ rootLabel childLabel,
        2 * T < R + rootReach rootLabel + childReach childLabel := by
  by_contra hrouting
  simp only [not_or, not_exists, not_lt] at hrouting
  rcases hrouting with ⟨hsame, hroot, hchild, hbalanced⟩
  obtain ⟨x, hx_zero, hx_R, hdiameter⟩ :=
    (exists_rootEdge_split_iff hR).2 ⟨hsame, hroot, hchild, hbalanced⟩
  exact (not_lt_of_ge hdiameter) (hfail x hx_zero hx_R)

/-- The sixteen root-edge terms reduce pointwise to internal, `(1,1)`, or `(1,2)`. -/
theorem rootEdge_failure_reduces_to_three_types {R M T : ℝ}
    {rootReach childReach : SixPointLabel → ℝ} (hR : 0 < R)
    (hrootRoot : rootReach .root ≤ T - R) (hchildRoot : childReach .root ≤ T - R)
    (hleftLower : T - R ≤ rootReach .left)
    (hleftLargest : rootReach .right < rootReach .left)
    (hclose : ∀ label, label ≠ .root → rootReach label - R ≤ childReach label)
    (hroute : T < 2 * M ∨ (∃ label, T < rootReach label) ∨
      (∃ label, T < childReach label) ∨
      ∃ rootLabel childLabel,
        2 * T < R + rootReach rootLabel + childReach childLabel) :
    T < 2 * M ∨ 2 * T < R + rootReach .left + childReach .left ∨
      2 * T < R + rootReach .left + childReach .right := by
  rcases hroute with hinternal | hroot | hchild | hbalanced
  · exact Or.inl hinternal
  · rcases hroot with ⟨label, hlabel⟩
    cases label
    · exfalso
      linarith
    · exact Or.inr <| Or.inl <| by nlinarith [hclose .left (by simp)]
    · exact Or.inr <| Or.inr <| by
        nlinarith [hclose .right (by simp)]
  · rcases hchild with ⟨label, hlabel⟩
    cases label
    · exfalso
      linarith
    · exact Or.inr <| Or.inl <| by nlinarith
    · exact Or.inr <| Or.inr <| by nlinarith
  · rcases hbalanced with ⟨rootLabel, childLabel, hlabels⟩
    cases rootLabel <;> cases childLabel
    · exfalso
      linarith
    · exact Or.inr <| Or.inl <| by nlinarith
    · exact Or.inr <| Or.inr <| by nlinarith
    · exact Or.inr <| Or.inl <| by nlinarith [hclose .left (by simp)]
    · exact Or.inr <| Or.inl hlabels
    · exact Or.inr <| Or.inr hlabels
    · exact Or.inr <| Or.inr <| by nlinarith [hclose .right (by simp)]
    · exact Or.inr <| Or.inl <| by nlinarith
    · exact Or.inr <| Or.inr <| by nlinarith

/-- Supports `37` and `57`: a red root--child edge against the full blue triangle. -/
def redRootEdgeBlueTrianglePacking (configuration : SixPointConfiguration)
    (redLabel : SixPointLabel) (hredLabel : redLabel ≠ .root) {R x : ℝ}
    (hRdist : dist (configuration .red .root) (configuration .red redLabel) = R)
    (hR_one : R ≤ 1) (hx_zero : 0 ≤ x) (hx_R : x ≤ R)
    (hblueLeft : dist (configuration .blue .root) (configuration .blue .left) ≤ 1)
    (hblueRight : dist (configuration .blue .root) (configuration .blue .right) ≤ 1) :
    SixPointPacking configuration where
  support := {(.red, .root), (.red, redLabel), (.blue, .root), (.blue, .left),
    (.blue, .right)}
  meets_color color := by
    cases color
    · exact ⟨.root, by simp⟩
    · exact ⟨.root, by simp⟩
  radius i := by
    rcases i with ⟨⟨color, label⟩, hlabel⟩
    cases color
    · by_cases hroot : label = .root
      · exact ⟨x, hx_zero, hx_R.trans hR_one⟩
      · exact ⟨R - x, sub_nonneg.mpr hx_R, by linarith⟩
    · cases label
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
    · have hi' : li = .root ∨ li = redLabel := by simpa using hi
      have hj' : lj = .root ∨ lj = redLabel := by simpa using hj
      rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
      · exact (hij (Subtype.ext rfl)).elim
      · dsimp
        rw [hRdist]
        simp [hredLabel]
      · dsimp
        rw [dist_comm, hRdist]
        simp [hredLabel]
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

/-- The radius at the red root is the split variable. -/
@[simp] theorem redRootEdgeBlueTrianglePacking_radius_root
    (configuration : SixPointConfiguration) (redLabel : SixPointLabel)
    (hredLabel : redLabel ≠ .root) {R x : ℝ}
    (hRdist : dist (configuration .red .root) (configuration .red redLabel) = R)
    (hR_one : R ≤ 1) (hx_zero : 0 ≤ x) (hx_R : x ≤ R)
    (hblueLeft : dist (configuration .blue .root) (configuration .blue .left) ≤ 1)
    (hblueRight : dist (configuration .blue .root) (configuration .blue .right) ≤ 1)
    (hmem : (.red, .root) ∈ (redRootEdgeBlueTrianglePacking configuration redLabel
      hredLabel hRdist hR_one hx_zero hx_R hblueLeft hblueRight).support) :
    ((redRootEdgeBlueTrianglePacking configuration redLabel hredLabel hRdist hR_one hx_zero hx_R
      hblueLeft hblueRight).radius ⟨(.red, .root), hmem⟩ : ℝ) = x := by
  rfl

/-- The radius at the selected red child is the complementary split. -/
@[simp] theorem redRootEdgeBlueTrianglePacking_radius_child
    (configuration : SixPointConfiguration) (redLabel : SixPointLabel)
    (hredLabel : redLabel ≠ .root) {R x : ℝ}
    (hRdist : dist (configuration .red .root) (configuration .red redLabel) = R)
    (hR_one : R ≤ 1) (hx_zero : 0 ≤ x) (hx_R : x ≤ R)
    (hblueLeft : dist (configuration .blue .root) (configuration .blue .left) ≤ 1)
    (hblueRight : dist (configuration .blue .root) (configuration .blue .right) ≤ 1)
    (hmem : (.red, redLabel) ∈ (redRootEdgeBlueTrianglePacking configuration redLabel
      hredLabel hRdist hR_one hx_zero hx_R hblueLeft hblueRight).support) :
    ((redRootEdgeBlueTrianglePacking configuration redLabel hredLabel hRdist hR_one hx_zero hx_R
      hblueLeft hblueRight).radius ⟨(.red, redLabel), hmem⟩ : ℝ) = R - x := by
  simp [redRootEdgeBlueTrianglePacking, hredLabel]

/-- Blue radii in a red root-edge packing are the canonical triangle radii. -/
@[simp] theorem redRootEdgeBlueTrianglePacking_radius_blue
    (configuration : SixPointConfiguration) (redLabel : SixPointLabel)
    (hredLabel : redLabel ≠ .root) {R x : ℝ}
    (hRdist : dist (configuration .red .root) (configuration .red redLabel) = R)
    (hR_one : R ≤ 1) (hx_zero : 0 ≤ x) (hx_R : x ≤ R)
    (hblueLeft : dist (configuration .blue .root) (configuration .blue .left) ≤ 1)
    (hblueRight : dist (configuration .blue .root) (configuration .blue .right) ≤ 1)
    (label : SixPointLabel)
    (hmem : (.blue, label) ∈ (redRootEdgeBlueTrianglePacking configuration redLabel
      hredLabel hRdist hR_one hx_zero hx_R hblueLeft hblueRight).support) :
    ((redRootEdgeBlueTrianglePacking configuration redLabel hredLabel hRdist hR_one hx_zero hx_R
      hblueLeft hblueRight).radius ⟨(.blue, label), hmem⟩ : ℝ) =
      canonicalTriangleRadius (configuration .blue .root) (configuration .blue .left)
        (configuration .blue .right) label := by
  cases label <;> rfl

/-- The total radius of a red root-edge packing is its edge length plus a semiperimeter. -/
theorem redRootEdgeBlueTrianglePacking_totalRadius
    (configuration : SixPointConfiguration) (redLabel : SixPointLabel)
    (hredLabel : redLabel ≠ .root) {R x : ℝ}
    (hRdist : dist (configuration .red .root) (configuration .red redLabel) = R)
    (hR_one : R ≤ 1) (hx_zero : 0 ≤ x) (hx_R : x ≤ R)
    (hblueLeft : dist (configuration .blue .root) (configuration .blue .left) ≤ 1)
    (hblueRight : dist (configuration .blue .root) (configuration .blue .right) ≤ 1) :
    (redRootEdgeBlueTrianglePacking configuration redLabel hredLabel hRdist hR_one hx_zero hx_R
      hblueLeft hblueRight).totalRadius = R +
      (dist (configuration .blue .root) (configuration .blue .left) +
        dist (configuration .blue .root) (configuration .blue .right) +
          dist (configuration .blue .left) (configuration .blue .right)) / 2 := by
  let packing := redRootEdgeBlueTrianglePacking configuration redLabel hredLabel hRdist
    hR_one hx_zero hx_R hblueLeft hblueRight
  let value : SixPointIndex → ℝ
    | (.red, .root) => x
    | (.red, label) => if label = redLabel then R - x else 0
    | (.blue, label) => canonicalTriangleRadius (configuration .blue .root)
        (configuration .blue .left) (configuration .blue .right) label
  rw [SixPointPacking.totalRadius]
  calc
    _ = ∑ i ∈ packing.support.attach, value i := by
      apply Finset.sum_congr rfl
      rintro ⟨⟨color, label⟩, hi⟩ -
      cases color <;> cases label <;>
        simp [redRootEdgeBlueTrianglePacking, value] at hi ⊢ <;> simp_all
    _ = ∑ i ∈ packing.support, value i := Finset.sum_attach _ _
    _ = _ := by
      cases redLabel
      · exact (hredLabel rfl).elim
      · simp [packing, redRootEdgeBlueTrianglePacking, value, canonicalTriangleRadius]
        ring
      · simp [packing, redRootEdgeBlueTrianglePacking, value, canonicalTriangleRadius]
        ring

/-- Cross reach from the red root to a labelled blue triangle ball. -/
def redRootBlueTriangleReach (configuration : SixPointConfiguration)
    (label : SixPointLabel) : ℝ :=
  dist (configuration .red .root) (configuration .blue label) +
    canonicalTriangleRadius (configuration .blue .root) (configuration .blue .left)
      (configuration .blue .right) label

/-- Cross reach from a red child to a labelled blue triangle ball. -/
def redChildBlueTriangleReach (configuration : SixPointConfiguration)
    (redLabel blueLabel : SixPointLabel) : ℝ :=
  dist (configuration .red redLabel) (configuration .blue blueLabel) +
    canonicalTriangleRadius (configuration .blue .root) (configuration .blue .left)
      (configuration .blue .right) blueLabel

private theorem same_color_pair_le_twice_bound {configuration : SixPointConfiguration}
    (packing : SixPointPacking configuration) (i j : packing.support)
    (hcolor : i.1.1 = j.1.1) {bound : ℝ} (hbound : 1 ≤ bound)
    (hdist : dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) ≤ bound) :
    dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) +
      packing.radius i + packing.radius j ≤ 2 * bound := by
  by_cases hij : i = j
  · subst j
    simp only [dist_self, zero_add]
    nlinarith [(packing.radius i).property.2]
  · nlinarith [packing.same_color_disjoint i j hij hcolor]

/-- The virtual diameter of supports `37` and `57` is the root-edge split diameter. -/
theorem redRootEdgeBlueTrianglePacking_virtualDiameter
    (configuration : SixPointConfiguration) (redLabel : SixPointLabel)
    (hredLabel : redLabel ≠ .root) {R M x : ℝ}
    (hRdist : dist (configuration .red .root) (configuration .red redLabel) = R)
    (hMdist : dist (configuration .blue .left) (configuration .blue .right) = M)
    (hR_one : R ≤ 1) (hM : 1 ≤ M) (hx_zero : 0 ≤ x) (hx_R : x ≤ R)
    (hblueLeft : dist (configuration .blue .root) (configuration .blue .left) ≤ 1)
    (hblueRight : dist (configuration .blue .root) (configuration .blue .right) ≤ 1) :
    (redRootEdgeBlueTrianglePacking configuration redLabel hredLabel hRdist hR_one hx_zero hx_R
      hblueLeft hblueRight).virtualDiameter =
      rootEdgeSplitDiameter R M x (redRootBlueTriangleReach configuration)
        (redChildBlueTriangleReach configuration redLabel) := by
  let packing := redRootEdgeBlueTrianglePacking configuration redLabel hredLabel hRdist
    hR_one hx_zero hx_R hblueLeft hblueRight
  let target := rootEdgeSplitDiameter R M x (redRootBlueTriangleReach configuration)
    (redChildBlueTriangleReach configuration redLabel)
  have hredDist (leftLabel rightLabel : SixPointLabel)
      (hleft : (.red, leftLabel) ∈ packing.support)
      (hright : (.red, rightLabel) ∈ packing.support) :
      dist (configuration .red leftLabel) (configuration .red rightLabel) ≤ M := by
    have hleft' : leftLabel = .root ∨ leftLabel = redLabel := by
      simpa [packing, redRootEdgeBlueTrianglePacking] using hleft
    have hright' : rightLabel = .root ∨ rightLabel = redLabel := by
      simpa [packing, redRootEdgeBlueTrianglePacking] using hright
    rcases hleft' with hleft' | hleft' <;> rcases hright' with hright' | hright'
    · subst leftLabel
      subst rightLabel
      simpa using (show (0 : ℝ) ≤ M by linarith)
    · subst leftLabel
      subst rightLabel
      linarith
    · subst leftLabel
      subst rightLabel
      rw [dist_comm]
      linarith
    · subst leftLabel
      subst rightLabel
      simpa using (show (0 : ℝ) ≤ M by linarith)
  have hblueDist (leftLabel rightLabel : SixPointLabel) :
      dist (configuration .blue leftLabel) (configuration .blue rightLabel) ≤ M := by
    cases leftLabel <;> cases rightLabel
    · simpa using (show (0 : ℝ) ≤ M by linarith)
    · exact hblueLeft.trans hM
    · exact hblueRight.trans hM
    · simpa [dist_comm] using hblueLeft.trans hM
    · simpa using (show (0 : ℝ) ≤ M by linarith)
    · rw [hMdist]
    · simpa [dist_comm] using hblueRight.trans hM
    · rw [dist_comm, hMdist]
    · simpa using (show (0 : ℝ) ≤ M by linarith)
  have htwoM : 2 * M ≤ target := le_max_left _ _
  have hcrossRoot :
      x + triangleMaximum (redRootBlueTriangleReach configuration) ≤ target :=
    le_max_of_le_right (le_max_left _ _)
  have hcrossChild :
      R - x + triangleMaximum (redChildBlueTriangleReach configuration redLabel) ≤ target :=
    le_max_of_le_right (le_max_right _ _)
  have hrootRadius (hmem : (.red, .root) ∈ packing.support) :
      (packing.radius ⟨(.red, .root), hmem⟩ : ℝ) = x := by rfl
  have hchildRadius (hmem : (.red, redLabel) ∈ packing.support) :
      (packing.radius ⟨(.red, redLabel), hmem⟩ : ℝ) = R - x := by
    simp [packing, redRootEdgeBlueTrianglePacking, hredLabel]
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
    · exact (same_color_pair_le_twice_bound packing ⟨_, hleft⟩ ⟨_, hright⟩ rfl hM
        (hredDist leftLabel rightLabel hleft hright)).trans htwoM
    · have hlabel : leftLabel = .root ∨ leftLabel = redLabel := by
        simpa [packing, redRootEdgeBlueTrianglePacking] using hleft
      rcases hlabel with hlabel | hlabel
      · subst leftLabel
        rw [hrootRadius hleft, hblueRadius rightLabel hright]
        have hreach := le_triangleMaximum (redRootBlueTriangleReach configuration) rightLabel
        simp only [redRootBlueTriangleReach] at hreach
        nlinarith
      · subst leftLabel
        rw [hchildRadius hleft, hblueRadius rightLabel hright]
        have hreach :=
          le_triangleMaximum (redChildBlueTriangleReach configuration redLabel) rightLabel
        simp only [redChildBlueTriangleReach] at hreach
        nlinarith
    · have hlabel : rightLabel = .root ∨ rightLabel = redLabel := by
        simpa [packing, redRootEdgeBlueTrianglePacking] using hright
      rcases hlabel with hlabel | hlabel
      · subst rightLabel
        rw [hblueRadius leftLabel hleft, hrootRadius hright, dist_comm]
        have hreach := le_triangleMaximum (redRootBlueTriangleReach configuration) leftLabel
        simp only [redRootBlueTriangleReach] at hreach
        nlinarith
      · subst rightLabel
        rw [hblueRadius leftLabel hleft, hchildRadius hright, dist_comm]
        have hreach :=
          le_triangleMaximum (redChildBlueTriangleReach configuration redLabel) leftLabel
        simp only [redChildBlueTriangleReach] at hreach
        nlinarith
    · exact (same_color_pair_le_twice_bound packing ⟨_, hleft⟩ ⟨_, hright⟩ rfl hM
        (hblueDist leftLabel rightLabel)).trans htwoM
  apply le_antisymm
  · unfold SixPointPacking.virtualDiameter
    apply Finset.sup'_le
    intro i hi
    apply Finset.sup'_le
    intro j hj
    exact hpair i j
  · let redRoot : packing.support := ⟨(.red, .root), by
      simp [packing, redRootEdgeBlueTrianglePacking]⟩
    let redChild : packing.support := ⟨(.red, redLabel), by
      simp [packing, redRootEdgeBlueTrianglePacking]⟩
    let blueLeft : packing.support := ⟨(.blue, .left), by
      simp [packing, redRootEdgeBlueTrianglePacking]⟩
    let blueRight : packing.support := ⟨(.blue, .right), by
      simp [packing, redRootEdgeBlueTrianglePacking]⟩
    have hdiameterM : 2 * M ≤ packing.virtualDiameter := by
      have hpairM := packing.pair_le_virtualDiameter blueLeft blueRight
      rw [hblueRadius .left blueLeft.property, hblueRadius .right blueRight.property,
        hMdist] at hpairM
      nlinarith [canonicalTriangleRadius_left_add_right (configuration .blue .root)
        (configuration .blue .left) (configuration .blue .right)]
    have hrootPoint (label : SixPointLabel) :
        redRootBlueTriangleReach configuration label + x ≤ packing.virtualDiameter := by
      let blue : packing.support := ⟨(.blue, label), by
        cases label <;> simp [packing, redRootEdgeBlueTrianglePacking]⟩
      have hpairRoot := packing.pair_le_virtualDiameter redRoot blue
      rw [hrootRadius redRoot.property, hblueRadius label blue.property] at hpairRoot
      simp only [redRootBlueTriangleReach]
      linarith
    have hchildPoint (label : SixPointLabel) :
        redChildBlueTriangleReach configuration redLabel label + (R - x) ≤
          packing.virtualDiameter := by
      let blue : packing.support := ⟨(.blue, label), by
        cases label <;> simp [packing, redRootEdgeBlueTrianglePacking]⟩
      have hpairChild := packing.pair_le_virtualDiameter redChild blue
      rw [hchildRadius redChild.property, hblueRadius label blue.property] at hpairChild
      simp only [redChildBlueTriangleReach]
      linarith
    have hdiameterRoot :
        x + triangleMaximum (redRootBlueTriangleReach configuration) ≤
          packing.virtualDiameter := by
      simp only [triangleMaximum, add_max, max_le_iff]
      exact ⟨by nlinarith [hrootPoint .root], by nlinarith [hrootPoint .left],
        by nlinarith [hrootPoint .right]⟩
    have hdiameterChild :
        R - x + triangleMaximum (redChildBlueTriangleReach configuration redLabel) ≤
          packing.virtualDiameter := by
      rw [show R - x + triangleMaximum (redChildBlueTriangleReach configuration redLabel) =
        triangleMaximum (redChildBlueTriangleReach configuration redLabel) + (R - x) by ring]
      simp only [triangleMaximum, max_add, max_le_iff]
      exact ⟨hchildPoint .root, hchildPoint .left, hchildPoint .right⟩
    simp only [rootEdgeSplitDiameter, rootEdgeCrossMaximum, max_le_iff]
    exact ⟨hdiameterM, hdiameterRoot, hdiameterChild⟩

/-- Supports `73` and `75`: a blue root--child edge against the full red triangle. -/
def blueRootEdgeRedTrianglePacking (configuration : SixPointConfiguration)
    (blueLabel : SixPointLabel) (hblueLabel : blueLabel ≠ .root) {R x : ℝ}
    (hRdist : dist (configuration .blue .root) (configuration .blue blueLabel) = R)
    (hR_one : R ≤ 1) (hx_zero : 0 ≤ x) (hx_R : x ≤ R)
    (hredLeft : dist (configuration .red .root) (configuration .red .left) ≤ 1)
    (hredRight : dist (configuration .red .root) (configuration .red .right) ≤ 1) :
    SixPointPacking configuration where
  support := {(.blue, .root), (.blue, blueLabel), (.red, .root), (.red, .left),
    (.red, .right)}
  meets_color color := by
    cases color
    · exact ⟨.root, by simp⟩
    · exact ⟨.root, by simp⟩
  radius i := by
    rcases i with ⟨⟨color, label⟩, hlabel⟩
    cases color
    · cases label
      · exact ⟨_, canonicalTriangleRadius_nonneg _ _ _ .root,
          canonicalTriangleRadius_le_one _ _ _ hredLeft hredRight .root⟩
      · exact ⟨_, canonicalTriangleRadius_nonneg _ _ _ .left,
          canonicalTriangleRadius_le_one _ _ _ hredLeft hredRight .left⟩
      · exact ⟨_, canonicalTriangleRadius_nonneg _ _ _ .right,
          canonicalTriangleRadius_le_one _ _ _ hredLeft hredRight .right⟩
    · by_cases hroot : label = .root
      · exact ⟨x, hx_zero, hx_R.trans hR_one⟩
      · exact ⟨R - x, sub_nonneg.mpr hx_R, by linarith⟩
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
    · have hi' : li = .root ∨ li = blueLabel := by simpa using hi
      have hj' : lj = .root ∨ lj = blueLabel := by simpa using hj
      rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
      · exact (hij (Subtype.ext rfl)).elim
      · dsimp
        rw [hRdist]
        simp [hblueLabel]
      · dsimp
        rw [dist_comm, hRdist]
        simp [hblueLabel]
      · exact (hij (Subtype.ext rfl)).elim

/-- The total radius of a blue root-edge packing is its edge length plus a semiperimeter. -/
theorem blueRootEdgeRedTrianglePacking_totalRadius
    (configuration : SixPointConfiguration) (blueLabel : SixPointLabel)
    (hblueLabel : blueLabel ≠ .root) {R x : ℝ}
    (hRdist : dist (configuration .blue .root) (configuration .blue blueLabel) = R)
    (hR_one : R ≤ 1) (hx_zero : 0 ≤ x) (hx_R : x ≤ R)
    (hredLeft : dist (configuration .red .root) (configuration .red .left) ≤ 1)
    (hredRight : dist (configuration .red .root) (configuration .red .right) ≤ 1) :
    (blueRootEdgeRedTrianglePacking configuration blueLabel hblueLabel hRdist hR_one hx_zero hx_R
      hredLeft hredRight).totalRadius = R +
      (dist (configuration .red .root) (configuration .red .left) +
        dist (configuration .red .root) (configuration .red .right) +
          dist (configuration .red .left) (configuration .red .right)) / 2 := by
  let packing := blueRootEdgeRedTrianglePacking configuration blueLabel hblueLabel hRdist
    hR_one hx_zero hx_R hredLeft hredRight
  let value : SixPointIndex → ℝ
    | (.red, label) => canonicalTriangleRadius (configuration .red .root)
        (configuration .red .left) (configuration .red .right) label
    | (.blue, .root) => x
    | (.blue, label) => if label = blueLabel then R - x else 0
  rw [SixPointPacking.totalRadius]
  calc
    _ = ∑ i ∈ packing.support.attach, value i := by
      apply Finset.sum_congr rfl
      rintro ⟨⟨color, label⟩, hi⟩ -
      cases color <;> cases label <;>
        simp [blueRootEdgeRedTrianglePacking, value] at hi ⊢ <;> simp_all
    _ = ∑ i ∈ packing.support, value i := Finset.sum_attach _ _
    _ = _ := by
      cases blueLabel
      · exact (hblueLabel rfl).elim
      · simp [packing, blueRootEdgeRedTrianglePacking, value, canonicalTriangleRadius]
        ring
      · simp [packing, blueRootEdgeRedTrianglePacking, value, canonicalTriangleRadius]
        ring

/-- Cross reach from the blue root to a labelled red triangle ball. -/
def blueRootRedTriangleReach (configuration : SixPointConfiguration)
    (label : SixPointLabel) : ℝ :=
  dist (configuration .blue .root) (configuration .red label) +
    canonicalTriangleRadius (configuration .red .root) (configuration .red .left)
      (configuration .red .right) label

/-- Cross reach from a blue child to a labelled red triangle ball. -/
def blueChildRedTriangleReach (configuration : SixPointConfiguration)
    (blueLabel redLabel : SixPointLabel) : ℝ :=
  dist (configuration .blue blueLabel) (configuration .red redLabel) +
    canonicalTriangleRadius (configuration .red .root) (configuration .red .left)
      (configuration .red .right) redLabel

/-- The virtual diameter of supports `73` and `75` is the root-edge split diameter. -/
theorem blueRootEdgeRedTrianglePacking_virtualDiameter
    (configuration : SixPointConfiguration) (blueLabel : SixPointLabel)
    (hblueLabel : blueLabel ≠ .root) {R L x : ℝ}
    (hRdist : dist (configuration .blue .root) (configuration .blue blueLabel) = R)
    (hLdist : dist (configuration .red .left) (configuration .red .right) = L)
    (hR_one : R ≤ 1) (hL : 1 ≤ L) (hx_zero : 0 ≤ x) (hx_R : x ≤ R)
    (hredLeft : dist (configuration .red .root) (configuration .red .left) ≤ 1)
    (hredRight : dist (configuration .red .root) (configuration .red .right) ≤ 1) :
    (blueRootEdgeRedTrianglePacking configuration blueLabel hblueLabel hRdist hR_one hx_zero hx_R
      hredLeft hredRight).virtualDiameter =
      rootEdgeSplitDiameter R L x (blueRootRedTriangleReach configuration)
        (blueChildRedTriangleReach configuration blueLabel) := by
  let packing := blueRootEdgeRedTrianglePacking configuration blueLabel hblueLabel hRdist
    hR_one hx_zero hx_R hredLeft hredRight
  let target := rootEdgeSplitDiameter R L x (blueRootRedTriangleReach configuration)
    (blueChildRedTriangleReach configuration blueLabel)
  have hblueDist (leftLabel rightLabel : SixPointLabel)
      (hleft : (.blue, leftLabel) ∈ packing.support)
      (hright : (.blue, rightLabel) ∈ packing.support) :
      dist (configuration .blue leftLabel) (configuration .blue rightLabel) ≤ L := by
    have hleft' : leftLabel = .root ∨ leftLabel = blueLabel := by
      simpa [packing, blueRootEdgeRedTrianglePacking] using hleft
    have hright' : rightLabel = .root ∨ rightLabel = blueLabel := by
      simpa [packing, blueRootEdgeRedTrianglePacking] using hright
    rcases hleft' with hleft' | hleft' <;> rcases hright' with hright' | hright'
    · subst leftLabel
      subst rightLabel
      simpa using (show (0 : ℝ) ≤ L by linarith)
    · subst leftLabel
      subst rightLabel
      linarith
    · subst leftLabel
      subst rightLabel
      rw [dist_comm]
      linarith
    · subst leftLabel
      subst rightLabel
      simpa using (show (0 : ℝ) ≤ L by linarith)
  have hredDist (leftLabel rightLabel : SixPointLabel) :
      dist (configuration .red leftLabel) (configuration .red rightLabel) ≤ L := by
    cases leftLabel <;> cases rightLabel
    · simpa using (show (0 : ℝ) ≤ L by linarith)
    · exact hredLeft.trans hL
    · exact hredRight.trans hL
    · simpa [dist_comm] using hredLeft.trans hL
    · simpa using (show (0 : ℝ) ≤ L by linarith)
    · rw [hLdist]
    · simpa [dist_comm] using hredRight.trans hL
    · rw [dist_comm, hLdist]
    · simpa using (show (0 : ℝ) ≤ L by linarith)
  have htwoL : 2 * L ≤ target := le_max_left _ _
  have hcrossRoot :
      x + triangleMaximum (blueRootRedTriangleReach configuration) ≤ target :=
    le_max_of_le_right (le_max_left _ _)
  have hcrossChild :
      R - x + triangleMaximum (blueChildRedTriangleReach configuration blueLabel) ≤ target :=
    le_max_of_le_right (le_max_right _ _)
  have hrootRadius (hmem : (.blue, .root) ∈ packing.support) :
      (packing.radius ⟨(.blue, .root), hmem⟩ : ℝ) = x := by rfl
  have hchildRadius (hmem : (.blue, blueLabel) ∈ packing.support) :
      (packing.radius ⟨(.blue, blueLabel), hmem⟩ : ℝ) = R - x := by
    simp [packing, blueRootEdgeRedTrianglePacking, hblueLabel]
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
    · exact (same_color_pair_le_twice_bound packing ⟨_, hleft⟩ ⟨_, hright⟩ rfl hL
        (hredDist leftLabel rightLabel)).trans htwoL
    · have hlabel : rightLabel = .root ∨ rightLabel = blueLabel := by
        simpa [packing, blueRootEdgeRedTrianglePacking] using hright
      rcases hlabel with hlabel | hlabel
      · subst rightLabel
        rw [hredRadius leftLabel hleft, hrootRadius hright, dist_comm]
        have hreach := le_triangleMaximum (blueRootRedTriangleReach configuration) leftLabel
        simp only [blueRootRedTriangleReach] at hreach
        nlinarith
      · subst rightLabel
        rw [hredRadius leftLabel hleft, hchildRadius hright, dist_comm]
        have hreach :=
          le_triangleMaximum (blueChildRedTriangleReach configuration blueLabel) leftLabel
        simp only [blueChildRedTriangleReach] at hreach
        nlinarith
    · have hlabel : leftLabel = .root ∨ leftLabel = blueLabel := by
        simpa [packing, blueRootEdgeRedTrianglePacking] using hleft
      rcases hlabel with hlabel | hlabel
      · subst leftLabel
        rw [hrootRadius hleft, hredRadius rightLabel hright]
        have hreach := le_triangleMaximum (blueRootRedTriangleReach configuration) rightLabel
        simp only [blueRootRedTriangleReach] at hreach
        nlinarith
      · subst leftLabel
        rw [hchildRadius hleft, hredRadius rightLabel hright]
        have hreach :=
          le_triangleMaximum (blueChildRedTriangleReach configuration blueLabel) rightLabel
        simp only [blueChildRedTriangleReach] at hreach
        nlinarith
    · exact (same_color_pair_le_twice_bound packing ⟨_, hleft⟩ ⟨_, hright⟩ rfl hL
        (hblueDist leftLabel rightLabel hleft hright)).trans htwoL
  apply le_antisymm
  · unfold SixPointPacking.virtualDiameter
    apply Finset.sup'_le
    intro i hi
    apply Finset.sup'_le
    intro j hj
    exact hpair i j
  · let blueRoot : packing.support := ⟨(.blue, .root), by
      simp [packing, blueRootEdgeRedTrianglePacking]⟩
    let blueChild : packing.support := ⟨(.blue, blueLabel), by
      simp [packing, blueRootEdgeRedTrianglePacking]⟩
    let redLeft : packing.support := ⟨(.red, .left), by
      simp [packing, blueRootEdgeRedTrianglePacking]⟩
    let redRight : packing.support := ⟨(.red, .right), by
      simp [packing, blueRootEdgeRedTrianglePacking]⟩
    have hdiameterL : 2 * L ≤ packing.virtualDiameter := by
      have hpairL := packing.pair_le_virtualDiameter redLeft redRight
      rw [hredRadius .left redLeft.property, hredRadius .right redRight.property,
        hLdist] at hpairL
      nlinarith [canonicalTriangleRadius_left_add_right (configuration .red .root)
        (configuration .red .left) (configuration .red .right)]
    have hrootPoint (label : SixPointLabel) :
        blueRootRedTriangleReach configuration label + x ≤ packing.virtualDiameter := by
      let red : packing.support := ⟨(.red, label), by
        cases label <;> simp [packing, blueRootEdgeRedTrianglePacking]⟩
      have hpairRoot := packing.pair_le_virtualDiameter blueRoot red
      rw [hrootRadius blueRoot.property, hredRadius label red.property] at hpairRoot
      simp only [blueRootRedTriangleReach]
      linarith
    have hchildPoint (label : SixPointLabel) :
        blueChildRedTriangleReach configuration blueLabel label + (R - x) ≤
          packing.virtualDiameter := by
      let red : packing.support := ⟨(.red, label), by
        cases label <;> simp [packing, blueRootEdgeRedTrianglePacking]⟩
      have hpairChild := packing.pair_le_virtualDiameter blueChild red
      rw [hchildRadius blueChild.property, hredRadius label red.property] at hpairChild
      simp only [blueChildRedTriangleReach]
      linarith
    have hdiameterRoot :
        x + triangleMaximum (blueRootRedTriangleReach configuration) ≤
          packing.virtualDiameter := by
      simp only [triangleMaximum, add_max, max_le_iff]
      exact ⟨by nlinarith [hrootPoint .root], by nlinarith [hrootPoint .left],
        by nlinarith [hrootPoint .right]⟩
    have hdiameterChild :
        R - x + triangleMaximum (blueChildRedTriangleReach configuration blueLabel) ≤
          packing.virtualDiameter := by
      rw [show R - x + triangleMaximum (blueChildRedTriangleReach configuration blueLabel) =
        triangleMaximum (blueChildRedTriangleReach configuration blueLabel) + (R - x) by ring]
      simp only [triangleMaximum, max_add, max_le_iff]
      exact ⟨hchildPoint .root, hchildPoint .left, hchildPoint .right⟩
    simp only [rootEdgeSplitDiameter, rootEdgeCrossMaximum, max_le_iff]
    exact ⟨hdiameterL, hdiameterRoot, hdiameterChild⟩

private theorem norm_tangent {E : Type*} [SeminormedAddCommGroup E] (x : E) {r : ℝ}
    (hr : 0 < r) : ‖x‖ ≤ (‖x‖ ^ 2 + r ^ 2) / (2 * r) := by
  rw [le_div_iff₀ (by positivity : 0 < 2 * r)]
  nlinarith [sq_nonneg (‖x‖ - r)]

private theorem weighted_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖a • x + b • y‖ ^ 2 =
      (a + b) * (a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2) - a * b * ‖x - y‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb,
    real_inner_smul_left, real_inner_smul_right]
  ring

private def twoPointGain (A rho : ℝ) : ℝ := A / rho

private def twoPointUpper (c A₁ A₂ rho₁ rho₂ sigma d₁ d₂ t₁ t₂ : ℝ) : ℝ :=
  A₁ / (2 * rho₁) * (1 + rho₁ ^ 2 + 4 * t₁ ^ 2) +
    A₂ / (2 * rho₂) * (1 + rho₂ ^ 2 + 4 * t₂ ^ 2) + sigma +
    (((twoPointGain A₁ rho₁ + twoPointGain A₂ rho₂) *
        (twoPointGain A₁ rho₁ * t₁ ^ 2 + twoPointGain A₂ rho₂ * t₂ ^ 2) -
      twoPointGain A₁ rho₁ * twoPointGain A₂ rho₂ * c ^ 2) / sigma) -
    d₁ * t₁ - d₂ * t₂

private theorem twoPointTangent_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e x₁ x₂ : E) {c A₁ A₂ rho₁ rho₂ sigma d₁ d₂ : ℝ}
    (he : ‖e‖ = 1) (hseparation : c ≤ ‖x₁ - x₂‖) (hc : 0 ≤ c)
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hrho₁ : 0 < rho₁) (hrho₂ : 0 < rho₂)
    (hsigma : 0 < sigma) :
    A₁ * ‖e - (2 : ℝ) • x₁‖ + A₂ * ‖e - (2 : ℝ) • x₂‖ -
        d₁ * ‖x₁‖ - d₂ * ‖x₂‖ ≤
      twoPointUpper c A₁ A₂ rho₁ rho₂ sigma d₁ d₂ ‖x₁‖ ‖x₂‖ := by
  let g₁ := twoPointGain A₁ rho₁
  let g₂ := twoPointGain A₂ rho₂
  have hg₁ : 0 ≤ g₁ := div_nonneg hA₁ hrho₁.le
  have hg₂ : 0 ≤ g₂ := div_nonneg hA₂ hrho₂.le
  have htangent₁ : A₁ * ‖e - (2 : ℝ) • x₁‖ ≤
      A₁ / (2 * rho₁) * (‖e - (2 : ℝ) • x₁‖ ^ 2 + rho₁ ^ 2) := by
    have h := mul_le_mul_of_nonneg_left (norm_tangent (e - (2 : ℝ) • x₁) hrho₁) hA₁
    calc
      _ ≤ _ := h
      _ = _ := by ring
  have htangent₂ : A₂ * ‖e - (2 : ℝ) • x₂‖ ≤
      A₂ / (2 * rho₂) * (‖e - (2 : ℝ) • x₂‖ ^ 2 + rho₂ ^ 2) := by
    have h := mul_le_mul_of_nonneg_left (norm_tangent (e - (2 : ℝ) • x₂) hrho₂) hA₂
    calc
      _ ≤ _ := h
      _ = _ := by ring
  have hsquare (x : E) : ‖e - (2 : ℝ) • x‖ ^ 2 =
      1 + 4 * ‖x‖ ^ 2 - 4 * ⟪e, x⟫_ℝ := by
    rw [norm_sub_sq_real]
    simp only [he, one_pow, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num :
      (0 : ℝ) ≤ 2), real_inner_smul_right]
    ring
  let u := g₁ • x₁ + g₂ • x₂
  have hsep_sq : c ^ 2 ≤ ‖x₁ - x₂‖ ^ 2 := by
    nlinarith [norm_nonneg (x₁ - x₂)]
  have hu_sq : ‖u‖ ^ 2 ≤
      (g₁ + g₂) * (g₁ * ‖x₁‖ ^ 2 + g₂ * ‖x₂‖ ^ 2) - g₁ * g₂ * c ^ 2 := by
    rw [show ‖u‖ ^ 2 =
      (g₁ + g₂) * (g₁ * ‖x₁‖ ^ 2 + g₂ * ‖x₂‖ ^ 2) -
        g₁ * g₂ * ‖x₁ - x₂‖ ^ 2 by
      exact weighted_norm_sq x₁ x₂ hg₁ hg₂]
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left hsep_sq (mul_nonneg hg₁ hg₂)) _
  have horientation : -2 * ⟪e, u⟫_ℝ ≤ sigma + ‖u‖ ^ 2 / sigma := by
    have hinner := real_inner_le_norm (-e) u
    simp only [inner_neg_left, norm_neg, he, one_mul] at hinner
    have hnorm : 2 * ‖u‖ ≤ sigma + ‖u‖ ^ 2 / sigma := by
      have h := norm_tangent u hsigma
      rw [show (‖u‖ ^ 2 + sigma ^ 2) / (2 * sigma) =
        (sigma + ‖u‖ ^ 2 / sigma) / 2 by field_simp; ring] at h
      linarith
    nlinarith
  have hu_scaled := (div_le_div_iff_of_pos_right hsigma).2 hu_sq
  have htangentSum := add_le_add htangent₁ htangent₂
  rw [hsquare x₁, hsquare x₂] at htangentSum
  have htangentSum' :
      A₁ * ‖e - (2 : ℝ) • x₁‖ + A₂ * ‖e - (2 : ℝ) • x₂‖ ≤
        A₁ / (2 * rho₁) * (1 + rho₁ ^ 2 + 4 * ‖x₁‖ ^ 2) +
          A₂ / (2 * rho₂) * (1 + rho₂ ^ 2 + 4 * ‖x₂‖ ^ 2) -
          2 * (twoPointGain A₁ rho₁ * ⟪e, x₁⟫_ℝ +
            twoPointGain A₂ rho₂ * ⟪e, x₂⟫_ℝ) := by
    calc
      _ ≤ _ := htangentSum
      _ = _ := by
        simp only [twoPointGain]
        field_simp [ne_of_gt hrho₁, ne_of_gt hrho₂]
        ring
  dsimp only [u, g₁, g₂] at horientation hu_scaled ⊢
  simp only [inner_add_right, real_inner_smul_right] at horientation
  have horientationBound :
      -2 * (twoPointGain A₁ rho₁ * ⟪e, x₁⟫_ℝ +
          twoPointGain A₂ rho₂ * ⟪e, x₂⟫_ℝ) ≤
        sigma +
          ((twoPointGain A₁ rho₁ + twoPointGain A₂ rho₂) *
              (twoPointGain A₁ rho₁ * ‖x₁‖ ^ 2 +
                twoPointGain A₂ rho₂ * ‖x₂‖ ^ 2) -
            twoPointGain A₁ rho₁ * twoPointGain A₂ rho₂ * c ^ 2) / sigma := by
    exact horientation.trans (add_le_add_right hu_scaled sigma)
  simp only [twoPointGain] at htangentSum' horientationBound
  simp only [twoPointUpper, twoPointGain] at ⊢
  linarith

private def twoPointQuadratic1 (A₁ A₂ rho₁ rho₂ sigma : ℝ) : ℝ :=
  2 * A₁ / rho₁ +
    (twoPointGain A₁ rho₁ + twoPointGain A₂ rho₂) * twoPointGain A₁ rho₁ / sigma

private def twoPointQuadratic2 (A₁ A₂ rho₁ rho₂ sigma : ℝ) : ℝ :=
  2 * A₂ / rho₂ +
    (twoPointGain A₁ rho₁ + twoPointGain A₂ rho₂) * twoPointGain A₂ rho₂ / sigma

private def twoPointBase (c A₁ A₂ rho₁ rho₂ sigma : ℝ) : ℝ :=
  A₁ / (2 * rho₁) * (1 + rho₁ ^ 2) + A₂ / (2 * rho₂) * (1 + rho₂ ^ 2) +
    sigma - twoPointGain A₁ rho₁ * twoPointGain A₂ rho₂ * c ^ 2 / sigma

private theorem twoPointUpper_eq_quadratic
    (c A₁ A₂ rho₁ rho₂ sigma d₁ d₂ t₁ t₂ : ℝ) :
    twoPointUpper c A₁ A₂ rho₁ rho₂ sigma d₁ d₂ t₁ t₂ =
      twoPointBase c A₁ A₂ rho₁ rho₂ sigma +
        twoPointQuadratic1 A₁ A₂ rho₁ rho₂ sigma * t₁ ^ 2 +
        twoPointQuadratic2 A₁ A₂ rho₁ rho₂ sigma * t₂ ^ 2 -
          d₁ * t₁ - d₂ * t₂ := by
  simp only [twoPointUpper, twoPointBase, twoPointQuadratic1, twoPointQuadratic2,
    twoPointGain]
  ring

private theorem quadratic_le_max_endpoints {a b d l x u : ℝ} (ha : 0 ≤ a)
    (hlx : l ≤ x) (hxu : x ≤ u) :
    a * x ^ 2 + b * x + d ≤
      max (a * l ^ 2 + b * l + d) (a * u ^ 2 + b * u + d) := by
  by_cases hlu : l = u
  · subst u
    have hx : x = l := le_antisymm hxu hlx
    subst x
    exact le_max_left _ _
  have hwidth : 0 < u - l := sub_pos.mpr (lt_of_le_of_ne (hlx.trans hxu) hlu)
  have hleft : a * l ^ 2 + b * l + d ≤
      max (a * l ^ 2 + b * l + d) (a * u ^ 2 + b * u + d) := le_max_left _ _
  have hright : a * u ^ 2 + b * u + d ≤
      max (a * l ^ 2 + b * l + d) (a * u ^ 2 + b * u + d) := le_max_right _ _
  have hcurve : a * (x - l) * (x - u) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha (sub_nonneg.mpr hlx))
      (sub_nonpos.mpr hxu)
  have hleftWeight : 0 ≤ u - x := sub_nonneg.mpr hxu
  have hrightWeight : 0 ≤ x - l := sub_nonneg.mpr hlx
  have hsecant :
      (u - l) * (a * x ^ 2 + b * x + d) ≤
        (u - x) * (a * l ^ 2 + b * l + d) +
          (x - l) * (a * u ^ 2 + b * u + d) := by
    nlinarith
  have hbound :
      (u - x) * (a * l ^ 2 + b * l + d) +
          (x - l) * (a * u ^ 2 + b * u + d) ≤
        (u - l) * max (a * l ^ 2 + b * l + d) (a * u ^ 2 + b * u + d) := by
    nlinarith [mul_le_mul_of_nonneg_left hleft hleftWeight,
      mul_le_mul_of_nonneg_left hright hrightWeight]
  exact (mul_le_mul_iff_of_pos_left hwidth).mp (hsecant.trans hbound)

private theorem twoPointUpper_le_vertices
    {c A₁ A₂ rho₁ rho₂ sigma d₁ d₂ t₁ t₂ : ℝ}
    (hquadratic1 : 0 ≤ twoPointQuadratic1 A₁ A₂ rho₁ rho₂ sigma)
    (hquadratic2 : 0 ≤ twoPointQuadratic2 A₁ A₂ rho₁ rho₂ sigma)
    (ht₁_one : t₁ ≤ 1) (ht₂_one : t₂ ≤ 1) (hsum : c ≤ t₁ + t₂) :
    twoPointUpper c A₁ A₂ rho₁ rho₂ sigma d₁ d₂ t₁ t₂ ≤
      max (twoPointUpper c A₁ A₂ rho₁ rho₂ sigma d₁ d₂ 1 1)
        (max (twoPointUpper c A₁ A₂ rho₁ rho₂ sigma d₁ d₂ 1 (c - 1))
          (twoPointUpper c A₁ A₂ rho₁ rho₂ sigma d₁ d₂ (c - 1) 1)) := by
  have ht₁_lower : c - 1 ≤ t₁ := by linarith
  have ht₂_lower : c - 1 ≤ t₂ := by linarith
  have hsecond :
      twoPointUpper c A₁ A₂ rho₁ rho₂ sigma d₁ d₂ t₁ t₂ ≤
        max (twoPointUpper c A₁ A₂ rho₁ rho₂ sigma d₁ d₂ t₁ (c - t₁))
          (twoPointUpper c A₁ A₂ rho₁ rho₂ sigma d₁ d₂ t₁ 1) := by
    have h := quadratic_le_max_endpoints hquadratic2
      (show c - t₁ ≤ t₂ by linarith) ht₂_one (b := -d₂)
      (d := twoPointBase c A₁ A₂ rho₁ rho₂ sigma +
        twoPointQuadratic1 A₁ A₂ rho₁ rho₂ sigma * t₁ ^ 2 - d₁ * t₁)
    rw [twoPointUpper_eq_quadratic, twoPointUpper_eq_quadratic,
      twoPointUpper_eq_quadratic]
    convert h using 1 <;> ring_nf
  have hdiagonal :
      twoPointUpper c A₁ A₂ rho₁ rho₂ sigma d₁ d₂ t₁ (c - t₁) ≤
        max (twoPointUpper c A₁ A₂ rho₁ rho₂ sigma d₁ d₂ (c - 1) 1)
          (twoPointUpper c A₁ A₂ rho₁ rho₂ sigma d₁ d₂ 1 (c - 1)) := by
    have h := quadratic_le_max_endpoints (add_nonneg hquadratic1 hquadratic2)
      ht₁_lower ht₁_one
      (b := -2 * twoPointQuadratic2 A₁ A₂ rho₁ rho₂ sigma * c - d₁ + d₂)
      (d := twoPointBase c A₁ A₂ rho₁ rho₂ sigma +
        twoPointQuadratic2 A₁ A₂ rho₁ rho₂ sigma * c ^ 2 - d₂ * c)
    rw [twoPointUpper_eq_quadratic, twoPointUpper_eq_quadratic,
      twoPointUpper_eq_quadratic]
    convert h using 1 <;> ring_nf
  have htop :
      twoPointUpper c A₁ A₂ rho₁ rho₂ sigma d₁ d₂ t₁ 1 ≤
        max (twoPointUpper c A₁ A₂ rho₁ rho₂ sigma d₁ d₂ (c - 1) 1)
          (twoPointUpper c A₁ A₂ rho₁ rho₂ sigma d₁ d₂ 1 1) := by
    have h := quadratic_le_max_endpoints hquadratic1 ht₁_lower ht₁_one (b := -d₁)
      (d := twoPointBase c A₁ A₂ rho₁ rho₂ sigma +
        twoPointQuadratic2 A₁ A₂ rho₁ rho₂ sigma - d₂)
    rw [twoPointUpper_eq_quadratic, twoPointUpper_eq_quadratic,
      twoPointUpper_eq_quadratic]
    convert h using 1 <;> ring_nf
  refine hsecond.trans (max_le ?_ ?_)
  · exact hdiagonal.trans <| max_le
      (le_max_right _ _ |>.trans <| le_max_right _ _)
      (le_max_left _ _ |>.trans <| le_max_right _ _)
  · exact htop.trans <| max_le
      (le_max_right _ _ |>.trans <| le_max_right _ _)
      (le_max_left _ _)

private def redPointUpper (c t₁ t₂ : ℝ) : ℝ :=
  twoPointUpper c (25 / 2) (19 / 2) (14 / 5) (7 / 4) (407 / 100) 0 (24 * c) t₁ t₂

private def bluePointUpper (c t₁ t₂ : ℝ) : ℝ :=
  twoPointUpper c (25 / 2) (19 / 2) (113 / 40) (213 / 100) (24 / 5)
    (15 * c - 3) (15 * c + 3) t₁ t₂

private def redPointVertex0 (c : ℝ) : ℝ :=
  627494429 / 7977200 - 24 * c - 118750 / 19943 * c ^ 2

private def redPointVertex1 (c : ℝ) : ℝ :=
  627494429 / 7977200 - 480716 / 19943 * c - 117708 / 19943 * c ^ 2

private def redPointVertex2 (c : ℝ) : ℝ :=
  627494429 / 7977200 - 2535139 / 39886 * c + 1102875 / 79772 * c ^ 2

private def bluePointVertex0 (c : ℝ) : ℝ :=
  99038091574697 / 1390360226400 - 30 * c - 296875 / 72207 * c ^ 2

private def bluePointVertex1 (c : ℝ) : ℝ :=
  107380252933097 / 1390360226400 - 574473748 / 15380091 * c -
    526885 / 272214 * c ^ 2

private def bluePointVertex2 (c : ℝ) : ℝ :=
  90695930216297 / 1390360226400 - 253592077 / 8159391 * c -
    79355 / 38307 * c ^ 2

private theorem redPointUpper_vertices (c : ℝ) :
    redPointUpper c 1 1 = redPointVertex0 c ∧
      redPointUpper c 1 (c - 1) = redPointVertex1 c ∧
      redPointUpper c (c - 1) 1 = redPointVertex2 c := by
  norm_num [redPointUpper, redPointVertex0, redPointVertex1, redPointVertex2,
    twoPointUpper, twoPointGain]
  constructor
  · ring
  constructor <;> ring

private theorem bluePointUpper_vertices (c : ℝ) :
    bluePointUpper c 1 1 = bluePointVertex0 c ∧
      bluePointUpper c 1 (c - 1) = bluePointVertex1 c ∧
      bluePointUpper c (c - 1) 1 = bluePointVertex2 c := by
  norm_num [bluePointUpper, bluePointVertex0, bluePointVertex1, bluePointVertex2,
    twoPointUpper, twoPointGain]
  constructor
  · ring
  constructor <;> ring

private theorem redPointVertex_dominates :
    redPointVertex1 barC < redPointVertex0 barC ∧
      redPointVertex2 barC < redPointVertex0 barC := by
  rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
  norm_num [redPointVertex0, redPointVertex1, redPointVertex2] at hlower hupper ⊢
  constructor <;> nlinarith [sq_nonneg (barC - 13866128436518096 / 10 ^ 16)]

private theorem bluePointVertex_dominates :
    bluePointVertex1 barC < bluePointVertex0 barC ∧
      bluePointVertex2 barC < bluePointVertex0 barC := by
  rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
  norm_num [bluePointVertex0, bluePointVertex1, bluePointVertex2] at hlower hupper ⊢
  constructor <;> nlinarith [sq_nonneg (barC - 13866128436518096 / 10 ^ 16)]

private theorem redPointUpper_le_vertex0 {t₁ t₂ : ℝ} (ht₁ : t₁ ≤ 1) (ht₂ : t₂ ≤ 1)
    (hsum : barC ≤ t₁ + t₂) : redPointUpper barC t₁ t₂ ≤ redPointVertex0 barC := by
  have hvertices := twoPointUpper_le_vertices
    (c := barC) (A₁ := 25 / 2) (A₂ := 19 / 2) (rho₁ := 14 / 5) (rho₂ := 7 / 4)
    (sigma := 407 / 100) (d₁ := 0) (d₂ := 24 * barC) (t₁ := t₁) (t₂ := t₂)
    (by norm_num [twoPointQuadratic1, twoPointGain])
    (by norm_num [twoPointQuadratic2, twoPointGain]) ht₁ ht₂ hsum
  rw [← redPointUpper, ← redPointUpper, ← redPointUpper, ← redPointUpper] at hvertices
  rw [redPointUpper_vertices barC |>.1, redPointUpper_vertices barC |>.2.1,
    redPointUpper_vertices barC |>.2.2] at hvertices
  exact hvertices.trans <| max_le (le_rfl) <| max_le
    redPointVertex_dominates.1.le redPointVertex_dominates.2.le

private theorem bluePointUpper_le_vertex0 {t₁ t₂ : ℝ} (ht₁ : t₁ ≤ 1)
    (ht₂ : t₂ ≤ 1) (hsum : barC ≤ t₁ + t₂) :
    bluePointUpper barC t₁ t₂ ≤ bluePointVertex0 barC := by
  have hvertices := twoPointUpper_le_vertices
    (c := barC) (A₁ := 25 / 2) (A₂ := 19 / 2) (rho₁ := 113 / 40)
    (rho₂ := 213 / 100) (sigma := 24 / 5) (d₁ := 15 * barC - 3)
    (d₂ := 15 * barC + 3) (t₁ := t₁) (t₂ := t₂)
    (by norm_num [twoPointQuadratic1, twoPointGain])
    (by norm_num [twoPointQuadratic2, twoPointGain]) ht₁ ht₂ hsum
  rw [← bluePointUpper, ← bluePointUpper, ← bluePointUpper, ← bluePointUpper] at hvertices
  rw [bluePointUpper_vertices barC |>.1, bluePointUpper_vertices barC |>.2.1,
    bluePointUpper_vertices barC |>.2.2] at hvertices
  exact hvertices.trans <| max_le (le_rfl) <| max_le
    bluePointVertex_dominates.1.le bluePointVertex_dominates.2.le

private theorem redPointTangent_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ : E) (he : ‖e‖ = 1) (hp₁ : ‖p₁‖ ≤ 1)
    (hp₂ : ‖p₂‖ ≤ 1) (hseparation : barC ≤ ‖p₁ - p₂‖) :
    (25 / 2) * ‖e - (2 : ℝ) • p₁‖ + (19 / 2) * ‖e - (2 : ℝ) • p₂‖ -
        24 * barC * ‖p₂‖ ≤ redPointVertex0 barC := by
  have htangent := twoPointTangent_le e p₁ p₂ (c := barC) (A₁ := 25 / 2)
    (A₂ := 19 / 2) (rho₁ := 14 / 5) (rho₂ := 7 / 4) (sigma := 407 / 100)
    (d₁ := 0) (d₂ := 24 * barC) he hseparation barC_pos.le
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hsum : barC ≤ ‖p₁‖ + ‖p₂‖ :=
    hseparation.trans (norm_sub_le p₁ p₂)
  have hupper : redPointUpper barC ‖p₁‖ ‖p₂‖ ≤ redPointVertex0 barC :=
    redPointUpper_le_vertex0 hp₁ hp₂ hsum
  simpa only [redPointUpper, zero_mul, sub_zero] using htangent.trans hupper

private theorem bluePointTangent_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e w₁ w₂ : E) (he : ‖e‖ = 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1) (hseparation : barC ≤ ‖w₁ - w₂‖) :
    (25 / 2) * ‖e - (2 : ℝ) • w₁‖ + (19 / 2) * ‖e - (2 : ℝ) • w₂‖ -
        (15 * barC - 3) * ‖w₁‖ - (15 * barC + 3) * ‖w₂‖ ≤
      bluePointVertex0 barC := by
  have htangent := twoPointTangent_le e w₁ w₂ (c := barC) (A₁ := 25 / 2)
    (A₂ := 19 / 2) (rho₁ := 113 / 40) (rho₂ := 213 / 100) (sigma := 24 / 5)
    (d₁ := 15 * barC - 3) (d₂ := 15 * barC + 3) he hseparation barC_pos.le
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hsum : barC ≤ ‖w₁‖ + ‖w₂‖ :=
    hseparation.trans (norm_sub_le w₁ w₂)
  refine htangent.trans ?_
  change bluePointUpper barC ‖w₁‖ ‖w₂‖ ≤ bluePointVertex0 barC
  exact bluePointUpper_le_vertex0 hw₁ hw₂ hsum

private theorem rootEdge_internal_polynomial_lt :
    redPointVertex0 barC + bluePointVertex0 barC +
        95 * barC - 97 * barC ^ 2 - 6 < -5 := by
  rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
  norm_num [redPointVertex0, bluePointVertex0] at hlower hupper ⊢
  nlinarith [sq_nonneg (barC - 13866128436518096 / 10 ^ 16)]

/-- Midpoint convexity splits a cross distance into one term for each color. -/
theorem midpoint_crossDistance_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e p w : E) :
    ‖e - p - w‖ ≤ (‖e - (2 : ℝ) • p‖ + ‖e - (2 : ℝ) • w‖) / 2 := by
  have heq : e - p - w =
      (1 / 2 : ℝ) • ((e - (2 : ℝ) • p) + (e - (2 : ℝ) • w)) := by
    module
  calc
    ‖e - p - w‖ = (1 / 2 : ℝ) *
        ‖(e - (2 : ℝ) • p) + (e - (2 : ℝ) • w)‖ := by
      rw [heq, norm_smul]
      norm_num [Real.norm_eq_abs]
    _ ≤ (1 / 2 : ℝ) *
        (‖e - (2 : ℝ) • p‖ + ‖e - (2 : ℝ) • w‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = _ := by ring

/-- The exact two-point tangent certificate for the root-edge internal separator. -/
theorem rootEdge_internal_expanded_lt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1)
    (hredSeparation : barC ≤ ‖p₁ - p₂‖)
    (hblueSeparation : barC ≤ ‖w₁ - w₂‖) :
    25 * ‖e - p₁ - w₁‖ + 19 * ‖e - p₂ - w₂‖ +
        (3 - 15 * barC) * ‖w₁‖ - (15 * barC + 3) * ‖w₂‖ -
        24 * barC * ‖p₂‖ + 95 * barC - 97 * barC ^ 2 - 6 < 0 := by
  have hmid₁ := midpoint_crossDistance_le e p₁ w₁
  have hmid₂ := midpoint_crossDistance_le e p₂ w₂
  have hred := redPointTangent_le e p₁ p₂ he hp₁ hp₂ hredSeparation
  have hblue := bluePointTangent_le e w₁ w₂ he hw₁ hw₂ hblueSeparation
  nlinarith [rootEdge_internal_polynomial_lt]

/-- Failure slack for the diagonal four-child matching. -/
def matchingFailureSlack (c L M B₁₁ B₂₂ : ℝ) : ℝ :=
  B₁₁ + B₂₂ - (2 * c - 1) * (L + M)

/-- Failure slack for the red coincident endpoint on the first matching edge. -/
def redEndpointFailureSlack (c L M b₁ b₂ B₁₁ : ℝ) : ℝ :=
  L - 1 + B₁₁ + (b₁ + M - b₂) / 2 - c * (L + (b₁ + b₂ + M) / 2)

/-- Internal failure slack for the red root--second-child edge. -/
def redRootEdgeInternalSlack (c M r₂ b₁ b₂ : ℝ) : ℝ :=
  2 * M - c * (r₂ + (b₁ + b₂ + M) / 2)

/-- Failure slack for the blue coincident endpoint on the first matching edge. -/
def blueEndpointFailureSlack (c L M r₁ r₂ B₁₁ : ℝ) : ℝ :=
  M - 1 + B₁₁ + (r₁ + L - r₂) / 2 - c * (M + (r₁ + r₂ + L) / 2)

/-- Internal failure slack for the blue root--second-child edge. -/
def blueRootEdgeInternalSlack (c L b₂ r₁ r₂ : ℝ) : ℝ :=
  2 * L - c * (b₂ + (r₁ + r₂ + L) / 2)

/-- The internal root-edge slack has a strictly negative positive separator. -/
theorem rootEdge_internal_separator_lt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1)
    (hredSeparation : barC ≤ ‖p₁ - p₂‖)
    (hblueSeparation : barC ≤ ‖w₁ - w₂‖) :
    19 * matchingFailureSlack barC ‖p₁ - p₂‖ ‖w₁ - w₂‖
          ‖e - p₁ - w₁‖ ‖e - p₂ - w₂‖ +
        6 * redEndpointFailureSlack barC ‖p₁ - p₂‖ ‖w₁ - w₂‖
          ‖w₁‖ ‖w₂‖ ‖e - p₁ - w₁‖ +
        24 * redRootEdgeInternalSlack barC ‖w₁ - w₂‖ ‖p₂‖ ‖w₁‖ ‖w₂‖ <
      0 := by
  have hexpanded := rootEdge_internal_expanded_lt e p₁ p₂ w₁ w₂ he hp₁ hp₂ hw₁ hw₂
    hredSeparation hblueSeparation
  have hcoefRed : 25 - 44 * barC ≤ 0 := by
    nlinarith [one_lt_barC_and_barC_lt_two.1]
  have hcoefBlue : 70 - 53 * barC ≤ 0 := by
    rcases barC_mem_isolation_box with ⟨hlower, hupper⟩
    norm_num at hlower hupper ⊢
    linarith
  have hredTerm := mul_le_mul_of_nonpos_left hredSeparation hcoefRed
  have hblueTerm := mul_le_mul_of_nonpos_left hblueSeparation hcoefBlue
  simp only [matchingFailureSlack, redEndpointFailureSlack, redRootEdgeInternalSlack]
  nlinarith

/-- A matching and its coincident endpoint exclude the red internal root-edge failure. -/
theorem redRootEdgeInternalSlack_neg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1)
    (hredSeparation : barC ≤ ‖p₁ - p₂‖)
    (hblueSeparation : barC ≤ ‖w₁ - w₂‖)
    (hmatching : 0 ≤ matchingFailureSlack barC ‖p₁ - p₂‖ ‖w₁ - w₂‖
      ‖e - p₁ - w₁‖ ‖e - p₂ - w₂‖)
    (hendpoint : 0 ≤ redEndpointFailureSlack barC ‖p₁ - p₂‖ ‖w₁ - w₂‖
      ‖w₁‖ ‖w₂‖ ‖e - p₁ - w₁‖) :
    redRootEdgeInternalSlack barC ‖w₁ - w₂‖ ‖p₂‖ ‖w₁‖ ‖w₂‖ < 0 := by
  have hseparator := rootEdge_internal_separator_lt e p₁ p₂ w₁ w₂ he hp₁ hp₂ hw₁ hw₂
    hredSeparation hblueSeparation
  nlinarith

/-- The color-transposed internal root-edge slack has the same strict separator. -/
theorem blueRootEdge_internal_separator_lt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1)
    (hredSeparation : barC ≤ ‖p₁ - p₂‖)
    (hblueSeparation : barC ≤ ‖w₁ - w₂‖) :
    19 * matchingFailureSlack barC ‖p₁ - p₂‖ ‖w₁ - w₂‖
          ‖e - p₁ - w₁‖ ‖e - p₂ - w₂‖ +
        6 * blueEndpointFailureSlack barC ‖p₁ - p₂‖ ‖w₁ - w₂‖
          ‖p₁‖ ‖p₂‖ ‖e - p₁ - w₁‖ +
        24 * blueRootEdgeInternalSlack barC ‖p₁ - p₂‖ ‖w₂‖ ‖p₁‖ ‖p₂‖ <
      0 := by
  have hseparator := rootEdge_internal_separator_lt e w₁ w₂ p₁ p₂ he hw₁ hw₂ hp₁ hp₂
    hblueSeparation hredSeparation
  have hcross₁ : e - w₁ - p₁ = e - p₁ - w₁ := by abel
  have hcross₂ : e - w₂ - p₂ = e - p₂ - w₂ := by abel
  rw [hcross₁, hcross₂] at hseparator
  simp only [matchingFailureSlack, redEndpointFailureSlack, redRootEdgeInternalSlack,
    blueEndpointFailureSlack, blueRootEdgeInternalSlack] at hseparator ⊢
  nlinarith

/-- A matching and its coincident endpoint exclude the blue internal root-edge failure. -/
theorem blueRootEdgeInternalSlack_neg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e p₁ p₂ w₁ w₂ : E) (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1)
    (hredSeparation : barC ≤ ‖p₁ - p₂‖)
    (hblueSeparation : barC ≤ ‖w₁ - w₂‖)
    (hmatching : 0 ≤ matchingFailureSlack barC ‖p₁ - p₂‖ ‖w₁ - w₂‖
      ‖e - p₁ - w₁‖ ‖e - p₂ - w₂‖)
    (hendpoint : 0 ≤ blueEndpointFailureSlack barC ‖p₁ - p₂‖ ‖w₁ - w₂‖
      ‖p₁‖ ‖p₂‖ ‖e - p₁ - w₁‖) :
    blueRootEdgeInternalSlack barC ‖p₁ - p₂‖ ‖w₂‖ ‖p₁‖ ‖p₂‖ < 0 := by
  have hseparator :=
    blueRootEdge_internal_separator_lt e p₁ p₂ w₁ w₂ he hp₁ hp₂ hw₁ hw₂
      hredSeparation hblueSeparation
  nlinarith

/-- In an admissible configuration, a diagonal matching and its red coincident endpoint rule out
the red root-edge internal primitive. -/
theorem SixPointConfiguration.redRootEdgeInternalSlack_neg_of_matching_endpoint
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS)
    (hmatching : 0 ≤ matchingFailureSlack barC
      (dist (configuration .red .left) (configuration .red .right))
      (dist (configuration .blue .left) (configuration .blue .right))
      (dist (configuration .red .left) (configuration .blue .left))
      (dist (configuration .red .right) (configuration .blue .right)))
    (hendpoint : 0 ≤ redEndpointFailureSlack barC
      (dist (configuration .red .left) (configuration .red .right))
      (dist (configuration .blue .left) (configuration .blue .right))
      (dist (configuration .blue .root) (configuration .blue .left))
      (dist (configuration .blue .root) (configuration .blue .right))
      (dist (configuration .red .left) (configuration .blue .left))) :
    redRootEdgeInternalSlack barC
      (dist (configuration .blue .left) (configuration .blue .right))
      (dist (configuration .red .root) (configuration .red .right))
      (dist (configuration .blue .root) (configuration .blue .left))
      (dist (configuration .blue .root) (configuration .blue .right)) < 0 := by
  let e := configuration.rootDisplacement
  let p₁ := configuration.redDisplacement .left
  let p₂ := configuration.redDisplacement .right
  let w₁ := configuration.bluePullback .left
  let w₂ := configuration.bluePullback .right
  have hL : ‖p₁ - p₂‖ =
      dist (configuration .red .left) (configuration .red .right) := by
    rw [← dist_eq_norm, configuration.dist_redDisplacement]
  have hM : ‖w₁ - w₂‖ =
      dist (configuration .blue .left) (configuration .blue .right) := by
    rw [← dist_eq_norm, configuration.dist_bluePullback]
  have hr₂ : ‖p₂‖ = dist (configuration .red .root) (configuration .red .right) := by
    simp [p₂, SixPointConfiguration.redDisplacement, dist_eq_norm, norm_sub_rev]
  have hb₁ : ‖w₁‖ = dist (configuration .blue .root) (configuration .blue .left) := by
    simp [w₁, SixPointConfiguration.bluePullback, dist_eq_norm]
  have hb₂ : ‖w₂‖ = dist (configuration .blue .root) (configuration .blue .right) := by
    simp [w₂, SixPointConfiguration.bluePullback, dist_eq_norm]
  have hB₁₁ : ‖e - p₁ - w₁‖ =
      dist (configuration .red .left) (configuration .blue .left) := by
    exact (configuration.dist_red_blue_eq_norm .left .left).symm
  have hB₂₂ : ‖e - p₂ - w₂‖ =
      dist (configuration .red .right) (configuration .blue .right) := by
    exact (configuration.dist_red_blue_eq_norm .right .right).symm
  have hredSeparation : barC ≤ ‖p₁ - p₂‖ := by
    have hsibling := configuration.two_mul_le_dist_redDisplacement h
    rw [barS, show 2 * (barC / 2) = barC by ring, dist_eq_norm] at hsibling
    exact hsibling
  have hblueSeparation : barC ≤ ‖w₁ - w₂‖ := by
    have hsibling := configuration.two_mul_le_dist_bluePullback h
    rw [barS, show 2 * (barC / 2) = barC by ring, dist_eq_norm] at hsibling
    exact hsibling
  have hnegative := redRootEdgeInternalSlack_neg e p₁ p₂ w₁ w₂
    (configuration.norm_rootDisplacement h)
    (configuration.norm_redDisplacement_le_one h (by simp))
    (configuration.norm_redDisplacement_le_one h (by simp))
    (configuration.norm_bluePullback_le_one h (by simp))
    (configuration.norm_bluePullback_le_one h (by simp)) hredSeparation hblueSeparation
    (by simpa only [hL, hM, hB₁₁, hB₂₂] using hmatching)
    (by simpa only [hL, hM, hb₁, hb₂, hB₁₁] using hendpoint)
  simpa only [hM, hr₂, hb₁, hb₂] using hnegative

end LeanPool.Besicovitch
