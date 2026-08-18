/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132ConvexK3.MetricDichotomy
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith

/-!
# Residual one-sided and four-edge bounds

Arithmetic and finite-package kernel for draft Section 6.1--6.3.  The
geometric circle/half-plane arguments supply the package-cardinality
hypotheses; this file proves the exact degree consequences, the surviving
penultimate anti-saturation step, and the two metric regimes of the
conditional four-edge cage.
-/

namespace LeanPool.Erdos132ConvexK3

/-- A fixed pair of radii contributes at most one point in one open
half-plane of the line of distinct centers. -/
theorem same_half_plane_fixed_radii_card_le_one
    {a b : Point ℝ} (hab : a ≠ b) {S : Finset (Point ℝ)} {radiusA radiusB : ℝ}
    (hS : ∀ p ∈ S,
      sqDist a p = radiusA ∧ sqDist b p = radiusB ∧ InLeftOpenHalfPlane a b p) :
    S.card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro p q hp hq
  have hpData := hS p hp
  have hqData := hS q hq
  apply same_half_plane_two_circle_unique hab
  · exact hpData.1.trans hqData.1.symm
  · exact hpData.2.1.trans hqData.2.1.symm
  · exact hpData.2.2
  · exact hqData.2.2

/-- A branch covered by two fixed-radius circle families has at most two
points once each family has the half-plane uniqueness bound. -/
theorem two_circle_families_card_le_two
    {S A B : Finset (Point ℝ)}
    (hcover : S ⊆ A ∪ B) (hA : A.card ≤ 1) (hB : B.card ≤ 1) :
    S.card ≤ 2 := by
  calc
    S.card ≤ (A ∪ B).card := Finset.card_le_card hcover
    _ ≤ A.card + B.card := Finset.card_union_le A B
    _ ≤ 2 := by omega

/-- A branch covered by three fixed-radius circle families has at most three
points. -/
theorem three_circle_families_card_le_three
    {S A B C : Finset (Point ℝ)}
    (hcover : S ⊆ A ∪ B ∪ C)
    (hA : A.card ≤ 1) (hB : B.card ≤ 1) (hC : C.card ≤ 1) :
    S.card ≤ 3 := by
  calc
    S.card ≤ (A ∪ B ∪ C).card := Finset.card_le_card hcover
    _ ≤ (A ∪ B).card + C.card := Finset.card_union_le (A ∪ B) C
    _ ≤ (A.card + B.card) + C.card :=
      Nat.add_le_add_right (Finset.card_union_le A B) C.card
    _ ≤ 3 := by omega

/-- Draft (6.3): two circle slots on either boundary arc, plus the shared
tip, give degree at most five when the tip is a `d₂` partner. -/
theorem one_sided_shared_tip_d2_degree_bound
    {degree leftArc rightArc : ℕ}
    (hdegree : degree ≤ leftArc + rightArc + 1)
    (hleft : leftArc ≤ 2) (hright : rightArc ≤ 2) :
    degree ≤ 5 := by
  omega

/-- Draft (6.4): three circle slots on either boundary arc, plus the shared
tip, give degree at most seven when the tip is a diameter partner. -/
theorem one_sided_shared_tip_d1_degree_bound
    {degree leftArc rightArc : ℕ}
    (hdegree : degree ≤ leftArc + rightArc + 1)
    (hleft : leftArc ≤ 3) (hright : rightArc ≤ 3) :
    degree ≤ 7 := by
  omega

/-- Unique farthest immediately gives the low-tip branch of Section 6.1. -/
theorem one_sided_shared_tip_low_degree_bound
    {degree : ℕ} (hdegree : degree ≤ 1) : degree ≤ 1 := hdegree

/-- Attempt 12, Section 1.  ED across the surviving `d₂` rung contradicts
the top-two gap and strict unique-farthest inequality if `Vs=d₁`. -/
theorem one_penultimate_anti_saturation
    {d₁ d₂ Vs Vp : ℝ}
    (hVpClasses : Vp ≤ d₁ ∧ (Vp < d₁ → Vp ≤ d₂))
    (hUniqueFarthest : Vp < Vs)
    (hED : Vs + d₂ < Vp + d₁) :
    Vs ≠ d₁ := by
  intro hVs
  have hVpLt : Vp < d₁ := by linarith
  have hVpLe : Vp ≤ d₂ := hVpClasses.2 hVpLt
  linarith

/-- Combining the anti-saturation exclusion with the one-sided `d₂` and
low-tip bounds gives the four saturation words degree at most five. -/
theorem one_penultimate_shared_tip_degree_le_five
    {degree : ℕ} {Vs d₁ d₂ d₃ : ℝ}
    (hSplit : Vs = d₁ ∨ Vs = d₂ ∨ Vs ≤ d₃)
    (hNotD₁ : Vs ≠ d₁)
    (hD₂ : Vs = d₂ → degree ≤ 5)
    (hLow : Vs ≤ d₃ → degree ≤ 1) :
    degree ≤ 5 := by
  rcases hSplit with hD₁ | hD₂eq | hLowEq
  · exact (hNotD₁ hD₁).elim
  · exact hD₂ hD₂eq
  · exact (hLow hLowEq).trans (by omega)

/-- The four possible distance bands for either central cage endpoint. -/
inductive CageDistanceBand where
  | d1
  | d2
  | d3
  | below
  deriving DecidableEq

instance : Fintype CageDistanceBand where
  elems := {.d1, .d2, .d3, .below}
  complete := by
    intro band
    cases band <;> simp

/-- General row of draft package table (6.5). -/
def fourEdgeGeneralPackage : CageDistanceBand → ℕ
  | .d1 => 4
  | .d2 => 3
  | .d3 => 1
  | .below => 0

/-- Long-metric row of draft package table (6.5). -/
def fourEdgeLongPackage : CageDistanceBand → ℕ
  | .d1 => 4
  | .d2 => 2
  | .d3 => 1
  | .below => 0

/-- Kernel rendering of both rows of the exact package table (6.5). -/
theorem four_edge_cage_package_table :
    fourEdgeGeneralPackage .d1 = 4 ∧
    fourEdgeGeneralPackage .d2 = 3 ∧
    fourEdgeGeneralPackage .d3 = 1 ∧
    fourEdgeGeneralPackage .below = 0 ∧
    fourEdgeLongPackage .d1 = 4 ∧
    fourEdgeLongPackage .d2 = 2 ∧
    fourEdgeLongPackage .d3 = 1 ∧
    fourEdgeLongPackage .below = 0 := by
  decide

/-- Draft (6.6): in the long metric regime, degree at least seven forces
both central endpoint distances into the diameter band. -/
theorem four_edge_cage_long_high_degree_forces_d1d1
    {degree : ℕ} {left right : CageDistanceBand}
    (hdegree : 7 ≤ degree)
    (hpackage : degree ≤ fourEdgeLongPackage left + fourEdgeLongPackage right) :
    left = .d1 ∧ right = .d1 := by
  cases left <;> cases right <;>
    simp [fourEdgeLongPackage] at hpackage ⊢ <;> omega

/-- Draft (6.7): in the short metric regime, degree at least seven forces
exactly one of the three displayed central states. -/
theorem four_edge_cage_short_high_degree_forces_three_states
    {degree : ℕ} {left right : CageDistanceBand}
    (hdegree : 7 ≤ degree)
    (hpackage : degree ≤
      fourEdgeGeneralPackage left + fourEdgeGeneralPackage right) :
    (left = .d1 ∧ right = .d2) ∨
      (left = .d2 ∧ right = .d1) ∨
      (left = .d1 ∧ right = .d1) := by
  cases left <;> cases right <;>
    simp [fourEdgeGeneralPackage] at hpackage ⊢ <;> omega

/-- Long-regime half-plane uniqueness turns (6.6) into (6.8). -/
theorem four_edge_cage_long_min_degree_le_six
    {degreeP degreeQ : ℕ}
    {leftP rightP leftQ rightQ : CageDistanceBand}
    (hpackageP : degreeP ≤
      fourEdgeLongPackage leftP + fourEdgeLongPackage rightP)
    (hpackageQ : degreeQ ≤
      fourEdgeLongPackage leftQ + fourEdgeLongPackage rightQ)
    (hUniqueD1D1 : ¬(leftP = .d1 ∧ rightP = .d1 ∧
      leftQ = .d1 ∧ rightQ = .d1)) :
    min degreeP degreeQ ≤ 6 := by
  by_contra hnot
  have hmin : 7 ≤ min degreeP degreeQ := by omega
  have hP : 7 ≤ degreeP := hmin.trans (Nat.min_le_left _ _)
  have hQ : 7 ≤ degreeQ := hmin.trans (Nat.min_le_right _ _)
  obtain ⟨hleftP, hrightP⟩ :=
    four_edge_cage_long_high_degree_forces_d1d1 hP hpackageP
  obtain ⟨hleftQ, hrightQ⟩ :=
    four_edge_cage_long_high_degree_forces_d1d1 hQ hpackageQ
  exact hUniqueD1D1 ⟨hleftP, hrightP, hleftQ, hrightQ⟩

/-- Short-regime occupied-circle exclusions and uniqueness turn (6.7) into
the conditional cage conclusion (6.8). -/
theorem four_edge_cage_short_min_degree_le_six
    {degreeP degreeQ : ℕ}
    {leftP rightP leftQ rightQ : CageDistanceBand}
    (hpackageP : degreeP ≤
      fourEdgeGeneralPackage leftP + fourEdgeGeneralPackage rightP)
    (hpackageQ : degreeQ ≤
      fourEdgeGeneralPackage leftQ + fourEdgeGeneralPackage rightQ)
    (hP12 : ¬(leftP = .d1 ∧ rightP = .d2))
    (hP21 : ¬(leftP = .d2 ∧ rightP = .d1))
    (hQ12 : ¬(leftQ = .d1 ∧ rightQ = .d2))
    (hQ21 : ¬(leftQ = .d2 ∧ rightQ = .d1))
    (hUniqueD1D1 : ¬(leftP = .d1 ∧ rightP = .d1 ∧
      leftQ = .d1 ∧ rightQ = .d1)) :
    min degreeP degreeQ ≤ 6 := by
  by_contra hnot
  have hmin : 7 ≤ min degreeP degreeQ := by omega
  have hP : 7 ≤ degreeP := hmin.trans (Nat.min_le_left _ _)
  have hQ : 7 ≤ degreeQ := hmin.trans (Nat.min_le_right _ _)
  have hstateP := four_edge_cage_short_high_degree_forces_three_states hP hpackageP
  have hstateQ := four_edge_cage_short_high_degree_forces_three_states hQ hpackageQ
  rcases hstateP with hstateP | hstateP | hstateP
  · exact (hP12 hstateP).elim
  · exact (hP21 hstateP).elim
  · rcases hstateQ with hstateQ | hstateQ | hstateQ
    · exact (hQ12 hstateQ).elim
    · exact (hQ21 hstateQ).elim
    · exact hUniqueD1D1 ⟨hstateP.1, hstateP.2, hstateQ.1, hstateQ.2⟩

end LeanPool.Erdos132ConvexK3
