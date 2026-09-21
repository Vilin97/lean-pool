/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Isometry

/-!
# A counterexample to Scottish Book Problem 155: formalization

This file formalizes the elementary metric core of `paper1`: the bent seed,
its fixed short-scale property, its explicit contraction, and the passage from
the fixed scale `1 / 2` to the closed-ball radius `1 / 4` used in the main
theorem.  The protected one-point extension and the transfinite construction
are not asserted here.
-/

namespace ScottishBook155

/-- The `ℓ₁` distance on the real plane. -/
def l1Dist (x y : ℝ × ℝ) : ℝ := |x.1 - y.1| + |x.2 - y.2|

/-- The bent line used as the seed of the construction in `paper1`. -/
noncomputable def bentMap (t : ℝ) : ℝ × ℝ :=
  if t ≤ 0 then (t, 0)
  else if t ≤ 1 then (0, t)
  else (1 - t, 1)

/-- Preservation of all distances up to a fixed scale. -/
def PreservesUpTo {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (r : ℝ) (f : X → Y) : Prop :=
  ∀ ⦃x y : X⦄, dist x y ≤ r → dist (f x) (f y) = dist x y

/-- Pairwise distance preservation on every closed ball of radius `r`. -/
def PreservesOnClosedBalls {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (r : ℝ) (f : X → Y) : Prop :=
  ∀ x p q, p ∈ Metric.closedBall x r → q ∈ Metric.closedBall x r →
    dist (f p) (f q) = dist p q

/-- The exact metric conclusion required of a counterexample to Problem 155,
at a specified uniform closed-ball radius. -/
def IsCounterexampleAt {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (r : ℝ) (f : X → Y) : Prop :=
  Function.Bijective f ∧ PreservesOnClosedBalls r f ∧ ¬ Isometry f

/-- A fixed scale of `2r` implies preservation on every closed ball of radius
`r`.  This is the last metric deduction in the proof of the main theorem. -/
theorem preservesOnClosedBalls_of_preservesUpTo_two_mul
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {r : ℝ} {f : X → Y} (h : PreservesUpTo (2 * r) f) :
    PreservesOnClosedBalls r f := by
  intro x p q hp hq
  apply h
  rw [show (2 : ℝ) * r = r + r by ring]
  exact (dist_triangle p x q).trans (add_le_add hp (by simpa [dist_comm] using hq))

/-- The final logical step of the paper's main proof: a bijection preserving
distances up to `1 / 2`, but contracting one pair, is a Problem 155
counterexample on every closed ball of radius `1 / 4`.  This theorem is
conditional; it does not construct the required spaces or map. -/
theorem isCounterexampleAt_one_quarter_of_short_scale
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} (hbij : Function.Bijective f)
    (hshort : PreservesUpTo ((1 : ℝ) / 2) f)
    {p q : X} (hcontracts : dist (f p) (f q) ≠ dist p q) :
    IsCounterexampleAt ((1 : ℝ) / 4) f := by
  refine ⟨hbij, ?_, ?_⟩
  · apply preservesOnClosedBalls_of_preservesUpTo_two_mul
    norm_num
    exact hshort
  · intro hisometry
    exact hcontracts (hisometry.dist_eq p q)

/-- The bent seed contracts the pair `(-1, 2)` from distance three to
distance one. -/
theorem bentMap_contraction :
    l1Dist (bentMap (-1)) (bentMap 2) = 1 ∧ |(-1 : ℝ) - 2| = 3 := by
  norm_num [bentMap, l1Dist]

/-- The bent seed is injective. -/
theorem bentMap_injective : Function.Injective bentMap := by
  intro s t h
  simp only [bentMap] at h
  split_ifs at h with hs0 hs1 ht0 ht1 <;> simp_all <;> linarith

/-- The bent seed preserves the `ℓ₁` distance whenever the parameter distance
is at most `1 / 2`. -/
theorem bentMap_short (s t : ℝ) (h : |s - t| ≤ (1 : ℝ) / 2) :
    l1Dist (bentMap s) (bentMap t) = |s - t| := by
  suffices ordered : ∀ s t : ℝ, s ≤ t → |s - t| ≤ (1 : ℝ) / 2 →
      l1Dist (bentMap s) (bentMap t) = |s - t| by
    rcases le_total s t with hst | hts
    · exact ordered s t hst h
    · rw [show l1Dist (bentMap s) (bentMap t) =
          l1Dist (bentMap t) (bentMap s) by simp [l1Dist, abs_sub_comm]]
      simpa [abs_sub_comm] using ordered t s hts (by simpa [abs_sub_comm] using h)
  intro a b hab hshort
  rw [abs_of_nonpos (sub_nonpos.mpr hab)] at hshort ⊢
  simp only [bentMap, l1Dist]
  split_ifs with ha0 ha1 hb0 hb1 <;>
    simp only [sub_zero, zero_sub] at *
  · rw [abs_of_nonpos (by linarith), abs_zero]
    linarith
  · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · exfalso
    linarith
  · exfalso
    linarith
  · rw [abs_zero, abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · exfalso
    linarith
  · exfalso
    linarith
  · norm_num
    linarith

end ScottishBook155
