/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132ConvexK3.GlobalAssembly
import LeanPool.Erdos132ConvexK3.WordClosures
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Geometric closure of the thirteen global cover words

This file transports the actual maximal-gap frames produced by
`GlobalAssembly` into the four raw local-geometry records proved in
`WordClosures`.  All cyclic arcs are explicit finsets of offsets.  The two
reflected row-4 routes use the orientation-reversing isometry
`reflectAcrossXAxis`; squared distances and degrees are transported back to
the original labelling.
-/

namespace LeanPool.Erdos132ConvexK3

/-- Reflection in the horizontal axis.  This preserves squared distances and
reverses signed orientation. -/
def reflectAcrossXAxis (p : Point ℝ) : Point ℝ := (p.1, -p.2)

@[simp] theorem reflectAcrossXAxis_sqDist (p q : Point ℝ) :
    sqDist (reflectAcrossXAxis p) (reflectAcrossXAxis q) = sqDist p q := by
  simp [reflectAcrossXAxis, sqDist]
  ring

@[simp] theorem reflectAcrossXAxis_turn (p q r : Point ℝ) :
    turn (reflectAcrossXAxis p) (reflectAcrossXAxis q)
      (reflectAcrossXAxis r) = -turn p q r := by
  simp [reflectAcrossXAxis, turn]
  ring

theorem reflectAcrossXAxis_injective : Function.Injective reflectAcrossXAxis := by
  rintro ⟨px, py⟩ ⟨qx, qy⟩ hpq
  simp only [reflectAcrossXAxis, Prod.mk.injEq, neg_inj] at hpq
  exact Prod.ext hpq.1 hpq.2

theorem reflectAcrossXAxis_strictConvexQuad_reverse
    {a b c d : Point ℝ} (h : StrictConvexQuad a b c d) :
    StrictConvexQuad (reflectAcrossXAxis a) (reflectAcrossXAxis d)
      (reflectAcrossXAxis c) (reflectAcrossXAxis b) := by
  rcases h with ⟨habc, habd, hbcd, hcda⟩
  simp only [StrictConvexQuad, reflectAcrossXAxis_turn]
  constructor
  · have hacd : 0 < turn a c d := by
      rwa [turn_cyclic a c d]
    rw [turn_swap a c d]
    linarith
  constructor
  · rw [turn_swap a b d]
    linarith
  constructor
  · have hdbc : 0 < turn d b c := by
      rwa [turn_cyclic d b c]
    rw [turn_swap d b c]
    linarith
  · have hcab : 0 < turn c a b := by
      rwa [turn_cyclic c a b]
    rw [turn_swap c a b]
    linarith

theorem reflectAcrossXAxis_halfPlane_reverse
    (a b p : Point ℝ) :
    InLeftOpenHalfPlane (reflectAcrossXAxis a) (reflectAcrossXAxis b)
        (reflectAcrossXAxis p) ↔
      InLeftOpenHalfPlane b a p := by
  simp only [InLeftOpenHalfPlane, reflectAcrossXAxis_turn]
  have h : turn b a p = -turn a b p := by
    simp [turn]
    ring
  rw [h]

theorem reflectAcrossXAxis_vertexDegree
    {n : ℕ} (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) (v : Fin n) :
    vertexDegree (fun i ↦ reflectAcrossXAxis (P i)) d₁ d₂ d₃ v =
      vertexDegree P d₁ d₂ d₃ v := by
  unfold vertexDegree
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
  simp only [reflectAcrossXAxis_sqDist]

theorem reflectAcrossXAxis_top_three_classes
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (h : HasTopThreeDistanceClasses P d₁ d₂ d₃) :
    HasTopThreeDistanceClasses
      (fun i ↦ reflectAcrossXAxis (P i)) d₁ d₂ d₃ := by
  simpa only [HasTopThreeDistanceClasses, reflectAcrossXAxis_sqDist] using h

private def chordDot (e t p : Point ℝ) : ℝ :=
  (t.1 - e.1) * (p.1 - e.1) + (t.2 - e.2) * (p.2 - e.2)

private theorem chordDot_shared_tip
    {e t s : Point ℝ} {d : ℝ}
    (hes : sqDist e s = d) (hts : sqDist t s = d) :
    2 * chordDot e t s = sqDist e t := by
  simp only [chordDot, sqDist] at *
  nlinarith

private theorem chordDot_penultimate
    {e t w : Point ℝ} {d₁ d₂ : ℝ}
    (hew : sqDist e w = d₁) (htw : sqDist t w = d₂) :
    d₁ - d₂ = 2 * chordDot e t w - sqDist e t := by
  simp only [chordDot, sqDist] at *
  nlinarith

private theorem chordDot_turn_identity (e t p : Point ℝ) :
    chordDot e t p ^ 2 + turn e t p ^ 2 =
      sqDist e t * sqDist e p := by
  simp only [chordDot, turn, sqDist]
  ring

/-- On one side of an oriented center line, the point on the first-center
circle which is strictly closer to the second center has strictly smaller
signed height than the common-radius tip. -/
theorem penultimate_turn_lt_shared_tip
    {e t w s : Point ℝ} {d₁ d₂ : ℝ}
    (het : e ≠ t) (hd₂d₁ : d₂ < d₁)
    (hes : sqDist e s = d₁) (hts : sqDist t s = d₁)
    (hew : sqDist e w = d₁) (htw : sqDist t w = d₂)
    (hw : 0 < turn e t w) (hs : 0 < turn e t s) :
    turn e t w < turn e t s := by
  have hetPos : 0 < sqDist e t := sqDist_pos_of_ne het
  have hdotS := chordDot_shared_tip hes hts
  have hdotW := chordDot_penultimate hew htw
  have hdotSPos : 0 < chordDot e t s := by linarith
  have hdotSLtW : chordDot e t s < chordDot e t w := by linarith
  have hdotSq : chordDot e t s ^ 2 < chordDot e t w ^ 2 := by
    nlinarith [sq_nonneg (chordDot e t w - chordDot e t s)]
  have hlagrangeS := chordDot_turn_identity e t s
  have hlagrangeW := chordDot_turn_identity e t w
  have hturnSq : turn e t w ^ 2 < turn e t s ^ 2 := by
    rw [hes] at hlagrangeS
    rw [hew] at hlagrangeW
    nlinarith
  nlinarith [sq_nonneg (turn e t s - turn e t w)]

private theorem euclideanDist_eq_sqrt_of_sqDist_eq_global
    {a b : Point ℝ} {d : ℝ} (h : sqDist a b = d) :
  euclideanDist a b = Real.sqrt d := by
  rw [← h]
  rw [← euclideanDist_sq]
  exact (Real.sqrt_sq dist_nonneg).symm

private theorem euclideanDist_le_sqrt_of_sqDist_le_global
    {a b : Point ℝ} {d : ℝ} (h : sqDist a b ≤ d) :
    euclideanDist a b ≤ Real.sqrt d := by
  have hsqrt : euclideanDist a b = Real.sqrt (sqDist a b) := by
    rw [← euclideanDist_sq]
    exact (Real.sqrt_sq dist_nonneg).symm
  rw [hsqrt]
  exact Real.sqrt_le_sqrt h

private theorem sqDist_eq_of_euclideanDist_eq_sqrt_global
    {a b : Point ℝ} {d : ℝ} (hd : 0 ≤ d)
    (h : euclideanDist a b = Real.sqrt d) : sqDist a b = d := by
  have hsqrt := Real.sq_sqrt hd
  have hdist := euclideanDist_sq a b
  rw [h] at hdist
  nlinarith

/-- Squared-distance form of red-blue forcing, with the two diagonal class
splits discharged from the global top-three hypothesis. -/
theorem red_blue_forcing_sqDist
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {a b c d : Fin n} (hac : a ≠ c) (hbd : b ≠ d)
    (hquad : StrictConvexQuad (P a) (P b) (P c) (P d))
    (hab : sqDist (P a) (P b) = d₁)
    (hcd : sqDist (P c) (P d) = d₂) :
    sqDist (P a) (P c) = d₁ ∧ sqDist (P b) (P d) = d₁ := by
  have hACBounds := top_three_class_bounds_of_ne hClasses hac
  have hBDBounds := top_three_class_bounds_of_ne hClasses hbd
  have hAC : euclideanDist (P a) (P c) ≤ Real.sqrt d₂ ∨
      euclideanDist (P a) (P c) = Real.sqrt d₁ := by
    rcases top_three_value_split hACBounds with
      h₁ | h₂ | hlow
    · exact Or.inr (euclideanDist_eq_sqrt_of_sqDist_eq_global h₁)
    · exact Or.inl (euclideanDist_le_sqrt_of_sqDist_le_global h₂.le)
    · exact Or.inl (euclideanDist_le_sqrt_of_sqDist_le_global
        (hlow.trans hClasses.1.le))
  have hBD : euclideanDist (P b) (P d) ≤ Real.sqrt d₂ ∨
      euclideanDist (P b) (P d) = Real.sqrt d₁ := by
    rcases top_three_value_split hBDBounds with
      h₁ | h₂ | hlow
    · exact Or.inr (euclideanDist_eq_sqrt_of_sqDist_eq_global h₁)
    · exact Or.inl (euclideanDist_le_sqrt_of_sqDist_le_global h₂.le)
    · exact Or.inl (euclideanDist_le_sqrt_of_sqDist_le_global
        (hlow.trans hClasses.1.le))
  have hforce := red_blue_forcing hquad
    (Real.sqrt_lt_sqrt (by
      rw [← hcd]
      exact sqDist_nonneg _ _) hClasses.2.1)
    (euclideanDist_eq_sqrt_of_sqDist_eq_global hab)
    (euclideanDist_eq_sqrt_of_sqDist_eq_global hcd) hAC hBD
  have hd₁ : 0 ≤ d₁ := by
    rw [← hab]
    exact sqDist_nonneg _ _
  exact ⟨sqDist_eq_of_euclideanDist_eq_sqrt_global hd₁ hforce.1,
    sqDist_eq_of_euclideanDist_eq_sqrt_global hd₁ hforce.2⟩

/-- Counterclockwise offset of a label from a chosen base. -/
def cyclicOffset
    {n : ℕ} (base j : Fin n) : ℕ := (j - base).val

@[simp] theorem cyclicAdvance_cyclicOffset
    {n : ℕ} [NeZero n] (base j : Fin n) :
    cyclicAdvance base (cyclicOffset base j) = j := by
  unfold cyclicOffset cyclicAdvance
  rw [fin_ofNat_val]
  abel

@[simp] theorem cyclicOffset_self
    {n : ℕ} [NeZero n] (base : Fin n) : cyclicOffset base base = 0 := by
  simp [cyclicOffset]

theorem cyclicOffset_cyclicAdvance
    {n : ℕ} [NeZero n] (base : Fin n) {k : ℕ} (hk : k < n) :
    cyclicOffset base (cyclicAdvance base k) = k := by
  unfold cyclicOffset cyclicAdvance
  have hcast : Fin.ofNat n k = ⟨k, hk⟩ := by
    apply Fin.ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt hk]
  rw [hcast]
  simp

theorem eq_cyclicAdvance_of_cyclicOffset_eq
    {n : ℕ} [NeZero n] {base j : Fin n} {k : ℕ}
    (h : cyclicOffset base j = k) :
    j = cyclicAdvance base k := by
  rw [← cyclicAdvance_cyclicOffset base j, h]

/-- Labels whose offsets lie strictly between two unwrapped positions. -/
noncomputable def cyclicOpenInterval
    {n : ℕ} (base : Fin n) (lo hi : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j ↦
    lo < cyclicOffset base j ∧ cyclicOffset base j < hi

/-- Labels in the open interval that wraps after `hi` and before `lo`. -/
noncomputable def cyclicWrapInterval
    {n : ℕ} (base : Fin n) (hi lo : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j ↦
    hi < cyclicOffset base j ∨ cyclicOffset base j < lo

@[simp] theorem mem_cyclicOpenInterval
    {n : ℕ} {base j : Fin n} {lo hi : ℕ} :
    j ∈ cyclicOpenInterval base lo hi ↔
      lo < cyclicOffset base j ∧ cyclicOffset base j < hi := by
  simp [cyclicOpenInterval]

@[simp] theorem mem_cyclicWrapInterval
    {n : ℕ} {base j : Fin n} {hi lo : ℕ} :
    j ∈ cyclicWrapInterval base hi lo ↔
      hi < cyclicOffset base j ∨ cyclicOffset base j < lo := by
  simp [cyclicWrapInterval]

/-- Four increasing unwrapped offsets in a single turn form a strict
quadrilateral, even when the last offsets use representatives past `n`. -/
theorem cyclic_strict_convex_quad_unwrapped
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ}
    (hConvex : CyclicStrictConvex P) (base : Fin n)
    {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hwindow : d < a + n) :
    StrictConvexQuad
      (P (cyclicAdvance base a)) (P (cyclicAdvance base b))
      (P (cyclicAdvance base c)) (P (cyclicAdvance base d)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact cyclic_strict_convex_turn_unwrapped hConvex base hab hbc (by omega)
  · exact cyclic_strict_convex_turn_unwrapped hConvex base hab
      (hbc.trans hcd) hwindow
  · exact cyclic_strict_convex_turn_unwrapped hConvex base hbc hcd (by omega)
  · have h := cyclic_strict_convex_turn_unwrapped hConvex base
      (a := c) (b := d) (c := a + n) hcd hwindow (by omega)
    rw [cyclicAdvance_period] at h
    exact h

/-- A point after an oriented chord in one unwrapped turn lies in its left
open half-plane. -/
theorem cyclic_inLeft_of_unwrapped_order
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ}
    (hConvex : CyclicStrictConvex P) (base : Fin n)
    {a b k : ℕ} (hab : a < b) (hbk : b < k) (hwindow : k < a + n) :
    InLeftOpenHalfPlane
      (P (cyclicAdvance base a)) (P (cyclicAdvance base b))
      (P (cyclicAdvance base k)) := by
  exact cyclic_strict_convex_turn_unwrapped hConvex base hab hbk hwindow

/-- The reversed chord sees the points on its short intervening arc in its
left open half-plane. -/
theorem cyclic_inLeft_reverse_of_between
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ}
    (hConvex : CyclicStrictConvex P) (base : Fin n)
    {a k b : ℕ} (hak : a < k) (hkb : k < b) (hbn : b < n) :
    InLeftOpenHalfPlane
      (P (cyclicAdvance base b)) (P (cyclicAdvance base a))
      (P (cyclicAdvance base k)) := by
  have h := cyclic_inLeft_of_unwrapped_order hConvex base
    (a := b) (b := a + n) (k := k + n) (by omega) (by omega) (by omega)
  rw [cyclicAdvance_period, cyclicAdvance_period] at h
  exact h

private theorem cyclicOpenInterval_ne_right
    {n : ℕ} [NeZero n] (base : Fin n) {a b : ℕ}
    (hbn : b < n) :
    ∀ j ∈ cyclicOpenInterval base a b, j ≠ cyclicAdvance base b := by
  intro j hj hEq
  subst j
  have hk := mem_cyclicOpenInterval.mp hj
  rw [cyclicOffset_cyclicAdvance base hbn] at hk
  omega

private theorem cyclicWrapInterval_ne_left
    {n : ℕ} [NeZero n] (base : Fin n) {a b : ℕ}
    (hba : b < a) (han : a < n) :
    ∀ j ∈ cyclicWrapInterval base a b, j ≠ cyclicAdvance base a := by
  intro j hj hEq
  subst j
  have hk := mem_cyclicWrapInterval.mp hj
  rw [cyclicOffset_cyclicAdvance base han] at hk
  omega

private theorem cyclicOpenInterval_center_ne_of_left
    {n : ℕ} [NeZero n] (base : Fin n) {e a b : ℕ}
    (he_a : e < a) (hbn : b < n) :
    ∀ j ∈ cyclicOpenInterval base a b, cyclicAdvance base e ≠ j := by
  intro j hj hEq
  subst j
  have hk := mem_cyclicOpenInterval.mp hj
  rw [cyclicOffset_cyclicAdvance base (by omega : e < n)] at hk
  omega

private theorem cyclicWrapInterval_center_ne_of_between
    {n : ℕ} [NeZero n] (base : Fin n) {a t b : ℕ}
    (ha_t : a < t) (ht_b : t < b) (hbn : b < n) :
    ∀ j ∈ cyclicWrapInterval base b a, cyclicAdvance base t ≠ j := by
  intro j hj hEq
  subst j
  have hk := mem_cyclicWrapInterval.mp hj
  rw [cyclicOffset_cyclicAdvance base (by omega : t < n)] at hk
  omega

/-- A six-label cyclic pattern with the displayed two-rung distances is the
raw shared-tip realization consumed by the full-two-rung kernel. -/
theorem fullTwoRungGeometry_of_cyclic_offsets
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hConvex : CyclicStrictConvex P)
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    (base : Fin n) {e v t w s r : ℕ}
    (he_v : e < v) (hv_t : v < t) (ht_w : t < w)
    (hw_s : w < s) (hs_r : s < r) (hr_n : r < n)
    (hes : sqDist (P (cyclicAdvance base e))
      (P (cyclicAdvance base s)) = d₁)
    (hts : sqDist (P (cyclicAdvance base t))
      (P (cyclicAdvance base s)) = d₁)
    (hew : sqDist (P (cyclicAdvance base e))
      (P (cyclicAdvance base w)) = d₁)
    (htw : sqDist (P (cyclicAdvance base t))
      (P (cyclicAdvance base w)) = d₂)
    (her : sqDist (P (cyclicAdvance base e))
      (P (cyclicAdvance base r)) = d₂)
    (htr : sqDist (P (cyclicAdvance base t))
      (P (cyclicAdvance base r)) = d₁) :
    Nonempty (FullTwoRungGeometry P d₁ d₂ d₃) := by
  classical
  let E := cyclicAdvance base e
  let V := cyclicAdvance base v
  let T := cyclicAdvance base t
  let W := cyclicAdvance base w
  let S := cyclicAdvance base s
  let R := cyclicAdvance base r
  let positiveArc := cyclicOpenInterval base v s
  let negativeArc := cyclicWrapInterval base s v
  have hInjective : Function.Injective P :=
    cyclic_strict_convex_injective hConvex (by omega)
  have hET : E ≠ T := by
    simpa [E, T] using cyclicAdvance_ne_of_lt base
      (a := e) (b := t) (by omega) (by omega) (by omega)
  have hTip : 0 < turn (P E) (P T) (P S) := by
    simpa [E, T, S] using cyclic_strict_convex_turn_unwrapped hConvex base
      (a := e) (b := t) (c := s) (by omega) (by omega) (by omega)
  have hVertex : turn (P E) (P T) (P V) < 0 := by
    have h := cyclic_strict_convex_turn_unwrapped hConvex base
      (a := e) (b := v) (c := t) (by omega) (by omega) (by omega)
    rw [turn_swap] at h
    simpa [E, T, V] using h
  have hWAbove : 0 < turn (P E) (P T) (P W) := by
    simpa [E, T, W] using cyclic_strict_convex_turn_unwrapped hConvex base
      (a := e) (b := t) (c := w) (by omega) (by omega) (by omega)
  have hRAbove : 0 < turn (P E) (P T) (P R) := by
    simpa [E, T, R] using cyclic_strict_convex_turn_unwrapped hConvex base
      (a := e) (b := t) (c := r) (by omega) (by omega) (by omega)
  have hPartition : ∀ j, j ≠ V →
      j ∈ positiveArc ∨ j ∈ (∅ : Finset (Fin n)) ∨
        j ∈ (∅ : Finset (Fin n)) ∨ j ∈ negativeArc ∨ j = S ∨ j = S := by
    intro j hjV
    let k := cyclicOffset base j
    have hk : k < n := by
      dsimp [k, cyclicOffset]
      exact (j - base).isLt
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    have hkV : k ≠ v := by
      intro hkv
      apply hjV
      rw [hjEq, hkv]
    by_cases hkS : k = s
    · right; right; right; right; left
      rw [hjEq, hkS]
    by_cases hkMiddle : v < k ∧ k < s
    · left
      exact mem_cyclicOpenInterval.mpr hkMiddle
    · right; right; right; left
      exact mem_cyclicWrapInterval.mpr (by omega)
  have hPositiveHalfPlane : ∀ j ∈ positiveArc,
      InLeftOpenHalfPlane (P E) (P V) (P j) := by
    intro j hj
    have hkData := mem_cyclicOpenInterval.mp hj
    let k := cyclicOffset base j
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    rw [hjEq]
    simpa [E, V] using cyclic_inLeft_of_unwrapped_order hConvex base
      (a := e) (b := v) (k := k) (by omega) (by omega) (by omega)
  have hNegativeHalfPlane : ∀ j ∈ negativeArc,
      InLeftOpenHalfPlane (P V) (P T) (P j) := by
    intro j hj
    have hkCases := mem_cyclicWrapInterval.mp hj
    let k := cyclicOffset base j
    have hk : k < n := by
      dsimp [k, cyclicOffset]
      exact (j - base).isLt
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    rw [hjEq]
    rcases hkCases with hkHigh | hkLow
    · exact cyclic_inLeft_of_unwrapped_order hConvex base
        (a := v) (b := t) (k := k) (by omega) (by omega) (by omega)
    · have h := cyclic_inLeft_of_unwrapped_order hConvex base
        (a := v) (b := t) (k := k + n) (by omega) (by omega) (by omega)
      rw [cyclicAdvance_period] at h
      exact h
  have hPositiveQuad : ∀ j ∈ positiveArc,
      StrictConvexQuad (P V) (P j) (P S) (P E) := by
    intro j hj
    have hkData := mem_cyclicOpenInterval.mp hj
    let k := cyclicOffset base j
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    have h := cyclic_strict_convex_quad_unwrapped hConvex base
      (a := v) (b := k) (c := s) (d := e + n)
      (by omega) (by omega) (by omega) (by omega)
    rw [cyclicAdvance_period] at h
    simpa [V, S, E, hjEq] using h
  have hNegativeQuad : ∀ j ∈ negativeArc,
      StrictConvexQuad (P T) (P S) (P j) (P V) := by
    intro j hj
    have hkCases := mem_cyclicWrapInterval.mp hj
    let k := cyclicOffset base j
    have hk : k < n := by
      dsimp [k, cyclicOffset]
      exact (j - base).isLt
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    rcases hkCases with hkHigh | hkLow
    · change s < k at hkHigh
      have h := cyclic_strict_convex_quad_unwrapped hConvex base
        (a := t) (b := s) (c := k) (d := v + n)
        (by omega) (by omega) (by omega) (by omega)
      rw [cyclicAdvance_period] at h
      simpa [T, S, V, hjEq] using h
    · change k < v at hkLow
      have h := cyclic_strict_convex_quad_unwrapped hConvex base
        (a := t) (b := s) (c := k + n) (d := v + n)
        (by omega) (by omega) (by omega) (by omega)
      rw [cyclicAdvance_period, cyclicAdvance_period] at h
      simpa [T, S, V, hjEq] using h
  have hAnti : StrictConvexQuad (P T) (P W) (P S) (P V) := by
    have h := cyclic_strict_convex_quad_unwrapped hConvex base
      (a := t) (b := w) (c := s) (d := v + n)
      (by omega) (by omega) (by omega) (by omega)
    rw [cyclicAdvance_period] at h
    simpa [T, W, S, V] using h
  refine ⟨{
    pointsInjective := hInjective
    classes := hClasses
    e := E
    t := T
    s := S
    w := W
    r := R
    vertex := V
    endpoint := S
    e_ne_t := hET
    e_ne_s := by
      simpa [E, S] using cyclicAdvance_ne_of_lt base
        (a := e) (b := s) (by omega) (by omega) (by omega)
    t_ne_s := by
      simpa [T, S] using cyclicAdvance_ne_of_lt base
        (a := t) (b := s) (by omega) (by omega) (by omega)
    w_ne_s := by
      simpa [W, S] using cyclicAdvance_ne_of_lt base
        (a := w) (b := s) (by omega) (by omega) (by omega)
    r_ne_s := by
      simpa [R, S] using cyclicAdvance_ne_of_lt base
        (a := r) (b := s) (by omega) (by omega) (by omega)
    vertex_ne_e := by
      simpa [V, E] using cyclicAdvance_ne_of_lt base
        (a := v) (b := e) (by omega) (by omega) (by omega)
    vertex_ne_t := by
      simpa [V, T] using cyclicAdvance_ne_of_lt base
        (a := v) (b := t) (by omega) (by omega) (by omega)
    vertex_ne_s := by
      simpa [V, S] using cyclicAdvance_ne_of_lt base
        (a := v) (b := s) (by omega) (by omega) (by omega)
    vertex_ne_w := by
      simpa [V, W] using cyclicAdvance_ne_of_lt base
        (a := v) (b := w) (by omega) (by omega) (by omega)
    vertex_ne_r := by
      simpa [V, R] using cyclicAdvance_ne_of_lt base
        (a := v) (b := r) (by omega) (by omega) (by omega)
    tipAbove := hTip
    vertexBelow := hVertex
    wAbove := hWAbove
    rAbove := hRAbove
    wBelowTip := penultimate_turn_lt_shared_tip
      (hInjective.ne hET) hClasses.2.1 hes hts hew htw hWAbove hTip
    es := hes
    ts := hts
    ew := hew
    tw := htw
    er := her
    tr := htr
    antiSaturationQuad := hAnti
    ePositiveArc := positiveArc
    eNegativeArc := ∅
    tPositiveArc := ∅
    tNegativeArc := negativeArc
    arcPartition := hPartition
    ePositive_ne_tip := by
      simpa [positiveArc, S] using cyclicOpenInterval_ne_right base (by omega)
    eNegative_ne_tip := by simp
    tPositive_ne_tip := by simp
    tNegative_ne_tip := by
      simpa [negativeArc, S] using cyclicWrapInterval_ne_left base (by omega) (by omega)
    ePositive_center_ne := by
      simpa [positiveArc, E] using
        cyclicOpenInterval_center_ne_of_left base he_v (by omega)
    eNegative_center_ne := by simp
    tPositive_center_ne := by simp
    tNegative_center_ne := by
      simpa [negativeArc, T] using
        cyclicWrapInterval_center_ne_of_between base hv_t (by omega) (by omega)
    ePositiveHalfPlane := hPositiveHalfPlane
    eNegativeHalfPlane := by simp
    tPositiveHalfPlane := by simp
    tNegativeHalfPlane := hNegativeHalfPlane
    ePositiveQuad := hPositiveQuad
    eNegativeQuad := by simp
    tPositiveQuad := by simp
    tNegativeQuad := hNegativeQuad }⟩

/-- The corresponding five-label cyclic pattern realizes the raw
one-penultimate anti-saturation record. -/
theorem onePenultimateGeometry_of_cyclic_offsets
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hConvex : CyclicStrictConvex P)
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    (base : Fin n) {e v t p s : ℕ}
    (he_v : e < v) (hv_t : v < t) (ht_p : t < p)
    (hp_s : p < s) (hs_n : s < n)
    (hes : sqDist (P (cyclicAdvance base e))
      (P (cyclicAdvance base s)) = d₁)
    (hts : sqDist (P (cyclicAdvance base t))
      (P (cyclicAdvance base s)) = d₁)
    (htp : sqDist (P (cyclicAdvance base t))
      (P (cyclicAdvance base p)) = d₂) :
    Nonempty (OnePenultimateWordGeometry P d₁ d₂ d₃) := by
  classical
  let E := cyclicAdvance base e
  let V := cyclicAdvance base v
  let T := cyclicAdvance base t
  let Q := cyclicAdvance base p
  let S := cyclicAdvance base s
  let leftArc := cyclicOpenInterval base v s
  let rightArc := cyclicWrapInterval base s v
  have hInjective : Function.Injective P :=
    cyclic_strict_convex_injective hConvex (by omega)
  have hPartition : ∀ j, j ≠ V →
      j ∈ leftArc ∨ j = S ∨ j ∈ rightArc := by
    intro j hjV
    let k := cyclicOffset base j
    have hk : k < n := by
      dsimp [k, cyclicOffset]
      exact (j - base).isLt
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    have hkV : k ≠ v := by
      intro hkv
      apply hjV
      rw [hjEq, hkv]
    by_cases hkS : k = s
    · right; left
      rw [hjEq, hkS]
    by_cases hkMiddle : v < k ∧ k < s
    · left
      exact mem_cyclicOpenInterval.mpr hkMiddle
    · right; right
      exact mem_cyclicWrapInterval.mpr (by omega)
  have hLeftHalfPlane : ∀ j ∈ leftArc,
      InLeftOpenHalfPlane (P E) (P V) (P j) := by
    intro j hj
    have hkData := mem_cyclicOpenInterval.mp hj
    let k := cyclicOffset base j
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    rw [hjEq]
    simpa [E, V] using cyclic_inLeft_of_unwrapped_order hConvex base
      (a := e) (b := v) (k := k) (by omega) (by omega) (by omega)
  have hRightHalfPlane : ∀ j ∈ rightArc,
      InLeftOpenHalfPlane (P V) (P T) (P j) := by
    intro j hj
    have hkCases := mem_cyclicWrapInterval.mp hj
    let k := cyclicOffset base j
    have hk : k < n := by
      dsimp [k, cyclicOffset]
      exact (j - base).isLt
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    rw [hjEq]
    rcases hkCases with hkHigh | hkLow
    · exact cyclic_inLeft_of_unwrapped_order hConvex base
        (a := v) (b := t) (k := k) (by omega) (by omega) (by omega)
    · have h := cyclic_inLeft_of_unwrapped_order hConvex base
        (a := v) (b := t) (k := k + n) (by omega) (by omega) (by omega)
      rw [cyclicAdvance_period] at h
      exact h
  have hLeftQuad : ∀ j ∈ leftArc,
      StrictConvexQuad (P V) (P j) (P S) (P E) := by
    intro j hj
    have hkData := mem_cyclicOpenInterval.mp hj
    let k := cyclicOffset base j
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    have h := cyclic_strict_convex_quad_unwrapped hConvex base
      (a := v) (b := k) (c := s) (d := e + n)
      (by omega) (by omega) (by omega) (by omega)
    rw [cyclicAdvance_period] at h
    simpa [V, S, E, hjEq] using h
  have hRightQuad : ∀ j ∈ rightArc,
      StrictConvexQuad (P T) (P S) (P j) (P V) := by
    intro j hj
    have hkCases := mem_cyclicWrapInterval.mp hj
    let k := cyclicOffset base j
    have hk : k < n := by
      dsimp [k, cyclicOffset]
      exact (j - base).isLt
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    rcases hkCases with hkHigh | hkLow
    · change s < k at hkHigh
      have h := cyclic_strict_convex_quad_unwrapped hConvex base
        (a := t) (b := s) (c := k) (d := v + n)
        (by omega) (by omega) (by omega) (by omega)
      rw [cyclicAdvance_period] at h
      simpa [T, S, V, hjEq] using h
    · change k < v at hkLow
      have h := cyclic_strict_convex_quad_unwrapped hConvex base
        (a := t) (b := s) (c := k + n) (d := v + n)
        (by omega) (by omega) (by omega) (by omega)
      rw [cyclicAdvance_period, cyclicAdvance_period] at h
      simpa [T, S, V, hjEq] using h
  have hRung : StrictConvexQuad (P T) (P Q) (P S) (P V) := by
    have h := cyclic_strict_convex_quad_unwrapped hConvex base
      (a := t) (b := p) (c := s) (d := v + n)
      (by omega) (by omega) (by omega) (by omega)
    rw [cyclicAdvance_period] at h
    simpa [T, Q, S, V] using h
  refine ⟨{
    pointsInjective := hInjective
    classes := hClasses
    e := E
    vertex := V
    t := T
    p := Q
    s := S
    e_ne_vertex := by
      simpa [E, V] using cyclicAdvance_ne_of_lt base
        (a := e) (b := v) (by omega) (by omega) (by omega)
    t_ne_vertex := by
      simpa [T, V] using cyclicAdvance_ne_of_lt base
        (a := t) (b := v) (by omega) (by omega) (by omega)
    p_ne_vertex := by
      simpa [Q, V] using cyclicAdvance_ne_of_lt base
        (a := p) (b := v) (by omega) (by omega) (by omega)
    s_ne_vertex := by
      simpa [S, V] using cyclicAdvance_ne_of_lt base
        (a := s) (b := v) (by omega) (by omega) (by omega)
    e_ne_t := by
      simpa [E, T] using cyclicAdvance_ne_of_lt base
        (a := e) (b := t) (by omega) (by omega) (by omega)
    e_ne_s := by
      simpa [E, S] using cyclicAdvance_ne_of_lt base
        (a := e) (b := s) (by omega) (by omega) (by omega)
    t_ne_p := by
      simpa [T, Q] using cyclicAdvance_ne_of_lt base
        (a := t) (b := p) (by omega) (by omega) (by omega)
    t_ne_s := by
      simpa [T, S] using cyclicAdvance_ne_of_lt base
        (a := t) (b := s) (by omega) (by omega) (by omega)
    p_ne_s := by
      simpa [Q, S] using cyclicAdvance_ne_of_lt base
        (a := p) (b := s) (by omega) (by omega) (by omega)
    leftArc := leftArc
    rightArc := rightArc
    arcPartition := hPartition
    left_e_ne := by
      intro j hj hej
      subst j
      have hk := mem_cyclicOpenInterval.mp hj
      have hoff := cyclicOffset_cyclicAdvance base (k := e) (by omega)
      dsimp [E] at hk
      rw [hoff] at hk
      omega
    right_t_ne := by
      intro j hj htj
      subst j
      have hk := mem_cyclicWrapInterval.mp hj
      have hoff := cyclicOffset_cyclicAdvance base (k := t) (by omega)
      dsimp [T] at hk
      rw [hoff] at hk
      omega
    left_s_ne := by
      intro j hj hjs
      subst j
      have hk := mem_cyclicOpenInterval.mp hj
      have hoff := cyclicOffset_cyclicAdvance base (k := s) (by omega)
      dsimp [S] at hk
      rw [hoff] at hk
      omega
    right_s_ne := by
      intro j hj hjs
      subst j
      have hk := mem_cyclicWrapInterval.mp hj
      have hoff := cyclicOffset_cyclicAdvance base (k := s) (by omega)
      dsimp [S] at hk
      rw [hoff] at hk
      omega
    leftHalfPlane := hLeftHalfPlane
    rightHalfPlane := hRightHalfPlane
    leftQuad := hLeftQuad
    rightQuad := hRightQuad
    rungQuad := hRung
    tipAbove := by
      simpa [E, T, S] using cyclic_strict_convex_turn_unwrapped hConvex base
        (a := e) (b := t) (c := s) (by omega) (by omega) (by omega)
    vertexBelow := by
      have h := cyclic_strict_convex_turn_unwrapped hConvex base
        (a := e) (b := v) (c := t) (by omega) (by omega) (by omega)
      rw [turn_swap] at h
      simpa [E, T, V] using h
    es := hes
    ts := hts
    tp := htp }⟩

/-- Reflection reverses the row-4 cyclic orientation and turns the displayed
five-label pattern into the raw one-penultimate orientation. -/
theorem reflectedOnePenultimateGeometry_of_cyclic_offsets
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hConvex : CyclicStrictConvex P)
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    (base : Fin n) {t v e s p : ℕ}
    (ht_v : t < v) (hv_e : v < e) (he_s : e < s)
    (hs_p : s < p) (hp_n : p < n)
    (hes : sqDist (P (cyclicAdvance base e))
      (P (cyclicAdvance base s)) = d₁)
    (hts : sqDist (P (cyclicAdvance base t))
      (P (cyclicAdvance base s)) = d₁)
    (htp : sqDist (P (cyclicAdvance base t))
      (P (cyclicAdvance base p)) = d₂) :
    Nonempty (OnePenultimateWordGeometry
      (fun i ↦ reflectAcrossXAxis (P i)) d₁ d₂ d₃) := by
  classical
  let E := cyclicAdvance base e
  let V := cyclicAdvance base v
  let T := cyclicAdvance base t
  let Q := cyclicAdvance base p
  let S := cyclicAdvance base s
  let leftArc := cyclicWrapInterval base s v
  let rightArc := cyclicOpenInterval base v s
  have hPInjective : Function.Injective P :=
    cyclic_strict_convex_injective hConvex (by omega)
  have hInjective : Function.Injective
      (fun i ↦ reflectAcrossXAxis (P i)) :=
    reflectAcrossXAxis_injective.comp hPInjective
  have hPartition : ∀ j, j ≠ V →
      j ∈ leftArc ∨ j = S ∨ j ∈ rightArc := by
    intro j hjV
    let k := cyclicOffset base j
    have hk : k < n := by
      dsimp [k, cyclicOffset]
      exact (j - base).isLt
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    have hkV : k ≠ v := by
      intro hkv
      apply hjV
      rw [hjEq, hkv]
    by_cases hkS : k = s
    · right; left
      rw [hjEq, hkS]
    by_cases hkMiddle : v < k ∧ k < s
    · right; right
      exact mem_cyclicOpenInterval.mpr hkMiddle
    · left
      exact mem_cyclicWrapInterval.mpr (by omega)
  have hLeftHalfPlane : ∀ j ∈ leftArc,
      InLeftOpenHalfPlane (reflectAcrossXAxis (P E))
        (reflectAcrossXAxis (P V)) (reflectAcrossXAxis (P j)) := by
    intro j hj
    rw [reflectAcrossXAxis_halfPlane_reverse]
    have hkCases := mem_cyclicWrapInterval.mp hj
    let k := cyclicOffset base j
    have hk : k < n := by
      dsimp [k, cyclicOffset]
      exact (j - base).isLt
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    rw [hjEq]
    rcases hkCases with hkHigh | hkLow
    · exact cyclic_inLeft_of_unwrapped_order hConvex base
        (a := v) (b := e) (k := k) (by omega) (by omega) (by omega)
    · have h := cyclic_inLeft_of_unwrapped_order hConvex base
        (a := v) (b := e) (k := k + n) (by omega) (by omega) (by omega)
      rw [cyclicAdvance_period] at h
      exact h
  have hRightHalfPlane : ∀ j ∈ rightArc,
      InLeftOpenHalfPlane (reflectAcrossXAxis (P V))
        (reflectAcrossXAxis (P T)) (reflectAcrossXAxis (P j)) := by
    intro j hj
    rw [reflectAcrossXAxis_halfPlane_reverse]
    have hkData := mem_cyclicOpenInterval.mp hj
    let k := cyclicOffset base j
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    rw [hjEq]
    simpa [T, V] using cyclic_inLeft_of_unwrapped_order hConvex base
      (a := t) (b := v) (k := k) (by omega) (by omega) (by omega)
  have hLeftQuad : ∀ j ∈ leftArc,
      StrictConvexQuad (reflectAcrossXAxis (P V))
        (reflectAcrossXAxis (P j)) (reflectAcrossXAxis (P S))
        (reflectAcrossXAxis (P E)) := by
    intro j hj
    have hkCases := mem_cyclicWrapInterval.mp hj
    let k := cyclicOffset base j
    have hk : k < n := by
      dsimp [k, cyclicOffset]
      exact (j - base).isLt
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    rcases hkCases with hkHigh | hkLow
    · change s < k at hkHigh
      have h := cyclic_strict_convex_quad_unwrapped hConvex base
        (a := v) (b := e) (c := s) (d := k)
        (by omega) (by omega) (by omega) (by omega)
      have hr := reflectAcrossXAxis_strictConvexQuad_reverse h
      simpa [V, E, S, hjEq] using hr
    · change k < v at hkLow
      have h := cyclic_strict_convex_quad_unwrapped hConvex base
        (a := v) (b := e) (c := s) (d := k + n)
        (by omega) (by omega) (by omega) (by omega)
      rw [cyclicAdvance_period] at h
      have hr := reflectAcrossXAxis_strictConvexQuad_reverse h
      simpa [V, E, S, hjEq] using hr
  have hRightQuad : ∀ j ∈ rightArc,
      StrictConvexQuad (reflectAcrossXAxis (P T))
        (reflectAcrossXAxis (P S)) (reflectAcrossXAxis (P j))
        (reflectAcrossXAxis (P V)) := by
    intro j hj
    have hkData := mem_cyclicOpenInterval.mp hj
    let k := cyclicOffset base j
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    have h := cyclic_strict_convex_quad_unwrapped hConvex base
      (a := t) (b := v) (c := k) (d := s)
      (by omega) (by omega) (by omega) (by omega)
    have hr := reflectAcrossXAxis_strictConvexQuad_reverse h
    simpa [T, V, S, hjEq] using hr
  have hRung : StrictConvexQuad (reflectAcrossXAxis (P T))
      (reflectAcrossXAxis (P Q)) (reflectAcrossXAxis (P S))
      (reflectAcrossXAxis (P V)) := by
    have h := cyclic_strict_convex_quad_unwrapped hConvex base
      (a := t) (b := v) (c := s) (d := p)
      (by omega) (by omega) (by omega) (by omega)
    have hr := reflectAcrossXAxis_strictConvexQuad_reverse h
    simpa [T, V, S, Q] using hr
  refine ⟨{
    pointsInjective := hInjective
    classes := reflectAcrossXAxis_top_three_classes hClasses
    e := E
    vertex := V
    t := T
    p := Q
    s := S
    e_ne_vertex := by
      simpa [E, V] using cyclicAdvance_ne_of_lt base
        (a := e) (b := v) (by omega) (by omega) (by omega)
    t_ne_vertex := by
      simpa [T, V] using cyclicAdvance_ne_of_lt base
        (a := t) (b := v) (by omega) (by omega) (by omega)
    p_ne_vertex := by
      simpa [Q, V] using cyclicAdvance_ne_of_lt base
        (a := p) (b := v) (by omega) (by omega) (by omega)
    s_ne_vertex := by
      simpa [S, V] using cyclicAdvance_ne_of_lt base
        (a := s) (b := v) (by omega) (by omega) (by omega)
    e_ne_t := by
      simpa [E, T] using cyclicAdvance_ne_of_lt base
        (a := e) (b := t) (by omega) (by omega) (by omega)
    e_ne_s := by
      simpa [E, S] using cyclicAdvance_ne_of_lt base
        (a := e) (b := s) (by omega) (by omega) (by omega)
    t_ne_p := by
      simpa [T, Q] using cyclicAdvance_ne_of_lt base
        (a := t) (b := p) (by omega) (by omega) (by omega)
    t_ne_s := by
      simpa [T, S] using cyclicAdvance_ne_of_lt base
        (a := t) (b := s) (by omega) (by omega) (by omega)
    p_ne_s := by
      simpa [Q, S] using cyclicAdvance_ne_of_lt base
        (a := p) (b := s) (by omega) (by omega) (by omega)
    leftArc := leftArc
    rightArc := rightArc
    arcPartition := hPartition
    left_e_ne := by
      simpa [leftArc, E] using
        cyclicWrapInterval_center_ne_of_between base hv_e he_s (by omega)
    right_t_ne := by
      simpa [rightArc, T] using
        cyclicOpenInterval_center_ne_of_left base ht_v (by omega)
    left_s_ne := by
      simpa [leftArc, S] using
        cyclicWrapInterval_ne_left base (by omega) (by omega)
    right_s_ne := by
      simpa [rightArc, S] using cyclicOpenInterval_ne_right base (by omega)
    leftHalfPlane := hLeftHalfPlane
    rightHalfPlane := hRightHalfPlane
    leftQuad := hLeftQuad
    rightQuad := hRightQuad
    rungQuad := hRung
    tipAbove := by
      have h := cyclic_strict_convex_turn_unwrapped hConvex base
        (a := e) (b := s) (c := t + n)
        (by omega) (by omega) (by omega)
      rw [cyclicAdvance_period] at h
      rw [turn_swap] at h
      simpa [E, T, S] using h
    vertexBelow := by
      have h := cyclic_strict_convex_turn_unwrapped hConvex base
        (a := e) (b := t + n) (c := v + n)
        (by omega) (by omega) (by omega)
      rw [cyclicAdvance_period, cyclicAdvance_period] at h
      simpa [E, T, V] using h
    es := by simpa using hes
    ts := by simpa using hts
    tp := by simpa using htp }⟩

private theorem reflected_cyclic_strictConvexQuad_unwrapped
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ}
    (hConvex : CyclicStrictConvex P) (base : Fin n)
    {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hwindow : d < a + n) :
    StrictConvexQuad
      (reflectAcrossXAxis (P (cyclicAdvance base a)))
      (reflectAcrossXAxis (P (cyclicAdvance base d)))
      (reflectAcrossXAxis (P (cyclicAdvance base c)))
      (reflectAcrossXAxis (P (cyclicAdvance base b))) :=
  reflectAcrossXAxis_strictConvexQuad_reverse
    (cyclic_strict_convex_quad_unwrapped hConvex base hab hbc hcd hwindow)

private theorem reflected_terminal_central_quads
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ}
    (hConvex : CyclicStrictConvex P) (base : Fin n)
    {t v x s w : ℕ} (ht_v : t < v) (hv_x : v < x) (hx_s : x < s)
    (hs_w : s < w) (hw_n : w < n) :
    StrictConvexQuad
        (reflectAcrossXAxis (P (cyclicAdvance base v)))
        (reflectAcrossXAxis (P (cyclicAdvance base w)))
        (reflectAcrossXAxis (P (cyclicAdvance base s)))
        (reflectAcrossXAxis (P (cyclicAdvance base x))) ∧
      StrictConvexQuad
        (reflectAcrossXAxis (P (cyclicAdvance base t)))
        (reflectAcrossXAxis (P (cyclicAdvance base w)))
        (reflectAcrossXAxis (P (cyclicAdvance base s)))
        (reflectAcrossXAxis (P (cyclicAdvance base v))) ∧
      StrictConvexQuad
        (reflectAcrossXAxis (P (cyclicAdvance base t)))
        (reflectAcrossXAxis (P (cyclicAdvance base w)))
        (reflectAcrossXAxis (P (cyclicAdvance base s)))
        (reflectAcrossXAxis (P (cyclicAdvance base x))) := by
  constructor
  · exact reflected_cyclic_strictConvexQuad_unwrapped hConvex base
      hv_x hx_s hs_w (by omega)
  constructor
  · exact reflected_cyclic_strictConvexQuad_unwrapped hConvex base
      ht_v (by omega) hs_w (by omega)
  · exact reflected_cyclic_strictConvexQuad_unwrapped hConvex base
      (by omega) hx_s hs_w (by omega)

/-- Reflected terminal-cage adapter for the row-4 `D32` orientation. -/
theorem reflectedRow1B32Geometry_of_cyclic_offsets
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hConvex : CyclicStrictConvex P)
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    (base : Fin n) {t v x s w : ℕ}
    (ht_v : t < v) (hv_x : v < x) (hx_s : x < s)
    (hsw : w = s + 1) (hw_n : w < n)
    (hxw : sqDist (P (cyclicAdvance base x))
      (P (cyclicAdvance base w)) ≤ d₂)
    (hxs : sqDist (P (cyclicAdvance base x))
      (P (cyclicAdvance base s)) = d₂)
    (htw : sqDist (P (cyclicAdvance base t))
      (P (cyclicAdvance base w)) = d₂)
    (hts : sqDist (P (cyclicAdvance base t))
      (P (cyclicAdvance base s)) = d₁) :
    Nonempty (Row1B32WordRealization
      (fun i ↦ reflectAcrossXAxis (P i)) d₁ d₂ d₃) := by
  classical
  let X := cyclicAdvance base x
  let V := cyclicAdvance base v
  let T := cyclicAdvance base t
  let W := cyclicAdvance base w
  let S := cyclicAdvance base s
  let leftArc := cyclicWrapInterval base w v
  let rightArc := cyclicOpenInterval base v s
  have hPInjective : Function.Injective P :=
    cyclic_strict_convex_injective hConvex (by omega)
  have hInjective : Function.Injective
      (fun i ↦ reflectAcrossXAxis (P i)) :=
    reflectAcrossXAxis_injective.comp hPInjective
  have hPartition : ∀ j, j ≠ V →
      j ∈ leftArc ∨ j = W ∨ j = S ∨ j ∈ rightArc := by
    intro j hjV
    let k := cyclicOffset base j
    have hk : k < n := by
      dsimp [k, cyclicOffset]
      exact (j - base).isLt
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    have hkV : k ≠ v := by
      intro hkv
      apply hjV
      rw [hjEq, hkv]
    by_cases hkW : k = w
    · right; left
      rw [hjEq, hkW]
    by_cases hkS : k = s
    · right; right; left
      rw [hjEq, hkS]
    by_cases hkMiddle : v < k ∧ k < s
    · right; right; right
      exact mem_cyclicOpenInterval.mpr hkMiddle
    · left
      exact mem_cyclicWrapInterval.mpr (by omega)
  have hLeftHalfPlane : ∀ j ∈ leftArc,
      InLeftOpenHalfPlane (reflectAcrossXAxis (P X))
        (reflectAcrossXAxis (P V)) (reflectAcrossXAxis (P j)) := by
    intro j hj
    rw [reflectAcrossXAxis_halfPlane_reverse]
    have hkCases := mem_cyclicWrapInterval.mp hj
    let k := cyclicOffset base j
    have hk : k < n := by
      dsimp [k, cyclicOffset]
      exact (j - base).isLt
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    rw [hjEq]
    rcases hkCases with hkHigh | hkLow
    · exact cyclic_inLeft_of_unwrapped_order hConvex base
        (a := v) (b := x) (k := k) (by omega) (by omega) (by omega)
    · have h := cyclic_inLeft_of_unwrapped_order hConvex base
        (a := v) (b := x) (k := k + n) (by omega) (by omega) (by omega)
      rw [cyclicAdvance_period] at h
      exact h
  have hRightHalfPlane : ∀ j ∈ rightArc,
      InLeftOpenHalfPlane (reflectAcrossXAxis (P V))
        (reflectAcrossXAxis (P T)) (reflectAcrossXAxis (P j)) := by
    intro j hj
    rw [reflectAcrossXAxis_halfPlane_reverse]
    have hkData := mem_cyclicOpenInterval.mp hj
    let k := cyclicOffset base j
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    rw [hjEq]
    simpa [T, V] using cyclic_inLeft_of_unwrapped_order hConvex base
      (a := t) (b := v) (k := k) (by omega) (by omega) (by omega)
  have hLeftQuad : ∀ j ∈ leftArc,
      StrictConvexQuad (reflectAcrossXAxis (P V))
        (reflectAcrossXAxis (P j)) (reflectAcrossXAxis (P S))
        (reflectAcrossXAxis (P X)) := by
    intro j hj
    have hkCases := mem_cyclicWrapInterval.mp hj
    let k := cyclicOffset base j
    have hk : k < n := by
      dsimp [k, cyclicOffset]
      exact (j - base).isLt
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    rcases hkCases with hkHigh | hkLow
    · change w < k at hkHigh
      have h := cyclic_strict_convex_quad_unwrapped hConvex base
        (a := v) (b := x) (c := s) (d := k)
        (by omega) (by omega) (by omega) (by omega)
      have hr := reflectAcrossXAxis_strictConvexQuad_reverse h
      simpa [V, X, S, hjEq] using hr
    · change k < v at hkLow
      have h := cyclic_strict_convex_quad_unwrapped hConvex base
        (a := v) (b := x) (c := s) (d := k + n)
        (by omega) (by omega) (by omega) (by omega)
      rw [cyclicAdvance_period] at h
      have hr := reflectAcrossXAxis_strictConvexQuad_reverse h
      simpa [V, X, S, hjEq] using hr
  have hRightQuad : ∀ j ∈ rightArc,
      StrictConvexQuad (reflectAcrossXAxis (P T))
        (reflectAcrossXAxis (P S)) (reflectAcrossXAxis (P j))
        (reflectAcrossXAxis (P V)) := by
    intro j hj
    have hkData := mem_cyclicOpenInterval.mp hj
    let k := cyclicOffset base j
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    have h := cyclic_strict_convex_quad_unwrapped hConvex base
      (a := t) (b := v) (c := k) (d := s)
      (by omega) (by omega) (by omega) (by omega)
    have hr := reflectAcrossXAxis_strictConvexQuad_reverse h
    simpa [T, V, S, hjEq] using hr
  have ⟨hCentralLeft, hCentralRight, hTerminal⟩ :=
    reflected_terminal_central_quads hConvex base ht_v hv_x hx_s
      (by omega) hw_n
  have hShortLeft : ∀ j ∈ leftArc,
      StrictConvexQuad (reflectAcrossXAxis (P V))
        (reflectAcrossXAxis (P j)) (reflectAcrossXAxis (P W))
        (reflectAcrossXAxis (P X)) := by
    intro j hj
    have hkCases := mem_cyclicWrapInterval.mp hj
    let k := cyclicOffset base j
    have hk : k < n := by
      dsimp [k, cyclicOffset]
      exact (j - base).isLt
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    rcases hkCases with hkHigh | hkLow
    · change w < k at hkHigh
      have h := cyclic_strict_convex_quad_unwrapped hConvex base
        (a := v) (b := x) (c := w) (d := k)
        (by omega) (by omega) (by omega) (by omega)
      have hr := reflectAcrossXAxis_strictConvexQuad_reverse h
      simpa [V, X, W, hjEq] using hr
    · change k < v at hkLow
      have h := cyclic_strict_convex_quad_unwrapped hConvex base
        (a := v) (b := x) (c := w) (d := k + n)
        (by omega) (by omega) (by omega) (by omega)
      rw [cyclicAdvance_period] at h
      have hr := reflectAcrossXAxis_strictConvexQuad_reverse h
      simpa [V, X, W, hjEq] using hr
  refine ⟨{
    pointsInjective := hInjective
    classes := reflectAcrossXAxis_top_three_classes hClasses
    x := X
    vertex := V
    t := T
    w := W
    s := S
    x_ne_vertex := by
      simpa [X, V] using cyclicAdvance_ne_of_lt base
        (a := x) (b := v) (by omega) (by omega) (by omega)
    t_ne_vertex := by
      simpa [T, V] using cyclicAdvance_ne_of_lt base
        (a := t) (b := v) (by omega) (by omega) (by omega)
    x_ne_t := by
      simpa [X, T] using cyclicAdvance_ne_of_lt base
        (a := x) (b := t) (by omega) (by omega) (by omega)
    x_ne_w := by
      simpa [X, W] using cyclicAdvance_ne_of_lt base
        (a := x) (b := w) (by omega) (by omega) (by omega)
    x_ne_s := by
      simpa [X, S] using cyclicAdvance_ne_of_lt base
        (a := x) (b := s) (by omega) (by omega) (by omega)
    t_ne_w := by
      simpa [T, W] using cyclicAdvance_ne_of_lt base
        (a := t) (b := w) (by omega) (by omega) (by omega)
    t_ne_s := by
      simpa [T, S] using cyclicAdvance_ne_of_lt base
        (a := t) (b := s) (by omega) (by omega) (by omega)
    w_ne_s := by
      simpa [W, S] using cyclicAdvance_ne_of_lt base
        (a := w) (b := s) (by omega) (by omega) (by omega)
    w_ne_vertex := by
      simpa [W, V] using cyclicAdvance_ne_of_lt base
        (a := w) (b := v) (by omega) (by omega) (by omega)
    s_ne_vertex := by
      simpa [S, V] using cyclicAdvance_ne_of_lt base
        (a := s) (b := v) (by omega) (by omega) (by omega)
    leftArc := leftArc
    rightArc := rightArc
    arcPartition := hPartition
    leftHalfPlane := hLeftHalfPlane
    left_x_ne := by
      simpa [leftArc, X] using
        cyclicWrapInterval_center_ne_of_between base hv_x (by omega) (by omega)
    rightHalfPlane := hRightHalfPlane
    right_t_ne := by
      simpa [rightArc, T] using
        cyclicOpenInterval_center_ne_of_left base ht_v (by omega)
    leftQuad := hLeftQuad
    rightQuad := hRightQuad
    centralLeftQuad := hCentralLeft
    centralRightQuad := hCentralRight
    terminalQuad := hTerminal
    shortLeftQuad := hShortLeft
    xw_le := by simpa using hxw
    xs := by simpa using hxs
    tw := by simpa using htw
    ts := by simpa using hts }⟩

/-- One endpoint of the row-4 four-edge cage, generated from its cyclic
offset pattern. -/
theorem fourEdgeEndpointGeometry_of_cyclic_offsets
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hConvex : CyclicStrictConvex P) (base : Fin n)
    {x v t w s : ℕ} (hx_v : x < v) (hv_t : v < t)
    (ht_w : t < w) (hsucc : s = w + 1) (hs_n : s < n)
    (hxw : sqDist (P (cyclicAdvance base x))
      (P (cyclicAdvance base w)) = d₁)
    (hts : sqDist (P (cyclicAdvance base t))
      (P (cyclicAdvance base s)) = d₁) :
    ∃ E : FourEdgeEndpointGeometry P d₁ d₂ d₃
        (cyclicAdvance base x) (cyclicAdvance base t)
        (cyclicAdvance base w) (cyclicAdvance base s),
      E.vertex = cyclicAdvance base v := by
  classical
  let X := cyclicAdvance base x
  let V := cyclicAdvance base v
  let T := cyclicAdvance base t
  let W := cyclicAdvance base w
  let S := cyclicAdvance base s
  let leftArc := cyclicOpenInterval base v w
  let rightArc := cyclicWrapInterval base s v
  have hPartition : ∀ j, j ≠ V →
      j ∈ leftArc ∨ j = W ∨ j = S ∨ j ∈ rightArc := by
    intro j hjV
    let k := cyclicOffset base j
    have hk : k < n := by
      dsimp [k, cyclicOffset]
      exact (j - base).isLt
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    have hkV : k ≠ v := by
      intro hkv
      apply hjV
      rw [hjEq, hkv]
    by_cases hkW : k = w
    · right; left
      rw [hjEq, hkW]
    by_cases hkS : k = s
    · right; right; left
      rw [hjEq, hkS]
    by_cases hkMiddle : v < k ∧ k < w
    · left
      exact mem_cyclicOpenInterval.mpr hkMiddle
    · right; right; right
      exact mem_cyclicWrapInterval.mpr (by omega)
  have hLeftHalfPlane : ∀ j ∈ leftArc,
      InLeftOpenHalfPlane (P X) (P V) (P j) := by
    intro j hj
    have hkData := mem_cyclicOpenInterval.mp hj
    let k := cyclicOffset base j
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    rw [hjEq]
    simpa [X, V] using cyclic_inLeft_of_unwrapped_order hConvex base
      (a := x) (b := v) (k := k) (by omega) (by omega) (by omega)
  have hRightHalfPlane : ∀ j ∈ rightArc,
      InLeftOpenHalfPlane (P V) (P T) (P j) := by
    intro j hj
    have hkCases := mem_cyclicWrapInterval.mp hj
    let k := cyclicOffset base j
    have hk : k < n := by
      dsimp [k, cyclicOffset]
      exact (j - base).isLt
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    rw [hjEq]
    rcases hkCases with hkHigh | hkLow
    · exact cyclic_inLeft_of_unwrapped_order hConvex base
        (a := v) (b := t) (k := k) (by omega) (by omega) (by omega)
    · have h := cyclic_inLeft_of_unwrapped_order hConvex base
        (a := v) (b := t) (k := k + n) (by omega) (by omega) (by omega)
      rw [cyclicAdvance_period] at h
      exact h
  have hLeftQuad : ∀ j ∈ leftArc,
      StrictConvexQuad (P V) (P j) (P W) (P X) := by
    intro j hj
    have hkData := mem_cyclicOpenInterval.mp hj
    let k := cyclicOffset base j
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    have h := cyclic_strict_convex_quad_unwrapped hConvex base
      (a := v) (b := k) (c := w) (d := x + n)
      (by omega) (by omega) (by omega) (by omega)
    rw [cyclicAdvance_period] at h
    simpa [V, W, X, hjEq] using h
  have hRightQuad : ∀ j ∈ rightArc,
      StrictConvexQuad (P T) (P S) (P j) (P V) := by
    intro j hj
    have hkCases := mem_cyclicWrapInterval.mp hj
    let k := cyclicOffset base j
    have hk : k < n := by
      dsimp [k, cyclicOffset]
      exact (j - base).isLt
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    rcases hkCases with hkHigh | hkLow
    · change s < k at hkHigh
      have h := cyclic_strict_convex_quad_unwrapped hConvex base
        (a := t) (b := s) (c := k) (d := v + n)
        (by omega) (by omega) (by omega) (by omega)
      rw [cyclicAdvance_period] at h
      simpa [T, S, V, hjEq] using h
    · change k < v at hkLow
      have h := cyclic_strict_convex_quad_unwrapped hConvex base
        (a := t) (b := s) (c := k + n) (d := v + n)
        (by omega) (by omega) (by omega) (by omega)
      rw [cyclicAdvance_period, cyclicAdvance_period] at h
      simpa [T, S, V, hjEq] using h
  refine ⟨{
    vertex := V
    w_ne_vertex := by
      simpa [W, V] using cyclicAdvance_ne_of_lt base
        (a := w) (b := v) (by omega) (by omega) (by omega)
    s_ne_vertex := by
      simpa [S, V] using cyclicAdvance_ne_of_lt base
        (a := s) (b := v) (by omega) (by omega) (by omega)
    left := {
      arc := leftArc
      center_ne_vertex := by
        simpa [X, V] using cyclicAdvance_ne_of_lt base
          (a := x) (b := v) (by omega) (by omega) (by omega)
      center_ne_arc := by
        intro j hj hxj
        subst j
        have hk := mem_cyclicOpenInterval.mp hj
        have hoff := cyclicOffset_cyclicAdvance base (k := x) (by omega)
        rw [hoff] at hk
        omega
      halfPlane := Or.inl hLeftHalfPlane
      quad := by
        intro j hj
        exact Or.inl (hLeftQuad j hj)
      diameterEdge := by simpa [X, W] using hxw }
    right := {
      arc := rightArc
      center_ne_vertex := by
        simpa [T, V] using cyclicAdvance_ne_of_lt base
          (a := t) (b := v) (by omega) (by omega) (by omega)
      center_ne_arc := by
        intro j hj htj
        subst j
        have hk := mem_cyclicWrapInterval.mp hj
        have hoff := cyclicOffset_cyclicAdvance base (k := t) (by omega)
        rw [hoff] at hk
        omega
      halfPlane := Or.inr hRightHalfPlane
      quad := by
        intro j hj
        exact Or.inr (hRightQuad j hj)
      diameterEdge := by simpa [T, S] using hts }
    arcPartition := hPartition }, rfl⟩

namespace K3CoverSequence

/-- Any actual two-cover witness exhausts the three strict distance ranks,
independently of the order in which its endpoints move. -/
theorem two_cover_rank_endpoints
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {i j : Fin n} {leftMoves rightMoves : ℕ}
    (path : K3CoverSequence P i j leftMoves rightMoves)
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    (hStart : TopThreeAdjacent P d₁ d₂ d₃ i j)
    (hEnd : TopThreeAdjacent P d₁ d₂ d₃
      (cyclicRetreat i leftMoves) (cyclicAdvance j rightMoves))
    (hMoves : leftMoves + rightMoves = 2) :
    sqDist (P i) (P j) = d₃ ∧
      sqDist (P (cyclicRetreat i leftMoves))
        (P (cyclicAdvance j rightMoves)) = d₁ := by
  cases path with
  | nil =>
      omega
  | @left i' j' leftMoves rightMoves hCover tail =>
      unfold IsLeftCover at hCover
      have hd₃d₂ := hClasses.1
      have hd₂d₁ := hClasses.2.1
      have hTailPos : 0 < leftMoves + rightMoves := by omega
      have hMid := left_cover_top_three_adjacent hClasses hStart hCover
      have hTailGrow := K3CoverSequence.sqDist_lt_terminal_of_positive
        tail hTailPos
      have hEnd' : TopThreeAdjacent P d₁ d₂ d₃
          (cyclicRetreat i (leftMoves + 1))
          (cyclicAdvance j rightMoves) := hEnd
      have hTailGrow' :
          sqDist (P (cyclicRetreat i 1)) (P j) <
            sqDist (P (cyclicRetreat i (leftMoves + 1)))
              (P (cyclicAdvance j rightMoves)) := by
        simpa [cyclicRetreat_add, Nat.add_comm] using hTailGrow
      rcases hStart.2 with hs₁ | hs₂ | hs₃ <;>
        rcases hMid.2 with hm₁ | hm₂ | hm₃ <;>
        rcases hEnd'.2 with he₁ | he₂ | he₃ <;>
        constructor <;> linarith
  | @right i' j' leftMoves rightMoves hCover tail =>
      unfold IsRightCover at hCover
      have hd₃d₂ := hClasses.1
      have hd₂d₁ := hClasses.2.1
      have hTailPos : 0 < leftMoves + rightMoves := by omega
      have hMid := right_cover_top_three_adjacent hClasses hStart hCover
      have hTailGrow := K3CoverSequence.sqDist_lt_terminal_of_positive
        tail hTailPos
      have hEnd' : TopThreeAdjacent P d₁ d₂ d₃
          (cyclicRetreat i leftMoves)
          (cyclicAdvance j (rightMoves + 1)) := hEnd
      have hTailGrow' :
          sqDist (P i) (P (cyclicAdvance j 1)) <
            sqDist (P (cyclicRetreat i leftMoves))
              (P (cyclicAdvance j (rightMoves + 1))) := by
        simpa [cyclicAdvance_add, Nat.add_comm] using hTailGrow
      rcases hStart.2 with hs₁ | hs₂ | hs₃ <;>
        rcases hMid.2 with hm₁ | hm₂ | hm₃ <;>
        rcases hEnd'.2 with he₁ | he₂ | he₃ <;>
        constructor <;> linarith

end K3CoverSequence

namespace K3CoverSequence

/-- A one-right/one-left path which starts on the right has the expected
`d₃,d₂,d₁` ladder. -/
theorem right_left_cover_rank_ladder
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {i j : Fin n} (hStart : TopThreeAdjacent P d₁ d₂ d₃ i j)
    (path : K3CoverSequence P i j 1 1) (hOrder : path.StartsRight) :
    sqDist (P i) (P j) = d₃ ∧
      sqDist (P i) (P (cyclicAdvance j 1)) = d₂ ∧
      sqDist (P (cyclicRetreat i 1)) (P (cyclicAdvance j 1)) = d₁ := by
  cases hOrder with
  | intro h₀ tail =>
      cases tail with
      | left h₁ tail =>
          cases tail with
          | nil =>
              unfold IsRightCover at h₀
              unfold IsLeftCover at h₁
              have hMid := right_cover_top_three_adjacent hClasses hStart h₀
              have hEnd := left_cover_top_three_adjacent hClasses hMid h₁
              have hd₃d₂ := hClasses.1
              have hd₂d₁ := hClasses.2.1
              have hEndRank : sqDist (P (cyclicRetreat i 1))
                  (P (cyclicAdvance j 1)) = d₁ :=
                two_covers_end_at_d₁ hClasses hStart hMid hEnd h₀ h₁
              have hMidRank : sqDist (P i) (P (cyclicAdvance j 1)) = d₂ := by
                rcases hMid.2 with hm₁ | hm₂ | hm₃
                · linarith
                · exact hm₂
                · rcases hStart.2 with hs₁ | hs₂ | hs₃ <;> linarith
              have hStartRank : sqDist (P i) (P j) = d₃ := by
                rcases hStart.2 with hs₁ | hs₂ | hs₃ <;> linarith
              exact ⟨hStartRank, hMidRank, hEndRank⟩

/-- The opposite one-left/one-right order has the same rank ladder, with
the middle edge obtained by retreating the left endpoint. -/
theorem left_right_cover_rank_ladder
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {i j : Fin n} (hStart : TopThreeAdjacent P d₁ d₂ d₃ i j)
    (path : K3CoverSequence P i j 1 1) (hOrder : path.StartsLeft) :
    sqDist (P i) (P j) = d₃ ∧
      sqDist (P (cyclicRetreat i 1)) (P j) = d₂ ∧
      sqDist (P (cyclicRetreat i 1)) (P (cyclicAdvance j 1)) = d₁ := by
  cases hOrder with
  | intro h₀ tail =>
      cases tail with
      | right h₁ tail =>
          cases tail with
          | nil =>
              unfold IsLeftCover at h₀
              unfold IsRightCover at h₁
              have hMid := left_cover_top_three_adjacent hClasses hStart h₀
              have hEnd := right_cover_top_three_adjacent hClasses hMid h₁
              have hd₃d₂ := hClasses.1
              have hd₂d₁ := hClasses.2.1
              have hEndRank : sqDist (P (cyclicRetreat i 1))
                  (P (cyclicAdvance j 1)) = d₁ :=
                two_covers_end_at_d₁ hClasses hStart hMid hEnd h₀ h₁
              have hMidRank : sqDist (P (cyclicRetreat i 1)) (P j) = d₂ := by
                rcases hMid.2 with hm₁ | hm₂ | hm₃
                · linarith
                · exact hm₂
                · rcases hStart.2 with hs₁ | hs₂ | hs₃ <;> linarith
              have hStartRank : sqDist (P i) (P j) = d₃ := by
                rcases hStart.2 with hs₁ | hs₂ | hs₃ <;> linarith
              exact ⟨hStartRank, hMidRank, hEndRank⟩

end K3CoverSequence

namespace ErLVGlobalFiveRowFrame

/-- First-neighbor gap at the second anchor `x+3`. -/
noncomputable def secondGap
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) : ℕ :=
  firstNeighborGap P d₁ d₂ d₃ (cyclicAdvance F.x 3)

/-- Offset of the second anchor's first counterclockwise neighbor from `x`. -/
noncomputable def uOffset
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) : ℕ := 3 + F.secondGap

/-- Offset of the first clockwise neighbor of `x`, measured counterclockwise. -/
noncomputable def zOffset
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) : ℕ :=
  n - (firstClockwiseNeighborOffset P d₁ d₂ d₃ F.x).val

theorem card_ge_eight
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) : 8 ≤ n :=
  eight_le_card_of_degree_seven (F.highDegree F.x)

theorem secondGap_pos
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) : 0 < F.secondGap := by
  have hdegree : 0 < vertexDegree P d₁ d₂ d₃ (cyclicAdvance F.x 3) := by
    have := F.highDegree (cyclicAdvance F.x 3)
    omega
  have hne := (firstNeighborOffset_spec_of_degree_pos hdegree).1
  dsimp [secondGap, firstNeighborGap]
  have hval : (firstNeighborOffset P d₁ d₂ d₃
      (cyclicAdvance F.x 3)).val ≠ 0 := by
    intro hz
    apply hne
    apply Fin.ext
    simpa using hz
  omega

theorem uOffset_add_M_lt_card
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) :
    F.uOffset + F.M < n := by
  let gx := firstNeighborGap P d₁ d₂ d₃ F.x
  let gt := F.secondGap
  let hx := (firstClockwiseNeighborOffset P d₁ d₂ d₃ F.x).val
  have hxdeg : 0 < vertexDegree P d₁ d₂ d₃ F.x := by
    have := F.highDegree F.x
    omega
  have hhx : 0 < hx := by
    simpa [hx] using firstClockwiseNeighborOffset_pos_of_degree_pos hxdeg
  have hbudget : gx + hx + 6 ≤ n := by
    simpa [gx, hx] using first_neighbor_gap_cw_budget (v := F.x)
      (F.highDegree F.x)
  have hgt : gt ≤ gx := by
    simpa [gt, gx, secondGap] using
      F.maximalGap (cyclicAdvance F.x 3)
  have hM : F.M ≤ 2 := by
    exact F.M_le_secondRight.trans
      (F.pair.second.rightMoves.le_add_left F.pair.second.leftMoves |>.trans
        F.pair.second.coverBudget)
  dsimp [uOffset]
  omega

theorem zOffset_lt_card
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) : F.zOffset < n := by
  have hxdeg : 0 < vertexDegree P d₁ d₂ d₃ F.x := by
    have := F.highDegree F.x
    omega
  have hhx :
      0 < (firstClockwiseNeighborOffset P d₁ d₂ d₃ F.x).val := by
    exact firstClockwiseNeighborOffset_pos_of_degree_pos hxdeg
  dsimp [zOffset]
  omega

/-- Outer localization is equality of unwrapped offsets, not merely equality
of labels. -/
theorem zOffset_eq_uOffset_add
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) :
    F.zOffset = F.uOffset + F.M + F.pair.first.leftMoves := by
  let hx := (firstClockwiseNeighborOffset P d₁ d₂ d₃ F.x).val
  let b := F.pair.first.leftMoves
  let zoff := F.zOffset
  let uoff := F.uOffset
  let soff := zoff - b
  let umoff := uoff + F.M
  have hxdeg : 0 < vertexDegree P d₁ d₂ d₃ F.x := by
    have := F.highDegree F.x
    omega
  have hhx : 0 < hx := by
    simpa [hx] using firstClockwiseNeighborOffset_pos_of_degree_pos hxdeg
  have hb : b ≤ 2 := by
    have := F.pair.first.coverBudget
    dsimp [b]
    omega
  have hUM := F.uOffset_add_M_lt_card
  have hzoff : zoff < n := by
    dsimp [zoff, zOffset, hx]
    omega
  have hbz : b ≤ zoff := by
    dsimp [zoff, zOffset, hx]
    have hbudget := first_neighbor_gap_cw_budget
      (P := P) (d₁ := d₁) (d₂ := d₂) (d₃ := d₃) (v := F.x)
      (F.highDegree F.x)
    omega
  have hsoff : soff < n := by
    dsimp [soff]
    omega
  have humoff : umoff < n := by
    simpa [umoff] using hUM
  have hzIndex :
      firstClockwiseNeighbor P d₁ d₂ d₃ F.x =
        cyclicAdvance F.x zoff := by
    dsimp [zoff, zOffset, hx]
    rw [show firstClockwiseNeighbor P d₁ d₂ d₃ F.x =
        cyclicRetreat F.x hx by rfl,
      cyclicRetreat_eq_advance_complement F.x hhx
        (firstClockwiseNeighborOffset P d₁ d₂ d₃ F.x).isLt]
  have hsIndex :
      cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) b =
        cyclicAdvance F.x soff := by
    rw [hzIndex, cyclicRetreat_advance F.x hbz hzoff]
  have huIndex :
      firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance F.x 3) =
        cyclicAdvance F.x uoff := by
    dsimp [uoff, uOffset, secondGap, firstCounterclockwiseNeighbor]
    rw [cyclicAdvance_add]
  have huMIndex :
      cyclicAdvance
          (firstCounterclockwiseNeighbor P d₁ d₂ d₃
            (cyclicAdvance F.x 3)) F.M =
        cyclicAdvance F.x umoff := by
    rw [huIndex, cyclicAdvance_add]
  have hoffLabel : cyclicAdvance F.x soff = cyclicAdvance F.x umoff := by
    rw [← hsIndex, ← huMIndex]
    exact F.outerLocalized
  have hoff : soff = umoff := by
    have hfin : Fin.ofNat n soff = Fin.ofNat n umoff := by
      unfold cyclicAdvance at hoffLabel
      exact add_left_cancel hoffLabel
    have hval := congrArg Fin.val hfin
    simpa [Fin.ofNat, Nat.mod_eq_of_lt hsoff,
      Nat.mod_eq_of_lt humoff] using hval
  dsimp [soff, umoff] at hoff
  omega

theorem firstClockwiseNeighbor_eq_offset
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) :
    firstClockwiseNeighbor P d₁ d₂ d₃ F.x =
      cyclicAdvance F.x F.zOffset := by
  let hx := (firstClockwiseNeighborOffset P d₁ d₂ d₃ F.x).val
  have hxdeg : 0 < vertexDegree P d₁ d₂ d₃ F.x := by
    have := F.highDegree F.x
    omega
  have hhx : 0 < hx := by
    simpa [hx] using firstClockwiseNeighborOffset_pos_of_degree_pos hxdeg
  dsimp [zOffset, hx]
  rw [show firstClockwiseNeighbor P d₁ d₂ d₃ F.x =
      cyclicRetreat F.x hx by rfl,
    cyclicRetreat_eq_advance_complement F.x hhx
      (firstClockwiseNeighborOffset P d₁ d₂ d₃ F.x).isLt]

theorem firstCounterclockwiseNeighbor_eq_uOffset
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃) :
    firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance F.x 3) =
      cyclicAdvance F.x F.uOffset := by
  dsimp [uOffset, secondGap, firstCounterclockwiseNeighbor]
  rw [cyclicAdvance_add]

private theorem row1B32Geometry_of_cyclic_offsets
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hConvex : CyclicStrictConvex P)
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    (base : Fin n) {u : ℕ} (hu : 3 < u) (hlast : u + 3 < n)
    (hxw : sqDist (P base) (P (cyclicAdvance base (u + 1))) ≤ d₂)
    (hxs : sqDist (P base) (P (cyclicAdvance base (u + 2))) = d₂)
    (htw : sqDist (P (cyclicAdvance base 3))
      (P (cyclicAdvance base (u + 1))) = d₂)
    (hts : sqDist (P (cyclicAdvance base 3))
      (P (cyclicAdvance base (u + 2))) = d₁) :
    Nonempty (Row1B32WordRealization P d₁ d₂ d₃) := by
  classical
  let X := base
  let V := cyclicAdvance base 1
  let T := cyclicAdvance base 3
  let W := cyclicAdvance base (u + 1)
  let S := cyclicAdvance base (u + 2)
  let leftArc := cyclicOpenInterval base 1 (u + 1)
  let rightArc := cyclicWrapInterval base (u + 2) 1
  have hInjective : Function.Injective P :=
    cyclic_strict_convex_injective hConvex (by omega)
  have hArcPartition : ∀ j, j ≠ V →
      j ∈ leftArc ∨ j = W ∨ j = S ∨ j ∈ rightArc := by
    intro j hjV
    let k := cyclicOffset base j
    have hk : k < n := by
      dsimp [k, cyclicOffset]
      exact (j - base).isLt
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    have hkV : k ≠ 1 := by
      intro hk1
      apply hjV
      rw [hjEq, hk1]
    by_cases hkW : k = u + 1
    · right; left
      rw [hjEq, hkW]
    by_cases hkS : k = u + 2
    · right; right; left
      rw [hjEq, hkS]
    by_cases hkLeft : 1 < k ∧ k < u + 1
    · left
      exact mem_cyclicOpenInterval.mpr hkLeft
    · right; right; right
      exact mem_cyclicWrapInterval.mpr (by omega)
  have hLeftHalfPlane : ∀ j ∈ leftArc,
      InLeftOpenHalfPlane (P X) (P V) (P j) := by
    intro j hj
    have hk := mem_cyclicOpenInterval.mp hj
    let k := cyclicOffset base j
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    rw [hjEq]
    simpa [X, V] using cyclic_inLeft_of_unwrapped_order hConvex base
      (a := 0) (b := 1) (k := k) (by omega) (by omega) (by
        dsimp [k, cyclicOffset]
        omega)
  have hRightHalfPlane : ∀ j ∈ rightArc,
      InLeftOpenHalfPlane (P V) (P T) (P j) := by
    intro j hj
    have hkCases := mem_cyclicWrapInterval.mp hj
    let k := cyclicOffset base j
    have hk : k < n := by
      dsimp [k, cyclicOffset]
      exact (j - base).isLt
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    rw [hjEq]
    rcases hkCases with hkHigh | hkLow
    · simpa [V, T] using cyclic_inLeft_of_unwrapped_order hConvex base
        (a := 1) (b := 3) (k := k) (by omega) (by omega) (by omega)
    · have h := cyclic_inLeft_of_unwrapped_order hConvex base
        (a := 1) (b := 3) (k := k + n) (by omega) (by omega) (by omega)
      rw [cyclicAdvance_period] at h
      simpa [V, T] using h
  have hLeftQuad : ∀ j ∈ leftArc,
      StrictConvexQuad (P V) (P j) (P S) (P X) := by
    intro j hj
    have hkData := mem_cyclicOpenInterval.mp hj
    let k := cyclicOffset base j
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    have h := cyclic_strict_convex_quad_unwrapped hConvex base
      (a := 1) (b := k) (c := u + 2) (d := n)
      (by omega) (by omega) (by omega) (by omega)
    have hperiod : cyclicAdvance base n = base := by
      simpa using cyclicAdvance_period base 0
    rw [hperiod] at h
    simpa [V, S, X, hjEq] using h
  have hRightQuad : ∀ j ∈ rightArc,
      StrictConvexQuad (P T) (P S) (P j) (P V) := by
    intro j hj
    have hkCases := mem_cyclicWrapInterval.mp hj
    let k := cyclicOffset base j
    have hk : k < n := by
      dsimp [k, cyclicOffset]
      exact (j - base).isLt
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    rcases hkCases with hkHigh | hkLow
    · change u + 2 < k at hkHigh
      have h := cyclic_strict_convex_quad_unwrapped hConvex base
        (a := 3) (b := u + 2) (c := k) (d := 1 + n)
        (by omega) (by omega) (by omega) (by omega)
      rw [show cyclicAdvance base (1 + n) = cyclicAdvance base 1 by
        simpa using cyclicAdvance_period base 1] at h
      simpa [T, S, V, hjEq] using h
    · have h := cyclic_strict_convex_quad_unwrapped hConvex base
        (a := 3) (b := u + 2) (c := k + n) (d := 1 + n)
        (by omega) (by omega) (by omega) (by omega)
      rw [cyclicAdvance_period base k,
        show cyclicAdvance base (1 + n) = cyclicAdvance base 1 by
          simpa using cyclicAdvance_period base 1] at h
      simpa [T, S, V, hjEq] using h
  have hCentralLeft : StrictConvexQuad (P V) (P W) (P S) (P X) := by
    have h := cyclic_strict_convex_quad_unwrapped hConvex base
      (a := 1) (b := u + 1) (c := u + 2) (d := n)
      (by omega) (by omega) (by omega) (by omega)
    rw [show cyclicAdvance base n = base by
      simpa using cyclicAdvance_period base 0] at h
    simpa [V, W, S, X] using h
  have hCentralRight : StrictConvexQuad (P T) (P W) (P S) (P V) := by
    have h := cyclic_strict_convex_quad_unwrapped hConvex base
      (a := 3) (b := u + 1) (c := u + 2) (d := 1 + n)
      (by omega) (by omega) (by omega) (by omega)
    rw [show cyclicAdvance base (1 + n) = cyclicAdvance base 1 by
      simpa using cyclicAdvance_period base 1] at h
    simpa [T, W, S, V] using h
  have hTerminal : StrictConvexQuad (P T) (P W) (P S) (P X) := by
    have h := cyclic_strict_convex_quad_unwrapped hConvex base
      (a := 3) (b := u + 1) (c := u + 2) (d := n)
      (by omega) (by omega) (by omega) (by omega)
    rw [show cyclicAdvance base n = base by
      simpa using cyclicAdvance_period base 0] at h
    simpa [T, W, S, X] using h
  have hShortLeft : ∀ j ∈ leftArc,
      StrictConvexQuad (P V) (P j) (P W) (P X) := by
    intro j hj
    have hkData := mem_cyclicOpenInterval.mp hj
    let k := cyclicOffset base j
    have hjEq : j = cyclicAdvance base k :=
      eq_cyclicAdvance_of_cyclicOffset_eq rfl
    have h := cyclic_strict_convex_quad_unwrapped hConvex base
      (a := 1) (b := k) (c := u + 1) (d := n)
      (by omega) (by omega) (by omega) (by omega)
    rw [show cyclicAdvance base n = base by
      simpa using cyclicAdvance_period base 0] at h
    simpa [V, W, X, hjEq] using h
  refine ⟨{
    pointsInjective := hInjective
    classes := hClasses
    x := X
    vertex := V
    t := T
    w := W
    s := S
    x_ne_vertex := by simpa [X, V] using (cyclicAdvance_ne_of_lt base
      (a := 0) (b := 1) (by omega) (by omega) (by omega))
    t_ne_vertex := by simpa [T, V] using (cyclicAdvance_ne_of_lt base
      (a := 3) (b := 1) (by omega) (by omega) (by omega))
    x_ne_t := by simpa [X, T] using (cyclicAdvance_ne_of_lt base
      (a := 0) (b := 3) (by omega) (by omega) (by omega))
    x_ne_w := by simpa [X, W] using (cyclicAdvance_ne_of_lt base
      (a := 0) (b := u + 1) (by omega) (by omega) (by omega))
    x_ne_s := by simpa [X, S] using (cyclicAdvance_ne_of_lt base
      (a := 0) (b := u + 2) (by omega) (by omega) (by omega))
    t_ne_w := by simpa [T, W] using (cyclicAdvance_ne_of_lt base
      (a := 3) (b := u + 1) (by omega) (by omega) (by omega))
    t_ne_s := by simpa [T, S] using (cyclicAdvance_ne_of_lt base
      (a := 3) (b := u + 2) (by omega) (by omega) (by omega))
    w_ne_s := by simpa [W, S] using (cyclicAdvance_ne_of_lt base
      (a := u + 1) (b := u + 2) (by omega) (by omega) (by omega))
    w_ne_vertex := by simpa [W, V] using (cyclicAdvance_ne_of_lt base
      (a := u + 1) (b := 1) (by omega) (by omega) (by omega))
    s_ne_vertex := by simpa [S, V] using (cyclicAdvance_ne_of_lt base
      (a := u + 2) (b := 1) (by omega) (by omega) (by omega))
    leftArc := leftArc
    rightArc := rightArc
    arcPartition := hArcPartition
    leftHalfPlane := hLeftHalfPlane
    left_x_ne := by simpa [leftArc, X] using
      (cyclicOpenInterval_center_ne_of_left base
        (e := 0) (a := 1) (b := u + 1) (by omega) (by omega))
    rightHalfPlane := hRightHalfPlane
    right_t_ne := by simpa [rightArc, T] using
      (cyclicWrapInterval_center_ne_of_between base
        (a := 1) (t := 3) (b := u + 2) (by omega) (by omega) (by omega))
    leftQuad := hLeftQuad
    rightQuad := hRightQuad
    centralLeftQuad := hCentralLeft
    centralRightQuad := hCentralRight
    terminalQuad := hTerminal
    shortLeftQuad := hShortLeft
    xw_le := by simpa [X, W] using hxw
    xs := by simpa [X, S] using hxs
    tw := by simpa [T, W] using htw
    ts := by simpa [T, S] using hts }⟩

/-- The canonical row-1 terminal word supplies exactly the raw terminal-cage
record used by `row1_B32_realization_degree_le_six`. -/
theorem row1_B32_raw_realization
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃)
    (hWord : F.RealizesCoverWord .row1_B32) :
    Nonempty (Row1B32WordRealization P d₁ d₂ d₃) := by
  classical
  rcases hWord with ⟨hRow, _hFirstOrder, _hSecondOrder, hRank⟩
  rcases hRow with ⟨hFirstRight, hFirstLeft, _hL, hM⟩
  have hSecondLeft : F.pair.second.leftMoves = 0 := by
    have hbudget := F.pair.second.coverBudget
    have houter := F.M_le_secondRight
    omega
  have hSecondRight : F.pair.second.rightMoves = 2 := by
    have hbudget := F.pair.second.coverBudget
    have houter := F.M_le_secondRight
    omega
  let X := F.x
  let V := cyclicAdvance F.x 1
  let T := cyclicAdvance F.x 3
  let U := cyclicAdvance F.x F.uOffset
  let W := cyclicAdvance F.x (F.uOffset + 1)
  let S := cyclicAdvance F.x (F.uOffset + 2)
  let Z := cyclicAdvance F.x (F.uOffset + 3)
  let leftArc := cyclicOpenInterval F.x 1 (F.uOffset + 1)
  let rightArc := cyclicWrapInterval F.x (F.uOffset + 2) 1
  have hn : 8 ≤ n := F.card_ge_eight
  have huPos : 3 < F.uOffset := by
    dsimp [uOffset]
    have := F.secondGap_pos
    omega
  have hzoff : F.zOffset = F.uOffset + 3 := by
    rw [F.zOffset_eq_uOffset_add, hM, hFirstLeft]
  have hlast : F.uOffset + 3 < n := by
    rw [← hzoff]
    exact F.zOffset_lt_card
  have hU :
      firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance F.x 3) = U := by
    simpa [U] using F.firstCounterclockwiseNeighbor_eq_uOffset
  have hZ : firstClockwiseNeighbor P d₁ d₂ d₃ F.x = Z := by
    rw [F.firstClockwiseNeighbor_eq_offset, hzoff]
  have hFirstTerminal :
      cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) 1 = S := by
    calc
      cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) 1 =
          cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x)
            F.pair.first.leftMoves := by rw [hFirstLeft]
      _ = cyclicAdvance
          (firstCounterclockwiseNeighbor P d₁ d₂ d₃
            (cyclicAdvance F.x 3)) F.M := F.outerLocalized
      _ = S := by rw [hU, hM, cyclicAdvance_add]
  have hSW : cyclicRetreat S 1 = W := by
    dsimp [S, W]
    simpa using cyclicRetreat_advance F.x
      (k := F.uOffset + 2) (m := 1) (by omega) (by omega)
  have hSecondPath :
      K3CoverSequence P (cyclicAdvance F.x 3)
        (firstCounterclockwiseNeighbor P d₁ d₂ d₃
          (cyclicAdvance F.x 3)) 0 2 := by
    simpa [hSecondLeft, hSecondRight] using F.pair.second.path
  have hLadder := right_right_cover_rank_ladder F.classes
    F.toUseSite.second_start_adjacent hSecondPath
  have hUseX : F.toUseSite.x = F.x := by
    unfold toUseSite erlvAtVertexUseSiteOfHighDegree
    rfl
  have hTW : sqDist (P T) (P W) = d₂ := by
    have h := hLadder.2.1
    rw [hUseX, hU] at h
    simpa [T, W, U, cyclicAdvance_add] using h
  have hTS : sqDist (P T) (P S) = d₁ := by
    have h := hLadder.2.2
    rw [hUseX, hU] at h
    simpa [T, S, U, cyclicAdvance_add] using h
  change F.firstStartSqDist = d₃ ∧ F.firstTerminalSqDist = d₂ at hRank
  have hXS : sqDist (P X) (P S) = d₂ := by
    have h := hRank.2
    dsimp only [firstTerminalSqDist] at h
    rw [hFirstLeft, hFirstRight, cyclicAdvance_zero, hFirstTerminal] at h
    simpa [X, sqDist_comm] using h
  have hXW : sqDist (P X) (P W) ≤ d₂ := by
    have hnot := F.pair.first.terminal.1
    unfold IsLeftCover at hnot
    have hle := le_of_not_gt hnot
    rw [hFirstLeft, hFirstRight, cyclicAdvance_zero, hFirstTerminal, hSW] at hle
    simpa [X, sqDist_comm, hXS] using hle
  exact row1B32Geometry_of_cyclic_offsets F.convex F.classes F.x
    huPos hlast hXW hXS hTW hTS

/-- Row 1 with first transition `d₂→d₁` is the direct full-two-rung
realization. -/
theorem row1_B21_raw_realization
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃)
    (hWord : F.RealizesCoverWord .row1_B21) :
    Nonempty (FullTwoRungGeometry P d₁ d₂ d₃) := by
  classical
  rcases hWord with ⟨hRow, _hFirstOrder, _hSecondOrder, hRank⟩
  rcases hRow with ⟨hFirstRight, hFirstLeft, _hL, hM⟩
  have hSecondLeft : F.pair.second.leftMoves = 0 := by
    have hbudget := F.pair.second.coverBudget
    have houter := F.M_le_secondRight
    omega
  have hSecondRight : F.pair.second.rightMoves = 2 := by
    have hbudget := F.pair.second.coverBudget
    have houter := F.M_le_secondRight
    omega
  have hn : 8 ≤ n := F.card_ge_eight
  have huPos : 3 < F.uOffset := by
    dsimp [uOffset]
    have := F.secondGap_pos
    omega
  have hzoff : F.zOffset = F.uOffset + 3 := by
    rw [F.zOffset_eq_uOffset_add, hM, hFirstLeft]
  have hlast : F.uOffset + 3 < n := by
    rw [← hzoff]
    exact F.zOffset_lt_card
  have hU :
      firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance F.x 3) =
        cyclicAdvance F.x F.uOffset :=
    F.firstCounterclockwiseNeighbor_eq_uOffset
  have hFirstTerminal :
      cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) 1 =
        cyclicAdvance F.x (F.uOffset + 2) := by
    calc
      cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) 1 =
          cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x)
            F.pair.first.leftMoves := by rw [hFirstLeft]
      _ = cyclicAdvance
          (firstCounterclockwiseNeighbor P d₁ d₂ d₃
            (cyclicAdvance F.x 3)) F.M := F.outerLocalized
      _ = cyclicAdvance F.x (F.uOffset + 2) := by
        rw [hU, hM, cyclicAdvance_add]
  have hSecondPath :
      K3CoverSequence P (cyclicAdvance F.x 3)
        (firstCounterclockwiseNeighbor P d₁ d₂ d₃
          (cyclicAdvance F.x 3)) 0 2 := by
    simpa [hSecondLeft, hSecondRight] using F.pair.second.path
  have hLadder := right_right_cover_rank_ladder F.classes
    F.toUseSite.second_start_adjacent hSecondPath
  have hUseX : F.toUseSite.x = F.x := by
    unfold toUseSite erlvAtVertexUseSiteOfHighDegree
    rfl
  have hTW : sqDist (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 1))) = d₂ := by
    have h := hLadder.2.1
    rw [hUseX, hU] at h
    simpa [cyclicAdvance_add] using h
  have hTS : sqDist (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 2))) = d₁ := by
    have h := hLadder.2.2
    rw [hUseX, hU] at h
    simpa [cyclicAdvance_add] using h
  change F.firstStartSqDist = d₂ ∧ F.firstTerminalSqDist = d₁ at hRank
  have hXS : sqDist (P F.x)
      (P (cyclicAdvance F.x (F.uOffset + 2))) = d₁ := by
    have h := hRank.2
    dsimp only [firstTerminalSqDist] at h
    rw [hFirstLeft, hFirstRight, cyclicAdvance_zero, hFirstTerminal] at h
    simpa [sqDist_comm] using h
  have hXR : sqDist (P F.x)
      (P (cyclicAdvance F.x (F.uOffset + 3))) = d₂ := by
    have h := hRank.1
    dsimp only [firstStartSqDist] at h
    rw [F.firstClockwiseNeighbor_eq_offset, hzoff] at h
    simpa [sqDist_comm] using h
  have hQuadSXΤW : StrictConvexQuad
      (P (cyclicAdvance F.x (F.uOffset + 2))) (P F.x)
      (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 1))) := by
    have h := cyclic_strict_convex_quad_unwrapped F.convex F.x
      (a := F.uOffset + 2) (b := n) (c := 3 + n)
      (d := F.uOffset + 1 + n)
      (by omega) (by omega) (by omega) (by omega)
    have hzero : cyclicAdvance F.x n = F.x := by
      simpa using cyclicAdvance_period F.x 0
    rw [hzero, cyclicAdvance_period, cyclicAdvance_period] at h
    simpa using h
  have hXW : sqDist (P F.x)
      (P (cyclicAdvance F.x (F.uOffset + 1))) = d₁ := by
    have hforce := red_blue_forcing_sqDist F.classes
      (a := cyclicAdvance F.x (F.uOffset + 2)) (b := F.x)
      (c := cyclicAdvance F.x 3)
      (d := cyclicAdvance F.x (F.uOffset + 1))
      (by
        simpa using cyclicAdvance_ne_of_lt F.x
          (a := F.uOffset + 2) (b := 3)
          (by omega) (by omega) (by omega))
      (by
        simpa using cyclicAdvance_ne_of_lt F.x
          (a := 0) (b := F.uOffset + 1)
          (by omega) (by omega) (by omega))
      hQuadSXΤW (by simpa [sqDist_comm] using hXS) hTW
    exact hforce.2
  have hQuadTSRX : StrictConvexQuad
      (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 2)))
      (P (cyclicAdvance F.x (F.uOffset + 3))) (P F.x) := by
    have h := cyclic_strict_convex_quad_unwrapped F.convex F.x
      (a := 3) (b := F.uOffset + 2) (c := F.uOffset + 3) (d := n)
      (by omega) (by omega) (by omega) (by omega)
    have hzero : cyclicAdvance F.x n = F.x := by
      simpa using cyclicAdvance_period F.x 0
    rw [hzero] at h
    simpa using h
  have hTR : sqDist (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 3))) = d₁ := by
    have hforce := red_blue_forcing_sqDist F.classes
      (a := cyclicAdvance F.x 3)
      (b := cyclicAdvance F.x (F.uOffset + 2))
      (c := cyclicAdvance F.x (F.uOffset + 3)) (d := F.x)
      (by
        simpa using cyclicAdvance_ne_of_lt F.x
          (a := 3) (b := F.uOffset + 3)
          (by omega) (by omega) (by omega))
      (by
        simpa using cyclicAdvance_ne_of_lt F.x
          (a := F.uOffset + 2) (b := 0)
          (by omega) (by omega) (by omega))
      hQuadTSRX hTS (by simpa [sqDist_comm] using hXR)
    exact hforce.1
  exact fullTwoRungGeometry_of_cyclic_offsets F.convex F.classes F.x
    (e := 0) (v := 1) (t := 3) (w := F.uOffset + 1)
    (s := F.uOffset + 2) (r := F.uOffset + 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simpa using hXS) hTS (by simpa using hXW) hTW
    (by simpa using hXR) hTR

/-- Row 1 with first transition `d₃→d₁` is the direct
one-penultimate realization. -/
theorem row1_B31_raw_realization
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃)
    (hWord : F.RealizesCoverWord .row1_B31) :
    Nonempty (OnePenultimateWordGeometry P d₁ d₂ d₃) := by
  rcases hWord with ⟨hRow, _hFirstOrder, _hSecondOrder, hRank⟩
  rcases hRow with ⟨hFirstRight, hFirstLeft, _hL, hM⟩
  have hSecondLeft : F.pair.second.leftMoves = 0 := by
    have hbudget := F.pair.second.coverBudget
    have houter := F.M_le_secondRight
    omega
  have hSecondRight : F.pair.second.rightMoves = 2 := by
    have hbudget := F.pair.second.coverBudget
    have houter := F.M_le_secondRight
    omega
  have huPos : 3 < F.uOffset := by
    dsimp [uOffset]
    have := F.secondGap_pos
    omega
  have hzoff : F.zOffset = F.uOffset + 3 := by
    rw [F.zOffset_eq_uOffset_add, hM, hFirstLeft]
  have hlast : F.uOffset + 3 < n := by
    rw [← hzoff]
    exact F.zOffset_lt_card
  have hU :
      firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance F.x 3) =
        cyclicAdvance F.x F.uOffset :=
    F.firstCounterclockwiseNeighbor_eq_uOffset
  have hFirstTerminal :
      cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) 1 =
        cyclicAdvance F.x (F.uOffset + 2) := by
    calc
      cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) 1 =
          cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x)
            F.pair.first.leftMoves := by rw [hFirstLeft]
      _ = cyclicAdvance
          (firstCounterclockwiseNeighbor P d₁ d₂ d₃
            (cyclicAdvance F.x 3)) F.M := F.outerLocalized
      _ = cyclicAdvance F.x (F.uOffset + 2) := by
        rw [hU, hM, cyclicAdvance_add]
  have hSecondPath :
      K3CoverSequence P (cyclicAdvance F.x 3)
        (firstCounterclockwiseNeighbor P d₁ d₂ d₃
          (cyclicAdvance F.x 3)) 0 2 := by
    simpa [hSecondLeft, hSecondRight] using F.pair.second.path
  have hLadder := right_right_cover_rank_ladder F.classes
    F.toUseSite.second_start_adjacent hSecondPath
  have hUseX : F.toUseSite.x = F.x := by
    unfold toUseSite erlvAtVertexUseSiteOfHighDegree
    rfl
  have hTW : sqDist (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 1))) = d₂ := by
    have h := hLadder.2.1
    rw [hUseX, hU] at h
    simpa [cyclicAdvance_add] using h
  have hTS : sqDist (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 2))) = d₁ := by
    have h := hLadder.2.2
    rw [hUseX, hU] at h
    simpa [cyclicAdvance_add] using h
  change F.firstStartSqDist = d₃ ∧ F.firstTerminalSqDist = d₁ at hRank
  have hXS : sqDist (P F.x)
      (P (cyclicAdvance F.x (F.uOffset + 2))) = d₁ := by
    have h := hRank.2
    dsimp only [firstTerminalSqDist] at h
    rw [hFirstLeft, hFirstRight, cyclicAdvance_zero, hFirstTerminal] at h
    simpa [sqDist_comm] using h
  exact onePenultimateGeometry_of_cyclic_offsets F.convex F.classes F.x
    (e := 0) (v := 1) (t := 3) (p := F.uOffset + 1)
    (s := F.uOffset + 2)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simpa using hXS) hTS hTW

/-- The row-2 left-first word is the direct one-penultimate geometry based
at the first lower endpoint. -/
theorem row2_BA_raw_realization
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃)
    (hWord : F.RealizesCoverWord .row2_BA) :
    Nonempty (OnePenultimateWordGeometry P d₁ d₂ d₃) := by
  rcases hWord with ⟨hRow, _hFirstOrder, _hSecondOrder⟩
  rcases hRow with ⟨hFirstRight, hFirstLeft, _hL, hM⟩
  have hSecondLeft : F.pair.second.leftMoves = 0 := by
    have hbudget := F.pair.second.coverBudget
    have houter := F.M_le_secondRight
    omega
  have hSecondRight : F.pair.second.rightMoves = 2 := by
    have hbudget := F.pair.second.coverBudget
    have houter := F.M_le_secondRight
    omega
  have huPos : 3 < F.uOffset := by
    dsimp [uOffset]
    have := F.secondGap_pos
    omega
  have hzoff : F.zOffset = F.uOffset + 3 := by
    rw [F.zOffset_eq_uOffset_add, hM, hFirstLeft]
  have hlast : F.uOffset + 3 < n := by
    rw [← hzoff]
    exact F.zOffset_lt_card
  have hU :
      firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance F.x 3) =
        cyclicAdvance F.x F.uOffset :=
    F.firstCounterclockwiseNeighbor_eq_uOffset
  have hFirstTerminal :
      cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) 1 =
        cyclicAdvance F.x (F.uOffset + 2) := by
    calc
      cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) 1 =
          cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x)
            F.pair.first.leftMoves := by rw [hFirstLeft]
      _ = cyclicAdvance
          (firstCounterclockwiseNeighbor P d₁ d₂ d₃
            (cyclicAdvance F.x 3)) F.M := F.outerLocalized
      _ = cyclicAdvance F.x (F.uOffset + 2) := by
        rw [hU, hM, cyclicAdvance_add]
  have hFirstStart : TopThreeAdjacent P d₁ d₂ d₃
      (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) F.x := by
    apply topThreeAdjacent_symm
    apply firstClockwiseNeighbor_adjacent_of_degree_pos
    have := F.highDegree F.x
    omega
  have hFirstPath : K3CoverSequence P
      (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) F.x 1 1 := by
    simpa [hFirstLeft, hFirstRight] using F.pair.first.path
  have hFirstEnds := K3CoverSequence.two_cover_rank_endpoints hFirstPath
    F.classes hFirstStart (by
      simpa [hFirstLeft, hFirstRight] using F.pair.first.adjacent) (by omega)
  have hPS : sqDist (P (cyclicAdvance F.x 1))
      (P (cyclicAdvance F.x (F.uOffset + 2))) = d₁ := by
    have h := hFirstEnds.2
    rw [hFirstTerminal] at h
    simpa [sqDist_comm] using h
  have hSecondPath :
      K3CoverSequence P (cyclicAdvance F.x 3)
        (firstCounterclockwiseNeighbor P d₁ d₂ d₃
          (cyclicAdvance F.x 3)) 0 2 := by
    simpa [hSecondLeft, hSecondRight] using F.pair.second.path
  have hLadder := right_right_cover_rank_ladder F.classes
    F.toUseSite.second_start_adjacent hSecondPath
  have hUseX : F.toUseSite.x = F.x := by
    unfold toUseSite erlvAtVertexUseSiteOfHighDegree
    rfl
  have hTW : sqDist (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 1))) = d₂ := by
    have h := hLadder.2.1
    rw [hUseX, hU] at h
    simpa [cyclicAdvance_add] using h
  have hTS : sqDist (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 2))) = d₁ := by
    have h := hLadder.2.2
    rw [hUseX, hU] at h
    simpa [cyclicAdvance_add] using h
  exact onePenultimateGeometry_of_cyclic_offsets F.convex F.classes F.x
    (e := 1) (v := 2) (t := 3) (p := F.uOffset + 1)
    (s := F.uOffset + 2)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    hPS hTS hTW

/-- The row-2 right-first word supplies the second full-two-rung
realization. -/
theorem row2_AB_raw_realization
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃)
    (hWord : F.RealizesCoverWord .row2_AB) :
    Nonempty (FullTwoRungGeometry P d₁ d₂ d₃) := by
  classical
  rcases hWord with ⟨hRow, hFirstOrder, _hSecondOrder⟩
  rcases hRow with ⟨hFirstRight, hFirstLeft, _hL, hM⟩
  have hSecondLeft : F.pair.second.leftMoves = 0 := by
    have hbudget := F.pair.second.coverBudget
    have houter := F.M_le_secondRight
    omega
  have hSecondRight : F.pair.second.rightMoves = 2 := by
    have hbudget := F.pair.second.coverBudget
    have houter := F.M_le_secondRight
    omega
  have huPos : 3 < F.uOffset := by
    dsimp [uOffset]
    have := F.secondGap_pos
    omega
  have hzoff : F.zOffset = F.uOffset + 3 := by
    rw [F.zOffset_eq_uOffset_add, hM, hFirstLeft]
  have hlast : F.uOffset + 3 < n := by
    rw [← hzoff]
    exact F.zOffset_lt_card
  have hU :
      firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance F.x 3) =
        cyclicAdvance F.x F.uOffset :=
    F.firstCounterclockwiseNeighbor_eq_uOffset
  have hZ : firstClockwiseNeighbor P d₁ d₂ d₃ F.x =
      cyclicAdvance F.x (F.uOffset + 3) := by
    rw [F.firstClockwiseNeighbor_eq_offset, hzoff]
  have hFirstTerminal :
      cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) 1 =
        cyclicAdvance F.x (F.uOffset + 2) := by
    calc
      cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) 1 =
          cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x)
            F.pair.first.leftMoves := by rw [hFirstLeft]
      _ = cyclicAdvance
          (firstCounterclockwiseNeighbor P d₁ d₂ d₃
            (cyclicAdvance F.x 3)) F.M := F.outerLocalized
      _ = cyclicAdvance F.x (F.uOffset + 2) := by
        rw [hU, hM, cyclicAdvance_add]
  have hFirstStart : TopThreeAdjacent P d₁ d₂ d₃
      (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) F.x := by
    apply topThreeAdjacent_symm
    apply firstClockwiseNeighbor_adjacent_of_degree_pos
    have := F.highDegree F.x
    omega
  have hFirstPath : K3CoverSequence P
      (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) F.x 1 1 := by
    simpa [hFirstLeft, hFirstRight] using F.pair.first.path
  have hFirstLadder := K3CoverSequence.right_left_cover_rank_ladder
    F.classes hFirstStart hFirstPath (by
      simpa [hFirstLeft, hFirstRight] using hFirstOrder)
  have hPR : sqDist (P (cyclicAdvance F.x 1))
      (P (cyclicAdvance F.x (F.uOffset + 3))) = d₂ := by
    have h := hFirstLadder.2.1
    rw [hZ] at h
    simpa [sqDist_comm] using h
  have hPS : sqDist (P (cyclicAdvance F.x 1))
      (P (cyclicAdvance F.x (F.uOffset + 2))) = d₁ := by
    have h := hFirstLadder.2.2
    rw [hFirstTerminal] at h
    simpa [sqDist_comm] using h
  have hSecondPath :
      K3CoverSequence P (cyclicAdvance F.x 3)
        (firstCounterclockwiseNeighbor P d₁ d₂ d₃
          (cyclicAdvance F.x 3)) 0 2 := by
    simpa [hSecondLeft, hSecondRight] using F.pair.second.path
  have hLadder := right_right_cover_rank_ladder F.classes
    F.toUseSite.second_start_adjacent hSecondPath
  have hUseX : F.toUseSite.x = F.x := by
    unfold toUseSite erlvAtVertexUseSiteOfHighDegree
    rfl
  have hTW : sqDist (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 1))) = d₂ := by
    have h := hLadder.2.1
    rw [hUseX, hU] at h
    simpa [cyclicAdvance_add] using h
  have hTS : sqDist (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 2))) = d₁ := by
    have h := hLadder.2.2
    rw [hUseX, hU] at h
    simpa [cyclicAdvance_add] using h
  have hQuadSPTW : StrictConvexQuad
      (P (cyclicAdvance F.x (F.uOffset + 2)))
      (P (cyclicAdvance F.x 1)) (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 1))) := by
    have h := cyclic_strict_convex_quad_unwrapped F.convex F.x
      (a := F.uOffset + 2) (b := 1 + n) (c := 3 + n)
      (d := F.uOffset + 1 + n)
      (by omega) (by omega) (by omega) (by omega)
    rw [cyclicAdvance_period, cyclicAdvance_period, cyclicAdvance_period] at h
    simpa using h
  have hPW : sqDist (P (cyclicAdvance F.x 1))
      (P (cyclicAdvance F.x (F.uOffset + 1))) = d₁ := by
    have hforce := red_blue_forcing_sqDist F.classes
      (a := cyclicAdvance F.x (F.uOffset + 2))
      (b := cyclicAdvance F.x 1) (c := cyclicAdvance F.x 3)
      (d := cyclicAdvance F.x (F.uOffset + 1))
      (by
        simpa using cyclicAdvance_ne_of_lt F.x
          (a := F.uOffset + 2) (b := 3)
          (by omega) (by omega) (by omega))
      (by
        simpa using cyclicAdvance_ne_of_lt F.x
          (a := 1) (b := F.uOffset + 1)
          (by omega) (by omega) (by omega))
      hQuadSPTW (by simpa [sqDist_comm] using hPS) hTW
    exact hforce.2
  have hQuadTSRP : StrictConvexQuad
      (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 2)))
      (P (cyclicAdvance F.x (F.uOffset + 3)))
      (P (cyclicAdvance F.x 1)) := by
    have h := cyclic_strict_convex_quad_unwrapped F.convex F.x
      (a := 3) (b := F.uOffset + 2) (c := F.uOffset + 3) (d := 1 + n)
      (by omega) (by omega) (by omega) (by omega)
    rw [cyclicAdvance_period] at h
    simpa using h
  have hTR : sqDist (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 3))) = d₁ := by
    have hforce := red_blue_forcing_sqDist F.classes
      (a := cyclicAdvance F.x 3)
      (b := cyclicAdvance F.x (F.uOffset + 2))
      (c := cyclicAdvance F.x (F.uOffset + 3))
      (d := cyclicAdvance F.x 1)
      (by
        simpa using cyclicAdvance_ne_of_lt F.x
          (a := 3) (b := F.uOffset + 3)
          (by omega) (by omega) (by omega))
      (by
        simpa using cyclicAdvance_ne_of_lt F.x
          (a := F.uOffset + 2) (b := 1)
          (by omega) (by omega) (by omega))
      hQuadTSRP hTS (by simpa [sqDist_comm] using hPR)
    exact hforce.1
  exact fullTwoRungGeometry_of_cyclic_offsets F.convex F.classes F.x
    (e := 1) (v := 2) (t := 3) (w := F.uOffset + 1)
    (s := F.uOffset + 2) (r := F.uOffset + 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hPS hTS hPW hTW hPR hTR

/-- The common `BB/DD` geometry in rows 3 and 5 is a direct full-two-rung
record. -/
theorem double_double_raw_realization
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃)
    (hFirstRight : F.pair.first.rightMoves = 0)
    (hFirstLeft : F.pair.first.leftMoves = 2) (hM : F.M = 2)
    (hSecondLeft : F.pair.second.leftMoves = 0)
    (hSecondRight : F.pair.second.rightMoves = 2) :
    Nonempty (FullTwoRungGeometry P d₁ d₂ d₃) := by
  classical
  have huPos : 3 < F.uOffset := by
    dsimp [uOffset]
    have := F.secondGap_pos
    omega
  have hzoff : F.zOffset = F.uOffset + 4 := by
    rw [F.zOffset_eq_uOffset_add, hM, hFirstLeft]
  have hlast : F.uOffset + 4 < n := by
    rw [← hzoff]
    exact F.zOffset_lt_card
  have hU :
      firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance F.x 3) =
        cyclicAdvance F.x F.uOffset :=
    F.firstCounterclockwiseNeighbor_eq_uOffset
  have hZ : firstClockwiseNeighbor P d₁ d₂ d₃ F.x =
      cyclicAdvance F.x (F.uOffset + 4) := by
    rw [F.firstClockwiseNeighbor_eq_offset, hzoff]
  have hZR : cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) 1 =
      cyclicAdvance F.x (F.uOffset + 3) := by
    rw [hZ]
    simpa using cyclicRetreat_advance F.x
      (k := F.uOffset + 4) (m := 1) (by omega) (by omega)
  have hZS : cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) 2 =
      cyclicAdvance F.x (F.uOffset + 2) := by
    rw [hZ]
    simpa using cyclicRetreat_advance F.x
      (k := F.uOffset + 4) (m := 2) (by omega) (by omega)
  have hFirstStart : TopThreeAdjacent P d₁ d₂ d₃
      (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) F.x := by
    apply topThreeAdjacent_symm
    apply firstClockwiseNeighbor_adjacent_of_degree_pos
    have := F.highDegree F.x
    omega
  have hFirstPath : K3CoverSequence P
      (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) F.x 2 0 := by
    simpa [hFirstLeft, hFirstRight] using F.pair.first.path
  have hFirstLadder := left_left_cover_rank_ladder F.classes
    hFirstStart hFirstPath
  have hXR : sqDist (P F.x)
      (P (cyclicAdvance F.x (F.uOffset + 3))) = d₂ := by
    have h := hFirstLadder.2.1
    rw [hZR] at h
    simpa [sqDist_comm] using h
  have hXS : sqDist (P F.x)
      (P (cyclicAdvance F.x (F.uOffset + 2))) = d₁ := by
    have h := hFirstLadder.2.2
    rw [hZS] at h
    simpa [sqDist_comm] using h
  have hSecondPath : K3CoverSequence P (cyclicAdvance F.x 3)
      (firstCounterclockwiseNeighbor P d₁ d₂ d₃
        (cyclicAdvance F.x 3)) 0 2 := by
    simpa [hSecondLeft, hSecondRight] using F.pair.second.path
  have hSecondLadder := right_right_cover_rank_ladder F.classes
    F.toUseSite.second_start_adjacent hSecondPath
  have hUseX : F.toUseSite.x = F.x := by
    unfold toUseSite erlvAtVertexUseSiteOfHighDegree
    rfl
  have hTW : sqDist (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 1))) = d₂ := by
    have h := hSecondLadder.2.1
    rw [hUseX, hU] at h
    simpa [cyclicAdvance_add] using h
  have hTS : sqDist (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 2))) = d₁ := by
    have h := hSecondLadder.2.2
    rw [hUseX, hU] at h
    simpa [cyclicAdvance_add] using h
  have hQuadSXTW : StrictConvexQuad
      (P (cyclicAdvance F.x (F.uOffset + 2))) (P F.x)
      (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 1))) := by
    have h := cyclic_strict_convex_quad_unwrapped F.convex F.x
      (a := F.uOffset + 2) (b := n) (c := 3 + n)
      (d := F.uOffset + 1 + n)
      (by omega) (by omega) (by omega) (by omega)
    have hzero : cyclicAdvance F.x n = F.x := by
      simpa using cyclicAdvance_period F.x 0
    rw [hzero, cyclicAdvance_period, cyclicAdvance_period] at h
    simpa using h
  have hXW : sqDist (P F.x)
      (P (cyclicAdvance F.x (F.uOffset + 1))) = d₁ := by
    have hforce := red_blue_forcing_sqDist F.classes
      (a := cyclicAdvance F.x (F.uOffset + 2)) (b := F.x)
      (c := cyclicAdvance F.x 3)
      (d := cyclicAdvance F.x (F.uOffset + 1))
      (by
        simpa using cyclicAdvance_ne_of_lt F.x
          (a := F.uOffset + 2) (b := 3)
          (by omega) (by omega) (by omega))
      (by
        simpa using cyclicAdvance_ne_of_lt F.x
          (a := 0) (b := F.uOffset + 1)
          (by omega) (by omega) (by omega))
      hQuadSXTW (by simpa [sqDist_comm] using hXS) hTW
    exact hforce.2
  have hQuadTSRX : StrictConvexQuad
      (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 2)))
      (P (cyclicAdvance F.x (F.uOffset + 3))) (P F.x) := by
    have h := cyclic_strict_convex_quad_unwrapped F.convex F.x
      (a := 3) (b := F.uOffset + 2) (c := F.uOffset + 3) (d := n)
      (by omega) (by omega) (by omega) (by omega)
    have hzero : cyclicAdvance F.x n = F.x := by
      simpa using cyclicAdvance_period F.x 0
    rw [hzero] at h
    simpa using h
  have hTR : sqDist (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 3))) = d₁ := by
    have hforce := red_blue_forcing_sqDist F.classes
      (a := cyclicAdvance F.x 3)
      (b := cyclicAdvance F.x (F.uOffset + 2))
      (c := cyclicAdvance F.x (F.uOffset + 3)) (d := F.x)
      (by
        simpa using cyclicAdvance_ne_of_lt F.x
          (a := 3) (b := F.uOffset + 3)
          (by omega) (by omega) (by omega))
      (by
        simpa using cyclicAdvance_ne_of_lt F.x
          (a := F.uOffset + 2) (b := 0)
          (by omega) (by omega) (by omega))
      hQuadTSRX hTS (by simpa [sqDist_comm] using hXR)
    exact hforce.1
  exact fullTwoRungGeometry_of_cyclic_offsets F.convex F.classes F.x
    (e := 0) (v := 1) (t := 3) (w := F.uOffset + 1)
    (s := F.uOffset + 2) (r := F.uOffset + 3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simpa using hXS) hTS (by simpa using hXW) hTW
    (by simpa using hXR) hTR

theorem row3_BB_DD_raw_realization
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃)
    (hWord : F.RealizesCoverWord .row3_BB_DD) :
    Nonempty (FullTwoRungGeometry P d₁ d₂ d₃) := by
  rcases hWord with ⟨hRow, _hFirstOrder, _hSecondOrder⟩
  rcases hRow with ⟨hFirstRight, hFirstLeft, _hL, hM⟩
  have hSecondLeft : F.pair.second.leftMoves = 0 := by
    have hbudget := F.pair.second.coverBudget
    have houter := F.M_le_secondRight
    omega
  have hSecondRight : F.pair.second.rightMoves = 2 := by
    have hbudget := F.pair.second.coverBudget
    have houter := F.M_le_secondRight
    omega
  exact F.double_double_raw_realization hFirstRight hFirstLeft hM
    hSecondLeft hSecondRight

theorem row5_BB_DD_raw_realization
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃)
    (hWord : F.RealizesCoverWord .row5_BB_DD) :
    Nonempty (FullTwoRungGeometry P d₁ d₂ d₃) := by
  rcases hWord with ⟨hRow, _hFirstOrder, _hSecondOrder⟩
  rcases hRow with ⟨hFirstRight, hFirstLeft, _hL, hM⟩
  have hSecondLeft : F.pair.second.leftMoves = 0 := by
    have hbudget := F.pair.second.coverBudget
    have houter := F.M_le_secondRight
    omega
  have hSecondRight : F.pair.second.rightMoves = 2 := by
    have hbudget := F.pair.second.coverBudget
    have houter := F.M_le_secondRight
    omega
  exact F.double_double_raw_realization hFirstRight hFirstLeft hM
    hSecondLeft hSecondRight

/-- Common direct row-4 full-two-rung adapter.  The second diameter center
is either `x+3` (`D21`) or `x+2` (`CD`). -/
theorem row4_full_raw_realization
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃)
    (hFirstRight : F.pair.first.rightMoves = 0)
    (hFirstLeft : F.pair.first.leftMoves = 2) (hM : F.M = 1)
    (tOffset : ℕ) (htLower : 1 < tOffset) (htUpper : tOffset ≤ 3)
    (hTU : sqDist (P (cyclicAdvance F.x tOffset))
      (P (cyclicAdvance F.x F.uOffset)) = d₂)
    (hTS : sqDist (P (cyclicAdvance F.x tOffset))
      (P (cyclicAdvance F.x (F.uOffset + 1))) = d₁) :
    Nonempty (FullTwoRungGeometry P d₁ d₂ d₃) := by
  classical
  have huPos : 3 < F.uOffset := by
    dsimp [uOffset]
    have := F.secondGap_pos
    omega
  have hzoff : F.zOffset = F.uOffset + 3 := by
    rw [F.zOffset_eq_uOffset_add, hM, hFirstLeft]
  have hlast : F.uOffset + 3 < n := by
    rw [← hzoff]
    exact F.zOffset_lt_card
  have hZ : firstClockwiseNeighbor P d₁ d₂ d₃ F.x =
      cyclicAdvance F.x (F.uOffset + 3) := by
    rw [F.firstClockwiseNeighbor_eq_offset, hzoff]
  have hZR : cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) 1 =
      cyclicAdvance F.x (F.uOffset + 2) := by
    rw [hZ]
    simpa using cyclicRetreat_advance F.x
      (k := F.uOffset + 3) (m := 1) (by omega) (by omega)
  have hZS : cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) 2 =
      cyclicAdvance F.x (F.uOffset + 1) := by
    rw [hZ]
    simpa using cyclicRetreat_advance F.x
      (k := F.uOffset + 3) (m := 2) (by omega) (by omega)
  have hFirstStart : TopThreeAdjacent P d₁ d₂ d₃
      (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) F.x := by
    apply topThreeAdjacent_symm
    apply firstClockwiseNeighbor_adjacent_of_degree_pos
    have := F.highDegree F.x
    omega
  have hFirstPath : K3CoverSequence P
      (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) F.x 2 0 := by
    simpa [hFirstLeft, hFirstRight] using F.pair.first.path
  have hFirstLadder := left_left_cover_rank_ladder F.classes
    hFirstStart hFirstPath
  have hXR : sqDist (P F.x)
      (P (cyclicAdvance F.x (F.uOffset + 2))) = d₂ := by
    have h := hFirstLadder.2.1
    rw [hZR] at h
    simpa [sqDist_comm] using h
  have hXS : sqDist (P F.x)
      (P (cyclicAdvance F.x (F.uOffset + 1))) = d₁ := by
    have h := hFirstLadder.2.2
    rw [hZS] at h
    simpa [sqDist_comm] using h
  have hQuadSXTU : StrictConvexQuad
      (P (cyclicAdvance F.x (F.uOffset + 1))) (P F.x)
      (P (cyclicAdvance F.x tOffset))
      (P (cyclicAdvance F.x F.uOffset)) := by
    have h := cyclic_strict_convex_quad_unwrapped F.convex F.x
      (a := F.uOffset + 1) (b := n) (c := tOffset + n)
      (d := F.uOffset + n)
      (by omega) (by omega) (by omega) (by omega)
    have hzero : cyclicAdvance F.x n = F.x := by
      simpa using cyclicAdvance_period F.x 0
    rw [hzero, cyclicAdvance_period, cyclicAdvance_period] at h
    simpa using h
  have hXU : sqDist (P F.x)
      (P (cyclicAdvance F.x F.uOffset)) = d₁ := by
    have hforce := red_blue_forcing_sqDist F.classes
      (a := cyclicAdvance F.x (F.uOffset + 1)) (b := F.x)
      (c := cyclicAdvance F.x tOffset)
      (d := cyclicAdvance F.x F.uOffset)
      (by
        simpa using cyclicAdvance_ne_of_lt F.x
          (a := F.uOffset + 1) (b := tOffset)
          (by omega) (by omega) (by omega))
      (by
        simpa using cyclicAdvance_ne_of_lt F.x
          (a := 0) (b := F.uOffset)
          (by omega) (by omega) (by omega))
      hQuadSXTU (by simpa [sqDist_comm] using hXS) hTU
    exact hforce.2
  have hQuadTSRX : StrictConvexQuad
      (P (cyclicAdvance F.x tOffset))
      (P (cyclicAdvance F.x (F.uOffset + 1)))
      (P (cyclicAdvance F.x (F.uOffset + 2))) (P F.x) := by
    have h := cyclic_strict_convex_quad_unwrapped F.convex F.x
      (a := tOffset) (b := F.uOffset + 1) (c := F.uOffset + 2) (d := n)
      (by omega) (by omega) (by omega) (by omega)
    have hzero : cyclicAdvance F.x n = F.x := by
      simpa using cyclicAdvance_period F.x 0
    rw [hzero] at h
    simpa using h
  have hTR : sqDist (P (cyclicAdvance F.x tOffset))
      (P (cyclicAdvance F.x (F.uOffset + 2))) = d₁ := by
    have hforce := red_blue_forcing_sqDist F.classes
      (a := cyclicAdvance F.x tOffset)
      (b := cyclicAdvance F.x (F.uOffset + 1))
      (c := cyclicAdvance F.x (F.uOffset + 2)) (d := F.x)
      (by
        simpa using cyclicAdvance_ne_of_lt F.x
          (a := tOffset) (b := F.uOffset + 2)
          (by omega) (by omega) (by omega))
      (by
        simpa using cyclicAdvance_ne_of_lt F.x
          (a := F.uOffset + 1) (b := 0)
          (by omega) (by omega) (by omega))
      hQuadTSRX hTS (by simpa [sqDist_comm] using hXR)
    exact hforce.1
  exact fullTwoRungGeometry_of_cyclic_offsets F.convex F.classes F.x
    (e := 0) (v := 1) (t := tOffset) (w := F.uOffset)
    (s := F.uOffset + 1) (r := F.uOffset + 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simpa using hXS) hTS (by simpa using hXU) hTU
    (by simpa using hXR) hTR

theorem row4_D21_raw_realization
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃)
    (hWord : F.RealizesCoverWord .row4_D21) :
    Nonempty (FullTwoRungGeometry P d₁ d₂ d₃) := by
  rcases hWord with
    ⟨hRow, _hFirstOrder, hSecondLeft, hSecondRight, _hSecondOrder, hRank⟩
  rcases hRow with ⟨hFirstRight, hFirstLeft, _hL, hM⟩
  have huPos : 3 < F.uOffset := by
    dsimp [uOffset]
    have := F.secondGap_pos
    omega
  have hlast : F.uOffset + 3 < n := by
    have hzoff : F.zOffset = F.uOffset + 3 := by
      rw [F.zOffset_eq_uOffset_add, hM, hFirstLeft]
    rw [← hzoff]
    exact F.zOffset_lt_card
  have hU := F.firstCounterclockwiseNeighbor_eq_uOffset
  change F.secondStartSqDist = d₂ ∧ F.secondTerminalSqDist = d₁ at hRank
  have hTU : sqDist (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x F.uOffset)) = d₂ := by
    have h := hRank.1
    dsimp only [secondStartSqDist] at h
    rw [hU] at h
    exact h
  have hTS : sqDist (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 1))) = d₁ := by
    have h := hRank.2
    dsimp only [secondTerminalSqDist] at h
    rw [hSecondLeft, hSecondRight, cyclicRetreat_zero, hU,
      cyclicAdvance_add] at h
    simpa using h
  exact F.row4_full_raw_realization hFirstRight hFirstLeft hM 3
    (by omega) (by omega) hTU hTS

theorem row4_CD_raw_realization
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃)
    (hWord : F.RealizesCoverWord .row4_CD) :
    Nonempty (FullTwoRungGeometry P d₁ d₂ d₃) := by
  rcases hWord with
    ⟨hRow, _hFirstOrder, hSecondLeft, hSecondRight, hSecondOrder⟩
  rcases hRow with ⟨hFirstRight, hFirstLeft, _hL, hM⟩
  have huPos : 3 < F.uOffset := by
    dsimp [uOffset]
    have := F.secondGap_pos
    omega
  have hlast : F.uOffset + 3 < n := by
    have hzoff : F.zOffset = F.uOffset + 3 := by
      rw [F.zOffset_eq_uOffset_add, hM, hFirstLeft]
    rw [← hzoff]
    exact F.zOffset_lt_card
  have hU := F.firstCounterclockwiseNeighbor_eq_uOffset
  have hSecondStart : TopThreeAdjacent P d₁ d₂ d₃
      (cyclicAdvance F.x 3)
      (firstCounterclockwiseNeighbor P d₁ d₂ d₃
        (cyclicAdvance F.x 3)) := by
    apply firstCounterclockwiseNeighbor_adjacent_of_degree_pos
    have := F.highDegree (cyclicAdvance F.x 3)
    omega
  have hSecondPath : K3CoverSequence P (cyclicAdvance F.x 3)
      (firstCounterclockwiseNeighbor P d₁ d₂ d₃
        (cyclicAdvance F.x 3)) 1 1 := by
    simpa [hSecondLeft, hSecondRight] using F.pair.second.path
  have hLadder := K3CoverSequence.left_right_cover_rank_ladder
    F.classes hSecondStart hSecondPath (by
      simpa [hSecondLeft, hSecondRight] using hSecondOrder)
  have hQU : sqDist (P (cyclicAdvance F.x 2))
      (P (cyclicAdvance F.x F.uOffset)) = d₂ := by
    have h := hLadder.2.1
    rw [hU] at h
    have hret : cyclicRetreat (cyclicAdvance F.x 3) 1 =
        cyclicAdvance F.x 2 := by
      simpa using cyclicRetreat_advance F.x
        (k := 3) (m := 1) (by omega) (by omega)
    rw [hret] at h
    exact h
  have hQS : sqDist (P (cyclicAdvance F.x 2))
      (P (cyclicAdvance F.x (F.uOffset + 1))) = d₁ := by
    have h := hLadder.2.2
    rw [hU, cyclicAdvance_add] at h
    have hret : cyclicRetreat (cyclicAdvance F.x 3) 1 =
        cyclicAdvance F.x 2 := by
      simpa using cyclicRetreat_advance F.x
        (k := 3) (m := 1) (by omega) (by omega)
    rw [hret] at h
    simpa using h
  exact F.row4_full_raw_realization hFirstRight hFirstLeft hM 2
    (by omega) (by omega) hQU hQS

/-- The first double-left ladder shared by every row-4 word. -/
theorem row4_first_ladder_data
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃)
    (hFirstRight : F.pair.first.rightMoves = 0)
    (hFirstLeft : F.pair.first.leftMoves = 2) (hM : F.M = 1) :
    F.uOffset + 3 < n ∧
      sqDist (P F.x) (P (cyclicAdvance F.x (F.uOffset + 1))) = d₁ ∧
      sqDist (P F.x) (P (cyclicAdvance F.x (F.uOffset + 2))) = d₂ := by
  have hzoff : F.zOffset = F.uOffset + 3 := by
    rw [F.zOffset_eq_uOffset_add, hM, hFirstLeft]
  have hlast : F.uOffset + 3 < n := by
    rw [← hzoff]
    exact F.zOffset_lt_card
  have hZ : firstClockwiseNeighbor P d₁ d₂ d₃ F.x =
      cyclicAdvance F.x (F.uOffset + 3) := by
    rw [F.firstClockwiseNeighbor_eq_offset, hzoff]
  have hZR : cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) 1 =
      cyclicAdvance F.x (F.uOffset + 2) := by
    rw [hZ]
    simpa using cyclicRetreat_advance F.x
      (k := F.uOffset + 3) (m := 1) (by omega) (by omega)
  have hZS : cyclicRetreat (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) 2 =
      cyclicAdvance F.x (F.uOffset + 1) := by
    rw [hZ]
    simpa using cyclicRetreat_advance F.x
      (k := F.uOffset + 3) (m := 2) (by omega) (by omega)
  have hFirstStart : TopThreeAdjacent P d₁ d₂ d₃
      (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) F.x := by
    apply topThreeAdjacent_symm
    apply firstClockwiseNeighbor_adjacent_of_degree_pos
    have := F.highDegree F.x
    omega
  have hFirstPath : K3CoverSequence P
      (firstClockwiseNeighbor P d₁ d₂ d₃ F.x) F.x 2 0 := by
    simpa [hFirstLeft, hFirstRight] using F.pair.first.path
  have hLadder := left_left_cover_rank_ladder F.classes hFirstStart hFirstPath
  have hXR : sqDist (P F.x)
      (P (cyclicAdvance F.x (F.uOffset + 2))) = d₂ := by
    have h := hLadder.2.1
    rw [hZR] at h
    simpa [sqDist_comm] using h
  have hXS : sqDist (P F.x)
      (P (cyclicAdvance F.x (F.uOffset + 1))) = d₁ := by
    have h := hLadder.2.2
    rw [hZS] at h
    simpa [sqDist_comm] using h
  exact ⟨hlast, hXS, hXR⟩

/-- The row-4 `D31` route becomes one-penultimate geometry after reflecting
the polygon across the horizontal axis. -/
theorem row4_D31_reflected_raw_realization
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃)
    (hWord : F.RealizesCoverWord .row4_D31) :
    Nonempty (OnePenultimateWordGeometry
      (fun i ↦ reflectAcrossXAxis (P i)) d₁ d₂ d₃) := by
  rcases hWord with
    ⟨hRow, _hFirstOrder, hSecondLeft, hSecondRight, _hSecondOrder, hRank⟩
  rcases hRow with ⟨hFirstRight, hFirstLeft, _hL, hM⟩
  obtain ⟨hlast, hXS, hXR⟩ :=
    F.row4_first_ladder_data hFirstRight hFirstLeft hM
  have huPos : 3 < F.uOffset := by
    dsimp [uOffset]
    have := F.secondGap_pos
    omega
  have hU := F.firstCounterclockwiseNeighbor_eq_uOffset
  change F.secondStartSqDist = d₃ ∧ F.secondTerminalSqDist = d₁ at hRank
  have hTS : sqDist (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 1))) = d₁ := by
    have h := hRank.2
    dsimp only [secondTerminalSqDist] at h
    rw [hSecondLeft, hSecondRight, cyclicRetreat_zero, hU,
      cyclicAdvance_add] at h
    simpa using h
  exact reflectedOnePenultimateGeometry_of_cyclic_offsets
    F.convex F.classes F.x
    (t := 0) (v := 1) (e := 3) (s := F.uOffset + 1)
    (p := F.uOffset + 2)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    hTS (by simpa using hXS) (by simpa using hXR)

/-- The row-4 `DC` route has the same reflected raw geometry, with `x+2`
as its first center. -/
theorem row4_DC_reflected_raw_realization
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃)
    (hWord : F.RealizesCoverWord .row4_DC) :
    Nonempty (OnePenultimateWordGeometry
      (fun i ↦ reflectAcrossXAxis (P i)) d₁ d₂ d₃) := by
  rcases hWord with
    ⟨hRow, _hFirstOrder, hSecondLeft, hSecondRight, hSecondOrder⟩
  rcases hRow with ⟨hFirstRight, hFirstLeft, _hL, hM⟩
  obtain ⟨hlast, hXS, hXR⟩ :=
    F.row4_first_ladder_data hFirstRight hFirstLeft hM
  have huPos : 3 < F.uOffset := by
    dsimp [uOffset]
    have := F.secondGap_pos
    omega
  have hU := F.firstCounterclockwiseNeighbor_eq_uOffset
  have hSecondStart : TopThreeAdjacent P d₁ d₂ d₃
      (cyclicAdvance F.x 3)
      (firstCounterclockwiseNeighbor P d₁ d₂ d₃
        (cyclicAdvance F.x 3)) := by
    apply firstCounterclockwiseNeighbor_adjacent_of_degree_pos
    have := F.highDegree (cyclicAdvance F.x 3)
    omega
  have hSecondPath : K3CoverSequence P (cyclicAdvance F.x 3)
      (firstCounterclockwiseNeighbor P d₁ d₂ d₃
        (cyclicAdvance F.x 3)) 1 1 := by
    simpa [hSecondLeft, hSecondRight] using F.pair.second.path
  have hLadder := K3CoverSequence.right_left_cover_rank_ladder
    F.classes hSecondStart hSecondPath (by
      simpa [hSecondLeft, hSecondRight] using hSecondOrder)
  have hQS : sqDist (P (cyclicAdvance F.x 2))
      (P (cyclicAdvance F.x (F.uOffset + 1))) = d₁ := by
    have h := hLadder.2.2
    rw [hU, cyclicAdvance_add] at h
    have hret : cyclicRetreat (cyclicAdvance F.x 3) 1 =
        cyclicAdvance F.x 2 := by
      simpa using cyclicRetreat_advance F.x
        (k := 3) (m := 1) (by omega) (by omega)
    rw [hret] at h
    simpa using h
  exact reflectedOnePenultimateGeometry_of_cyclic_offsets
    F.convex F.classes F.x
    (t := 0) (v := 1) (e := 2) (s := F.uOffset + 1)
    (p := F.uOffset + 2)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    hQS (by simpa using hXS) (by simpa using hXR)

/-- The row-4 `D32` terminal cage is the reflected terminal realization. -/
theorem row4_D32_reflected_raw_realization
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃)
    (hWord : F.RealizesCoverWord .row4_D32) :
    Nonempty (Row1B32WordRealization
      (fun i ↦ reflectAcrossXAxis (P i)) d₁ d₂ d₃) := by
  rcases hWord with
    ⟨hRow, _hFirstOrder, hSecondLeft, hSecondRight, _hSecondOrder, hRank⟩
  rcases hRow with ⟨hFirstRight, hFirstLeft, _hL, hM⟩
  obtain ⟨hlast, hXS, hXR⟩ :=
    F.row4_first_ladder_data hFirstRight hFirstLeft hM
  have huPos : 3 < F.uOffset := by
    dsimp [uOffset]
    have := F.secondGap_pos
    omega
  have hU := F.firstCounterclockwiseNeighbor_eq_uOffset
  change F.secondStartSqDist = d₃ ∧ F.secondTerminalSqDist = d₂ at hRank
  have hTS : sqDist (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 1))) = d₂ := by
    have h := hRank.2
    dsimp only [secondTerminalSqDist] at h
    rw [hSecondLeft, hSecondRight, cyclicRetreat_zero, hU,
      cyclicAdvance_add] at h
    simpa using h
  have hTRle : sqDist (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 2))) ≤ d₂ := by
    have hnot := F.pair.second.terminal.2
    unfold IsRightCover at hnot
    have hle := le_of_not_gt hnot
    rw [hSecondLeft, hSecondRight, cyclicRetreat_zero, hU,
      cyclicAdvance_add, cyclicAdvance_add] at hle
    have hle' : sqDist (P (cyclicAdvance F.x 3))
        (P (cyclicAdvance F.x (F.uOffset + 2))) ≤
          sqDist (P (cyclicAdvance F.x 3))
            (P (cyclicAdvance F.x (F.uOffset + 1))) := by
      simpa [cyclicAdvance_add] using hle
    exact hle'.trans_eq hTS
  exact reflectedRow1B32Geometry_of_cyclic_offsets
    F.convex F.classes F.x
    (t := 0) (v := 2) (x := 3) (s := F.uOffset + 1)
    (w := F.uOffset + 2)
    (by omega) (by omega) (by omega) rfl (by omega)
    hTRle hTS (by simpa using hXR) (by simpa using hXS)

/-- The row-4 `DD` word supplies the complete two-endpoint four-edge cage. -/
theorem row4_DD_raw_realization
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (F : ErLVGlobalFiveRowFrame P d₁ d₂ d₃)
    (hWord : F.RealizesCoverWord .row4_DD) :
    Nonempty (Row4DDWordRealization P d₁ d₂ d₃) := by
  classical
  rcases hWord with
    ⟨hRow, _hFirstOrder, hSecondLeft, hSecondRight, _hSecondOrder⟩
  rcases hRow with ⟨hFirstRight, hFirstLeft, _hL, hM⟩
  obtain ⟨hlast, hXW, hXS⟩ :=
    F.row4_first_ladder_data hFirstRight hFirstLeft hM
  have huPos : 3 < F.uOffset := by
    dsimp [uOffset]
    have := F.secondGap_pos
    omega
  have hU := F.firstCounterclockwiseNeighbor_eq_uOffset
  have hSecondPath : K3CoverSequence P (cyclicAdvance F.x 3)
      (firstCounterclockwiseNeighbor P d₁ d₂ d₃
        (cyclicAdvance F.x 3)) 0 2 := by
    simpa [hSecondLeft, hSecondRight] using F.pair.second.path
  have hSecondLadder := right_right_cover_rank_ladder F.classes
    F.toUseSite.second_start_adjacent hSecondPath
  have hUseX : F.toUseSite.x = F.x := by
    unfold toUseSite erlvAtVertexUseSiteOfHighDegree
    rfl
  have hTW : sqDist (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 1))) = d₂ := by
    have h := hSecondLadder.2.1
    rw [hUseX, hU] at h
    simpa [cyclicAdvance_add] using h
  have hTS : sqDist (P (cyclicAdvance F.x 3))
      (P (cyclicAdvance F.x (F.uOffset + 2))) = d₁ := by
    have h := hSecondLadder.2.2
    rw [hUseX, hU] at h
    simpa [cyclicAdvance_add] using h
  obtain ⟨first, hFirstVertex⟩ :=
    fourEdgeEndpointGeometry_of_cyclic_offsets (d₂ := d₂) (d₃ := d₃)
      F.convex F.x
      (x := 0) (v := 1) (t := 3) (w := F.uOffset + 1)
      (s := F.uOffset + 2)
      (by omega) (by omega) (by omega) rfl (by omega)
      (by simpa using hXW) hTS
  obtain ⟨second, hSecondVertex⟩ :=
    fourEdgeEndpointGeometry_of_cyclic_offsets (d₂ := d₂) (d₃ := d₃)
      F.convex F.x
      (x := 0) (v := 2) (t := 3) (w := F.uOffset + 1)
      (s := F.uOffset + 2)
      (by omega) (by omega) (by omega) rfl (by omega)
      (by simpa using hXW) hTS
  have hSide (k : ℕ) (hk : k < F.uOffset + 1) :
      InLeftOpenHalfPlane
        (P (cyclicAdvance F.x (F.uOffset + 1)))
        (P (cyclicAdvance F.x (F.uOffset + 2)))
        (P (cyclicAdvance F.x k)) := by
    have h := cyclic_inLeft_of_unwrapped_order F.convex F.x
      (a := F.uOffset + 1) (b := F.uOffset + 2) (k := k + n)
      (by omega) (by omega) (by omega)
    rw [cyclicAdvance_period] at h
    exact h
  have hInjective : Function.Injective P :=
    cyclic_strict_convex_injective F.convex (by omega)
  refine ⟨{
    pointsInjective := hInjective
    classes := F.classes
    x := cyclicAdvance F.x 0
    t := cyclicAdvance F.x 3
    w := cyclicAdvance F.x (F.uOffset + 1)
    s := cyclicAdvance F.x (F.uOffset + 2)
    w_ne_s := by
      simpa using cyclicAdvance_ne_of_lt F.x
        (a := F.uOffset + 1) (b := F.uOffset + 2)
        (by omega) (by omega) (by omega)
    x_ne_w := by
      simpa using cyclicAdvance_ne_of_lt F.x
        (a := 0) (b := F.uOffset + 1)
        (by omega) (by omega) (by omega)
    x_ne_s := by
      simpa using cyclicAdvance_ne_of_lt F.x
        (a := 0) (b := F.uOffset + 2)
        (by omega) (by omega) (by omega)
    t_ne_w := by
      simpa using cyclicAdvance_ne_of_lt F.x
        (a := 3) (b := F.uOffset + 1)
        (by omega) (by omega) (by omega)
    t_ne_s := by
      simpa using cyclicAdvance_ne_of_lt F.x
        (a := 3) (b := F.uOffset + 2)
        (by omega) (by omega) (by omega)
    first := first
    second := second
    first_ne_second := by
      rw [hFirstVertex, hSecondVertex]
      exact cyclicAdvance_ne_of_lt F.x
        (a := 1) (b := 2) (by omega) (by omega) (by omega)
    xSide := by
      simpa using hSide 0 (by omega)
    tSide := hSide 3 (by omega)
    firstSide := by
      rw [hFirstVertex]
      exact hSide 1 (by omega)
    secondSide := by
      rw [hSecondVertex]
      exact hSide 2 (by omega)
    xw := by simpa using hXW
    xs := by simpa using hXS
    tw := hTW
    ts := hTS }⟩

end ErLVGlobalFiveRowFrame

private theorem geometric_word_degree_bound
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (word : ExceptionalCoverWord)
    (hRealizes : GeometricallyRealizesCoverWord P d₁ d₂ d₃ word) :
    ∃ v, vertexDegree P d₁ d₂ d₃ v ≤ word.route.degreeBound := by
  obtain ⟨F, hWord⟩ := hRealizes
  cases word with
  | row1_B32 =>
      obtain ⟨G⟩ := F.row1_B32_raw_realization hWord
      exact ⟨G.vertex, row1_B32_realization_degree_le_six G⟩
  | row1_B31 =>
      obtain ⟨G⟩ := F.row1_B31_raw_realization hWord
      exact ⟨G.vertex, one_penultimate_realization_degree_le_five G⟩
  | row1_B21 =>
      obtain ⟨G⟩ := F.row1_B21_raw_realization hWord
      exact ⟨G.vertex, fullTwoRung_realization_degree_le_six G⟩
  | row2_AB =>
      obtain ⟨G⟩ := F.row2_AB_raw_realization hWord
      exact ⟨G.vertex, fullTwoRung_realization_degree_le_six G⟩
  | row2_BA =>
      obtain ⟨G⟩ := F.row2_BA_raw_realization hWord
      exact ⟨G.vertex, one_penultimate_realization_degree_le_five G⟩
  | row3_BB_DD =>
      obtain ⟨G⟩ := F.row3_BB_DD_raw_realization hWord
      exact ⟨G.vertex, fullTwoRung_realization_degree_le_six G⟩
  | row4_D32 =>
      obtain ⟨G⟩ := F.row4_D32_reflected_raw_realization hWord
      refine ⟨G.vertex, ?_⟩
      simpa only [reflectAcrossXAxis_vertexDegree, ExceptionalCoverWord.route,
        WordClosureRoute.degreeBound] using
        row1_B32_realization_degree_le_six G
  | row4_D31 =>
      obtain ⟨G⟩ := F.row4_D31_reflected_raw_realization hWord
      refine ⟨G.vertex, ?_⟩
      simpa only [reflectAcrossXAxis_vertexDegree, ExceptionalCoverWord.route,
        WordClosureRoute.degreeBound] using
        one_penultimate_realization_degree_le_five G
  | row4_D21 =>
      obtain ⟨G⟩ := F.row4_D21_raw_realization hWord
      exact ⟨G.vertex, fullTwoRung_realization_degree_le_six G⟩
  | row4_CD =>
      obtain ⟨G⟩ := F.row4_CD_raw_realization hWord
      exact ⟨G.vertex, fullTwoRung_realization_degree_le_six G⟩
  | row4_DC =>
      obtain ⟨G⟩ := F.row4_DC_reflected_raw_realization hWord
      refine ⟨G.vertex, ?_⟩
      simpa only [reflectAcrossXAxis_vertexDegree, ExceptionalCoverWord.route,
        WordClosureRoute.degreeBound] using
        one_penultimate_realization_degree_le_five G
  | row4_DD =>
      obtain ⟨G⟩ := F.row4_DD_raw_realization hWord
      exact row4_DD_realization_degree_le_six G
  | row5_BB_DD =>
      obtain ⟨G⟩ := F.row5_BB_DD_raw_realization hWord
      exact ⟨G.vertex, fullTwoRung_realization_degree_le_six G⟩

/-- The thirteen canonical maximal-gap words all transport to their four raw
geometric closure predicates. -/
theorem global_thirteen_word_closure_complete :
    GlobalThirteenWordClosureComplete := by
  intro n _ P d₁ d₂ d₃
  refine ⟨{
    fullTwoRung := ?_
    antiSaturation := ?_
    terminalCage := ?_
    fourEdgeCage := ?_ }⟩
  · intro word hRoute hRealizes
    simpa only [hRoute, WordClosureRoute.degreeBound] using
      geometric_word_degree_bound word hRealizes
  · intro word hRoute hRealizes
    simpa only [hRoute, WordClosureRoute.degreeBound] using
      geometric_word_degree_bound word hRealizes
  · intro word hRoute hRealizes
    simpa only [hRoute, WordClosureRoute.degreeBound] using
      geometric_word_degree_bound word hRealizes
  · intro word hRoute hRealizes
    simpa only [hRoute, WordClosureRoute.degreeBound] using
      geometric_word_degree_bound word hRealizes

/-- Raw convex top-three data now constructs the complete thirteen-word
reduction package without an additional hypothesis. -/
theorem convex_top_three_draft_reduction_complete :
    ConvexTopThreeDraftReductionComplete :=
  convex_top_three_draft_reduction_complete_of_global_word_closure
    global_thirteen_word_closure_complete

/-- Every finite strictly convex three-distance configuration has a vertex
incident to at most six edges from its three largest distance classes. -/
theorem convex_top_three_degree_six : ConvexTopThreeDegreeSixStatement :=
  convex_k3_degree_six_of_reduction
    convex_top_three_draft_reduction_complete

end LeanPool.Erdos132ConvexK3
