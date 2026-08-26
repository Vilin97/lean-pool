/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Congruence
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Basic geometry for the Wei E2 configuration

This file fixes the challenge point type, the diameter-star indexing, and the
raw geometric hypotheses used by the angle-parametrization route.
-/

namespace LeanPool.Erdos132WeiE2.Geometry

open EuclideanGeometry

/-- The plane used by the challenge statement. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The standard real-linear isometry from the complex plane to the challenge plane. -/
noncomputable def complexPlaneEquiv : ℂ ≃ₗᵢ[ℝ] Plane :=
  Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)

/-- Complex coordinates of a point in the challenge plane. -/
noncomputable def toComplex (x : Plane) : ℂ := complexPlaneEquiv.symm x

/-- Signed doubled area, transported through the standard Complex isometry. -/
noncomputable def orientedArea (a b c : Plane) : ℝ :=
  let u := toComplex b - toComplex a
  let v := toComplex c - toComplex a
  u.re * v.im - u.im * v.re

/-- The order in which the seven diameter edges form their cycle. -/
def walkIndex (i : Fin 7) : Fin 7 := 3 * i

/-- The angle between the two unit diameter edges incident at vertex `i`. -/
noncomputable def apexAngle (p : Fin 7 → Plane) (i : Fin 7) : ℝ :=
  ∠ (p (i + 3)) (p i) (p (i + 4))

/-- The geometric and edge-class hypotheses copied from the challenge. -/
structure E2GeometryHypotheses (p : Fin 7 → Plane) : Prop where
  hdiam : ∀ i : Fin 7, dist (p i) (p (i + 3)) = 1
  hshort : ∀ i j : Fin 7, i ≠ j → j ≠ i + 3 → i ≠ j + 3 → dist (p i) (p j) < 1
  hC : dist (p 0) (p 1) = dist (p 3) (p 4)
  hB : dist (p 1) (p 2) = dist (p 2) (p 3)
  hA₁ : dist (p 4) (p 5) = dist (p 5) (p 6)
  hA₂ : dist (p 5) (p 6) = dist (p 6) (p 0)
  hBA : dist (p 1) (p 2) < dist (p 4) (p 5)
  hAC : dist (p 4) (p 5) < dist (p 0) (p 1)

/-- One of the two diameter partners of `i` is not a diameter partner of a
different index `j`. This is a finite fact about the seven-cycle. -/
private theorem exists_diameter_partner_avoiding
    (i j : Fin 7) (hij : i ≠ j) :
    ∃ k : Fin 7,
      (k = i + 3 ∨ i = k + 3) ∧ k ≠ j ∧ k ≠ j + 3 ∧ j ≠ k + 3 := by
  revert hij
  fin_cases i <;> fin_cases j <;> decide

/-- The challenge hypotheses force all seven labelled points to be distinct. -/
theorem pairwise_distinct_of_diameter_pattern
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) : Function.Injective p := by
  intro i j hp
  by_contra hij
  obtain ⟨k, hik, hkj, hkj3, hjk3⟩ := exists_diameter_partner_avoiding i j hij
  have hdik : dist (p i) (p k) = 1 := by
    rcases hik with hik | hik
    · simpa [hik] using h.hdiam i
    · simpa [hik, dist_comm] using h.hdiam k
  have hdjk : dist (p j) (p k) = 1 := by simpa [hp] using hdik
  have hshort := h.hshort j k hkj.symm hkj3 hjk3
  linarith

/-- Every distance is bounded by the common diameter. -/
theorem dist_le_one_of_diameter_pattern
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) (i j : Fin 7) :
    dist (p i) (p j) ≤ 1 := by
  by_cases hij : i = j
  · subst j
    simp
  by_cases hj : j = i + 3
  · exact (show dist (p i) (p j) = 1 by simpa [hj] using h.hdiam i).le
  by_cases hi : i = j + 3
  · exact (show dist (p i) (p j) = 1 by simpa [hi, dist_comm] using h.hdiam j).le
  exact (h.hshort i j hij hj hi).le

/-- Distance one occurs exactly on the two orientations of the labelled
diameter cycle. -/
theorem dist_eq_one_iff_diameter_related
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) (i j : Fin 7) :
    dist (p i) (p j) = 1 ↔ j = i + 3 ∨ i = j + 3 := by
  constructor
  · intro hd
    by_contra hrelated
    have hij : i ≠ j := by
      intro hij
      subst j
      rw [dist_self] at hd
      exact zero_ne_one hd
    have hj : j ≠ i + 3 := fun hj ↦ hrelated (Or.inl hj)
    have hi : i ≠ j + 3 := fun hi ↦ hrelated (Or.inr hi)
    have hshort := h.hshort i j hij hj hi
    linarith
  · rintro (hj | hi)
    · simpa [hj] using h.hdiam i
    · simpa [hi, dist_comm] using h.hdiam j

/-- Every apex triangle is nondegenerate. -/
theorem apex_not_collinear
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) (i : Fin 7) :
    ¬Collinear ℝ ({p (i + 3), p i, p (i + 4)} : Set Plane) := by
  intro hcollinear
  have hinjective := pairwise_distinct_of_diameter_pattern h
  have hleft : p (i + 3) ≠ p i := by
    intro heq
    have := hinjective heq
    omega
  have hright : p (i + 4) ≠ p i := by
    intro heq
    have := hinjective heq
    omega
  have hends : p (i + 3) ≠ p (i + 4) := by
    intro heq
    have := hinjective heq
    omega
  have hleftDist : dist (p (i + 3)) (p i) = 1 := by
    simpa [dist_comm] using h.hdiam i
  have hrightDist : dist (p (i + 4)) (p i) = 1 := by
    have hindex : (i + 4) + 3 = i := by omega
    simpa [hindex] using h.hdiam (i + 4)
  have hbase : dist (p (i + 3)) (p (i + 4)) < 1 :=
    h.hshort (i + 3) (i + 4) (by omega) (by omega) (by omega)
  rcases
      (collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.mp hcollinear) with
    hbad | hbad | hzero | hpi
  · exact hleft hbad
  · exact hright hbad
  · have hcos := law_cos (p (i + 3)) (p i) (p (i + 4))
    rw [hleftDist, hrightDist, hzero, Real.cos_zero] at hcos
    have hdistZero : dist (p (i + 3)) (p (i + 4)) = 0 := by
      have hnonneg : 0 ≤ dist (p (i + 3)) (p (i + 4)) := dist_nonneg
      nlinarith
    exact hends (dist_eq_zero.mp hdistZero)
  · have hcos := law_cos (p (i + 3)) (p i) (p (i + 4))
    rw [hleftDist, hrightDist, hpi, Real.cos_pi] at hcos
    have hnonneg : 0 ≤ dist (p (i + 3)) (p (i + 4)) := dist_nonneg
    nlinarith

end LeanPool.Erdos132WeiE2.Geometry
