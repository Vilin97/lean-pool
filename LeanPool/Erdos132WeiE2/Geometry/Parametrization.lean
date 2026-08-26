/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132WeiE2.Geometry.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

/-!
# Angle parametrization of the Wei E2 diameter star

This module states the frozen geometry/algebra interface. The proof skeleton
follows the certificate walk and does not use the broken E2 swap argument.
-/

namespace LeanPool.Erdos132WeiE2.Geometry

attribute [local instance] Complex.finrank_real_complex_fact

/-- The seven apex angles have the certificate classes `C,A,A,A,C,B,B`. -/
structure AngleClasses (p : Fin 7 → Plane) (A B C : ℝ) : Prop where
  angle0 : apexAngle p 0 = C
  angle1 : apexAngle p 1 = A
  angle2 : apexAngle p 2 = A
  angle3 : apexAngle p 3 = A
  angle4 : apexAngle p 4 = C
  angle5 : apexAngle p 5 = B
  angle6 : apexAngle p 6 = B

/-- The edge-length consequences of the three apex-angle classes. -/
structure EdgeFormulas (p : Fin 7 → Plane) (A B C : ℝ) : Prop where
  edgeC : dist (p 0) (p 1) = 2 * Real.sin (C / 2)
  edgeB : dist (p 1) (p 2) = 2 * Real.sin (B / 2)
  edgeA : dist (p 4) (p 5) = 2 * Real.sin (A / 2)

/-- The required diagonal part of the frozen certificate dictionary (interface v1.2). -/
structure DistanceDictionary (p : Fin 7 → Plane) (A B : ℝ) : Prop where
  q_sq :
    (dist (p 0) (p 2)) ^ 2 =
      3 - 2 * Real.cos A - 2 * Real.cos B + 2 * Real.cos (A + B)
  ra_sq :
    (dist (p 0) (p 5)) ^ 2 =
      4 - 4 * Real.cos A - 2 * Real.cos B + 4 * Real.cos (A + B) -
        2 * Real.cos (2 * A + B)
  rb_sq :
    (dist (p 1) (p 3)) ^ 2 =
      4 - 2 * Real.cos A - 4 * Real.cos B + 4 * Real.cos (A + B) -
        2 * Real.cos (A + 2 * B)

/-- Frozen interface v1.2, with optional class equalities omitted. -/
structure E2AngleParametrization (p : Fin 7 → Plane) (A B C : ℝ) : Prop where
  B_pos : 0 < B
  B_lt_A : B < A
  A_lt_C : A < C
  C_lt_pi_div_three : C < Real.pi / 3
  angle_sum : 2 * C + 3 * A + 2 * B = Real.pi
  closure : 2 * Real.sin (A / 2) * (1 + 2 * Real.cos (A + B)) = 1
  edgeC : dist (p 0) (p 1) = 2 * Real.sin (C / 2)
  edgeB : dist (p 1) (p 2) = 2 * Real.sin (B / 2)
  edgeA : dist (p 4) (p 5) = 2 * Real.sin (A / 2)
  q_sq :
    (dist (p 0) (p 2)) ^ 2 =
      3 - 2 * Real.cos A - 2 * Real.cos B + 2 * Real.cos (A + B)
  ra_sq :
    (dist (p 0) (p 5)) ^ 2 =
      4 - 4 * Real.cos A - 2 * Real.cos B + 4 * Real.cos (A + B) -
        2 * Real.cos (2 * A + B)
  rb_sq :
    (dist (p 1) (p 3)) ^ 2 =
      4 - 2 * Real.cos A - 4 * Real.cos B + 4 * Real.cos (A + B) -
        2 * Real.cos (A + 2 * B)

/-- Equal base lengths in two unit apex triangles give equal apex angles. -/
private theorem apexAngle_eq_of_base_dist_eq
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) {i j : Fin 7}
    (hbase : dist (p (i + 3)) (p (i + 4)) =
      dist (p (j + 3)) (p (j + 4))) :
    apexAngle p i = apexAngle p j := by
  have hleft (k : Fin 7) : dist (p (k + 3)) (p k) = 1 := by
    simpa [dist_comm] using h.hdiam k
  have hright (k : Fin 7) : dist (p k) (p (k + 4)) = 1 := by
    have hd := h.hdiam (k + 4)
    have hindex : (k + 4) + 3 = k := by omega
    simpa [hindex, dist_comm] using hd
  have hcongruent := EuclideanGeometry.side_side_side
    (show dist (p (i + 3)) (p i) = dist (p (j + 3)) (p j) by
      rw [hleft i, hleft j])
    (show dist (p i) (p (i + 4)) = dist (p j) (p (j + 4)) by
      rw [hright i, hright j])
    (show dist (p (i + 4)) (p (i + 3)) =
        dist (p (j + 4)) (p (j + 3)) by
      simpa [dist_comm] using hbase)
  simpa [apexAngle] using
    EuclideanGeometry.angle_eq_of_congruent hcongruent (0 : Fin 3) 1 2

/-- The challenge edge equalities give the certificate angle-class pattern. -/
theorem apex_angle_classes
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) :
    AngleClasses p (apexAngle p 1) (apexAngle p 5) (apexAngle p 0) := by
  have h04 : apexAngle p 0 = apexAngle p 4 :=
    apexAngle_eq_of_base_dist_eq h h.hC.symm
  have h12 : apexAngle p 1 = apexAngle p 2 :=
    apexAngle_eq_of_base_dist_eq h h.hA₁
  have h23 : apexAngle p 2 = apexAngle p 3 :=
    apexAngle_eq_of_base_dist_eq h h.hA₂
  have h56 : apexAngle p 5 = apexAngle p 6 :=
    apexAngle_eq_of_base_dist_eq h h.hB
  exact
    { angle0 := rfl
      angle1 := rfl
      angle2 := h12.symm
      angle3 := h23.symm.trans h12.symm
      angle4 := h04.symm
      angle5 := rfl
      angle6 := h56.symm }

private def complexCross (x y : ℂ) : ℝ :=
  x.re * y.im - x.im * y.re

private theorem complex_oangle_eq_angle_of_cross_pos
    {x y : ℂ} (hcross : 0 < complexCross x y) :
    Complex.orientation.oangle x y = InnerProductGeometry.angle x y := by
  have hx : x ≠ 0 := by
    intro hx
    simp [hx, complexCross] at hcross
  have hy : y ≠ 0 := by
    intro hy
    simp [hy, complexCross] at hcross
  rcases Complex.orientation.oangle_eq_angle_or_eq_neg_angle hx hy with hpos | hneg
  · exact hpos
  · have hsin : 0 < Real.Angle.sin (Complex.orientation.oangle x y) := by
      rw [Complex.oangle, Real.Angle.sin_coe, Complex.sin_arg]
      have him : ((starRingEnd ℂ) x * y).im = complexCross x y := by
        simp [complexCross]
        ring
      rw [him]
      exact div_pos hcross (norm_pos_iff.mpr
        (mul_ne_zero ((map_ne_zero (starRingEnd ℂ)).2 hx) hy))
    rw [hneg, Real.Angle.sin_neg, Real.Angle.sin_coe] at hsin
    have hnonneg := Real.sin_nonneg_of_nonneg_of_le_pi
      (InnerProductGeometry.angle_nonneg x y) (InnerProductGeometry.angle_le_pi x y)
    linarith

private theorem complex_oangle_eq_neg_angle_of_cross_neg
    {x y : ℂ} (hcross : complexCross x y < 0) :
    Complex.orientation.oangle x y = -InnerProductGeometry.angle x y := by
  have hx : x ≠ 0 := by
    intro hx
    simp [hx, complexCross] at hcross
  have hy : y ≠ 0 := by
    intro hy
    simp [hy, complexCross] at hcross
  rcases Complex.orientation.oangle_eq_angle_or_eq_neg_angle hx hy with hpos | hneg
  · have hsin : Real.Angle.sin (Complex.orientation.oangle x y) < 0 := by
      rw [Complex.oangle, Real.Angle.sin_coe, Complex.sin_arg]
      have him : ((starRingEnd ℂ) x * y).im = complexCross x y := by
        simp [complexCross]
        ring
      rw [him]
      exact div_neg_of_neg_of_pos hcross (norm_pos_iff.mpr
        (mul_ne_zero ((map_ne_zero (starRingEnd ℂ)).2 hx) hy))
    rw [hpos, Real.Angle.sin_coe] at hsin
    have hnonneg := Real.sin_nonneg_of_nonneg_of_le_pi
      (InnerProductGeometry.angle_nonneg x y) (InnerProductGeometry.angle_le_pi x y)
    linarith
  · exact hneg

private theorem apexAngle_pos
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) (i : Fin 7) :
    0 < apexAngle p i := by
  exact EuclideanGeometry.angle_pos_of_not_collinear (apex_not_collinear h i)

private theorem apexAngle_lt_pi
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) (i : Fin 7) :
    apexAngle p i < Real.pi := by
  exact EuclideanGeometry.angle_lt_pi_of_not_collinear (apex_not_collinear h i)

private theorem apex_base_sq
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) (i : Fin 7) :
    (dist (p (i + 3)) (p (i + 4))) ^ 2 = 2 - 2 * Real.cos (apexAngle p i) := by
  have hleft : dist (p (i + 3)) (p i) = 1 := by
    simpa [dist_comm] using h.hdiam i
  have hright : dist (p i) (p (i + 4)) = 1 := by
    have hd := h.hdiam (i + 4)
    have hindex : (i + 4) + 3 = i := by omega
    simpa [hindex, dist_comm] using hd
  have hcos := EuclideanGeometry.law_cos (p (i + 3)) (p i) (p (i + 4))
  rw [hleft, dist_comm (p (i + 4)) (p i), hright] at hcos
  norm_num at hcos
  simpa [apexAngle, pow_two] using hcos

private theorem apexAngle_lt_of_base_dist_lt
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) {i j : Fin 7}
    (hbase : dist (p (i + 3)) (p (i + 4)) <
      dist (p (j + 3)) (p (j + 4))) :
    apexAngle p i < apexAngle p j := by
  have hsquare :
      (dist (p (i + 3)) (p (i + 4))) ^ 2 <
        (dist (p (j + 3)) (p (j + 4))) ^ 2 :=
    (sq_lt_sq₀ dist_nonneg dist_nonneg).2 hbase
  have hcos : Real.cos (apexAngle p j) < Real.cos (apexAngle p i) := by
    rw [apex_base_sq h i, apex_base_sq h j] at hsquare
    linarith
  by_contra hnot
  have hreverse : apexAngle p j ≤ apexAngle p i := le_of_not_gt hnot
  have hcosReverse := Real.antitoneOn_cos
    ⟨(apexAngle_pos h j).le, (apexAngle_lt_pi h j).le⟩
    ⟨(apexAngle_pos h i).le, (apexAngle_lt_pi h i).le⟩ hreverse
  linarith

private theorem apexAngle_lt_pi_div_three
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) (i : Fin 7)
    (hbase : dist (p (i + 3)) (p (i + 4)) < 1) :
    apexAngle p i < Real.pi / 3 := by
  have hsquare : (dist (p (i + 3)) (p (i + 4))) ^ 2 < 1 := by
    nlinarith [dist_nonneg (x := p (i + 3)) (y := p (i + 4))]
  have hcos : 1 / 2 < Real.cos (apexAngle p i) := by
    rw [apex_base_sq h i] at hsquare
    linarith
  by_contra hnot
  have hthirdNonneg : 0 ≤ Real.pi / 3 := by positivity
  have hthirdLePi : Real.pi / 3 ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hcosLe := Real.antitoneOn_cos
    ⟨hthirdNonneg, hthirdLePi⟩
    ⟨(apexAngle_pos h i).le, (apexAngle_lt_pi h i).le⟩ (le_of_not_gt hnot)
  rw [Real.cos_pi_div_three] at hcosLe
  norm_num at hcosLe
  linarith

private theorem apex_base_lt_one
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) (i : Fin 7) :
    dist (p (i + 3)) (p (i + 4)) < 1 := by
  exact h.hshort (i + 3) (i + 4) (by omega) (by omega) (by omega)

private theorem apex_base_eq_two_mul_sin_half
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) (i : Fin 7) :
    dist (p (i + 3)) (p (i + 4)) =
      2 * Real.sin (apexAngle p i / 2) := by
  have hhalfNonneg : 0 ≤ apexAngle p i / 2 := by
    exact div_nonneg (apexAngle_pos h i).le (by norm_num)
  have hhalfLePi : apexAngle p i / 2 ≤ Real.pi := by
    linarith [apexAngle_lt_pi h i, Real.pi_pos]
  have hrightNonneg : 0 ≤ 2 * Real.sin (apexAngle p i / 2) :=
    mul_nonneg (by norm_num) (Real.sin_nonneg_of_nonneg_of_le_pi hhalfNonneg hhalfLePi)
  apply (sq_eq_sq₀ dist_nonneg hrightNonneg).mp
  rw [apex_base_sq h i]
  have htrig := Real.cos_two_mul (apexAngle p i / 2)
  have hdouble : 2 * (apexAngle p i / 2) = apexAngle p i := by ring
  rw [hdouble] at htrig
  nlinarith [Real.sin_sq_add_cos_sq (apexAngle p i / 2)]

private noncomputable def walkComplexPoint (p : Fin 7 → Plane) (k : Fin 7) : ℂ :=
  toComplex (p (walkIndex k))

private noncomputable def walkComplexEdge (p : Fin 7 → Plane) (k : Fin 7) : ℂ :=
  walkComplexPoint p (k + 1) - walkComplexPoint p k

private theorem walkComplexEdge_ne_zero
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) (k : Fin 7) :
    walkComplexEdge p k ≠ 0 := by
  intro hedge
  have hz : walkComplexPoint p (k + 1) = walkComplexPoint p k := sub_eq_zero.mp hedge
  have hp : p (walkIndex (k + 1)) = p (walkIndex k) :=
    complexPlaneEquiv.symm.injective (by
      simpa [walkComplexPoint, toComplex] using hz)
  have hi := pairwise_distinct_of_diameter_pattern h hp
  have hne : walkIndex (k + 1) ≠ walkIndex k := by
    fin_cases k <;> decide
  exact hne hi

private theorem walkComplexAngle_eq_apex
    (p : Fin 7 → Plane) (k : Fin 7) :
    InnerProductGeometry.angle (-walkComplexEdge p k) (walkComplexEdge p (k + 1)) =
      apexAngle p (walkIndex (k + 1)) := by
  have hmap := complexPlaneEquiv.symm.toLinearIsometry.angle_map
    (p (walkIndex k) - p (walkIndex (k + 1)))
    (p (walkIndex (k + 2)) - p (walkIndex (k + 1)))
  have hstep : (k + 1) + 1 = k + 2 := by omega
  have hprev : walkIndex k = walkIndex (k + 1) + 4 := by
    simp only [walkIndex]
    omega
  have hnext : walkIndex (k + 2) = walkIndex (k + 1) + 3 := by
    simp only [walkIndex]
    omega
  simpa [walkComplexEdge, walkComplexPoint, hstep, neg_sub, hprev, hnext,
    apexAngle, EuclideanGeometry.angle, toComplex, InnerProductGeometry.angle_comm] using hmap

private theorem walkComplexCross_eq_neg_orientedArea
    (p : Fin 7 → Plane) (k : Fin 7) :
    complexCross (-walkComplexEdge p k) (walkComplexEdge p (k + 1)) =
      -orientedArea (p (walkIndex k)) (p (walkIndex (k + 1)))
        (p (walkIndex (k + 2))) := by
  have hstep : (k + 1) + 1 = k + 2 := by omega
  simp only [walkComplexEdge, walkComplexPoint, hstep, orientedArea, complexCross,
    Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im]
  ring

private noncomputable def walkComplexTurn (p : Fin 7 → Plane) (k : Fin 7) :
    Real.Angle :=
  Complex.orientation.oangle (-walkComplexEdge p k) (walkComplexEdge p (k + 1))

private noncomputable def walkExteriorTurn (p : Fin 7 → Plane) (k : Fin 7) :
    Real.Angle :=
  Complex.orientation.oangle (walkComplexEdge p k) (walkComplexEdge p (k + 1))

private theorem walkComplexTurn_eq_exterior_add_pi
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) (k : Fin 7) :
    walkComplexTurn p k = walkExteriorTurn p k + Real.pi := by
  exact Complex.orientation.oangle_neg_left (walkComplexEdge_ne_zero h k)
    (walkComplexEdge_ne_zero h (k + 1))

private theorem walkComplexTurn_sum
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) :
    walkComplexTurn p 0 + walkComplexTurn p 1 + walkComplexTurn p 2 +
      walkComplexTurn p 3 + walkComplexTurn p 4 + walkComplexTurn p 5 +
        walkComplexTurn p 6 = Real.pi := by
  have h0 := walkComplexEdge_ne_zero h (0 : Fin 7)
  have h1 := walkComplexEdge_ne_zero h (1 : Fin 7)
  have h2 := walkComplexEdge_ne_zero h (2 : Fin 7)
  have h3 := walkComplexEdge_ne_zero h (3 : Fin 7)
  have h4 := walkComplexEdge_ne_zero h (4 : Fin 7)
  have h5 := walkComplexEdge_ne_zero h (5 : Fin 7)
  have h6 := walkComplexEdge_ne_zero h (6 : Fin 7)
  have hexterior :
      walkExteriorTurn p 0 + walkExteriorTurn p 1 + walkExteriorTurn p 2 +
        walkExteriorTurn p 3 + walkExteriorTurn p 4 + walkExteriorTurn p 5 +
          walkExteriorTurn p 6 = 0 := by
    simp only [walkExteriorTurn]
    calc
      Complex.orientation.oangle (walkComplexEdge p 0) (walkComplexEdge p 1) +
            Complex.orientation.oangle (walkComplexEdge p 1) (walkComplexEdge p 2) +
          Complex.orientation.oangle (walkComplexEdge p 2) (walkComplexEdge p 3) +
        Complex.orientation.oangle (walkComplexEdge p 3) (walkComplexEdge p 4) +
          Complex.orientation.oangle (walkComplexEdge p 4) (walkComplexEdge p 5) +
        Complex.orientation.oangle (walkComplexEdge p 5) (walkComplexEdge p 6) +
        Complex.orientation.oangle (walkComplexEdge p 6) (walkComplexEdge p 0) =
          Complex.orientation.oangle (walkComplexEdge p 0) (walkComplexEdge p 2) +
            Complex.orientation.oangle (walkComplexEdge p 2) (walkComplexEdge p 3) +
          Complex.orientation.oangle (walkComplexEdge p 3) (walkComplexEdge p 4) +
            Complex.orientation.oangle (walkComplexEdge p 4) (walkComplexEdge p 5) +
          Complex.orientation.oangle (walkComplexEdge p 5) (walkComplexEdge p 6) +
          Complex.orientation.oangle (walkComplexEdge p 6) (walkComplexEdge p 0) := by
            rw [Complex.orientation.oangle_add h0 h1 h2]
      _ = Complex.orientation.oangle (walkComplexEdge p 0) (walkComplexEdge p 3) +
            Complex.orientation.oangle (walkComplexEdge p 3) (walkComplexEdge p 4) +
          Complex.orientation.oangle (walkComplexEdge p 4) (walkComplexEdge p 5) +
            Complex.orientation.oangle (walkComplexEdge p 5) (walkComplexEdge p 6) +
          Complex.orientation.oangle (walkComplexEdge p 6) (walkComplexEdge p 0) := by
            rw [Complex.orientation.oangle_add h0 h2 h3]
      _ = Complex.orientation.oangle (walkComplexEdge p 0) (walkComplexEdge p 4) +
            Complex.orientation.oangle (walkComplexEdge p 4) (walkComplexEdge p 5) +
          Complex.orientation.oangle (walkComplexEdge p 5) (walkComplexEdge p 6) +
          Complex.orientation.oangle (walkComplexEdge p 6) (walkComplexEdge p 0) := by
            rw [Complex.orientation.oangle_add h0 h3 h4]
      _ = Complex.orientation.oangle (walkComplexEdge p 0) (walkComplexEdge p 5) +
            Complex.orientation.oangle (walkComplexEdge p 5) (walkComplexEdge p 6) +
          Complex.orientation.oangle (walkComplexEdge p 6) (walkComplexEdge p 0) := by
            rw [Complex.orientation.oangle_add h0 h4 h5]
      _ = Complex.orientation.oangle (walkComplexEdge p 0) (walkComplexEdge p 6) +
          Complex.orientation.oangle (walkComplexEdge p 6) (walkComplexEdge p 0) := by
            rw [Complex.orientation.oangle_add h0 h5 h6]
      _ = 0 := Complex.orientation.oangle_add_oangle_rev _ _
  have hsevenPi :
      (Real.pi : Real.Angle) + Real.pi + Real.pi + Real.pi + Real.pi + Real.pi + Real.pi =
        Real.pi := by
    calc
      (Real.pi : Real.Angle) + Real.pi + Real.pi + Real.pi + Real.pi + Real.pi + Real.pi =
          (Real.pi + Real.pi) + (Real.pi + Real.pi) + (Real.pi + Real.pi) + Real.pi := by
            abel
      _ = Real.pi := by simp
  rw [walkComplexTurn_eq_exterior_add_pi h 0,
    walkComplexTurn_eq_exterior_add_pi h 1,
    walkComplexTurn_eq_exterior_add_pi h 2,
    walkComplexTurn_eq_exterior_add_pi h 3,
    walkComplexTurn_eq_exterior_add_pi h 4,
    walkComplexTurn_eq_exterior_add_pi h 5,
    walkComplexTurn_eq_exterior_add_pi h 6]
  calc
    (walkExteriorTurn p 0 + Real.pi) + (walkExteriorTurn p 1 + Real.pi) +
          (walkExteriorTurn p 2 + Real.pi) + (walkExteriorTurn p 3 + Real.pi) +
        (walkExteriorTurn p 4 + Real.pi) + (walkExteriorTurn p 5 + Real.pi) +
        (walkExteriorTurn p 6 + Real.pi) =
      (walkExteriorTurn p 0 + walkExteriorTurn p 1 + walkExteriorTurn p 2 +
          walkExteriorTurn p 3 + walkExteriorTurn p 4 + walkExteriorTurn p 5 +
          walkExteriorTurn p 6) +
        (Real.pi + Real.pi + Real.pi + Real.pi + Real.pi + Real.pi + Real.pi) := by
          abel
    _ = Real.pi := by rw [hexterior, hsevenPi, zero_add]

/-- The star structure and edge order determine the three ordered angle classes. -/
theorem ordered_angle_classes
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p) :
    ∃ A B C : ℝ,
      0 < B ∧ B < A ∧ A < C ∧ C < Real.pi / 3 ∧ AngleClasses p A B C := by
  refine ⟨apexAngle p 1, apexAngle p 5, apexAngle p 0, apexAngle_pos h 5, ?_, ?_, ?_,
    apex_angle_classes h⟩
  · exact apexAngle_lt_of_base_dist_lt h h.hBA
  · apply apexAngle_lt_of_base_dist_lt h
    simpa using h.hAC.trans_eq h.hC
  · apply apexAngle_lt_pi_div_three h 0
    exact h.hshort 3 4 (by decide) (by decide) (by decide)

/-- The consistently oriented star walk gives the certificate angle sum. -/
theorem star_angle_sum
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p)
    {A B C : ℝ} (hclasses : AngleClasses p A B C) :
    2 * C + 3 * A + 2 * B = Real.pi := by
  obtain ⟨ε, hε, hturn⟩ := diameter_star_structure h
  have hw0 : walkIndex ((0 : Fin 7) + 1) = 3 := by decide
  have hw1 : walkIndex ((1 : Fin 7) + 1) = 6 := by decide
  have hw2 : walkIndex ((2 : Fin 7) + 1) = 2 := by decide
  have hw3 : walkIndex ((3 : Fin 7) + 1) = 5 := by decide
  have hw4 : walkIndex ((4 : Fin 7) + 1) = 1 := by decide
  have hw5 : walkIndex ((5 : Fin 7) + 1) = 4 := by decide
  have hw6 : walkIndex ((6 : Fin 7) + 1) = 0 := by decide
  have hmod : ((2 * C + 3 * A + 2 * B : ℝ) : Real.Angle) = Real.pi := by
    rcases hε with rfl | rfl
    · have hturnNeg (k : Fin 7) :
          walkComplexTurn p k = -(apexAngle p (walkIndex (k + 1)) : Real.Angle) := by
        have harea := hturn k
        have hcross :
            complexCross (-walkComplexEdge p k) (walkComplexEdge p (k + 1)) < 0 := by
          rw [walkComplexCross_eq_neg_orientedArea]
          norm_num at harea ⊢
          linarith
        have hoangle := complex_oangle_eq_neg_angle_of_cross_neg hcross
        rw [walkComplexAngle_eq_apex] at hoangle
        exact hoangle
      have hsum := walkComplexTurn_sum h
      rw [hturnNeg 0, hturnNeg 1, hturnNeg 2, hturnNeg 3, hturnNeg 4,
        hturnNeg 5, hturnNeg 6] at hsum
      rw [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hclasses.angle0,
        hclasses.angle1, hclasses.angle2, hclasses.angle3, hclasses.angle4,
        hclasses.angle5, hclasses.angle6] at hsum
      have hnegative :
          -((A + B + A + B + A + C + C : ℝ) : Real.Angle) = Real.pi := by
        calc
          -((A + B + A + B + A + C + C : ℝ) : Real.Angle) =
              -((A : Real.Angle) + B + A + B + A + C + C) := by
                simp only [Real.Angle.coe_add]
          _ = -(A : Real.Angle) - B - A - B - A - C - C := by abel
          _ =
              -A + -B + -A + -B + -A + -C + -C := by abel
          _ = Real.pi := hsum
      have hnegated := congrArg (fun θ : Real.Angle ↦ -θ) hnegative
      have hpositive :
          ((A + B + A + B + A + C + C : ℝ) : Real.Angle) = Real.pi := by
        simpa using hnegated
      have hreal : 2 * C + 3 * A + 2 * B = A + B + A + B + A + C + C := by ring
      rw [hreal]
      exact hpositive
    · have hturnPos (k : Fin 7) :
          walkComplexTurn p k = (apexAngle p (walkIndex (k + 1)) : Real.Angle) := by
        have harea := hturn k
        have hcross :
            0 < complexCross (-walkComplexEdge p k) (walkComplexEdge p (k + 1)) := by
          rw [walkComplexCross_eq_neg_orientedArea]
          norm_num at harea ⊢
          linarith
        have hoangle := complex_oangle_eq_angle_of_cross_pos hcross
        rw [walkComplexAngle_eq_apex] at hoangle
        exact hoangle
      have hsum := walkComplexTurn_sum h
      rw [hturnPos 0, hturnPos 1, hturnPos 2, hturnPos 3, hturnPos 4,
        hturnPos 5, hturnPos 6] at hsum
      rw [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hclasses.angle0,
        hclasses.angle1, hclasses.angle2, hclasses.angle3, hclasses.angle4,
        hclasses.angle5, hclasses.angle6] at hsum
      have hpositive :
          ((A + B + A + B + A + C + C : ℝ) : Real.Angle) = Real.pi := by
        simpa only [Real.Angle.coe_add] using hsum
      have hreal : 2 * C + 3 * A + 2 * B = A + B + A + B + A + C + C := by ring
      rw [hreal]
      exact hpositive
  have hBpos : 0 < B := by rw [← hclasses.angle5]; exact apexAngle_pos h 5
  have hApos : 0 < A := by rw [← hclasses.angle1]; exact apexAngle_pos h 1
  have hCpos : 0 < C := by rw [← hclasses.angle0]; exact apexAngle_pos h 0
  have hBthird : B < Real.pi / 3 := by
    rw [← hclasses.angle5]
    exact apexAngle_lt_pi_div_three h 5 (apex_base_lt_one h 5)
  have hAthird : A < Real.pi / 3 := by
    rw [← hclasses.angle1]
    exact apexAngle_lt_pi_div_three h 1 (apex_base_lt_one h 1)
  have hCthird : C < Real.pi / 3 := by
    rw [← hclasses.angle0]
    exact apexAngle_lt_pi_div_three h 0 (apex_base_lt_one h 0)
  have hsumPos : 0 < 2 * C + 3 * A + 2 * B := by positivity
  have hsumUpper : 2 * C + 3 * A + 2 * B < 7 * Real.pi / 3 := by linarith
  obtain ⟨n, hn⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hmod
  have hnzero : n = 0 := by
    by_contra hnzero
    rcases lt_or_gt_of_ne hnzero with hnneg | hnpos
    · have hnle : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      nlinarith [Real.pi_pos]
    · have hnle : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      nlinarith [Real.pi_pos]
  subst n
  norm_num at hn
  linarith

/-- Unit isosceles apex triangles give the three edge formulas. -/
theorem edge_formulas
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p)
    {A B C : ℝ} (hclasses : AngleClasses p A B C) :
    EdgeFormulas p A B C := by
  constructor
  · simpa [hclasses.angle4] using apex_base_eq_two_mul_sin_half h 4
  · simpa [hclasses.angle5] using apex_base_eq_two_mul_sin_half h 5
  · simpa [hclasses.angle1] using apex_base_eq_two_mul_sin_half h 1

/-- Closing the normalized Complex walk gives the scalar closure identity. -/
theorem star_scalar_closure
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p)
    {A B C : ℝ} (hclasses : AngleClasses p A B C)
    (hsum : 2 * C + 3 * A + 2 * B = Real.pi) :
    2 * Real.sin (A / 2) * (1 + 2 * Real.cos (A + B)) = 1 := by
  sorry

/-- Norm expansion of the normalized certificate walk gives required G6, G8, and G9. -/
theorem distance_dictionary
    {p : Fin 7 → Plane} (h : E2GeometryHypotheses p)
    {A B C : ℝ} (hclasses : AngleClasses p A B C)
    (hsum : 2 * C + 3 * A + 2 * B = Real.pi) :
    DistanceDictionary p A B := by
  sorry

/-- Geometry half of the frozen E2 solution interface. -/
theorem e2_angle_parametrization
    (p : Fin 7 → EuclideanSpace ℝ (Fin 2))
    (hdiam : ∀ i : Fin 7, dist (p i) (p (i + 3)) = 1)
    (hshort : ∀ i j : Fin 7, i ≠ j → j ≠ i + 3 → i ≠ j + 3 → dist (p i) (p j) < 1)
    (hC : dist (p 0) (p 1) = dist (p 3) (p 4))
    (hB : dist (p 1) (p 2) = dist (p 2) (p 3))
    (hA₁ : dist (p 4) (p 5) = dist (p 5) (p 6))
    (hA₂ : dist (p 5) (p 6) = dist (p 6) (p 0))
    (hBA : dist (p 1) (p 2) < dist (p 4) (p 5))
    (hAC : dist (p 4) (p 5) < dist (p 0) (p 1)) :
    ∃ A B C : ℝ, E2AngleParametrization p A B C := by
  sorry

end LeanPool.Erdos132WeiE2.Geometry
