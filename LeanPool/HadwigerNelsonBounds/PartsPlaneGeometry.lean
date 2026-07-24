/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsCanonicalTriangle

/-!
# Plane geometry for the Parts spindle

This module gives an explicit triangular-lattice realization and elementary
distance-preserving rotations.  The two exact cosines are the angles used in
Parts' doubled wheel and spindle.
-/

namespace HadwigerNelsonBounds

/-- A point in `R²` from its two Cartesian coordinates. -/
noncomputable def pointR2 (x y : ℝ) : R2 :=
  WithLp.toLp 2 ![x, y]

@[simp] lemma pointR2_zero (x y : ℝ) : pointR2 x y 0 = x := rfl
@[simp] lemma pointR2_one (x y : ℝ) : pointR2 x y 1 = y := rfl

/-- The triangular-lattice point with axial coordinates `(q,r)`. -/
noncomputable def partsAxialPoint (q r : ℤ) : R2 :=
  pointR2 (((q : ℝ) - r) / 2)
    (((q : ℝ) + r) * Real.sqrt 3 / 2)

@[simp] lemma partsAxialPoint_zero : partsAxialPoint 0 0 = 0 := by
  ext i
  fin_cases i <;> simp [partsAxialPoint, pointR2]

lemma partsAxialPoint_add (q r q' r' : ℤ) :
    partsAxialPoint (q + q') (r + r') =
      partsAxialPoint q r + partsAxialPoint q' r' := by
  ext i
  fin_cases i <;> simp [partsAxialPoint, pointR2] <;> ring

lemma partsAxialPoint_neg (q r : ℤ) :
    partsAxialPoint (-q) (-r) = -partsAxialPoint q r := by
  ext i
  fin_cases i <;> simp [partsAxialPoint, pointR2] <;> ring

lemma partsAxialPoint_sub (q r q' r' : ℤ) :
    partsAxialPoint (q - q') (r - r') =
      partsAxialPoint q r - partsAxialPoint q' r' := by
  ext i
  fin_cases i <;> simp [partsAxialPoint, pointR2] <;> ring

private lemma partsPoint_195 :
    partsPoint (195 : Fin 481) = ⟨6, 0, 6, 0⟩ := by decide

private lemma partsPoint_205 :
    partsPoint (205 : Fin 481) = ⟨6, 0, -6, 0⟩ := by decide

private lemma partsPoint_215 :
    partsPoint (215 : Fin 481) = ⟨-12, 0, 0, 0⟩ := by decide

lemma partsTriangleA_eq_axial : partsTriangleA = partsAxialPoint 1 0 := by
  ext i
  fin_cases i
  · norm_num [partsTriangleA, partsPoint_195, PartsPoint.toR2,
      partsAxialPoint, pointR2]
  · have hsqrt : Real.sqrt 3 ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    simp [partsTriangleA, partsPoint_195, PartsPoint.toR2,
      partsAxialPoint, pointR2]
    field_simp [hsqrt]
    nlinarith [sqrt_three_mul_self]

lemma partsTriangleB_eq_axial : partsTriangleB = partsAxialPoint 0 (-1) := by
  ext i
  fin_cases i
  · norm_num [partsTriangleB, partsPoint_205, PartsPoint.toR2,
      partsAxialPoint, pointR2]
  · have hsqrt : Real.sqrt 3 ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    simp [partsTriangleB, partsPoint_205, PartsPoint.toR2,
      partsAxialPoint, pointR2]
    field_simp [hsqrt]
    nlinarith [sqrt_three_mul_self]

lemma partsTriangleC_eq_axial : partsTriangleC = partsAxialPoint (-1) 1 := by
  ext i
  fin_cases i
  · norm_num [partsTriangleC, partsPoint_215, PartsPoint.toR2,
      partsAxialPoint, pointR2]
  · norm_num [partsTriangleC, partsPoint_215, PartsPoint.toR2,
      partsAxialPoint, pointR2]

/-- Squared distance on the axial triangular lattice. -/
lemma partsAxialPoint_dist_sq (q r q' r' : ℤ) :
    dist (partsAxialPoint q r) (partsAxialPoint q' r') ^ 2 =
      ((q - q' : ℤ) : ℝ) ^ 2 +
        ((q - q' : ℤ) : ℝ) * ((r - r' : ℤ) : ℝ) +
        ((r - r' : ℤ) : ℝ) ^ 2 := by
  rw [PiLp.dist_sq_eq_of_L2]
  simp only [Fin.sum_univ_two, partsAxialPoint, pointR2_zero, pointR2_one,
    Real.dist_eq, sq_abs, Int.cast_sub]
  have hsqrt : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt_three_mul_self
  ring_nf
  rw [show Real.sqrt 3 ^ 2 = 3 by nlinarith]
  ring

lemma partsAxialPoint_dist_eq_one {q r q' r' : ℤ}
    (hnorm : (q - q') ^ 2 + (q - q') * (r - r') + (r - r') ^ 2 = 1) :
    dist (partsAxialPoint q r) (partsAxialPoint q' r') = 1 := by
  have hsq : dist (partsAxialPoint q r) (partsAxialPoint q' r') ^ 2 = 1 := by
    rw [partsAxialPoint_dist_sq]
    exact_mod_cast hnorm
  have hnonneg : 0 ≤ dist (partsAxialPoint q r) (partsAxialPoint q' r') :=
    dist_nonneg
  nlinarith

/-- Rotation through an angle represented by its cosine and sine. -/
noncomputable def planeRotation (cosine sine : ℝ) (p : R2) : R2 :=
  pointR2 (cosine * p 0 - sine * p 1)
    (sine * p 0 + cosine * p 1)

@[simp] lemma planeRotation_zero (cosine sine : ℝ) :
    planeRotation cosine sine 0 = 0 := by
  ext i
  fin_cases i <;> simp [planeRotation, pointR2]

lemma planeRotation_dist_eq {cosine sine : ℝ}
    (htrig : cosine ^ 2 + sine ^ 2 = 1) (p q : R2) :
    dist (planeRotation cosine sine p) (planeRotation cosine sine q) =
      dist p q := by
  have hsq :
      dist (planeRotation cosine sine p) (planeRotation cosine sine q) ^ 2 =
        dist p q ^ 2 := by
    rw [PiLp.dist_sq_eq_of_L2, PiLp.dist_sq_eq_of_L2]
    simp only [Fin.sum_univ_two, planeRotation, pointR2_zero, pointR2_one,
      Real.dist_eq, sq_abs]
    nlinarith [sq_nonneg (p 0 - q 0), sq_nonneg (p 1 - q 1)]
  have hleft : 0 ≤
      dist (planeRotation cosine sine p) (planeRotation cosine sine q) :=
    dist_nonneg
  have hright : 0 ≤ dist p q := dist_nonneg
  nlinarith

lemma planeRotation_displacement_sq {cosine sine : ℝ}
    (htrig : cosine ^ 2 + sine ^ 2 = 1) (p : R2) :
    dist p (planeRotation cosine sine p) ^ 2 =
      2 * (1 - cosine) * dist p 0 ^ 2 := by
  rw [PiLp.dist_sq_eq_of_L2, PiLp.dist_sq_eq_of_L2]
  simp [Fin.sum_univ_two, planeRotation, pointR2, Real.dist_eq, sq_abs]
  nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]

/-- The doubled-wheel angle has cosine `7/8`. -/
noncomputable def partsPatchCosine : ℝ := 7 / 8

/-- Positive sine of the doubled-wheel angle. -/
noncomputable def partsPatchSine : ℝ := Real.sqrt 15 / 8

lemma partsPatch_trig : partsPatchCosine ^ 2 + partsPatchSine ^ 2 = 1 := by
  have hsqrt : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  rw [partsPatchCosine, partsPatchSine]
  nlinarith

/-- Rotation used to superimpose the second triangular-lattice patch. -/
noncomputable def partsPatchRotation : R2 → R2 :=
  planeRotation partsPatchCosine partsPatchSine

lemma partsPatchRotation_dist_eq (p q : R2) :
    dist (partsPatchRotation p) (partsPatchRotation q) = dist p q :=
  planeRotation_dist_eq partsPatch_trig p q

lemma partsPatchRotation_displacement_sq (p : R2) :
    dist p (partsPatchRotation p) ^ 2 = dist p 0 ^ 2 / 4 := by
  rw [partsPatchRotation, planeRotation_displacement_sq partsPatch_trig,
    partsPatchCosine]
  ring

@[simp] lemma partsPatchRotation_zero : partsPatchRotation 0 = 0 :=
  planeRotation_zero _ _

/-- Apply the doubled-wheel rotation exactly when selecting its second patch. -/
noncomputable def partsApplyPatch (rotated : Bool) (p : R2) : R2 :=
  if rotated then partsPatchRotation p else p

lemma partsApplyPatch_dist_eq (rotated : Bool) (p q : R2) :
    dist (partsApplyPatch rotated p) (partsApplyPatch rotated q) = dist p q := by
  cases rotated <;> simp [partsApplyPatch, partsPatchRotation_dist_eq]

@[simp] lemma partsApplyPatch_zero (rotated : Bool) :
    partsApplyPatch rotated 0 = 0 := by
  cases rotated <;> simp [partsApplyPatch]

/-- Optionally apply the central inversion used by a triangle witness. -/
def partsApplyNegation (negated : Bool) (p : R2) : R2 :=
  if negated then -p else p

lemma partsApplyNegation_dist_eq (negated : Bool) (p q : R2) :
    dist (partsApplyNegation negated p) (partsApplyNegation negated q) =
      dist p q := by
  cases negated <;> simp [partsApplyNegation]

/-- Translate, optionally invert, and optionally rotate a canonical triangle. -/
noncomputable def partsTriangleMotion (rotated : Bool) (centerQ centerR : ℤ)
    (negated : Bool) (p : R2) : R2 :=
  partsApplyPatch rotated
    (partsAxialPoint centerQ centerR + partsApplyNegation negated p)

lemma partsTriangleMotion_dist_eq (rotated : Bool) (centerQ centerR : ℤ)
    (negated : Bool) (p q : R2) :
    dist (partsTriangleMotion rotated centerQ centerR negated p)
        (partsTriangleMotion rotated centerQ centerR negated q) = dist p q := by
  rw [partsTriangleMotion, partsTriangleMotion, partsApplyPatch_dist_eq,
    dist_add_left, partsApplyNegation_dist_eq]

lemma partsTriangleMotion_A (rotated : Bool) (centerQ centerR : ℤ)
    (negated : Bool) :
    partsTriangleMotion rotated centerQ centerR negated partsTriangleA =
      partsApplyPatch rotated
        (partsAxialPoint
          (centerQ + if negated then -1 else 1) centerR) := by
  rw [partsTriangleMotion, partsTriangleA_eq_axial]
  apply congrArg (partsApplyPatch rotated)
  cases negated <;>
    ext i <;> fin_cases i <;>
      simp [partsApplyNegation, partsAxialPoint, pointR2] <;> ring

lemma partsTriangleMotion_B (rotated : Bool) (centerQ centerR : ℤ)
    (negated : Bool) :
    partsTriangleMotion rotated centerQ centerR negated partsTriangleB =
      partsApplyPatch rotated
        (partsAxialPoint centerQ
          (centerR + if negated then 1 else -1)) := by
  rw [partsTriangleMotion, partsTriangleB_eq_axial]
  apply congrArg (partsApplyPatch rotated)
  cases negated <;>
    ext i <;> fin_cases i <;>
      simp [partsApplyNegation, partsAxialPoint, pointR2] <;> ring

lemma partsTriangleMotion_C (rotated : Bool) (centerQ centerR : ℤ)
    (negated : Bool) :
    partsTriangleMotion rotated centerQ centerR negated partsTriangleC =
      partsApplyPatch rotated
        (partsAxialPoint
          (centerQ + if negated then 1 else -1)
          (centerR + if negated then -1 else 1)) := by
  rw [partsTriangleMotion, partsTriangleC_eq_axial]
  apply congrArg (partsApplyPatch rotated)
  cases negated <;>
    ext i <;> fin_cases i <;>
      simp [partsApplyNegation, partsAxialPoint, pointR2] <;> ring

/-- Pull a proper plane coloring back along any distance-preserving map. -/
noncomputable def pullbackUnitDistanceColoring {color : Type*}
    (planeColoring : unitDistanceGraph.Coloring color) (motion : R2 → R2)
    (hdist : ∀ p q, dist (motion p) (motion q) = dist p q) :
    unitDistanceGraph.Coloring color :=
  SimpleGraph.Coloring.mk (fun p => planeColoring (motion p)) (by
    intro p q hadj
    apply planeColoring.valid
    rw [unitDistanceGraph_adj] at hadj ⊢
    have hpq : dist p q = 1 := hadj.2.elim id (fun h => by
      rw [dist_comm]
      exact h)
    constructor
    · intro heq
      have hzero : dist (motion p) (motion q) = 0 := by
        rw [heq]
        exact dist_self _
      rw [hdist] at hzero
      linarith
    · left
      rw [hdist]
      exact hpq)

@[simp] lemma pullbackUnitDistanceColoring_apply {color : Type*}
    (planeColoring : unitDistanceGraph.Coloring color) (motion : R2 → R2)
    (hdist : ∀ p q, dist (motion p) (motion q) = dist p q) (p : R2) :
    pullbackUnitDistanceColoring planeColoring motion hdist p =
      planeColoring (motion p) := rfl

/-- Every rigid image of the checked canonical triangle is non-monochromatic. -/
theorem parts_triangle_motion_not_monochromatic
    (planeColoring : unitDistanceGraph.Coloring (Fin 4))
    (rotated : Bool) (centerQ centerR : ℤ) (negated : Bool) :
    ¬(planeColoring
          (partsTriangleMotion rotated centerQ centerR negated partsTriangleA) =
        planeColoring
          (partsTriangleMotion rotated centerQ centerR negated partsTriangleB) ∧
      planeColoring
          (partsTriangleMotion rotated centerQ centerR negated partsTriangleB) =
        planeColoring
          (partsTriangleMotion rotated centerQ centerR negated partsTriangleC)) := by
  let motion := partsTriangleMotion rotated centerQ centerR negated
  let pulled : unitDistanceGraph.Coloring (Fin 4) :=
    SimpleGraph.Coloring.mk (fun p => planeColoring (motion p)) (by
      intro p q hadj
      apply planeColoring.valid
      rw [unitDistanceGraph_adj] at hadj ⊢
      have hpq : dist p q = 1 := hadj.2.elim id (fun h => by
        rw [dist_comm]
        exact h)
      constructor
      · intro heq
        have hzero : dist (motion p) (motion q) = 0 := by simp [heq]
        dsimp [motion] at hzero
        rw [partsTriangleMotion_dist_eq] at hzero
        linarith
      · left
        dsimp [motion]
        rw [partsTriangleMotion_dist_eq]
        exact hpq)
  intro hmono
  apply parts_canonical_triangle_not_monochromatic pulled
  change planeColoring (motion partsTriangleA) =
      planeColoring (motion partsTriangleB) ∧
    planeColoring (motion partsTriangleB) =
      planeColoring (motion partsTriangleC)
  simpa [motion] using hmono

/-- The final spindle angle has cosine `31/32`. -/
noncomputable def partsSpindleCosine : ℝ := 31 / 32

/-- Positive sine of the final spindle angle. -/
noncomputable def partsSpindleSine : ℝ := Real.sqrt 63 / 32

lemma partsSpindle_trig :
    partsSpindleCosine ^ 2 + partsSpindleSine ^ 2 = 1 := by
  have hsqrt : Real.sqrt 63 ^ 2 = 63 := Real.sq_sqrt (by norm_num)
  rw [partsSpindleCosine, partsSpindleSine]
  nlinarith

/-- Rotation used to close the final spindle. -/
noncomputable def partsSpindleRotation : R2 → R2 :=
  planeRotation partsSpindleCosine partsSpindleSine

lemma partsSpindleRotation_dist_eq (p q : R2) :
    dist (partsSpindleRotation p) (partsSpindleRotation q) = dist p q :=
  planeRotation_dist_eq partsSpindle_trig p q

lemma partsSpindleRotation_displacement_sq (p : R2) :
    dist p (partsSpindleRotation p) ^ 2 = dist p 0 ^ 2 / 16 := by
  rw [partsSpindleRotation, planeRotation_displacement_sq partsSpindle_trig,
    partsSpindleCosine]
  ring

@[simp] lemma partsSpindleRotation_zero : partsSpindleRotation 0 = 0 :=
  planeRotation_zero _ _

end HadwigerNelsonBounds
