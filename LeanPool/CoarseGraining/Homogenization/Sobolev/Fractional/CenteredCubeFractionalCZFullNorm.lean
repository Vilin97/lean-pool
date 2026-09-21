/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.CenteredCubeFractionalCZ

/-!
# Full-norm fractional Calderón--Zygmund estimate on centered cubes

The homogeneous fractional estimate and the normalized finite-`L^p` estimate
combine into the source-facing inhomogeneous fractional-Sobolev estimate.
The combination is carried out at the powered full norm, so its constant is
uniform in the cube, fractional order, and coefficient scale.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem cubeEuclideanWspFullENorm_le_of_component_bounds
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder)
    (q : FiniteLpExponent) (F G : Vec d → Vec d) (A : ℝ≥0∞)
    (hLp :
      (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm q.exponent F ≤
        A * (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm q.exponent G)
    (hSemi : cubeEuclideanWspESeminorm Q s q F ≤
      A * cubeEuclideanWspESeminorm Q s q G) :
    cubeEuclideanWspFullENorm Q s q F ≤ A * cubeEuclideanWspFullENorm Q s q G := by
  let W := cubeEuclideanWspScalePowerWeight Q s q
  let LF := (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm q.exponent F
  let LG := (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm q.exponent G
  let SF := cubeEuclideanWspESeminorm Q s q F
  let SG := cubeEuclideanWspESeminorm Q s q G
  let t := q.exponent.toReal
  have ht : 0 < t :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one q.one_lt)) q.lt_top.ne
  have hLpPower : LF ^ t ≤ (A * LG) ^ t :=
    ENNReal.rpow_le_rpow (by simpa only [LF, LG] using hLp) ht.le
  have hSemiPower : SF ^ t ≤ (A * SG) ^ t :=
    ENNReal.rpow_le_rpow (by simpa only [SF, SG] using hSemi) ht.le
  have hFirst : W * LF ^ t ≤ A ^ t * (W * LG ^ t) := by
    calc
      W * LF ^ t ≤ W * (A * LG) ^ t := by
        simpa only [mul_comm] using mul_le_mul_left hLpPower W
      _ = A ^ t * (W * LG ^ t) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ ht.le]
        ring
  have hSecond : SF ^ t ≤ A ^ t * SG ^ t := by
    calc
      SF ^ t ≤ (A * SG) ^ t := hSemiPower
      _ = A ^ t * SG ^ t := ENNReal.mul_rpow_of_nonneg _ _ ht.le
  have hPower : W * LF ^ t + SF ^ t ≤ A ^ t * (W * LG ^ t + SG ^ t) := by
    calc
      W * LF ^ t + SF ^ t ≤ A ^ t * (W * LG ^ t) + A ^ t * SG ^ t :=
        add_le_add hFirst hSecond
      _ = A ^ t * (W * LG ^ t + SG ^ t) := by ring
  have hRoot := ENNReal.rpow_le_rpow hPower (inv_nonneg.mpr ht.le)
  rw [cubeEuclideanWspFullENorm]
  change (W * LF ^ t + SF ^ t) ^ t⁻¹ ≤
    A * (W * LG ^ t + SG ^ t) ^ t⁻¹
  calc
    (W * LF ^ t + SF ^ t) ^ t⁻¹ ≤
        (A ^ t * (W * LG ^ t + SG ^ t)) ^ t⁻¹ := hRoot
    _ = A * (W * LG ^ t + SG ^ t) ^ t⁻¹ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr ht.le),
        ← ENNReal.rpow_mul, mul_inv_cancel₀ ht.ne', ENNReal.rpow_one]

/-- A supplied zero-trace centered-cube divergence solution with fractional
`L² ∩ L^q` datum satisfies the full fractional-Sobolev Calderón--Zygmund
estimate.  The constant is fixed before all scale, order, datum, and solution
parameters. -/
theorem centeredCubeH10ScalarDivergence_fractional_cz_full
    (d : ℕ) [NeZero d] (q : FiniteLpExponent) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m : ℤ) (sigma0 : ℝ) (s : FractionalOrder)
        (h : CubeEuclideanWspL2Field (originCube d m) s q)
        (w : H10Function (openCubeSet (originCube d m))),
        0 < sigma0 →
        IsCenteredCubeH10ScalarDivergenceSolution m sigma0 w h.toLpTwo →
          cubeEuclideanWspFullENorm (originCube d m) s q w.toH1Function.grad ≤
            C * (ENNReal.ofReal sigma0)⁻¹ *
              cubeEuclideanWspFullENorm (originCube d m) s q h.toField := by
  obtain ⟨CLp, hCLp_top, hCLp⟩ :=
    CubeCalderonZygmund.centeredCubeH10ScalarDivergence_cz d q
  obtain ⟨CSemi, hCSemi_top, hCSemi⟩ :=
    centeredCubeH10ScalarDivergence_fractional_cz d q
  let C : ℝ≥0∞ := CLp + CSemi
  refine ⟨C, ENNReal.add_lt_top.mpr ⟨hCLp_top, hCSemi_top⟩, ?_⟩
  intro m sigma0 s h w hsigma0 hsolution
  let Q : TriadicCube d := originCube d m
  let hField : CubeEuclideanL2LpField Q q :=
    { toField := h.toField
      euclideanMemLp := h.euclideanMemLp
      euclideanMemL2 := h.euclideanMemL2 }
  have hLpRaw := hCLp m sigma0 hField w hsigma0 (by
    simpa only [Q, hField] using! hsolution)
  have hLp :
      (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm q.exponent
          w.toH1Function.grad ≤
        (C * (ENNReal.ofReal sigma0)⁻¹) *
          (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm q.exponent
            h.toField := by
    calc
      (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm q.exponent
          w.toH1Function.grad ≤
          CLp * (ENNReal.ofReal sigma0)⁻¹ *
            (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm q.exponent
              h.toField := by
          simpa only [Q, centeredCubeDomain] using hLpRaw
      _ ≤ (C * (ENNReal.ofReal sigma0)⁻¹) *
            (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm q.exponent
              h.toField := by
          gcongr
          exact le_add_right (le_refl CLp)
  obtain ⟨gradW, hgradW, hSemiRaw⟩ := hCSemi m sigma0 s h w hsigma0 hsolution
  have hSemi : cubeEuclideanWspESeminorm Q s q w.toH1Function.grad ≤
      (C * (ENNReal.ofReal sigma0)⁻¹) *
        cubeEuclideanWspESeminorm Q s q h.toField := by
    calc
      cubeEuclideanWspESeminorm Q s q w.toH1Function.grad ≤
          CSemi * (ENNReal.ofReal sigma0)⁻¹ *
            cubeEuclideanWspESeminorm Q s q h.toField := by
          simpa only [Q, hgradW] using hSemiRaw
      _ ≤ (C * (ENNReal.ofReal sigma0)⁻¹) *
            cubeEuclideanWspESeminorm Q s q h.toField := by
          gcongr
          exact le_add_left (le_refl CSemi)
  have hFull := cubeEuclideanWspFullENorm_le_of_component_bounds Q s q
    w.toH1Function.grad h.toField (C * (ENNReal.ofReal sigma0)⁻¹) hLp hSemi
  simpa only [Q, mul_assoc] using hFull

end

end Homogenization
