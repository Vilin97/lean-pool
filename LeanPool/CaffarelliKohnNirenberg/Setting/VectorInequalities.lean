/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.H1
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.Smooth
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Scaling
public import LeanPool.CaffarelliKohnNirenberg.Statements.Alpha
public import LeanPool.CaffarelliKohnNirenberg.Statements.Beta
public import LeanPool.CaffarelliKohnNirenberg.Statements.Gamma
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradientSq
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable

/-!
# Vector Inequalities

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

noncomputable section
namespace CKN

/-! ## Componentwise vector estimates -/

/-- The time-integrated cubed interpolation estimate applied to each velocity component.

This estimate uses the larger ball of radius `2 * r` for the input norms.
For finite-constant interpolation on a single ball, see
`CKN.interpolationBall_finite` in `CKN.Setting.InterpolationBall`. -/
theorem vector_h1_interpolation_cylinder_l3_componentwise
    {x₀ : Vec3} {r t : ℝ} (hr : 0 < r) (u : ℝ → Vec3 → Vec3)
    (hu : ∀ _i : Fin 3, ℝ → H1Function (euclideanBall x₀ (2 * r)))
    (hcomp : ∀ (i : Fin 3) (s : ℝ), (hu i s).toFun = fun x => u s x i)
    (i : Fin 3) :
    ∫⁻ s in Set.Ioc (t - r ^ 2) t,
        lpNormOn 3 (euclideanBall x₀ r) (fun x => u s x i) ^ (3 : ℕ) ≤
      ∫⁻ s in Set.Ioc (t - r ^ 2) t,
        localSobolevConstant ^ (3 / 2 : ℝ) *
          lpNormOn 2 (euclideanBall x₀ (2 * r)) (fun x => u s x i) ^ (3 / 2 : ℝ) *
            (weakGradientLpNormOn 2 (euclideanBall x₀ (2 * r)) (hu i s).grad +
              (Real.toNNReal (32 / r) : ℝ≥0∞) *
                lpNormOn 2 (euclideanBall x₀ (2 * r)) (fun x => u s x i)) ^
              (3 / 2 : ℝ) := by
  have h := h1InterpolationCylinderL3 (t := t) hr (u := hu i)
  simpa only [hcomp i] using h

/-! ## Scale quantities -/

/-- Algebraic translation of a scale-normalized cylinder interpolation estimate into the
`γ`, `α`, and `β` quantities.

The hypothesis is the vector-valued cylinder estimate produced by the analytic lift.  It
is stated as a cube of the desired right-hand side, with the input scale
quantities evaluated at `2 * r`.  The single-ball analytic estimate is available
as `CKN.interpolationBall_three_finite` in `CKN.Setting.InterpolationBall`. -/
theorem gamma_le_of_scale_normalized_interpolation
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (_ : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r C : ℝ} (hr : 0 < r)
    (_ : closure (parabolicCylinder z.1 z.2 (2 * r)) ⊆ spaceTimeSet Ω I)
    (hC : 0 ≤ C)
    (hα : 0 ≤ alpha u z (2 * r)) (hβ : 0 ≤ beta u Du z (2 * r))
    (hfinite :
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ⊤)
    (hinterpolation :
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≤
        ENNReal.ofReal (r ^ (2 : ℝ) *
          (C * alpha u z (2 * r) ^ (1 / 2 : ℝ) * beta u Du z (2 * r) ^ (1 / 2 : ℝ) +
            C * alpha u z (2 * r)) ^ (3 : ℝ))) :
    gamma u z r ≤
      C * alpha u z (2 * r) ^ (1 / 2 : ℝ) * beta u Du z (2 * r) ^ (1 / 2 : ℝ) +
        C * alpha u z (2 * r) := by
  let A : ℝ := alpha u z (2 * r)
  let B : ℝ := beta u Du z (2 * r)
  let M : ℝ := C * A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) + C * A
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hto :
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal ≤
        r ^ (2 : ℝ) * M ^ (3 : ℝ) := by
    have hto' :=
      (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).mpr hinterpolation
    calc
      _ ≤ (ENNReal.ofReal (r ^ (2 : ℝ) *
          (C * alpha u z (2 * r) ^ (1 / 2 : ℝ) * beta u Du z (2 * r) ^ (1 / 2 : ℝ) +
            C * alpha u z (2 * r)) ^ (3 : ℝ))).toReal := hto'
      _ = r ^ (2 : ℝ) * M ^ (3 : ℝ) := by
        have hnonneg : 0 ≤ r ^ (2 : ℝ) *
            (C * alpha u z (2 * r) ^ (1 / 2 : ℝ) * beta u Du z (2 * r) ^
                (1 / 2 : ℝ) + C * alpha u z (2 * r)) ^ (3 : ℝ) := by
          positivity
        rw [ENNReal.toReal_ofReal hnonneg]
  have hscaled :
      r ^ (-2 : ℝ) *
          (∫⁻ w in parabolicCylinder z.1 z.2 r,
            ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal ≤
        M ^ (3 : ℝ) := by
    calc
      r ^ (-2 : ℝ) *
          (∫⁻ w in parabolicCylinder z.1 z.2 r,
            ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal ≤
          r ^ (-2 : ℝ) * (r ^ (2 : ℝ) * M ^ (3 : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hto (Real.rpow_nonneg (le_of_lt hr) _)
      _ = M ^ (3 : ℝ) := by
        rw [← mul_assoc, ← Real.rpow_add hr]
        norm_num
  change (r ^ (-2 : ℝ) *
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal) ^
      (1 / 3 : ℝ) ≤ _
  calc
    _ ≤ (M ^ (3 : ℝ)) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hscaled (by norm_num)
    _ = M := by
      rw [← Real.rpow_mul hM]
      norm_num
    _ = C * alpha u z (2 * r) ^ (1 / 2 : ℝ) * beta u Du z (2 * r) ^ (1 / 2 : ℝ) +
        C * alpha u z (2 * r) := by rfl

end CKN
