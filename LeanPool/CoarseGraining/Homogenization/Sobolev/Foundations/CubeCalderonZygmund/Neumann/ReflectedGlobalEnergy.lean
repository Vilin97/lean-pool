/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.Neumann.ReflectionWeakEquation
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ReflectedGlobalEnergy

/-!
# Global energy for centered-Neumann even reflection

The centered-Neumann good-`lambda` argument uses the same parent-cube zero
extensions as the Dirichlet argument, but the solution gradient and datum are
transported by the coordinate-fold even reflection.  This file identifies the
actual global energy of those extensions with its source-cube expression.
-/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory

/-- Source-cube squared energy represented by the zero-extended Neumann even
reflections on the centered parent. -/
noncomputable def neumannReflectedSourceSquaredEnergy {d : ℕ} (m : ℤ)
    (eps sigma0 : ℝ)
    (u : H1MeanZeroFunction (openCubeSet (originCube d m)))
    (H : Vec d → Vec d) : ℝ :=
  (3 : ℝ) ^ d *
    ((∫ x in openCubeSet (originCube d m),
        ‖hilbertifyVecField u.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume) +
      (eps⁻¹) ^ (2 : ℕ) * (sigma0⁻¹) ^ (2 : ℕ) *
        ∫ x in openCubeSet (originCube d m),
          ‖hilbertifyVecField H x‖ ^ (2 : ℕ) ∂volume)

/-- Natural large-scale cutoff formed from the exact reflected Neumann
source energy. -/
noncomputable def neumannReflectedGoodLambdaCutoff {d : ℕ} (m : ℤ)
    (depth : ℕ) (eps sigma0 : ℝ)
    (u : H1MeanZeroFunction (openCubeSet (originCube d m)))
    (H : Vec d → Vec d) : ℝ :=
  Real.sqrt (((2 * reflectedStoppingRadius (d := d) m depth) ^ d)⁻¹ *
    neumannReflectedSourceSquaredEnergy (d := d) m eps sigma0 u H)

theorem neumannReflectedGoodLambdaCutoff_nonneg {d : ℕ} (m : ℤ)
    (depth : ℕ) (eps sigma0 : ℝ)
    (u : H1MeanZeroFunction (openCubeSet (originCube d m)))
    (H : Vec d → Vec d) :
    0 ≤ neumannReflectedGoodLambdaCutoff m depth eps sigma0 u H := by
  unfold neumannReflectedGoodLambdaCutoff
  exact Real.sqrt_nonneg _

/-- The zero-extended gradient of an even-reflected centered-Neumann solution
has exactly `3^d` times its source-cube squared energy. -/
theorem integral_sqNorm_reflectedParentGradientExtension_eq_three_pow_of_evenReflection
    {d : ℕ} {m : ℤ}
    (u : H1MeanZeroFunction (openCubeSet (originCube d m)))
    (uP : H1Function (openCubeSet (originCube d (m + 1))))
    (huP : uP.grad = cubeCoordinateFoldReflectedVectorField (originCube d m)
      (fun y ↦ u.toH1Function.grad y)) :
    ∫ x, ‖reflectedParentGradientExtension m uP x‖ ^ (2 : ℕ) ∂volume =
      (3 : ℝ) ^ d *
        ∫ x in openCubeSet (originCube d m),
          ‖hilbertifyVecField u.toH1Function.grad x‖ ^ (2 : ℕ)
          ∂volume := by
  have hu : MemVectorL2 (openCubeSet (originCube d m))
      (fun y ↦ u.toH1Function.grad y) := by
    simpa only [MemVectorL2, volumeMeasureOn] using
      u.toH1Function.grad_memVectorL2
  rw [integral_sqNorm_reflectedParentGradientExtension, huP]
  simpa only [hilbertifyVecField, HilbertVec.norm_sq_ofVec] using
    setIntegral_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField_self_pairing_of_memVectorL2_three_pow
      hu

/-- The zero-extended even-reflected datum has exactly `3^d` times its
source-cube squared energy. -/
theorem integral_sqNorm_hilbertify_reflectedParentDatumExtension_eq_three_pow_of_evenReflection
    {d : ℕ} {m : ℤ} (H HP : Vec d → Vec d)
    (hH : MemVectorL2 (openCubeSet (originCube d m)) H)
    (hHP : HP = cubeCoordinateFoldReflectedVectorField (originCube d m) H) :
    ∫ x, ‖hilbertifyVecField (reflectedParentDatumExtension m HP) x‖ ^
        (2 : ℕ) ∂volume =
      (3 : ℝ) ^ d *
        ∫ x in openCubeSet (originCube d m),
          ‖hilbertifyVecField H x‖ ^ (2 : ℕ) ∂volume := by
  rw [integral_sqNorm_hilbertify_reflectedParentDatumExtension, hHP]
  simpa only [hilbertifyVecField, HilbertVec.norm_sq_ofVec] using
    setIntegral_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField_self_pairing_of_memVectorL2_three_pow
      hH

/-- The even-reflected source datum is globally square-integrable after
parent restriction and extension by zero. -/
theorem memLp_hilbertify_reflectedParentDatumExtension_two_of_evenReflection
    {d : ℕ} {m : ℤ} (H HP : Vec d → Vec d)
    (hH : MemVectorL2 (openCubeSet (originCube d m)) H)
    (hHP : HP = cubeCoordinateFoldReflectedVectorField (originCube d m) H) :
    MemLp (hilbertifyVecField (reflectedParentDatumExtension m HP)) 2 volume := by
  apply memLp_hilbertify_reflectedParentDatumExtension_two m HP
  rw [hHP]
  exact
    memVectorL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField
      hH

/-- Exact scalar rescaling of the even-reflected datum energy. -/
theorem integral_sqNorm_smul_hilbertify_reflectedParentDatumExtension_eq_three_pow_of_evenReflection
    {d : ℕ} {m : ℤ} {sigma0 : ℝ} (hsigma0 : 0 < sigma0)
    (H HP : Vec d → Vec d)
    (hH : MemVectorL2 (openCubeSet (originCube d m)) H)
    (hHP : HP = cubeCoordinateFoldReflectedVectorField (originCube d m) H) :
    ∫ x, ‖sigma0⁻¹ •
        hilbertifyVecField (reflectedParentDatumExtension m HP) x‖ ^
        (2 : ℕ) ∂volume =
      (sigma0⁻¹) ^ (2 : ℕ) * (3 : ℝ) ^ d *
        ∫ x in openCubeSet (originCube d m),
          ‖hilbertifyVecField H x‖ ^ (2 : ℕ) ∂volume := by
  have hpoint :
      (fun x : Vec d ↦
        ‖sigma0⁻¹ •
          hilbertifyVecField (reflectedParentDatumExtension m HP) x‖ ^
          (2 : ℕ)) =
        fun x ↦ (sigma0⁻¹) ^ (2 : ℕ) *
          ‖hilbertifyVecField (reflectedParentDatumExtension m HP) x‖ ^
            (2 : ℕ) := by
    funext x
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hsigma0.le)]
    ring
  rw [hpoint, MeasureTheory.integral_const_mul,
    integral_sqNorm_hilbertify_reflectedParentDatumExtension_eq_three_pow_of_evenReflection
      H HP hH hHP]
  ring

/-- The global squared energy of the actual zero extensions agrees exactly
with the centered-Neumann source energy. -/
theorem reflectedGlobalSquaredEnergy_eq_neumannReflectedSourceSquaredEnergy
    {d : ℕ} {m : ℤ} {eps sigma0 : ℝ} (hsigma0 : 0 < sigma0)
    (u : H1MeanZeroFunction (openCubeSet (originCube d m)))
    (uP : H1Function (openCubeSet (originCube d (m + 1))))
    (H HP : Vec d → Vec d)
    (hH : MemVectorL2 (openCubeSet (originCube d m)) H)
    (huP : uP.grad = cubeCoordinateFoldReflectedVectorField (originCube d m)
      (fun y ↦ u.toH1Function.grad y))
    (hHP : HP = cubeCoordinateFoldReflectedVectorField (originCube d m) H) :
    reflectedGlobalSquaredEnergy m eps sigma0 uP HP =
      neumannReflectedSourceSquaredEnergy m eps sigma0 u H := by
  unfold reflectedGlobalSquaredEnergy neumannReflectedSourceSquaredEnergy
  rw [integral_sqNorm_reflectedParentGradientExtension_eq_three_pow_of_evenReflection
      u uP huP,
    integral_sqNorm_smul_hilbertify_reflectedParentDatumExtension_eq_three_pow_of_evenReflection
      hsigma0 H HP hH hHP]
  ring

/-- The source-facing Neumann cutoff is exactly the cutoff formed from the
global energy of the actual zero extensions. -/
theorem neumannReflectedGoodLambdaCutoff_eq_globalEnergy
    {d : ℕ} {m : ℤ} {depth : ℕ} {eps sigma0 : ℝ}
    (hsigma0 : 0 < sigma0)
    (u : H1MeanZeroFunction (openCubeSet (originCube d m)))
    (uP : H1Function (openCubeSet (originCube d (m + 1))))
    (H HP : Vec d → Vec d)
    (hH : MemVectorL2 (openCubeSet (originCube d m)) H)
    (huP : uP.grad = cubeCoordinateFoldReflectedVectorField (originCube d m)
      (fun y ↦ u.toH1Function.grad y))
    (hHP : HP = cubeCoordinateFoldReflectedVectorField (originCube d m) H) :
    neumannReflectedGoodLambdaCutoff m depth eps sigma0 u H =
      Real.sqrt (((2 * reflectedStoppingRadius (d := d) m depth) ^ d)⁻¹ *
        reflectedGlobalSquaredEnergy m eps sigma0 uP HP) := by
  unfold neumannReflectedGoodLambdaCutoff
  rw [reflectedGlobalSquaredEnergy_eq_neumannReflectedSourceSquaredEnergy
    hsigma0 u uP H HP hH huP hHP]

end CubeCalderonZygmund

end

end Homogenization
