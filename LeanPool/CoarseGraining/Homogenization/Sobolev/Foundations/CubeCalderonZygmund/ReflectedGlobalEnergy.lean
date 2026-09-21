/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ReflectedLocalInputs
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.ReflectionL2
import LeanPool.CoarseGraining.Homogenization.Ambient.CoefficientFieldHilbert

/-! # Reflected Global Energy -/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory Set

/-!
# Global energy of the reflected zero extensions

The global stopping argument applies to the zero extensions of the gradient
and of the datum on the reflected parent cube.  This file keeps the exact
`3^d` reflection factor and the `sigma0⁻¹` datum normalization visible in the
real cutoff used at the large scale.
-/

/-- The smallest scale used by the global good-`lambda` stopping argument. -/
noncomputable def reflectedStoppingRadius {d : ℕ} (m : ℤ) (depth : ℕ) : ℝ :=
  cubeRadius (originCube d m) / (10 * (3 : ℝ) ^ depth)

/-- The global squared energy of the two zero-extended reflected fields. -/
noncomputable def reflectedGlobalSquaredEnergy {d : ℕ} (m : ℤ)
    (eps sigma0 : ℝ)
    (uP : H1Function (openCubeSet (originCube d (m + 1))))
    (HP : Vec d → Vec d) : ℝ :=
  (∫ x, ‖reflectedParentGradientExtension m uP x‖ ^ (2 : ℕ) ∂volume) +
    (eps⁻¹) ^ (2 : ℕ) *
      ∫ x, ‖sigma0⁻¹ • hilbertifyVecField (reflectedParentDatumExtension m HP) x‖ ^
        (2 : ℕ) ∂volume

/-- The source-cube expression exactly represented by the global reflected
energy.  The scalar normalization of the datum is deliberately explicit. -/
noncomputable def reflectedSourceSquaredEnergy {d : ℕ} (m : ℤ)
    (eps sigma0 : ℝ)
    (u : H10Function (openCubeSet (originCube d m)))
    (H : Vec d → Vec d) : ℝ :=
  (3 : ℝ) ^ d *
    ((∫ x in openCubeSet (originCube d m),
        ‖hilbertifyVecField u.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume) +
      (eps⁻¹) ^ (2 : ℕ) * (sigma0⁻¹) ^ (2 : ℕ) *
        ∫ x in openCubeSet (originCube d m),
          ‖hilbertifyVecField H x‖ ^ (2 : ℕ) ∂volume)

/-- The real large-scale cutoff for the reflected fields.  In particular, it
contains both the exact outer reflection mass `(3 : ℝ)^d` and the squared
scaled-datum factor `(eps⁻¹)^2 * (sigma0⁻¹)^2`. -/
noncomputable def reflectedGoodLambdaCutoff {d : ℕ} (m : ℤ) (depth : ℕ)
    (eps sigma0 : ℝ)
    (u : H10Function (openCubeSet (originCube d m)))
    (H : Vec d → Vec d) : ℝ :=
  Real.sqrt (((2 * reflectedStoppingRadius (d := d) m depth) ^ d)⁻¹ *
    reflectedSourceSquaredEnergy (d := d) m eps sigma0 u H)

theorem reflectedStoppingRadius_pos {d : ℕ} (m : ℤ) (depth : ℕ) :
    0 < reflectedStoppingRadius (d := d) m depth := by
  unfold reflectedStoppingRadius
  exact div_pos (cubeRadius_pos (originCube d m)) (by positivity)

theorem reflectedGoodLambdaCutoff_nonneg {d : ℕ} (m : ℤ) (depth : ℕ)
    (eps sigma0 : ℝ)
    (u : H10Function (openCubeSet (originCube d m)))
    (H : Vec d → Vec d) :
    0 ≤ reflectedGoodLambdaCutoff m depth eps sigma0 u H := by
  unfold reflectedGoodLambdaCutoff
  exact Real.sqrt_nonneg _

private theorem integral_sqNorm_indicator_hilbertifyVecField
    {d : ℕ} (U : Set (Vec d)) (hU : MeasurableSet U) (G : Vec d → Vec d) :
    ∫ x, ‖U.indicator (hilbertifyVecField G) x‖ ^ (2 : ℕ) ∂volume =
      ∫ x in U, ‖hilbertifyVecField G x‖ ^ (2 : ℕ) ∂volume := by
  have hpoint :
      (fun x : Vec d => ‖U.indicator (hilbertifyVecField G) x‖ ^ (2 : ℕ)) =
        U.indicator (fun x => ‖hilbertifyVecField G x‖ ^ (2 : ℕ)) := by
    funext x
    by_cases hx : x ∈ U
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  rw [hpoint, integral_indicator_eq_integral_restrict hU]

/-- Zero-extending a parent gradient has exactly its parent-cube squared
energy. -/
theorem integral_sqNorm_reflectedParentGradientExtension
    {d : ℕ} (m : ℤ)
    (uP : H1Function (openCubeSet (originCube d (m + 1)))) :
    ∫ x, ‖reflectedParentGradientExtension m uP x‖ ^ (2 : ℕ) ∂volume =
      ∫ x in openCubeSet (originCube d (m + 1)),
        ‖hilbertifyVecField uP.grad x‖ ^ (2 : ℕ)
        ∂volume := by
  simpa only [reflectedParentGradientExtension] using
    integral_sqNorm_indicator_hilbertifyVecField
      (openCubeSet (originCube d (m + 1)))
      (measurableSet_openCubeSet (originCube d (m + 1))) uP.grad

/-- Zero-extending a parent vector datum has exactly its parent-cube squared
energy in the Hilbert realization. -/
theorem integral_sqNorm_hilbertify_reflectedParentDatumExtension
    {d : ℕ} (m : ℤ) (HP : Vec d → Vec d) :
    ∫ x, ‖hilbertifyVecField (reflectedParentDatumExtension m HP) x‖ ^ (2 : ℕ)
        ∂volume =
      ∫ x in openCubeSet (originCube d (m + 1)),
        ‖hilbertifyVecField HP x‖ ^ (2 : ℕ) ∂volume := by
  rw [hilbertifyVecField_reflectedParentDatumExtension]
  exact integral_sqNorm_indicator_hilbertifyVecField
    (openCubeSet (originCube d (m + 1)))
    (measurableSet_openCubeSet (originCube d (m + 1))) HP

theorem integral_sqNorm_reflectedParentGradientExtension_eq_three_pow
    {d : ℕ} {m : ℤ}
    (u : H10Function (openCubeSet (originCube d m)))
    (uP : H1Function (openCubeSet (originCube d (m + 1))))
    (huP : uP.grad = cubeDirichletOddReflectionVectorField (originCube d m)
      (fun y => u.toH1Function.grad y)) :
    ∫ x, ‖reflectedParentGradientExtension m uP x‖ ^ (2 : ℕ) ∂volume =
      (3 : ℝ) ^ d *
        ∫ x in openCubeSet (originCube d m),
          ‖hilbertifyVecField u.toH1Function.grad x‖ ^ (2 : ℕ)
          ∂volume := by
  have hu : MemVectorL2 (openCubeSet (originCube d m))
      (fun y => u.toH1Function.grad y) := by
    simpa only [MemVectorL2, volumeMeasureOn] using u.toH1Function.grad_memVectorL2
  rw [integral_sqNorm_reflectedParentGradientExtension, huP]
  simpa only [hilbertifyVecField, HilbertVec.norm_sq_ofVec] using
    setIntegral_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField_self_pairing_of_memVectorL2_three_pow
      hu

theorem integral_sqNorm_hilbertify_reflectedParentDatumExtension_eq_three_pow
    {d : ℕ} {m : ℤ} (H : Vec d → Vec d) (HP : Vec d → Vec d)
    (hH : MemVectorL2 (openCubeSet (originCube d m)) H)
    (hHP : HP = cubeDirichletOddReflectionVectorField (originCube d m) H) :
    ∫ x, ‖hilbertifyVecField (reflectedParentDatumExtension m HP) x‖ ^ (2 : ℕ)
        ∂volume =
      (3 : ℝ) ^ d *
        ∫ x in openCubeSet (originCube d m),
          ‖hilbertifyVecField H x‖ ^ (2 : ℕ) ∂volume := by
  rw [integral_sqNorm_hilbertify_reflectedParentDatumExtension, hHP]
  simpa only [hilbertifyVecField, HilbertVec.norm_sq_ofVec] using
    setIntegral_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField_self_pairing_of_memVectorL2_three_pow
      hH

/-- The zero extensions are globally square-integrable whenever their parent
fields are square-integrable on the reflected parent cube. -/
theorem memLp_reflectedParentGradientExtension_two
    {d : ℕ} (m : ℤ)
    (uP : H1Function (openCubeSet (originCube d (m + 1)))) :
    MemLp (reflectedParentGradientExtension m uP) 2 volume := by
  rw [show reflectedParentGradientExtension m uP =
      (openCubeSet (originCube d (m + 1))).indicator
        (hilbertifyVecField uP.grad) by rfl,
    memLp_indicator_iff_restrict (measurableSet_openCubeSet (originCube d (m + 1)))]
  exact memHilbertVectorL2_hilbertifyVecField uP.grad_memVectorL2

theorem memLp_hilbertify_reflectedParentDatumExtension_two
    {d : ℕ} (m : ℤ) (HP : Vec d → Vec d)
    (hHP : MemVectorL2 (openCubeSet (originCube d (m + 1))) HP) :
    MemLp (hilbertifyVecField (reflectedParentDatumExtension m HP)) 2 volume := by
  rw [hilbertifyVecField_reflectedParentDatumExtension,
    memLp_indicator_iff_restrict (measurableSet_openCubeSet (originCube d (m + 1)))]
  exact memHilbertVectorL2_hilbertifyVecField hHP

/-- The reflected source datum supplies the global `L²` input needed by the
good-`lambda` stopping construction after extension by zero. -/
theorem memLp_hilbertify_reflectedParentDatumExtension_two_of_reflection
    {d : ℕ} {m : ℤ} (H HP : Vec d → Vec d)
    (hH : MemVectorL2 (openCubeSet (originCube d m)) H)
    (hHP : HP = cubeDirichletOddReflectionVectorField (originCube d m) H) :
    MemLp (hilbertifyVecField (reflectedParentDatumExtension m HP)) 2 volume := by
  apply memLp_hilbertify_reflectedParentDatumExtension_two m HP
  rw [hHP]
  exact memVectorL2_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField hH

/-- The squared gradient of the zero extension is globally integrable. -/
theorem integrable_sqNorm_reflectedParentGradientExtension
    {d : ℕ} (m : ℤ)
    (uP : H1Function (openCubeSet (originCube d (m + 1)))) :
    Integrable (fun x => ‖reflectedParentGradientExtension m uP x‖ ^ (2 : ℕ)) volume :=
  (memLp_reflectedParentGradientExtension_two m uP).integrable_norm_pow (by norm_num)

/-- The squared scaled datum of the zero extension is globally integrable. -/
theorem integrable_sqNorm_smul_hilbertify_reflectedParentDatumExtension
    {d : ℕ} (m : ℤ) (sigma0 : ℝ) (HP : Vec d → Vec d)
    (hHP : MemVectorL2 (openCubeSet (originCube d (m + 1))) HP) :
    Integrable (fun x =>
      ‖sigma0⁻¹ • hilbertifyVecField (reflectedParentDatumExtension m HP) x‖ ^ (2 : ℕ))
      volume := by
  have hmem : MemLp
      (sigma0⁻¹ • hilbertifyVecField (reflectedParentDatumExtension m HP)) 2 volume :=
    (memLp_hilbertify_reflectedParentDatumExtension_two m HP hHP).const_smul sigma0⁻¹
  exact hmem.integrable_norm_pow (by norm_num)

theorem integrable_sqNorm_smul_hilbertify_reflectedParentDatumExtension_of_reflection
    {d : ℕ} {m : ℤ} (sigma0 : ℝ) (H HP : Vec d → Vec d)
    (hH : MemVectorL2 (openCubeSet (originCube d m)) H)
    (hHP : HP = cubeDirichletOddReflectionVectorField (originCube d m) H) :
    Integrable (fun x =>
      ‖sigma0⁻¹ • hilbertifyVecField (reflectedParentDatumExtension m HP) x‖ ^ (2 : ℕ))
      volume := by
  have hmem : MemLp
      (sigma0⁻¹ • hilbertifyVecField (reflectedParentDatumExtension m HP)) 2 volume :=
    (memLp_hilbertify_reflectedParentDatumExtension_two_of_reflection H HP hH hHP).const_smul
      sigma0⁻¹
  exact hmem.integrable_norm_pow (by norm_num)

/-- The exact scalar rescaling of the reflected datum energy. -/
theorem integral_sqNorm_smul_hilbertify_reflectedParentDatumExtension_eq_three_pow
    {d : ℕ} {m : ℤ} {sigma0 : ℝ} (hsigma0 : 0 < sigma0)
    (H : Vec d → Vec d) (HP : Vec d → Vec d)
    (hH : MemVectorL2 (openCubeSet (originCube d m)) H)
    (hHP : HP = cubeDirichletOddReflectionVectorField (originCube d m) H) :
    ∫ x, ‖sigma0⁻¹ • hilbertifyVecField (reflectedParentDatumExtension m HP) x‖ ^
        (2 : ℕ) ∂volume =
      (sigma0⁻¹) ^ (2 : ℕ) * (3 : ℝ) ^ d *
        ∫ x in openCubeSet (originCube d m),
          ‖hilbertifyVecField H x‖ ^ (2 : ℕ) ∂volume := by
  have hpoint :
      (fun x : Vec d =>
        ‖sigma0⁻¹ • hilbertifyVecField (reflectedParentDatumExtension m HP) x‖ ^
          (2 : ℕ)) =
        fun x => (sigma0⁻¹) ^ (2 : ℕ) *
          ‖hilbertifyVecField (reflectedParentDatumExtension m HP) x‖ ^ (2 : ℕ) := by
    funext x
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hsigma0.le)]
    ring
  rw [hpoint, MeasureTheory.integral_const_mul,
    integral_sqNorm_hilbertify_reflectedParentDatumExtension_eq_three_pow H HP hH hHP]
  ring

/-- The global squared energy of the zero-extended reflected fields is
exactly `3^d` times the Euclidean source-cube energy, including the scaled
datum factor. -/
theorem reflectedGlobalSquaredEnergy_eq_reflectedSourceSquaredEnergy
    {d : ℕ} {m : ℤ} {eps sigma0 : ℝ} (hsigma0 : 0 < sigma0)
    (u : H10Function (openCubeSet (originCube d m)))
    (uP : H1Function (openCubeSet (originCube d (m + 1))))
    (H HP : Vec d → Vec d)
    (hH : MemVectorL2 (openCubeSet (originCube d m)) H)
    (huP : uP.grad = cubeDirichletOddReflectionVectorField (originCube d m)
      (fun y => u.toH1Function.grad y))
    (hHP : HP = cubeDirichletOddReflectionVectorField (originCube d m) H) :
    reflectedGlobalSquaredEnergy m eps sigma0 uP HP =
      reflectedSourceSquaredEnergy m eps sigma0 u H := by
  unfold reflectedGlobalSquaredEnergy reflectedSourceSquaredEnergy
  rw [integral_sqNorm_reflectedParentGradientExtension_eq_three_pow u uP huP,
    integral_sqNorm_smul_hilbertify_reflectedParentDatumExtension_eq_three_pow
      hsigma0 H HP hH hHP]
  ring

/-- The source-facing large-scale cutoff is exactly the cutoff formed from
the global energy of the actual zero extensions. -/
theorem reflectedGoodLambdaCutoff_eq_globalEnergy
    {d : ℕ} {m : ℤ} {depth : ℕ} {eps sigma0 : ℝ} (hsigma0 : 0 < sigma0)
    (u : H10Function (openCubeSet (originCube d m)))
    (uP : H1Function (openCubeSet (originCube d (m + 1))))
    (H HP : Vec d → Vec d)
    (hH : MemVectorL2 (openCubeSet (originCube d m)) H)
    (huP : uP.grad = cubeDirichletOddReflectionVectorField (originCube d m)
      (fun y => u.toH1Function.grad y))
    (hHP : HP = cubeDirichletOddReflectionVectorField (originCube d m) H) :
    reflectedGoodLambdaCutoff m depth eps sigma0 u H =
      Real.sqrt (((2 * reflectedStoppingRadius (d := d) m depth) ^ d)⁻¹ *
        reflectedGlobalSquaredEnergy m eps sigma0 uP HP) := by
  unfold reflectedGoodLambdaCutoff
  rw [reflectedGlobalSquaredEnergy_eq_reflectedSourceSquaredEnergy
    hsigma0 u uP H HP hH huP hHP]

/-- A nontrivial source energy makes the large-scale cutoff strictly positive.
This is intentionally conditional: zero source data have zero cutoff. -/
theorem reflectedGoodLambdaCutoff_pos_of_sourceSquaredEnergy_pos
    {d : ℕ} (m : ℤ) (depth : ℕ) (eps sigma0 : ℝ)
    (u : H10Function (openCubeSet (originCube d m))) (H : Vec d → Vec d)
    (henergy : 0 < reflectedSourceSquaredEnergy m eps sigma0 u H) :
    0 < reflectedGoodLambdaCutoff m depth eps sigma0 u H := by
  unfold reflectedGoodLambdaCutoff
  apply Real.sqrt_pos.2
  have hrho : 0 < reflectedStoppingRadius (d := d) m depth :=
    reflectedStoppingRadius_pos m depth
  exact mul_pos (inv_pos.mpr (pow_pos (mul_pos (by norm_num) hrho) _)) henergy

end CubeCalderonZygmund

end

end Homogenization
