/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI GPT-5.6 Sol, Jon Crall
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.TwoDimensionalSingularValues

/-!
# Davis--Kahan 1970, Examples 4.1 and 4.2

The two worked examples immediately following Proposition 4.3 are mathematical
counterexamples, not merely exposition.  They show respectively that the
full-displacement minimum can fail for the Ky Fan two norm beyond `pi / 3` in
real two-space, and that it can fail even at arbitrarily small phase perturbation
in complex two-space.

The complex calculation is written in an eigenbasis of the planar direct
rotation.  In that basis the direct rotation is `diag(e^{i theta},e^{-i theta})`;
multiplication by the global phase `e^{i delta}` gives the source competitor
`V = e^{i delta} U` without changing its singular values.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section4Examples

open scoped InnerProductSpace BigOperators
open Module (finrank)

noncomputable section

/-- The two-dimensional real model space of the Section 4 examples. -/
abbrev RealPlane := EuclideanSpace ℝ (Fin 2)
/-- The two-dimensional complex model space of the Section 4 examples. -/
abbrev ComplexPlane := EuclideanSpace ℂ (Fin 2)

/-! ## Shared two-dimensional coordinate calculations -/

private theorem real_entry (M : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    (Matrix.toEuclideanLin M) (EuclideanSpace.basisFun (Fin 2) ℝ i) j = M j i := by
  simp [Matrix.toLpLin_apply, EuclideanSpace.basisFun_apply, Matrix.mulVec_single]

private theorem real_norm_sq (x : RealPlane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

private theorem real_inner (x y : RealPlane) :
    ⟪x, y⟫_ℝ = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

private theorem real_gramTrace (M : Matrix (Fin 2) (Fin 2) ℝ) :
    TauCeti.gramTraceFinTwo (Matrix.toEuclideanLin M) =
      M 0 0 ^ 2 + M 1 0 ^ 2 + (M 0 1 ^ 2 + M 1 1 ^ 2) := by
  show ∑ i : Fin 2,
    ‖(Matrix.toEuclideanLin M) (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ^ 2 = _
  rw [Fin.sum_univ_two, real_norm_sq, real_norm_sq]
  rw [real_entry, real_entry, real_entry, real_entry]

private theorem real_gramDet (M : Matrix (Fin 2) (Fin 2) ℝ) :
    TauCeti.gramDetFinTwo (Matrix.toEuclideanLin M) =
      (M 0 0 * M 1 1 - M 0 1 * M 1 0) ^ 2 := by
  show ‖(Matrix.toEuclideanLin M) (EuclideanSpace.basisFun (Fin 2) ℝ 0)‖ ^ 2 *
      ‖(Matrix.toEuclideanLin M) (EuclideanSpace.basisFun (Fin 2) ℝ 1)‖ ^ 2 -
      ‖⟪(Matrix.toEuclideanLin M) (EuclideanSpace.basisFun (Fin 2) ℝ 0),
        (Matrix.toEuclideanLin M) (EuclideanSpace.basisFun (Fin 2) ℝ 1)⟫_ℝ‖ ^ 2 = _
  rw [real_norm_sq, real_norm_sq, real_inner, Real.norm_eq_abs, sq_abs]
  rw [real_entry, real_entry, real_entry, real_entry]
  ring

private theorem half_chord_sq (theta : ℝ) :
    (1 - Real.cos theta) ^ 2 + Real.sin theta ^ 2 =
      (2 * Real.sin (theta / 2)) ^ 2 := by
  have hpy := Real.sin_sq_add_cos_sq theta
  have hhalf := Real.sin_sq_add_cos_sq (theta / 2)
  have hdouble :
      Real.cos theta = 1 - 2 * Real.sin (theta / 2) ^ 2 := by
    have htheta : theta = theta / 2 + theta / 2 := by ring
    calc
      Real.cos theta = Real.cos (theta / 2 + theta / 2) := by rw [← htheta]
      _ = Real.cos (theta / 2) * Real.cos (theta / 2) -
          Real.sin (theta / 2) * Real.sin (theta / 2) := by rw [Real.cos_add]
      _ = 1 - 2 * Real.sin (theta / 2) ^ 2 := by nlinarith
  nlinarith

private theorem sin_half_nonneg {theta : ℝ} (h0 : 0 ≤ theta)
    (hpi : theta ≤ Real.pi / 2) :
    0 ≤ Real.sin (theta / 2) := by
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
    (by linarith [Real.pi_pos])

/-! ## Example 4.1: the real reflection -/

/-- The source's planar direct rotation `U`. -/
def example41DirectRotation (theta : ℝ) : RealPlane →ₗ[ℝ] RealPlane :=
  Matrix.toEuclideanLin
    !![Real.cos theta, -Real.sin theta;
       Real.sin theta,  Real.cos theta]

/-- The source's competing reflection, exchanging the two one-dimensional
subspaces separated by angle `theta`. -/
def example41Reflection (theta : ℝ) : RealPlane →ₗ[ℝ] RealPlane :=
  Matrix.toEuclideanLin
    !![Real.cos theta, Real.sin theta;
       Real.sin theta, -Real.cos theta]

/-- Coordinate matrix of `1 - U`. -/
def example41DirectDisplacement (theta : ℝ) : RealPlane →ₗ[ℝ] RealPlane :=
  Matrix.toEuclideanLin
    !![1 - Real.cos theta, Real.sin theta;
       -Real.sin theta, 1 - Real.cos theta]

/-- Coordinate matrix of `1 - V` for the reflecting competitor. -/
def example41ReflectionDisplacement (theta : ℝ) : RealPlane →ₗ[ℝ] RealPlane :=
  Matrix.toEuclideanLin
    !![1 - Real.cos theta, -Real.sin theta;
       -Real.sin theta, 1 + Real.cos theta]

private def example41DirectDisplacementMatrix (theta : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - Real.cos theta, Real.sin theta;
     -Real.sin theta, 1 - Real.cos theta]

private def example41ReflectionDisplacementMatrix (theta : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - Real.cos theta, -Real.sin theta;
     -Real.sin theta, 1 + Real.cos theta]

private theorem example41DirectDisplacement_eq_matrix (theta : ℝ) :
    example41DirectDisplacement theta =
      Matrix.toEuclideanLin (example41DirectDisplacementMatrix theta) := rfl

private theorem example41ReflectionDisplacement_eq_matrix (theta : ℝ) :
    example41ReflectionDisplacement theta =
      Matrix.toEuclideanLin (example41ReflectionDisplacementMatrix theta) := rfl

/-- The displacement of Example 4.1's direct rotation, as an explicit matrix. -/
@[simp] theorem one_sub_example41DirectRotation (theta : ℝ) :
    LinearMap.id - example41DirectRotation theta = example41DirectDisplacement theta := by
  ext x i
  fin_cases i <;>
    simp [example41DirectRotation, example41DirectDisplacement,
      Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail] <;>
    ring

/-- The displacement of Example 4.1's reflection, as an explicit matrix. -/
@[simp] theorem one_sub_example41Reflection (theta : ℝ) :
    LinearMap.id - example41Reflection theta = example41ReflectionDisplacement theta := by
  ext x i
  fin_cases i <;>
    simp [example41Reflection, example41ReflectionDisplacement,
      Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail] <;>
    ring

/-- Example 4.1's direct rotation has the two equal chord singular values
`2 sin(theta/2)`. -/
theorem example4_1_directRotation_singularValues
    {theta : ℝ} (h0 : 0 ≤ theta) (hpi : theta ≤ Real.pi / 2) :
    (LinearMap.id - example41DirectRotation theta).singularValues =
      TauCeti.pairSingularValues
        (2 * Real.sin (theta / 2)) (2 * Real.sin (theta / 2)) := by
  rw [one_sub_example41DirectRotation]
  have hs : 0 ≤ 2 * Real.sin (theta / 2) :=
    mul_nonneg (by norm_num) (sin_half_nonneg h0 hpi)
  have htr : TauCeti.gramTraceFinTwo (example41DirectDisplacement theta) =
      (2 * Real.sin (theta / 2)) ^ 2 +
        (2 * Real.sin (theta / 2)) ^ 2 := by
    rw [example41DirectDisplacement_eq_matrix, real_gramTrace]
    change
      (1 - Real.cos theta) ^ 2 + (-Real.sin theta) ^ 2 +
          (Real.sin theta ^ 2 + (1 - Real.cos theta) ^ 2) =
        (2 * Real.sin (theta / 2)) ^ 2 +
          (2 * Real.sin (theta / 2)) ^ 2
    have h := half_chord_sq theta
    nlinarith
  have hdt : TauCeti.gramDetFinTwo (example41DirectDisplacement theta) =
      (2 * Real.sin (theta / 2)) ^ 2 *
        (2 * Real.sin (theta / 2)) ^ 2 := by
    rw [example41DirectDisplacement_eq_matrix, real_gramDet]
    change
      ((1 - Real.cos theta) * (1 - Real.cos theta) -
          Real.sin theta * (-Real.sin theta)) ^ 2 =
        (2 * Real.sin (theta / 2)) ^ 2 *
          (2 * Real.sin (theta / 2)) ^ 2
    have h := half_chord_sq theta
    have hin :
        (1 - Real.cos theta) * (1 - Real.cos theta) -
            Real.sin theta * (-Real.sin theta) =
          (2 * Real.sin (theta / 2)) ^ 2 := by
      nlinarith
    rw [hin]
    ring
  exact TauCeti.singularValues_eq_pair_of_gram_trace_det_fin_two
    (example41DirectDisplacement theta) hs hs le_rfl htr hdt

/-- Example 4.1's reflection has singular values `2, 0`. -/
theorem example4_1_reflection_singularValues (theta : ℝ) :
    (LinearMap.id - example41Reflection theta).singularValues =
      TauCeti.pairSingularValues 2 0 := by
  rw [one_sub_example41Reflection]
  have hpy := Real.sin_sq_add_cos_sq theta
  have htr : TauCeti.gramTraceFinTwo (example41ReflectionDisplacement theta) =
      (2 : ℝ) ^ 2 + 0 ^ 2 := by
    rw [example41ReflectionDisplacement_eq_matrix, real_gramTrace]
    change
      (1 - Real.cos theta) ^ 2 + (-Real.sin theta) ^ 2 +
          ((-Real.sin theta) ^ 2 + (1 + Real.cos theta) ^ 2) =
        (2 : ℝ) ^ 2 + 0 ^ 2
    nlinarith
  have hdt : TauCeti.gramDetFinTwo (example41ReflectionDisplacement theta) =
      (2 : ℝ) ^ 2 * 0 ^ 2 := by
    rw [example41ReflectionDisplacement_eq_matrix, real_gramDet]
    change
      ((1 - Real.cos theta) * (1 + Real.cos theta) -
          (-Real.sin theta) * (-Real.sin theta)) ^ 2 =
        (2 : ℝ) ^ 2 * 0 ^ 2
    have hdet :
        (1 - Real.cos theta) * (1 + Real.cos theta) -
            (-Real.sin theta) * (-Real.sin theta) = 0 := by
      nlinarith
    rw [hdet]
    norm_num
  exact TauCeti.singularValues_eq_pair_of_gram_trace_det_fin_two
    (example41ReflectionDisplacement theta) (by norm_num) le_rfl (by norm_num) htr hdt

/-- The paper's displayed Ky Fan two norm for the reflection is exactly `2`. -/
theorem example4_1_reflection_kyFan_two (theta : ℝ) :
    TauCeti.kyFanSum 2 (LinearMap.id - example41Reflection theta) = 2 := by
  rw [TauCeti.kyFanSum_eq_sum_fin, Fin.sum_univ_two,
    example4_1_reflection_singularValues]
  simp

/-- The paper's displayed Ky Fan two norm for the direct rotation is
`4 sin(theta/2)`. -/
theorem example4_1_directRotation_kyFan_two
    {theta : ℝ} (h0 : 0 ≤ theta) (hpi : theta ≤ Real.pi / 2) :
    TauCeti.kyFanSum 2 (LinearMap.id - example41DirectRotation theta) =
      4 * Real.sin (theta / 2) := by
  rw [TauCeti.kyFanSum_eq_sum_fin, Fin.sum_univ_two,
    example4_1_directRotation_singularValues h0 hpi]
  simp
  ring

/-- **Davis--Kahan 1970, Example 4.1.**  On the principal-angle range, the
reflecting competitor has smaller Ky Fan two displacement exactly for
`theta > pi/3`. -/
theorem example4_1_reflection_beats_direct_iff
    {theta : ℝ} (h0 : 0 ≤ theta) (hpi : theta ≤ Real.pi / 2) :
    TauCeti.kyFanSum 2 (LinearMap.id - example41Reflection theta) <
        TauCeti.kyFanSum 2 (LinearMap.id - example41DirectRotation theta) ↔
      Real.pi / 3 < theta := by
  rw [example4_1_reflection_kyFan_two,
    example4_1_directRotation_kyFan_two h0 hpi]
  constructor
  · intro h
    by_contra hnot
    have htheta : theta ≤ Real.pi / 3 := le_of_not_gt hnot
    have hsin : Real.sin (theta / 2) ≤ Real.sin (Real.pi / 6) := by
      refine Real.sin_le_sin_of_le_of_le_pi_div_two ?_ ?_ ?_
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
      · linarith
    rw [Real.sin_pi_div_six] at hsin
    nlinarith
  · intro htheta
    have hx : Real.pi / 6 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos]
    have hy : theta / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos]
    have hsin : Real.sin (Real.pi / 6) < Real.sin (theta / 2) :=
      Real.strictMonoOn_sin hx hy (by linarith)
    rw [Real.sin_pi_div_six] at hsin
    nlinarith

/-! ## Example 4.2: a complex global phase -/

/-- `e^{it}` written in real and imaginary coordinates. -/
def example42Phase (t : ℝ) : ℂ :=
  (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I

/-- Example 4.2's phase at parameter zero. -/
@[simp] theorem example42Phase_zero : example42Phase 0 = 1 := by
  simp [example42Phase]

/-- Addition of angles becomes multiplication of phases. -/
theorem example42Phase_mul (a b : ℝ) :
    example42Phase a * example42Phase b = example42Phase (a + b) := by
  apply Complex.ext
  · simp [example42Phase, Complex.mul_re, Complex.mul_im, Real.cos_add, Real.sin_add]
  · simp [example42Phase, Complex.mul_re, Complex.mul_im, Real.cos_add, Real.sin_add]
    ring

/-- The exact chord length of a unit complex phase. -/
theorem norm_one_sub_example42Phase (t : ℝ) :
    ‖(1 : ℂ) - example42Phase t‖ = 2 * |Real.sin (t / 2)| := by
  have hpy := Real.sin_sq_add_cos_sq t
  have hhalf := Real.sin_sq_add_cos_sq (t / 2)
  have hdouble : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
    have ht : t = t / 2 + t / 2 := by ring
    calc
      Real.cos t = Real.cos (t / 2 + t / 2) := by rw [← ht]
      _ = Real.cos (t / 2) * Real.cos (t / 2) -
          Real.sin (t / 2) * Real.sin (t / 2) := by rw [Real.cos_add]
      _ = 1 - 2 * Real.sin (t / 2) ^ 2 := by nlinarith
  apply (sq_eq_sq₀ (norm_nonneg _)
    (mul_nonneg (by norm_num) (abs_nonneg _))).mp
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [example42Phase, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  nlinarith [sq_abs (Real.sin (t / 2))]

/-- The direct rotation in its complex eigenbasis. -/
def example42DirectRotation (theta : ℝ) : ComplexPlane →ₗ[ℂ] ComplexPlane :=
  Matrix.toEuclideanLin
    !![example42Phase theta, 0;
       0, example42Phase (-theta)]

/-- The source competitor `V = e^{i delta} U`, written after multiplying the
two diagonal phases. -/
def example42Competitor (theta delta : ℝ) : ComplexPlane →ₗ[ℂ] ComplexPlane :=
  Matrix.toEuclideanLin
    !![example42Phase (theta + delta), 0;
       0, example42Phase (delta - theta)]

/-- Literal full displacement of the phase competitor. -/
def example42Displacement (theta delta : ℝ) : ComplexPlane →ₗ[ℂ] ComplexPlane :=
  Matrix.toEuclideanLin
    !![(1 : ℂ) - example42Phase (theta + delta), 0;
       0, (1 : ℂ) - example42Phase (delta - theta)]

/-- The coordinate family really is the paper's `V = e^{i delta} U`. -/
theorem example42Competitor_eq_phase_smul (theta delta : ℝ) :
    example42Competitor theta delta =
      example42Phase delta • example42DirectRotation theta := by
  have hplus : example42Phase (theta + delta) =
      example42Phase delta * example42Phase theta := by
    calc
      example42Phase (theta + delta) = example42Phase (delta + theta) := by rw [add_comm]
      _ = example42Phase delta * example42Phase theta := (example42Phase_mul delta theta).symm
  have hminus : example42Phase (delta - theta) =
      example42Phase delta * example42Phase (-theta) := by
    rw [sub_eq_add_neg]
    exact (example42Phase_mul delta (-theta)).symm
  ext x i
  fin_cases i <;>
    simp [example42Competitor, example42DirectRotation,
      Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail,
      LinearMap.smul_apply, hplus, hminus, mul_assoc]

/-- The displacement of Example 4.2's competitor, as an explicit matrix. -/
@[simp] theorem one_sub_example42Competitor (theta delta : ℝ) :
    LinearMap.id - example42Competitor theta delta = example42Displacement theta delta := by
  ext x i
  fin_cases i <;>
    simp [example42Competitor, example42Displacement,
      Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail] <;>
    ring

private theorem complex_entry (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    (Matrix.toEuclideanLin M) (EuclideanSpace.basisFun (Fin 2) ℂ i) j = M j i := by
  simp [Matrix.toLpLin_apply, EuclideanSpace.basisFun_apply, Matrix.mulVec_single]

private theorem complex_norm_sq (x : ComplexPlane) :
    ‖x‖ ^ 2 = ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two]

private theorem complex_inner (x y : ComplexPlane) :
    ⟪x, y⟫_ℂ = star (x 0) * y 0 + star (x 1) * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

private theorem complexDiagonal_gramTrace (z0 z1 : ℂ) :
    TauCeti.gramTraceFinTwo
        (Matrix.toEuclideanLin !![z0, 0; 0, z1]) =
      ‖z0‖ ^ 2 + ‖z1‖ ^ 2 := by
  show ∑ i : Fin 2,
    ‖(Matrix.toEuclideanLin !![z0, 0; 0, z1])
      (EuclideanSpace.basisFun (Fin 2) ℂ i)‖ ^ 2 = _
  rw [Fin.sum_univ_two, complex_norm_sq, complex_norm_sq]
  rw [complex_entry, complex_entry, complex_entry, complex_entry]
  simp

private theorem complexDiagonal_gramDet (z0 z1 : ℂ) :
    TauCeti.gramDetFinTwo
        (Matrix.toEuclideanLin !![z0, 0; 0, z1]) =
      ‖z0‖ ^ 2 * ‖z1‖ ^ 2 := by
  show ‖(Matrix.toEuclideanLin !![z0, 0; 0, z1])
      (EuclideanSpace.basisFun (Fin 2) ℂ 0)‖ ^ 2 *
      ‖(Matrix.toEuclideanLin !![z0, 0; 0, z1])
      (EuclideanSpace.basisFun (Fin 2) ℂ 1)‖ ^ 2 -
      ‖⟪(Matrix.toEuclideanLin !![z0, 0; 0, z1])
          (EuclideanSpace.basisFun (Fin 2) ℂ 0),
        (Matrix.toEuclideanLin !![z0, 0; 0, z1])
          (EuclideanSpace.basisFun (Fin 2) ℂ 1)⟫_ℂ‖ ^ 2 = _
  rw [complex_norm_sq, complex_norm_sq, complex_inner]
  simp only [complex_entry]
  simp

private theorem example42_plus_norm
    {theta delta : ℝ} (h0 : 0 ≤ delta) (hlt : delta < theta)
    (hpi : theta ≤ Real.pi / 2) :
    ‖(1 : ℂ) - example42Phase (theta + delta)‖ =
      2 * Real.sin ((theta + delta) / 2) := by
  rw [norm_one_sub_example42Phase, abs_of_nonneg]
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
    (by linarith [Real.pi_pos])

private theorem example42_minus_norm
    {theta delta : ℝ} (h0 : 0 ≤ delta) (hlt : delta < theta)
    (hpi : theta ≤ Real.pi / 2) :
    ‖(1 : ℂ) - example42Phase (delta - theta)‖ =
      2 * Real.sin ((theta - delta) / 2) := by
  rw [norm_one_sub_example42Phase]
  have harg : (delta - theta) / 2 = -((theta - delta) / 2) := by ring
  rw [harg, Real.sin_neg, abs_neg, abs_of_nonneg]
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
    (by linarith [Real.pi_pos])

/-- Example 4.2's two singular values. -/
theorem example4_2_competitor_singularValues
    {theta delta : ℝ} (h0 : 0 ≤ delta) (hlt : delta < theta)
    (hpi : theta ≤ Real.pi / 2) :
    (LinearMap.id - example42Competitor theta delta).singularValues =
      TauCeti.pairSingularValues
        (2 * Real.sin ((theta + delta) / 2))
        (2 * Real.sin ((theta - delta) / 2)) := by
  rw [one_sub_example42Competitor]
  have hplus0 : 0 ≤ Real.sin ((theta + delta) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
      (by linarith [Real.pi_pos])
  have hminus0 : 0 ≤ Real.sin ((theta - delta) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
      (by linarith [Real.pi_pos])
  have hordSin : Real.sin ((theta - delta) / 2) ≤
      Real.sin ((theta + delta) / 2) := by
    refine Real.sin_le_sin_of_le_of_le_pi_div_two ?_ ?_ ?_
    · linarith [Real.pi_pos]
    · linarith
    · linarith
  have hplus := example42_plus_norm h0 hlt hpi
  have hminus := example42_minus_norm h0 hlt hpi
  have htr : TauCeti.gramTraceFinTwo (example42Displacement theta delta) =
      (2 * Real.sin ((theta + delta) / 2)) ^ 2 +
        (2 * Real.sin ((theta - delta) / 2)) ^ 2 := by
    rw [show example42Displacement theta delta = Matrix.toEuclideanLin
      !![(1 : ℂ) - example42Phase (theta + delta), 0;
         0, (1 : ℂ) - example42Phase (delta - theta)] from rfl,
      complexDiagonal_gramTrace, hplus, hminus]
  have hdt : TauCeti.gramDetFinTwo (example42Displacement theta delta) =
      (2 * Real.sin ((theta + delta) / 2)) ^ 2 *
        (2 * Real.sin ((theta - delta) / 2)) ^ 2 := by
    rw [show example42Displacement theta delta = Matrix.toEuclideanLin
      !![(1 : ℂ) - example42Phase (theta + delta), 0;
         0, (1 : ℂ) - example42Phase (delta - theta)] from rfl,
      complexDiagonal_gramDet, hplus, hminus]
  exact TauCeti.singularValues_eq_pair_of_gram_trace_det_fin_two
    (example42Displacement theta delta)
    (mul_nonneg (by norm_num) hplus0)
    (mul_nonneg (by norm_num) hminus0)
    (mul_le_mul_of_nonneg_left hordSin (by norm_num)) htr hdt

/-- **Davis--Kahan 1970, Example 4.2, displayed norm formula.** -/
theorem example4_2_competitor_kyFan_two
    {theta delta : ℝ} (h0 : 0 ≤ delta) (hlt : delta < theta)
    (hpi : theta ≤ Real.pi / 2) :
    TauCeti.kyFanSum 2 (LinearMap.id - example42Competitor theta delta) =
      4 * Real.sin (theta / 2) * Real.cos (delta / 2) := by
  rw [TauCeti.kyFanSum_eq_sum_fin, Fin.sum_univ_two,
    example4_2_competitor_singularValues h0 hlt hpi]
  simp
  rw [show (theta + delta) / 2 = theta / 2 + delta / 2 by ring,
    show (theta - delta) / 2 = theta / 2 - delta / 2 by ring,
    Real.sin_add, Real.sin_sub]
  ring

/-- At `delta = 0` the phase family reduces to the direct rotation. -/
theorem example42Competitor_zero (theta : ℝ) :
    example42Competitor theta 0 = example42DirectRotation theta := by
  ext x i
  fin_cases i <;>
    simp [example42Competitor, example42DirectRotation,
      Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]

/-- **Davis--Kahan 1970, Example 4.2, failure of minimality.**  Every nonzero
phase `0 < delta < theta` strictly lowers the Ky Fan two displacement. -/
theorem example4_2_nonzero_phase_beats_direct
    {theta delta : ℝ} (hdelta : 0 < delta) (hlt : delta < theta)
    (hpi : theta ≤ Real.pi / 2) :
    TauCeti.kyFanSum 2 (LinearMap.id - example42Competitor theta delta) <
      TauCeti.kyFanSum 2 (LinearMap.id - example42DirectRotation theta) := by
  have htheta : 0 < theta := hdelta.trans hlt
  have hsource := example4_2_competitor_kyFan_two hdelta.le hlt hpi
  have hzero := example4_2_competitor_kyFan_two
    (theta := theta) (delta := 0) (by norm_num) htheta hpi
  rw [example42Competitor_zero] at hzero
  rw [hsource, hzero]
  have hs : 0 < Real.sin (theta / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by linarith [Real.pi_pos])
  have hsd : 0 < Real.sin (delta / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by linarith [Real.pi_pos])
  have hcd : 0 < Real.cos (delta / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hpy := Real.sin_sq_add_cos_sq (delta / 2)
  have hclt : Real.cos (delta / 2) < 1 := by
    nlinarith [sq_pos_of_pos hsd]
  have hprod :
      0 < (4 * Real.sin (theta / 2)) * (1 - Real.cos (delta / 2)) :=
    mul_pos (mul_pos (by norm_num) hs) (sub_pos.mpr hclt)
  have hstrict :
      4 * Real.sin (theta / 2) * Real.cos (delta / 2) <
        4 * Real.sin (theta / 2) := by
    nlinarith
  simpa using hstrict

end

end Section4Examples
end DavisKahan1970
end TauCeti
