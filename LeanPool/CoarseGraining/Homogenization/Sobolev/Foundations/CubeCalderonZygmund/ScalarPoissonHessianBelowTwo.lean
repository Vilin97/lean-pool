/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ScalarPoissonGradientBelowTwo
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.WeakHessianFiniteP
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.W10pWeakTestClosure
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ReflectedParentInteriorHessian
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ReflectedParentHessianRowIdentification
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ReflectedHessianRowOneLevelTail
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ScalarPoissonHessianTwo
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.H1CutoffIntegrationByParts
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.SourceParentFiniteLpExtension
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.WeakHessianRowL2Energy
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.VectorFieldAndApex.WeakEquationHelpers
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ZeroExtensionGraph

/-!
# Scalar Poisson Hessian estimates below the energy exponent

The endpoint is obtained by localized duality on the odd-reflected parent
cube.  The small utility below is intentionally kept here: it is the exact
bridge used when a compactly supported `H¹₀` multiplier must be inserted into
the smooth-test divergence identity.
-/

namespace Homogenization

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

private theorem weak_divergence_identity_of_h10
    {d : ℕ} {U : Set (Vec d)} [IsFiniteMeasure (volume.restrict U)]
    (w : H1Function U) (h : Vec d → Vec d) (hh : MemVectorL2 U h)
    (sigma0 : ℝ)
    (hweak : ∀ phi : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) phi →
      HasCompactSupport phi → tsupport phi ⊆ U →
      sigma0 * ∫ x in U, vecDot (w.grad x) (euclideanGradient phi x) ∂volume =
        -∫ x in U, vecDot (h x) (euclideanGradient phi x) ∂volume)
    (v : H10Function U) :
    sigma0 * ∫ x in U, vecDot (w.grad x) (v.toH1Function.grad x) ∂volume =
      -∫ x in U, vecDot (h x) (v.toH1Function.grad x) ∂volume := by
  simpa only [H10Function.toW10pOfExponentLETwo_grad] using!
    weak_divergence_identity_of_w10p FiniteLpExponent.two le_rfl w h hh sigma0
      hweak (v.toW10pOfExponentLETwo FiniteLpExponent.two le_rfl)

private theorem parent_adjoint_gradient_cz
    (d : ℕ) [NeZero d] (p : FiniteLpExponent)
    (hp : 2 < p.exponent.toReal) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ)
      (h : CubeEuclideanL2LpField (originCube d m) p),
      let hP := sourceParentFiniteLpExtension m p h
      let v := openCubeSetScalarDivergenceSolution (originCube d (m + 1))
        (by norm_num : (0 : ℝ) < 1) hP.toField
        (memVectorL2_sourceParentFiniteLpExtension m p h)
      (centeredCubeDomain d (m + 1)).normalizedEuclideanLpENorm p.exponent
          v.toH1Function.grad ≤
        C * (centeredCubeDomain d m).normalizedEuclideanLpENorm p.exponent
          h.toField := by
  obtain ⟨C, hCtop, hC⟩ := centeredCubeH10ScalarDivergence_cz_of_two_lt d p hp
  refine ⟨C, hCtop, ?_⟩
  intro m h
  let hP := sourceParentFiniteLpExtension m p h
  let v := openCubeSetScalarDivergenceSolution (originCube d (m + 1))
    (by norm_num : (0 : ℝ) < 1) hP.toField
    (memVectorL2_sourceParentFiniteLpExtension m p h)
  have hv : IsCenteredCubeH10ScalarDivergenceSolution (m + 1) 1 v hP.toLpTwo := by
    intro psi
    simpa only [v] using! INTERNAL.openCubeSetScalarDivergenceSolution_normalized_weak
      (m + 1) (by norm_num : (0 : ℝ) < 1) hP.toField
      (memVectorL2_sourceParentFiniteLpExtension m p h) psi
  have hbound := hC (m + 1) 1 hP v (by norm_num) hv
  calc
    (centeredCubeDomain d (m + 1)).normalizedEuclideanLpENorm p.exponent
        v.toH1Function.grad ≤
      C * (ENNReal.ofReal (1 : ℝ))⁻¹ *
        (centeredCubeDomain d (m + 1)).normalizedEuclideanLpENorm p.exponent
          hP.toField := hbound
    _ = C * eLpNorm (hilbertifyVecField hP.toField) p.exponent
        (normalizedCubeMeasure (originCube d (m + 1))) := by
      simp only [ENNReal.ofReal_one, inv_one, mul_one,
        BoundedMeasurableDomain.normalizedEuclideanLpENorm,
        BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
        MeasureTheory.eLpNorm_norm, centeredCubeDomain,
        cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
      rfl
    _ ≤ C * eLpNorm (hilbertifyVecField h.toField) p.exponent
        (normalizedCubeMeasure (originCube d m)) := by
      gcongr
      exact eLpNorm_sourceParentFiniteLpExtension_le m p h
    _ = C * (centeredCubeDomain d m).normalizedEuclideanLpENorm p.exponent
        h.toField := by
      simp only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
        BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
        MeasureTheory.eLpNorm_norm, centeredCubeDomain,
        cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
      rfl

/-- The adjoint parent solution has the high-exponent gradient estimate and,
by Poincaré, the value estimate needed by the lower-order cutoff terms. -/
private theorem exists_parent_adjoint_value_bound
    (d : ℕ) [NeZero d] (p : FiniteLpExponent)
    (hp : 2 < p.exponent.toReal) :
    ∃ (Ccz P : ℝ≥0∞), Ccz < ∞ ∧ P < ∞ ∧ ∀ (m : ℤ)
      (h : CubeEuclideanL2LpField (originCube d m) p),
      let hP := sourceParentFiniteLpExtension m p h
      let v := openCubeSetScalarDivergenceSolution (originCube d (m + 1))
        (by norm_num : (0 : ℝ) < 1) hP.toField
        (memVectorL2_sourceParentFiniteLpExtension m p h)
      eLpNorm v.toH1Function.toFun p.exponent
          (normalizedCubeMeasure (originCube d (m + 1))) ≤
        P * ENNReal.ofReal (centeredCubeScale (m + 1)) * Ccz *
          eLpNorm (hilbertifyVecField h.toField) p.exponent
            (normalizedCubeMeasure (originCube d m)) ∧
      eLpNorm (hilbertifyVecField v.toH1Function.grad) p.exponent
          (normalizedCubeMeasure (originCube d (m + 1))) ≤
        Ccz * eLpNorm (hilbertifyVecField h.toField) p.exponent
          (normalizedCubeMeasure (originCube d m)) ∧
      MemLp (hilbertifyVecField v.toH1Function.grad) p.exponent
          (normalizedCubeMeasure (originCube d (m + 1))) ∧
      MemLp v.toH1Function.toFun p.exponent
          (normalizedCubeMeasure (originCube d (m + 1))) := by
  obtain ⟨Ccz, hCczTop, hCcz⟩ :=
    parent_adjoint_gradient_cz d p hp
  obtain ⟨Cp, hCp, hPoincare⟩ :=
    W10pFunction.exists_poincare_constant_of_isOpenBoundedConvexDomain
      p.one_lt p.lt_top.ne
      (isOpenBoundedConvexDomain_openCubeSet (originCube d 0))
  let P : ℝ≥0∞ := ENNReal.ofReal (Cp * d)
  refine ⟨Ccz, P, hCczTop, ENNReal.ofReal_lt_top, ?_⟩
  intro m h
  let hP := sourceParentFiniteLpExtension m p h
  let v := openCubeSetScalarDivergenceSolution (originCube d (m + 1))
    (by norm_num : (0 : ℝ) < 1) hP.toField
    (memVectorL2_sourceParentFiniteLpExtension m p h)
  have hgradBound : eLpNorm (hilbertifyVecField v.toH1Function.grad) p.exponent
      (normalizedCubeMeasure (originCube d (m + 1))) ≤
      Ccz * eLpNorm (hilbertifyVecField h.toField) p.exponent
        (normalizedCubeMeasure (originCube d m)) := by
    simpa only [hP, v, BoundedMeasurableDomain.normalizedEuclideanLpENorm,
      BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
      eLpNorm_norm, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using!
      hCcz m h
  have hvgrad2 : MemLp (hilbertifyVecField v.toH1Function.grad) 2
      (normalizedCubeMeasure (originCube d (m + 1))) := by
    rw [normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    exact (memHilbertVectorL2_hilbertifyVecField
      v.toH1Function.grad_memVectorL2).smul_measure ENNReal.ofReal_ne_top
  have hsourceTop : eLpNorm (hilbertifyVecField h.toField) p.exponent
      (normalizedCubeMeasure (originCube d m)) < ∞ :=
    h.toCubeEuclideanLpField.euclideanMemLp.eLpNorm_lt_top
  have hgradTop : eLpNorm (hilbertifyVecField v.toH1Function.grad) p.exponent
      (normalizedCubeMeasure (originCube d (m + 1))) < ∞ :=
    lt_of_le_of_lt hgradBound (ENNReal.mul_lt_top hCczTop hsourceTop)
  have hvgrad : MemLp (hilbertifyVecField v.toH1Function.grad) p.exponent
      (normalizedCubeMeasure (originCube d (m + 1))) :=
    ⟨hvgrad2.aestronglyMeasurable, hgradTop⟩
  have hvalueBound :=
    ScalarPoissonGradientBelowTwo.centeredCubeH10_value_eLpNorm_le_scale_mul_grad
      p Cp hCp hPoincare (m + 1) v (by
        simpa only [centeredCubeDomain,
          cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using hvgrad)
  have hvalue : eLpNorm v.toH1Function.toFun p.exponent
      (normalizedCubeMeasure (originCube d (m + 1))) ≤
      P * ENNReal.ofReal (centeredCubeScale (m + 1)) * Ccz *
        eLpNorm (hilbertifyVecField h.toField) p.exponent
          (normalizedCubeMeasure (originCube d m)) := by
    calc
      eLpNorm v.toH1Function.toFun p.exponent
          (normalizedCubeMeasure (originCube d (m + 1))) ≤
        P * ENNReal.ofReal (centeredCubeScale (m + 1)) *
          eLpNorm (hilbertifyVecField v.toH1Function.grad) p.exponent
            (normalizedCubeMeasure (originCube d (m + 1))) := by
          simpa only [P, centeredCubeDomain,
            cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using hvalueBound
      _ ≤ P * ENNReal.ofReal (centeredCubeScale (m + 1)) * Ccz *
          eLpNorm (hilbertifyVecField h.toField) p.exponent
            (normalizedCubeMeasure (originCube d m)) := by
          calc
            P * ENNReal.ofReal (centeredCubeScale (m + 1)) *
                eLpNorm (hilbertifyVecField v.toH1Function.grad) p.exponent
                  (normalizedCubeMeasure (originCube d (m + 1))) ≤
              P * ENNReal.ofReal (centeredCubeScale (m + 1)) *
                (Ccz * eLpNorm (hilbertifyVecField h.toField) p.exponent
                  (normalizedCubeMeasure (originCube d m))) := by
                gcongr
            _ = _ := by ac_rfl
  have hvalueTop : eLpNorm v.toH1Function.toFun p.exponent
      (normalizedCubeMeasure (originCube d (m + 1))) < ∞ :=
    lt_of_le_of_lt hvalue <| ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
        hCczTop) hsourceTop
  have hvfun2 : MemLp v.toH1Function.toFun 2
      (normalizedCubeMeasure (originCube d (m + 1))) := by
    rw [normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    exact v.toH1Function.memL2.smul_measure ENNReal.ofReal_ne_top
  exact ⟨hvalue, hgradBound, hvgrad, ⟨hvfun2.aestronglyMeasurable, hvalueTop⟩⟩

private theorem norm_basisVec {d : ℕ} (i : Fin d) : ‖basisVec i‖ = (1 : ℝ) := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).2 ?_
    intro j
    by_cases hji : j = i
    · subst j
      simp [basisVec]
    · simp [basisVec, hji]
  · have hi : ‖basisVec i i‖ ≤ ‖basisVec i‖ := norm_le_pi_norm (basisVec i) i
    simpa [basisVec] using hi

private theorem euclideanCoordLaplacian_le_hessian
    {d : ℕ} {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (x : Vec d) {B : ℝ} (hB : ‖iteratedFDeriv ℝ 2 η x‖ ≤ B) :
    |euclideanCoordLaplacian η x| ≤ (d : ℝ) * B := by
  have hcoord : ∀ i : Fin d, |euclideanCoordSecondDeriv i i η x| ≤ B := by
    intro i
    calc
      |euclideanCoordSecondDeriv i i η x| =
          ‖fderiv ℝ (fderiv ℝ η) x (basisVec i) (basisVec i)‖ := by
            rw [euclideanCoordSecondDeriv_eq_fderiv_fderiv hη]
            simp [Real.norm_eq_abs]
      _ = ‖iteratedFDeriv ℝ 2 η x ![basisVec i, basisVec i]‖ := by
            simp [iteratedFDeriv_two_apply]
      _ ≤ ‖iteratedFDeriv ℝ 2 η x‖ * ∏ j, ‖![basisVec i, basisVec i] j‖ := by
            simpa using ContinuousMultilinearMap.le_opNorm
              (iteratedFDeriv ℝ 2 η x) ![basisVec i, basisVec i]
      _ = ‖iteratedFDeriv ℝ 2 η x‖ := by simp [norm_basisVec]
      _ ≤ B := hB
  calc
    |euclideanCoordLaplacian η x| =
        |∑ i : Fin d, euclideanCoordSecondDeriv i i η x| := rfl
    _ ≤ ∑ i : Fin d, |euclideanCoordSecondDeriv i i η x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, B := Finset.sum_le_sum fun i _ => hcoord i
    _ = (d : ℝ) * B := by simp [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private theorem quantitativeCubeCutoff_euclideanCoordLaplacian_bound
    {d : ℕ} {Q : TriadicCube d} {ρ₁ ρ₂ : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂) (x : Vec d) :
    |euclideanCoordLaplacian (η : Vec d → ℝ) x| ≤
      (d : ℝ) * (quantitativeCubeCutoffHessianConst d /
        (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2)) := by
  apply euclideanCoordLaplacian_le_hessian η.smooth x
  simpa using η.hessian_bound x

private theorem vector_multiplier_eLpNorm
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (p : ℝ≥0∞) {f : α → E} {g : α → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ x, ‖f x‖ ≤ C * |g x|) :
    eLpNorm f p μ ≤ C.toNNReal • eLpNorm g p μ := by
  apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
  filter_upwards with x
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
  apply ENNReal.coe_le_coe.mpr
  refine (NNReal.coe_le_coe).mp ?_
  change ‖f x‖ ≤ (C.toNNReal : ℝ) * ‖g x‖
  simpa [Real.coe_toNNReal _ hC, Real.norm_eq_abs] using h x

private theorem scalar_multiplier_eLpNorm
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (p : ℝ≥0∞) {f g : α → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ x, |f x| ≤ C * |g x|) :
    eLpNorm f p μ ≤ C.toNNReal • eLpNorm g p μ := by
  apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
  filter_upwards with x
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
  apply ENNReal.coe_le_coe.mpr
  refine (NNReal.coe_le_coe).mp ?_
  change ‖f x‖ ≤ (C.toNNReal : ℝ) * ‖g x‖
  simpa [Real.coe_toNNReal _ hC, Real.norm_eq_abs] using h x

private theorem scalar_mul_bounded_vector_eLpNorm
    {d : ℕ} {μ : Measure (Vec d)} (p : ℝ≥0∞)
    {v : Vec d → ℝ} {G : Vec d → HilbertVec d} {C : ℝ}
    (hC : 0 ≤ C) (hG : ∀ x, ‖G x‖ ≤ C) :
    eLpNorm (fun x => v x • G x) p μ ≤ C.toNNReal • eLpNorm v p μ := by
  apply vector_multiplier_eLpNorm p hC
  intro x
  rw [norm_smul]
  simpa [Real.norm_eq_abs, mul_comm] using
    (mul_le_mul_of_nonneg_left (hG x) (abs_nonneg (v x)))

private theorem scalar_mul_bounded_scalar_eLpNorm
    {d : ℕ} {μ : Measure (Vec d)} (p : ℝ≥0∞)
    {w L : Vec d → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hL : ∀ x, |L x| ≤ C) :
    eLpNorm (fun x => w x * L x) p μ ≤ C.toNNReal • eLpNorm w p μ := by
  apply scalar_multiplier_eLpNorm p hC
  intro x
  simpa [abs_mul, mul_comm] using
    (mul_le_mul_of_nonneg_left (hL x) (abs_nonneg (w x)))

private theorem quantitativeCubeCutoff_hilbertGradient_bound
    {d : ℕ} {Q : TriadicCube d} {ρ₁ ρ₂ : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂) (x : Vec d) :
    ‖HilbertVec.ofVec (euclideanGradient (η : Vec d → ℝ) x)‖ ≤
      (d : ℝ) * (quantitativeCubeCutoffGradientConst d /
        ((ρ₂ - ρ₁) * cubeRadius Q)) := by
  let K : ℝ := quantitativeCubeCutoffGradientConst d /
    ((ρ₂ - ρ₁) * cubeRadius Q)
  have hK : 0 ≤ K := by
    refine (norm_nonneg (fderiv ℝ (η : Vec d → ℝ) x)).trans ?_
    simpa [K] using η.gradient_bound x
  have hgrad : ‖euclideanGradient (η : Vec d → ℝ) x‖ ≤ K := by
    refine (pi_norm_le_iff_of_nonneg hK).2 ?_
    intro i
    calc
      ‖euclideanGradient (η : Vec d → ℝ) x i‖ =
          ‖(fderiv ℝ (η : Vec d → ℝ) x) (basisVec i)‖ := by
            simp [euclideanGradient, euclideanCoordDeriv]
      _ ≤ ‖fderiv ℝ (η : Vec d → ℝ) x‖ * ‖basisVec i‖ := by
            simpa using (fderiv ℝ (η : Vec d → ℝ) x).le_opNorm (basisVec i)
      _ = ‖fderiv ℝ (η : Vec d → ℝ) x‖ := by simp [norm_basisVec]
      _ ≤ K := by simpa [K] using η.gradient_bound x
  calc
    ‖HilbertVec.ofVec (euclideanGradient (η : Vec d → ℝ) x)‖ ≤
        (d : ℝ) * ‖euclideanGradient (η : Vec d → ℝ) x‖ :=
      HilbertVec.norm_ofVec_le_mul_norm _
    _ ≤ (d : ℝ) * K := mul_le_mul_of_nonneg_left hgrad (Nat.cast_nonneg d)
    _ = (d : ℝ) * (quantitativeCubeCutoffGradientConst d /
        ((ρ₂ - ρ₁) * cubeRadius Q)) := rfl

/-- The two cutoff products used in the reflected-parent mutual testing step.
The first is an admissible local row test; the second is its canonical
zero-trace extension to the parent adjoint problem. -/
private theorem exists_localized_mutual_tests
    {d : ℕ} {m : ℤ}
    (r : H1Function (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ)))
    (v : H10Function (openCubeSet (originCube d (m + 1)))) :
    ∃ (η : QuantitativeCubeCutoff (originCube d (m + 1)) (1 / 3 : ℝ) (5 / 12 : ℝ))
      (rowTest : H10Function
        (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ)))
      (adjTest : H10Function (openCubeSet (originCube d (m + 1)))),
      ((fun x ↦ rowTest.toH1Function.grad x) =ᵐ[volume.restrict
          (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ))]
        fun x j ↦ η x * v.toH1Function.grad x j +
          v.toH1Function.toFun x * (fderiv ℝ (η : Vec d → ℝ) x) (basisVec j)) ∧
      ((fun x ↦ adjTest.toH1Function.grad x) =ᵐ[volume.restrict
          (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ))]
        fun x j ↦ η x * r.grad x j +
          r.toFun x * (fderiv ℝ (η : Vec d → ℝ) x) (basisVec j)) := by
  let Qp : TriadicCube d := originCube d (m + 1)
  let U : Set (Vec d) := scaledOpenCubeSet Qp (1 / 2 : ℝ)
  let P : Set (Vec d) := openCubeSet Qp
  have hU : IsOpenBoundedConvexDomain U :=
    isOpenBoundedConvexDomain_scaledOpenCubeSet_of_pos Qp (by norm_num)
  have hP : IsOpen P := isOpen_openCubeSet Qp
  have hUP : U ⊆ P := by
    intro x hx
    apply scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one Qp (ρ := 1 / 2)
      (by norm_num) (by norm_num)
    intro i
    exact le_of_lt (hx i)
  let η : QuantitativeCubeCutoff Qp (1 / 3 : ℝ) (5 / 12 : ℝ) :=
    QuantitativeCubeCutoff.canonical Qp (1 / 3 : ℝ) (5 / 12 : ℝ)
      (by norm_num) (by norm_num)
  have hηsub : tsupport (η : Vec d → ℝ) ⊆ U := by
    exact (η.tsupport_subset_scaledClosedCubeSet_of_support_subset).trans
      (scaledClosedCubeSet_subset_scaledOpenCubeSet_of_lt Qp (by norm_num))
  let vU : H1Function U := v.toH1Function.restrict hU.isOpen hUP
  let rowTest : H10Function U :=
    vU.mulContDiffHasCompactSupportToH10 hU η.smooth η.hasCompactSupport hηsub
  let adjTestU : H10Function U :=
    r.mulContDiffHasCompactSupportToH10 hU η.smooth η.hasCompactSupport hηsub
  let adjTest : H10Function P :=
    adjTestU.extendByZeroToOpenSuperset hU.isOpen.measurableSet hP hUP
  refine ⟨η, rowTest, adjTest, ?_, ?_⟩
  · simpa only [rowTest, vU, H1Function.restrict] using
      (WeakPoissonEquationOn.mulContDiffHasCompactSupportToH10_grad_ae
        vU hU η.smooth η.hasCompactSupport hηsub)
  · have hadj := WeakPoissonEquationOn.mulContDiffHasCompactSupportToH10_grad_ae
      r hU η.smooth η.hasCompactSupport hηsub
    filter_upwards [ae_restrict_mem hU.isOpen.measurableSet, hadj] with x hxU hx
    change adjTestU.zeroExtensionGrad x = _
    rw [adjTestU.zeroExtensionGrad_apply_of_mem hxU]
    exact hx

private theorem exists_reflected_source_row_setup
    {d : ℕ} [NeZero d] {m : ℤ} (q : FiniteLpExponent) {F : Vec d → ℝ}
    (hF : MemLp F 2 (normalizedCubeMeasure (originCube d m)))
    (hFq : MemLp F q.exponent (normalizedCubeMeasure (originCube d m)))
    {B : ℝ≥0∞} (hBtop : B < ∞)
    {u : H10Function (openCubeSet (originCube d m))}
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F)
    (H : HasWeakHessianOn (openCubeSet (originCube d m)) u.toH1Function)
    (i : Fin d)
    (hgrad : eLpNorm (hilbertifyVecField u.toH1Function.grad) q.exponent
      (normalizedCubeMeasure (originCube d m)) ≤ B) :
    ∃ (r : H1Function (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ)))
      (b : Vec d → Vec d),
      (∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ) →
        ∫ x in scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ),
            vecDot (r.grad x) (euclideanGradient φ x) ∂volume =
          -∫ x in scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ),
            vecDot (b x) (euclideanGradient φ x) ∂volume) ∧
      MemVectorL2 (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ)) b ∧
      (hilbertifyVecField r.grad =ᵐ[volume.restrict
        (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ))]
        fun x ↦ HilbertVec.ofVec
          (cubeDirichletOddReflectionHessianRowVectorField
            (originCube d m) i (fun y j ↦ H.hess i j y) x)) ∧
      b = (fun x j ↦ if j = i then
        cubeDirichletOddReflectionScalar (originCube d m) F x else 0) ∧
      MemLp (hilbertifyVecField b) q.exponent
        (normalizedCubeMeasure (originCube d (m + 1))) ∧
      eLpNorm (hilbertifyVecField b) q.exponent
        (normalizedCubeMeasure (originCube d (m + 1))) =
        eLpNorm F q.exponent (normalizedCubeMeasure (originCube d m)) ∧
      MemLp r.toFun q.exponent ((normalizedCubeMeasure (originCube d (m + 1))).restrict
        (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ))) ∧
      eLpNorm r.toFun q.exponent ((normalizedCubeMeasure (originCube d (m + 1))).restrict
        (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ))) ≤ B := by
  obtain ⟨uP, _huPfun, huPgrad, hweakP, uU, _huUfun, huUgrad, HU, _hHU⟩ :=
    hweak.exists_cubeDirichletOddReflectionParent_innerHalf_hasWeakHessianOn hF
  let U : Set (Vec d) := scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ)
  let FR : Vec d → ℝ := cubeDirichletOddReflectionScalar (originCube d m) F
  let b : Vec d → Vec d := fun x j ↦ if j = i then FR x else 0
  let r : H1Function U := HU.gradCoordH1Function i
  have hUopen : IsOpen U :=
    (isOpenBoundedConvexDomain_scaledOpenCubeSet_of_pos
      (originCube d (m + 1)) (by norm_num : 0 < (1 / 2 : ℝ))).isOpen
  have hUP : U ⊆ openCubeSet (originCube d (m + 1)) := by
    intro x hx
    apply scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one
      (originCube d (m + 1)) (ρ := 1 / 2) (by norm_num) (by norm_num)
    intro j
    exact le_of_lt (hx j)
  have hFopen : MemScalarL2 (openCubeSet (originCube d m)) F := by
    exact memL2On_openCubeSet_of_memLp_normalizedCubeMeasure _ hF
  have hFRparent : MemScalarL2 (openCubeSet (originCube d (m + 1))) FR := by
    simpa only [FR] using
      memScalarL2_openCubeSet_succ_originCube_cubeDirichletOddReflectionScalar
        (m := m) hFopen
  have hFRU : MemScalarL2 U FR := memL2On_mono hUP hFRparent
  have hweakU : WeakPoissonEquationOn U uU FR := by
    have hres := hweakP.restrict hUopen hUP
    intro φ hφ hφs hφsub
    have ht := hres.test φ hφ hφs hφsub
    simpa only [H1Function.restrict, huUgrad] using ht
  have hrow : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      ∫ x in U, vecDot (r.grad x) (euclideanGradient φ x) ∂volume =
        -∫ x in U, vecDot (b x) (euclideanGradient φ x) ∂volume := by
    simpa only [r, b, FR, one_mul] using
      hweakU.gradCoordH1Function_weakDivergence hUopen hFRU HU i
  have hb : MemVectorL2 U b := by
    simpa only [b] using memVectorL2_singleCoordinate hFRU i
  have hid := H.cubeDirichletOddReflectionParent_innerHalf_hessianRow_ae_eq
    huPgrad huUgrad HU i
  have hrowid : hilbertifyVecField r.grad =ᵐ[volume.restrict U]
      fun x ↦ HilbertVec.ofVec
        (cubeDirichletOddReflectionHessianRowVectorField
          (originCube d m) i (fun y j ↦ H.hess i j y) x) := by
    simpa only [r, U, hilbertifyVecField,
      HasWeakHessianOn.gradCoordH1Function_grad] using! hid
  have hrnorm : eLpNorm r.toFun q.exponent
      ((normalizedCubeMeasure (originCube d (m + 1))).restrict U) ≤ B := by
    let Q : TriadicCube d := originCube d m
    let refl : Vec d → ℝ :=
      cubeDirichletOddReflectionGradientCoordScalar Q i
        (fun y ↦ u.toH1Function.grad y i)
    have hscalar : (fun x ↦ uU.grad x i) = refl := by
      funext x
      have hx := congrArg (fun G : Vec d → Vec d ↦ G x i)
        (huUgrad.trans huPgrad)
      change uU.grad x i =
        cubeDirichletOddReflectionVectorField Q (fun y ↦ u.toH1Function.grad y) x i at hx
      rw [hx]
      simp only [refl, cubeDirichletOddReflectionGradientCoordScalar,
        cubeDirichletOddReflectionVectorField,
        cubeCoordinateFoldReflectedVectorField, Pi.smul_apply, smul_eq_mul]
      ring
    calc
      eLpNorm r.toFun q.exponent ((normalizedCubeMeasure (originCube d (m + 1))).restrict U) =
        eLpNorm refl q.exponent ((normalizedCubeMeasure (originCube d (m + 1))).restrict U) := by
          change eLpNorm (fun x ↦ uU.grad x i) q.exponent
            ((normalizedCubeMeasure (originCube d (m + 1))).restrict U) = _
          rw [hscalar]
      _ ≤ eLpNorm refl q.exponent (normalizedCubeMeasure (originCube d (m + 1))) :=
        eLpNorm_mono_measure refl Measure.restrict_le_self
      _ = eLpNorm (fun y ↦ u.toH1Function.grad y i) q.exponent
          (normalizedCubeMeasure (originCube d m)) := by
        simpa only [refl, Q] using
          eLpNorm_normalizedCubeMeasure_succ_originCube_gradientCoordScalar i
            (fun y ↦ u.toH1Function.grad y i) q
      _ ≤ eLpNorm (hilbertifyVecField u.toH1Function.grad) q.exponent
          (normalizedCubeMeasure (originCube d m)) :=
        coordinate_eLpNorm_le_euclidean _ q u.toH1Function.grad i
      _ ≤ B := hgrad
  have hFRq : MemLp FR q.exponent (normalizedCubeMeasure (originCube d (m + 1))) := by
    simpa only [FR] using
      memLp_normalizedCubeMeasure_succ_originCube_cubeDirichletOddReflectionScalar q hFq
  have hbq : MemLp (hilbertifyVecField b) q.exponent
      (normalizedCubeMeasure (originCube d (m + 1))) := by
    refine ⟨?_, ?_⟩
    · let L : ℝ →L[ℝ] HilbertVec d :=
        (HilbertVec.ofVecL d).comp (ContinuousLinearMap.single ℝ (fun _ : Fin d ↦ ℝ) i)
      have hL := L.continuous.comp_aestronglyMeasurable hFRq.aestronglyMeasurable
      have hbfield : hilbertifyVecField b =
          fun x ↦ HilbertVec.ofVec (Pi.single i (FR x)) := by
        funext x
        change HilbertVec.ofVec (b x) = HilbertVec.ofVec (Pi.single i (FR x))
        congr 1
        funext j
        by_cases hji : j = i
        · subst j; simp [b]
        · simp [b, hji]
      rw [hbfield]
      simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply,
        HilbertVec.ofVecL_apply] using hL
    · have hnorm : eLpNorm (hilbertifyVecField b) q.exponent
          (normalizedCubeMeasure (originCube d (m + 1))) =
        eLpNorm FR q.exponent (normalizedCubeMeasure (originCube d (m + 1))) := by
          apply eLpNorm_congr_norm_ae
          apply ae_of_all; intro x
          change ‖HilbertVec.ofVec (fun j ↦ if j = i then FR x else 0)‖ = ‖FR x‖
          have hs : (fun j ↦ if j = i then FR x else 0) = Pi.single i (FR x) := by
            funext j; by_cases hji : j = i
            · subst j; simp
            · simp [hji]
          rw [hs]
          exact PiLp.norm_single (2 : ℝ≥0∞) (fun _ : Fin d ↦ ℝ) i (FR x)
      rw [hnorm]
      exact hFRq.eLpNorm_lt_top
  have hbnorm : eLpNorm (hilbertifyVecField b) q.exponent
      (normalizedCubeMeasure (originCube d (m + 1))) =
      eLpNorm F q.exponent (normalizedCubeMeasure (originCube d m)) := by
    calc
      eLpNorm (hilbertifyVecField b) q.exponent
          (normalizedCubeMeasure (originCube d (m + 1))) =
        eLpNorm FR q.exponent (normalizedCubeMeasure (originCube d (m + 1))) := by
          apply eLpNorm_congr_norm_ae
          apply ae_of_all; intro x
          change ‖HilbertVec.ofVec (fun j ↦ if j = i then FR x else 0)‖ = ‖FR x‖
          have hs : (fun j ↦ if j = i then FR x else 0) = Pi.single i (FR x) := by
            funext j; by_cases hji : j = i
            · subst j; simp
            · simp [hji]
          rw [hs]
          exact PiLp.norm_single (2 : ℝ≥0∞) (fun _ : Fin d ↦ ℝ) i (FR x)
      _ = eLpNorm F q.exponent (normalizedCubeMeasure (originCube d m)) := by
        simpa only [FR] using
          eLpNorm_normalizedCubeMeasure_succ_originCube_cubeDirichletOddReflectionScalar F q
  have hrmeas : AEStronglyMeasurable r.toFun
      ((normalizedCubeMeasure (originCube d (m + 1))).restrict U) := by
    have hr2 : MemLp r.toFun 2 ((normalizedCubeMeasure (originCube d (m + 1))).restrict U) := by
      rw [normalizedCubeMeasure, cubeMeasure,
        volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
        Measure.restrict_smul, Measure.restrict_restrict_of_subset hUP]
      exact r.memL2.smul_measure ENNReal.ofReal_ne_top
    exact hr2.aestronglyMeasurable
  have hrq : MemLp r.toFun q.exponent
      ((normalizedCubeMeasure (originCube d (m + 1))).restrict U) :=
    ⟨hrmeas, lt_of_le_of_lt hrnorm hBtop⟩
  refine ⟨r, b, hrow, hb, hrowid, ?_, hbq, hbnorm, hrq, hrnorm⟩
  rfl

private theorem mutual_raw_identity {I C J D E A Hterm : ℝ}
    (hrow : I + C = -D - E)
    (hadjoint : I + A = -J)
    (hibp : C = -A - Hterm) :
    J = D + E - 2 * A - Hterm := by
  linarith

private noncomputable def sourceHessianRowRadialDatum
    {d : ℕ} {m : ℤ} (q : FiniteLpExponent)
    {u : H1Function (openCubeSet (originCube d m))}
    (H : HasWeakHessianOn (openCubeSet (originCube d m)) u)
    (i : Fin d) (n : ℕ) : CubeEuclideanL2LpField (originCube d m) q.conjugate :=
  INTERNAL.cubeRadialTruncationL2LpField (originCube d m) q
    (fun x j ↦ H.hess i j x)
    (by
      simpa only [hilbertifyVecField] using!
        (H.hessianHilbertRow_memLp_two i).aestronglyMeasurable) n

private theorem sourceHessianRowRadialDatum_memVectorL2
    {d : ℕ} {m : ℤ} (q : FiniteLpExponent)
    {u : H1Function (openCubeSet (originCube d m))}
    (H : HasWeakHessianOn (openCubeSet (originCube d m)) u)
    (i : Fin d) (n : ℕ) :
    MemVectorL2 (openCubeSet (originCube d m))
      (sourceHessianRowRadialDatum q H i n).toField := by
  apply INTERNAL.cubeRadialTruncation_memVectorL2

private theorem reflected_datum_parent_transport
    {d : ℕ} {m : ℤ} (q : FiniteLpExponent)
    (F : Vec d → ℝ) (i : Fin d) :
    eLpNorm (hilbertifyVecField
      (fun x j ↦ if j = i then
        cubeDirichletOddReflectionScalar (originCube d m) F x else 0))
        q.exponent (normalizedCubeMeasure (originCube d (m + 1))) =
      eLpNorm F q.exponent (normalizedCubeMeasure (originCube d m)) := by
  let FR : Vec d → ℝ := cubeDirichletOddReflectionScalar (originCube d m) F
  have hfield : (fun x j ↦ if j = i then
      cubeDirichletOddReflectionScalar (originCube d m) F x else 0) =
      (fun x j ↦ if j = i then FR x else 0) := by
    rfl
  have hsingle : ∀ x, (fun j ↦ if j = i then FR x else 0) = Pi.single i (FR x) := by
    intro x
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  rw [hfield]
  calc
    eLpNorm (hilbertifyVecField (fun x j ↦ if j = i then FR x else 0))
        q.exponent (normalizedCubeMeasure (originCube d (m + 1))) =
      eLpNorm FR q.exponent (normalizedCubeMeasure (originCube d (m + 1))) := by
        apply MeasureTheory.eLpNorm_congr_norm_ae
        exact MeasureTheory.ae_of_all _ fun x ↦ by
          change ‖HilbertVec.ofVec (fun j ↦ if j = i then FR x else 0)‖ = ‖FR x‖
          rw [hsingle x]
          exact PiLp.norm_single (2 : ℝ≥0∞) (fun _ : Fin d ↦ ℝ) i (FR x)
    _ = eLpNorm F q.exponent (normalizedCubeMeasure (originCube d m)) := by
      simpa only [FR] using
        eLpNorm_normalizedCubeMeasure_succ_originCube_cubeDirichletOddReflectionScalar F q

/-- The already-established scalar gradient theorem, restated in the raw
normalized-cube conventions used by the reflected Hessian argument. -/
private theorem source_gradient_below_two_bound
    {d : ℕ} [NeZero d] {q : FiniteLpExponent}
    (hq : q.exponent.toReal < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (F : Vec d → ℝ)
      (u : H10Function (openCubeSet (originCube d m))),
      MemLp F 2 (normalizedCubeMeasure (originCube d m)) →
      MemLp F q.exponent (normalizedCubeMeasure (originCube d m)) →
      CubeDirichletWeakPoissonProblem (originCube d m) u F →
      eLpNorm (hilbertifyVecField u.toH1Function.grad) q.exponent
        (normalizedCubeMeasure (originCube d m)) ≤
        C * ENNReal.ofReal (cubeScaleFactor (originCube d m)) *
          eLpNorm F q.exponent (normalizedCubeMeasure (originCube d m)) := by
  obtain ⟨C, hCtop, hC⟩ :=
    centeredCubeH10ScalarPoisson_gradient_cz_of_lt_two d q hq
  refine ⟨C, hCtop, ?_⟩
  intro m F u hF2 hFq hweak
  have hweak' : ∀ phi : H10Function (openCubeSet (originCube d m)),
      (1 : ℝ) * ∫ x, vecDot (u.toH1Function.grad x)
        (phi.toH1Function.grad x) ∂(centeredCubeDomain d m).normalizedVolume =
        ∫ x, F x * phi.toH1Function.toFun x
          ∂(centeredCubeDomain d m).normalizedVolume := by
    intro phi
    have hs := congrArg (fun z : ℝ =>
      (ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal • z)
      (hweak phi)
    simpa only [one_mul, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
      MeasureTheory.integral_smul_measure] using hs
  simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
    BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
    MeasureTheory.eLpNorm_norm, centeredCubeDomain,
    cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    ENNReal.ofReal_one, inv_one, mul_one] using!
    hC m 1 F u (by simpa only [centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using hF2)
      (by simpa only [centeredCubeDomain,
        cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using hFq)
      (by norm_num) hweak'

private theorem source_hessian_row_radial_pairing_moment
    {d : ℕ} {m : ℤ} (q : FiniteLpExponent)
    {u : H1Function (openCubeSet (originCube d m))}
    (H : HasWeakHessianOn (openCubeSet (originCube d m)) u)
    (i : Fin d) (n : ℕ) :
    let R : Vec d → Vec d := fun x j => H.hess i j x
    let Frow : Vec d → HilbertVec d := fun x => HilbertVec.ofVec (R x)
    let hRmeas : AEStronglyMeasurable Frow
      (volumeMeasureOn (openCubeSet (originCube d m))) :=
      (H.hessianHilbertRow_memLp_two i).aestronglyMeasurable
    let Gfield := INTERNAL.cubeRadialTruncationL2LpField
      (originCube d m) q R hRmeas n
    let μ := normalizedCubeMeasure (originCube d m)
    ∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n Frow x ∂μ =
      ENNReal.ofReal (∫ x, vecDot (R x) (Gfield.toField x) ∂μ) := by
  dsimp
  let R : Vec d → Vec d := fun x j => H.hess i j x
  let Frow : Vec d → HilbertVec d := fun x => HilbertVec.ofVec (R x)
  let hRmeas : AEStronglyMeasurable Frow
      (volumeMeasureOn (openCubeSet (originCube d m))) :=
    (H.hessianHilbertRow_memLp_two i).aestronglyMeasurable
  let Gfield := INTERNAL.cubeRadialTruncationL2LpField
    (originCube d m) q R hRmeas n
  let μ : Measure (Vec d) := normalizedCubeMeasure (originCube d m)
  have hRtwo : MemVectorL2 (openCubeSet (originCube d m)) R := by
    apply MeasureTheory.MemLp.of_eval
    intro j
    exact H.hess_memL2 i j
  have hGtwo : MemVectorL2 (openCubeSet (originCube d m)) Gfield.toField := by
    simpa only [Gfield] using INTERNAL.cubeRadialTruncation_memVectorL2
      (originCube d m) q R hRmeas n
  have hk : Integrable (fun x => vecDot (R x) (Gfield.toField x)) μ := by
    simpa only [μ, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using
      INTERNAL.centeredCube_integrable_vecDot_of_memVectorL2 m hRtwo hGtwo
  have hk0 : 0 ≤ᵐ[μ] fun x => vecDot (R x) (Gfield.toField x) := by
    filter_upwards with x
    change 0 ≤ vecDot (R x)
      (INTERNAL.vectorRadialTruncation q.exponent.toReal n R x)
    rw [vecDot_comm, INTERNAL.vecDot_vectorRadialTruncation_self]
    · split_ifs with hx
      · exact Real.rpow_nonneg (euclideanNorm_nonneg _) _
      · exact le_rfl
    · rw [← ENNReal.toReal_one]
      exact (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).mpr q.one_lt
  have hpoint : ∀ᵐ x ∂μ, ENNReal.ofReal
      (vecDot (R x) (Gfield.toField x)) =
        INTERNAL.truncatedMoment q.exponent.toReal n Frow x := by
    filter_upwards with x
    simpa only [Frow, Gfield, INTERNAL.cubeRadialTruncationL2LpField,
      INTERNAL.vectorRadialTruncation, HilbertVec.ofVec_toVec] using
      INTERNAL.ofReal_vecDot_vectorRadialTruncation_eq_truncatedMoment
        (show 1 < q.exponent.toReal by
          rw [← ENNReal.toReal_one]
          exact (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).mpr q.one_lt)
        n R x
  exact INTERNAL.lintegral_truncatedMoment_eq_ofReal_integral hk hk0 hpoint

private theorem source_hessian_row_radial_norm_eq_moment_rpow
    {d : ℕ} {m : ℤ} (q : FiniteLpExponent)
    {u : H1Function (openCubeSet (originCube d m))}
    (H : HasWeakHessianOn (openCubeSet (originCube d m))
      u) (i : Fin d) (n : ℕ) :
    eLpNorm (hilbertifyVecField
      (sourceHessianRowRadialDatum q H i n).toField)
      q.conjugate.exponent (normalizedCubeMeasure (originCube d m)) =
      (∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n
        (fun x => HilbertVec.ofVec (fun j => H.hess i j x)) x ∂
          normalizedCubeMeasure (originCube d m)) ^
        (1 - q.exponent.toReal⁻¹) := by
  let : ENNReal.HolderConjugate q.exponent q.conjugate.exponent := q.holderConjugate
  have hmoment := INTERNAL.eLpNorm_hilbertRadialTruncation_rpow_conjugate_eq_truncatedMoment
    (μ := normalizedCubeMeasure (originCube d m)) q n
    (fun x => HilbertVec.ofVec (fun j => H.hess i j x))
  have hqreal : 1 < q.exponent.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).mpr q.one_lt
  have hreal : q.exponent.toReal.HolderConjugate q.conjugate.exponent.toReal :=
    ENNReal.HolderConjugate.toReal hqreal
  have hexp : (q.conjugate.exponent.toReal)⁻¹ =
      1 - q.exponent.toReal⁻¹ := by
    have hsum := hreal.one_div_add_one_div
    rw [one_div] at hsum
    norm_num at hsum
    linarith
  have hr0 : q.conjugate.exponent.toReal ≠ 0 :=
    (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans q.conjugate.one_lt))
      q.conjugate.lt_top.ne).ne'
  change eLpNorm (INTERNAL.hilbertRadialTruncation q.exponent.toReal n
      (fun x => HilbertVec.ofVec (fun j => H.hess i j x)))
      q.conjugate.exponent (normalizedCubeMeasure (originCube d m)) = _
  calc
    eLpNorm (INTERNAL.hilbertRadialTruncation q.exponent.toReal n
        (fun x => HilbertVec.ofVec (fun j => H.hess i j x)))
        q.conjugate.exponent (normalizedCubeMeasure (originCube d m)) =
      (eLpNorm (INTERNAL.hilbertRadialTruncation q.exponent.toReal n
        (fun x => HilbertVec.ofVec (fun j => H.hess i j x)))
        q.conjugate.exponent (normalizedCubeMeasure (originCube d m)) ^
          q.conjugate.exponent.toReal) ^
          (q.conjugate.exponent.toReal)⁻¹ := by
            rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hr0, ENNReal.rpow_one]
    _ = _ := by rw [hmoment, hexp]

private theorem indicator_setIntegral_parent_eq_child
    {d : ℕ} {U P : Set (Vec d)} {f : Vec d → ℝ}
    (hU : MeasurableSet U) (hUP : U ⊆ P) :
    ∫ x in P, U.indicator f x ∂volume = ∫ x in U, f x ∂volume := by
  rw [MeasureTheory.integral_indicator hU, Measure.restrict_restrict hU,
    Set.inter_eq_left.mpr hUP]

private theorem row_weak_test_expanded
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (r v : H1Function U) (F : Vec d → Vec d) (η : Vec d → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ U)
    (hF : MemVectorL2 U F)
    (hrow : ∀ φ : H10Function U,
      ∫ x in U, vecDot (r.grad x) (φ.toH1Function.grad x) ∂volume =
        -∫ x in U, vecDot (F x) (φ.toH1Function.grad x) ∂volume) :
    let I := ∫ x in U, η x * vecDot (r.grad x) (v.grad x) ∂volume
    let C := ∫ x in U, v x * vecDot (r.grad x) (euclideanGradient η x) ∂volume
    let D := ∫ x in U, η x * vecDot (F x) (v.grad x) ∂volume
    let E := ∫ x in U, v x * vecDot (F x) (euclideanGradient η x) ∂volume
    I + C = -D - E := by
  dsimp
  let τ : H10Function U := v.mulContDiffHasCompactSupportToH10 hU
    hη hη_compact hη_sub
  let Vη : Vec d → Vec d := fun x j => η x * v.grad x j
  let Vdη : Vec d → Vec d := fun x j => v x * euclideanGradient η x j
  have hVη : MemVectorL2 U Vη := by
    apply MeasureTheory.MemLp.of_eval
    intro j
    exact WeakPoissonEquationOn.memScalarL2_mul_of_contDiff_hasCompactSupport_tsupport_subset
      (U := U) (V := U) hU.isOpen.measurableSet hη hη_compact hη_sub
      (v.gradMemL2 j)
  have hVdη : MemVectorL2 U Vdη := by
    apply MeasureTheory.MemLp.of_eval
    intro j
    have hbase : MemScalarL2 U
        (fun x => euclideanCoordDeriv j η x * v x) :=
      WeakPoissonEquationOn.memScalarL2_mul_of_contDiff_hasCompactSupport_tsupport_subset
        (U := U) (V := U) hU.isOpen.measurableSet
        (contDiff_euclideanCoordDeriv hη j)
        (hasCompactSupport_euclideanCoordDeriv hη_compact j)
        ((tsupport_euclideanCoordDeriv_subset_tsupport j η).trans hη_sub)
        v.memL2
    simpa only [Vdη, euclideanGradient, euclideanCoordDeriv, mul_comm] using hbase
  have hτgrad : (fun x => τ.toH1Function.grad x) =ᵐ[volume.restrict U]
      fun x => Vη x + Vdη x := by
    simpa only [τ, Vη, Vdη, euclideanGradient, euclideanCoordDeriv] using!
      WeakPoissonEquationOn.mulContDiffHasCompactSupportToH10_grad_ae
        v hU hη hη_compact hη_sub
  have hIint : IntegrableOn (fun x => vecDot (r.grad x) (Vη x)) U volume :=
    integrableOn_vecDot_of_memVectorL2 r.grad_memVectorL2 hVη
  have hCint : IntegrableOn (fun x => vecDot (r.grad x) (Vdη x)) U volume :=
    integrableOn_vecDot_of_memVectorL2 r.grad_memVectorL2 hVdη
  have hDint : IntegrableOn (fun x => vecDot (F x) (Vη x)) U volume :=
    integrableOn_vecDot_of_memVectorL2 hF hVη
  have hEint : IntegrableOn (fun x => vecDot (F x) (Vdη x)) U volume :=
    integrableOn_vecDot_of_memVectorL2 hF hVdη
  have hleft :
      ∫ x in U, vecDot (r.grad x) (τ.toH1Function.grad x) ∂volume =
        (∫ x in U, vecDot (r.grad x) (Vη x) ∂volume) +
          ∫ x in U, vecDot (r.grad x) (Vdη x) ∂volume := by
    calc
      ∫ x in U, vecDot (r.grad x) (τ.toH1Function.grad x) ∂volume =
          ∫ x in U, vecDot (r.grad x) (Vη x + Vdη x) ∂volume := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hτgrad] with x hx
        rw [hx]
      _ = ∫ x in U, (vecDot (r.grad x) (Vη x) +
          vecDot (r.grad x) (Vdη x)) ∂volume := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        simp only [vecDot, Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := MeasureTheory.integral_add hIint hCint
  have hright :
      ∫ x in U, vecDot (F x) (τ.toH1Function.grad x) ∂volume =
        (∫ x in U, vecDot (F x) (Vη x) ∂volume) +
          ∫ x in U, vecDot (F x) (Vdη x) ∂volume := by
    calc
      ∫ x in U, vecDot (F x) (τ.toH1Function.grad x) ∂volume =
          ∫ x in U, vecDot (F x) (Vη x + Vdη x) ∂volume := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hτgrad] with x hx
        rw [hx]
      _ = ∫ x in U, (vecDot (F x) (Vη x) +
          vecDot (F x) (Vdη x)) ∂volume := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        simp only [vecDot, Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := MeasureTheory.integral_add hDint hEint
  have htest := hrow τ
  rw [hleft, hright] at htest
  have hI :
      ∫ x in U, vecDot (r.grad x) (Vη x) ∂volume =
        ∫ x in U, η x * vecDot (r.grad x) (v.grad x) ∂volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    simp only [Vη, vecDot]
    calc
      ∑ i, r.grad x i * (η x * v.grad x i) =
          ∑ i, η x * (r.grad x i * v.grad x i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hC :
      ∫ x in U, vecDot (r.grad x) (Vdη x) ∂volume =
        ∫ x in U, v x * vecDot (r.grad x) (euclideanGradient η x) ∂volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    simp only [Vdη, vecDot]
    calc
      ∑ i, r.grad x i * (v x * euclideanGradient η x i) =
          ∑ i, v x * (r.grad x i * euclideanGradient η x i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hD :
      ∫ x in U, vecDot (F x) (Vη x) ∂volume =
        ∫ x in U, η x * vecDot (F x) (v.grad x) ∂volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    simp only [Vη, vecDot]
    calc
      ∑ i, F x i * (η x * v.grad x i) =
          ∑ i, η x * (F x i * v.grad x i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hE :
      ∫ x in U, vecDot (F x) (Vdη x) ∂volume =
        ∫ x in U, v x * vecDot (F x) (euclideanGradient η x) ∂volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    simp only [Vdη, vecDot]
    calc
      ∑ i, F x i * (v x * euclideanGradient η x i) =
          ∑ i, v x * (F x i * euclideanGradient η x i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [Finset.mul_sum]
  rw [hI, hC, hD, hE] at htest
  linarith

private theorem parent_weak_test_expanded
    {d : ℕ} {U P : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hPopen : IsOpen P) (hUP : U ⊆ P)
    (r : H1Function U) (vP : H1Function P) (G : Vec d → Vec d)
    (η : Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ U)
    (hparent : ∀ ψ : H10Function P,
      ∫ x in P, vecDot (vP.grad x) (ψ.toH1Function.grad x) ∂volume =
        -∫ x in P, vecDot (G x) (ψ.toH1Function.grad x) ∂volume) :
    let I := ∫ x in U, η x * vecDot (vP.grad x) (r.grad x) ∂volume
    let A := ∫ x in U, r x * vecDot (vP.grad x) (euclideanGradient η x) ∂volume
    let J := ∫ x in U, vecDot (G x)
      (fun j => η x * r.grad x j + r x * euclideanGradient η x j) ∂volume
    I + A = -J := by
  dsimp
  let σU : H10Function U := r.mulContDiffHasCompactSupportToH10 hU
    hη hη_compact hη_sub
  let σP : H10Function P := σU.extendByZeroToOpenSuperset
    hU.isOpen.measurableSet hPopen hUP
  let Rη : Vec d → Vec d := fun x j => η x * r.grad x j
  let Rdη : Vec d → Vec d := fun x j => r x * euclideanGradient η x j
  have hRη : MemVectorL2 U Rη := by
    apply MeasureTheory.MemLp.of_eval
    intro j
    exact WeakPoissonEquationOn.memScalarL2_mul_of_contDiff_hasCompactSupport_tsupport_subset
      (U := U) (V := U) hU.isOpen.measurableSet hη hη_compact hη_sub
      (r.gradMemL2 j)
  have hRdη : MemVectorL2 U Rdη := by
    apply MeasureTheory.MemLp.of_eval
    intro j
    have hbase : MemScalarL2 U
        (fun x => euclideanCoordDeriv j η x * r x) :=
      WeakPoissonEquationOn.memScalarL2_mul_of_contDiff_hasCompactSupport_tsupport_subset
        (U := U) (V := U) hU.isOpen.measurableSet
        (contDiff_euclideanCoordDeriv hη j)
        (hasCompactSupport_euclideanCoordDeriv hη_compact j)
        ((tsupport_euclideanCoordDeriv_subset_tsupport j η).trans hη_sub)
        r.memL2
    simpa only [Rdη, euclideanGradient, euclideanCoordDeriv, mul_comm] using hbase
  have hσUgrad : (fun x => σU.toH1Function.grad x) =ᵐ[volume.restrict U]
      fun x => Rη x + Rdη x := by
    simpa only [σU, Rη, Rdη, euclideanGradient, euclideanCoordDeriv] using!
      WeakPoissonEquationOn.mulContDiffHasCompactSupportToH10_grad_ae
        r hU hη hη_compact hη_sub
  have hσPgrad : σP.toH1Function.grad = σU.zeroExtensionGrad := by
    simpa only [σP] using H10Function.extendByZeroToOpenSuperset_grad
      σU hU.isOpen.measurableSet hPopen hUP
  have hleft_indicator :
      (fun x => vecDot (vP.grad x) (σP.toH1Function.grad x)) =
        U.indicator (fun x => vecDot (vP.grad x) (σU.toH1Function.grad x)) := by
    funext x
    rw [hσPgrad]
    by_cases hx : x ∈ U
    · simp only [H10Function.zeroExtensionGrad_apply_of_mem _ hx, Set.indicator_of_mem hx]
    · simp only [H10Function.zeroExtensionGrad_apply_of_not_mem _ hx,
        Set.indicator_of_notMem hx, vecDot_zero_right]
  have hright_indicator :
      (fun x => vecDot (G x) (σP.toH1Function.grad x)) =
        U.indicator (fun x => vecDot (G x) (σU.toH1Function.grad x)) := by
    funext x
    rw [hσPgrad]
    by_cases hx : x ∈ U
    · simp only [H10Function.zeroExtensionGrad_apply_of_mem _ hx, Set.indicator_of_mem hx]
    · simp only [H10Function.zeroExtensionGrad_apply_of_not_mem _ hx,
        Set.indicator_of_notMem hx, vecDot_zero_right]
  have hparent_test := hparent σP
  rw [hleft_indicator, hright_indicator,
    indicator_setIntegral_parent_eq_child hU.isOpen.measurableSet hUP,
    indicator_setIntegral_parent_eq_child hU.isOpen.measurableSet hUP] at hparent_test
  have hleft_expand :
      ∫ x in U, vecDot (vP.grad x) (σU.toH1Function.grad x) ∂volume =
        ∫ x in U, vecDot (vP.grad x) (Rη x + Rdη x) ∂volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hσUgrad] with x hx
    rw [hx]
  have hright_expand :
      ∫ x in U, vecDot (G x) (σU.toH1Function.grad x) ∂volume =
        ∫ x in U, vecDot (G x) (Rη x + Rdη x) ∂volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hσUgrad] with x hx
    rw [hx]
  rw [hleft_expand, hright_expand] at hparent_test
  let vU : H1Function U := vP.restrict hU.isOpen hUP
  have hIint : IntegrableOn (fun x => vecDot (vP.grad x) (Rη x)) U volume := by
    simpa only [vU, H1Function.restrict] using
      integrableOn_vecDot_of_memVectorL2 vU.grad_memVectorL2 hRη
  have hAint : IntegrableOn (fun x => vecDot (vP.grad x) (Rdη x)) U volume := by
    simpa only [vU, H1Function.restrict] using
      integrableOn_vecDot_of_memVectorL2 vU.grad_memVectorL2 hRdη
  have hsplit :
      ∫ x in U, vecDot (vP.grad x) (Rη x + Rdη x) ∂volume =
        (∫ x in U, vecDot (vP.grad x) (Rη x) ∂volume) +
          ∫ x in U, vecDot (vP.grad x) (Rdη x) ∂volume := by
    rw [show (fun x => vecDot (vP.grad x) (Rη x + Rdη x)) =
        fun x => vecDot (vP.grad x) (Rη x) + vecDot (vP.grad x) (Rdη x) by
      funext x
      simp only [vecDot, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    exact MeasureTheory.integral_add hIint hAint
  rw [hsplit] at hparent_test
  have hI :
      ∫ x in U, vecDot (vP.grad x) (Rη x) ∂volume =
        ∫ x in U, η x * vecDot (vP.grad x) (r.grad x) ∂volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    simp only [Rη, vecDot]
    calc
      ∑ i, vP.grad x i * (η x * r.grad x i) =
          ∑ i, η x * (vP.grad x i * r.grad x i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hA :
      ∫ x in U, vecDot (vP.grad x) (Rdη x) ∂volume =
        ∫ x in U, r x * vecDot (vP.grad x) (euclideanGradient η x) ∂volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    simp only [Rdη, vecDot]
    calc
      ∑ i, vP.grad x i * (r x * euclideanGradient η x i) =
          ∑ i, r x * (vP.grad x i * euclideanGradient η x i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [Finset.mul_sum]
  rw [hI, hA] at hparent_test
  simpa only [Rη, Rdη] using! hparent_test

private theorem localized_four_term_bound
    {J D E A Hterm BD BE BA BH : ℝ}
    (hidentity : J = D + E - 2 * A - Hterm)
    (hD : |D| ≤ BD) (hE : |E| ≤ BE) (hA : |A| ≤ BA) (hH : |Hterm| ≤ BH) :
    J ≤ BD + BE + 2 * BA + BH := by
  have hD' : D ≤ BD := (le_abs_self D).trans hD
  have hE' : E ≤ BE := (le_abs_self E).trans hE
  have hA' : -A ≤ BA := by
    calc -A ≤ |-A| := le_abs_self (-A)
      _ = |A| := abs_neg A
      _ ≤ BA := hA
  have hH' : -Hterm ≤ BH := by
    calc -Hterm ≤ |-Hterm| := le_abs_self (-Hterm)
      _ = |Hterm| := abs_neg Hterm
      _ ≤ BH := hH
  rw [hidentity]
  linarith

private theorem normalized_holder_pairing
    {d : ℕ} {Q : TriadicCube d} {q : FiniteLpExponent}
    (F G : Vec d → Vec d)
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) q.exponent
      (normalizedCubeMeasure Q))
    (hG : MemLp (fun x => HilbertVec.ofVec (G x)) q.conjugate.exponent
      (normalizedCubeMeasure Q)) :
    |∫ x, vecDot (F x) (G x) ∂(normalizedCubeMeasure Q)| ≤
      (eLpNorm (fun x => HilbertVec.ofVec (F x)) q.exponent
        (normalizedCubeMeasure Q)).toReal *
      (eLpNorm (fun x => HilbertVec.ofVec (G x)) q.conjugate.exponent
        (normalizedCubeMeasure Q)).toReal := by
  let : ENNReal.HolderConjugate q.exponent q.conjugate.exponent := q.holderConjugate
  exact INTERNAL.abs_integral_vecDot_le_eLpNorm_toReal_mul hF hG

private theorem rowValue_restrict_transport
    {d : ℕ} {m : ℤ} (q : FiniteLpExponent)
    {u : H1Function (openCubeSet (originCube d m))}
    {uP : H1Function (openCubeSet (originCube d (m + 1)))}
    (huPgrad : uP.grad = cubeDirichletOddReflectionVectorField
      (originCube d m) (fun y ↦ u.grad y))
    {uU : H1Function (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ))}
    (huUgrad : uU.grad = uP.grad)
    (HU : HasWeakHessianOn
      (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ)) uU)
    (i : Fin d) {B : ℝ≥0∞}
    (hgrad : eLpNorm (hilbertifyVecField u.grad) q.exponent
      (normalizedCubeMeasure (originCube d m)) ≤ B) :
    eLpNorm (HU.gradCoordH1Function i).toFun q.exponent
      ((normalizedCubeMeasure (originCube d (m + 1))).restrict
        (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ))) ≤ B := by
  let Q : TriadicCube d := originCube d m
  let U : Set (Vec d) := scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ)
  let refl : Vec d → ℝ :=
    cubeDirichletOddReflectionGradientCoordScalar Q i (fun y ↦ u.grad y i)
  have hscalar : (fun x ↦ uU.grad x i) = refl := by
    funext x
    have hx := congrArg (fun G : Vec d → Vec d ↦ G x i)
      (huUgrad.trans huPgrad)
    change uU.grad x i =
      cubeDirichletOddReflectionVectorField Q (fun y ↦ u.grad y) x i at hx
    rw [hx]
    simp only [refl, cubeDirichletOddReflectionGradientCoordScalar,
      cubeDirichletOddReflectionVectorField,
      cubeCoordinateFoldReflectedVectorField, Pi.smul_apply, smul_eq_mul]
    ring
  calc
    eLpNorm (HU.gradCoordH1Function i).toFun q.exponent
        ((normalizedCubeMeasure (originCube d (m + 1))).restrict U) =
      eLpNorm refl q.exponent
        ((normalizedCubeMeasure (originCube d (m + 1))).restrict U) := by
          change eLpNorm (fun x ↦ uU.grad x i) q.exponent
            ((normalizedCubeMeasure (originCube d (m + 1))).restrict U) = _
          rw [hscalar]
    _ ≤ eLpNorm refl q.exponent (normalizedCubeMeasure (originCube d (m + 1))) :=
      eLpNorm_mono_measure refl Measure.restrict_le_self
    _ = eLpNorm (fun y ↦ u.grad y i) q.exponent
        (normalizedCubeMeasure (originCube d m)) := by
      simpa only [refl, Q] using
        eLpNorm_normalizedCubeMeasure_succ_originCube_gradientCoordScalar i
          (fun y ↦ u.grad y i) q
    _ ≤ eLpNorm (hilbertifyVecField u.grad) q.exponent
        (normalizedCubeMeasure (originCube d m)) :=
      coordinate_eLpNorm_le_euclidean _ q u.grad i
    _ ≤ B := hgrad

private theorem restricted_raw_holder_vec
    {d : ℕ} (Q : TriadicCube d) (q : FiniteLpExponent)
    (U : Set (Vec d)) (hU : MeasurableSet U) (hUP : U ⊆ openCubeSet Q)
    (F G : Vec d → Vec d)
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) q.exponent
      (normalizedCubeMeasure Q))
    (hG : MemLp (fun x => HilbertVec.ofVec (G x)) q.conjugate.exponent
      (normalizedCubeMeasure Q)) :
    |∫ x in U, vecDot (F x) (G x) ∂volume| ≤ cubeVolume Q *
        (eLpNorm (fun x => HilbertVec.ofVec (F x)) q.exponent
          (normalizedCubeMeasure Q)).toReal *
        (eLpNorm (fun x => HilbertVec.ofVec (G x)) q.conjugate.exponent
          (normalizedCubeMeasure Q)).toReal := by
  let : ENNReal.HolderConjugate q.exponent q.conjugate.exponent := q.holderConjugate
  let μ : Measure (Vec d) := normalizedCubeMeasure Q
  let Iraw : ℝ := ∫ x in U, vecDot (F x) (G x) ∂volume
  let Inorm : ℝ := ∫ x, vecDot (F x) (Set.indicator U G x) ∂μ
  have hGind : MemLp (fun x => HilbertVec.ofVec (Set.indicator U G x))
      q.conjugate.exponent μ := by
    have heq : (fun x => HilbertVec.ofVec (Set.indicator U G x)) =
        Set.indicator U (fun x => HilbertVec.ofVec (G x)) := by
      funext x; by_cases hx : x ∈ U <;> simp [hx]
    rw [heq]
    exact hG.indicator hU
  have hholder := INTERNAL.abs_integral_vecDot_le_eLpNorm_toReal_mul hF hGind
  have hGind_norm : eLpNorm (fun x => HilbertVec.ofVec (Set.indicator U G x))
      q.conjugate.exponent μ ≤
      eLpNorm (fun x => HilbertVec.ofVec (G x)) q.conjugate.exponent μ := by
    apply eLpNorm_mono_ae
    filter_upwards with x
    by_cases hx : x ∈ U <;> simp [hx]
  have hμ : μ = ENNReal.ofReal ((cubeVolume Q)⁻¹) • volume.restrict (openCubeSet Q) := by
    change normalizedCubeMeasure Q = _
    rw [normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  have hInorm : Inorm = (cubeVolume Q)⁻¹ * Iraw := by
    change ∫ x, vecDot (F x) (Set.indicator U G x) ∂μ = _
    rw [hμ, integral_smul_measure, smul_eq_mul]
    have hindicator : (fun x => vecDot (F x) (Set.indicator U G x)) =
        Set.indicator U (fun x => vecDot (F x) (G x)) := by
      funext x; by_cases hx : x ∈ U <;> simp [hx, vecDot]
    rw [hindicator, integral_indicator hU,
      Measure.restrict_restrict_of_subset hUP]
    simp only [Iraw, ENNReal.toReal_ofReal (inv_nonneg.mpr (cubeVolume_pos Q).le)]
  have hIraw : Iraw = cubeVolume Q * Inorm := by
    rw [hInorm]
    field_simp [(cubeVolume_pos Q).ne']
  have hraw_abs : |Iraw| = cubeVolume Q * |Inorm| := by
    rw [hIraw, abs_mul, abs_of_nonneg (cubeVolume_pos Q).le]
  have hholder' : |Inorm| ≤
      (eLpNorm (fun x => HilbertVec.ofVec (F x)) q.exponent μ).toReal *
        (eLpNorm (fun x => HilbertVec.ofVec (Set.indicator U G x))
          q.conjugate.exponent μ).toReal := by simpa only [Inorm] using hholder
  have hright :
      (eLpNorm (fun x => HilbertVec.ofVec (F x)) q.exponent μ).toReal *
          (eLpNorm (fun x => HilbertVec.ofVec (Set.indicator U G x))
            q.conjugate.exponent μ).toReal ≤
        (eLpNorm (fun x => HilbertVec.ofVec (F x)) q.exponent μ).toReal *
          (eLpNorm (fun x => HilbertVec.ofVec (G x))
            q.conjugate.exponent μ).toReal := by
    exact mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono hG.eLpNorm_ne_top hGind_norm) ENNReal.toReal_nonneg
  change |Iraw| ≤ _
  rw [hraw_abs]
  refine (mul_le_mul_of_nonneg_left (hholder'.trans hright)
    (cubeVolume_pos Q).le).trans_eq ?_
  simp only [μ, mul_assoc]

private theorem scalar_indicator_mul_bounded_memLp_and_norm
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    (U : Set α) (hU : MeasurableSet U) (r L : α → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hr : MemLp r p (μ.restrict U))
    (hL : AEStronglyMeasurable L (μ.restrict U))
    (hLbound : ∀ x, |L x| ≤ C) :
    MemLp (U.indicator (fun x ↦ r x * L x)) p μ ∧
    eLpNorm (U.indicator (fun x ↦ r x * L x)) p μ ≤
      C.toNNReal • eLpNorm r p (μ.restrict U) := by
  have hlocal : MemLp (fun x ↦ r x * L x) p (μ.restrict U) := by
    refine MemLp.of_le_mul (c := C) hr ?_ ?_
    · exact hr.aestronglyMeasurable.mul hL
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul]
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_left (hLbound x) (abs_nonneg (r x)))
  constructor
  · rw [memLp_indicator_iff_restrict hU]; exact hlocal
  · rw [eLpNorm_indicator_eq_eLpNorm_restrict hU]
    apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
    filter_upwards with x
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
    apply ENNReal.coe_le_coe.mpr
    refine (NNReal.coe_le_coe).mp ?_
    change ‖r x * L x‖ ≤ (C.toNNReal : ℝ) * ‖r x‖
    rw [Real.norm_eq_abs, abs_mul]
    simpa [Real.coe_toNNReal _ hC, mul_comm] using
      (mul_le_mul_of_nonneg_left (hLbound x) (abs_nonneg (r x)))

private theorem scalar_single_hilbert_memLp_and_norm
    {α : Type*} [MeasurableSpace α] {d : ℕ} (i : Fin d)
    {μ : Measure α} {p : ℝ≥0∞} (f : α → ℝ) (hf : MemLp f p μ) :
    MemLp (fun x ↦ HilbertVec.ofVec (Pi.single i (f x))) p μ ∧
    eLpNorm (fun x ↦ HilbertVec.ofVec (Pi.single i (f x))) p μ =
      eLpNorm f p μ := by
  let L : ℝ →L[ℝ] HilbertVec d :=
    (HilbertVec.ofVecL d).comp (ContinuousLinearMap.single ℝ (fun _ : Fin d ↦ ℝ) i)
  have hmeas : AEStronglyMeasurable (fun x ↦ HilbertVec.ofVec (Pi.single i (f x))) μ := by
    change AEStronglyMeasurable (L ∘ f) μ
    exact L.continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable
  have henorm : eLpNorm (fun x ↦ HilbertVec.ofVec (Pi.single i (f x))) p μ =
      eLpNorm f p μ := by
    apply eLpNorm_congr_norm_ae
    apply ae_of_all; intro x
    exact PiLp.norm_single (2 : ℝ≥0∞) (fun _ : Fin d ↦ ℝ) i (f x)
  exact ⟨⟨hmeas, henorm.symm ▸ hf.eLpNorm_lt_top⟩, henorm⟩

private theorem localized_Hterm_raw_bound
    {d : ℕ} (Q : TriadicCube d) (q : FiniteLpExponent) (i : Fin d)
    (U : Set (Vec d)) (hU : MeasurableSet U) (hUP : U ⊆ openCubeSet Q)
    (r v L : Vec d → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hr : MemLp r q.exponent ((normalizedCubeMeasure Q).restrict U))
    (hL : AEStronglyMeasurable L ((normalizedCubeMeasure Q).restrict U))
    (hLbound : ∀ x, |L x| ≤ C)
    (hv : MemLp v q.conjugate.exponent (normalizedCubeMeasure Q)) :
    |∫ x in U, r x * v x * L x ∂volume| ≤ cubeVolume Q *
        (C.toNNReal • eLpNorm r q.exponent
          ((normalizedCubeMeasure Q).restrict U)).toReal *
        (eLpNorm v q.conjugate.exponent (normalizedCubeMeasure Q)).toReal := by
  obtain ⟨hrL, hrLnorm⟩ :=
    scalar_indicator_mul_bounded_memLp_and_norm U hU r L hC hr hL hLbound
  obtain ⟨hrLvec, hrLveceq⟩ := scalar_single_hilbert_memLp_and_norm i
    (U.indicator (fun x ↦ r x * L x)) hrL
  obtain ⟨hvvec, hvveceq⟩ := scalar_single_hilbert_memLp_and_norm i v hv
  have hraw := restricted_raw_holder_vec Q q U hU hUP
    (fun x ↦ Pi.single i (U.indicator (fun y ↦ r y * L y) x))
    (fun x ↦ Pi.single i (v x)) hrLvec hvvec
  have hdot : ∀ x : Vec d, vecDot (Pi.single i (U.indicator (fun y ↦ r y * L y) x))
      (Pi.single i (v x)) = U.indicator (fun y ↦ r y * L y) x * v x := by
    intro x; classical
    rw [vecDot, Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [hji]
    · simp
  have hraw' : |∫ x in U, r x * v x * L x ∂volume| ≤ cubeVolume Q *
      (eLpNorm (fun x ↦ HilbertVec.ofVec
        (Pi.single i (U.indicator (fun y ↦ r y * L y) x))) q.exponent
        (normalizedCubeMeasure Q)).toReal *
      (eLpNorm (fun x ↦ HilbertVec.ofVec (Pi.single i (v x)))
        q.conjugate.exponent (normalizedCubeMeasure Q)).toReal := by
    calc
      |∫ x in U, r x * v x * L x ∂volume| =
        |∫ x in U, vecDot (Pi.single i (U.indicator (fun y ↦ r y * L y) x))
          (Pi.single i (v x)) ∂volume| := by
            congr 1; apply setIntegral_congr_fun hU
            intro x hx
            change r x * v x * L x = vecDot (Pi.single i (U.indicator (fun y ↦ r y * L y) x))
              (Pi.single i (v x))
            rw [hdot]; simp [hx]; ring
      _ ≤ _ := hraw
  rw [hrLveceq, hvveceq] at hraw'
  apply hraw'.trans
  have hsmultop : C.toNNReal • eLpNorm r q.exponent
      ((normalizedCubeMeasure Q).restrict U) ≠ ∞ := by
    rw [ENNReal.smul_def]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hr.eLpNorm_ne_top
  have hnormmono := ENNReal.toReal_mono hsmultop hrLnorm
  calc
    cubeVolume Q * (eLpNorm (U.indicator (fun x ↦ r x * L x)) q.exponent
      (normalizedCubeMeasure Q)).toReal *
      (eLpNorm v q.conjugate.exponent (normalizedCubeMeasure Q)).toReal =
      (cubeVolume Q * (eLpNorm v q.conjugate.exponent
        (normalizedCubeMeasure Q)).toReal) *
        (eLpNorm (U.indicator (fun x ↦ r x * L x)) q.exponent
          (normalizedCubeMeasure Q)).toReal := by ring
    _ ≤ (cubeVolume Q * (eLpNorm v q.conjugate.exponent
        (normalizedCubeMeasure Q)).toReal) *
        (C.toNNReal • eLpNorm r q.exponent ((normalizedCubeMeasure Q).restrict U)).toReal :=
      mul_le_mul_of_nonneg_left hnormmono
        (mul_nonneg (cubeVolume_pos Q).le ENNReal.toReal_nonneg)
    _ = _ := by ring

private theorem localized_Aterm_raw_bound
    {d : ℕ} (Q : TriadicCube d) (q : FiniteLpExponent) (i : Fin d)
    (U : Set (Vec d)) (hU : MeasurableSet U) (hUP : U ⊆ openCubeSet Q)
    (r : Vec d → ℝ) (V E : Vec d → Vec d) {C : ℝ} (hC : 0 ≤ C)
    (hr : MemLp r q.exponent ((normalizedCubeMeasure Q).restrict U))
    (hV : MemLp (fun x ↦ HilbertVec.ofVec (V x)) q.conjugate.exponent
      (normalizedCubeMeasure Q))
    (hE : AEStronglyMeasurable (fun x ↦ HilbertVec.ofVec (E x))
      (normalizedCubeMeasure Q))
    (hEbound : ∀ x, ‖HilbertVec.ofVec (E x)‖ ≤ C) :
    |∫ x in U, r x * vecDot (V x) (E x) ∂volume| ≤ cubeVolume Q *
      (eLpNorm r q.exponent ((normalizedCubeMeasure Q).restrict U)).toReal *
      (C.toNNReal • eLpNorm (fun x ↦ HilbertVec.ofVec (V x))
        q.conjugate.exponent (normalizedCubeMeasure Q)).toReal := by
  let μ : Measure (Vec d) := normalizedCubeMeasure Q
  let dot : Vec d → ℝ := fun x ↦ vecDot (V x) (E x)
  have hdotmeas : AEStronglyMeasurable dot μ := by
    have h : AEStronglyMeasurable
        (fun x ↦ inner ℝ (HilbertVec.ofVec (V x)) (HilbertVec.ofVec (E x))) μ :=
      hV.aestronglyMeasurable.inner hE
    simpa only [dot, HilbertVec.inner_def] using h
  have hdot : MemLp dot q.conjugate.exponent μ := by
    refine MemLp.of_le_mul (c := C) hV hdotmeas ?_
    filter_upwards with x
    calc
      ‖dot x‖ = |inner ℝ (HilbertVec.ofVec (V x)) (HilbertVec.ofVec (E x))| := by
        simp only [dot, HilbertVec.inner_def, Real.norm_eq_abs]
      _ ≤ ‖HilbertVec.ofVec (V x)‖ * ‖HilbertVec.ofVec (E x)‖ := by
        simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ)
          (HilbertVec.ofVec (V x)) (HilbertVec.ofVec (E x))
      _ ≤ ‖HilbertVec.ofVec (V x)‖ * C :=
        mul_le_mul_of_nonneg_left (hEbound x) (norm_nonneg _)
      _ = C * ‖HilbertVec.ofVec (V x)‖ := by ring
  have hrind : MemLp (U.indicator r) q.exponent μ := by
    rw [memLp_indicator_iff_restrict hU]; exact hr
  have hrindeq : eLpNorm (U.indicator r) q.exponent μ =
      eLpNorm r q.exponent (μ.restrict U) := eLpNorm_indicator_eq_eLpNorm_restrict hU
  obtain ⟨hrvec, hrveceq⟩ := scalar_single_hilbert_memLp_and_norm i (U.indicator r) hrind
  obtain ⟨hdotvec, hdotveceq⟩ := scalar_single_hilbert_memLp_and_norm i dot hdot
  have hraw := restricted_raw_holder_vec Q q U hU hUP
    (fun x ↦ Pi.single i (U.indicator r x)) (fun x ↦ Pi.single i (dot x)) hrvec hdotvec
  have hdot_single : ∀ x : Vec d, vecDot (Pi.single i (U.indicator r x))
      (Pi.single i (dot x)) = U.indicator r x * dot x := by
    intro x; classical
    rw [vecDot, Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [hji]
    · simp
  have hraw' : |∫ x in U, r x * vecDot (V x) (E x) ∂volume| ≤ cubeVolume Q *
      (eLpNorm (fun x ↦ HilbertVec.ofVec (Pi.single i (U.indicator r x)))
        q.exponent μ).toReal *
      (eLpNorm (fun x ↦ HilbertVec.ofVec (Pi.single i (dot x)))
        q.conjugate.exponent μ).toReal := by
    calc
      |∫ x in U, r x * vecDot (V x) (E x) ∂volume| =
        |∫ x in U, vecDot (Pi.single i (U.indicator r x))
          (Pi.single i (dot x)) ∂volume| := by
          congr 1; apply setIntegral_congr_fun hU
          intro x hx
          change r x * vecDot (V x) (E x) =
            vecDot (Pi.single i (U.indicator r x)) (Pi.single i (dot x))
          rw [hdot_single]; simp [hx, dot]
      _ ≤ _ := hraw
  rw [hrveceq, hdotveceq, hrindeq] at hraw'
  apply hraw'.trans
  have hsmultop : C.toNNReal • eLpNorm (fun x ↦ HilbertVec.ofVec (V x))
      q.conjugate.exponent μ ≠ ∞ := by
    rw [ENNReal.smul_def]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hV.eLpNorm_ne_top
  have hdotnorm : eLpNorm dot q.conjugate.exponent μ ≤ C.toNNReal •
      eLpNorm (fun x ↦ HilbertVec.ofVec (V x)) q.conjugate.exponent μ := by
    apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
    filter_upwards with x
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
    apply ENNReal.coe_le_coe.mpr
    refine (NNReal.coe_le_coe).mp ?_
    change ‖dot x‖ ≤ (C.toNNReal : ℝ) * ‖HilbertVec.ofVec (V x)‖
    simpa [Real.coe_toNNReal _ hC] using (show ‖dot x‖ ≤ C * ‖HilbertVec.ofVec (V x)‖ by
      calc
        ‖dot x‖ = |inner ℝ (HilbertVec.ofVec (V x)) (HilbertVec.ofVec (E x))| := by
          simp only [dot, HilbertVec.inner_def, Real.norm_eq_abs]
        _ ≤ ‖HilbertVec.ofVec (V x)‖ * ‖HilbertVec.ofVec (E x)‖ := by
          simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ)
            (HilbertVec.ofVec (V x)) (HilbertVec.ofVec (E x))
        _ ≤ ‖HilbertVec.ofVec (V x)‖ * C :=
          mul_le_mul_of_nonneg_left (hEbound x) (norm_nonneg _)
        _ = C * ‖HilbertVec.ofVec (V x)‖ := by ring)
  have hnormmono := ENNReal.toReal_mono hsmultop hdotnorm
  calc
    cubeVolume Q * (eLpNorm r q.exponent ((normalizedCubeMeasure Q).restrict U)).toReal *
      (eLpNorm dot q.conjugate.exponent μ).toReal =
      (cubeVolume Q * (eLpNorm r q.exponent ((normalizedCubeMeasure Q).restrict U)).toReal) *
        (eLpNorm dot q.conjugate.exponent μ).toReal := by ring
    _ ≤ (cubeVolume Q * (eLpNorm r q.exponent ((normalizedCubeMeasure Q).restrict U)).toReal) *
        (C.toNNReal • eLpNorm (fun x ↦ HilbertVec.ofVec (V x)) q.conjugate.exponent μ).toReal :=
      mul_le_mul_of_nonneg_left hnormmono
        (mul_nonneg (cubeVolume_pos Q).le ENNReal.toReal_nonneg)
    _ = _ := by ring

private theorem localized_Eterm_raw_bound
    {d : ℕ} (Q : TriadicCube d) (q : FiniteLpExponent) (i : Fin d)
    (U : Set (Vec d)) (hU : MeasurableSet U) (hUP : U ⊆ openCubeSet Q)
    (b E : Vec d → Vec d) (v : Vec d → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hb : MemLp (fun x ↦ HilbertVec.ofVec (b x)) q.exponent (normalizedCubeMeasure Q))
    (hE : AEStronglyMeasurable (fun x ↦ HilbertVec.ofVec (E x)) (normalizedCubeMeasure Q))
    (hEbound : ∀ x, ‖HilbertVec.ofVec (E x)‖ ≤ C)
    (hv : MemLp v q.conjugate.exponent (normalizedCubeMeasure Q)) :
    |∫ x in U, v x * vecDot (b x) (E x) ∂volume| ≤ cubeVolume Q *
      (C.toNNReal • eLpNorm (fun x ↦ HilbertVec.ofVec (b x)) q.exponent
        (normalizedCubeMeasure Q)).toReal *
      (eLpNorm v q.conjugate.exponent (normalizedCubeMeasure Q)).toReal := by
  let μ : Measure (Vec d) := normalizedCubeMeasure Q
  let dot : Vec d → ℝ := fun x ↦ vecDot (b x) (E x)
  have hdotmeas : AEStronglyMeasurable dot μ := by
    have h : AEStronglyMeasurable
        (fun x ↦ inner ℝ (HilbertVec.ofVec (b x)) (HilbertVec.ofVec (E x))) μ :=
      hb.aestronglyMeasurable.inner hE
    simpa only [dot, HilbertVec.inner_def] using h
  have hdot : MemLp dot q.exponent μ := by
    refine MemLp.of_le_mul (c := C) hb hdotmeas ?_
    filter_upwards with x
    calc
      ‖dot x‖ = |inner ℝ (HilbertVec.ofVec (b x)) (HilbertVec.ofVec (E x))| := by
        simp only [dot, HilbertVec.inner_def, Real.norm_eq_abs]
      _ ≤ ‖HilbertVec.ofVec (b x)‖ * ‖HilbertVec.ofVec (E x)‖ := by
        simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ)
          (HilbertVec.ofVec (b x)) (HilbertVec.ofVec (E x))
      _ ≤ ‖HilbertVec.ofVec (b x)‖ * C :=
        mul_le_mul_of_nonneg_left (hEbound x) (norm_nonneg _)
      _ = C * ‖HilbertVec.ofVec (b x)‖ := by ring
  obtain ⟨hdotvec, hdotveceq⟩ := scalar_single_hilbert_memLp_and_norm i dot hdot
  obtain ⟨hvvec, hvveceq⟩ := scalar_single_hilbert_memLp_and_norm i v hv
  have hraw := restricted_raw_holder_vec Q q U hU hUP
    (fun x ↦ Pi.single i (dot x)) (fun x ↦ Pi.single i (v x)) hdotvec hvvec
  have hdot_single : ∀ x : Vec d,
      vecDot (Pi.single i (dot x)) (Pi.single i (v x)) = dot x * v x := by
    intro x; classical
    rw [vecDot, Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [hji]
    · simp
  have hraw' : |∫ x in U, v x * vecDot (b x) (E x) ∂volume| ≤ cubeVolume Q *
      (eLpNorm (fun x ↦ HilbertVec.ofVec (Pi.single i (dot x))) q.exponent μ).toReal *
      (eLpNorm (fun x ↦ HilbertVec.ofVec (Pi.single i (v x)))
        q.conjugate.exponent μ).toReal := by
    calc
      |∫ x in U, v x * vecDot (b x) (E x) ∂volume| =
          |∫ x in U, vecDot (Pi.single i (dot x)) (Pi.single i (v x)) ∂volume| := by
        congr 1; apply setIntegral_congr_fun hU
        intro x _
        change v x * vecDot (b x) (E x) = vecDot (Pi.single i (dot x)) (Pi.single i (v x))
        rw [hdot_single]; simp only [dot]; ring
      _ ≤ _ := hraw
  rw [hdotveceq, hvveceq] at hraw'
  apply hraw'.trans
  have hsmultop : C.toNNReal • eLpNorm (fun x ↦ HilbertVec.ofVec (b x))
      q.exponent μ ≠ ∞ := by
    rw [ENNReal.smul_def]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hb.eLpNorm_ne_top
  have hdotnorm : eLpNorm dot q.exponent μ ≤ C.toNNReal •
      eLpNorm (fun x ↦ HilbertVec.ofVec (b x)) q.exponent μ := by
    apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
    filter_upwards with x
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
    apply ENNReal.coe_le_coe.mpr
    refine (NNReal.coe_le_coe).mp ?_
    change ‖dot x‖ ≤ (C.toNNReal : ℝ) * ‖HilbertVec.ofVec (b x)‖
    simpa [Real.coe_toNNReal _ hC] using (show ‖dot x‖ ≤ C * ‖HilbertVec.ofVec (b x)‖ by
      calc
        ‖dot x‖ = |inner ℝ (HilbertVec.ofVec (b x)) (HilbertVec.ofVec (E x))| := by
          simp only [dot, HilbertVec.inner_def, Real.norm_eq_abs]
        _ ≤ ‖HilbertVec.ofVec (b x)‖ * ‖HilbertVec.ofVec (E x)‖ := by
          simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ)
            (HilbertVec.ofVec (b x)) (HilbertVec.ofVec (E x))
        _ ≤ ‖HilbertVec.ofVec (b x)‖ * C :=
          mul_le_mul_of_nonneg_left (hEbound x) (norm_nonneg _)
        _ = C * ‖HilbertVec.ofVec (b x)‖ := by ring)
  have hnormmono := ENNReal.toReal_mono hsmultop hdotnorm
  calc
    cubeVolume Q * (eLpNorm dot q.exponent μ).toReal *
      (eLpNorm v q.conjugate.exponent μ).toReal =
      (cubeVolume Q * (eLpNorm v q.conjugate.exponent μ).toReal) *
        (eLpNorm dot q.exponent μ).toReal := by ring
    _ ≤ (cubeVolume Q * (eLpNorm v q.conjugate.exponent μ).toReal) *
        (C.toNNReal • eLpNorm (fun x ↦ HilbertVec.ofVec (b x)) q.exponent μ).toReal :=
      mul_le_mul_of_nonneg_left hnormmono
        (mul_nonneg (cubeVolume_pos Q).le ENNReal.toReal_nonneg)
    _ = _ := by ring

private theorem originCube_parent_volume_ratio
    {d : ℕ} (m : ℤ) :
    cubeVolume (originCube d (m + 1)) /
      cubeVolume (originCube d m) = (3 : ℝ) ^ d := by
  have hs : (3 : ℝ) ^ m ≠ 0 := zpow_ne_zero _ (by norm_num)
  simp only [cubeVolume, cubeScaleFactor, originCube]
  rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0) m 1]
  norm_num
  field_simp [hs]
  ring

private theorem source_subset_inner_half {d : ℕ} (m : ℤ) :
    openCubeSet (originCube d m) ⊆
      scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ) := by
  rw [← scaledOpenCubeSet_originCube_succ_one_div_three]
  exact (scaledOpenCubeSet_subset_scaledClosedCubeSet _ _).trans
    (scaledClosedCubeSet_subset_scaledOpenCubeSet_of_lt _ (by norm_num))

private theorem canonical_cutoff_source_one_gradient_zero
    {d : ℕ} (m : ℤ) (x : Vec d) (hx : x ∈ openCubeSet (originCube d m)) :
    let Qp := originCube d (m + 1)
    let η := QuantitativeCubeCutoff.canonical Qp (1 / 3 : ℝ) (5 / 12 : ℝ)
      (by norm_num) (by norm_num)
    η x = 1 ∧ euclideanGradient (η : Vec d → ℝ) x = 0 := by
  dsimp
  let Qp := originCube d (m + 1)
  have hxinner : x ∈ scaledClosedCubeSet Qp (1 / 3 : ℝ) := by
    apply scaledOpenCubeSet_subset_scaledClosedCubeSet
    simpa only [Qp] using (show x ∈ scaledOpenCubeSet (originCube d (m + 1))
      (1 / 3 : ℝ) by
        rw [scaledOpenCubeSet_originCube_succ_one_div_three]
        exact hx)
  constructor
  · exact QuantitativeCubeCutoff.canonicalFun_eq_one_on_inner
      (by norm_num) (by norm_num) hxinner
  · funext j
    change (fderiv ℝ (QuantitativeCubeCutoff.canonicalFun Qp (1 / 3 : ℝ)
      (5 / 12 : ℝ)) x) (basisVec j) = 0
    apply QuantitativeCubeCutoff.canonicalFun_fderiv_apply_basisVec_eq_zero_of_abs_sub_center_lt_inner
      Qp (by norm_num) (by norm_num)
    have hxopen : x ∈ scaledOpenCubeSet Qp (1 / 3 : ℝ) := by
      rw [show Qp = originCube d (m + 1) by rfl,
        scaledOpenCubeSet_originCube_succ_one_div_three]
      exact hx
    exact hxopen j

private theorem actual_Jraw_bridge
    {d : ℕ} (m : ℤ) (i : Fin d) (R G : Vec d → Vec d) (r : Vec d → ℝ) :
    let Q := originCube d m
    let Qp := originCube d (m + 1)
    let U := scaledOpenCubeSet Qp (1 / 2 : ℝ)
    let η := QuantitativeCubeCutoff.canonical Qp (1 / 3 : ℝ) (5 / 12 : ℝ)
      (by norm_num) (by norm_num)
    let Rref := cubeDirichletOddReflectionHessianRowVectorField Q i R
    ∫ x in U, vecDot (openParentDatumExtension (openCubeSet Q) G x)
      (fun j => η x * Rref x j + r x *
        (fderiv ℝ (η : Vec d → ℝ) x) (basisVec j)) ∂volume =
      ∫ x in openCubeSet Q, vecDot (G x) (R x) ∂volume := by
  dsimp
  let Q := originCube d m
  let Qp := originCube d (m + 1)
  let U := scaledOpenCubeSet Qp (1 / 2 : ℝ)
  let η := QuantitativeCubeCutoff.canonical Qp (1 / 3 : ℝ) (5 / 12 : ℝ)
    (by norm_num) (by norm_num)
  let Rref := cubeDirichletOddReflectionHessianRowVectorField Q i R
  have hQU : openCubeSet Q ⊆ U := by
    simpa only [Q, Qp, U] using source_subset_inner_half (d := d) m
  have hQmeas : MeasurableSet (openCubeSet Q) := (isOpen_openCubeSet Q).measurableSet
  have hindicator :
      (fun x => vecDot (openParentDatumExtension (openCubeSet Q) G x)
        (fun j => η x * Rref x j + r x *
          (fderiv ℝ (η : Vec d → ℝ) x) (basisVec j))) =
      (openCubeSet Q).indicator (fun x => vecDot (G x)
        (fun j => η x * Rref x j + r x *
          (fderiv ℝ (η : Vec d → ℝ) x) (basisVec j))) := by
    funext x
    by_cases hx : x ∈ openCubeSet Q <;> simp [openParentDatumExtension, hx, vecDot]
  rw [hindicator, indicator_setIntegral_parent_eq_child hQmeas hQU]
  refine MeasureTheory.setIntegral_congr_fun hQmeas ?_
  intro x hx
  obtain ⟨hη, hgrad⟩ := canonical_cutoff_source_one_gradient_zero m x
    (by simpa only [Q] using hx)
  have href : Rref x = R x :=
    cubeDirichletOddReflectionHessianRowVectorField_eq_self_of_mem_openCubeSet Q i R hx
  have hderiv : ∀ j : Fin d, (fderiv ℝ (η : Vec d → ℝ) x) (basisVec j) = 0 :=
    fun j => congrFun hgrad j
  simp only [hderiv, mul_zero, add_zero, href]
  change η x = 1 at hη
  have hscale : (fun j => η x * R x j) = R x := by
    funext j; rw [hη]; ring
  rw [hscale]

private theorem localized_Dterm_raw_bound
    {d : ℕ} (Q : TriadicCube d) (q : FiniteLpExponent)
    (U : Set (Vec d)) (hU : MeasurableSet U) (hUP : U ⊆ openCubeSet Q)
    (η : Vec d → ℝ) (b V : Vec d → Vec d)
    (hb : MemLp (fun x ↦ HilbertVec.ofVec (b x)) q.exponent
      (normalizedCubeMeasure Q))
    (hV : MemLp (fun x ↦ HilbertVec.ofVec (V x)) q.conjugate.exponent
      (normalizedCubeMeasure Q))
    (hη : AEStronglyMeasurable η (normalizedCubeMeasure Q))
    (hηbound : ∀ x, 0 ≤ η x ∧ η x ≤ 1) :
    |∫ x in U, η x * vecDot (b x) (V x) ∂volume| ≤ cubeVolume Q *
      (eLpNorm (fun x ↦ HilbertVec.ofVec (b x)) q.exponent
        (normalizedCubeMeasure Q)).toReal *
      (eLpNorm (fun x ↦ HilbertVec.ofVec (V x)) q.conjugate.exponent
        (normalizedCubeMeasure Q)).toReal := by
  let μ : Measure (Vec d) := normalizedCubeMeasure Q
  let B : Vec d → Vec d := fun x ↦ η x • b x
  have hbvec : AEStronglyMeasurable b μ :=
    (HilbertVec.continuousLinearEquivVec d).continuous.comp_aestronglyMeasurable
      hb.aestronglyMeasurable
  have hBmeas : AEStronglyMeasurable (fun x ↦ HilbertVec.ofVec (B x)) μ := by
    have hsmul : AEStronglyMeasurable (fun x ↦ η x • b x) μ := hη.smul hbvec
    exact (HilbertVec.ofVecL d).continuous.comp_aestronglyMeasurable hsmul
  have hB : MemLp (fun x ↦ HilbertVec.ofVec (B x)) q.exponent μ := by
    refine MemLp.of_le_mul (c := 1) hb hBmeas ?_
    filter_upwards with x
    change ‖(HilbertVec.ofVecL d) (η x • b x)‖ ≤ 1 * ‖(HilbertVec.ofVecL d) (b x)‖
    rw [(HilbertVec.ofVecL d).map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (hηbound x).1, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hηbound x).2
  have hBnorm : eLpNorm (fun x ↦ HilbertVec.ofVec (B x)) q.exponent μ ≤
      eLpNorm (fun x ↦ HilbertVec.ofVec (b x)) q.exponent μ := by
    apply eLpNorm_mono_ae
    filter_upwards with x
    change ‖(HilbertVec.ofVecL d) (η x • b x)‖ ≤ ‖(HilbertVec.ofVecL d) (b x)‖
    rw [(HilbertVec.ofVecL d).map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (hηbound x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hηbound x).2
  have hraw := restricted_raw_holder_vec Q q U hU hUP B V hB hV
  have hraw' : |∫ x in U, η x * vecDot (b x) (V x) ∂volume| ≤ cubeVolume Q *
      (eLpNorm (fun x ↦ HilbertVec.ofVec (B x)) q.exponent μ).toReal *
      (eLpNorm (fun x ↦ HilbertVec.ofVec (V x)) q.conjugate.exponent μ).toReal := by
    calc
      |∫ x in U, η x * vecDot (b x) (V x) ∂volume| =
        |∫ x in U, vecDot (B x) (V x) ∂volume| := by
          congr 1; apply setIntegral_congr_fun hU
          intro x _
          change η x * vecDot (b x) (V x) = vecDot (η x • b x) (V x)
          simp only [vecDot_smul_left]
      _ ≤ _ := hraw
  apply hraw'.trans
  have hnormmono : (eLpNorm (fun x ↦ HilbertVec.ofVec (B x)) q.exponent μ).toReal ≤
      (eLpNorm (fun x ↦ HilbertVec.ofVec (b x)) q.exponent μ).toReal :=
    ENNReal.toReal_mono hb.eLpNorm_ne_top hBnorm
  calc
    cubeVolume Q * (eLpNorm (fun x ↦ HilbertVec.ofVec (B x)) q.exponent μ).toReal *
        (eLpNorm (fun x ↦ HilbertVec.ofVec (V x)) q.conjugate.exponent μ).toReal =
      (cubeVolume Q * (eLpNorm (fun x ↦ HilbertVec.ofVec (V x))
        q.conjugate.exponent μ).toReal) *
        (eLpNorm (fun x ↦ HilbertVec.ofVec (B x)) q.exponent μ).toReal := by ring
    _ ≤ (cubeVolume Q * (eLpNorm (fun x ↦ HilbertVec.ofVec (V x))
        q.conjugate.exponent μ).toReal) *
        (eLpNorm (fun x ↦ HilbertVec.ofVec (b x)) q.exponent μ).toReal :=
      mul_le_mul_of_nonneg_left hnormmono
        (mul_nonneg (cubeVolume_pos Q).le ENNReal.toReal_nonneg)
    _ = _ := by ring

private theorem raw_source_pairing_eq_volume_mul_normalized
    {d : ℕ} (m : ℤ) (R G : Vec d → Vec d) :
    (∫ x in openCubeSet (originCube d m), vecDot (G x) (R x) ∂volume) =
      cubeVolume (originCube d m) *
        ∫ x, vecDot (G x) (R x) ∂normalizedCubeMeasure (originCube d m) := by
  let Q := originCube d m
  let Jraw : ℝ := ∫ x in openCubeSet Q, vecDot (G x) (R x) ∂volume
  let Jnorm : ℝ := ∫ x, vecDot (G x) (R x) ∂normalizedCubeMeasure Q
  have hμ : normalizedCubeMeasure Q = ENNReal.ofReal ((cubeVolume Q)⁻¹) •
      volume.restrict (openCubeSet Q) := by
    rw [normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_originCube_eq_volume_restrict_openCubeSet_originCube]
  have hJnorm : Jnorm = (cubeVolume Q)⁻¹ * Jraw := by
    change ∫ x, vecDot (G x) (R x) ∂normalizedCubeMeasure Q = _
    rw [hμ]
    simp only [Jraw, integral_smul_measure, smul_eq_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (cubeVolume_pos Q).le)]
  have hJraw : Jraw = cubeVolume Q * Jnorm := by
    rw [hJnorm]
    field_simp [(cubeVolume_pos Q).ne']
  simpa only [Q, Jraw, Jnorm] using hJraw

private theorem actual_Jraw_eq_source_volume_mul_normalized
    {d : ℕ} (m : ℤ) (i : Fin d) (R G : Vec d → Vec d) (r : Vec d → ℝ) :
    let Q := originCube d m
    let Qp := originCube d (m + 1)
    let U := scaledOpenCubeSet Qp (1 / 2 : ℝ)
    let η := QuantitativeCubeCutoff.canonical Qp (1 / 3 : ℝ) (5 / 12 : ℝ)
      (by norm_num) (by norm_num)
    let Rref := cubeDirichletOddReflectionHessianRowVectorField Q i R
    ∫ x in U, vecDot (openParentDatumExtension (openCubeSet Q) G x)
      (fun j => η x * Rref x j + r x *
        (fderiv ℝ (η : Vec d → ℝ) x) (basisVec j)) ∂volume =
      cubeVolume Q * ∫ x, vecDot (G x) (R x) ∂normalizedCubeMeasure Q := by
  dsimp
  rw [actual_Jraw_bridge]
  exact raw_source_pairing_eq_volume_mul_normalized m R G

private theorem htrunc_of_raw_four_terms
    {V J D E A H BD BE BA BH : ℝ} {T K : ℝ≥0∞}
    (hV : 0 < V) (hKtop : K ≠ ∞)
    (hT : T = ENNReal.ofReal J)
    (hid : V * J = D + E - 2 * A - H)
    (hD : |D| ≤ V * BD) (hE : |E| ≤ V * BE)
    (hA : |A| ≤ V * BA) (hH : |H| ≤ V * BH)
    {X : ℝ} (hsum : BD + BE + 2 * BA + BH ≤ K.toReal * X) :
    T ≠ ∞ ∧ T ≤ K * ENNReal.ofReal X := by
  have hid' : J = D / V + E / V - 2 * (A / V) - H / V := by
    field_simp [hV.ne'] at hid ⊢
    linarith
  have hD' : |D / V| ≤ BD := by
    rw [abs_div, abs_of_pos hV]
    apply (div_le_iff₀ hV).mpr
    simpa [mul_comm] using hD
  have hE' : |E / V| ≤ BE := by
    rw [abs_div, abs_of_pos hV]
    apply (div_le_iff₀ hV).mpr
    simpa [mul_comm] using hE
  have hA' : |A / V| ≤ BA := by
    rw [abs_div, abs_of_pos hV]
    apply (div_le_iff₀ hV).mpr
    simpa [mul_comm] using hA
  have hH' : |H / V| ≤ BH := by
    rw [abs_div, abs_of_pos hV]
    apply (div_le_iff₀ hV).mpr
    simpa [mul_comm] using hH
  have hraw : J ≤ K.toReal * X :=
    (localized_four_term_bound hid' hD' hE' hA' hH').trans hsum
  constructor
  · rw [hT]
    exact ENNReal.ofReal_ne_top
  · have hKreal : 0 ≤ K.toReal := ENNReal.toReal_nonneg
    calc
      T = ENNReal.ofReal J := hT
      _ ≤ ENNReal.ofReal (K.toReal * X) := ENNReal.ofReal_le_ofReal hraw
      _ = K * ENNReal.ofReal X := by
        rw [ENNReal.ofReal_mul hKreal, ENNReal.ofReal_toReal hKtop]

/-- The literal source pairing does not depend on the row-value representative
beside `∇η`: both parent expressions collapse to the same source pairing. -/
private theorem actual_Jraw_congr_row_value
    {d : ℕ} (m : ℤ) (i : Fin d) (R G : Vec d → Vec d)
    (r₁ r₂ : Vec d → ℝ) :
    let Q := originCube d m
    let Qp := originCube d (m + 1)
    let U := scaledOpenCubeSet Qp (1 / 2 : ℝ)
    let η := QuantitativeCubeCutoff.canonical Qp (1 / 3 : ℝ) (5 / 12 : ℝ)
      (by norm_num) (by norm_num)
    let Rref := cubeDirichletOddReflectionHessianRowVectorField Q i R
    (∫ x in U, vecDot (openParentDatumExtension (openCubeSet Q) G x)
      (fun j => η x * Rref x j + r₁ x *
        (fderiv ℝ (η : Vec d → ℝ) x) (basisVec j)) ∂volume) =
      ∫ x in U, vecDot (openParentDatumExtension (openCubeSet Q) G x)
        (fun j => η x * Rref x j + r₂ x *
          (fderiv ℝ (η : Vec d → ℝ) x) (basisVec j)) ∂volume := by
  dsimp
  rw [actual_Jraw_bridge, actual_Jraw_bridge]

/-- Scalar collection of the four Holder bounds after raw-volume division.
The scale factors `ss`, `sp` are kept explicit so the cutoff cancellations
are audited before selecting the final ENNReal coefficient. -/
private theorem coefficient_algebra_after_raw_division
    {D E A Hterm : ℝ} {Fq Vgrad Vval Rval : ℝ≥0∞}
    {ratio Kg Kl kg kl Ccz P Csrc ss sp F Nn : ℝ}
    (hratio : 0 ≤ ratio) (hKg : 0 ≤ Kg) (hKl : 0 ≤ Kl)
    (hCcz : 0 ≤ Ccz) (hP : 0 ≤ P) (hCsrc : 0 ≤ Csrc)
    (hss : 0 ≤ ss) (hF : 0 ≤ F) (hNn : 0 ≤ Nn)
    (hFq : Fq.toReal ≤ F)
    (hgrad : Vgrad.toReal ≤ Ccz * Nn)
    (hval : Vval.toReal ≤ P * sp * Ccz * Nn)
    (hrow : Rval.toReal ≤ Csrc * ss * F)
    (hKgsp : Kg * sp ≤ kg) (hKgss : Kg * ss ≤ kg)
    (hKlsssp : Kl * ss * sp ≤ kl)
    (hD : |D| ≤ ratio * Fq.toReal * Vgrad.toReal)
    (hE : |E| ≤ ratio * (Kg.toNNReal • Fq).toReal * Vval.toReal)
    (hA : |A| ≤ ratio * Rval.toReal * (Kg.toNNReal • Vgrad).toReal)
    (hH : |Hterm| ≤ ratio * (Kl.toNNReal • Rval).toReal * Vval.toReal) :
    |D| + |E| + 2 * |A| + |Hterm| ≤
      (ratio * Ccz * (1 + kg * P + 2 * kg * Csrc + kl * Csrc * P) * F) * Nn := by
  have hsmulF : (Kg.toNNReal • Fq).toReal = Kg * Fq.toReal := by
    rw [ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul]
    rw [ENNReal.coe_toReal, Real.coe_toNNReal _ hKg]
  have hsmulV : (Kg.toNNReal • Vgrad).toReal = Kg * Vgrad.toReal := by
    rw [ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul]
    rw [ENNReal.coe_toReal, Real.coe_toNNReal _ hKg]
  have hsmulR : (Kl.toNNReal • Rval).toReal = Kl * Rval.toReal := by
    rw [ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul]
    rw [ENNReal.coe_toReal, Real.coe_toNNReal _ hKl]
  rw [hsmulF] at hE
  rw [hsmulV] at hA
  rw [hsmulR] at hH
  have hD' : |D| ≤ ratio * Ccz * F * Nn := by
    calc
      |D| ≤ ratio * Fq.toReal * Vgrad.toReal := hD
      _ ≤ ratio * F * (Ccz * Nn) := by gcongr
      _ = ratio * Ccz * F * Nn := by ring
  have hE' : |E| ≤ ratio * Ccz * (kg * P) * F * Nn := by
    calc
      |E| ≤ ratio * (Kg * Fq.toReal) * Vval.toReal := hE
      _ ≤ ratio * (Kg * F) * (P * sp * Ccz * Nn) := by gcongr
      _ = ratio * Ccz * F * Nn * (P * (Kg * sp)) := by ring
      _ ≤ ratio * Ccz * F * Nn * (P * kg) := by gcongr
      _ = ratio * Ccz * (kg * P) * F * Nn := by ring
  have hA' : |A| ≤ ratio * Ccz * (kg * Csrc) * F * Nn := by
    calc
      |A| ≤ ratio * Rval.toReal * (Kg * Vgrad.toReal) := hA
      _ ≤ ratio * (Csrc * ss * F) * (Kg * (Ccz * Nn)) := by gcongr
      _ = ratio * Ccz * F * Nn * (Csrc * (Kg * ss)) := by ring
      _ ≤ ratio * Ccz * F * Nn * (Csrc * kg) := by gcongr
      _ = ratio * Ccz * (kg * Csrc) * F * Nn := by ring
  have hH' : |Hterm| ≤ ratio * Ccz * (kl * Csrc * P) * F * Nn := by
    calc
      |Hterm| ≤ ratio * (Kl * Rval.toReal) * Vval.toReal := hH
      _ ≤ ratio * (Kl * (Csrc * ss * F)) * (P * sp * Ccz * Nn) := by gcongr
      _ = ratio * Ccz * F * Nn * (Csrc * P * (Kl * ss * sp)) := by ring
      _ ≤ ratio * Ccz * F * Nn * (Csrc * P * kl) := by gcongr
      _ = ratio * Ccz * (kl * Csrc * P) * F * Nn := by ring
  calc
    |D| + |E| + 2 * |A| + |Hterm| ≤ ratio * Ccz * F * Nn +
        ratio * Ccz * (kg * P) * F * Nn +
        2 * (ratio * Ccz * (kg * Csrc) * F * Nn) +
        ratio * Ccz * (kl * Csrc * P) * F * Nn := by gcongr
    _ = _ := by ring

/-- The exact per-row `htrunc` closure once the four *raw* mutual-testing
terms have been bounded. The raw parent pairing is normalized through the
canonical cutoff/reflection bridge before it is identified with the source
radial moment. -/
private theorem source_hessian_row_htrunc_of_raw_term_bounds
    {d : ℕ} {m : ℤ} (q : FiniteLpExponent)
    {u : H1Function (openCubeSet (originCube d m))}
    (Hsrc : HasWeakHessianOn (openCubeSet (originCube d m)) u)
    (i : Fin d) {K : ℝ≥0∞} (hKtop : K ≠ ∞)
    (hterms : ∀ n : ℕ, ∃ (D E A Hterm BD BE BA BH : ℝ),
      let Q := originCube d m
      let Qp := originCube d (m + 1)
      let U := scaledOpenCubeSet Qp (1 / 2 : ℝ)
      let η := QuantitativeCubeCutoff.canonical Qp (1 / 3 : ℝ) (5 / 12 : ℝ)
        (by norm_num) (by norm_num)
      let R : Vec d → Vec d := fun x j => Hsrc.hess i j x
      let G := (sourceHessianRowRadialDatum q Hsrc i n).toField
      let r : Vec d → ℝ := fun _ => 0
      let Jraw := ∫ x in U, vecDot (openParentDatumExtension (openCubeSet Q) G x)
        (fun j => η x *
          cubeDirichletOddReflectionHessianRowVectorField Q i R x j +
          r x * (fderiv ℝ (η : Vec d → ℝ) x) (basisVec j)) ∂volume
      Jraw = D + E - 2 * A - Hterm ∧
      |D| ≤ cubeVolume Q * BD ∧ |E| ≤ cubeVolume Q * BE ∧
      |A| ≤ cubeVolume Q * BA ∧ |Hterm| ≤ cubeVolume Q * BH ∧
      BD + BE + 2 * BA + BH ≤ K.toReal *
        ((∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n
          (fun x => HilbertVec.ofVec (fun j => Hsrc.hess i j x)) x ∂
          normalizedCubeMeasure Q) ^ (1 - q.exponent.toReal⁻¹)).toReal) :
    ∀ n : ℕ,
      (∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n
        (fun x => HilbertVec.ofVec (fun j => Hsrc.hess i j x)) x ∂
        normalizedCubeMeasure (originCube d m)) ≠ ∞ ∧
      (∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n
        (fun x => HilbertVec.ofVec (fun j => Hsrc.hess i j x)) x ∂
        normalizedCubeMeasure (originCube d m)) ≤ K *
        (∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n
          (fun x => HilbertVec.ofVec (fun j => Hsrc.hess i j x)) x ∂
          normalizedCubeMeasure (originCube d m)) ^
          (1 - q.exponent.toReal⁻¹) := by
  intro n
  obtain ⟨D, E, A, Hterm, BD, BE, BA, BH, hid, hD, hE, hA, hH, hsum⟩ := hterms n
  let Q := originCube d m
  let R : Vec d → Vec d := fun x j => Hsrc.hess i j x
  let G := (sourceHessianRowRadialDatum q Hsrc i n).toField
  let T : ℝ≥0∞ := ∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n
    (fun x => HilbertVec.ofVec (R x)) x ∂normalizedCubeMeasure Q
  have hmoment := source_hessian_row_radial_pairing_moment q Hsrc i n
  have hT : T = ENNReal.ofReal (∫ x, vecDot (G x) (R x) ∂normalizedCubeMeasure Q) := by
    simpa only [T, R, G, vecDot_comm] using! hmoment
  have hJ : cubeVolume Q *
      (∫ x, vecDot (G x) (R x) ∂normalizedCubeMeasure Q) =
      D + E - 2 * A - Hterm := by
    rw [← actual_Jraw_eq_source_volume_mul_normalized]
    simpa only [Q, R, G] using hid
  have hTtop : T ≠ ∞ := by
    rw [hT]
    exact ENNReal.ofReal_ne_top
  have hid' : (∫ x, vecDot (G x) (R x) ∂normalizedCubeMeasure Q) =
      D / cubeVolume Q + E / cubeVolume Q - 2 * (A / cubeVolume Q) -
        Hterm / cubeVolume Q := by
    field_simp [(cubeVolume_pos Q).ne'] at hJ ⊢
    linarith
  have hD' : |D / cubeVolume Q| ≤ BD := by
    rw [abs_div, abs_of_pos (cubeVolume_pos Q)]
    apply (div_le_iff₀ (cubeVolume_pos Q)).mpr
    simpa [mul_comm] using hD
  have hE' : |E / cubeVolume Q| ≤ BE := by
    rw [abs_div, abs_of_pos (cubeVolume_pos Q)]
    apply (div_le_iff₀ (cubeVolume_pos Q)).mpr
    simpa [mul_comm] using hE
  have hA' : |A / cubeVolume Q| ≤ BA := by
    rw [abs_div, abs_of_pos (cubeVolume_pos Q)]
    apply (div_le_iff₀ (cubeVolume_pos Q)).mpr
    simpa [mul_comm] using hA
  have hH' : |Hterm / cubeVolume Q| ≤ BH := by
    rw [abs_div, abs_of_pos (cubeVolume_pos Q)]
    apply (div_le_iff₀ (cubeVolume_pos Q)).mpr
    simpa [mul_comm] using hH
  have hraw : (∫ x, vecDot (G x) (R x) ∂normalizedCubeMeasure Q) ≤
      K.toReal * (T ^ (1 - q.exponent.toReal⁻¹)).toReal := by
    exact (localized_four_term_bound hid' hD' hE' hA' hH').trans hsum
  constructor
  · simpa only [Q, T] using hTtop
  · have hpow_nonneg : 0 ≤ 1 - q.exponent.toReal⁻¹ := by
      exact sub_nonneg.mpr (inv_le_one_of_one_le₀ (le_of_lt (by
        rw [← ENNReal.toReal_one]
        exact (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).mpr q.one_lt)))
    have hpowtop : T ^ (1 - q.exponent.toReal⁻¹) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg hpow_nonneg hTtop
    calc
      T = ENNReal.ofReal (∫ x, vecDot (G x) (R x) ∂normalizedCubeMeasure Q) := hT
      _ ≤ ENNReal.ofReal (K.toReal *
          (T ^ (1 - q.exponent.toReal⁻¹)).toReal) := ENNReal.ofReal_le_ofReal hraw
      _ = K * T ^ (1 - q.exponent.toReal⁻¹) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hKtop, ENNReal.ofReal_toReal hpowtop]

private theorem actual_mutual_identity_package
    {d : ℕ} [NeZero d] {m : ℤ} (q : FiniteLpExponent)
    {F : Vec d → ℝ}
    (hF : MemLp F 2 (normalizedCubeMeasure (originCube d m)))
    (hFq : MemLp F q.exponent (normalizedCubeMeasure (originCube d m)))
    {B : ℝ≥0∞} (hBtop : B < ∞)
    {u : H10Function (openCubeSet (originCube d m))}
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F)
    (H : HasWeakHessianOn (openCubeSet (originCube d m)) u.toH1Function)
    (i : Fin d)
    (hgrad : eLpNorm (hilbertifyVecField u.toH1Function.grad) q.exponent
      (normalizedCubeMeasure (originCube d m)) ≤ B)
    (n : ℕ) :
    ∃ (r : H1Function (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ)))
      (b : Vec d → Vec d)
      (v : H10Function (openCubeSet (originCube d (m + 1))))
      (η : QuantitativeCubeCutoff (originCube d (m + 1)) (1 / 3 : ℝ) (5 / 12 : ℝ)),
      let U := scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ)
      let R := fun x j ↦ H.hess i j x
      let GP := (sourceParentFiniteLpExtension m q.conjugate (sourceHessianRowRadialDatum q H i n)).toField
      η = QuantitativeCubeCutoff.canonical (originCube d (m + 1))
        (1 / 3 : ℝ) (5 / 12 : ℝ) (by norm_num) (by norm_num) ∧
      (hilbertifyVecField r.grad =ᵐ[volume.restrict U]
        fun x ↦ HilbertVec.ofVec
          (cubeDirichletOddReflectionHessianRowVectorField
            (originCube d m) i R x)) ∧
      b = (fun x j ↦ if j = i then
        cubeDirichletOddReflectionScalar (originCube d m) F x else 0) ∧
      v = openCubeSetScalarDivergenceSolution (originCube d (m + 1))
        (by norm_num : (0 : ℝ) < 1) GP
        (memVectorL2_sourceParentFiniteLpExtension m q.conjugate
          (sourceHessianRowRadialDatum q H i n)) ∧
      MemLp (hilbertifyVecField b) q.exponent
        (normalizedCubeMeasure (originCube d (m + 1))) ∧
      eLpNorm (hilbertifyVecField b) q.exponent
        (normalizedCubeMeasure (originCube d (m + 1))) =
        eLpNorm F q.exponent (normalizedCubeMeasure (originCube d m)) ∧
      MemLp r.toFun q.exponent
        ((normalizedCubeMeasure (originCube d (m + 1))).restrict U) ∧
      eLpNorm r.toFun q.exponent
        ((normalizedCubeMeasure (originCube d (m + 1))).restrict U) ≤ B ∧
      (∫ x in U, vecDot (GP x)
          (fun j ↦ η x * r.grad x j + r x * euclideanGradient (η : Vec d → ℝ) x j)
          ∂volume) =
        (∫ x in U, η x * vecDot (b x) (v.toH1Function.grad x) ∂volume) +
          (∫ x in U, v x * vecDot (b x) (euclideanGradient (η : Vec d → ℝ) x)
            ∂volume) -
          2 * (∫ x in U, r x * vecDot (v.toH1Function.grad x)
            (euclideanGradient (η : Vec d → ℝ) x) ∂volume) -
          (∫ x in U, r x * v x * euclideanCoordLaplacian (η : Vec d → ℝ) x
            ∂volume) := by
  let Qp : TriadicCube d := originCube d (m + 1)
  let U : Set (Vec d) := scaledOpenCubeSet Qp (1 / 2 : ℝ)
  let R : Vec d → Vec d := fun x j ↦ H.hess i j x
  let G := sourceHessianRowRadialDatum q H i n
  let GP := sourceParentFiniteLpExtension m q.conjugate G
  let v : H10Function (openCubeSet Qp) := openCubeSetScalarDivergenceSolution Qp
    (by norm_num : (0 : ℝ) < 1) GP.toField
    (memVectorL2_sourceParentFiniteLpExtension m q.conjugate G)
  obtain ⟨r, b, hrow, hb2, hrowid, hbeq, hbq, hbNorm, hrq, hrNorm⟩ :=
    exists_reflected_source_row_setup q hF hFq hBtop hweak H i hgrad
  let η : QuantitativeCubeCutoff Qp (1 / 3 : ℝ) (5 / 12 : ℝ) :=
    QuantitativeCubeCutoff.canonical Qp (1 / 3 : ℝ) (5 / 12 : ℝ)
      (by norm_num) (by norm_num)
  have hU : IsOpenBoundedConvexDomain U :=
    isOpenBoundedConvexDomain_scaledOpenCubeSet_of_pos Qp (by norm_num)
  have hUP : U ⊆ openCubeSet Qp := by
    intro x hx
    apply scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one Qp
      (ρ := 1 / 2) (by norm_num) (by norm_num)
    intro j; exact le_of_lt (hx j)
  have hηsub : tsupport (η : Vec d → ℝ) ⊆ U := by
    exact (η.tsupport_subset_scaledClosedCubeSet_of_support_subset).trans
      (scaledClosedCubeSet_subset_scaledOpenCubeSet_of_lt Qp (by norm_num))
  let vU : H1Function U := v.toH1Function.restrict hU.isOpen hUP
  have hrowH10 : ∀ φ : H10Function U,
      ∫ x in U, vecDot (r.grad x) (φ.toH1Function.grad x) ∂volume =
        -∫ x in U, vecDot (b x) (φ.toH1Function.grad x) ∂volume := by
    let : IsFiniteMeasure (volume.restrict U) := by
      simpa using hU.isFiniteMeasure_restrict_volume
    simpa only [one_mul] using
      weak_divergence_identity_of_h10 r b hb2 1 (by
        simpa only [one_mul] using hrow)
  have hrow' := row_weak_test_expanded hU r vU b (η : Vec d → ℝ)
    η.smooth η.hasCompactSupport hηsub hb2 hrowH10
  have hparent : ∀ ψ : H10Function (openCubeSet Qp),
      ∫ x in openCubeSet Qp, vecDot (v.toH1Function.grad x)
        (ψ.toH1Function.grad x) ∂volume =
        -∫ x in openCubeSet Qp, vecDot (GP.toField x)
          (ψ.toH1Function.grad x) ∂volume := by
    intro ψ
    simpa only [v, one_mul] using openCubeSetScalarDivergenceSolution_weak Qp
      (by norm_num : (0 : ℝ) < 1) GP.toField
      (memVectorL2_sourceParentFiniteLpExtension m q.conjugate G) ψ
  have hparent' := parent_weak_test_expanded (U := U) (P := openCubeSet Qp)
    hU (isOpen_openCubeSet Qp) hUP r v.toH1Function
    GP.toField (η : Vec d → ℝ) η.smooth η.hasCompactSupport hηsub hparent
  have hibp := h1_cutoff_integration_by_parts hU r vU η.smooth
    η.hasCompactSupport hηsub
  dsimp only at hrow' hparent' hibp
  have hIcomm :
      (∫ x in U, η x * vecDot (r.grad x) (vU.grad x) ∂volume) =
      ∫ x in U, η x * vecDot (v.toH1Function.grad x) (r.grad x) ∂volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    simp only [vU, H1Function.restrict]
    rw [vecDot_comm]
  have hCibp :
      (∫ x in U, vU x * vecDot (r.grad x) (euclideanGradient (η : Vec d → ℝ) x)
        ∂volume) =
      -(∫ x in U, r x * vecDot (v.toH1Function.grad x)
        (euclideanGradient (η : Vec d → ℝ) x) ∂volume) -
      ∫ x in U, r x * v x * euclideanCoordLaplacian (η : Vec d → ℝ) x ∂volume := by
    simpa only [vU, H1Function.restrict] using hibp
  rw [hIcomm] at hrow'
  have hCibp' :
      (∫ x in U, v.toH1Function x * vecDot (r.grad x)
        (euclideanGradient (η : Vec d → ℝ) x) ∂volume) =
      -(∫ x in U, r x * vecDot (v.toH1Function.grad x)
        (euclideanGradient (η : Vec d → ℝ) x) ∂volume) -
      ∫ x in U, r x * v.toH1Function x *
        euclideanCoordLaplacian (η : Vec d → ℝ) x ∂volume := by
    simpa only [vU, H1Function.restrict] using hCibp
  refine ⟨r, b, v, η, rfl, ?_, ?_, rfl, hbq, hbNorm, hrq, hrNorm, ?_⟩
  · simpa only [U, R] using hrowid
  · exact hbeq
  · exact mutual_raw_identity hrow' hparent' hCibp'

/-- Concrete four-term witness from the reflected row and the parent adjoint
solution. All terms in the mutual identity receive their actual localized
Holder bounds. -/
private theorem actual_mutual_raw_term_bounds
    {d : ℕ} [NeZero d] {m : ℤ} (q : FiniteLpExponent)
    {F : Vec d → ℝ}
    (hF : MemLp F 2 (normalizedCubeMeasure (originCube d m)))
    (hFq : MemLp F q.exponent (normalizedCubeMeasure (originCube d m)))
    {B : ℝ≥0∞} (hBtop : B < ∞)
    {u : H10Function (openCubeSet (originCube d m))}
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F)
    (H : HasWeakHessianOn (openCubeSet (originCube d m)) u.toH1Function)
    (i : Fin d)
    (hgrad : eLpNorm (hilbertifyVecField u.toH1Function.grad) q.exponent
      (normalizedCubeMeasure (originCube d m)) ≤ B)
    {Ccz P : ℝ≥0∞}
    (hAdj : ∀ (m : ℤ) (h : CubeEuclideanL2LpField (originCube d m) q.conjugate),
      let hP := sourceParentFiniteLpExtension m q.conjugate h
      let v := openCubeSetScalarDivergenceSolution (originCube d (m + 1))
        (by norm_num : (0 : ℝ) < 1) hP.toField
        (memVectorL2_sourceParentFiniteLpExtension m q.conjugate h)
      eLpNorm v.toH1Function.toFun q.conjugate.exponent
          (normalizedCubeMeasure (originCube d (m + 1))) ≤
        P * ENNReal.ofReal (centeredCubeScale (m + 1)) * Ccz *
          eLpNorm (hilbertifyVecField h.toField) q.conjugate.exponent
            (normalizedCubeMeasure (originCube d m)) ∧
      eLpNorm (hilbertifyVecField v.toH1Function.grad) q.conjugate.exponent
          (normalizedCubeMeasure (originCube d (m + 1))) ≤
        Ccz * eLpNorm (hilbertifyVecField h.toField) q.conjugate.exponent
          (normalizedCubeMeasure (originCube d m)) ∧
      MemLp (hilbertifyVecField v.toH1Function.grad) q.conjugate.exponent
          (normalizedCubeMeasure (originCube d (m + 1))) ∧
      MemLp v.toH1Function.toFun q.conjugate.exponent
          (normalizedCubeMeasure (originCube d (m + 1))))
    (n : ℕ) :
    ∃ (r : H1Function (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ)))
      (b : Vec d → Vec d) (D E A Hterm : ℝ),
      let Qp := originCube d (m + 1)
      let U := scaledOpenCubeSet Qp (1 / 2 : ℝ)
      let η := QuantitativeCubeCutoff.canonical Qp (1 / 3 : ℝ) (5 / 12 : ℝ)
        (by norm_num) (by norm_num)
      let G := sourceHessianRowRadialDatum q H i n
      let GP := sourceParentFiniteLpExtension m q.conjugate G
      let v := openCubeSetScalarDivergenceSolution Qp (by norm_num : (0 : ℝ) < 1)
        GP.toField (memVectorL2_sourceParentFiniteLpExtension m q.conjugate G)
      (hilbertifyVecField r.grad =ᵐ[volume.restrict U]
        fun x ↦ HilbertVec.ofVec
          (cubeDirichletOddReflectionHessianRowVectorField (originCube d m) i
            (fun y j ↦ H.hess i j y) x)) ∧
      b = (fun x j ↦ if j = i then
        cubeDirichletOddReflectionScalar (originCube d m) F x else 0) ∧
      (∫ x in U, vecDot (GP.toField x)
          (fun j ↦ η x *
            cubeDirichletOddReflectionHessianRowVectorField (originCube d m) i
              (fun y j ↦ H.hess i j y) x j +
            r x * euclideanGradient (η : Vec d → ℝ) x j)
          ∂volume) = D + E - 2 * A - Hterm ∧
      |D| ≤ cubeVolume Qp *
        (eLpNorm (hilbertifyVecField b) q.exponent
          (normalizedCubeMeasure Qp)).toReal *
        (eLpNorm (hilbertifyVecField v.toH1Function.grad) q.conjugate.exponent
          (normalizedCubeMeasure Qp)).toReal ∧
      |E| ≤ cubeVolume Qp *
        (((d : ℝ) * (quantitativeCubeCutoffGradientConst d /
          (((5 / 12 : ℝ) - 1 / 3) * cubeRadius Qp))).toNNReal •
          eLpNorm (hilbertifyVecField b) q.exponent
            (normalizedCubeMeasure Qp)).toReal *
        (eLpNorm v.toH1Function.toFun q.conjugate.exponent
          (normalizedCubeMeasure Qp)).toReal ∧
      |A| ≤ cubeVolume Qp *
        (eLpNorm r.toFun q.exponent ((normalizedCubeMeasure Qp).restrict U)).toReal *
        (((d : ℝ) * (quantitativeCubeCutoffGradientConst d /
          (((5 / 12 : ℝ) - 1 / 3) * cubeRadius Qp))).toNNReal •
          eLpNorm (hilbertifyVecField v.toH1Function.grad) q.conjugate.exponent
            (normalizedCubeMeasure Qp)).toReal ∧
      |Hterm| ≤ cubeVolume Qp *
        (((d : ℝ) * (quantitativeCubeCutoffHessianConst d /
          (((5 / 12 : ℝ) - 1 / 3) * cubeRadius Qp) ^ 2)).toNNReal •
          eLpNorm r.toFun q.exponent ((normalizedCubeMeasure Qp).restrict U)).toReal *
        (eLpNorm v.toH1Function.toFun q.conjugate.exponent
          (normalizedCubeMeasure Qp)).toReal ∧
      eLpNorm (hilbertifyVecField b) q.exponent (normalizedCubeMeasure Qp) =
        eLpNorm F q.exponent (normalizedCubeMeasure (originCube d m)) ∧
      eLpNorm r.toFun q.exponent ((normalizedCubeMeasure Qp).restrict U) ≤ B ∧
      eLpNorm v.toH1Function.toFun q.conjugate.exponent
          (normalizedCubeMeasure Qp) ≤
        P * ENNReal.ofReal (centeredCubeScale (m + 1)) * Ccz *
          eLpNorm (hilbertifyVecField G.toField) q.conjugate.exponent
            (normalizedCubeMeasure (originCube d m)) ∧
      eLpNorm (hilbertifyVecField v.toH1Function.grad) q.conjugate.exponent
          (normalizedCubeMeasure Qp) ≤
        Ccz * eLpNorm (hilbertifyVecField G.toField) q.conjugate.exponent
          (normalizedCubeMeasure (originCube d m)) := by
  let Qp : TriadicCube d := originCube d (m + 1)
  let U : Set (Vec d) := scaledOpenCubeSet Qp (1 / 2 : ℝ)
  let G := sourceHessianRowRadialDatum q H i n
  let GP := sourceParentFiniteLpExtension m q.conjugate G
  let v : H10Function (openCubeSet Qp) := openCubeSetScalarDivergenceSolution Qp
    (by norm_num : (0 : ℝ) < 1) GP.toField
    (memVectorL2_sourceParentFiniteLpExtension m q.conjugate G)
  obtain ⟨hvval, hvgradBound, hvgrad, hvfun⟩ := hAdj m G
  obtain ⟨r, b, v', η, hηeq, hrowid, hbeq, hv', hbq, hbNorm, hrq, hrNorm, hid⟩ :=
    actual_mutual_identity_package q hF hFq hBtop hweak H i hgrad n
  subst v'
  let D : ℝ := ∫ x in U, η x * vecDot (b x) (v.toH1Function.grad x) ∂volume
  let E : ℝ := ∫ x in U, v x * vecDot (b x)
    (euclideanGradient (η : Vec d → ℝ) x) ∂volume
  let A : ℝ := ∫ x in U, r x * vecDot (v.toH1Function.grad x)
    (euclideanGradient (η : Vec d → ℝ) x) ∂volume
  let Hterm : ℝ := ∫ x in U, r x * v x *
    euclideanCoordLaplacian (η : Vec d → ℝ) x ∂volume
  have hU : IsOpenBoundedConvexDomain U :=
    isOpenBoundedConvexDomain_scaledOpenCubeSet_of_pos Qp (by norm_num)
  have hUP : U ⊆ openCubeSet Qp := by
    intro x hx
    apply scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one Qp
      (ρ := 1 / 2) (by norm_num) (by norm_num)
    intro j; exact le_of_lt (hx j)
  have hηmeas : AEStronglyMeasurable (η : Vec d → ℝ)
      (normalizedCubeMeasure Qp) := η.smooth.continuous.aestronglyMeasurable
  have hEmeas : AEStronglyMeasurable
      (fun x ↦ HilbertVec.ofVec (euclideanGradient (η : Vec d → ℝ) x))
      (normalizedCubeMeasure Qp) := by
    apply Continuous.aestronglyMeasurable
    apply (HilbertVec.ofVecL d).continuous.comp
    exact continuous_pi fun j => (contDiff_euclideanCoordDeriv η.smooth j).continuous
  have hD := localized_Dterm_raw_bound Qp q U hU.isOpen.measurableSet hUP
    (η : Vec d → ℝ) b v.toH1Function.grad
    hbq
    hvgrad hηmeas (fun x => ⟨η.nonneg x, η.le_one x⟩)
  let Kg : ℝ := (d : ℝ) * (quantitativeCubeCutoffGradientConst d /
    (((5 / 12 : ℝ) - 1 / 3) * cubeRadius Qp))
  have hKg : 0 ≤ Kg := by
    exact (norm_nonneg (HilbertVec.ofVec (euclideanGradient (η : Vec d → ℝ) 0))).trans
      (by simpa only [Kg] using quantitativeCubeCutoff_hilbertGradient_bound η 0)
  have hgradbound : ∀ x, ‖HilbertVec.ofVec
      (euclideanGradient (η : Vec d → ℝ) x)‖ ≤ Kg := by
    intro x
    simpa only [Kg] using quantitativeCubeCutoff_hilbertGradient_bound η x
  have hE := localized_Eterm_raw_bound Qp q i U hU.isOpen.measurableSet hUP b
    (euclideanGradient (η : Vec d → ℝ)) v.toH1Function.toFun hKg hbq hEmeas
    hgradbound hvfun
  have hA := localized_Aterm_raw_bound Qp q i U hU.isOpen.measurableSet hUP r
    v.toH1Function.grad (euclideanGradient (η : Vec d → ℝ)) hKg hrq hvgrad hEmeas
    hgradbound
  have hLmeas : AEStronglyMeasurable (euclideanCoordLaplacian (η : Vec d → ℝ))
      (normalizedCubeMeasure Qp) :=
    (contDiff_euclideanCoordLaplacian η.smooth).continuous.aestronglyMeasurable
  let Kl : ℝ := (d : ℝ) * (quantitativeCubeCutoffHessianConst d /
    (((5 / 12 : ℝ) - 1 / 3) * cubeRadius Qp) ^ 2)
  have hKl : 0 ≤ Kl := by
    exact (abs_nonneg (euclideanCoordLaplacian (η : Vec d → ℝ) 0)).trans
      (by simpa only [Kl] using quantitativeCubeCutoff_euclideanCoordLaplacian_bound η 0)
  have hlapbound : ∀ x, |euclideanCoordLaplacian (η : Vec d → ℝ) x| ≤ Kl := by
    intro x
    simpa only [Kl] using quantitativeCubeCutoff_euclideanCoordLaplacian_bound η x
  have hH := localized_Hterm_raw_bound Qp q i U hU.isOpen.measurableSet hUP r
    v.toH1Function.toFun (euclideanCoordLaplacian (η : Vec d → ℝ)) hKl hrq hLmeas.restrict
    hlapbound hvfun
  refine ⟨r, b, D, E, A, Hterm, hrowid, hbeq, ?_, ?_, ?_, ?_, ?_, hbNorm, hrNorm,
    hvval, ?_⟩
  · let Rref : Vec d → Vec d :=
      cubeDirichletOddReflectionHessianRowVectorField (originCube d m) i
        (fun y j ↦ H.hess i j y)
    have hrowid' : r.grad =ᵐ[volume.restrict U] Rref := by
      filter_upwards [hrowid] with x hx
      apply_fun (fun z : HilbertVec d ↦ z.toVec) at hx
      simpa only [HilbertVec.toVec_ofVec] using! hx
    have hleft :
        (∫ x in U, vecDot (GP.toField x)
          (fun j ↦ η x * Rref x j + r x *
            euclideanGradient (η : Vec d → ℝ) x j) ∂volume) =
        ∫ x in U, vecDot (GP.toField x)
          (fun j ↦ η x * r.grad x j + r x *
            euclideanGradient (η : Vec d → ℝ) x j) ∂volume := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hrowid'] with x hx
      simp only [hx]
    rw [← hηeq]
    calc
      (∫ x in U, vecDot (GP.toField x)
          (fun j ↦ η x * Rref x j + r x *
            euclideanGradient (η : Vec d → ℝ) x j) ∂volume) =
        ∫ x in U, vecDot (GP.toField x)
          (fun j ↦ η x * r.grad x j + r x *
            euclideanGradient (η : Vec d → ℝ) x j) ∂volume := hleft
      _ = D + E - 2 * A - Hterm := by
        simpa only [Qp, U, G, GP, v, D, E, A, Hterm] using hid
  · simpa only [D] using! hD
  · simpa only [E, Kg] using! hE
  · simpa only [A, Kg] using! hA
  · simpa only [Hterm, Kl] using hH
  · exact hvgradBound

private theorem cutoff_gradient_parent_scale_eq
    {d : ℕ} (m : ℤ) :
    (d : ℝ) *
        (quantitativeCubeCutoffGradientConst d /
          (((5 / 12 : ℝ) - (1 / 3 : ℝ)) *
            cubeRadius (originCube d (m + 1)))) *
      centeredCubeScale (m + 1) =
        (24 : ℝ) * d * quantitativeCubeCutoffGradientConst d := by
  let s : ℝ := (3 : ℝ) ^ m
  have hspos : 0 < s := by dsimp [s]; exact zpow_pos (by norm_num) m
  have hsne : s ≠ 0 := hspos.ne'
  have hparent : cubeRadius (originCube d (m + 1)) = (3 / 2 : ℝ) * s := by
    dsimp [cubeRadius, cubeScaleFactor, originCube, s]
    rw [zpow_add₀]
    · norm_num; ring
    · norm_num
  change (d : ℝ) *
      (quantitativeCubeCutoffGradientConst d /
        (((5 / 12 : ℝ) - (1 / 3 : ℝ)) *
          cubeRadius (originCube d (m + 1)))) * (3 : ℝ) ^ (m + 1) = _
  rw [hparent, zpow_add₀]
  · norm_num
    field_simp [hsne]
    ring
  · norm_num

private theorem cutoff_gradient_source_scale_eq
    {d : ℕ} (m : ℤ) :
    (d : ℝ) *
        (quantitativeCubeCutoffGradientConst d /
          (((5 / 12 : ℝ) - (1 / 3 : ℝ)) *
            cubeRadius (originCube d (m + 1)))) *
      centeredCubeScale m =
        (8 : ℝ) * d * quantitativeCubeCutoffGradientConst d := by
  let s : ℝ := (3 : ℝ) ^ m
  have hspos : 0 < s := by dsimp [s]; exact zpow_pos (by norm_num) m
  have hsne : s ≠ 0 := hspos.ne'
  have hparent : cubeRadius (originCube d (m + 1)) = (3 / 2 : ℝ) * s := by
    dsimp [cubeRadius, cubeScaleFactor, originCube, s]
    rw [zpow_add₀]
    · norm_num; ring
    · norm_num
  change (d : ℝ) *
      (quantitativeCubeCutoffGradientConst d /
        (((5 / 12 : ℝ) - (1 / 3 : ℝ)) *
          cubeRadius (originCube d (m + 1)))) * (3 : ℝ) ^ m = _
  rw [hparent]
  norm_num
  field_simp [hsne]
  ring

private theorem cutoff_hessian_scale_eq
    {d : ℕ} (m : ℤ) :
    (d : ℝ) *
        (quantitativeCubeCutoffHessianConst d /
          ((((5 / 12 : ℝ) - (1 / 3 : ℝ)) *
            cubeRadius (originCube d (m + 1))) ^ 2)) *
      centeredCubeScale m * centeredCubeScale (m + 1) =
        (192 : ℝ) * d * quantitativeCubeCutoffHessianConst d := by
  let s : ℝ := (3 : ℝ) ^ m
  have hspos : 0 < s := by dsimp [s]; exact zpow_pos (by norm_num) m
  have hsne : s ≠ 0 := hspos.ne'
  have hparent : cubeRadius (originCube d (m + 1)) = (3 / 2 : ℝ) * s := by
    dsimp [cubeRadius, cubeScaleFactor, originCube, s]
    rw [zpow_add₀]
    · norm_num; ring
    · norm_num
  change (d : ℝ) *
      (quantitativeCubeCutoffHessianConst d /
        ((((5 / 12 : ℝ) - (1 / 3 : ℝ)) *
          cubeRadius (originCube d (m + 1))) ^ 2)) *
        (3 : ℝ) ^ m * (3 : ℝ) ^ (m + 1) = _
  rw [hparent, zpow_add₀]
  · norm_num
    field_simp [hsne]
    ring
  · norm_num

private theorem cutoff_coefficient_nonneg_and_bounds
    {d : ℕ} (m : ℤ) :
    let Kg : ℝ := (d : ℝ) *
      (quantitativeCubeCutoffGradientConst d /
        (((5 / 12 : ℝ) - (1 / 3 : ℝ)) * cubeRadius (originCube d (m + 1))))
    let Kl : ℝ := (d : ℝ) *
      (quantitativeCubeCutoffHessianConst d /
        ((((5 / 12 : ℝ) - (1 / 3 : ℝ)) * cubeRadius (originCube d (m + 1))) ^ 2))
    0 ≤ Kg ∧ 0 ≤ Kl ∧
    Kg * centeredCubeScale (m + 1) ≤
      24 * d * quantitativeCubeCutoffGradientConst d ∧
    Kg * centeredCubeScale m ≤
      24 * d * quantitativeCubeCutoffGradientConst d ∧
    Kl * centeredCubeScale m * centeredCubeScale (m + 1) ≤
      192 * d * quantitativeCubeCutoffHessianConst d := by
  dsimp
  have hg : 0 ≤ quantitativeCubeCutoffGradientConst d := by
    dsimp [quantitativeCubeCutoffGradientConst]
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
      smoothTransitionProfile.derivBound_nonneg
  have hh : 0 ≤ quantitativeCubeCutoffHessianConst d := by
    dsimp [quantitativeCubeCutoffHessianConst]
    positivity
  have hden : 0 ≤ ((5 / 12 : ℝ) - (1 / 3 : ℝ)) *
      cubeRadius (originCube d (m + 1)) :=
    mul_nonneg (by norm_num) (cubeRadius_pos _).le
  have hden2 : 0 ≤ (((5 / 12 : ℝ) - (1 / 3 : ℝ)) *
      cubeRadius (originCube d (m + 1))) ^ 2 := sq_nonneg _
  refine ⟨mul_nonneg (Nat.cast_nonneg d) (div_nonneg hg hden),
    mul_nonneg (Nat.cast_nonneg d) (div_nonneg hh hden2), ?_, ?_, ?_⟩
  · rw [cutoff_gradient_parent_scale_eq]
  · rw [cutoff_gradient_source_scale_eq]
    nlinarith [mul_nonneg (Nat.cast_nonneg d) hg]
  · rw [cutoff_hessian_scale_eq]

private theorem coefficient_K_toReal_mul_source_norm
    {Fq : ℝ≥0∞} {ratio kg kl Ccz P Csrc Nn : ℝ}
    (hratio : 0 ≤ ratio) (hCcz : 0 ≤ Ccz) (hP : 0 ≤ P)
    (hCsrc : 0 ≤ Csrc) (hkg : 0 ≤ kg) (hkl : 0 ≤ kl) :
    let K0 : ℝ≥0∞ := ENNReal.ofReal
      (ratio * Ccz * (1 + kg * P + 2 * kg * Csrc + kl * Csrc * P))
    K0.toReal * Fq.toReal * Nn =
      (ratio * Ccz * (1 + kg * P + 2 * kg * Csrc + kl * Csrc * P) *
        Fq.toReal) * Nn := by
  dsimp
  have hK : 0 ≤ ratio * Ccz *
      (1 + kg * P + 2 * kg * Csrc + kl * Csrc * P) := by positivity
  rw [ENNReal.toReal_ofReal hK]

private theorem row_eLpNorm_of_raw_term_bounds
    {d : ℕ} {m : ℤ} (q : FiniteLpExponent)
    {u : H1Function (openCubeSet (originCube d m))}
    (Hsrc : HasWeakHessianOn (openCubeSet (originCube d m)) u)
    (i : Fin d) {K : ℝ≥0∞} (hKtop : K ≠ ∞)
    (hterms : ∀ n : ℕ, ∃ (D E A Hterm BD BE BA BH : ℝ),
      let Q := originCube d m
      let Qp := originCube d (m + 1)
      let U := scaledOpenCubeSet Qp (1 / 2 : ℝ)
      let η := QuantitativeCubeCutoff.canonical Qp (1 / 3 : ℝ) (5 / 12 : ℝ)
        (by norm_num) (by norm_num)
      let R : Vec d → Vec d := fun x j => Hsrc.hess i j x
      let G := (sourceHessianRowRadialDatum q Hsrc i n).toField
      let r : Vec d → ℝ := fun _ => 0
      let Jraw := ∫ x in U, vecDot (openParentDatumExtension (openCubeSet Q) G x)
        (fun j => η x *
          cubeDirichletOddReflectionHessianRowVectorField Q i R x j +
          r x * (fderiv ℝ (η : Vec d → ℝ) x) (basisVec j)) ∂volume
      Jraw = D + E - 2 * A - Hterm ∧
      |D| ≤ cubeVolume Q * BD ∧ |E| ≤ cubeVolume Q * BE ∧
      |A| ≤ cubeVolume Q * BA ∧ |Hterm| ≤ cubeVolume Q * BH ∧
      BD + BE + 2 * BA + BH ≤ K.toReal *
        ((∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n
          (fun x => HilbertVec.ofVec (fun j => Hsrc.hess i j x)) x ∂
          normalizedCubeMeasure Q) ^ (1 - q.exponent.toReal⁻¹)).toReal) :
    MemLp (fun x ↦ HilbertVec.ofVec (fun j ↦ Hsrc.hess i j x)) q.exponent
      (normalizedCubeMeasure (originCube d m)) ∧
    eLpNorm (fun x ↦ HilbertVec.ofVec (fun j ↦ Hsrc.hess i j x)) q.exponent
      (normalizedCubeMeasure (originCube d m)) ≤ K := by
  let R : Vec d → HilbertVec d := fun x ↦ HilbertVec.ofVec (fun j ↦ Hsrc.hess i j x)
  have hRtwo : MemLp R 2 (normalizedCubeMeasure (originCube d m)) := by
    simpa only [R] using! Hsrc.hessianHilbertRow_memLp_two_normalizedCubeMeasure
      (originCube d m) i
  have hqreal : 1 < q.exponent.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).mpr q.one_lt
  have hbound : eLpNorm R q.exponent
      (normalizedCubeMeasure (originCube d m)) ≤ K := by
    rw [← ENNReal.ofReal_toReal q.lt_top.ne]
    apply INTERNAL.eLpNorm_le_of_truncated_cross_bound hqreal hRtwo.aestronglyMeasurable
    exact source_hessian_row_htrunc_of_raw_term_bounds q Hsrc i hKtop hterms
  refine ⟨⟨hRtwo.aestronglyMeasurable, lt_of_le_of_lt hbound hKtop.lt_top⟩, ?_⟩
  simpa only [R] using hbound

private theorem source_hessian_row_raw_term_package
    {d : ℕ} [NeZero d] {q : FiniteLpExponent}
    (hq : q.exponent.toReal < 2) :
    ∃ Crow : ℝ≥0∞, Crow < ∞ ∧ ∀ (m : ℤ) (F : Vec d → ℝ),
      MemLp F 2 (normalizedCubeMeasure (originCube d m)) →
      MemLp F q.exponent (normalizedCubeMeasure (originCube d m)) →
      ∀ (u : H10Function (openCubeSet (originCube d m))),
      CubeDirichletWeakPoissonProblem (originCube d m) u F →
      ∀ (H : HasWeakHessianOn (openCubeSet (originCube d m)) u.toH1Function)
      (i : Fin d),
        MemLp (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x)) q.exponent
          (normalizedCubeMeasure (originCube d m)) ∧
        eLpNorm (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x)) q.exponent
          (normalizedCubeMeasure (originCube d m)) ≤
          Crow * eLpNorm F q.exponent (normalizedCubeMeasure (originCube d m)) := by
  obtain ⟨Csrc, hCsrcTop, hCsrc⟩ := source_gradient_below_two_bound (d := d) hq
  have hqconj : 2 < q.conjugate.exponent.toReal :=
    INTERNAL.conjugate_toReal_gt_two_of_lt_two q hq
  obtain ⟨Ccz, P, hCczTop, hPTop, hAdj⟩ :=
    exists_parent_adjoint_value_bound d q.conjugate hqconj
  let ratio : ℝ := (3 : ℝ) ^ d
  let kg : ℝ := 24 * d * quantitativeCubeCutoffGradientConst d
  let kl : ℝ := 192 * d * quantitativeCubeCutoffHessianConst d
  let K0 : ℝ≥0∞ := ENNReal.ofReal
    (ratio * Ccz.toReal *
      (1 + kg * P.toReal + 2 * kg * Csrc.toReal + kl * Csrc.toReal * P.toReal))
  refine ⟨K0, ENNReal.ofReal_lt_top, ?_⟩
  intro m F hF2 hFq u hweak H i
  let K : ℝ≥0∞ := K0 * eLpNorm F q.exponent
    (normalizedCubeMeasure (originCube d m))
  have hKtop : K ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFq.eLpNorm_ne_top
  apply row_eLpNorm_of_raw_term_bounds q H i hKtop
  intro n
  let Q : TriadicCube d := originCube d m
  let Qp : TriadicCube d := originCube d (m + 1)
  let U : Set (Vec d) := scaledOpenCubeSet Qp (1 / 2 : ℝ)
  let η := QuantitativeCubeCutoff.canonical Qp (1 / 3 : ℝ) (5 / 12 : ℝ)
    (by norm_num) (by norm_num)
  let R : Vec d → Vec d := fun x j => H.hess i j x
  let G := sourceHessianRowRadialDatum q H i n
  let Nn : ℝ≥0∞ := eLpNorm (hilbertifyVecField G.toField)
    q.conjugate.exponent (normalizedCubeMeasure Q)
  let B : ℝ≥0∞ := Csrc * ENNReal.ofReal (centeredCubeScale m) *
    eLpNorm F q.exponent (normalizedCubeMeasure Q)
  have hgrad : eLpNorm (hilbertifyVecField u.toH1Function.grad) q.exponent
      (normalizedCubeMeasure Q) ≤ B := by
    simpa only [Q, B, centeredCubeScale, cubeScaleFactor_originCube] using
      hCsrc m F u hF2 hFq hweak
  have hBtop : B < ∞ := by
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hCsrcTop ENNReal.ofReal_lt_top)
      hFq.eLpNorm_lt_top
  obtain ⟨r, b, D, E, A, Hterm, _, _, hid, hD, hE, hA, hH, hbNorm,
    hrNorm, hvval, hvgrad⟩ :=
    actual_mutual_raw_term_bounds q hF2 hFq hBtop hweak H i hgrad hAdj n
  let Kg : ℝ := (d : ℝ) * (quantitativeCubeCutoffGradientConst d /
    (((5 / 12 : ℝ) - 1 / 3) * cubeRadius Qp))
  let Kl : ℝ := (d : ℝ) * (quantitativeCubeCutoffHessianConst d /
    (((5 / 12 : ℝ) - 1 / 3) * cubeRadius Qp) ^ 2)
  let FqNorm : ℝ≥0∞ := eLpNorm F q.exponent (normalizedCubeMeasure Q)
  let Vgrad : ℝ≥0∞ := eLpNorm
    (hilbertifyVecField (openCubeSetScalarDivergenceSolution Qp (by norm_num : (0 : ℝ) < 1)
      (sourceParentFiniteLpExtension m q.conjugate G).toField
      (memVectorL2_sourceParentFiniteLpExtension m q.conjugate G)).toH1Function.grad)
    q.conjugate.exponent (normalizedCubeMeasure Qp)
  let Vval : ℝ≥0∞ := eLpNorm
    (openCubeSetScalarDivergenceSolution Qp (by norm_num : (0 : ℝ) < 1)
      (sourceParentFiniteLpExtension m q.conjugate G).toField
      (memVectorL2_sourceParentFiniteLpExtension m q.conjugate G)).toH1Function.toFun
    q.conjugate.exponent (normalizedCubeMeasure Qp)
  let Rval : ℝ≥0∞ := eLpNorm r.toFun q.exponent
    ((normalizedCubeMeasure Qp).restrict U)
  let BD : ℝ := |D| / cubeVolume Q
  let BE : ℝ := |E| / cubeVolume Q
  let BA : ℝ := |A| / cubeVolume Q
  let BH : ℝ := |Hterm| / cubeVolume Q
  have hvol : cubeVolume Qp = cubeVolume Q * ratio := by
    have hratio := originCube_parent_volume_ratio (d := d) m
    calc
      cubeVolume Qp = (cubeVolume Qp / cubeVolume Q) * cubeVolume Q :=
        (div_mul_cancel₀ _ (cubeVolume_pos Q).ne').symm
      _ = cubeVolume Q * ratio := by rw [hratio]; ring
  refine ⟨D, E, A, Hterm, BD, BE, BA, BH, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hGP : (sourceParentFiniteLpExtension m q.conjugate G).toField =
        openParentDatumExtension (openCubeSet Q) G.toField := by
      simpa only [Q, G] using sourceParentFiniteLpExtension_toField m q.conjugate G
    have hid' :
        (∫ x in U, vecDot (openParentDatumExtension (openCubeSet Q) G.toField x)
          (fun j => η x * cubeDirichletOddReflectionHessianRowVectorField Q i R x j +
            r x * (fderiv ℝ (η : Vec d → ℝ) x) (basisVec j)) ∂volume) =
          D + E - 2 * A - Hterm := by
      simpa only [Q, Qp, U, η, R, G, euclideanGradient] using hGP ▸ hid
    calc
      _ = ∫ x in U, vecDot (openParentDatumExtension (openCubeSet Q) G.toField x)
          (fun j => η x * cubeDirichletOddReflectionHessianRowVectorField Q i R x j +
            r x * (fderiv ℝ (η : Vec d → ℝ) x) (basisVec j)) ∂volume := by
        simpa only [Q, Qp, U, η, R, G] using
          (actual_Jraw_congr_row_value (d := d) m i R G.toField (fun _ => 0) r)
      _ = _ := hid'
  · change |D| ≤ cubeVolume Q * (|D| / cubeVolume Q)
    rw [mul_div_cancel₀ _ (cubeVolume_pos Q).ne']
  · change |E| ≤ cubeVolume Q * (|E| / cubeVolume Q)
    rw [mul_div_cancel₀ _ (cubeVolume_pos Q).ne']
  · change |A| ≤ cubeVolume Q * (|A| / cubeVolume Q)
    rw [mul_div_cancel₀ _ (cubeVolume_pos Q).ne']
  · change |Hterm| ≤ cubeVolume Q * (|Hterm| / cubeVolume Q)
    rw [mul_div_cancel₀ _ (cubeVolume_pos Q).ne']
  · obtain ⟨hKg, hKl, hKgsp, hKgss, hKlsssp⟩ :=
      cutoff_coefficient_nonneg_and_bounds (d := d) m
    have hratio : 0 ≤ ratio := by dsimp [ratio]; positivity
    have hCcz : 0 ≤ Ccz.toReal := ENNReal.toReal_nonneg
    have hP : 0 ≤ P.toReal := ENNReal.toReal_nonneg
    have hCsrc : 0 ≤ Csrc.toReal := ENNReal.toReal_nonneg
    have hss : 0 ≤ centeredCubeScale m := by dsimp [centeredCubeScale]; positivity
    have hF : 0 ≤ FqNorm.toReal := ENNReal.toReal_nonneg
    have hNn : 0 ≤ Nn.toReal := ENNReal.toReal_nonneg
    have hNtop : Nn ≠ ∞ := G.euclideanMemLp.eLpNorm_ne_top
    have hVgrad : Vgrad.toReal ≤ Ccz.toReal * Nn.toReal := by
      have hright : Ccz * Nn ≠ ∞ := ENNReal.mul_ne_top hCczTop.ne hNtop
      have h := ENNReal.toReal_mono hright (by
        simpa only [Q, Qp, G, Nn, Vgrad] using hvgrad)
      simpa only [ENNReal.toReal_mul] using h
    have hVval : Vval.toReal ≤ P.toReal * centeredCubeScale (m + 1) *
        Ccz.toReal * Nn.toReal := by
      have hscale : 0 ≤ centeredCubeScale (m + 1) := (centeredCubeScale_pos _).le
      have hright : P * ENNReal.ofReal (centeredCubeScale (m + 1)) * Ccz * Nn ≠ ∞ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hPTop.ne
          ENNReal.ofReal_ne_top) hCczTop.ne) hNtop
      have h := ENNReal.toReal_mono hright (by
        simpa only [Q, Qp, G, Nn, Vval] using hvval)
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hscale] using h
    have hRval : Rval.toReal ≤ Csrc.toReal * centeredCubeScale m * FqNorm.toReal := by
      have hscale : 0 ≤ centeredCubeScale m := (centeredCubeScale_pos _).le
      have hright : Csrc * ENNReal.ofReal (centeredCubeScale m) * FqNorm ≠ ∞ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top hCsrcTop.ne ENNReal.ofReal_ne_top)
          hFq.eLpNorm_ne_top
      have h := ENNReal.toReal_mono hright (by
        simpa only [Q, B, FqNorm] using hrNorm)
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hscale] using h
    have hFbound : FqNorm.toReal ≤ FqNorm.toReal := le_rfl
    have hDdiv : |D| / cubeVolume Q ≤ ratio * FqNorm.toReal * Vgrad.toReal := by
      rw [div_le_iff₀ (cubeVolume_pos Q)]
      calc
        |D| ≤ cubeVolume Qp * FqNorm.toReal * Vgrad.toReal := by
          simpa only [Q, Qp, FqNorm, Vgrad] using hbNorm ▸ hD
        _ = (ratio * FqNorm.toReal * Vgrad.toReal) * cubeVolume Q := by rw [hvol]; ring
    have hEdiv : |E| / cubeVolume Q ≤ ratio * (Kg.toNNReal • FqNorm).toReal * Vval.toReal := by
      rw [div_le_iff₀ (cubeVolume_pos Q)]
      calc
        |E| ≤ cubeVolume Qp * (Kg.toNNReal • FqNorm).toReal * Vval.toReal := by
          simpa only [Q, Qp, FqNorm, Vval, Kg] using hbNorm ▸ hE
        _ = (ratio * (Kg.toNNReal • FqNorm).toReal * Vval.toReal) * cubeVolume Q := by
          rw [hvol]; ring
    have hAdiv : |A| / cubeVolume Q ≤ ratio * Rval.toReal * (Kg.toNNReal • Vgrad).toReal := by
      rw [div_le_iff₀ (cubeVolume_pos Q)]
      calc
        |A| ≤ cubeVolume Qp * Rval.toReal * (Kg.toNNReal • Vgrad).toReal := by
          simpa only [Q, Qp, U, Rval, Vgrad, Kg] using hA
        _ = (ratio * Rval.toReal * (Kg.toNNReal • Vgrad).toReal) * cubeVolume Q := by
          rw [hvol]; ring
    have hHdiv : |Hterm| / cubeVolume Q ≤ ratio * (Kl.toNNReal • Rval).toReal * Vval.toReal := by
      rw [div_le_iff₀ (cubeVolume_pos Q)]
      calc
        |Hterm| ≤ cubeVolume Qp * (Kl.toNNReal • Rval).toReal * Vval.toReal := by
          simpa only [Q, Qp, U, Rval, Vval, Kl] using hH
        _ = (ratio * (Kl.toNNReal • Rval).toReal * Vval.toReal) * cubeVolume Q := by
          rw [hvol]; ring
    have hsum := coefficient_algebra_after_raw_division
      (D := |D| / cubeVolume Q) (E := |E| / cubeVolume Q)
      (A := |A| / cubeVolume Q) (Hterm := |Hterm| / cubeVolume Q)
      (ratio := ratio) (Kg := Kg) (Kl := Kl) (kg := kg) (kl := kl)
      (Ccz := Ccz.toReal) (P := P.toReal) (Csrc := Csrc.toReal)
      (ss := centeredCubeScale m) (sp := centeredCubeScale (m + 1))
      (F := FqNorm.toReal) (Nn := Nn.toReal)
      hratio hKg hKl hCcz hP hCsrc hss hF hNn hFbound hVgrad hVval hRval
      hKgsp hKgss hKlsssp
      (by rw [abs_of_nonneg (div_nonneg (abs_nonneg _) (cubeVolume_pos Q).le)]; exact hDdiv)
      (by rw [abs_of_nonneg (div_nonneg (abs_nonneg _) (cubeVolume_pos Q).le)]; exact hEdiv)
      (by rw [abs_of_nonneg (div_nonneg (abs_nonneg _) (cubeVolume_pos Q).le)]; exact hAdiv)
      (by rw [abs_of_nonneg (div_nonneg (abs_nonneg _) (cubeVolume_pos Q).le)]; exact hHdiv)
    have hkg : 0 ≤ kg := by
      have hgc : 0 ≤ quantitativeCubeCutoffGradientConst d := by
        dsimp [quantitativeCubeCutoffGradientConst]
        exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
          smoothTransitionProfile.derivBound_nonneg
      exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hgc
    have hkl : 0 ≤ kl := by
      dsimp [kl, quantitativeCubeCutoffHessianConst]
      positivity
    have hKcoeff := coefficient_K_toReal_mul_source_norm
      (Fq := FqNorm) (ratio := ratio) (kg := kg) (kl := kl)
      (Ccz := Ccz.toReal) (P := P.toReal) (Csrc := Csrc.toReal) (Nn := Nn.toReal)
      hratio hCcz hP hCsrc hkg hkl
    have hNmoment : Nn =
        (∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n
          (fun x => HilbertVec.ofVec (fun j => H.hess i j x)) x ∂
          normalizedCubeMeasure Q) ^ (1 - q.exponent.toReal⁻¹) := by
      simpa only [Q, G, Nn] using source_hessian_row_radial_norm_eq_moment_rpow q H i n
    calc
      BD + BE + 2 * BA + BH =
          |D| / cubeVolume Q + |E| / cubeVolume Q +
            2 * (|A| / cubeVolume Q) + |Hterm| / cubeVolume Q := by rfl
      _ ≤ (ratio * Ccz.toReal *
          (1 + kg * P.toReal + 2 * kg * Csrc.toReal + kl * Csrc.toReal * P.toReal) *
          FqNorm.toReal) * Nn.toReal := by
        simpa only [abs_of_nonneg (div_nonneg (abs_nonneg _) (cubeVolume_pos Q).le)] using hsum
      _ = K.toReal * Nn.toReal := by
        simpa only [K, ENNReal.toReal_mul, K0, FqNorm] using hKcoeff.symm
      _ = K.toReal *
          ((∫⁻ x, INTERNAL.truncatedMoment q.exponent.toReal n
            (fun x => HilbertVec.ofVec (fun j => H.hess i j x)) x ∂
            normalizedCubeMeasure Q) ^ (1 - q.exponent.toReal⁻¹)).toReal := by rw [hNmoment]

private theorem outer_hessian_from_row_bootstrap
    (d : ℕ) [NeZero d] (q : FiniteLpExponent)
    (Crow : ℝ≥0∞) (hCrow : Crow < ∞)
    (hrow : ∀ (m : ℤ) (F : Vec d → ℝ),
      MemLp F 2 (normalizedCubeMeasure (originCube d m)) →
      MemLp F q.exponent (normalizedCubeMeasure (originCube d m)) →
      ∀ (u : H10Function (openCubeSet (originCube d m))),
      CubeDirichletWeakPoissonProblem (originCube d m) u F →
      ∀ (H : HasWeakHessianOn (openCubeSet (originCube d m)) u.toH1Function),
      MemLp (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x)) 2
        (normalizedCubeMeasure (originCube d m)) →
      ∀ i : Fin d,
        MemLp (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x)) q.exponent
          (normalizedCubeMeasure (originCube d m)) ∧
        eLpNorm (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x)) q.exponent
          (normalizedCubeMeasure (originCube d m)) ≤
          Crow * eLpNorm F q.exponent (normalizedCubeMeasure (originCube d m))) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (F : Vec d → ℝ),
      MemLp F 2 (normalizedCubeMeasure (originCube d m)) →
      MemLp F q.exponent (normalizedCubeMeasure (originCube d m)) →
      ∀ u : H10Function (openCubeSet (originCube d m)),
        CubeDirichletWeakPoissonProblem (originCube d m) u F →
        ∃ H : HasWeakHessianOn (openCubeSet (originCube d m)) u.toH1Function,
          MemLp (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x)) q.exponent
            (normalizedCubeMeasure (originCube d m)) ∧
          eLpNorm (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x)) q.exponent
            (normalizedCubeMeasure (originCube d m)) ≤
            C * eLpNorm F q.exponent (normalizedCubeMeasure (originCube d m)) := by
  obtain ⟨_, _, htwo⟩ :=
    exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le_two d
  let C : ℝ≥0∞ := d * Crow
  refine ⟨C, ENNReal.mul_lt_top ENNReal.coe_lt_top hCrow, ?_⟩
  intro m F hF2 hFq u hweak
  obtain ⟨H, hHtwo, _⟩ := htwo m F hF2 u hweak
  have hrows := fun i ↦ hrow m F hF2 hFq u hweak H hHtwo i
  have hrowsMem : ∀ i : Fin d,
      MemLp (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x)) q.exponent
        (normalizedCubeMeasure (originCube d m)) := fun i ↦ (hrows i).1
  refine ⟨H, H.hessianHilbertMat_memLp_normalizedCubeMeasure_of_rows
    (originCube d m) q hrowsMem, ?_⟩
  calc
    eLpNorm (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x)) q.exponent
        (normalizedCubeMeasure (originCube d m)) ≤
      ∑ i : Fin d, eLpNorm (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x))
        q.exponent (normalizedCubeMeasure (originCube d m)) :=
      H.eLpNorm_hessianHilbertMat_normalizedCubeMeasure_le_sum_rows
        (originCube d m) q hrowsMem
    _ ≤ ∑ _i : Fin d, Crow * eLpNorm F q.exponent
        (normalizedCubeMeasure (originCube d m)) :=
      Finset.sum_le_sum fun i _ ↦ (hrows i).2
    _ = C * eLpNorm F q.exponent (normalizedCubeMeasure (originCube d m)) := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, C]
      ring

/-- Calderón--Zygmund Hessian estimate on centered cubes below the energy
exponent.  The Hessian representative is supplied by the energy estimate and
its `L^q` bound is obtained row-by-row from the localized duality argument. -/
theorem exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le_of_lt_two
    (d : ℕ) [NeZero d] (q : FiniteLpExponent)
    (hq : q.exponent.toReal < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (F : Vec d → ℝ),
      MemLp F 2 (normalizedCubeMeasure (originCube d m)) →
      MemLp F q.exponent (normalizedCubeMeasure (originCube d m)) →
      ∀ u : H10Function (openCubeSet (originCube d m)),
        CubeDirichletWeakPoissonProblem (originCube d m) u F →
        ∃ H : HasWeakHessianOn (openCubeSet (originCube d m)) u.toH1Function,
          MemLp (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x)) q.exponent
            (normalizedCubeMeasure (originCube d m)) ∧
          eLpNorm (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x)) q.exponent
            (normalizedCubeMeasure (originCube d m)) ≤
            C * eLpNorm F q.exponent (normalizedCubeMeasure (originCube d m)) := by
  obtain ⟨Crow, hCrow, hrow⟩ :=
    source_hessian_row_raw_term_package (d := d) (q := q) hq
  apply outer_hessian_from_row_bootstrap d q Crow hCrow
  intro m F hF2 hFq u hweak H _ i
  exact hrow m F hF2 hFq u hweak H i

/-- The centered-cube formulation of the below-two Hessian estimate. -/
theorem centeredCubeH10ScalarPoisson_hessian_cz_of_lt_two
    (d : ℕ) [NeZero d] (q : FiniteLpExponent)
    (hq : q.exponent.toReal < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (F : Vec d → ℝ),
      MemLp F 2 (normalizedCubeMeasure (originCube d m)) →
      MemLp F q.exponent (normalizedCubeMeasure (originCube d m)) →
      ∀ u : H10Function (openCubeSet (originCube d m)),
        CubeDirichletWeakPoissonProblem (originCube d m) u F →
        ∃ H : HasWeakHessianOn (openCubeSet (originCube d m)) u.toH1Function,
          MemLp (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x)) q.exponent
            (normalizedCubeMeasure (originCube d m)) ∧
          eLpNorm (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x)) q.exponent
            (normalizedCubeMeasure (originCube d m)) ≤
            C * eLpNorm F q.exponent (normalizedCubeMeasure (originCube d m)) :=
  exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le_of_lt_two d q hq

end CubeCalderonZygmund

end
end Homogenization
