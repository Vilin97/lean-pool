/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.LimitHessianPointwise
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ScaledCubeGeometry
import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.Basic

/-! # Harmonic Interior Hessian -/

namespace Homogenization

open scoped ENNReal

noncomputable section

/-!
# Fixed-radius interior weak Hessians for harmonic functions

This is an internal regularity-engine wrapper around the existing
difference-quotient construction.  It fixes all geometric radii, so callers of
the harmonic regularity chain need provide neither cutoffs nor forcing
integrability nor a Hessian witness.
-/

namespace CubeCalderonZygmund

variable {d : ℕ}

/-- Internal cutoff from the half cube to the seven-twelfths cube, leaving a
strict margin inside the two-thirds ambient region. -/
noncomputable def innerHalfSevenTwelfthCutoff (Q : TriadicCube d) :
    QuantitativeCubeCutoff Q (1 / 2 : ℝ) (7 / 12 : ℝ) :=
  QuantitativeCubeCutoff.canonical Q (1 / 2 : ℝ) (7 / 12 : ℝ)
    (by norm_num) (by norm_num)

/-- Internal outer cutoff used by the fixed-radius interior construction. -/
noncomputable def outerThreeQuarterSevenEighthCutoff (Q : TriadicCube d) :
    QuantitativeCubeCutoff Q (3 / 4 : ℝ) (7 / 8 : ℝ) :=
  QuantitativeCubeCutoff.canonical Q (3 / 4 : ℝ) (7 / 8 : ℝ)
    (by norm_num) (by norm_num)

/-- A weakly harmonic `H¹` function on a triadic cube has the canonical
strict-interior weak Hessian supplied by the existing difference-quotient
theorem. -/
theorem exists_innerHalf_hasWeakHessianOn_harmonic
    {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}
    (h : WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0)) :
    ∃ uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)),
      uS.toFun = u.toFun ∧
        uS.grad = u.grad ∧
          ∃ H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS,
            H.hessianCoordL2NormSum ≤
              ∑ i : Fin d, ∑ _j : Fin d,
                @WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestBound
                  d Q u (fun _ => 0) i (1 / 2 : ℝ) (7 / 12 : ℝ)
                  (3 / 4 : ℝ) (7 / 8 : ℝ)
                  (outerThreeQuarterSevenEighthCutoff Q) := by
  let V : Set (Vec d) := scaledOpenCubeSet Q (2 / 3 : ℝ)
  have hzero_mem : MemScalarL2 (openCubeSet Q) (fun _ => 0) := by
    simp [MemScalarL2, volumeMeasureOn]
  have hV : IsOpenBoundedConvexDomain V := by
    exact isOpenBoundedConvexDomain_scaledOpenCubeSet_of_pos Q
      (by norm_num : 0 < (2 / 3 : ℝ))
  have hη_sub :
      tsupport (innerHalfSevenTwelfthCutoff Q : Vec d → ℝ) ⊆ V := by
    have hclosed :
        tsupport (innerHalfSevenTwelfthCutoff Q : Vec d → ℝ) ⊆
          scaledClosedCubeSet Q (7 / 12 : ℝ) :=
      (innerHalfSevenTwelfthCutoff Q).tsupport_subset_scaledClosedCubeSet_of_support_subset
    exact hclosed.trans
      (scaledClosedCubeSet_subset_scaledOpenCubeSet_of_lt Q
        (by norm_num : (7 / 12 : ℝ) < 2 / 3))
  have hinnerV : scaledClosedCubeSet Q (1 / 2 : ℝ) ⊆ V := by
    exact scaledClosedCubeSet_subset_scaledOpenCubeSet_of_lt Q
      (by norm_num : (1 / 2 : ℝ) < 2 / 3)
  have hVν : V ⊆ scaledClosedCubeSet Q (2 / 3 : ℝ) :=
    scaledOpenCubeSet_subset_scaledClosedCubeSet Q (2 / 3 : ℝ)
  simpa [V, innerHalfSevenTwelfthCutoff, outerThreeQuarterSevenEighthCutoff] using
    h.exists_hasWeakHessianOn_restrict_hessianCoordL2NormSum_le_of_strict_inner_margin
      hzero_mem hV (innerHalfSevenTwelfthCutoff Q) hη_sub hinnerV
      (outerThreeQuarterSevenEighthCutoff Q) hVν
      (by norm_num : 0 ≤ (2 / 3 : ℝ)) (by norm_num : (2 / 3 : ℝ) < 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1) (by norm_num : 0 ≤ (7 / 8 : ℝ))
      (by norm_num : (7 / 8 : ℝ) < 1) (by norm_num : 0 ≤ (1 / 2 : ℝ))

/-- Harmonicity is unchanged by subtracting the integral average.  This is
spelled out here because the regularity construction is applied to the
mean-zero representative, whereas the public interior carrier keeps the
original value representative. -/
private theorem WeakPoissonEquationOn.subAverage
    {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {u : H1Function U}
    (h : WeakPoissonEquationOn U u (fun _ => 0)) :
    WeakPoissonEquationOn U u.subAverage (fun _ => 0) := by
  intro φ hφ hφs hφ_sub
  simpa only [H1Function.grad_subAverage] using h.test φ hφ hφs hφ_sub

/-- A constant shift of the value representative keeps a weak Hessian with
the same coordinate fields. -/
private noncomputable def HasWeakHessianOn.addConst
    {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {u : H1Function U} (H : HasWeakHessianOn U u) (c : ℝ) :
    HasWeakHessianOn U (u.addConst c) where
  hess := H.hess
  hess_memL2 := H.hess_memL2
  weak_second := by
    intro i j φ hφ hφs hφ_sub
    simpa only [H1Function.grad_addConst] using H.weak_second i j φ hφ hφs hφ_sub

private theorem setIntegral_sq_eq_toScalarL2_norm_sq
    {U : Set (Vec d)} (w : H1Function U) :
    ∫ x in U, w.toFun x ^ 2 ∂MeasureTheory.volume = ‖w.toScalarL2‖ ^ 2 := by
  simpa [H1Function.toScalarL2, Homogenization.toScalarL2] using
    (toReal_eLpNorm_two_sq_eq_integral_sq w.memL2).symm

private theorem setIntegral_gradCoord_sq_eq_norm_sq
    {U : Set (Vec d)} (w : H1Function U) (i : Fin d) :
    ∫ x in U, (w.grad x i) ^ 2 ∂MeasureTheory.volume =
      ‖w.gradCoordToScalarL2 i‖ ^ 2 := by
  simpa [H1Function.gradCoordToScalarL2, Homogenization.toScalarL2] using
    (toReal_eLpNorm_two_sq_eq_integral_sq (w.gradMemL2 i)).symm

private noncomputable def harmonicInteriorHessianEnergyCoreConstant (d : ℕ) : ℝ :=
  Real.sqrt
    ((13824 : ℝ) * (d : ℝ) * quantitativeCubeCutoffGradientConst d ^ 2 *
      (1 + (256 : ℝ) * (d : ℝ) * quantitativeCubeCutoffGradientConst d ^ 2 *
        (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue ^ 2))

private theorem openCubeInnerQuotientHessianSmoothTestReducedBound_le_harmonic_energy
    (Q : TriadicCube d) [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q))]
    (u : H1Function (openCubeSet Q)) (i : Fin d) :
    @WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestReducedBound
        d Q u.subAverage (fun _ => 0) i (1 / 2 : ℝ) (7 / 12 : ℝ)
        (3 / 4 : ℝ) (7 / 8 : ℝ)
        (outerThreeQuarterSevenEighthCutoff Q) ≤
      harmonicInteriorHessianEnergyCoreConstant d * (cubeScaleFactor Q)⁻¹ *
        u.gradientCoordL2NormSum := by
  let L : ℝ := cubeScaleFactor Q
  let K : ℝ := quantitativeCubeCutoffGradientConst d
  let C0 : ℝ := (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue
  let G : ℝ := u.gradientCoordL2NormSum
  let a : ℝ := ∫ x in openCubeSet Q, (u.subAverage.grad x i) ^ 2
    ∂MeasureTheory.volume
  let b : ℝ := ∫ x in openCubeSet Q, u.subAverage.toFun x ^ 2
    ∂MeasureTheory.volume
  have hLpos : 0 < L := by
    rw [show L = 2 * cubeRadius Q by simpa [L] using cubeScaleFactor_eq_two_mul_cubeRadius Q]
    exact mul_pos (by norm_num) (cubeRadius_pos Q)
  have hG_nonneg : 0 ≤ G := by
    exact u.gradientCoordL2NormSum_nonneg
  have hcoord_le : ‖u.subAverage.gradCoordToScalarL2 i‖ ≤ G := by
    calc
      ‖u.subAverage.gradCoordToScalarL2 i‖ ≤ u.subAverage.gradientCoordL2NormSum :=
        Finset.single_le_sum (fun j _hj => norm_nonneg _) (Finset.mem_univ i)
      _ = G := by simp [G]
  have ha_eq : a = ‖u.subAverage.gradCoordToScalarL2 i‖ ^ 2 := by
    simpa [a] using setIntegral_gradCoord_sq_eq_norm_sq u.subAverage i
  have ha_le : a ≤ G ^ 2 := by
    rw [ha_eq]
    exact (sq_le_sq₀ (norm_nonneg _) hG_nonneg).2 hcoord_le
  have hvalue_le : ‖u.subAverage.toScalarL2‖ ≤ L * C0 * G := by
    have hbase := (scaledTranslatedCubeMeanZeroH1CoerciveEstimate Q).bound_subAverage u
    have hgrad : ‖u.gradToVectorL2‖ ≤ G := by
      exact u.norm_gradToVectorL2_le_gradientCoordL2NormSum
    have hconst : (scaledTranslatedCubeMeanZeroH1CoerciveEstimate Q).fixedValue = L * C0 := by
      simpa [L, C0] using scaledTranslatedCubeMeanZeroH1CoerciveEstimate_constant Q
    change ‖u.subAverage.toScalarL2‖ ≤ L * C0 * G
    change ‖u.subAverage.toScalarL2‖ ≤
      (scaledTranslatedCubeMeanZeroH1CoerciveEstimate Q).fixedValue * ‖u.gradToVectorL2‖ at hbase
    rw [hconst] at hbase
    exact hbase.trans (mul_le_mul_of_nonneg_left hgrad (mul_nonneg hLpos.le
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg))
  have hb_eq : b = ‖u.subAverage.toScalarL2‖ ^ 2 := by
    simpa [b] using setIntegral_sq_eq_toScalarL2_norm_sq u.subAverage
  have hb_le : b ≤ (L * C0 * G) ^ 2 := by
    rw [hb_eq]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg hLpos.le
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg) hG_nonneg)).2 hvalue_le
  have hKinner :
      (3 : ℝ) * ((d : ℝ) * (K / (((7 / 12 : ℝ) - (1 / 2 : ℝ)) * cubeRadius Q)) ^ 2) =
        ((1728 : ℝ) * (d : ℝ) * K ^ 2) * L⁻¹ ^ 2 := by
    rw [show cubeRadius Q = L / 2 by
      dsimp [L]
      rw [cubeScaleFactor_eq_two_mul_cubeRadius]
      field_simp [cubeRadius_pos Q |>.ne']]
    field_simp [hLpos.ne']
    ring
  have hKouter :
      (d : ℝ) * (K / (((7 / 8 : ℝ) - (3 / 4 : ℝ)) * cubeRadius Q)) ^ 2 =
        ((256 : ℝ) * (d : ℝ) * K ^ 2) * L⁻¹ ^ 2 := by
    rw [show cubeRadius Q = L / 2 by
      dsimp [L]
      rw [cubeScaleFactor_eq_two_mul_cubeRadius]
      field_simp [cubeRadius_pos Q |>.ne']]
    field_simp [hLpos.ne']
    ring
  have hcore_nonneg : 0 ≤ harmonicInteriorHessianEnergyCoreConstant d := Real.sqrt_nonneg _
  rw [WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestReducedBound]
  have hzero :
      (2 : ℝ) * ∫ x in openCubeSet Q, (0 : ℝ) ^ 2 ∂MeasureTheory.volume = 0 := by
    norm_num
  rw [hzero, zero_add]
  change
    (4 *
      (3 * ((d : ℝ) *
        (K / (((7 / 12 : ℝ) - (1 / 2 : ℝ)) * cubeRadius Q)) ^ 2) *
        (2 * a + 2 *
          (((d : ℝ) *
            (K / (((7 / 8 : ℝ) - (3 / 4 : ℝ)) * cubeRadius Q)) ^ 2) * b)))) ^
      (1 / (2 : ℝ)) ≤
      harmonicInteriorHessianEnergyCoreConstant d * L⁻¹ * G
  rw [← Real.sqrt_eq_rpow]
  rw [hKinner, hKouter]
  apply (Real.sqrt_le_iff).2
  constructor
  · exact mul_nonneg (mul_nonneg hcore_nonneg (inv_nonneg.mpr hLpos.le)) hG_nonneg
  have htarget_nonneg : 0 ≤
      (13824 : ℝ) * (d : ℝ) * K ^ 2 *
        (1 + (256 : ℝ) * (d : ℝ) * K ^ 2 * C0 ^ 2) := by positivity
  have hinv_sq : L⁻¹ ^ 2 * L ^ 2 = 1 := by field_simp [hLpos.ne']
  have hcore_sq : harmonicInteriorHessianEnergyCoreConstant d ^ 2 =
      (13824 : ℝ) * (d : ℝ) * K ^ 2 *
        (1 + (256 : ℝ) * (d : ℝ) * K ^ 2 * C0 ^ 2) := by
    have hactual_nonneg : 0 ≤
        (13824 : ℝ) * (d : ℝ) * quantitativeCubeCutoffGradientConst d ^ 2 *
          (1 + (256 : ℝ) * (d : ℝ) * quantitativeCubeCutoffGradientConst d ^ 2 *
            (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue ^ 2) := by
      simpa [K, C0] using htarget_nonneg
    dsimp [harmonicInteriorHessianEnergyCoreConstant]
    rw [Real.sq_sqrt hactual_nonneg]
  have hX_nonneg : 0 ≤ (d : ℝ) * K ^ 2 :=
    mul_nonneg (Nat.cast_nonneg d) (sq_nonneg K)
  have hLinv_sq_nonneg : 0 ≤ L⁻¹ ^ 2 := sq_nonneg _
  have houter_nonneg : 0 ≤ (1728 : ℝ) * (d : ℝ) * K ^ 2 * L⁻¹ ^ 2 := by
    positivity
  have hinner :
      2 * a + 2 * (256 * (d : ℝ) * K ^ 2 * L⁻¹ ^ 2 * b) ≤
        2 * G ^ 2 + 2 * (256 * (d : ℝ) * K ^ 2 * L⁻¹ ^ 2 *
          (L * C0 * G) ^ 2) := by
    have hcoeff : 0 ≤ (256 : ℝ) * (d : ℝ) * K ^ 2 * L⁻¹ ^ 2 := by positivity
    exact add_le_add
      (mul_le_mul_of_nonneg_left ha_le (by norm_num))
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hb_le hcoeff) (by norm_num))
  calc
    4 * (1728 * (d : ℝ) * K ^ 2 * L⁻¹ ^ 2 *
        (2 * a + 2 * (256 * (d : ℝ) * K ^ 2 * L⁻¹ ^ 2 * b)))
        ≤ 4 * (1728 * (d : ℝ) * K ^ 2 * L⁻¹ ^ 2 *
          (2 * G ^ 2 + 2 * (256 * (d : ℝ) * K ^ 2 * L⁻¹ ^ 2 *
            (L * C0 * G) ^ 2))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hinner houter_nonneg) (by norm_num)
    _ ≤ (harmonicInteriorHessianEnergyCoreConstant d * L⁻¹ * G) ^ 2 := by
      have hcancel : L⁻¹ ^ 2 * (L * C0 * G) ^ 2 = C0 ^ 2 * G ^ 2 := by
        calc
          L⁻¹ ^ 2 * (L * C0 * G) ^ 2 =
              (L⁻¹ ^ 2 * L ^ 2) * (C0 ^ 2 * G ^ 2) := by ring
          _ = C0 ^ 2 * G ^ 2 := by rw [hinv_sq, one_mul]
      have hupper_eq :
          4 * (1728 * (d : ℝ) * K ^ 2 * L⁻¹ ^ 2 *
            (2 * G ^ 2 + 2 * (256 * (d : ℝ) * K ^ 2 * L⁻¹ ^ 2 *
              (L * C0 * G) ^ 2))) =
            (13824 : ℝ) * (d : ℝ) * K ^ 2 *
              (1 + (256 : ℝ) * (d : ℝ) * K ^ 2 * C0 ^ 2) * L⁻¹ ^ 2 * G ^ 2 := by
        calc
          4 * (1728 * (d : ℝ) * K ^ 2 * L⁻¹ ^ 2 *
              (2 * G ^ 2 + 2 * (256 * (d : ℝ) * K ^ 2 * L⁻¹ ^ 2 *
                (L * C0 * G) ^ 2))) =
              (13824 : ℝ) * (d : ℝ) * K ^ 2 * L⁻¹ ^ 2 * G ^ 2 +
                ((13824 : ℝ) * (d : ℝ) * K ^ 2 * L⁻¹ ^ 2) *
                  ((256 : ℝ) * (d : ℝ) * K ^ 2) *
                    (L⁻¹ ^ 2 * (L * C0 * G) ^ 2) := by ring
          _ = (13824 : ℝ) * (d : ℝ) * K ^ 2 *
              (1 + (256 : ℝ) * (d : ℝ) * K ^ 2 * C0 ^ 2) * L⁻¹ ^ 2 * G ^ 2 := by
                rw [hcancel]
                ring
      rw [hupper_eq]
      rw [show (harmonicInteriorHessianEnergyCoreConstant d * L⁻¹ * G) ^ 2 =
        harmonicInteriorHessianEnergyCoreConstant d ^ 2 * L⁻¹ ^ 2 * G ^ 2 by ring,
        hcore_sq]

/-- The fixed-radius construction can be run after mean-zero normalization
and then translated back to the original value representative on the inner
cube. -/
theorem exists_innerHalf_hasWeakHessianOn_harmonic_same_values
    {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}
    (h : WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0)) :
    ∃ uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)),
      uS.toFun = u.toFun ∧
        uS.grad = u.grad ∧
          Nonempty (HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS) := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let : MeasureTheory.IsFiniteMeasure
      (volumeMeasureOn (scaledOpenCubeSet Q (1 / 2 : ℝ))) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_scaledOpenCubeSet_of_pos Q
        (by norm_num : 0 < (1 / 2 : ℝ))).isFiniteMeasure_restrict_volume
  have hsub : WeakPoissonEquationOn (openCubeSet Q) u.subAverage (fun _ => 0) :=
    WeakPoissonEquationOn.subAverage h
  obtain ⟨v, hvfun, hvgrad, H, hH⟩ :=
    exists_innerHalf_hasWeakHessianOn_harmonic (Q := Q) hsub
  let c : ℝ := integralAverage (openCubeSet Q) u
  let uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)) := v.addConst c
  let HS : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS :=
    HasWeakHessianOn.addConst H c
  refine ⟨uS, ?_, ?_, ⟨HS⟩⟩
  · funext x
    have hx : v.toFun x = u.subAverage.toFun x := congrFun hvfun x
    simp only [uS, H1Function.addConst_apply, c, hx, H1Function.subAverage_apply]
    ring
  · funext x
    calc
      uS.grad x = v.grad x := H1Function.grad_addConst v c x
      _ = u.subAverage.grad x := congrFun hvgrad x
      _ = u.grad x := u.grad_subAverage x

/-- Dimension-only, scale-correct interior Hessian energy estimate for weakly
harmonic functions.  The construction is run on the mean-zero representative
to control the cutoff lower-order term, then its value carrier is translated
back by the original cube average. -/
theorem exists_harmonic_innerHalf_hessian_energy_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : TriadicCube d) (u : H1Function (openCubeSet Q)),
        WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0) →
          ∃ uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)),
            uS.toFun = u.toFun ∧
              uS.grad = u.grad ∧
                ∃ H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS,
                  H.hessianCoordL2NormSum ≤
                    C * (cubeScaleFactor Q)⁻¹ * u.gradientCoordL2NormSum := by
  let C : ℝ := 1 + (d : ℝ) ^ 2 * harmonicInteriorHessianEnergyCoreConstant d
  refine ⟨C, ?_, ?_⟩
  · dsimp [C, harmonicInteriorHessianEnergyCoreConstant]
    nlinarith [sq_nonneg (d : ℝ), Real.sqrt_nonneg
      ((13824 : ℝ) * (d : ℝ) * quantitativeCubeCutoffGradientConst d ^ 2 *
        (1 + (256 : ℝ) * (d : ℝ) * quantitativeCubeCutoffGradientConst d ^ 2 *
          (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue ^ 2))]
  intro Q u h
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let : MeasureTheory.IsFiniteMeasure
      (volumeMeasureOn (scaledOpenCubeSet Q (1 / 2 : ℝ))) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_scaledOpenCubeSet_of_pos Q
        (by norm_num : 0 < (1 / 2 : ℝ))).isFiniteMeasure_restrict_volume
  have hsub : WeakPoissonEquationOn (openCubeSet Q) u.subAverage (fun _ => 0) :=
    WeakPoissonEquationOn.subAverage h
  obtain ⟨v, hvfun, hvgrad, H, hH⟩ :=
    exists_innerHalf_hasWeakHessianOn_harmonic (Q := Q) hsub
  let c : ℝ := integralAverage (openCubeSet Q) u
  let uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)) := v.addConst c
  let HS : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS :=
    HasWeakHessianOn.addConst H c
  refine ⟨uS, ?_, ?_, HS, ?_⟩
  · funext x
    have hx : v.toFun x = u.subAverage.toFun x := congrFun hvfun x
    simp only [uS, H1Function.addConst_apply, c, hx, H1Function.subAverage_apply]
    ring
  · funext x
    calc
      uS.grad x = v.grad x := H1Function.grad_addConst v c x
      _ = u.subAverage.grad x := congrFun hvgrad x
      _ = u.grad x := u.grad_subAverage x
  have hHred : H.hessianCoordL2NormSum ≤
      ∑ i : Fin d, ∑ _j : Fin d,
        @WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestReducedBound
          d Q u.subAverage (fun _ => 0) i (1 / 2 : ℝ) (7 / 12 : ℝ)
          (3 / 4 : ℝ) (7 / 8 : ℝ)
          (outerThreeQuarterSevenEighthCutoff Q) := by
    refine hH.trans ?_
    exact Finset.sum_le_sum fun i _hi =>
      Finset.sum_le_sum fun _j _hj =>
        WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestBound_le_reducedBound
          u.subAverage (fun _ => 0) i (outerThreeQuarterSevenEighthCutoff Q)
  have hsum :
      (∑ i : Fin d, ∑ _j : Fin d,
        @WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestReducedBound
          d Q u.subAverage (fun _ => 0) i (1 / 2 : ℝ) (7 / 12 : ℝ)
          (3 / 4 : ℝ) (7 / 8 : ℝ)
          (outerThreeQuarterSevenEighthCutoff Q)) ≤
        (d : ℝ) ^ 2 * harmonicInteriorHessianEnergyCoreConstant d *
          (cubeScaleFactor Q)⁻¹ * u.gradientCoordL2NormSum := by
    calc
      (∑ i : Fin d, ∑ _j : Fin d,
          @WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestReducedBound
            d Q u.subAverage (fun _ => 0) i (1 / 2 : ℝ) (7 / 12 : ℝ)
            (3 / 4 : ℝ) (7 / 8 : ℝ)
            (outerThreeQuarterSevenEighthCutoff Q)) ≤
          ∑ _i : Fin d, ∑ _j : Fin d,
            harmonicInteriorHessianEnergyCoreConstant d * (cubeScaleFactor Q)⁻¹ *
              u.gradientCoordL2NormSum := by
            exact Finset.sum_le_sum fun i _hi =>
              Finset.sum_le_sum fun _j _hj =>
                openCubeInnerQuotientHessianSmoothTestReducedBound_le_harmonic_energy Q u i
      _ = (d : ℝ) ^ 2 * harmonicInteriorHessianEnergyCoreConstant d *
          (cubeScaleFactor Q)⁻¹ * u.gradientCoordL2NormSum := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
  have hscale_nonneg : 0 ≤ (cubeScaleFactor Q)⁻¹ * u.gradientCoordL2NormSum := by
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt (by
      rw [cubeScaleFactor_eq_two_mul_cubeRadius Q]
      exact mul_pos (by norm_num) (cubeRadius_pos Q)))) u.gradientCoordL2NormSum_nonneg
  have hconst_le : (d : ℝ) ^ 2 * harmonicInteriorHessianEnergyCoreConstant d ≤ C := by
    dsimp [C]
    linarith [sq_nonneg (d : ℝ), Real.sqrt_nonneg
      ((13824 : ℝ) * (d : ℝ) * quantitativeCubeCutoffGradientConst d ^ 2 *
        (1 + (256 : ℝ) * (d : ℝ) * quantitativeCubeCutoffGradientConst d ^ 2 *
          (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue ^ 2))]
  change HS.hessianCoordL2NormSum ≤ C * (cubeScaleFactor Q)⁻¹ * u.gradientCoordL2NormSum
  calc
    HS.hessianCoordL2NormSum = H.hessianCoordL2NormSum := rfl
    _ ≤ (d : ℝ) ^ 2 * harmonicInteriorHessianEnergyCoreConstant d *
        (cubeScaleFactor Q)⁻¹ * u.gradientCoordL2NormSum := hHred.trans hsum
    _ = ((d : ℝ) ^ 2 * harmonicInteriorHessianEnergyCoreConstant d) *
        ((cubeScaleFactor Q)⁻¹ * u.gradientCoordL2NormSum) := by ring
    _ ≤ C * ((cubeScaleFactor Q)⁻¹ * u.gradientCoordL2NormSum) :=
      mul_le_mul_of_nonneg_right hconst_le hscale_nonneg
    _ = C * (cubeScaleFactor Q)⁻¹ * u.gradientCoordL2NormSum := by ring

end CubeCalderonZygmund

end

end Homogenization
