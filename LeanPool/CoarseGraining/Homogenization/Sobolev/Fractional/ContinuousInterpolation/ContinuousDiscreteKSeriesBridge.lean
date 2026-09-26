/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.DiscreteKOverlapEnergy
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.TriadicSeries

/-!
# Triadic continuous/discrete K-series bridge

This module compares the canonical continuous triadic K-sample energy with
the extended internal discrete K-functional energy.
-/

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal

noncomputable section

private theorem triadicContinuousKScale_eq_rpow (j : ℕ) :
    (triadicContinuousKScale j).1 = Real.rpow 3 (-(j : ℝ)) := by
  change ((3 : ℝ)⁻¹) ^ j = Real.rpow 3 (-(j : ℝ))
  rw [← Real.rpow_natCast, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 3)]
  symm
  exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3) _

private theorem triadicContinuousKSample_weight_eq_depth_weight_sq
    (s : FractionalOrder) (j : ℕ) :
    Real.rpow (triadicContinuousKScale j).1 (-2 * s.1) =
      (Real.rpow 3 (s.1 * (j : ℝ))) ^ 2 := by
  rw [triadicContinuousKScale_eq_rpow]
  calc
    Real.rpow (Real.rpow 3 (-(j : ℝ))) (-2 * s.1) =
        Real.rpow 3 ((-(j : ℝ)) * (-2 * s.1)) :=
      (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _).symm
    _ = Real.rpow 3 ((s.1 * (j : ℝ)) * 2) := by
      congr 1
      ring
    _ = Real.rpow (Real.rpow 3 (s.1 * (j : ℝ))) (2 : ℝ) :=
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _
    _ = (Real.rpow 3 (s.1 * (j : ℝ))) ^ 2 :=
      Real.rpow_natCast _ 2

/-- The squared continuous/discrete bridge factor is finite as an extended
nonnegative real. -/
theorem ofReal_sq_continuousDiscreteKBridgeConstant_ne_top (d : ℕ) :
    ENNReal.ofReal (continuousDiscreteKBridgeConstant d ^ 2) ≠ ∞ :=
  ENNReal.ofReal_ne_top

private theorem triadicContinuousKSampleTerm_le_mul_discreteDepthTerm
    {d : ℕ} (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (j : ℕ) :
    triadicContinuousKSampleTerm s F j ≤
      ENNReal.ofReal (continuousDiscreteKBridgeConstant d ^ 2) *
        ENNReal.ofReal
          ((cubeKBesovVectorDepthSeminorm (originCube d 0) s.1 F j) ^ 2) := by
  let C : ℝ := continuousDiscreteKBridgeConstant d
  let W : ℝ := Real.rpow 3 (s.1 * (j : ℝ))
  let Kc : ℝ := continuousKFunctional (triadicContinuousKScale j) F
  let Kd : ℝ := cubeVectorKFunctional (originCube d 0)
    (Real.rpow 3 (-(j : ℝ))) F
  have hC : 0 ≤ C := continuousDiscreteKBridgeConstant_nonneg d
  have hKc : 0 ≤ Kc := continuousKFunctional_nonneg _ F
  have hKd : 0 ≤ Kd := cubeVectorKFunctional_nonneg _ _ _
  have hK : Kc ≤ C * Kd := by
    simpa only [C, Kc, Kd, triadicContinuousKScale_eq_rpow] using
      continuousKFunctional_le_mul_cubeVectorKFunctional
        (triadicContinuousKScale j) F
  have hreal : W ^ 2 * Kc ^ 2 ≤ C ^ 2 * (W * Kd) ^ 2 := by
    have hsquare : Kc ^ 2 ≤ C ^ 2 * Kd ^ 2 := by
      calc
        Kc ^ 2 ≤ (C * Kd) ^ 2 :=
          (sq_le_sq₀ hKc (mul_nonneg hC hKd)).mpr hK
        _ = C ^ 2 * Kd ^ 2 := by ring
    calc
      W ^ 2 * Kc ^ 2 ≤ W ^ 2 * (C ^ 2 * Kd ^ 2) :=
        mul_le_mul_of_nonneg_left hsquare (sq_nonneg W)
      _ = C ^ 2 * (W * Kd) ^ 2 := by ring
  unfold triadicContinuousKSampleTerm cubeKBesovVectorDepthSeminorm
  rw [triadicContinuousKSample_weight_eq_depth_weight_sq]
  change ENNReal.ofReal (W ^ 2) * ENNReal.ofReal (Kc ^ 2) ≤
    ENNReal.ofReal (C ^ 2) * ENNReal.ofReal ((W * Kd) ^ 2)
  rw [← ENNReal.ofReal_mul (sq_nonneg W)]
  rw [← ENNReal.ofReal_mul (sq_nonneg C)]
  exact ENNReal.ofReal_le_ofReal hreal

private theorem discreteDepthTerm_le_mul_triadicContinuousKSampleTerm
    {d : ℕ} (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (j : ℕ) :
    ENNReal.ofReal
        ((cubeKBesovVectorDepthSeminorm (originCube d 0) s.1 F j) ^ 2) ≤
      ENNReal.ofReal (continuousDiscreteKBridgeConstant d ^ 2) *
        triadicContinuousKSampleTerm s F j := by
  let C : ℝ := continuousDiscreteKBridgeConstant d
  let W : ℝ := Real.rpow 3 (s.1 * (j : ℝ))
  let Kc : ℝ := continuousKFunctional (triadicContinuousKScale j) F
  let Kd : ℝ := cubeVectorKFunctional (originCube d 0)
    (Real.rpow 3 (-(j : ℝ))) F
  have hC : 0 ≤ C := continuousDiscreteKBridgeConstant_nonneg d
  have hKc : 0 ≤ Kc := continuousKFunctional_nonneg _ F
  have hKd : 0 ≤ Kd := cubeVectorKFunctional_nonneg _ _ _
  have hK : Kd ≤ C * Kc := by
    simpa only [C, Kc, Kd, triadicContinuousKScale_eq_rpow] using
      cubeVectorKFunctional_le_mul_continuousKFunctional
        (triadicContinuousKScale j) F
  have hreal : (W * Kd) ^ 2 ≤ C ^ 2 * (W ^ 2 * Kc ^ 2) := by
    have hsquare : Kd ^ 2 ≤ C ^ 2 * Kc ^ 2 := by
      calc
        Kd ^ 2 ≤ (C * Kc) ^ 2 :=
          (sq_le_sq₀ hKd (mul_nonneg hC hKc)).mpr hK
        _ = C ^ 2 * Kc ^ 2 := by ring
    calc
      (W * Kd) ^ 2 = W ^ 2 * Kd ^ 2 := by ring
      _ ≤ W ^ 2 * (C ^ 2 * Kc ^ 2) :=
        mul_le_mul_of_nonneg_left hsquare (sq_nonneg W)
      _ = C ^ 2 * (W ^ 2 * Kc ^ 2) := by ring
  unfold triadicContinuousKSampleTerm cubeKBesovVectorDepthSeminorm
  rw [triadicContinuousKSample_weight_eq_depth_weight_sq]
  change ENNReal.ofReal ((W * Kd) ^ 2) ≤
    ENNReal.ofReal (C ^ 2) * (ENNReal.ofReal (W ^ 2) * ENNReal.ofReal (Kc ^ 2))
  rw [← ENNReal.ofReal_mul (sq_nonneg W)]
  rw [← ENNReal.ofReal_mul (sq_nonneg C)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The squared discrete partial seminorm is exactly its finite `ENNReal`
sum of depth energies. -/
theorem ofReal_sq_cubeKPartialSeminorm_eq_sum_depthTerms
    {d : ℕ} (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (N : ℕ) :
    ENNReal.ofReal
        ((cubeKBesovVectorPartialSeminormTwo (originCube d 0) s.1 N F) ^ 2) =
      ∑ j ∈ Finset.range (N + 1), ENNReal.ofReal
        ((cubeKBesovVectorDepthSeminorm (originCube d 0) s.1 F j) ^ 2) := by
  rw [sq_cubeKBesovVectorPartialSeminormTwo]
  exact ENNReal.ofReal_sum_of_nonneg fun j _ => sq_nonneg _

private theorem finite_triadicContinuousKSampleSum_le_mul_cubeKPartial
    {d : ℕ} (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), triadicContinuousKSampleTerm s F j) ≤
      ENNReal.ofReal (continuousDiscreteKBridgeConstant d ^ 2) *
        ENNReal.ofReal
          ((cubeKBesovVectorPartialSeminormTwo (originCube d 0) s.1 N F) ^ 2) := by
  calc
    (∑ j ∈ Finset.range (N + 1), triadicContinuousKSampleTerm s F j)
        ≤ ∑ j ∈ Finset.range (N + 1),
          ENNReal.ofReal (continuousDiscreteKBridgeConstant d ^ 2) *
            ENNReal.ofReal
              ((cubeKBesovVectorDepthSeminorm (originCube d 0) s.1 F j) ^ 2) := by
            apply Finset.sum_le_sum
            intro j hj
            exact triadicContinuousKSampleTerm_le_mul_discreteDepthTerm s F j
    _ = ENNReal.ofReal (continuousDiscreteKBridgeConstant d ^ 2) *
        (∑ j ∈ Finset.range (N + 1), ENNReal.ofReal
          ((cubeKBesovVectorDepthSeminorm (originCube d 0) s.1 F j) ^ 2)) := by
            rw [Finset.mul_sum]
    _ = _ := by rw [← ofReal_sq_cubeKPartialSeminorm_eq_sum_depthTerms]

private theorem cubeKPartial_le_mul_finite_triadicContinuousKSampleSum
    {d : ℕ} (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (N : ℕ) :
    ENNReal.ofReal
        ((cubeKBesovVectorPartialSeminormTwo (originCube d 0) s.1 N F) ^ 2) ≤
      ENNReal.ofReal (continuousDiscreteKBridgeConstant d ^ 2) *
        (∑ j ∈ Finset.range (N + 1), triadicContinuousKSampleTerm s F j) := by
  rw [ofReal_sq_cubeKPartialSeminorm_eq_sum_depthTerms]
  calc
    (∑ j ∈ Finset.range (N + 1), ENNReal.ofReal
        ((cubeKBesovVectorDepthSeminorm (originCube d 0) s.1 F j) ^ 2))
        ≤ ∑ j ∈ Finset.range (N + 1),
          ENNReal.ofReal (continuousDiscreteKBridgeConstant d ^ 2) *
            triadicContinuousKSampleTerm s F j := by
            apply Finset.sum_le_sum
            intro j hj
            exact discreteDepthTerm_le_mul_triadicContinuousKSampleTerm s F j
    _ = ENNReal.ofReal (continuousDiscreteKBridgeConstant d ^ 2) *
        (∑ j ∈ Finset.range (N + 1), triadicContinuousKSampleTerm s F j) := by
            rw [Finset.mul_sum]

/-- The canonical continuous triadic sample energy is bounded by the extended
internal discrete K-functional energy, with the squared bridge constant. -/
theorem triadicContinuousKSampleEnergy_le_mul_extendedDiscreteKFunctionalEnergy
    {d : ℕ} (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    triadicContinuousKSampleEnergy s F ≤
      ENNReal.ofReal (continuousDiscreteKBridgeConstant d ^ 2) *
        extendedDiscreteKFunctionalEnergy s F := by
  rw [triadicContinuousKSampleEnergy,
    ENNReal.tsum_eq_iSup_nat' (Filter.tendsto_add_atTop_nat 1)]
  refine iSup_le fun N => ?_
  calc
    (∑ j ∈ Finset.range (N + 1), triadicContinuousKSampleTerm s F j)
        ≤ ENNReal.ofReal (continuousDiscreteKBridgeConstant d ^ 2) *
          ENNReal.ofReal
            ((cubeKBesovVectorPartialSeminormTwo (originCube d 0) s.1 N F) ^ 2) :=
      finite_triadicContinuousKSampleSum_le_mul_cubeKPartial s F N
    _ ≤ ENNReal.ofReal (continuousDiscreteKBridgeConstant d ^ 2) *
        extendedDiscreteKFunctionalEnergy s F :=
      mul_le_mul_right
        (ofReal_sq_cubeKPartialSeminorm_le_extendedDiscreteKFunctionalEnergy s F N) _

/-- The extended internal discrete K-functional energy is bounded by the
canonical continuous triadic sample energy, with the same squared constant. -/
theorem extendedDiscreteKFunctionalEnergy_le_mul_triadicContinuousKSampleEnergy
    {d : ℕ} (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    extendedDiscreteKFunctionalEnergy s F ≤
      ENNReal.ofReal (continuousDiscreteKBridgeConstant d ^ 2) *
        triadicContinuousKSampleEnergy s F := by
  refine iSup_le fun N => ?_
  calc
    ENNReal.ofReal
        ((cubeKBesovVectorPartialSeminormTwo (originCube d 0) s.1 N F) ^ 2)
        ≤ ENNReal.ofReal (continuousDiscreteKBridgeConstant d ^ 2) *
          (∑ j ∈ Finset.range (N + 1), triadicContinuousKSampleTerm s F j) :=
      cubeKPartial_le_mul_finite_triadicContinuousKSampleSum s F N
    _ ≤ ENNReal.ofReal (continuousDiscreteKBridgeConstant d ^ 2) *
        triadicContinuousKSampleEnergy s F :=
      mul_le_mul_right (ENNReal.sum_le_tsum _) _

/-- Finiteness of the extended discrete energy transfers to the continuous
triadic sampled energy. -/
theorem triadicContinuousKSampleEnergy_ne_top_of_extendedDiscreteKFunctionalEnergy_ne_top
    {d : ℕ} (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d)
    (hF : extendedDiscreteKFunctionalEnergy s F ≠ ∞) :
    triadicContinuousKSampleEnergy s F ≠ ∞ := by
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF)
    (triadicContinuousKSampleEnergy_le_mul_extendedDiscreteKFunctionalEnergy s F)

/-- Finiteness of the continuous triadic sampled energy transfers to the
extended discrete K-functional energy. -/
theorem extendedDiscreteKFunctionalEnergy_ne_top_of_triadicContinuousKSampleEnergy_ne_top
    {d : ℕ} (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d)
    (hF : triadicContinuousKSampleEnergy s F ≠ ∞) :
    extendedDiscreteKFunctionalEnergy s F ≠ ∞ := by
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF)
    (extendedDiscreteKFunctionalEnergy_le_mul_triadicContinuousKSampleEnergy s F)

/-- Discarding the endpoint sample cannot increase the nonnegative triadic
sample energy. -/
theorem triadicContinuousKShiftedSampleEnergy_le_triadicContinuousKSampleEnergy
    {d : ℕ} (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    triadicContinuousKShiftedSampleEnergy s F ≤ triadicContinuousKSampleEnergy s F := by
  unfold triadicContinuousKShiftedSampleEnergy triadicContinuousKSampleEnergy
  exact ENNReal.tsum_comp_le_tsum_of_injective Nat.succ_injective _

end

end Homogenization
