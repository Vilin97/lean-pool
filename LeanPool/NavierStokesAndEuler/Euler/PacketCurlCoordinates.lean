/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPotentialRegularity
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangularRegularity

@[expose] public section

/-! Coordinate realization of the actual slow curl and its bounded coefficients. -/

noncomputable section

namespace EulerPacketPiola

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerLiftedGradientSpace
  EulerMeanBoundary EulerPacketCrossProduct EulerCylinderSobolev EulerMeanCoefficients
open scoped BoundedContinuousFunction ContDiff

private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance

/-- The coefficient of one genuine spatial derivative in the slow curl. -/
def curlCoefficient (i : Fin 3) : (Space →L[ℝ] Space) →L[ℝ] (Space →L[ℝ] Space) :=
  crossOperator.comp ((ContinuousLinearMap.apply ℝ Space (EuclideanSpace.single i 1)).comp
    (ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
      : (Space →L[ℝ] Space) →L[ℝ] (Space →L[ℝ] Space)))

@[simp] theorem curlCoefficient_apply (i : Fin 3) (G : Space →L[ℝ] Space) :
    curlCoefficient i G = crossLeft (G.adjoint (EuclideanSpace.single i 1)) := rfl

theorem curlCoefficient_norm (i : Fin 3) : ‖curlCoefficient i‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro G
  rw [curlCoefficient_apply, one_mul]
  calc
    ‖crossLeft (G.adjoint (EuclideanSpace.single i 1))‖ ≤
        ‖G.adjoint (EuclideanSpace.single i 1)‖ := crossLeft_norm_le _
    _ ≤ ‖G.adjoint‖*‖EuclideanSpace.single i (1 : ℝ)‖ := G.adjoint.le_opNorm _
    _ = ‖G‖ := by simp only [PiLp.norm_single, norm_one, mul_one, LinearIsometryEquiv.norm_map]

theorem slowDerivative_coordinates (D : LiftTangent →L[ℝ] Space) (G : Space →L[ℝ] Space) :
    D.comp ((ContinuousLinearMap.inl ℝ Space ℝ).comp G) =
      ∑ i : Fin 3, rankOne ℝ (D (standardDirection i.succ))
        (G.adjoint (EuclideanSpace.single i 1)) := by
  have he (v : Space) :
      (∑ i : Fin 3, ⟪G.adjoint (EuclideanSpace.single i 1),v⟫_ℝ •
        standardDirection i.succ) = (G v,0) := by
    simp_rw [G.adjoint_inner_left, standardDirection_succ]
    apply Prod.ext
    · change (∑ i : Fin 3, ⟪EuclideanSpace.single i 1,G v⟫_ℝ • EuclideanSpace.single i 1) = G v
      ext j
      simp [EuclideanSpace.inner_single_left, Pi.single_apply]
    · simp [Fin.sum_univ_succ]
  apply ContinuousLinearMap.ext
  intro v
  change D (G v,0) = ∑ i : Fin 3, ⟪G.adjoint (EuclideanSpace.single i 1),v⟫_ℝ •
    D (standardDirection i.succ)
  rw [← he v, map_sum]
  simp only [map_smul]

/-- The literal slow curl is a sum of three rectangular coefficient products. -/
theorem curlMatrix_coordinates (D : LiftTangent →L[ℝ] Space) (G : Space →L[ℝ] Space) :
    curlMatrix (D.comp ((ContinuousLinearMap.inl ℝ Space ℝ).comp G)) =
      ∑ i : Fin 3, curlCoefficient i G (D (standardDirection i.succ)) := by
  rw [slowDerivative_coordinates]
  change curlOperator (∑ i : Fin 3, rankOne ℝ (D (standardDirection i.succ))
    (G.adjoint (EuclideanSpace.single i 1))) = _
  rw [map_sum]
  simp only [curlOperator_apply, curlMatrix_rankOne, curlCoefficient_apply, crossLeft_apply]

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

private local instance : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) := inferInstance

def curlCoefficientPath (i : Fin 3) :
    C(K,Space →ᵇ Space →L[ℝ] Space) →L[ℝ] C(K,Space →ᵇ Space →L[ℝ] Space) :=
  ((curlCoefficient i).compLeftContinuousBounded Space).compLeftContinuous ℝ K

omit [CompactSpace K] in
@[simp] theorem curlCoefficientPath_apply (i : Fin 3)
    (G : C(K,Space →ᵇ Space →L[ℝ] Space)) (t : K) (y : Space) :
    curlCoefficientPath i G t y = curlCoefficient i (G t y) := rfl

theorem curlCoefficientPath_norm (i : Fin 3) : ‖curlCoefficientPath (K := K) i‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro G
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg G)).mpr
  intro t
  apply (BoundedContinuousFunction.norm_le (norm_nonneg G)).mpr
  intro y
  change ‖curlCoefficient i (G t y)‖ ≤ ‖G‖
  exact ((curlCoefficient i).le_of_opNorm_le (curlCoefficient_norm i) (G t y)).trans
    (by simpa only [one_mul] using ((G t).norm_coe_le_norm y).trans (G.norm_coe_le_norm t))

omit [CompactSpace K] in
theorem curlCoefficientPath_translation (i : Fin 3)
    (G : C(K,Space →ᵇ Space →L[ℝ] Space)) (a : Space) :
    translateCoefficientPath (curlCoefficientPath i G) a =
      curlCoefficientPath i (translateCoefficientPath G a) := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro y
  rfl

theorem curlCoefficientPath_orbit (i : Fin 3) (G : C(K,Space →ᵇ Space →L[ℝ] Space))
    (hG : ContDiff ℝ ∞ (translateCoefficientPath G)) :
    ContDiff ℝ ∞ (translateCoefficientPath (curlCoefficientPath i G)) := by
  have he : translateCoefficientPath (curlCoefficientPath i G) =
      fun a => curlCoefficientPath i (translateCoefficientPath G a) :=
    funext (curlCoefficientPath_translation i G)
  rw [he]
  exact (curlCoefficientPath i).contDiff.comp hG

theorem curlCoefficientPath_bound (i : Fin 3) (G : C(K,Space →ᵇ Space →L[ℝ] Space))
    (hG : ContDiff ℝ ∞ (translateCoefficientPath G)) (n : ℕ) (C : ℝ)
    (hb : ∀ a, ‖iteratedFDeriv ℝ n (translateCoefficientPath G) a‖ ≤ C) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (curlCoefficientPath i G)) a‖ ≤ C := by
  have he : translateCoefficientPath (curlCoefficientPath i G) =
      fun a => curlCoefficientPath i (translateCoefficientPath G a) :=
    funext (curlCoefficientPath_translation i G)
  rw [he]
  have h := (curlCoefficientPath (K := K) i).norm_iteratedFDeriv_comp_left
    (hG.contDiffAt (x := a)) (n := n) (by simp)
  exact h.trans ((mul_le_mul_of_nonneg_right (curlCoefficientPath_norm i) (norm_nonneg _)).trans
    (by simpa only [one_mul] using hb a))

end EulerPacketPiola
