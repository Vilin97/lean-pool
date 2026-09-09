/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets
public import LeanPool.NavierStokesAndEuler.Euler.TransverseSourceFrame
public import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus

@[expose] public section

/-!
# Actual source coefficient paths for the transverse inverse

Evaluation of the uniformly smooth spatial coefficient path gives a genuine
smooth map from position to time paths. Restriction to the fixed orthonormal
reference plane is a linear contraction. The pointwise source derivative
bounds therefore imply exactly the time-path coefficient bounds required by
the constructed transverse inverse.
-/

noncomputable section

open scoped ContDiff BoundedContinuousFunction


namespace EulerTransverseSourceCoefficientPath

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerTransverseFrameCoordinates EulerTransverseSourceFrame
  EulerOperatorGevreyCalculus EulerGevrey

section Evaluation

variable {K V : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private local instance : NormedAddCommGroup (Space →ᵇ V) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ V) := inferInstance

/-- Actual spatial evaluation, performed uniformly along the time path. -/
def pathEvaluation (x : Space) : C(K,Space →ᵇ V) →L[ℝ] C(K,V) :=
  (BoundedContinuousFunction.evalCLM ℝ x).compLeftContinuous ℝ K

/-- Evaluation is a contraction in the genuine uniform path norm. -/
theorem pathEvaluation_norm (x : Space) : ‖pathEvaluation (K := K) (V := V) x‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).2
  intro t
  exact ((A t).norm_coe_le_norm x).trans (A.norm_coe_le_norm t)

/-- The source coefficient viewed as a time path at a spatial position. -/
def pointPath (A : SmoothCoefficientPath K V) (x : Space) : C(K,V) :=
  pathEvaluation 0 (translateCoefficientPath A.field x)

/-- The coefficient path has the literal prescribed pointwise values. -/
theorem pointPath_apply (A : SmoothCoefficientPath K V) (x : Space) (t : K) :
    pointPath A x t = A.field t x := by
  change A.field t (0+x) = A.field t x
  rw [zero_add]

/-- Genuine smooth position dependence, in the uniform time-path norm. -/
theorem pointPath_contDiff (A : SmoothCoefficientPath K V) : ContDiff ℝ ∞ (pointPath A) := by
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(K,Space →ᵇ V)) (F := C(K,V)) (pathEvaluation 0)).comp A.translation_contDiff

/-- Source pointwise derivative bounds give actual operator-norm derivatives of the time path. -/
theorem pointPath_derivative_bound (A : SmoothCoefficientPath K V)
    (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t x, ‖iteratedFDeriv ℝ n (A.field t : Space → V) x‖ ≤ C) (x : Space) :
    ‖iteratedFDeriv ℝ n (pointPath A) x‖ ≤ C := by
  have h := (pathEvaluation (K := K) (V := V) 0).norm_iteratedFDeriv_comp_left
    (A.translation_contDiff.contDiffAt (x := x)) (n := n) (by simp)
  exact h.trans ((mul_le_mul_of_nonneg_right (pathEvaluation_norm (K := K) (V := V) 0)
    (norm_nonneg _)).trans (by simpa only [one_mul] using A.norm_iteratedFDeriv_translation_le n C
      hC hb x))

/-- Every prescribed factorial coefficient bound survives the time-path construction. -/
theorem pointPath_gevrey (A : SmoothCoefficientPath K V)
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (d : ℕ)
    (hb : ∀ n t x, ‖iteratedFDeriv ℝ n (A.field t : Space → V) x‖ ≤ C*majorant Rc d n)
    (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (pointPath A) x‖ ≤ C*majorant Rc d n :=
  pointPath_derivative_bound A n _ (mul_nonneg hC (majorant_nonneg Rc hRc d n)) (hb n) x

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Independent angle variables can be added by a fixed spatial projection. -/
theorem pointPath_pullback_contDiff (L : P →L[ℝ] Space) (A : SmoothCoefficientPath K V) :
    ContDiff ℝ ∞ (fun x => pointPath A (L x)) :=
  (pointPath_contDiff A).comp L.contDiff

/-- A spatial projection of norm at most one preserves the literal source derivative bounds. -/
theorem pointPath_pullback_derivative_bound (L : P →L[ℝ] Space) (hL : ‖L‖ ≤ 1)
    (A : SmoothCoefficientPath K V) (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t x, ‖iteratedFDeriv ℝ n (A.field t : Space → V) x‖ ≤ C) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => pointPath A (L y)) x‖ ≤ C := by
  change ‖iteratedFDeriv ℝ n ((pointPath A) ∘ L) x‖ ≤ C
  rw [L.iteratedFDeriv_comp_right (pointPath_contDiff A) x (by simp)]
  have h := (iteratedFDeriv ℝ n (pointPath A) (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  exact h.trans ((mul_le_mul (pointPath_derivative_bound A n C hC hb (L x))
    (pow_le_one₀ (norm_nonneg L) hL) (pow_nonneg (norm_nonneg L) n) hC).trans_eq (mul_one C))

/-- Joint spatial/angle coefficient bounds follow from the source spatial bounds. -/
theorem pointPath_pullback_gevrey (L : P →L[ℝ] Space) (hL : ‖L‖ ≤ 1)
    (A : SmoothCoefficientPath K V)
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (d : ℕ)
    (hb : ∀ n t x, ‖iteratedFDeriv ℝ n (A.field t : Space → V) x‖ ≤ C*majorant Rc d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => pointPath A (L y)) x‖ ≤ C*majorant Rc d n :=
  pointPath_pullback_derivative_bound L hL A n _
    (mul_nonneg hC (majorant_nonneg Rc hRc d n)) (hb n) x

end Evaluation

section Frame

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

private local instance : NormedAddCommGroup (U →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (U →L[ℝ] Space) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,U →L[ℝ] Space) := inferInstance
private local instance (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,U →L[ℝ] Space) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,Space →L[ℝ] Space) :=
  inferInstance
private local instance (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,Space →L[ℝ] Space) := inferInstance

variable (m₀ : Space) (Rperp : U ≃ₗᵢ[ℝ] referencePlane m₀)

/-- The fixed orthonormal reference embedding is a contraction, including a trivial plane. -/
theorem referenceEmbedding_norm : ‖referenceEmbedding m₀ Rperp‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  change ‖Rperp v‖ ≤ 1*‖v‖
  rw [one_mul, Rperp.norm_map]

/-- Restrict an actual coefficient operator to the reference plane. -/
def referenceRestriction : (Space →L[ℝ] Space) →L[ℝ] (U →L[ℝ] Space) :=
  (compL ℝ U Space Space).flip (referenceEmbedding m₀ Rperp)

/-- The time-path reference restriction is a genuine bounded linear map. -/
def framePathMap (T : ℝ) : C(Icc (0 : ℝ) T,Space →L[ℝ] Space) →L[ℝ]
    C(Icc (0 : ℝ) T,U →L[ℝ] Space) :=
  (referenceRestriction m₀ Rperp).compLeftContinuous ℝ (Icc (0 : ℝ) T)

/-- This restriction is exactly the source frame path `F Rperp`. -/
theorem framePathMap_apply (T : ℝ) (A : C(Icc (0 : ℝ) T,Space →L[ℝ] Space)) :
    framePathMap m₀ Rperp T A = framePath m₀ Rperp T A := rfl

/-- Orthogonal reference restriction does not enlarge the coefficient path norm. -/
theorem framePathMap_norm (T : ℝ) : ‖framePathMap m₀ Rperp T‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).2
  intro t
  calc
    ‖framePathMap m₀ Rperp T A t‖ ≤ ‖A t‖ * ‖referenceEmbedding m₀ Rperp‖ := opNorm_comp_le _ _
    _ ≤ ‖A t‖ * 1 := mul_le_mul_of_nonneg_left (referenceEmbedding_norm m₀ Rperp) (norm_nonneg _)
    _ ≤ ‖A‖ := by simpa only [mul_one] using A.norm_coe_le_norm t

/-- The actual source frame depends smoothly on position in time-path operator norm. -/
theorem sourceFrame_contDiff (T : ℝ)
    (A : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)) :
    ContDiff ℝ ∞ (fun x => framePath m₀ Rperp T (pointPath A x)) := by
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(Icc (0 : ℝ) T,Space →L[ℝ] Space))
    (F := C(Icc (0 : ℝ) T,U →L[ℝ] Space)) (framePathMap m₀ Rperp T)).comp (pointPath_contDiff A)

/-- Source spatial factorial bounds give the exact frame-path bounds used by the inverse. -/
theorem sourceFrame_gevrey (T : ℝ)
    (A : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (d : ℕ)
    (hb : ∀ n t x, ‖iteratedFDeriv ℝ n (A.field t : Space → Space →L[ℝ] Space) x‖ ≤
      C*majorant Rc d n) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (fun y => framePath m₀ Rperp T (pointPath A y)) x‖ ≤ C*majorant Rc d n := by
  exact contraction_bound (framePathMap m₀ Rperp T) (framePathMap_norm m₀ Rperp T)
    (pointPath A) (pointPath_contDiff A) Rc C hRc hC d (pointPath_gevrey A Rc C hRc hC d hb) n x

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The literal frame remains smooth after adjoining independent angle coordinates. -/
theorem sourceFrame_pullback_contDiff (T : ℝ) (L : P →L[ℝ] Space)
    (A : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space)) :
    ContDiff ℝ ∞ (fun x => framePath m₀ Rperp T (pointPath A (L x))) :=
  (sourceFrame_contDiff m₀ Rperp T A).comp L.contDiff

/-- The actual source `F Rperp` coefficients satisfy the full joint parameter factorial bounds. -/
theorem sourceFrame_pullback_gevrey (T : ℝ) (L : P →L[ℝ] Space) (hL : ‖L‖ ≤ 1)
    (A : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (d : ℕ)
    (hb : ∀ n t x, ‖iteratedFDeriv ℝ n (A.field t : Space → Space →L[ℝ] Space) x‖ ≤
      C*majorant Rc d n) (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => framePath m₀ Rperp T (pointPath A (L y))) x‖ ≤
      C*majorant Rc d n := by
  exact contraction_bound (framePathMap m₀ Rperp T) (framePathMap_norm m₀ Rperp T)
    (fun y => pointPath A (L y)) (pointPath_pullback_contDiff L A) Rc C hRc hC d
    (pointPath_pullback_gevrey L hL A Rc C hRc hC d hb) n x

end Frame

end EulerTransverseSourceCoefficientPath
