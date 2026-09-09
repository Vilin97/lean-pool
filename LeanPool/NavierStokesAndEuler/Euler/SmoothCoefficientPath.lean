/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPath

@[expose] public section

/-! All-order spatial translation regularity uniformly over a compact parameter interval. -/

noncomputable section

namespace EulerMeanCoefficients

open EulerSmoothLimit MeasureTheory InnerProductSpace
open scoped ContDiff BoundedContinuousFunction

universe u v w

section Mapping

variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
  {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {W : Type w} [NormedAddCommGroup W] [NormedSpace ℝ W]

private local instance : NormedAddCommGroup (Space →ᵇ V) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ V) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ W) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ W) := inferInstance

def mapCoefficientPath (L : V →L[ℝ] W) : C(K, Space →ᵇ V) →L[ℝ] C(K, Space →ᵇ W) :=
  (L.compLeftContinuousBounded Space).compLeftContinuous ℝ K

omit [CompactSpace K] in
@[simp] theorem mapCoefficientPath_apply (L : V →L[ℝ] W)
    (A : C(K, Space →ᵇ V)) (t : K) (x : Space) : mapCoefficientPath L A t x = L (A t x) := rfl

end Mapping

/-- Actual coefficient jets, continuous in the uniform time-path norm at every fixed spatial order. -/
structure SmoothCoefficientPath (K : Type u) [TopologicalSpace K] [CompactSpace K]
    (V : Type v) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  field : C(K, Space →ᵇ V)
  smooth : ∀ t, ContDiff ℝ ∞ (field t : Space → V)
  jet : (n : ℕ) → C(K, Space →ᵇ (Space [×n]→L[ℝ] V))
  jet_eq : ∀ n t x, jet n t x = iteratedFDeriv ℝ n (field t : Space → V) x

namespace SmoothCoefficientPath

variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
  {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]

private local instance : NormedAddCommGroup (Space →ᵇ V) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ V) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ (Space →L[ℝ] V)) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ (Space →L[ℝ] V)) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (Space →ᵇ (Space [×n]→L[ℝ] V)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (Space →ᵇ (Space [×n]→L[ℝ] V)) := inferInstance

def derivativeField (A : SmoothCoefficientPath K V) : C(K, Space →ᵇ (Space →L[ℝ] V)) :=
  mapCoefficientPath
    (continuousMultilinearCurryFin1 ℝ Space V).toContinuousLinearEquiv.toContinuousLinearMap (A.jet
      1)

theorem derivativeField_eq (A : SmoothCoefficientPath K V) (t : K) (x : Space) :
    A.derivativeField t x = fderiv ℝ (A.field t : Space → V) x := by
  change continuousMultilinearCurryFin1 ℝ Space V (A.jet 1 t x) = _
  rw [A.jet_eq]
  apply ContinuousLinearMap.ext
  intro a
  rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
  simp

def derivativeJet (A : SmoothCoefficientPath K V) (n : ℕ) :
    C(K, Space →ᵇ (Space [×n]→L[ℝ] (Space →L[ℝ] V))) :=
  mapCoefficientPath (K := K) (V := Space [×(n+1)]→L[ℝ] V)
    (W := Space [×n]→L[ℝ] (Space →L[ℝ] V))
    (continuousMultilinearCurryRightEquiv' ℝ n Space
      V).toContinuousLinearEquiv.toContinuousLinearMap
      (A.jet (n+1))

theorem derivativeJet_eq (A : SmoothCoefficientPath K V) (n : ℕ) (t : K) (x : Space) :
    A.derivativeJet n t x = iteratedFDeriv ℝ n (fderiv ℝ (A.field t : Space → V)) x := by
  change continuousMultilinearCurryRightEquiv' ℝ n Space V (A.jet (n+1) t x) = _
  rw [A.jet_eq, iteratedFDeriv_succ_eq_comp_right]
  exact (continuousMultilinearCurryRightEquiv' ℝ n Space V).apply_symm_apply _

def derivative (A : SmoothCoefficientPath K V) : SmoothCoefficientPath K (Space →L[ℝ] V) where
  field := A.derivativeField
  smooth t := by
    have he : (A.derivativeField t : Space → Space →L[ℝ] V) =
        fderiv ℝ (A.field t : Space → V) := funext (A.derivativeField_eq t)
    rw [he]
    exact (A.smooth t).fderiv_right (m := ∞) (by simp)
  jet := A.derivativeJet
  jet_eq n t x := by
    have he : (A.derivativeField t : Space → Space →L[ℝ] V) =
        fderiv ℝ (A.field t : Space → V) := funext (A.derivativeField_eq t)
    rw [he]
    exact A.derivativeJet_eq n t x

theorem translation_hasFDerivAt (A : SmoothCoefficientPath K V) (a : Space) :
    HasFDerivAt (translateCoefficientPath A.field)
      (pathDerivativeMap (translateCoefficientPath A.derivative.field a)) a := by
  apply translateCoefficientPath_hasFDerivAt A.field A.derivative.field A.smooth
    A.derivativeField_eq ‖A.jet 2‖ (norm_nonneg _)
  intro t x
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv, ← A.jet_eq]
  exact ((A.jet 2 t).norm_coe_le_norm x).trans ((A.jet 2).norm_coe_le_norm t)

theorem translation_fderiv (A : SmoothCoefficientPath K V) :
    fderiv ℝ (translateCoefficientPath A.field) =
      fun a => pathDerivativeBundling (translateCoefficientPath A.derivative.field a) :=
  funext (fun a => (A.translation_hasFDerivAt a).fderiv)

private theorem translation_contDiff_nat_aux (n : ℕ) :
    ∀ (V : Type v) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : SmoothCoefficientPath K V),
      ContDiff ℝ n (translateCoefficientPath A.field) := by
  induction n with
  | zero =>
    intro V _ _ A
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
      (fun a => (A.translation_hasFDerivAt a).continuousAt))
  | succ n ih =>
    intro V _ _ A
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun a => (A.translation_hasFDerivAt a).differentiableAt, by simp, ?_⟩
    rw [A.translation_fderiv]
    exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (n : ℕ∞ω))
      (E := C(K, Space →ᵇ (Space →L[ℝ] V))) (F := Space →L[ℝ] C(K, Space →ᵇ V))
      (pathDerivativeBundling (K := K) (V := V))).comp
      (ih (Space →L[ℝ] V) A.derivative)

/-- Smoothness in the spatial translation parameter holds in the uniform time-path topology. -/
theorem translation_contDiff (A : SmoothCoefficientPath K V) :
    ContDiff ℝ ∞ (translateCoefficientPath A.field) :=
  contDiff_infty.mpr (fun n => translation_contDiff_nat_aux n V A)

end SmoothCoefficientPath

end EulerMeanCoefficients
