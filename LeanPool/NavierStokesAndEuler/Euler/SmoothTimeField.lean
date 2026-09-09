/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothPathSuperposition

@[expose] public section

/-! Smooth bounded fields on a general real normed domain, with actual
spatial jets continuous in the uniform time-path norm. This extends the
ordinary-space coefficient interface to the lifted four-dimensional flow. -/

noncomputable section

open scoped ContDiff BoundedContinuousFunction

universe u

structure SmoothTimeField (K E V : Type u) [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] where
  field : C(K, E →ᵇ V)
  smooth : ∀ t, ContDiff ℝ ∞ (field t : E → V)
  jet : (n : ℕ) → C(K, E →ᵇ (E [×n]→L[ℝ] V))
  jet_eq : ∀ n t x, jet n t x = iteratedFDeriv ℝ n (field t : E → V) x

namespace SmoothTimeField

variable {K E V W : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

private local instance : NormedAddCommGroup (E →ᵇ V) := inferInstance
private local instance : NormedSpace ℝ (E →ᵇ V) := inferInstance
private local instance : NormedAddCommGroup (E →ᵇ W) := inferInstance
private local instance : NormedSpace ℝ (E →ᵇ W) := inferInstance
private local instance : NormedAddCommGroup (E →ᵇ (E →L[ℝ] V)) := inferInstance
private local instance : NormedSpace ℝ (E →ᵇ (E →L[ℝ] V)) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V)) := inferInstance

def mapPath (L : V →L[ℝ] W) : C(K,E →ᵇ V) →L[ℝ] C(K,E →ᵇ W) :=
  (L.compLeftContinuousBounded E).compLeftContinuous ℝ K

def derivativeField (A : SmoothTimeField K E V) : C(K,E →ᵇ (E →L[ℝ] V)) :=
  mapPath (continuousMultilinearCurryFin1 ℝ E V).toContinuousLinearEquiv.toContinuousLinearMap
    (A.jet 1)

theorem derivativeField_eq (A : SmoothTimeField K E V) (t : K) (x : E) :
    A.derivativeField t x = fderiv ℝ (A.field t : E → V) x := by
  change continuousMultilinearCurryFin1 ℝ E V (A.jet 1 t x) = _
  rw [A.jet_eq]
  apply ContinuousLinearMap.ext
  intro a
  rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
  simp

def derivativeJet (A : SmoothTimeField K E V) (n : ℕ) :
    C(K,E →ᵇ (E [×n]→L[ℝ] (E →L[ℝ] V))) :=
  mapPath (K := K) (V := E [×(n+1)]→L[ℝ] V) (W := E [×n]→L[ℝ] (E →L[ℝ] V))
    (continuousMultilinearCurryRightEquiv' ℝ n E V).toContinuousLinearEquiv.toContinuousLinearMap
    (A.jet (n+1))

theorem derivativeJet_eq (A : SmoothTimeField K E V) (n : ℕ) (t : K) (x : E) :
    A.derivativeJet n t x = iteratedFDeriv ℝ n (fderiv ℝ (A.field t : E → V)) x := by
  change continuousMultilinearCurryRightEquiv' ℝ n E V (A.jet (n+1) t x) = _
  rw [A.jet_eq, iteratedFDeriv_succ_eq_comp_right]
  exact (continuousMultilinearCurryRightEquiv' ℝ n E V).apply_symm_apply _

def derivative (A : SmoothTimeField K E V) : SmoothTimeField K E (E →L[ℝ] V) where
  field := A.derivativeField
  smooth t := by
    have he : (A.derivativeField t : E → E →L[ℝ] V) = fderiv ℝ (A.field t : E → V) :=
      funext (A.derivativeField_eq t)
    rw [he]
    exact (A.smooth t).fderiv_right (m := ∞) (by simp)
  jet := A.derivativeJet
  jet_eq n t x := by
    have he : (A.derivativeField t : E → E →L[ℝ] V) = fderiv ℝ (A.field t : E → V) :=
      funext (A.derivativeField_eq t)
    rw [he]
    exact A.derivativeJet_eq n t x

end SmoothTimeField

namespace EulerMeanCoefficients.SmoothCoefficientPath

open EulerSmoothLimit

def toSmoothTimeField {K V : Type} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (A : SmoothCoefficientPath K V) :
    SmoothTimeField K Space V :=
  ⟨A.field, A.smooth, A.jet, A.jet_eq⟩

@[simp] theorem toSmoothTimeField_field {K V : Type} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (A : SmoothCoefficientPath K V) :
    A.toSmoothTimeField.field = A.field := rfl

end EulerMeanCoefficients.SmoothCoefficientPath
