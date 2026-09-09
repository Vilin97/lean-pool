/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldJoint
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section

/-! Genuine linear restriction of smooth coefficient fields, including
the exact spatial tensors and preservation of actual time derivatives. -/

noncomputable section


open scoped ContDiff BoundedContinuousFunction BigOperators

universe u

namespace SmoothTimeField

variable {K E F V : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private local instance (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (F [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (F [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V)) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (F →ᵇ (F [×n]→L[ℝ] V)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (F →ᵇ (F [×n]→L[ℝ] V)) := inferInstance

def precompLinear (A : SmoothTimeField K E V) (L : F →L[ℝ] E) :
    SmoothTimeField K F V where
  field := (BoundedContinuousFunction.compContinuousCLM V ℝ ⟨L,L.continuous⟩).compLeftContinuous ℝ
    K A.field
  smooth t := (A.smooth t).comp_continuousLinearMap
  jet n := ((BoundedContinuousFunction.compContinuousCLM (F [×n]→L[ℝ] V) ℝ
    ⟨L,L.continuous⟩).compLeftContinuous ℝ K)
    (mapPath (ContinuousMultilinearMap.compContinuousLinearMapL (F := V) (fun _ : Fin n => L))
      (A.jet n))
  jet_eq n t x := by
    change (A.jet n t (L x)).compContinuousLinearMap (fun _ : Fin n => L) =
      iteratedFDeriv ℝ n ((A.field t : E → V) ∘ L) x
    rw [A.jet_eq]
    exact (L.iteratedFDeriv_comp_right (A.smooth t) x (by simp)).symm

@[simp] theorem precompLinear_apply (A : SmoothTimeField K E V) (L : F →L[ℝ] E)
    (t : K) (x : F) : (A.precompLinear L).field t x = A.field t (L x) := rfl

@[simp] theorem precompLinear_jet_apply (A : SmoothTimeField K E V) (L : F →L[ℝ] E)
    (n : ℕ) (t : K) (x : F) :
    (A.precompLinear L).jet n t x = (A.jet n t (L x)).compContinuousLinearMap (fun _ : Fin n => L)
      := rfl

theorem precompLinear_jet_norm_le (A : SmoothTimeField K E V) (L : F →L[ℝ] E) (n : ℕ) :
    ‖(A.precompLinear L).jet n‖ ≤ ‖A.jet n‖ * ‖L‖^n := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))).2
  intro t
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))).2
  intro x
  rw [precompLinear_jet_apply]
  have hh := (A.jet n t (L x)).norm_compContinuousLinearMap_le (fun _ : Fin n => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (((A.jet n t).norm_coe_le_norm (L x)).trans ((A.jet n).norm_coe_le_norm t))
    (pow_nonneg (norm_nonneg _) _))

end SmoothTimeField

namespace SmoothTimeField

open Set

variable {E F V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : ℝ} {hT : 0 ≤ T}

theorem TimeDerivative.precompLinear (L : F →L[ℝ] E)
    {A A₁ : SmoothTimeField (Icc (0 : ℝ) T) E V}
    (h : TimeDerivative T hT A A₁) :
    TimeDerivative T hT (A.precompLinear L) (A₁.precompLinear L) := by
  intro t x
  exact h t (L x)

end SmoothTimeField
