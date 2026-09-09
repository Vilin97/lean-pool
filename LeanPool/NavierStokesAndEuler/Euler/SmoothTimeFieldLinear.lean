/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldJoint

@[expose] public section

/-! Fixed bounded linear maps preserve the actual spatial and time jets of
smooth bounded coefficient paths. -/

noncomputable section


open scoped ContDiff BoundedContinuousFunction

universe u

namespace SmoothTimeField

variable {K E V W : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

private local instance (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] W) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] W) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V)) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] W)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] W)) := inferInstance

def map (L : V →L[ℝ] W) (A : SmoothTimeField K E V) : SmoothTimeField K E W where
  field := mapPath L A.field
  smooth t := L.contDiff.comp (A.smooth t)
  jet n := mapPath
    (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => E) V W L) (A.jet n)
  jet_eq n t x := by
    change L.compContinuousMultilinearMap (A.jet n t x) =
      iteratedFDeriv ℝ n (L ∘ (A.field t : E → V)) x
    rw [A.jet_eq]
    exact (L.iteratedFDeriv_comp_left (A.smooth t).contDiffAt (by simp)).symm

@[simp] theorem map_apply (L : V →L[ℝ] W) (A : SmoothTimeField K E V) (t : K) (x : E) :
    (A.map L).field t x = L (A.field t x) := rfl

@[simp] theorem map_jet_apply (L : V →L[ℝ] W) (A : SmoothTimeField K E V)
    (n : ℕ) (t : K) (x : E) :
    (A.map L).jet n t x = L.compContinuousMultilinearMap (A.jet n t x) := rfl

theorem map_jet_norm_le (L : V →L[ℝ] W) (A : SmoothTimeField K E V) (n : ℕ) :
    ‖(A.map L).jet n‖ ≤ ‖L‖ * ‖A.jet n‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg L) (norm_nonneg _))).2
  intro t
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (norm_nonneg L) (norm_nonneg _))).2
  intro x
  rw [map_jet_apply]
  exact (L.norm_compContinuousMultilinearMap_le (A.jet n t x)).trans
    (mul_le_mul_of_nonneg_left
      (((A.jet n t).norm_coe_le_norm x).trans ((A.jet n).norm_coe_le_norm t)) (norm_nonneg L))

end SmoothTimeField

namespace SmoothTimeField

open Set

variable {E V W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {T : ℝ} {hT : 0 ≤ T}

theorem TimeDerivative.map (L : V →L[ℝ] W)
    {A A₁ : SmoothTimeField (Icc (0 : ℝ) T) E V}
    (h : TimeDerivative T hT A A₁) : TimeDerivative T hT (A.map L) (A₁.map L) := by
  intro t x
  exact L.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ) (h t x)

end SmoothTimeField
