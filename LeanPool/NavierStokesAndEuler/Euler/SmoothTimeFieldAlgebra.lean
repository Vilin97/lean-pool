/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldLinear

@[expose] public section

/-! Addition of actual smooth bounded fields and their genuine time jets. -/

noncomputable section


open scoped ContDiff BoundedContinuousFunction

universe u

namespace SmoothTimeField

variable {K E V : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private local instance (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V)) := inferInstance

def add (A B : SmoothTimeField K E V) : SmoothTimeField K E V where
  field := A.field + B.field
  smooth t := (A.smooth t).add (B.smooth t)
  jet n := A.jet n + B.jet n
  jet_eq n t x := by
    change A.jet n t x + B.jet n t x =
      iteratedFDeriv ℝ n ((A.field t : E → V) + (B.field t : E → V)) x
    rw [A.jet_eq, B.jet_eq]
    exact (iteratedFDeriv_add_apply ((A.smooth t).contDiffAt.of_le (by simp))
      ((B.smooth t).contDiffAt.of_le (by simp))).symm

@[simp] theorem add_apply (A B : SmoothTimeField K E V) (t : K) (x : E) :
    (A.add B).field t x = A.field t x + B.field t x := rfl

theorem add_jet_norm_le (A B : SmoothTimeField K E V) (n : ℕ) :
    ‖(A.add B).jet n‖ ≤ ‖A.jet n‖ + ‖B.jet n‖ := norm_add_le _ _

theorem jet_eq_of_field_eq (A B : SmoothTimeField K E V)
    (h : ∀ t x, A.field t x = B.field t x) (n : ℕ) : A.jet n = B.jet n := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro x
  rw [A.jet_eq, B.jet_eq]
  exact congrArg (fun f : E → V => iteratedFDeriv ℝ n f x) (funext (h t))

end SmoothTimeField

namespace SmoothTimeField

open Set

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : ℝ} {hT : 0 ≤ T}

theorem TimeDerivative.add
    {A A₁ B B₁ : SmoothTimeField (Icc (0 : ℝ) T) E V}
    (hA : TimeDerivative T hT A A₁) (hB : TimeDerivative T hT B B₁) :
    TimeDerivative T hT (A.add B) (A₁.add B₁) := by
  intro t x
  exact (hA t x).add (hB t x)

end SmoothTimeField
