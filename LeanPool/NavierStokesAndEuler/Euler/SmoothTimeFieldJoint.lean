/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeField
public import LeanPool.NavierStokesAndEuler.Euler.VolterraConvolution
import Mathlib.Analysis.Calculus.FDeriv.Partial

/-! Actual time derivatives and the genuine spatial jets give joint C¹
regularity on the interior of the time interval. -/

@[expose] public section


noncomputable section


open scoped ContDiff Topology BoundedContinuousFunction

namespace SmoothTimeField

open Set Filter EulerVolterraConvolution

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : ℝ) (hT : 0 ≤ T) (A A₁ : SmoothTimeField (Icc (0 : ℝ) T) E V)

/-- Real field, given by `extendPath T hT A.field t x`. -/
def realField (t : ℝ) (x : E) : V := extendPath T hT A.field t x

@[simp] theorem realField_apply (t : Icc (0 : ℝ) T) (x : E) :
    A.realField T hT t x = A.field t x := by
  simp only [realField, extendPath, projIcc_of_mem hT t.property]

theorem realField_joint_continuous : Continuous (Function.uncurry (A.realField T hT)) := by
  have hc := extendPath_continuous T hT A.field
  change Continuous (fun p : ℝ × E => extendPath T hT A.field p.1 p.2)
  fun_prop

/-- Time derivative, given by `∀ t : Icc (0 : ℝ) T, ∀ x : E, HasDerivWithinAt (fun s =>
A.realField T hT s x) (A₁.field t x) (Icc (0 : ℝ) T) t`. -/
def TimeDerivative : Prop := ∀ t : Icc (0 : ℝ) T, ∀ x : E,
  HasDerivWithinAt (fun s => A.realField T hT s x) (A₁.field t x) (Icc (0 : ℝ) T) t

/-- Joint derivative, given by `(ContinuousLinearMap.toSpanSingleton ℝ (A₁.realField T hT t
x)).coprod (A.derivative.realField T hT t x)`. -/
def jointDerivative (t : ℝ) (x : E) : (ℝ × E) →L[ℝ] V :=
  (ContinuousLinearMap.toSpanSingleton ℝ (A₁.realField T hT t x)).coprod
    (A.derivative.realField T hT t x)

theorem jointDerivative_continuous :
    Continuous (Function.uncurry (jointDerivative T hT A A₁)) := by
  have h₁ : Continuous (fun p : ℝ × E =>
      ContinuousLinearMap.toSpanSingleton ℝ (A₁.realField T hT p.1 p.2)) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ V).continuous.comp
      (A₁.realField_joint_continuous T hT)
  exact h₁.continuousLinearMapCoprod (A.derivative.realField_joint_continuous T hT)

theorem realField_hasFDerivAt (htime : TimeDerivative T hT A A₁)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    HasFDerivAt (Function.uncurry (A.realField T hT)) (jointDerivative T hT A A₁ t x) (t,x) := by
  have hloc : ∀ᶠ p : ℝ × E in 𝓝 (t,x), p.1 ∈ Ioo 0 T :=
    (continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 ht.2)
  apply HasStrictFDerivAt.hasFDerivAt
  apply hasStrictFDerivAt_uncurry_coprod
    (f := A.realField T hT) (u := (t,x))
    (f₁ := fun s y => ContinuousLinearMap.toSpanSingleton ℝ (A₁.realField T hT s y))
    (f₂ := A.derivative.realField T hT)
  · filter_upwards [hloc] with p hp
    have hd := (htime ⟨p.1,hp.1.le,hp.2.le⟩ p.2).hasDerivAt (Icc_mem_nhds hp.1 hp.2)
    change HasFDerivAt (fun s => A.realField T hT s p.2)
      (ContinuousLinearMap.toSpanSingleton ℝ (A₁.realField T hT p.1 p.2)) p.1
    simpa only [realField, extendPath, projIcc_of_mem hT ⟨hp.1.le,hp.2.le⟩]
      using hd.hasFDerivAt
  · apply Eventually.of_forall
    intro p
    change HasFDerivAt (A.field (projIcc 0 T hT p.1) : E → V)
      (A.derivativeField (projIcc 0 T hT p.1) p.2) p.2
    rw [A.derivativeField_eq]
    have hd := ((A.smooth (projIcc 0 T hT p.1)).differentiable (by simp) p.2).hasFDerivAt
    exact hd
  · exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ V).continuous.comp
      (A₁.realField_joint_continuous T hT)).continuousAt
  · exact (A.derivative.realField_joint_continuous T hT).continuousAt

theorem realField_contDiffAt_one (htime : TimeDerivative T hT A A₁)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    ContDiffAt ℝ 1 (Function.uncurry (A.realField T hT)) (t,x) := by
  rw [contDiffAt_one_iff]
  refine ⟨Function.uncurry (jointDerivative T hT A A₁),
    {p : ℝ × E | p.1 ∈ Ioo 0 T}, ?_,
    (jointDerivative_continuous T hT A A₁).continuousOn, ?_⟩
  · exact (continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 ht.2)
  · intro p hp
    exact realField_hasFDerivAt T hT A A₁ htime p.1 hp p.2

end SmoothTimeField
