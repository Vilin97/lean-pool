/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothPathTimeJets
public import Mathlib.Analysis.Calculus.FDeriv.Partial

@[expose] public section

/-! Joint time-space differentiability of a genuine smooth family of
continuous paths, and the actual mixed derivative of its spatial Jacobian. -/

noncomputable section


open scoped ContDiff Topology

namespace EulerSmoothPathJoint

open Set Filter EulerVolterraConvolution EulerSmoothPathTimeJets

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (T : ℝ) (hT : 0 ≤ T) (f q : E → C(Icc (0 : ℝ) T,V))

def timeSlice (t : ℝ) (x : E) : V := extendPath T hT (f x) t

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
theorem timeSlice_joint_continuous (hf : Continuous f) :
    Continuous (Function.uncurry (timeSlice T hT f)) := by
  unfold timeSlice extendPath
  fun_prop

def spatialDerivative (x : E) : C(Icc (0 : ℝ) T,E →L[ℝ] V) :=
  ((continuousMultilinearCurryFin1 ℝ E
    V).toContinuousLinearEquiv.toContinuousLinearMap.compLeftContinuous
    ℝ (Icc (0 : ℝ) T)) (jetFamily T f 1 x)

theorem spatialDerivative_contDiff (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (spatialDerivative T f) := by
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(Icc (0 : ℝ) T,E [×1]→L[ℝ] V)) (F := C(Icc (0 : ℝ) T,E →L[ℝ] V))
    ((continuousMultilinearCurryFin1 ℝ E
      V).toContinuousLinearEquiv.toContinuousLinearMap.compLeftContinuous
      ℝ (Icc (0 : ℝ) T))).comp (jetFamily_contDiff T f hf 1)

theorem spatialDerivative_apply (hf : ContDiff ℝ ∞ f) (x : E) (t : Icc (0 : ℝ) T) :
    spatialDerivative T f x t = fderiv ℝ (fun y => f y t) x := by
  change continuousMultilinearCurryFin1 ℝ E V (jetFamily T f 1 x t) = _
  rw [jetFamily_apply T f hf]
  apply ContinuousLinearMap.ext
  intro v
  rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
  simp

theorem timeSlice_hasFDerivAt (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : E) :
    HasFDerivAt (timeSlice T hT f t) (spatialDerivative T f x (projIcc 0 T hT t)) x := by
  rw [spatialDerivative_apply T f hf]
  exact (((ContinuousMap.evalCLM ℝ (projIcc 0 T hT t)).contDiff.comp hf).differentiable
    (by simp) x).hasFDerivAt

def jointDerivative (t : ℝ) (x : E) : (ℝ × E) →L[ℝ] V :=
  (ContinuousLinearMap.toSpanSingleton ℝ (timeSlice T hT q t x)).coprod
    (timeSlice T hT (spatialDerivative T f) t x)

theorem jointDerivative_continuous (hf : ContDiff ℝ ∞ f) (hq : Continuous q) :
    Continuous (Function.uncurry (jointDerivative T hT f q)) := by
  exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ V).continuous.comp
    (timeSlice_joint_continuous T hT q hq)).continuousLinearMapCoprod
      (timeSlice_joint_continuous T hT (spatialDerivative T f)
        (spatialDerivative_contDiff T f hf).continuous)

variable (hf : ContDiff ℝ ∞ f) (hq : ContDiff ℝ ∞ q)
  (hd : ∀ x (t : Icc (0 : ℝ) T),
    HasDerivWithinAt (extendPath T hT (f x)) (q x t) (Icc (0 : ℝ) T) t)

include hf hq hd in
theorem joint_hasFDerivAt (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    HasFDerivAt (Function.uncurry (timeSlice T hT f)) (jointDerivative T hT f q t x) (t,x) := by
  have hloc : ∀ᶠ p : ℝ × E in 𝓝 (t,x), p.1 ∈ Ioo 0 T :=
    (continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 ht.2)
  apply HasStrictFDerivAt.hasFDerivAt
  apply hasStrictFDerivAt_uncurry_coprod
    (f := timeSlice T hT f) (u := (t,x))
    (f₁ := fun s y => ContinuousLinearMap.toSpanSingleton ℝ (timeSlice T hT q s y))
    (f₂ := timeSlice T hT (spatialDerivative T f))
  · filter_upwards [hloc] with p hp
    change HasFDerivAt (fun s => timeSlice T hT f s p.2)
      (ContinuousLinearMap.toSpanSingleton ℝ (timeSlice T hT q p.1 p.2)) p.1
    have hh := (hd p.2 ⟨p.1,hp.1.le,hp.2.le⟩).hasDerivAt (Icc_mem_nhds hp.1 hp.2)
    have he : timeSlice T hT q p.1 p.2 = q p.2 ⟨p.1,hp.1.le,hp.2.le⟩ := by
      simp only [timeSlice, extendPath, projIcc_of_mem hT ⟨hp.1.le,hp.2.le⟩]
    rw [he]
    exact hh.hasFDerivAt
  · apply Eventually.of_forall
    intro p
    exact timeSlice_hasFDerivAt T hT f hf p.1 p.2
  · exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ V).continuous.comp
      (timeSlice_joint_continuous T hT q hq.continuous)).continuousAt
  · exact (timeSlice_joint_continuous T hT (spatialDerivative T f)
      (spatialDerivative_contDiff T f hf).continuous).continuousAt

include hf hq hd in
theorem joint_contDiffAt_one (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    ContDiffAt ℝ 1 (Function.uncurry (timeSlice T hT f)) (t,x) := by
  rw [contDiffAt_one_iff]
  refine ⟨Function.uncurry (jointDerivative T hT f q), {p : ℝ × E | p.1 ∈ Ioo 0 T}, ?_,
    (jointDerivative_continuous T hT f q hf hq.continuous).continuousOn, ?_⟩
  · exact (continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 ht.2)
  · intro p hp
    exact joint_hasFDerivAt T hT f q hf hq hd p.1 hp p.2

include hf hq hd in
theorem spatialDerivative_time (x : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (spatialDerivative T f x))
      (spatialDerivative T q x t) (Icc (0 : ℝ) T) t := by
  have h := (continuousMultilinearCurryFin1 ℝ E
    V).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt
    (t : ℝ) (jetFamily_hasDerivWithinAt T hT f q hf hq hd 1 x t)
  exact h

end EulerSmoothPathJoint
