/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeLpMap

@[expose] public section

/-! Actual bounded time-dependent linear operators on Bochner L² time fields. -/

noncomputable section

namespace EulerTimeLp

open MeasureTheory Set EulerVolterraConvolution
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous compact-time operator path acts on every actual square-integrable time field. -/
theorem timeApply_memLp (T : ℝ) (hT : 0 ≤ T) (A : C(Icc (0 : ℝ) T, E →L[ℝ] F))
    (u : TimeLp T E) : MemLp (fun t => extendPath T hT A t (u t)) 2 (timeMeasure T) := by
  apply (Lp.memLp u).of_le_mul (c := ‖A‖)
  · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      ((extendPath_continuous T hT A).aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable u))
  · exact Filter.Eventually.of_forall fun t =>
      ((extendPath T hT A t).le_opNorm (u t)).trans
        (mul_le_mul_of_nonneg_right (extendPath_norm_le T hT A t) (norm_nonneg (u t)))

/-- The genuine pointwise time-dependent operator action, represented in Bochner L². -/
def timeApply (T : ℝ) (hT : 0 ≤ T) (A : C(Icc (0 : ℝ) T, E →L[ℝ] F))
    (u : TimeLp T E) : TimeLp T F :=
  (timeApply_memLp T hT A u).toLp (fun t => extendPath T hT A t (u t))

/-- The actual Bochner action has its literal pointwise representative almost everywhere. -/
theorem timeApply_ae (T : ℝ) (hT : 0 ≤ T) (A : C(Icc (0 : ℝ) T, E →L[ℝ] F))
    (u : TimeLp T E) :
    (timeApply T hT A u : ℝ → F) =ᵐ[timeMeasure T] fun t => extendPath T hT A t (u t) :=
  (timeApply_memLp T hT A u).coeFn_toLp

/-- Actual time-dependent bounded operator application is linear in the time field. -/
def timeApplyLinear (T : ℝ) (hT : 0 ≤ T) (A : C(Icc (0 : ℝ) T, E →L[ℝ] F)) :
    TimeLp T E →ₗ[ℝ] TimeLp T F where
  toFun := timeApply T hT A
  map_add' u v := by
    apply Lp.ext
    filter_upwards [timeApply_ae T hT A (u+v), timeApply_ae T hT A u, timeApply_ae T hT A v,
      Lp.coeFn_add u v, Lp.coeFn_add (timeApply T hT A u) (timeApply T hT A v)] with t h1 h2 h3 h4
        h5
    simp only [Pi.add_apply] at h4 h5
    rw [h1, h5, h2, h3, h4, map_add]
  map_smul' r u := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [timeApply_ae T hT A (r • u), timeApply_ae T hT A u,
      Lp.coeFn_smul r u, Lp.coeFn_smul r (timeApply T hT A u)] with t h1 h2 h3 h4
    simp only [Pi.smul_apply] at h3 h4
    rw [h1, h4, h2, h3, map_smul]

/-- The actual time multiplier has the uniform operator-path norm bound. -/
theorem timeApply_bound (T : ℝ) (hT : 0 ≤ T) (A : C(Icc (0 : ℝ) T, E →L[ℝ] F))
    (u : TimeLp T E) : ‖timeApply T hT A u‖ ≤ ‖A‖*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [timeApply_ae T hT A u] with t ht
  rw [ht]
  exact ((extendPath T hT A t).le_opNorm (u t)).trans
    (mul_le_mul_of_nonneg_right (extendPath_norm_le T hT A t) (norm_nonneg (u t)))

/-- The bounded actual time multiplier on Bochner L² spaces. -/
def timeMultiplier (T : ℝ) (hT : 0 ≤ T) (A : C(Icc (0 : ℝ) T, E →L[ℝ] F)) :
    TimeLp T E →L[ℝ] TimeLp T F :=
  (timeApplyLinear T hT A).mkContinuous ‖A‖ (timeApply_bound T hT A)

/-- The continuous linear time multiplier agrees with literal pointwise application. -/
theorem timeMultiplier_ae (T : ℝ) (hT : 0 ≤ T) (A : C(Icc (0 : ℝ) T, E →L[ℝ] F))
    (u : TimeLp T E) :
    (timeMultiplier T hT A u : ℝ → F) =ᵐ[timeMeasure T] fun t => extendPath T hT A t (u t) :=
  timeApply_ae T hT A u

/-- A continuous path is carried to its actual pointwise operator path by the Bochner multiplier. -/
theorem timeMultiplier_pathLp (T : ℝ) (hT : 0 ≤ T) (A : C(Icc (0 : ℝ) T, E →L[ℝ] F))
    (u : C(Icc (0 : ℝ) T, E)) :
    timeMultiplier T hT A (pathLp T hT u) =
      pathLp T hT (⟨fun t => A t (u t), A.continuous.clm_apply u.continuous⟩ : C(Icc (0 : ℝ) T, F))
        := by
  apply Lp.ext
  filter_upwards [timeMultiplier_ae T hT A (pathLp T hT u), pathLp_ae T hT u,
    pathLp_ae T hT (⟨fun t => A t (u t), A.continuous.clm_apply u.continuous⟩ : C(Icc (0 : ℝ) T,
      F))]
    with t h1 h2 h3
  rw [h1, h2, h3]
  rfl

end EulerTimeLp
