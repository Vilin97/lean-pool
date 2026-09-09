/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TerminalTimePrimitive

@[expose] public section

/-!
# Spatial bounded maps on genuine Bochner time spaces

A bounded spatial map acts on each time slice. The lift commutes with actual
terminal integration and initial trace. These identities let spatial
translations and their difference quotients act on a fixed time Hilbert space.
-/

noncomputable section

namespace EulerTimeLpBoundedMap

open MeasureTheory Set InnerProductSpace ContinuousLinearMap EulerTimeLp
  EulerTerminalTimePrimitive

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The actual pointwise lift of a bounded spatial map to Bochner L² time. -/
def timeLift (T : ℝ) (A : E →L[ℝ] F) : TimeLp T E →L[ℝ] TimeLp T F :=
  A.compLpL 2 (timeMeasure T)

theorem timeLift_ae (T : ℝ) (A : E →L[ℝ] F) (u : TimeLp T E) :
    timeLift T A u =ᵐ[timeMeasure T] fun t => A (u t) := A.coeFn_compLpL u

theorem timeLift_norm_le (T : ℝ) (A : E →L[ℝ] F) : ‖timeLift T A‖ ≤ ‖A‖ :=
  A.norm_compLpL_le

theorem timeLift_apply_norm_le (T : ℝ) (A : E →L[ℝ] F) (u : TimeLp T E) :
    ‖timeLift T A u‖ ≤ ‖A‖*‖u‖ := A.norm_compLp_le u

theorem timeLift_add (T : ℝ) (A B : E →L[ℝ] F) :
    timeLift T (A+B) = timeLift T A + timeLift T B := A.add_compLpL B

theorem timeLift_smul (T : ℝ) (c : ℝ) (A : E →L[ℝ] F) :
    timeLift T (c • A) = c • timeLift T A := A.smul_compLpL c

theorem timeLift_comp (T : ℝ) (A : F →L[ℝ] G) (B : E →L[ℝ] F) :
    timeLift T (A.comp B) = (timeLift T A).comp (timeLift T B) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [timeLift_ae T (A.comp B) u,
    timeLift_ae T A (timeLift T B u), timeLift_ae T B u] with t hab ha hb
  exact hab.trans ((congrArg A hb).symm.trans ha.symm)

theorem timeLift_id (T : ℝ) : timeLift T (ContinuousLinearMap.id ℝ E) =
    ContinuousLinearMap.id ℝ (TimeLp T E) := by
  apply ContinuousLinearMap.ext
  intro u
  exact Lp.ext (timeLift_ae T (ContinuousLinearMap.id ℝ E) u)

theorem zeroExtension_timeLift (T : ℝ) (A : E →L[ℝ] F) (u : TimeLp T E) :
    zeroExtension T (timeLift T A u) =ᵐ[volume] fun t => A (zeroExtension T u t) := by
  have h := (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Icc).1 (timeLift_ae T A u)
  filter_upwards [h] with t ht
  by_cases hmem : t ∈ Icc (0 : ℝ) T
  · simpa only [zeroExtension, indicator_of_mem hmem] using ht
  · simp only [zeroExtension, indicator_of_notMem hmem, map_zero]

/-- An isometric spatial map remains isometric on the actual time space. -/
theorem timeLift_norm_map (T : ℝ) (A : E →L[ℝ] F)
    (hA : ∀ x, ‖A x‖ = ‖x‖) (u : TimeLp T E) : ‖timeLift T A u‖ = ‖u‖ := by
  have he : ∀ᵐ t ∂timeMeasure T, ‖timeLift T A u t‖ = ‖u t‖ := by
    filter_upwards [timeLift_ae T A u] with t ht
    exact (congrArg norm ht).trans (hA (u t))
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.le)))
    (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.ge)))

/-- The actual pointwise lift of a linear spatial isometry. -/
def timeLiftIsometry (T : ℝ) (A : E →ₗᵢ[ℝ] F) : TimeLp T E →ₗᵢ[ℝ] TimeLp T F where
  toLinearMap := (timeLift T A.toContinuousLinearMap).toLinearMap
  norm_map' := timeLift_norm_map T A.toContinuousLinearMap A.norm_map

/-- Bounded spatial maps commute with the genuine Bochner terminal primitive. -/
theorem realPrimitive_timeLift [CompleteSpace E] [CompleteSpace F] (T : ℝ) (A : E →L[ℝ] F)
    (u : TimeLp T E) (t : ℝ) :
    realPrimitive T (timeLift T A u) t = A (realPrimitive T u t) := by
  change (∫ r in T..t, zeroExtension T (timeLift T A u) r) =
    A (∫ r in T..t, zeroExtension T u r)
  have h : (∫ r in T..t, zeroExtension T (timeLift T A u) r) =
      ∫ r in T..t, A (zeroExtension T u r) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [zeroExtension_timeLift T A u] with r hr
    exact fun _ => hr
  exact h.trans (A.intervalIntegral_comp_comm (zeroExtension_integrable T u).intervalIntegrable)

/-- The terminal-zero normalization is preserved by every bounded spatial map. -/
theorem initialTrace_timeLift [CompleteSpace E] [CompleteSpace F] (T : ℝ) (hT : 0 ≤ T)
    (A : E →L[ℝ] F) (u : TimeLp T E) :
    initialTrace T hT (timeLift T A u) = A (initialTrace T hT u) :=
  realPrimitive_timeLift T A u 0

/-- Commutation also holds as an equality of actual Bochner L² fields. -/
theorem primitiveTimeLp_timeLift [CompleteSpace E] [CompleteSpace F] (T : ℝ) (hT : 0 ≤ T)
    (A : E →L[ℝ] F) (u : TimeLp T E) :
    primitiveTimeLp T hT (timeLift T A u) = timeLift T A (primitiveTimeLp T hT u) := by
  apply Lp.ext
  filter_upwards [primitiveTimeLp_ae T hT (timeLift T A u),
    primitiveTimeLp_ae T hT u, timeLift_ae T A (primitiveTimeLp T hT u)] with t hAu hu ha
  exact hAu.trans ((realPrimitive_timeLift T A u t).trans ((congrArg A hu).symm.trans ha.symm))

section Adjoint

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The genuine time-space adjoint acts by the spatial adjoint at each time. -/
theorem timeLift_adjoint (T : ℝ) (A : H →L[ℝ] K) :
    (timeLift T A).adjoint = timeLift T A.adjoint := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [adjoint_inner_left, MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [timeLift_ae T A v, timeLift_ae T A.adjoint u] with t ha hadj
  rw [ha, hadj, adjoint_inner_left]

end Adjoint

end EulerTimeLpBoundedMap
