/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpSpatialCutoff
public import LeanPool.NavierStokesAndEuler.Euler.LpDerivativeBundling

@[expose] public section

/-! Compact approximation proves actual translation differentiability for noncompact smooth L²
  fields. -/

noncomputable section

namespace EulerLpTranslation

open MeasureTheory EulerSmoothLimit EulerNoncompactTransport EulerLpDerivative Filter
open scoped ContDiff Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def cutoffLp (f : Space → V) (hf : ContDiff ℝ ∞ f) (n : ℕ) : L2Space V :=
  compactField (cutoffField f n) (cutoffField_compact f n) (cutoffField_smooth f hf n)

def cutoffDerivativeLp (f : Space → V) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    L2Space (Space →L[ℝ] V) :=
  compactDerivative (cutoffField f n) (cutoffField_compact f n) (cutoffField_smooth f hf n)

theorem cutoffLp_ae (f : Space → V) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    cutoffLp f hf n =ᵐ[volume] cutoffField f n :=
  compactField_ae _ _ _

theorem cutoffDerivativeLp_ae (f : Space → V) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    cutoffDerivativeLp f hf n =ᵐ[volume] fderiv ℝ (cutoffField f n) :=
  compactDerivative_ae _ _ _

theorem cutoffLp_tendsto (f : Space → V) (hf : ContDiff ℝ ∞ f)
    (hLp : MemLp f 2 volume) : Tendsto (cutoffLp f hf) atTop (𝓝 (hLp.toLp f)) := by
  apply EulerLpConvergence.tendsto_of_dominated volume (cutoffLp f hf) (hLp.toLp f)
    (cutoffField f) f (cutoffLp_ae f hf) hLp.coeFn_toLp (fun x => ‖f x‖) hLp.norm
  · apply Eventually.of_forall
    intro n
    apply Eventually.of_forall
    intro x
    have he : cutoffField f n x - f x = (cutoff n x - 1) • f x := by
      simp only [cutoffField, sub_smul, one_smul]
    rw [he, norm_smul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (cutoff_sub_one_norm n x) (norm_nonneg _)
  · exact Eventually.of_forall (cutoffField_tendsto f)

theorem cutoffDerivativeLp_tendsto (f : Space → V) (hf : ContDiff ℝ ∞ f)
    (hLp : MemLp f 2 volume) (hDLp : MemLp (fderiv ℝ f) 2 volume) :
    Tendsto (cutoffDerivativeLp f hf) atTop (𝓝 (hDLp.toLp (fderiv ℝ f))) := by
  obtain ⟨M, hM0, hM⟩ := cutoff_derivative_bound
  have hD (n : ℕ) (x : Space) : ‖fderiv ℝ (cutoff n) x‖ ≤ M :=
    (hM n x).trans ((mul_le_mul_of_nonneg_left (cutoffScale_le_one n) hM0).trans_eq (mul_one M))
  apply EulerLpConvergence.tendsto_of_dominated volume (cutoffDerivativeLp f hf)
    (hDLp.toLp (fderiv ℝ f)) (fun n => fderiv ℝ (cutoffField f n)) (fderiv ℝ f)
    (cutoffDerivativeLp_ae f hf) hDLp.coeFn_toLp
    (fun x => ‖fderiv ℝ f x‖ + M * ‖f x‖) (hDLp.norm.add (hLp.norm.const_mul M))
  · apply Eventually.of_forall
    intro n
    apply Eventually.of_forall
    intro x
    rw [cutoffField_fderiv f hf]
    have he : cutoff n x • fderiv ℝ f x + (fderiv ℝ (cutoff n) x).smulRight (f x) - fderiv ℝ f x =
        (cutoff n x - 1) • fderiv ℝ f x + (fderiv ℝ (cutoff n) x).smulRight (f x) := by
      rw [sub_smul, one_smul]
      abel
    rw [he]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · rw [norm_smul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (cutoff_sub_one_norm n x) (norm_nonneg
        _)
    · rw [ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul_of_nonneg_right (hD n x) (norm_nonneg _)
  · exact Eventually.of_forall (cutoffField_fderiv_tendsto f hf)

/-- No compact support assumption is needed once the actual field and its actual derivative lie in L². -/
theorem smooth_hasFDerivAt (f : Space → V) (hf : ContDiff ℝ ∞ f)
    (hLp : MemLp f 2 volume) (hDLp : MemLp (fderiv ℝ f) 2 volume) :
    HasFDerivAt (fun a : Space => translation a (hLp.toLp f))
      (derivativeMap volume (hDLp.toLp (fderiv ℝ f))) 0 := by
  apply translation_hasFDerivAt_limit (cutoffLp f hf)
    (fun n => derivativeMap volume (cutoffDerivativeLp f hf n))
    (hLp.toLp f) (derivativeMap volume (hDLp.toLp (fderiv ℝ f)))
  · intro n
    exact compactField_hasFDerivAt _ _ _
  · exact cutoffLp_tendsto f hf hLp
  · exact (EulerLpDerivative.derivativeBundling volume).continuous.continuousAt.tendsto.comp
      (cutoffDerivativeLp_tendsto f hf hLp hDLp)

end EulerLpTranslation
