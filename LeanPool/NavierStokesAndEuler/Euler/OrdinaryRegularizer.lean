/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryMollifier
public import LeanPool.NavierStokesAndEuler.Euler.OrdinarySmoothingOperator
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryHelmholtzField

@[expose] public section

/-! Actual symmetric, solenoidal smoothing operators. They converge
to Helmholtz projection, with an explicit H¹ approximation error. -/

noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerMeanSmoothRepresentative EulerOrdinaryMollifier
open scoped ContDiff Topology

theorem projection_inner (u v : L2) :
    ⟪solenoidalProjection u,v⟫_ℝ=⟪u,solenoidalProjection v⟫_ℝ :=
  solenoidalSpace.inner_starProjection_left_eq_right u v

theorem projection_idempotent (u : L2) :
    solenoidalProjection (solenoidalProjection u)=solenoidalProjection u :=
  solenoidalSpace.starProjection_eq_self_iff.mpr (solenoidalProjection_mem u)

def regularizerMap (n : ℕ) : L2 →L[ℝ] L2 :=
  solenoidalProjection.comp ((mollifier n).comp solenoidalProjection)

@[simp] theorem regularizerMap_apply (n : ℕ) (u : L2) :
    regularizerMap n u=solenoidalProjection (mollify n (solenoidalProjection u)) := rfl

theorem regularizerMap_translation (n : ℕ) (a : Space) (u : L2) :
    EulerMeanSolenoidal.translation a (regularizerMap n u)=
      regularizerMap n (EulerMeanSolenoidal.translation a u) := by
  simp only [regularizerMap_apply,solenoidalProjection_translation,mollify_translation]

theorem regularizerMap_smooth (n : ℕ) (u : L2) : SmoothOrbit (regularizerMap n u) := by
  have h := solenoidalProjection.contDiff.comp (mollify_smooth n (solenoidalProjection u))
  simpa only [Function.comp_def,← solenoidalProjection_translation,← regularizerMap_apply] using h

theorem regularizerMap_symmetric (n : ℕ) (u v : L2) :
    ⟪regularizerMap n u,v⟫_ℝ=⟪u,regularizerMap n v⟫_ℝ := by
  simp only [regularizerMap_apply,projection_inner,mollify_symmetric]

theorem regularizerMap_contract (n : ℕ) (u : L2) : ‖regularizerMap n u‖ ≤ ‖u‖ :=
  (solenoidalProjection_apply_norm_le _).trans
    ((mollify_norm_le n _).trans (solenoidalProjection_apply_norm_le u))

def regularizer (n : ℕ) : SmoothingOperator where
  op := regularizerMap n
  smooth := regularizerMap_smooth n
  translation := regularizerMap_translation n
  symmetric := regularizerMap_symmetric n
  contraction := regularizerMap_contract n
  solenoidal _u := solenoidalProjection_mem _

theorem regularizer_tendsto (u : L2) :
    Tendsto (fun n => (regularizer n).op u) atTop (𝓝 (solenoidalProjection u)) := by
  change Tendsto (fun n => solenoidalProjection (mollify n (solenoidalProjection u)))
    atTop (𝓝 (solenoidalProjection u))
  have h := solenoidalProjection.continuous.tendsto (solenoidalProjection u)
  simpa only [Function.comp_def,projection_idempotent] using h.comp (mollify_tendsto
    (solenoidalProjection u))

theorem regularizer_error (n : ℕ) (A : SmoothL2Field Space) :
    ‖(regularizer n).op A.toLp-solenoidalProjection A.toLp‖ ≤
      (2*EulerNoncompactTransport.cutoffScale n)*‖(solenoidalField A).derivative.toLp‖ := by
  change ‖solenoidalProjection (mollify n (solenoidalProjection A.toLp))-
    solenoidalProjection A.toLp‖ ≤ _
  have he : solenoidalProjection (mollify n (solenoidalProjection A.toLp))-
      solenoidalProjection A.toLp=solenoidalProjection
        (mollify n (solenoidalProjection A.toLp)-solenoidalProjection A.toLp) := by
    rw [map_sub,projection_idempotent]
  rw [he]
  apply (solenoidalProjection_apply_norm_le _).trans
  simpa only [solenoidalField_toLp] using mollify_error n (solenoidalField A)

theorem solenoidalField_wordBound (A : SmoothL2Field Space) (q : ℕ) (M : ℝ)
    (hM : WordBound q M A) : WordBound q M (solenoidalField A) := by
  intro k hk w
  rw [solenoidalField_word]
  exact (solenoidalProjection_apply_norm_le _).trans (hM k hk w)

def regularizerError (n : ℕ) : ℝ := 6*EulerNoncompactTransport.cutoffScale n

theorem regularizerError_nonneg (n : ℕ) : 0 ≤ regularizerError n :=
  mul_nonneg (by norm_num) (EulerNoncompactTransport.cutoffScale_pos n).le

theorem regularizerError_tendsto : Tendsto regularizerError atTop (𝓝 (0 : ℝ)) := by
  change Tendsto (fun n => 6*EulerNoncompactTransport.cutoffScale n) atTop (𝓝 (0 : ℝ))
  simpa only [regularizerError,mul_zero] using
    EulerNoncompactTransport.cutoffScale_tendsto.const_mul 6

theorem regularizer_error_wordBound (n : ℕ) (A : SmoothL2Field Space) (M : ℝ)
    (hM : WordBound 1 M A) :
    ‖(regularizer n).op A.toLp-solenoidalProjection A.toLp‖ ≤ regularizerError n*M := by
  apply (regularizer_error n A).trans
  have hb := wordBound_jet_norm (solenoidalField_wordBound A 1 M hM) (le_refl 1)
  rw [← (solenoidalField A).derivative.norm_jetLp_zero,(solenoidalField A).norm_derivative_jetLp]
  exact (mul_le_mul_of_nonneg_left hb
    (mul_nonneg (by norm_num) (EulerNoncompactTransport.cutoffScale_pos n).le)).trans_eq (by
      simp only [regularizerError,pow_one]
      ring)

end EulerOrdinarySobolev
