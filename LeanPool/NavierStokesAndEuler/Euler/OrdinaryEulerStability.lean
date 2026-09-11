/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import LeanPool.NavierStokesAndEuler.Euler.Foundations.BreakdownCriterion
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerDifference
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryH3Norms
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordBounds
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Uniform H³ comparison and the actual no-gradient-escape consequence
for genuine ordinary Euler evolutions. No energy inequality is assumed. -/

section

/-! A regularized H³ norm of the actual Euler difference satisfies the
quadratic stability inequality. The regularization only removes the
square-root singularity at a vanishing difference. -/

section

/-! The scalar comparison lemma with genuine one-sided endpoint derivatives. -/

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open Set Real

theorem quadratic_stability_within (X X' : ℝ → ℝ) (C ε T : ℝ)
    (hC : 0 < C) (hε : 0 < ε) (_hT : 0 ≤ T)
    (hsmall : 2 * ε * exp (3 * C * T) ≤ 1 / 2)
    (hcont : ContinuousOn X (Icc 0 T)) (hinit : X 0 ≤ ε)
    (hder : ∀ t ∈ Ico 0 T, HasDerivWithinAt X (X' t) (Icc 0 T) t)
    (hineq : ∀ t ∈ Ico 0 T, X' t ≤ C * (X t + (X t) ^ 2)) :
    ∀ t ∈ Icc 0 T, X t ≤ 2*ε*exp (3*C*T) := by
  let F : ℝ → ℝ := fun t => 2*ε*exp (3*C*t)
  have hF (t : ℝ) : HasDerivAt F (3*C*F t) t := by
    have hh := ((hasDerivAt_id t).const_mul (3*C)).exp.const_mul (2*ε)
    simp only [id_eq,mul_one] at hh
    change HasDerivAt (fun s => 2*ε*exp (3*C*s)) (3*C*(2*ε*exp (3*C*t))) t
    exact hh.congr_deriv (by ring)
  have hFp (t : ℝ) : 0 < F t := by dsimp [F]; positivity
  have hbound : ∀ t ∈ Icc 0 T, X t ≤ F t := by
    apply image_le_of_deriv_right_lt_deriv_boundary hcont
      (fun t ht => (hder t ht).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    · simpa only [F,mul_zero,exp_zero,mul_one] using (hinit.trans (by linarith : ε ≤ 2*ε))
    · exact hF
    · intro t ht he
      have hFt : F t ≤ 1/2 := by
        calc
          F t ≤ 2*ε*exp (3*C*T) := by dsimp [F]; gcongr; exact ht.2.le
          _ ≤ _ := hsmall
      have hb := hineq t ht
      rw [he] at hb
      have hfsq : (F t)^2 ≤ F t := by nlinarith [hFp t]
      have hh := mul_le_mul_of_nonneg_left hfsq hC.le
      nlinarith [mul_pos hC (hFp t)]
  intro t ht
  apply (hbound t ht).trans
  dsimp [F]
  gcongr
  exact ht.2

end EulerOrdinarySobolev

end
end

end

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open Set Real MeasureTheory EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerVolterraConvolution
open scoped ContDiff

/-- Stability constant, given by `1+1800*h3ProductConstant*(1+M)`. -/
def stabilityConstant (M : ℝ) : ℝ := 1+1800*h3ProductConstant*(1+M)

theorem stabilityConstant_pos {M : ℝ} (hM : 0 ≤ M) : 0 < stabilityConstant M := by
  have hC := h3ProductConstant_nonneg
  unfold stabilityConstant
  positivity

theorem regularized_energy_bound (e ep M δ : ℝ) (he : 0 ≤ e) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hp : ep ≤ 3600 * h3ProductConstant * (M + sqrt e) * e) :
    20*ep/sqrt (e+δ^2) ≤ stabilityConstant M *
      (40*sqrt (e+δ^2)+(40*sqrt (e+δ^2))^2) := by
  let s := sqrt (e+δ^2)
  have hs : 0 < s := sqrt_pos.mpr (by nlinarith)
  have hs2 : s^2=e+δ^2 := sq_sqrt (by positivity)
  have he2 : e ≤ s^2 := by nlinarith [sq_nonneg δ]
  have hse : sqrt e ≤ 40*s := by
    have hl : sqrt e ≤ s := sqrt_le_sqrt (by nlinarith [sq_nonneg δ])
    linarith
  have hC := h3ProductConstant_nonneg
  have hb : ep ≤ 3600*h3ProductConstant*(M+40*s)*s^2 := by
    apply hp.trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add le_rfl hse) (by positivity)) he2
      he (by positivity)
  have hd : 20*ep/s ≤ 1800*h3ProductConstant*(M+40*s)*(40*s) := by
    apply (div_le_iff₀ hs).mpr
    exact (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 20)).trans_eq (by ring)
  apply hd.trans
  have hx : 0 ≤ 40*s := by positivity
  have ha : (M+40*s)*(40*s) ≤ (1+M)*(40*s+(40*s)^2) := by
    nlinarith [mul_nonneg hM (sq_nonneg (40*s))]
  calc
    _ = (1800*h3ProductConstant)*((M+40*s)*(40*s)) := by ring
    _ ≤ (1800*h3ProductConstant)*((1+M)*(40*s+(40*s)^2)) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    _ = (1800*h3ProductConstant*(1+M))*(40*s+(40*s)^2) := by ring
    _ ≤ stabilityConstant M*(40*s+(40*s)^2) :=
      mul_le_mul_of_nonneg_right (by unfold stabilityConstant; linarith)
        (add_nonneg hx (sq_nonneg _))

namespace Evolution

variable {T : ℝ} {hT : 0 ≤ T}

/-- Norm envelope, given by `⟨fun t => 40*sqrt (U.energyPath V t+δ^2), continuous_const.mul
(((U.energyPath V).continuous.add continuous_const).sqrt)⟩`. -/
def normEnvelope (U V : Evolution T hT) (δ : ℝ) : C(Icc (0 : ℝ) T,ℝ) :=
  ⟨fun t => 40*sqrt (U.energyPath V t+δ^2),
    continuous_const.mul (((U.energyPath V).continuous.add continuous_const).sqrt)⟩

/-- Envelope derivative, given by `20*U.energyDerivative V t/sqrt (U.energyPath V t+δ^2)`. -/
def envelopeDerivative (U V : Evolution T hT) (δ : ℝ) (t : Icc (0 : ℝ) T) : ℝ :=
  20*U.energyDerivative V t/sqrt (U.energyPath V t+δ^2)

theorem energyPath_nonneg (U V : Evolution T hT) (t : Icc (0 : ℝ) T) : 0 ≤ U.energyPath V t :=
  wordEnergy_nonneg 3 _

theorem normEnvelope_nonneg (U V : Evolution T hT) (δ : ℝ) (t : Icc (0 : ℝ) T) :
    0 ≤ U.normEnvelope V δ t := by
  change 0 ≤ 40*sqrt _
  positivity

theorem normEnvelope_hasDerivWithinAt (U V : Evolution T hT) (δ : ℝ) (hδ : 0 < δ)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (U.normEnvelope V δ)) (U.envelopeDerivative V δ t)
      (Icc (0 : ℝ) T) t := by
  have he : extendPath T hT (U.energyPath V) t=U.energyPath V t := by
    simp only [extendPath,projIcc_of_mem hT t.property]
  have hp : 0 < U.energyPath V t+δ^2 := by nlinarith [U.energyPath_nonneg V t]
  have h := (((U.energy_hasDerivWithinAt V t).add_const (δ^2)).sqrt (by
    simp only [he]
    exact hp.ne')).const_mul 40
  have hd : 40*(U.energyDerivative V t/(2*sqrt (extendPath T hT (U.energyPath V) t+δ^2))) =
      U.envelopeDerivative V δ t := by
    rw [he]
    unfold envelopeDerivative
    ring
  exact h.congr_deriv hd

theorem envelopeDerivative_bound (U V : Evolution T hT) (M δ : ℝ)
    (hM : ∀ t, WordBound 4 M (U.velocity t)) (hδ : 0 < δ) (t : Icc (0 : ℝ) T) :
    U.envelopeDerivative V δ t ≤ stabilityConstant M *
      (U.normEnvelope V δ t+(U.normEnvelope V δ t)^2) :=
  regularized_energy_bound _ _ M δ (U.energyPath_nonneg V t)
    (wordBound_nonneg (hM t)) hδ (U.energyDerivative_bound V M hM t)

theorem normEnvelope_majorizes (U V : Evolution T hT) (δ : ℝ) (t : Icc (0 : ℝ) T) :
    tensorNorm 3 (U.difference V t) ≤ U.normEnvelope V δ t := by
  apply (tensorNorm_le_sqrt_energy _).trans
  exact mul_le_mul_of_nonneg_left (sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg δ)))
    (by norm_num : (0 : ℝ) ≤ 40)

theorem normEnvelope_initial (U V : Evolution T hT) (ε : ℝ) (hε : 0 < ε)
    (hinit : tensorNorm 3 (U.difference V ⟨0, le_rfl, hT⟩) ≤ ε) :
    U.normEnvelope V ε ⟨0,le_rfl,hT⟩ ≤ 320*ε := by
  have hs := tensorNorm_nonneg 3 (U.difference V ⟨0,le_rfl,hT⟩)
  have hb := energy_le_tensorNorm_sq (U.difference V ⟨0,le_rfl,hT⟩)
  have he := U.energyPath_nonneg V ⟨0,le_rfl,hT⟩
  have hp := pow_le_pow_left₀ hs hinit 2
  have hroot := sq_sqrt (show 0 ≤ U.energyPath V ⟨0,le_rfl,hT⟩+ε^2 by positivity)
  have hr : sqrt (U.energyPath V ⟨0,le_rfl,hT⟩+ε^2) ≤ 8*ε := by
    change U.energyPath V ⟨0,le_rfl,hT⟩ ≤ _ at hb
    nlinarith [sqrt_nonneg (U.energyPath V ⟨0,le_rfl,hT⟩+ε^2)]
  change 40*sqrt _ ≤ 320*ε
  nlinarith

theorem h3_stability (U V : Evolution T hT) (M ε : ℝ)
    (hM : ∀ t, WordBound 4 M (U.velocity t)) (hε : 0 < ε)
    (hinit : tensorNorm 3 (U.difference V ⟨0, le_rfl, hT⟩) ≤ ε)
    (hsmall : 640 * ε * exp (3 * stabilityConstant M * T) ≤ 1 / 2)
    (t : Icc (0 : ℝ) T) :
    tensorNorm 3 (U.difference V t) ≤ 640*ε*exp (3*stabilityConstant M*T) := by
  have hMp := stabilityConstant_pos (wordBound_nonneg (hM ⟨0,le_rfl,hT⟩))
  have hb := quadratic_stability_within
    (extendPath T hT (U.normEnvelope V ε))
    (fun r => U.envelopeDerivative V ε (projIcc 0 T hT r))
    (stabilityConstant M) (320*ε) T hMp (by positivity) hT
    (by nlinarith [hsmall]) (extendPath_continuous T hT (U.normEnvelope V ε)).continuousOn
    (by
        simpa only [extendPath,projIcc_of_mem hT ⟨le_rfl,hT⟩] using U.normEnvelope_initial V ε hε
            hinit)
    (fun r hr => by
      have h := U.normEnvelope_hasDerivWithinAt V ε hε ⟨r,hr.1,hr.2.le⟩
      simpa only [projIcc_of_mem hT ⟨hr.1,hr.2.le⟩] using h)
    (fun r hr => by
      simpa only [extendPath,projIcc_of_mem hT ⟨hr.1,hr.2.le⟩] using
        U.envelopeDerivative_bound V M ε hM hε ⟨r,hr.1,hr.2.le⟩)
    t t.property
  apply (U.normEnvelope_majorizes V ε t).trans
  have hb' : U.normEnvelope V ε t ≤ 2*(320*ε)*exp (3*stabilityConstant M*T) := by
    simpa only [extendPath,projIcc_of_mem hT t.property] using hb
  exact hb'.trans_eq (by ring)

end Evolution
end EulerOrdinarySobolev

end
end

end

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev.Evolution

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerMeanSobolevBoundedField EulerSmoothSobolev EulerVolterraConvolution Finset
open scoped ContDiff Topology BoundedContinuousFunction

variable {T : ℝ} {hT : 0 ≤ T}

/-- Reference norm path, given by `⟨fun t => tensorNorm 4 (U.velocity t),by apply
continuous_finsetSum intro n _ exact (U.velocity_continuous n).norm⟩`. -/
def referenceNormPath (U : Evolution T hT) : C(Icc (0 : ℝ) T,ℝ) :=
  ⟨fun t => tensorNorm 4 (U.velocity t),by
    apply continuous_finsetSum
    intro n _
    exact (U.velocity_continuous n).norm⟩

/-- Reference size, given by `‖U.referenceNormPath‖`. -/
def referenceSize (U : Evolution T hT) : ℝ := ‖U.referenceNormPath‖

theorem referenceSize_nonneg (U : Evolution T hT) : 0 ≤ U.referenceSize := norm_nonneg _

theorem referenceWordBound (U : Evolution T hT) (t : Icc (0 : ℝ) T) :
    WordBound 4 U.referenceSize (U.velocity t) := by
  have h := (U.referenceNormPath).norm_coe_le_norm t
  change ‖tensorNorm 4 (U.velocity t)‖ ≤ U.referenceSize at h
  rw [Real.norm_of_nonneg (tensorNorm_nonneg 4 (U.velocity t))] at h
  intro n hn w
  exact (wordBound_tensorNorm 4 (U.velocity t) n hn w).trans h

theorem gradient_continuous (U : Evolution T hT) (x : Space) :
    Continuous (fun t => fderiv ℝ (U.velocity t).field x) := by
  have h := (BoundedContinuousFunction.evalCLM ℝ x :
      (Space →ᵇ (Space →L[ℝ] Space)) →L[ℝ] (Space →L[ℝ] Space)).continuous.comp
    (continuous_finiteField (fun t => (U.velocity t).derivative)
      (continuous_jetLp_derivative U.velocity U.velocity_continuous))
  have he : (fun t => fderiv ℝ (U.velocity t).field x) =
      fun t => (BoundedContinuousFunction.evalCLM ℝ x)
        (finiteField ((U.velocity t).derivative)) := by
    funext t
    exact (finiteField_apply ((U.velocity t).derivative) x).symm
  rw [he]
  exact h

theorem eventually_h3_bound (U : Evolution T hT) (V : ℕ → Evolution T hT)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (hinit : ∀ n, tensorNorm 3 (U.difference (V n) ⟨0, le_rfl, hT⟩) ≤ ε n) :
    ∀ᶠ n in atTop, ∀ t : Icc (0 : ℝ) T,
      tensorNorm 3 (U.difference (V n) t) ≤
        640*ε n*Real.exp (3*stabilityConstant U.referenceSize*T) := by
  have hb : Tendsto (fun n => 640*ε n*Real.exp (3*stabilityConstant U.referenceSize*T))
      atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using (hlim.const_mul 640).mul_const
      (Real.exp (3*stabilityConstant U.referenceSize*T))
  have hs : ∀ᶠ n in atTop, 640*ε n*Real.exp (3*stabilityConstant U.referenceSize*T) ≤ 1/2 :=
    hb.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [hs] with n hn t
  exact U.h3_stability (V n) U.referenceSize (ε n) U.referenceWordBound (hε n) (hinit n) hn t

theorem sampled_h3_tendsto_zero (U : Evolution T hT) (V : ℕ → Evolution T hT)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (hinit : ∀ n, tensorNorm 3 (U.difference (V n) ⟨0, le_rfl, hT⟩) ≤ ε n)
    (times : ℕ → Icc (0 : ℝ) T) :
    Tendsto (fun n => tensorNorm 3 (U.difference (V n) (times n))) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n => tensorNorm_nonneg 3 _))
    ((U.eventually_h3_bound V ε hε hlim hinit).mono (fun n hn => hn (times n)))
  simpa only [mul_zero,zero_mul] using (hlim.const_mul 640).mul_const
    (Real.exp (3*stabilityConstant U.referenceSize*T))

theorem no_gradient_escape (U : Evolution T hT) (V : ℕ → Evolution T hT)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (hinit : ∀ n, tensorNorm 3 (U.difference (V n) ⟨0, le_rfl, hT⟩) ≤ ε n)
    (times : ℕ → Icc (0 : ℝ) T) :
    ¬ Tendsto (fun n => ‖fderiv ℝ ((V n).velocity (times n)).field 0‖) atTop atTop := by
  let err : ℕ → ℝ := fun n => (9*smoothEmbeddingConstant) *
    tensorNorm 3 (U.difference (V n) (times n))
  have he : Tendsto err atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (U.sampled_h3_tendsto_zero V ε hε hlim hinit times).const_mul (9*smoothEmbeddingConstant)
  have hc : Continuous (fun r => fderiv ℝ (U.velocity (projIcc 0 T hT r)).field 0) :=
    (U.gradient_continuous 0).comp continuous_projIcc
  apply EulerBreakdownCriterion.no_escape_near_compact_trajectory
    (fun r => fderiv ℝ (U.velocity (projIcc 0 T hT r)).field 0)
    (fun n => fderiv ℝ ((V n).velocity (times n)).field 0)
    (fun n => (times n : ℝ)) err T hc.continuousOn (fun n => (times n).property) he
  apply Eventually.of_forall
  intro n
  have hb := real_smooth_fderiv_le_H3 3 (U.difference (V n) (times n)).field
    (U.difference (V n) (times n)).smooth
    (fun j _ => (U.difference (V n) (times n)).integrable j) 0
  have hf : (U.difference (V n) (times n)).field =
      ((V n).velocity (times n)).field-(U.velocity (times n)).field :=
    funext (fieldSub_field _ _)
  rw [hf,fderiv_sub (((V n).velocity (times n)).smooth.differentiable (by simp) 0)
    ((U.velocity (times n)).smooth.differentiable (by simp) 0)] at hb
  rw [projIcc_of_mem hT (times n).property]
  change _ ≤ (9*smoothEmbeddingConstant)*tensorNorm 3 (U.difference (V n) (times n))
  rw [tensorNorm_eq,hf]
  exact hb

end EulerOrdinarySobolev.Evolution
