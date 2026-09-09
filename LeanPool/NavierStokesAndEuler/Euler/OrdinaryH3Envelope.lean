/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerDifference
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryH3Norms
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryQuadraticStability
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordBounds
import Mathlib.Algebra.Order.Star.Real

/-! A regularized H³ norm of the actual Euler difference satisfies the
quadratic stability inequality. The regularization only removes the
square-root singularity at a vanishing difference. -/

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
