/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseFixedSobolev
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevAcceleration
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpGramSobolev
public import LeanPool.NavierStokesAndEuler.Euler.TransverseFixedClassical
import LeanPool.NavierStokesAndEuler.Euler.ContinuousAccelerationSobolev
import LeanPool.NavierStokesAndEuler.Euler.FixedEvolutionRegularity
import LeanPool.NavierStokesAndEuler.Euler.MeanPathLpBlocks
import LeanPool.NavierStokesAndEuler.Euler.PacketMajorantShift
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear
import LeanPool.NavierStokesAndEuler.Euler.TimeH1SobolevReconstruction
import LeanPool.NavierStokesAndEuler.Euler.TimeLpAccelerationSobolev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Same-radius history acceleration and time trace

The true fixed-Sobolev inverse estimate passes through the actual Gram
acceleration and bounded H¹ reconstruction. For continuous forcing the
continuous Gram formula gives the time-uniform acceleration as well.
All input and output external radii are identical.
-/

@[expose] public section


noncomputable section

namespace EulerFixedEvolutionSobolev

open Set ContinuousLinearMap InnerProductSpace EulerTimeLp EulerVolterraConvolution
  EulerTransverseFixedSobolev EulerTransverseFixedEvolution EulerTimeLpAccelerationSobolev
  EulerTimeLpGramSobolev EulerTimeH1Reconstruction EulerTimeH1SobolevReconstruction
  EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

/-- Trace cost, given by `T⁻¹*Real.sqrt T+2*Real.sqrt T`. -/
def traceCost (T : ℝ) : ℝ := T⁻¹*Real.sqrt T+2*Real.sqrt T

theorem traceCost_nonneg (T : ℝ) (hT : 0 ≤ T) : 0 ≤ traceCost T := by
  unfold traceCost
  positivity

theorem weak_radius_bounds (ι : Type*) [Fintype ι] (q : ℕ) (T Rc C₀ C₁ CH c Cf R : ℝ)
    (hT : 0 ≤ T) (hRc : 0 ≤ Rc) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hCH : 0 ≤ CH) (hCf : 0 ≤ Cf)
    (hR : 2 * blockCost ι q T Rc C₀ C₁ CH c Cf * (sobolevCoefficientRadius ι Rc + 1) ≤ R) :
    1 ≤ R ∧ sobolevCoefficientRadius ι Rc ≤ R := by
  have hM := blockCost_one_le ι q T Rc C₀ C₁ CH c Cf hT hRc hC₀ hC₁ hCH hCf
  have hRc0 := sobolevCoefficientRadius_nonneg (ι := ι) Rc hRc
  constructor <;> nlinarith

variable {X U E ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype ι]
  (directions : ι → X) (hdir : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : X → C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (H : X → C(Icc (0 : ℝ) T, E →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hLower : ∀ x t v, c * ‖v‖ ^ 2 ≤ ‖Q x t v‖ ^ 2)
  (hd : ∀ x (t : Icc (0 : ℝ) T),
    HasDerivWithinAt (extendPath T hT (Q x)) (Q₁ x t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K) (hPotential : ∀ x t v, ⟪H x t v, v⟫_ℝ ≤ K * ‖v‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)
  (hQ : ContDiff ℝ ∞ Q) (hQ₁ : ContDiff ℝ ∞ Q₁) (hH : ContDiff ℝ ∞ H)
  (Rc C₀ C₁ CH Cf R : ℝ) (hRc : 0 ≤ Rc)
  (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hCH : 0 ≤ CH) (hCf : 0 ≤ Cf)
  (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C₀ * majorant Rc 0 n)
  (hbQ₁ : ∀ n x, ‖iteratedFDeriv ℝ n Q₁ x‖ ≤ C₁ * majorant Rc 0 n)
  (hbH : ∀ n x, ‖iteratedFDeriv ℝ n H x‖ ≤ CH * majorant Rc 0 n)
  (hRweak : 2 * blockCost ι q T Rc C₀ C₁ CH c Cf * (sobolevCoefficientRadius ι Rc + 1) ≤ R)
  (hRstrong : 2 * gramBlockCost ι q c Rc C₀ (accelerationBlockAmplitude ι q Rc C₀ C₁ Cf 1) *
    (sobolevCoefficientRadius ι Rc + 1) ≤ R)

include hdir hQ hQ₁ hH hRc hC₀ hC₁ hCH hCf hbQ hbQ₁ hbH hRweak hRstrong

/-- Actual L² acceleration has the second shift, in the same fixed Hq block. -/
theorem accelerationLp_block_gevrey (f : X → TimeLp T E) (hf : ContDiff ℝ ∞ f) (d : ℕ)
    (hfb : ∀ n x, block directions q f n x ≤ Cf * majorant R d n) (n : ℕ) (x : X) :
    block directions q (fun y => accelerationLp T hT (Q y) (Q₁ y) (H y) c hc (hLower y) (hd y)
      K hK (hPotential y) hsmall (f y)) n x ≤ majorant R (d+2) n := by
  let v := fun y => velocityLp T hT (Q y) (Q₁ y) (H y) c hc (hLower y) (hd y)
    K hK (hPotential y) hsmall (f y)
  have hv : ContDiff ℝ ∞ v := velocityLp_contDiff T hT Q Q₁ H c hc hLower hd
    K hK hPotential hsmall hQ hQ₁ hH f hf
  obtain ⟨hR1,hRcR⟩ := weak_radius_bounds ι q T Rc C₀ C₁ CH c Cf R hT hRc hC₀ hC₁ hCH hCf hRweak
  have hbv (k y) : block directions q v k y ≤ 1*majorant R (d+1) k := by
    simpa only [one_mul] using velocityLp_block_gevrey directions hdir q T hT Q Q₁ H
      c hc hLower hd K hK hPotential hsmall hQ hQ₁ hH Rc C₀ C₁ CH Cf R hRc hC₀ hC₁ hCH hCf
      hbQ hbQ₁ hbH hRweak f hf d hfb k y
  have hbf (k y) : block directions q f k y ≤ Cf*majorant R (d+1) k :=
    (hfb k y).trans (mul_le_mul_of_nonneg_left (majorant_mono_shift R hR1 d (d+1) k (by omega)) hCf)
  exact solution_block_bound directions hdir q T hT Q Q₁ c hc hLower f v hQ hQ₁ hf hv
    Rc R C₀ C₁ Cf 1 hRc hRcR hC₀ hC₁ hCf zero_le_one hRstrong hbQ hbQ₁ (d+1) hbf hbv n x

/-- The actual H¹ representative has a uniform-time block estimate with
the explicit time-trace cost, and no new external-radius factor. -/
theorem velocityPath_block_gevrey (hTpos : 0 < T)
    (f : X → TimeLp T E) (hf : ContDiff ℝ ∞ f) (d : ℕ)
    (hfb : ∀ n x, block directions q f n x ≤ Cf * majorant R d n) (n : ℕ) (x : X) :
    block directions q (fun y => velocityPath T hT (Q y) (Q₁ y) (H y) c hc (hLower y) (hd y)
      K hK (hPotential y) hsmall (f y)) n x ≤ traceCost T*majorant R (d+2) n := by
  let v := fun y => velocityLp T hT (Q y) (Q₁ y) (H y) c hc (hLower y) (hd y)
    K hK (hPotential y) hsmall (f y)
  let a := fun y => accelerationLp T hT (Q y) (Q₁ y) (H y) c hc (hLower y) (hd y)
    K hK (hPotential y) hsmall (f y)
  have hv : ContDiff ℝ ∞ v := velocityLp_contDiff T hT Q Q₁ H c hc hLower hd
    K hK hPotential hsmall hQ hQ₁ hH f hf
  have ha : ContDiff ℝ ∞ a := accelerationLp_contDiff T hT Q Q₁ H c hc hLower hd
    K hK hPotential hsmall hQ hQ₁ hH f hf
  have hR1 := (weak_radius_bounds ι q T Rc C₀ C₁ CH c Cf R hT hRc hC₀ hC₁ hCH hCf hRweak).1
  have hbv (k y) : block directions q v k y ≤ 1*majorant R (d+2) k := by
    have hb := velocityLp_block_gevrey directions hdir q T hT Q Q₁ H
      c hc hLower hd K hK hPotential hsmall hQ hQ₁ hH Rc C₀ C₁ CH Cf R hRc hC₀ hC₁ hCH hCf
      hbQ hbQ₁ hbH hRweak f hf d hfb k y
    simpa only [one_mul] using hb.trans (majorant_mono_shift R hR1 (d+1) (d+2) k (by omega))
  have hba (k y) : block directions q a k y ≤ 1*majorant R (d+2) k := by
    simpa only [one_mul] using accelerationLp_block_gevrey directions hdir q T hT Q Q₁ H
      c hc hLower hd K hK hPotential hsmall hQ hQ₁ hH Rc C₀ C₁ CH Cf R hRc hC₀ hC₁ hCH hCf
      hbQ hbQ₁ hbH hRweak hRstrong f hf d hfb k y
  have h := reconstruction_block_gevrey directions q T hTpos v a hv ha R 1 1 (d+2) hbv hba n x
  change block directions q (fun y => reconstruction T hTpos.le (v y,a y)) n x ≤
    traceCost T*majorant R (d+2) n
  simpa only [mul_one,traceCost] using h

/-- A bounded continuous-time forcing family enters the actual time-L² space
with no amplitude loss on a source interval of length at most one. -/
theorem continuousVelocity_block_gevrey (hTpos : 0 < T) (hT1 : T ≤ 1)
    (f : X → C(Icc (0 : ℝ) T, E)) (hf : ContDiff ℝ ∞ f) (d : ℕ)
    (hfb : ∀ n x, block directions q f n x ≤ Cf * majorant R d n) (n : ℕ) (x : X) :
    block directions q (fun y => velocityPath T hT (Q y) (Q₁ y) (H y) c hc (hLower y) (hd y)
      K hK (hPotential y) hsmall (pathLp T hT (f y))) n x ≤ traceCost T*majorant R (d+2) n := by
  have hsqrt : Real.sqrt T ≤ 1 := by simpa using Real.sqrt_le_sqrt hT1
  have hn : ‖pathLpOperator (E := E) T hT‖ ≤ 1 :=
    (EulerMeanTimeContinuousTranslation.pathLpOperator_norm_sqrt T hT).trans hsqrt
  let flp := fun y => pathLp T hT (f y)
  have hflp : ContDiff ℝ ∞ flp := (pathLpOperator (E := E) T hT).contDiff.comp hf
  have hb (k y) : block directions q flp k y ≤ Cf*majorant R d k :=
    (block_comp_clm_le directions q (pathLpOperator (E := E) T hT) f hf k y).trans
      ((mul_le_mul_of_nonneg_right hn (block_nonneg directions q f k y)).trans
        (by simpa only [one_mul] using hfb k y))
  exact velocityPath_block_gevrey directions hdir q T hT Q Q₁ H c hc hLower hd K hK hPotential
      hsmall
    hQ hQ₁ hH Rc C₀ C₁ CH Cf R hRc hC₀ hC₁ hCH hCf hbQ hbQ₁ hbH hRweak hRstrong hTpos flp hflp d hb
        n x

/-- The genuine continuous Gram acceleration has the third shift; its norm
includes the endpoint needed for gluing the first-order evolution. -/
theorem classicalAcceleration_block_gevrey (hTpos : 0 < T) (hT1 : T ≤ 1)
    (hRuniform : 2 * gramBlockCost ι q c Rc C₀ (accelerationBlockAmplitude ι q Rc C₀ C₁ Cf
        (traceCost
        T)) *
      (sobolevCoefficientRadius ι Rc + 1) ≤ R)
    (f : X → C(Icc (0 : ℝ) T, E)) (hf : ContDiff ℝ ∞ f) (d : ℕ)
    (hfb : ∀ n x, block directions q f n x ≤ Cf * majorant R d n) (n : ℕ) (x : X) :
    block directions q (fun y => classicalAcceleration T hT (Q y) (Q₁ y) (H y) c hc (hLower y) (hd
        y)
      K hK (hPotential y) hsmall (f y)) n x ≤ majorant R (d+3) n := by
  let v := fun y => velocityPath T hT (Q y) (Q₁ y) (H y) c hc (hLower y) (hd y)
    K hK (hPotential y) hsmall (pathLp T hT (f y))
  have hv : ContDiff ℝ ∞ v := continuousVelocity_contDiff T hT Q Q₁ H c hc hLower hd
    K hK hPotential hsmall hQ hQ₁ hH f hf
  obtain ⟨hR1,hRcR⟩ := weak_radius_bounds ι q T Rc C₀ C₁ CH c Cf R hT hRc hC₀ hC₁ hCH hCf hRweak
  have hbv (k y) : block directions q v k y ≤ traceCost T*majorant R (d+2) k :=
    continuousVelocity_block_gevrey directions hdir q T hT Q Q₁ H c hc hLower hd K hK hPotential
        hsmall
      hQ hQ₁ hH Rc C₀ C₁ CH Cf R hRc hC₀ hC₁ hCH hCf hbQ hbQ₁ hbH hRweak hRstrong hTpos hT1 f hf d
          hfb k y
  have hbf (k y) : block directions q f k y ≤ Cf*majorant R (d+2) k :=
    (hfb k y).trans (mul_le_mul_of_nonneg_left (majorant_mono_shift R hR1 d (d+2) k (by omega)) hCf)
  exact EulerContinuousAccelerationSobolev.acceleration_block_bound directions hdir q T Q Q₁ c hc
      hLower v f
    hQ hQ₁ hv hf Rc R C₀ C₁ Cf (traceCost T) hRc hRcR hC₀ hC₁ hCf (traceCost_nonneg T hT)
    hRuniform hbQ hbQ₁ (d+2) hbf hbv n x

end EulerFixedEvolutionSobolev
