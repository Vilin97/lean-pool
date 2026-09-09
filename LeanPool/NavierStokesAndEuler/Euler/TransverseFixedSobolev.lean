/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseGevreyInverse
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevTensorInverse
public import LeanPool.NavierStokesAndEuler.Euler.TransverseFixedEvolution
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevProductGevrey
import LeanPool.NavierStokesAndEuler.Euler.TransverseParameterRegularity
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Same-radius fixed-Sobolev estimates for the actual transverse history

The finite base order stays inside each external word. Only coefficient
tensor bounds are converted to word sums; forcing and solution use the same
external radius and base order. The recurrence is applied to the actual
coercive inverse, with its proved polynomial norm bound.
-/

@[expose] public section


noncomputable section

namespace EulerTransverseFixedSobolev

open Set ContinuousLinearMap InnerProductSpace EulerTimeLp EulerVolterraConvolution
  EulerTimeH1FrameTransport EulerTransverseFixedSpaceInverse EulerTransverseParameterRegularity
  EulerTransverseCoefficientGevrey EulerTransverseGevreyInverse EulerCoerciveProjection
  EulerTransverseGramInverse EulerOperatorGevreyCalculus EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

/-- Forcing block amplitude, given by `3*sobolevCoefficientAmplitude ι q Rc (T*derivativeCost T
C₀ C₁)*Cf`. -/
def forcingBlockAmplitude (ι : Type*) [Fintype ι] (q : ℕ) (T Rc C₀ C₁ Cf : ℝ) : ℝ :=
  3*sobolevCoefficientAmplitude ι q Rc (T*derivativeCost T C₀ C₁)*Cf

/-- Block cost, given by `inverseBlockCost ι q (inverseCost T C₀ C₁ c) Rc (formCost T C₀ C₁ CH)
(forcingBlockAmplitude ι q T Rc C₀ C₁ Cf)`. -/
def blockCost (ι : Type*) [Fintype ι] (q : ℕ) (T Rc C₀ C₁ CH c Cf : ℝ) : ℝ :=
  inverseBlockCost ι q (inverseCost T C₀ C₁ c) Rc (formCost T C₀ C₁ CH)
    (forcingBlockAmplitude ι q T Rc C₀ C₁ Cf)

theorem forcingBlockAmplitude_nonneg (ι : Type*) [Fintype ι] (q : ℕ) (T Rc C₀ C₁ Cf : ℝ)
    (hT : 0 ≤ T) (hRc : 0 ≤ Rc) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hCf : 0 ≤ Cf) :
    0 ≤ forcingBlockAmplitude ι q T Rc C₀ C₁ Cf := by
  have hb := sobolevCoefficientAmplitude_nonneg (ι := ι) q Rc (T*derivativeCost T C₀ C₁)
    hRc (by unfold derivativeCost; positivity)
  unfold forcingBlockAmplitude
  positivity

theorem blockCost_one_le (ι : Type*) [Fintype ι] (q : ℕ) (T Rc C₀ C₁ CH c Cf : ℝ)
    (hT : 0 ≤ T) (hRc : 0 ≤ Rc) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hCH : 0 ≤ CH) (hCf : 0 ≤ Cf) : 1 ≤ blockCost ι q T Rc C₀ C₁ CH c Cf := by
  have hI : 0 ≤ inverseCost T C₀ C₁ c := by unfold inverseCost; positivity
  have hC : 0 ≤ formCost T C₀ C₁ CH := by unfold formCost; positivity
  have hA := sobolevCoefficientAmplitude_nonneg (ι := ι) q Rc _ hRc hC
  have hB := forcingBlockAmplitude_nonneg ι q T Rc C₀ C₁ Cf hT hRc hC₀ hC₁ hCf
  have hS := sobolevInverseCost_nonneg (inverseCost T C₀ C₁ c)
    (sobolevCoefficientAmplitude ι q Rc (formCost T C₀ C₁ CH)) hI hA q
  unfold blockCost inverseBlockCost
  linarith [mul_nonneg hS (add_nonneg hA hB)]

variable {X U E ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype ι]

/-- The actual weak forcing pullback has coefficient-only tensor bounds. -/
theorem forcingOperator_bound (T : ℝ) (hT : 0 ≤ T)
    (Q Q₁ : X → C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (hQ : ContDiff ℝ ∞ Q) (hQ₁ : ContDiff ℝ ∞ Q₁)
    (Rc C₀ C₁ : ℝ) (hRc : 0 ≤ Rc) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C₀ * majorant Rc 0 n)
    (hbQ₁ : ∀ n x, ‖iteratedFDeriv ℝ n Q₁ x‖ ≤ C₁ * majorant Rc 0 n)
    (n : ℕ) (x : X) :
    ‖iteratedFDeriv ℝ n (fun y => -(fixedFramePrimitive T hT (Q y) (Q₁ y)).adjoint) x‖ ≤
      (T*derivativeCost T C₀ C₁)*majorant Rc 0 n :=
  neg_bound (fun y => (fixedFramePrimitive T hT (Q y) (Q₁ y)).adjoint)
    Rc (T*derivativeCost T C₀ C₁) 0
    (adjoint_bound (fun y => fixedFramePrimitive T hT (Q y) (Q₁ y))
      (contDiff_fixedFramePrimitive T hT Q Q₁ hQ hQ₁)
      Rc (T*derivativeCost T C₀ C₁) hRc (by unfold derivativeCost; positivity) 0
      (fixedFramePrimitive_bound T hT Q Q₁ hQ hQ₁ Rc C₀ C₁ hRc hC₀ hC₁ hbQ hbQ₁)) n x

variable (directions : ι → X) (hdir : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
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
  (hR : 2 * blockCost ι q T Rc C₀ C₁ CH c Cf * (sobolevCoefficientRadius ι Rc + 1) ≤ R)

include hdir hQ hQ₁ hH hRc hC₀ hC₁ hCH hCf hbQ hbQ₁ hbH hR

/-- The genuine zero-trace coordinate solver gains one factorial shift at
the identical external radius and fixed base Sobolev order. -/
theorem solver_block_gevrey (f : X → TimeLp T E) (hf : ContDiff ℝ ∞ f) (d : ℕ)
    (hfb : ∀ n x, block directions q f n x ≤ Cf * majorant R d n) (n : ℕ) (x : X) :
    block directions q (fun y => fixedFrameSolver T hT (Q y) (Q₁ y) (H y)
      c hc (hLower y) (hd y) K hK (hPotential y) hsmall (f y)) n x ≤ majorant R (d+1) n := by
  let A := fun y => fixedFrameOperator T hT (Q y) (Q₁ y) (H y)
  let δ := fun y => fixedCoercivity T (Q y) (Q₁ y) c
  let J := fun y => -(fixedFramePrimitive T hT (Q y) (Q₁ y)).adjoint
  let v := fun y => fixedFrameSolver T hT (Q y) (Q₁ y) (H y)
    c hc (hLower y) (hd y) K hK (hPotential y) hsmall (f y)
  let rhs := fun y => J y (f y)
  have hδ (y : X) : 0 < δ y := fixedCoercivity_pos T hT (Q y) (Q₁ y) c hc
  have hco (y : X) (u : zeroTraceDerivatives (U := U) T hT) :
      δ y*‖u‖^2 ≤ ⟪A y u,u⟫_ℝ :=
    fixedFrameOperator_coercive T hT (Q y) (Q₁ y) (H y) c hc (hLower y) (hd y)
      K hK (hPotential y) hsmall u
  let inv := fun y => coerciveInverse (A y) (δ y) (hδ y) (hco y)
  have hA : ContDiff ℝ ∞ A := contDiff_fixedFrameOperator T hT Q Q₁ H hQ hQ₁ hH
  have hJ : ContDiff ℝ ∞ J :=
    (contDiff_adjoint (contDiff_fixedFramePrimitive T hT Q Q₁ hQ hQ₁)).neg
  have hv : ContDiff ℝ ∞ v := contDiff_fixedFrameSolution T hT Q Q₁ H c hc hLower hd
    K hK hPotential hsmall hQ hQ₁ hH f hf
  have hrhs : ContDiff ℝ ∞ rhs := hJ.clm_apply hf
  have heq (y : X) : A y (v y) = rhs y :=
    operator_inverse_apply (A y) (δ y) (hδ y) (hco y) (rhs y)
  have hinv (y : X) : ‖inv y‖ ≤ inverseCost T C₀ C₁ c := by
    apply (coerciveInverse_norm_le (A y) (δ y) (hδ y) (hco y)).trans
    apply fixedCoercivity_inv_le T hT (Q y) (Q₁ y) c hc C₀ C₁
    · simpa only [norm_iteratedFDeriv_zero,majorant,Nat.add_zero,pow_zero,
        Nat.factorial_zero,Nat.cast_one,one_pow,mul_one] using hbQ 0 y
    · simpa only [norm_iteratedFDeriv_zero,majorant,Nat.add_zero,pow_zero,
        Nat.factorial_zero,Nat.cast_one,one_pow,mul_one] using hbQ₁ 0 y
  have hCA : 0 ≤ formCost T C₀ C₁ CH := by unfold formCost; positivity
  have hCJ : 0 ≤ T*derivativeCost T C₀ C₁ := by unfold derivativeCost; positivity
  have hJA : 0 ≤ sobolevCoefficientAmplitude ι q Rc (T*derivativeCost T C₀ C₁) :=
    sobolevCoefficientAmplitude_nonneg q Rc _ hRc hCJ
  have hM := blockCost_one_le ι q T Rc C₀ C₁ CH c Cf hT hRc hC₀ hC₁ hCH hCf
  have hr0 := sobolevCoefficientRadius_nonneg (ι := ι) Rc hRc
  have hrR : sobolevCoefficientRadius ι Rc ≤ R := by nlinarith
  have hAb (k y) : ‖iteratedFDeriv ℝ k A y‖ ≤ formCost T C₀ C₁ CH*majorant Rc 0 k :=
    fixedFrameOperator_bound T hT Q Q₁ H hQ hQ₁ hH Rc C₀ C₁ CH hRc hC₀ hC₁ hCH hbQ hbQ₁ hbH k y
  have hJb (k y) : ‖iteratedFDeriv ℝ k J y‖ ≤ (T*derivativeCost T C₀ C₁)*majorant Rc 0 k :=
    forcingOperator_bound T hT Q Q₁ hQ hQ₁ Rc C₀ C₁ hRc hC₀ hC₁ hbQ hbQ₁ k y
  have hJB (k y) : coefficientBlock directions q J k y ≤
      sobolevCoefficientAmplitude ι q Rc (T*derivativeCost T C₀ C₁) *
        majorant (sobolevCoefficientRadius ι Rc) 0 k :=
    coefficientBlock_of_tensor_bound directions hdir q J hJ Rc _ hRc hCJ hJb k y
  have hrhsb (k y) : block directions q rhs k y ≤
      forcingBlockAmplitude ι q T Rc C₀ C₁ Cf*majorant R d k :=
    block_clm_apply_gevrey directions q J f hJ hf (sobolevCoefficientRadius ι Rc) R
      (sobolevCoefficientAmplitude ι q Rc (T*derivativeCost T C₀ C₁)) Cf
      hr0 hrR hJA hCf hJB d hfb k y
  exact inverse_block_gevrey_of_tensor directions hdir q A v rhs hA hv hrhs heq inv
    (fun y u => inverse_operator_apply (A y) (δ y) (hδ y) (hco y) u)
    (inverseCost T C₀ C₁ c) Rc (formCost T C₀ C₁ CH) (forcingBlockAmplitude ι q T Rc C₀ C₁ Cf) R
    hRc hCA (forcingBlockAmplitude_nonneg ι q T Rc C₀ C₁ Cf hT hRc hC₀ hC₁ hCf)
    hinv hAb hR d hrhsb n x

/-- Forgetting the zero-trace subtype is a contraction, so the actual
coordinate L² velocity has the identical word estimate. -/
theorem velocityLp_block_gevrey (f : X → TimeLp T E) (hf : ContDiff ℝ ∞ f) (d : ℕ)
    (hfb : ∀ n x, block directions q f n x ≤ Cf * majorant R d n) (n : ℕ) (x : X) :
    block directions q (fun y => EulerTransverseFixedEvolution.velocityLp T hT (Q y) (Q₁ y) (H y)
      c hc (hLower y) (hd y) K hK (hPotential y) hsmall (f y)) n x ≤ majorant R (d+1) n := by
  let v := fun y => fixedFrameSolver T hT (Q y) (Q₁ y) (H y)
    c hc (hLower y) (hd y) K hK (hPotential y) hsmall (f y)
  have hv : ContDiff ℝ ∞ v := contDiff_fixedFrameSolution T hT Q Q₁ H c hc hLower hd
    K hK hPotential hsmall hQ hQ₁ hH f hf
  have hb := solver_block_gevrey directions hdir q T hT Q Q₁ H c hc hLower hd K hK hPotential hsmall
    hQ hQ₁ hH Rc C₀ C₁ CH Cf R hRc hC₀ hC₁ hCH hCf hbQ hbQ₁ hbH hR f hf d hfb n x
  have h := block_comp_clm_le directions q (zeroTraceDerivatives (U := U) T hT).subtypeL v hv n x
  apply h.trans
  exact (mul_le_mul_of_nonneg_right (zeroTraceDerivatives (U := U) T hT).norm_subtypeL_le
    (block_nonneg directions q v n x)).trans (by simpa only [one_mul] using hb)

end EulerTransverseFixedSobolev
