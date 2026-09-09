/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryIterated

@[expose] public section

/-! Factorial bounds for actual spatial derivatives of the localized Newtonian operator family. -/

noncomputable section


namespace EulerMeanBoundary

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerMeanGradientTest
  EulerMeanCutoffCurl EulerGevrey Finset
open scoped ContDiff

theorem majorant_four_radius (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    majorant R 0 n ≤ majorant (4*R) 0 n := by
  unfold majorant
  simp only [Nat.add_zero]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR (by linarith) n) (sq_nonneg _)

/-- One extra derivative costs a fixed factor in the Gevrey radius, not a factorial shift. -/
theorem majorant_next_four_radius (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    majorant R 0 (n+1) ≤ R * majorant (4*R) 0 n := by
  have hs : ((n : ℝ)+1)^2 ≤ (4 : ℝ)^n := by
    calc
      _ ≤ ((2 : ℝ)^n)^2 := pow_le_pow_left₀ (by positivity)
        (EulerPacketUniformScaleSums.stage_count_le_two_pow n) 2
      _ = _ := by rw [← pow_mul, Nat.mul_comm n 2, pow_mul]; norm_num
  have H := mul_le_mul_of_nonneg_left hs
    (mul_nonneg (mul_nonneg hR (pow_nonneg hR n)) (sq_nonneg (n.factorial : ℝ)))
  unfold majorant
  simp only [Nat.add_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    pow_succ, mul_pow]
  nlinarith only [H]

def cutoffGevreyAmplitude (supportRadius coefficientRadius coefficientSize : ℝ) : ℝ :=
  3 * cutoffCurlConstant * coefficientSize *
    (1 + coefficientRadius *
      (volume (Metric.closedBall (0 : Space) supportRadius)).toReal ^ (1/3 : ℝ))

theorem cutoffGevreyAmplitude_nonneg (R Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) :
    0 ≤ cutoffGevreyAmplitude R Rc C := by
  unfold cutoffGevreyAmplitude
  have h := cutoffCurlConstant_pos.le
  positivity

section LinearCutoffOperation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cutoffOperation_gevrey (L : Cutoff → E)
    (hadd : ∀ χ ψ, L (χ.add ψ) = L χ + L ψ)
    (hsmul : ∀ χ c, L (χ.scale c) = c • L χ)
    (hsub : ∀ χ ψ, L (χ.sub ψ) = L χ - L ψ)
    (hbound : ∀ χ, ‖L χ‖ ≤ cutoffBound χ)
    (χ : Cutoff) (R Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hs : tsupport χ.field ⊆ Metric.closedBall (0 : Space) R)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n χ.field x‖ ≤ C * majorant Rc 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => L (χ.translate b)) a‖ ≤
      cutoffGevreyAmplitude R Rc C * majorant (4*Rc) 0 n := by
  have H := cutoffOperation_iteratedFDeriv_bound L hadd hsmul hsub hbound n χ R
    (C * majorant Rc 0 n) (C * majorant Rc 0 (n+1))
    (mul_nonneg hC (majorant_nonneg Rc hRc _ _))
    (mul_nonneg hC (majorant_nonneg Rc hRc _ _)) hs (hb n) (hb (n+1)) a
  have hV : 0 ≤ (volume (Metric.closedBall (0 : Space) R)).toReal ^ (1/3 : ℝ) := by positivity
  have hinner := add_le_add
    (mul_le_mul_of_nonneg_left (majorant_four_radius Rc hRc n) hC)
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (majorant_next_four_radius Rc hRc n) hC) hV)
  apply H.trans
  calc
    _ ≤ 3 * cutoffCurlConstant *
        (C * majorant (4*Rc) 0 n + C * (Rc * majorant (4*Rc) 0 n) *
          (volume (Metric.closedBall (0 : Space) R)).toReal ^ (1/3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hinner (mul_nonneg (by norm_num) cutoffCurlConstant_pos.le)
    _ = _ := by unfold cutoffGevreyAmplitude; ring

end LinearCutoffOperation

theorem cutoffCurl_gevrey (χ : Cutoff) (R Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hs : tsupport χ.field ⊆ Metric.closedBall (0 : Space) R)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n χ.field x‖ ≤ C * majorant Rc 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => cutoffCurl (χ.translate b)) a‖ ≤
      cutoffGevreyAmplitude R Rc C * majorant (4*Rc) 0 n :=
  cutoffOperation_gevrey cutoffCurl cutoffCurl_add cutoffCurl_scale cutoffCurl_sub
    cutoffCurl_norm_le χ R Rc C hRc hC hs hb n a

theorem weakPotential_gevrey (χ : Cutoff) (R Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hs : tsupport χ.field ⊆ Metric.closedBall (0 : Space) R)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n χ.field x‖ ≤ C * majorant Rc 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => weakPotential (χ.translate b)) a‖ ≤
      cutoffGevreyAmplitude R Rc C * majorant (4*Rc) 0 n :=
  cutoffOperation_gevrey weakPotential weakPotential_add weakPotential_scale weakPotential_sub
    weakPotential_operatorNorm_le χ R Rc C hRc hC hs hb n a

/-- The true derivatives split between the two cutoff positions by the bilinear derivative rule. -/
theorem mixedBoundaryOperator_iteratedFDeriv_le (χ ψ : Cutoff) (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n
      (fun b : Space => mixedBoundaryOperator (χ.translate b) (ψ.translate b)) a‖ ≤
      ∑ k ∈ range (n+1), (n.choose k : ℝ) *
        ‖iteratedFDeriv ℝ k (fun b : Space => cutoffCurl (χ.translate b)) a‖ *
        ‖iteratedFDeriv ℝ (n-k) (fun b : Space => weakPotential (ψ.translate b)) a‖ := by
  have h :=
    (ContinuousLinearMap.compL ℝ L2 homogeneousSpace
      L2).norm_iteratedFDeriv_le_of_bilinear_of_le_one
      (f := fun b : Space => cutoffCurl (χ.translate b))
      (g := fun b : Space => weakPotential (ψ.translate b))
      (cutoffCurl_contDiff χ) (weakPotential_contDiff ψ) a (n := n) (by simp)
      (by
        convert ContinuousLinearMap.norm_compL_le ℝ L2 homogeneousSpace L2 using 1)
  exact h

/-- Factorial estimates follow from the genuine operator family, at every order and parameter. -/
theorem mixedBoundaryOperator_gevrey (χ ψ : Cutoff) (Rχ Rψ Rc Cχ Cψ : ℝ)
    (hRc : 0 ≤ Rc) (hCχ : 0 ≤ Cχ) (hCψ : 0 ≤ Cψ)
    (hsχ : tsupport χ.field ⊆ Metric.closedBall (0 : Space) Rχ)
    (hsψ : tsupport ψ.field ⊆ Metric.closedBall (0 : Space) Rψ)
    (hbχ : ∀ n x, ‖iteratedFDeriv ℝ n χ.field x‖ ≤ Cχ * majorant Rc 0 n)
    (hbψ : ∀ n x, ‖iteratedFDeriv ℝ n ψ.field x‖ ≤ Cψ * majorant Rc 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n
      (fun b : Space => mixedBoundaryOperator (χ.translate b) (ψ.translate b)) a‖ ≤
      3 * cutoffGevreyAmplitude Rχ Rc Cχ * cutoffGevreyAmplitude Rψ Rc Cψ *
        majorant (4*Rc) 0 n := by
  have H := sequence_product_majorant (4*Rc)
    (cutoffGevreyAmplitude Rχ Rc Cχ) (cutoffGevreyAmplitude Rψ Rc Cψ)
    (mul_nonneg (by norm_num) hRc)
    (cutoffGevreyAmplitude_nonneg Rχ Rc Cχ hRc hCχ)
    (cutoffGevreyAmplitude_nonneg Rψ Rc Cψ hRc hCψ) 0 0
    (fun k => ‖iteratedFDeriv ℝ k (fun b : Space => cutoffCurl (χ.translate b)) a‖)
    (fun k => ‖iteratedFDeriv ℝ k (fun b : Space => weakPotential (ψ.translate b)) a‖)
    (fun k => by
      rw [abs_of_nonneg (norm_nonneg _)]
      exact cutoffCurl_gevrey χ Rχ Rc Cχ hRc hCχ hsχ hbχ k a)
    (fun k => by
      rw [abs_of_nonneg (norm_nonneg _)]
      exact weakPotential_gevrey ψ Rψ Rc Cψ hRc hCψ hsψ hbψ k a) n
  exact (mixedBoundaryOperator_iteratedFDeriv_le χ ψ n a).trans ((le_abs_self _).trans H)

end EulerMeanBoundary
