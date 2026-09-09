/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseStrongEstimates

@[expose] public section

/-!
# Continuous acceleration from the genuine Gram inverse

A continuous velocity and continuous forcing give an actual continuous
acceleration path through the previously constructed positive Gram inverse.
Its norm and its identification with the strong L² acceleration are proved
directly, for arbitrary complete real Hilbert coefficient spaces.
-/

noncomputable section

namespace EulerContinuousGramAcceleration

open Set MeasureTheory ContinuousLinearMap EulerTimeLp EulerVolterraConvolution
  EulerTransverseGramInverse EulerTransverseGramPath EulerTransverseStrongEstimates

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t v, c*‖v‖^2 ≤ ‖Q t v‖^2)

/-- The actual continuous acceleration recovered from velocity and forcing. -/
def accelerationPath (v : C(Icc (0 : ℝ) T, U)) (f : C(Icc (0 : ℝ) T, E)) :
    C(Icc (0 : ℝ) T, U) :=
  ⟨fun t => gramInverse (Q t) c hc (hQ t)
      ((Q t).adjoint (f t-(2 : ℝ) • Q₁ t (v t))),
    (gramInversePath T Q c hc hQ).continuous.clm_apply
      ((adjointPath T Q).continuous.clm_apply
        (f.continuous.sub ((Q₁.continuous.clm_apply v.continuous).const_smul (2 : ℝ))))⟩

@[simp] theorem accelerationPath_apply (v : C(Icc (0 : ℝ) T, U))
    (f : C(Icc (0 : ℝ) T, E)) (t : Icc (0 : ℝ) T) :
    accelerationPath T Q Q₁ c hc hQ v f t =
      gramInverse (Q t) c hc (hQ t) ((Q t).adjoint (f t-(2 : ℝ) • Q₁ t (v t))) := rfl

/-- The strong projected equation holds at every time for this path. -/
theorem accelerationPath_equation (v : C(Icc (0 : ℝ) T, U))
    (f : C(Icc (0 : ℝ) T, E)) (t : Icc (0 : ℝ) T) :
    gram (Q t) (accelerationPath T Q Q₁ c hc hQ v f t) =
      (Q t).adjoint (f t-(2 : ℝ) • Q₁ t (v t)) :=
  gram_inverse_apply (Q t) c hc (hQ t) _

/-- The continuous acceleration has the same explicit coefficient bound as the L² inverse. -/
theorem accelerationPath_norm (v : C(Icc (0 : ℝ) T, U))
    (f : C(Icc (0 : ℝ) T, E)) :
    ‖accelerationPath T Q Q₁ c hc hQ v f‖ ≤
      c⁻¹*‖Q‖*(‖f‖+2*‖Q₁‖*‖v‖) := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro t
  have hQv : ‖Q₁ t (v t)‖ ≤ ‖Q₁‖*‖v‖ :=
    ((Q₁ t).le_opNorm _).trans
      (mul_le_mul (Q₁.norm_coe_le_norm t) (v.norm_coe_le_norm t) (norm_nonneg (v t)) (norm_nonneg
        Q₁))
  have hr : ‖f t-(2 : ℝ) • Q₁ t (v t)‖ ≤ ‖f‖+2*‖Q₁‖*‖v‖ := by
    calc
      _ ≤ ‖f t‖+‖(2 : ℝ) • Q₁ t (v t)‖ := norm_sub_le _ _
      _ = ‖f t‖+2*‖Q₁ t (v t)‖ := by norm_num only [norm_smul, Real.norm_ofNat]
      _ ≤ ‖f‖+2*(‖Q₁‖*‖v‖) :=
        add_le_add (f.norm_coe_le_norm t) (mul_le_mul_of_nonneg_left hQv (by norm_num))
      _ = _ := by ring
  have hAdj : ‖(Q t).adjoint‖ ≤ ‖Q‖ := by
    simpa only [LinearIsometryEquiv.norm_map] using Q.norm_coe_le_norm t
  calc
    _ ≤ ‖gramInverse (Q t) c hc (hQ t)‖ *
        ‖(Q t).adjoint (f t-(2 : ℝ) • Q₁ t (v t))‖ :=
      (gramInverse (Q t) c hc (hQ t)).le_opNorm _
    _ ≤ c⁻¹*(‖Q‖*‖f t-(2 : ℝ) • Q₁ t (v t)‖) :=
      mul_le_mul (gramInverse_norm (Q t) c hc (hQ t))
        (((Q t).adjoint.le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hAdj (norm_nonneg _)))
        (norm_nonneg _) (inv_nonneg.mpr hc.le)
    _ ≤ c⁻¹*(‖Q‖*(‖f‖+2*‖Q₁‖*‖v‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr (norm_nonneg Q)) (inv_nonneg.mpr
        hc.le)
    _ = _ := by ring

/-- Every genuine L² strong acceleration with the given continuous data is
almost everywhere this constructed continuous path. -/
theorem accelerationPath_ae (hT : 0 ≤ T) (v a : TimeLp T U) (f : TimeLp T E)
    (vC : C(Icc (0 : ℝ) T, U)) (fC : C(Icc (0 : ℝ) T, E))
    (hv : (v : ℝ → U) =ᵐ[timeMeasure T] extendPath T hT vC)
    (hf : (f : ℝ → E) =ᵐ[timeMeasure T] extendPath T hT fC)
    (heq : ∀ᵐ t ∂timeMeasure T, gram (extendPath T hT Q t) (a t) =
      (extendPath T hT Q t).adjoint (f t-(2 : ℝ) • extendPath T hT Q₁ t (v t))) :
    (a : ℝ → U) =ᵐ[timeMeasure T] extendPath T hT (accelerationPath T Q Q₁ c hc hQ vC fC) := by
  filter_upwards [heq, hv, hf] with t ht hvt hft
  dsimp only [extendPath] at ht hvt hft ⊢
  have hi := congrArg (gramInverse (Q (projIcc 0 T hT t)) c hc (hQ _)) ht
  rw [inverse_gram_apply, hvt, hft] at hi
  exact hi

end EulerContinuousGramAcceleration
