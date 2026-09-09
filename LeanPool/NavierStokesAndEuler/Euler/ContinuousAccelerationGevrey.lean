/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ContinuousGramAcceleration
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousGramGevrey
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousAccelerationForcing

@[expose] public section

/-!
# Uniform-time regularity of actual acceleration

The continuous acceleration is the already constructed Gram inverse applied
to its literal forcing. Smoothness and factorial estimates therefore apply
to the actual continuous path, including its endpoint values.
-/

noncomputable section

namespace EulerContinuousAccelerationGevrey

open Set ContinuousLinearMap EulerContinuousGramAcceleration
  EulerContinuousGramPath EulerContinuousGramGevrey EulerContinuousAccelerationForcing
  EulerOperatorGevreyCalculus EulerTimeLpGramGevrey EulerGevrey
open scoped ContDiff

variable {P U E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (Q Q₁ : P → C(Icc (0 : ℝ) T,U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hLower : ∀ x t v, c*‖v‖^2 ≤ ‖Q x t v‖^2)
  (v : P → C(Icc (0 : ℝ) T,U)) (f : P → C(Icc (0 : ℝ) T,E))

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The continuous acceleration is the genuine continuous Gram solve. -/
theorem acceleration_eq_solve :
    (fun x => accelerationPath T (Q x) (Q₁ x) c hc (hLower x) (v x) (f x)) =
      fun x => solve T (Q x) c hc (hLower x) (forcing Q Q₁ f v x) := by
  funext x
  apply ContinuousMap.ext
  intro t
  rfl

/-- Actual uniform-time acceleration depends smoothly on the actual coefficients and data. -/
theorem acceleration_contDiff {n : ℕ∞ω}
    (hQ : ContDiff ℝ n Q) (hQ₁ : ContDiff ℝ n Q₁)
    (hv : ContDiff ℝ n v) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => accelerationPath T (Q x) (Q₁ x) c hc (hLower x) (v x) (f x)) :=
  Eq.mpr (congrArg (fun g : P → C(Icc (0 : ℝ) T,U) => ContDiff ℝ n g)
    (acceleration_eq_solve T Q Q₁ c hc hLower v f))
    (solve_contDiff T c hc Q hLower (forcing Q Q₁ f v) hQ
      (forcing_contDiff Q Q₁ f v hQ hQ₁ hf hv))

/-- The actual continuous acceleration has one factorial shift relative to
its velocity and forcing data, with a polynomial radius condition. -/
theorem acceleration_gevrey
    (hQ : ContDiff ℝ ∞ Q) (hQ₁ : ContDiff ℝ ∞ Q₁)
    (hv : ContDiff ℝ ∞ v) (hf : ContDiff ℝ ∞ f)
    (Rc R C₀ C₁ Cf Cv : ℝ) (hRc : 0 ≤ Rc) (hR : 0 ≤ R) (hRcR : Rc ≤ R)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hCf : 0 ≤ Cf) (hCv : 0 ≤ Cv)
    (hstrong : 2*gramCost c C₀ (3*C₀*(Cf+6*C₁*Cv))*(Rc+1) ≤ R)
    (hQb : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C₀*majorant Rc 0 n)
    (hQ₁b : ∀ n x, ‖iteratedFDeriv ℝ n Q₁ x‖ ≤ C₁*majorant Rc 0 n)
    (d : ℕ)
    (hfb : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ Cf*majorant R d n)
    (hvb : ∀ n x, ‖iteratedFDeriv ℝ n v x‖ ≤ Cv*majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n
      (fun y => accelerationPath T (Q y) (Q₁ y) c hc (hLower y) (v y) (f y)) x‖ ≤
      majorant R (d+1) n := by
  have hbQR (k y) : ‖iteratedFDeriv ℝ k Q y‖ ≤ C₀*majorant R 0 k :=
    (hQb k y).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc R hRc hRcR 0 k) hC₀)
  have hbQ₁R (k y) : ‖iteratedFDeriv ℝ k Q₁ y‖ ≤ C₁*majorant R 0 k :=
    (hQ₁b k y).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc R hRc hRcR 0 k) hC₁)
  let g := forcing Q Q₁ f v
  have hg : ContDiff ℝ ∞ g := forcing_contDiff Q Q₁ f v hQ hQ₁ hf hv
  have hgb : ∀ k y, ‖iteratedFDeriv ℝ k g y‖ ≤ (3*C₀*(Cf+6*C₁*Cv))*majorant R d k :=
    forcing_bound Q Q₁ f v hQ hQ₁ hf hv R C₀ C₁ Cf Cv hR hC₀ hC₁ hCf hCv d
      hbQR hbQ₁R hfb hvb
  have hs := EulerContinuousGramGevrey.solution_gevrey T Q c hc hLower hQ
    Rc C₀ hRc hC₀ hQb g hg (3*C₀*(Cf+6*C₁*Cv)) R (by positivity) hstrong d hgb n x
  exact (congrArg (fun g : P → C(Icc (0 : ℝ) T,U) => ‖iteratedFDeriv ℝ n g x‖)
    (acceleration_eq_solve T Q Q₁ c hc hLower v f)).trans_le hs

end EulerContinuousAccelerationGevrey
