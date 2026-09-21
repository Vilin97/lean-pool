/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Carlson.L.Basic
public import LeanPool.CarlsonFunctions.Carlson.R.JointParameter
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.Derivatives

/-!
# Carlson's L-function: entire regularized continuation

The continued L-function is the exponent derivative of the continued R-function.
Joint entireness of R proves joint entireness of L, not merely separate
existence of derivatives. This establishes the parameter part of Carlson (1987),
(2.1), for arbitrary complex Dirichlet parameters. This module retains the original
right-half-plane node interface. `Carlson.L.SlitContinuation` extends it to the full
product slit plane and proves joint holomorphy in all arguments.
-/

open Complex ProbabilityTheory
open scoped Classical
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The exponent derivative of the entire regularized R-continuation. -/
def regCarlsonLContinued (t : ℂ) (z : ι → ℂ) (hz : z ∈ carlsonRVariableDomain)
    (b : ι → ℂ) : ℂ := deriv (fun s => regCarlsonRContinued s z hz b) t

/-- The normalized L-continuation. At poles of `Γ(∑ i, b i)` this is only
Lean's totalized expression; the entire object is `regCarlsonLContinued`. -/
def carlsonLContinued (t : ℂ) (z : ι → ℂ) (hz : z ∈ carlsonRVariableDomain)
    (b : ι → ℂ) : ℂ := Gamma (∑ i, b i) * regCarlsonLContinued t z hz b

/-- The derivative characterization holds at every complex Dirichlet parameter. -/
theorem hasDerivAt_regCarlsonRContinued_L (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    HasDerivAt (fun s => regCarlsonRContinued s z hz b)
      (regCarlsonLContinued t z hz b) t :=
  (analyticAt_regCarlsonRContinued_comp hz analyticAt_id analyticAt_const).differentiableAt.hasDerivAt

/-- Joint entireness in the exponent and the Dirichlet parameters, including
nonpositive integral parameters and totals. -/
theorem analyticOnNhd_regCarlsonLContinued_exponent_parameters {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) :
    AnalyticOnNhd ℂ (fun p : Option ι → ℂ =>
      regCarlsonLContinued (p none) z hz (fun i => p (some i))) Set.univ := by
  have h := (analyticOnNhd_regCarlsonRContinued_exponent_parameters hz).partialDeriv
    isOpen_univ none
  have heq : SeveralComplexVariables.partialDeriv none
      (fun p : Option ι → ℂ => regCarlsonRContinued (p none) z hz (fun i => p (some i))) =
      (fun p : Option ι → ℂ => regCarlsonLContinued (p none) z hz (fun i => p (some i))) := by
    funext p
    simp only [SeveralComplexVariables.partialDeriv, regCarlsonLContinued,
      Function.update_self, Function.update_of_ne (Option.some_ne_none _)]
  rwa [heq] at h

/-- Analytic substitutions in the exponent and parameters preserve analyticity. -/
theorem analyticAt_regCarlsonLContinued_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {b : E → ι → ℂ} {p : E} {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) (hf : AnalyticAt ℂ f p) (hb : AnalyticAt ℂ b p) :
    AnalyticAt ℂ (fun w => regCarlsonLContinued (f w) z hz (b w)) p := by
  let g : E → Option ι → ℂ := fun w i => i.elim (f w) (b w)
  have hg : AnalyticAt ℂ g p := by
    apply analyticAt_pi_iff.mpr
    intro i
    cases i with
    | none => exact hf
    | some i => exact (analyticAt_pi_iff.mp hb) i
  exact (analyticOnNhd_regCarlsonLContinued_exponent_parameters hz (g p)
    (Set.mem_univ _)).comp hg

theorem analyticOnNhd_regCarlsonLContinued (t : ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) :
    AnalyticOnNhd ℂ (regCarlsonLContinued t z hz) Set.univ :=
  fun _ _ => analyticAt_regCarlsonLContinued_comp hz analyticAt_const analyticAt_id

/-- On the convergence region the continued function equals the power-log integral. -/
theorem regCarlsonLContinued_eq_integral (t : ℂ) {b z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) (hb : b ∈ mvBetaConvergent) :
    regCarlsonLContinued t z hz b = regCarlsonLIntegral t b z := by
  unfold regCarlsonLContinued
  simp_rw [regCarlsonRContinued_eq_integral _ hz hb]
  exact (hasDerivAt_regCarlsonRIntegral_L t hb hz).deriv

/-- L satisfies the existing general Dirichlet-continuation specification. -/
theorem isRegCarlsonLContinuation_continued (t : ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) :
    IsRegCarlsonContinuation (carlsonLKernel t) z (regCarlsonLContinued t z hz) :=
  ⟨analyticOnNhd_regCarlsonLContinued t hz,
    fun _ hb => regCarlsonLContinued_eq_integral t hz hb⟩

/-- Any entire continuation of the native L-integral is the selected L-function. -/
theorem IsRegCarlsonContinuation.eq_regCarlsonLContinued {t : ℂ} {z : ι → ℂ}
    {G : (ι → ℂ) → ℂ} (hG : IsRegCarlsonContinuation (carlsonLKernel t) z G)
    (hz : z ∈ carlsonRVariableDomain) : G = regCarlsonLContinued t z hz :=
  hG.eq (isRegCarlsonLContinuation_continued t hz)

theorem carlsonLContinued_eq_integral (t : ℂ) {b z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) (hb : b ∈ mvBetaConvergent) :
    carlsonLContinued t z hz b = carlsonLIntegral t b z := by
  simp only [carlsonLContinued, carlsonLIntegral, regCarlsonLContinued_eq_integral t hz hb]

end DirichletTransform
end
