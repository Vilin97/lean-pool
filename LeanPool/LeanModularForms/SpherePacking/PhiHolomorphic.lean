/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.Modularforms.EtaCleanup

/-!
# Holomorphicity of E₂ and φ₀ on the upper half-plane

E₂ is holomorphic because `E₂ = (πI/12)⁻¹ · logDeriv(η)` where η is
the Dedekind eta function. Since η is holomorphic and nonvanishing on ℍ,
`logDeriv(η)` is holomorphic, hence E₂ is holomorphic.
-/

open UpperHalfPlane Set Filter Topology Function
open scoped Real

noncomputable section

/-- The Dedekind eta function is differentiable on ℍ (as a function ℂ → ℂ). -/
theorem dedekindEtaFun'_differentiableOn :
    DifferentiableOn ℂ dedekindEtaFun' {z : ℂ | 0 < z.im} :=
  fun z hz => (eta_DifferentiableAt_UpperHalfPlane' ⟨z, hz⟩).differentiableWithinAt

/-- The Dedekind eta function is nonzero on ℍ. -/
theorem dedekindEtaFun'_ne_zero_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    dedekindEtaFun' z ≠ 0 := by
  simpa [dedekindEtaFun', Periodic.qParam] using etaProdTerm_ne_zero ⟨z, hz⟩

/-- `logDeriv(η)` is differentiable on ℍ. -/
theorem logDeriv_eta_differentiableOn :
    DifferentiableOn ℂ (logDeriv dedekindEtaFun') {z : ℂ | 0 < z.im} :=
  (dedekindEtaFun'_differentiableOn.deriv isOpen_upperHalfPlaneSet).div
    dedekindEtaFun'_differentiableOn
    (fun _ hz => dedekindEtaFun'_ne_zero_of_im_pos hz)

/-- E₂ is holomorphic on the upper half-plane.
Proof: `logDeriv(η) = (π·I/12) · E₂` by `eta_logDeriv'`, so
`E₂ = (π·I/12)⁻¹ · logDeriv(η)` is holomorphic. -/
theorem E₂_differentiableOn :
    DifferentiableOn ℂ (E₂ ∘ ofComplex) {z : ℂ | 0 < z.im} := by
  apply DifferentiableOn.congr
    ((differentiableOn_const ((↑Real.pi * Complex.I / 12)⁻¹)).mul logDeriv_eta_differentiableOn)
  intro z hz
  simp only [comp, ofComplex_apply_of_im_pos hz, Pi.mul_apply]
  have h := eta_logDeriv' ⟨z, hz⟩
  have hpi : (↑Real.pi : ℂ) * Complex.I / 12 ≠ 0 := by
    apply div_ne_zero
    · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) Complex.I_ne_zero
    · norm_num
  change logDeriv dedekindEtaFun' z = _ at h
  rw [h, inv_mul_cancel_left₀ hpi]

end
