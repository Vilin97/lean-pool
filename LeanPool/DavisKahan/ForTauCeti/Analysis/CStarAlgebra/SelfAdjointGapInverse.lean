/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-!
# Norm and inverse bounds from real spectral position

Two consequences of where a self-adjoint element sits on the real line:

* `TauCeti.IsSelfAdjoint.norm_le_iff_spectrum_subset_Icc`: `‖a‖ ≤ r` **iff** the real
  spectrum is contained in `[-r, r]`. This is the isometric continuous functional
  calculus specialized to the identity function.
* `TauCeti.isUnit_of_forall_le_abs` and
  `TauCeti.IsSelfAdjoint.norm_ringInverse_le`: if the real spectrum avoids the open
  interval `(-r, r)` then `a` is a unit whose inverse has norm at most `r⁻¹`.

Invertibility needs no self-adjointness and no norm: it is exactly
`spectrum.isUnit_of_zero_notMem`, since a spectral gap around `0` in particular keeps
`0` out of the spectrum. Only the quantitative bound on the inverse uses the
functional calculus.

These are the analytic inputs to the constant-one interval/exterior Sylvester estimate
for the Davis--Kahan `sin Θ` theorem (shift-and-invert argument).

Proposed Mathlib destinations: the two norm results belong beside `norm_cfc_le_iff` in
`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Isometric.lean`.
`isUnit_of_forall_le_abs` uses no analysis and belongs instead near
`spectrum.zero_notMem_iff` in `Mathlib/Algebra/Algebra/Spectrum/Basic.lean`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib/Analysis/CStarAlgebra/SelfAdjointGapInverse.lean`
  at Davis--Kahan commit `fc38eb4`.
* Original declarations: `ForMathlib.IsSelfAdjoint.norm_le_of_spectrum_subset_Icc`,
  `ForMathlib.IsSelfAdjoint.exists_two_sided_inverse_of_spectrum_gap`
  (namespace renamed `ForMathlib` → `TauCeti`).
* Extraction class: **copied**, converted to the Tau Ceti module system, then
  redesigned for upstreaming (backlog §9.1): the norm bound was strengthened to an
  iff, and the bundled existential `∃ j, j * a = 1 ∧ a * j = 1 ∧ ‖j‖ ≤ r⁻¹` was split
  into an `IsUnit` statement and a norm bound on the canonical `Ring.inverse`.
* Spectra influence: **none** (imports only Mathlib).
-/

public section

namespace TauCeti

section Unit

variable {A : Type*} [Ring A] [Algebra ℝ A] {a : A} {r : ℝ}

/-- An element whose real spectrum is bounded away from `0` is a unit.

Neither self-adjointness nor a norm is needed: the hypothesis is used only to rule out
`0 ∈ spectrum ℝ a`. -/
theorem isUnit_of_forall_le_abs (hr : 0 < r) (hσ : ∀ x ∈ spectrum ℝ a, r ≤ |x|) :
    IsUnit a := by
  refine spectrum.isUnit_of_zero_notMem ℝ fun h => ?_
  have h0 := hσ 0 h
  rw [abs_zero] at h0
  linarith

end Unit

variable {A : Type*} [CStarAlgebra A] {a : A} {r : ℝ}

/-- A self-adjoint element of a C⋆-algebra has norm at most `r` exactly when its real
spectrum is contained in `[-r, r]`. -/
theorem IsSelfAdjoint.norm_le_iff_spectrum_subset_Icc (ha : IsSelfAdjoint a) (hr : 0 ≤ r) :
    ‖a‖ ≤ r ↔ spectrum ℝ a ⊆ Set.Icc (-r) r := by
  conv_lhs => rw [← cfc_id ℝ a]
  rw [norm_cfc_le_iff (id : ℝ → ℝ) a hr]
  simp [Set.subset_def, Set.mem_Icc, Real.norm_eq_abs, abs_le]

/-- If the real spectrum of a self-adjoint element avoids the open interval `(-r, r)`,
its inverse has norm at most `r⁻¹`.

`TauCeti.isUnit_of_forall_le_abs` supplies the invertibility, so `Ring.inverse a` is a
genuine two-sided inverse here. -/
theorem IsSelfAdjoint.norm_ringInverse_le (ha : IsSelfAdjoint a) (hr : 0 < r)
    (hσ : ∀ x ∈ spectrum ℝ a, r ≤ |x|) : ‖Ring.inverse a‖ ≤ r⁻¹ := by
  rw [← cfc_ringInverse_id (R := ℝ) a (isUnit_of_forall_le_abs hr hσ)]
  refine norm_cfc_le (by positivity) fun x hx => ?_
  rw [Real.norm_eq_abs, abs_inv]
  exact inv_anti₀ hr (hσ x hx)

end TauCeti
