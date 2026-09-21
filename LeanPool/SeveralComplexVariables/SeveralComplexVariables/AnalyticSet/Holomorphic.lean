/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.AnalyticSet.Basic
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Biholomorphic

/-!
# Holomorphic equations and biholomorphic transport of analytic sets

On open finite-dimensional complex domains, holomorphic finite-coordinate equations define
analytic subsets. Biholomorphic changes of ambient coordinates preserve analytic subsets. These
results use the holomorphy–analyticity equivalence and are separated from `AnalyticSet.Basic` so
that the definition and elementary analytic-set operations do not import holomorphic mapping
theory.

References: [Range][Range1986] I §3.2; [Fritzsche–Grauert][FritzscheGrauert2002] I §8;
[Scheidemann][Scheidemann2005] §4.1.

## Main results

* `isAnalyticSet_zeroSet_pi_of_differentiableOn`: Holomorphic finite-coordinate equations on an open
  finite-dimensional domain define an analytic subset, using Mathlib's equivalence of holomorphy and
  analyticity.
* `IsAnalyticSet.image_biholomorphic`: Biholomorphic changes of ambient coordinates preserve
  analytic subsets.

## References

* [K. Fritzsche and H. Grauert, *From Holomorphic Functions to Complex
  Manifolds*][FritzscheGrauert2002]
* [R. M. Range, *Holomorphic Functions and Integral Representations in Several Complex
  Variables*][Range1986]
* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public noncomputable section

open Set

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Holomorphic finite-coordinate equations on an open finite-dimensional domain define an analytic
subset, using Mathlib's equivalence of holomorphy and analyticity. -/
theorem isAnalyticSet_zeroSet_pi_of_differentiableOn [FiniteDimensional ℂ E]
    {ι : Type*} [Fintype ι] {U : Set E} (hU : IsOpen U)
    {f : E → (ι → ℂ)} (hf : DifferentiableOn ℂ f U) :
    IsAnalyticSet U (U ∩ f ⁻¹' {0}) :=
  isAnalyticSet_zeroSet_pi hU (hf.analyticOnNhd_of_finiteDimensional hU)

/-- Biholomorphic changes of ambient coordinates preserve analytic subsets. -/
theorem IsAnalyticSet.image_biholomorphic [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    {e : OpenPartialHomeomorph E F} (he : IsBiholomorphic e)
    {A : Set E} (hA : IsAnalyticSet e.source A) : IsAnalyticSet e.target (e '' A) := by
  let := FiniteDimensional.complete ℂ E
  have h := hA.preimage e.open_target
    (he.2.analyticOnNhd_of_finiteDimensional e.open_target) e.symm.mapsTo
  convert h using 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e.map_source (hA.subset hx), by simpa [e.left_inv (hA.subset hx)] using hx⟩
  · rintro ⟨hy, hx⟩
    exact ⟨e.symm y, hx, e.right_inv hy⟩

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
