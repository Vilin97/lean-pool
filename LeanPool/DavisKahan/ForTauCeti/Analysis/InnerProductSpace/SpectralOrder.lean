/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.QuadraticFormBounds
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.ReducingSubspace
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
public import LeanPool.DavisKahan.ForTauCeti.Analysis.RCLike.ScalarTransportFunctionalCalculus
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Spectral order and quadratic forms over `RCLike`

For bounded self-adjoint operators on Hilbert spaces over an arbitrary `RCLike` field,
actual spectral inclusions imply upper and lower quadratic-form bounds.  The real continuous
functional calculus is supplied by scalar transport, so the same spectral-order API serves
real, complex, and abstract `RCLike` scalars.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original modules: the former real and complex spectral-order bridges, now unified after the
  real continuous functional calculus became available over arbitrary `RCLike` scalars.
* Extraction class: **authored in place**, for Tau Ceti — `ForMathlib` was
  retired on 2026-07-29 and `ForTauCeti` is the single staging library, whose
  destination is Tau Ceti and not Mathlib (`ForTauCeti/README.md`).
* Original authors / copyright: Jon Crall, Claude Opus 4.8, GPT 5.6 High; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — the `ForTauCeti` import firewall admits only
  Mathlib, `TauCeti` and `ForTauCeti` (enforced by `scripts/check_dependency_layers.py`).
-/

public section

namespace TauCeti
namespace SpectralOrder
open TauCeti
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
  ContinuousLinearMap.instStarOrderedRingRCLike

/-- A spectral upper bound implies a quadratic-form upper bound. -/
theorem re_inner_le_of_spectrum_subset_Iic
    (T : H →L[𝕜] H) (hT : IsSelfAdjoint T) {c : ℝ}
    (hσ : spectrum ℝ T ⊆ Set.Iic c) (x : H) :
    RCLike.re ⟪T x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
  have hle : T ≤ algebraMap ℝ (H →L[𝕜] H) c :=
    le_algebraMap_of_spectrum_le (fun r hr => hσ hr) hT
  have hpos : (algebraMap ℝ (H →L[𝕜] H) c - T).IsPositive := by
    rw [← ContinuousLinearMap.nonneg_iff_isPositive]
    exact sub_nonneg.mpr hle
  have hx := hpos.re_inner_nonneg_left x
  have hcOp : algebraMap ℝ (H →L[𝕜] H) c =
      (algebraMap ℝ 𝕜 c) • (1 : H →L[𝕜] H) := by
    rw [Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_smul 𝕜]
  have hcx : RCLike.re ⟪(algebraMap ℝ 𝕜 c) • x, x⟫_𝕜 = c * ‖x‖ ^ 2 := by
    rw [inner_smul_left, RCLike.algebraMap_eq_ofReal, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
  rw [hcOp] at hx
  simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left, map_sub] at hx
  rw [hcx] at hx
  linarith

/-- A spectral lower bound implies a quadratic-form lower bound. -/
theorem le_re_inner_of_spectrum_subset_Ici
    (T : H →L[𝕜] H) (hT : IsSelfAdjoint T) {c : ℝ}
    (hσ : spectrum ℝ T ⊆ Set.Ici c) (x : H) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  have hle : algebraMap ℝ (H →L[𝕜] H) c ≤ T :=
    algebraMap_le_of_le_spectrum (fun r hr => hσ hr) hT
  have hpos : (T - algebraMap ℝ (H →L[𝕜] H) c).IsPositive := by
    rw [← ContinuousLinearMap.nonneg_iff_isPositive]
    exact sub_nonneg.mpr hle
  have hx := hpos.re_inner_nonneg_left x
  have hcOp : algebraMap ℝ (H →L[𝕜] H) c =
      (algebraMap ℝ 𝕜 c) • (1 : H →L[𝕜] H) := by
    rw [Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_smul 𝕜]
  have hcx : RCLike.re ⟪(algebraMap ℝ 𝕜 c) • x, x⟫_𝕜 = c * ‖x‖ ^ 2 := by
    rw [inner_smul_left, RCLike.algebraMap_eq_ofReal, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
  rw [hcOp] at hx
  simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left, map_sub] at hx
  rw [hcx] at hx
  linarith


/-- Spectral upper bound, packaged as a global upper form bound. -/
theorem upperFormBoundOn_top_of_spectrum_subset_Iic
    (T : H →L[𝕜] H) (hT : IsSelfAdjoint T) {c : ℝ}
    (hσ : spectrum ℝ T ⊆ Set.Iic c) :
    T.UpperFormBoundOn ⊤ c := by
  intro x _
  exact re_inner_le_of_spectrum_subset_Iic T hT hσ x

/-- Spectral lower bound, packaged as a global lower form bound. -/
theorem lowerFormBoundOn_top_of_spectrum_subset_Ici
    (T : H →L[𝕜] H) (hT : IsSelfAdjoint T) {c : ℝ}
    (hσ : spectrum ℝ T ⊆ Set.Ici c) :
    T.LowerFormBoundOn ⊤ c := by
  intro x _
  exact le_re_inner_of_spectrum_subset_Ici T hT hσ x

/-- A spectral upper bound for the actual restriction gives the corresponding
form bound on the reducing subspace. -/
theorem re_inner_le_on_subspace_of_restriction_spectrum_subset_Iic
    {A : H →L[𝕜] H} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    (hU : ∀ x ∈ U, A x ∈ U) {c : ℝ}
    (hσ : spectrum ℝ (A.restrict hU) ⊆ Set.Iic c)
    {x : H} (hx : x ∈ U) :
    RCLike.re ⟪A x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
  let : CompleteSpace U :=
    completeSpace_coe_iff_isComplete.mpr U.isComplete_coe_of_hasOrthogonalProjection
  have hres : IsSelfAdjoint (A.restrict hU) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (hA.restrict_invariant hU)
  have h := re_inner_le_of_spectrum_subset_Iic
    (A.restrict hU) hres hσ (⟨x, hx⟩ : U)
  -- restates the hypothesis with the definition unfolded, the form the following
  -- step matches against.
  change RCLike.re ⟪A x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 at h
  exact h

/-- A spectral lower bound for the actual restriction gives the corresponding
form bound on the reducing subspace. -/
theorem le_re_inner_on_subspace_of_restriction_spectrum_subset_Ici
    {A : H →L[𝕜] H} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    (hU : ∀ x ∈ U, A x ∈ U) {c : ℝ}
    (hσ : spectrum ℝ (A.restrict hU) ⊆ Set.Ici c)
    {x : H} (hx : x ∈ U) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜 := by
  let : CompleteSpace U :=
    completeSpace_coe_iff_isComplete.mpr U.isComplete_coe_of_hasOrthogonalProjection
  have hres : IsSelfAdjoint (A.restrict hU) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (hA.restrict_invariant hU)
  have h := le_re_inner_of_spectrum_subset_Ici
    (A.restrict hU) hres hσ (⟨x, hx⟩ : U)
  -- restates the hypothesis with the definition unfolded, the form the following
  -- step matches against.
  change c * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜 at h
  exact h


/-- Restriction-spectrum upper bridge, packaged as a subspace form bound. -/
theorem upperFormBoundOn_of_restriction_spectrum_subset_Iic
    {A : H →L[𝕜] H} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    (hU : ∀ x ∈ U, A x ∈ U) {c : ℝ}
    (hσ : spectrum ℝ (A.restrict hU) ⊆ Set.Iic c) :
    A.UpperFormBoundOn U c := by
  intro x hx
  exact re_inner_le_on_subspace_of_restriction_spectrum_subset_Iic hA hU hσ hx

/-- Restriction-spectrum lower bridge, packaged as a subspace form bound. -/
theorem lowerFormBoundOn_of_restriction_spectrum_subset_Ici
    {A : H →L[𝕜] H} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    (hU : ∀ x ∈ U, A x ∈ U) {c : ℝ}
    (hσ : spectrum ℝ (A.restrict hU) ⊆ Set.Ici c) :
    A.LowerFormBoundOn U c := by
  intro x hx
  exact le_re_inner_on_subspace_of_restriction_spectrum_subset_Ici hA hU hσ hx


/-- The sharp projector bound from spectra of the actual restrictions, uniformly over `RCLike`. -/
theorem opNorm_starProjection_sub_le_of_restriction_spectra
    {A B : H →L[𝕜] H} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U W : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    [W.HasOrthogonalProjection]
    (hU : A.Reduces U) (hW : B.Reduces W)
    {c g : ℝ} (hg : 0 < g)
    (hUhi : spectrum ℝ (A.restrict hU.1) ⊆ Set.Ici (c + g))
    (hUlo : spectrum ℝ (A.restrict hU.2) ⊆ Set.Iic c)
    (hWhi : spectrum ℝ (B.restrict hW.1) ⊆ Set.Ici (c + g))
    (hWlo : spectrum ℝ (B.restrict hW.2) ⊆ Set.Iic c) :
    ‖(U.starProjection - W.starProjection : H →L[𝕜] H)‖ ≤ ‖B - A‖ / g := by
  apply Submodule.opNorm_starProjection_sub_le_of_formBounds hA hB hU hW hg
  · exact lowerFormBoundOn_of_restriction_spectrum_subset_Ici hA hU.1 hUhi
  · exact upperFormBoundOn_of_restriction_spectrum_subset_Iic hA hU.2 hUlo
  · exact lowerFormBoundOn_of_restriction_spectrum_subset_Ici hB hW.1 hWhi
  · exact upperFormBoundOn_of_restriction_spectrum_subset_Iic hB hW.2 hWlo


end SpectralOrder
end TauCeti
