/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.Directional.EstimateDefs
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.DirectionalQuadratic.Polarization

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Transport of mixed directional quadratic data

This file pulls mixed directional quadratic estimate data across linear isometry equivalences.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Pull back mixed-directional quadratic estimate data from an isometric coordinate model. -/
theorem MixedDirectionalQuadraticEstimateAt.of_image_linearIsometryEquiv
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ}
    (e : E ≃ₗᵢ[ℝ] F) {x : E}
    (h : MixedDirectionalQuadraticEstimateAt D (fun i ↦ e (v i))
      (u ∘ e.symm) (e x)) :
    MixedDirectionalQuadraticEstimateAt D v u x := by
  rcases h with ⟨pF, a, hest⟩
  refine ⟨e.symm pF, a, ?_⟩
  intro ε hε
  have htend : Filter.Tendsto (fun z : E ↦ e z) (nhds 0) (nhds 0) := by
    simpa using (e.continuous.continuousAt (x := 0)).tendsto
  filter_upwards [htend.eventually (hest ε hε)] with z hz
  have hpoint : e x + e z = e (x + z) := by
    simp [map_add]
  have hslope : pF = e (e.symm pF) := by
    simp
  have hquad := inner_mixedDirectionalQuadraticSum_self_linearIsometryEquiv D v a e z
  have hnorm : ‖e z‖ ^ 2 = ‖z‖ ^ 2 := by
    simp
  rw [hpoint] at hz
  rw [hslope] at hz
  rw [affineRemainder_comp_linearIsometryEquiv] at hz
  rw [hquad] at hz
  rw [hnorm] at hz
  exact hz

/-- Pull back punctured normalized mixed-directional quadratic estimate data from an isometric
coordinate model. -/
theorem MixedDirectionalQuadraticQuotientEstimateAt.of_image_linearIsometryEquiv
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ}
    (e : E ≃ₗᵢ[ℝ] F) {x : E}
    (h : MixedDirectionalQuadraticQuotientEstimateAt D (fun i ↦ e (v i))
      (u ∘ e.symm) (e x)) :
    MixedDirectionalQuadraticQuotientEstimateAt D v u x := by
  rcases h with ⟨pF, a, hest⟩
  refine ⟨e.symm pF, a, ?_⟩
  intro ε hε
  have htend_nhds :
      Filter.Tendsto (fun z : E ↦ e z) (nhdsWithin 0 {z : E | z ≠ 0}) (nhds 0) := by
    simpa using
      ((e.continuous.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds)
  have htend_principal :
      Filter.Tendsto (fun z : E ↦ e z) (nhdsWithin 0 {z : E | z ≠ 0})
        (Filter.principal {z : F | z ≠ 0}) := by
    rw [Filter.tendsto_principal]
    filter_upwards [self_mem_nhdsWithin] with z hz
    intro hez
    apply hz
    have hpre := congrArg e.symm hez
    simpa using hpre
  have htend :
      Filter.Tendsto (fun z : E ↦ e z) (nhdsWithin 0 {z : E | z ≠ 0})
        (nhdsWithin 0 {z : F | z ≠ 0}) := by
    rw [nhdsWithin]
    exact Filter.tendsto_inf.2 ⟨htend_nhds, htend_principal⟩
  filter_upwards [htend.eventually (hest ε hε)] with z hz
  have hpoint : e x + e z = e (x + z) := by
    simp [map_add]
  have hslope : pF = e (e.symm pF) := by
    simp
  have hquad := inner_mixedDirectionalQuadraticSum_self_linearIsometryEquiv D v a e z
  have hnorm : ‖e z‖ ^ 2 = ‖z‖ ^ 2 := by
    simp
  rw [hpoint] at hz
  rw [hslope] at hz
  rw [affineRemainder_comp_linearIsometryEquiv] at hz
  rw [hquad] at hz
  rw [hnorm] at hz
  exact hz

/-- Pointwise transport of mixed-directional quadratic estimate data through a linear isometry
equivalence. -/
theorem mixedDirectionalQuadraticEstimateAt_comp_linearIsometryEquiv
    {ι : Type*} (e : E ≃ₗᵢ[ℝ] F) {D : Finset ι} {v : ι → E} {u : F → ℝ}
    {x : E} :
    MixedDirectionalQuadraticEstimateAt D v (u ∘ e) x ↔
      MixedDirectionalQuadraticEstimateAt D (fun i ↦ e (v i)) u (e x) := by
  constructor
  · intro h
    have h' :=
      MixedDirectionalQuadraticEstimateAt.of_image_linearIsometryEquiv
        (e := e.symm) (u := u) (x := e x) (v := fun i ↦ e (v i)) (D := D)
        (by simpa [Function.comp_def] using h)
    simpa using h'
  · intro h
    have h' :=
      MixedDirectionalQuadraticEstimateAt.of_image_linearIsometryEquiv
        (e := e) (u := u ∘ e) (x := x) (v := v) (D := D)
        (by simpa [Function.comp_def] using h)
    simpa using h'

/-- Set-level transport of mixed-directional quadratic estimate data through a linear isometry
equivalence. -/
theorem mixedDirectionalQuadraticEstimateSet_comp_linearIsometryEquiv
    {ι : Type*} (e : E ≃ₗᵢ[ℝ] F) (D : Finset ι) (v : ι → E) (u : F → ℝ) :
    mixedDirectionalQuadraticEstimateSet D v (u ∘ e) =
      e ⁻¹' mixedDirectionalQuadraticEstimateSet D (fun i ↦ e (v i)) u := by
  ext x
  exact mixedDirectionalQuadraticEstimateAt_comp_linearIsometryEquiv (e := e)

/-- Pointwise transport of mixed-directional quotient-estimate data through a linear isometry
equivalence. -/
theorem mixedDirectionalQuadraticQuotientEstimateAt_comp_linearIsometryEquiv
    {ι : Type*} (e : E ≃ₗᵢ[ℝ] F) {D : Finset ι} {v : ι → E} {u : F → ℝ}
    {x : E} :
    MixedDirectionalQuadraticQuotientEstimateAt D v (u ∘ e) x ↔
      MixedDirectionalQuadraticQuotientEstimateAt D (fun i ↦ e (v i)) u (e x) := by
  constructor
  · intro h
    have h' :=
      MixedDirectionalQuadraticQuotientEstimateAt.of_image_linearIsometryEquiv
        (e := e.symm) (u := u) (x := e x) (v := fun i ↦ e (v i)) (D := D)
        (by simpa [Function.comp_def] using h)
    simpa using h'
  · intro h
    have h' :=
      MixedDirectionalQuadraticQuotientEstimateAt.of_image_linearIsometryEquiv
        (e := e) (u := u ∘ e) (x := x) (v := v) (D := D)
        (by simpa [Function.comp_def] using h)
    simpa using h'

/-- Set-level transport of mixed-directional quotient-estimate data through a linear isometry
equivalence. -/
theorem mixedDirectionalQuadraticQuotientEstimateSet_comp_linearIsometryEquiv
    {ι : Type*} (e : E ≃ₗᵢ[ℝ] F) (D : Finset ι) (v : ι → E) (u : F → ℝ) :
    mixedDirectionalQuadraticQuotientEstimateSet D v (u ∘ e) =
      e ⁻¹' mixedDirectionalQuadraticQuotientEstimateSet D (fun i ↦ e (v i)) u := by
  ext x
  exact mixedDirectionalQuadraticQuotientEstimateAt_comp_linearIsometryEquiv (e := e)

/-- Pull back polarized mixed-directional quadratic estimate data from an isometric coordinate
model. -/
theorem PolarizedMixedDirectionalQuadraticEstimateAt.of_image_linearIsometryEquiv
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ}
    (e : E ≃ₗᵢ[ℝ] F) {x : E}
    (h : PolarizedMixedDirectionalQuadraticEstimateAt D (fun i ↦ e (v i))
      (u ∘ e.symm) (e x)) :
    PolarizedMixedDirectionalQuadraticEstimateAt D v u x := by
  rcases h with ⟨pF, q, r, hest⟩
  refine ⟨e.symm pF, q, r, ?_⟩
  intro ε hε
  have htend : Filter.Tendsto (fun z : E ↦ e z) (nhds 0) (nhds 0) := by
    simpa using (e.continuous.continuousAt (x := 0)).tendsto
  filter_upwards [htend.eventually (hest ε hε)] with z hz
  have hpoint : e x + e z = e (x + z) := by
    simp [map_add]
  have hslope : pF = e (e.symm pF) := by
    simp
  have hquad := inner_polarizedMixedQuadraticSum_self_linearIsometryEquiv D v q r e z
  have hnorm : ‖e z‖ ^ 2 = ‖z‖ ^ 2 := by
    simp
  rw [hpoint] at hz
  rw [hslope] at hz
  rw [affineRemainder_comp_linearIsometryEquiv] at hz
  rw [hquad] at hz
  rw [hnorm] at hz
  exact hz

/-- Pull back punctured normalized polarized mixed-directional quadratic estimate data from an
isometric coordinate model. -/
theorem PolarizedMixedDirectionalQuadraticQuotientEstimateAt.of_image_linearIsometryEquiv
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ}
    (e : E ≃ₗᵢ[ℝ] F) {x : E}
    (h : PolarizedMixedDirectionalQuadraticQuotientEstimateAt D (fun i ↦ e (v i))
      (u ∘ e.symm) (e x)) :
    PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x := by
  rcases h with ⟨pF, q, r, hest⟩
  refine ⟨e.symm pF, q, r, ?_⟩
  intro ε hε
  have htend_nhds :
      Filter.Tendsto (fun z : E ↦ e z) (nhdsWithin 0 {z : E | z ≠ 0}) (nhds 0) := by
    simpa using
      ((e.continuous.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds)
  have htend_principal :
      Filter.Tendsto (fun z : E ↦ e z) (nhdsWithin 0 {z : E | z ≠ 0})
        (Filter.principal {z : F | z ≠ 0}) := by
    rw [Filter.tendsto_principal]
    filter_upwards [self_mem_nhdsWithin] with z hz
    intro hez
    apply hz
    have hpre := congrArg e.symm hez
    simpa using hpre
  have htend :
      Filter.Tendsto (fun z : E ↦ e z) (nhdsWithin 0 {z : E | z ≠ 0})
        (nhdsWithin 0 {z : F | z ≠ 0}) := by
    rw [nhdsWithin]
    exact Filter.tendsto_inf.2 ⟨htend_nhds, htend_principal⟩
  filter_upwards [htend.eventually (hest ε hε)] with z hz
  have hpoint : e x + e z = e (x + z) := by
    simp [map_add]
  have hslope : pF = e (e.symm pF) := by
    simp
  have hquad := inner_polarizedMixedQuadraticSum_self_linearIsometryEquiv D v q r e z
  have hnorm : ‖e z‖ ^ 2 = ‖z‖ ^ 2 := by
    simp
  rw [hpoint] at hz
  rw [hslope] at hz
  rw [affineRemainder_comp_linearIsometryEquiv] at hz
  rw [hquad] at hz
  rw [hnorm] at hz
  exact hz

/-- Pointwise transport of polarized mixed-directional estimate data through a linear isometry
equivalence. -/
theorem polarizedMixedDirectionalQuadraticEstimateAt_comp_linearIsometryEquiv
    {ι : Type*} [DecidableEq ι] (e : E ≃ₗᵢ[ℝ] F) {D : Finset ι} {v : ι → E}
    {u : F → ℝ} {x : E} :
    PolarizedMixedDirectionalQuadraticEstimateAt D v (u ∘ e) x ↔
      PolarizedMixedDirectionalQuadraticEstimateAt D (fun i ↦ e (v i)) u (e x) := by
  constructor
  · intro h
    have h' :=
      PolarizedMixedDirectionalQuadraticEstimateAt.of_image_linearIsometryEquiv
        (e := e.symm) (u := u) (x := e x) (v := fun i ↦ e (v i)) (D := D)
        (by simpa [Function.comp_def] using h)
    simpa using h'
  · intro h
    have h' :=
      PolarizedMixedDirectionalQuadraticEstimateAt.of_image_linearIsometryEquiv
        (e := e) (u := u ∘ e) (x := x) (v := v) (D := D)
        (by simpa [Function.comp_def] using h)
    simpa using h'

/-- Set-level transport of polarized mixed-directional estimate data through a linear isometry
equivalence. -/
theorem polarizedMixedDirectionalQuadraticEstimateSet_comp_linearIsometryEquiv
    {ι : Type*} [DecidableEq ι] (e : E ≃ₗᵢ[ℝ] F) (D : Finset ι) (v : ι → E)
    (u : F → ℝ) :
    polarizedMixedDirectionalQuadraticEstimateSet D v (u ∘ e) =
      e ⁻¹' polarizedMixedDirectionalQuadraticEstimateSet D (fun i ↦ e (v i)) u := by
  ext x
  exact polarizedMixedDirectionalQuadraticEstimateAt_comp_linearIsometryEquiv (e := e)

/-- Pointwise transport of polarized mixed-directional quotient-estimate data through a linear
isometry equivalence. -/
theorem polarizedMixedDirectionalQuadraticQuotientEstimateAt_comp_linearIsometryEquiv
    {ι : Type*} [DecidableEq ι] (e : E ≃ₗᵢ[ℝ] F) {D : Finset ι} {v : ι → E}
    {u : F → ℝ} {x : E} :
    PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v (u ∘ e) x ↔
      PolarizedMixedDirectionalQuadraticQuotientEstimateAt D (fun i ↦ e (v i)) u (e x) := by
  constructor
  · intro h
    have h' :=
      PolarizedMixedDirectionalQuadraticQuotientEstimateAt.of_image_linearIsometryEquiv
        (e := e.symm) (u := u) (x := e x) (v := fun i ↦ e (v i)) (D := D)
        (by simpa [Function.comp_def] using h)
    simpa using h'
  · intro h
    have h' :=
      PolarizedMixedDirectionalQuadraticQuotientEstimateAt.of_image_linearIsometryEquiv
        (e := e) (u := u ∘ e) (x := x) (v := v) (D := D)
        (by simpa [Function.comp_def] using h)
    simpa using h'

/-- Set-level transport of polarized mixed-directional quotient-estimate data through a linear
isometry equivalence. -/
theorem polarizedMixedDirectionalQuadraticQuotientEstimateSet_comp_linearIsometryEquiv
    {ι : Type*} [DecidableEq ι] (e : E ≃ₗᵢ[ℝ] F) (D : Finset ι) (v : ι → E)
    (u : F → ℝ) :
    polarizedMixedDirectionalQuadraticQuotientEstimateSet D v (u ∘ e) =
      e ⁻¹' polarizedMixedDirectionalQuadraticQuotientEstimateSet D (fun i ↦ e (v i)) u := by
  ext x
  exact polarizedMixedDirectionalQuadraticQuotientEstimateAt_comp_linearIsometryEquiv (e := e)


end AleksandrovDifferentiability
