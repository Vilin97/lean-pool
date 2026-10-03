/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.Directional.EstimateDefs

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Directional estimate transport

This file proves pointwise and set-level transport lemmas for fixed-direction scalar estimate sets
under linear isometry equivalences.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Pointwise transport of the fixed-direction scalar line-good predicate through a linear
isometry equivalence. -/
theorem mem_directionalLineScalarEstimateSet_comp_linearIsometryEquiv
    (e : E ≃ₗᵢ[ℝ] F) {u : F → ℝ} {x v : E} :
    x ∈ directionalLineScalarEstimateSet v (u ∘ e) ↔
      e x ∈ directionalLineScalarEstimateSet (e v) u := by
  simp [directionalLineScalarEstimateSet, lineRestriction_comp_linearIsometryEquiv]

/-- Set-level transport of the fixed-direction scalar line-good predicate through a linear
isometry equivalence. -/
theorem directionalLineScalarEstimateSet_comp_linearIsometryEquiv
    (e : E ≃ₗᵢ[ℝ] F) (u : F → ℝ) (v : E) :
    directionalLineScalarEstimateSet v (u ∘ e) =
      e ⁻¹' directionalLineScalarEstimateSet (e v) u := by
  ext x
  exact mem_directionalLineScalarEstimateSet_comp_linearIsometryEquiv (e := e)

/-- Pointwise transport of the fixed-direction scalar quotient line-good predicate through a
linear isometry equivalence. -/
theorem mem_directionalLineScalarQuotientEstimateSet_comp_linearIsometryEquiv
    (e : E ≃ₗᵢ[ℝ] F) {u : F → ℝ} {x v : E} :
    x ∈ directionalLineScalarQuotientEstimateSet v (u ∘ e) ↔
      e x ∈ directionalLineScalarQuotientEstimateSet (e v) u := by
  simp [directionalLineScalarQuotientEstimateSet, lineRestriction_comp_linearIsometryEquiv]

/-- Set-level transport of the fixed-direction scalar quotient line-good predicate through a
linear isometry equivalence. -/
theorem directionalLineScalarQuotientEstimateSet_comp_linearIsometryEquiv
    (e : E ≃ₗᵢ[ℝ] F) (u : F → ℝ) (v : E) :
    directionalLineScalarQuotientEstimateSet v (u ∘ e) =
      e ⁻¹' directionalLineScalarQuotientEstimateSet (e v) u := by
  ext x
  exact mem_directionalLineScalarQuotientEstimateSet_comp_linearIsometryEquiv (e := e)

/-- Pointwise transport of finite directional slice-good data through a linear isometry
equivalence. -/
theorem mem_directionalSliceEstimateSet_comp_linearIsometryEquiv
    {ι : Type*} (e : E ≃ₗᵢ[ℝ] F) {D : Finset ι} {v : ι → E} {u : F → ℝ}
    {x : E} :
    x ∈ directionalSliceEstimateSet D v (u ∘ e) ↔
      e x ∈ directionalSliceEstimateSet D (fun i ↦ e (v i)) u := by
  simp [directionalSliceEstimateSet, DirectionalSliceEstimateAt,
    lineRestriction_comp_linearIsometryEquiv, map_add]

/-- Pointwise transport of finite directional slice data through a linear isometry
equivalence. -/
theorem directionalSliceEstimateAt_comp_linearIsometryEquiv
    {ι : Type*} (e : E ≃ₗᵢ[ℝ] F) {D : Finset ι} {v : ι → E} {u : F → ℝ}
    {x : E} :
    DirectionalSliceEstimateAt D v (u ∘ e) x ↔
      DirectionalSliceEstimateAt D (fun i ↦ e (v i)) u (e x) := by
  change x ∈ directionalSliceEstimateSet D v (u ∘ e) ↔
    e x ∈ directionalSliceEstimateSet D (fun i ↦ e (v i)) u
  exact mem_directionalSliceEstimateSet_comp_linearIsometryEquiv (e := e)

/-- Set-level transport of finite directional slice-good data through a linear isometry
equivalence. -/
theorem directionalSliceEstimateSet_comp_linearIsometryEquiv
    {ι : Type*} (e : E ≃ₗᵢ[ℝ] F) (D : Finset ι) (v : ι → E) (u : F → ℝ) :
    directionalSliceEstimateSet D v (u ∘ e) =
      e ⁻¹' directionalSliceEstimateSet D (fun i ↦ e (v i)) u := by
  ext x
  exact mem_directionalSliceEstimateSet_comp_linearIsometryEquiv (e := e)

/-- Pointwise transport of finite directional quotient slice-good data through a linear isometry
equivalence. -/
theorem mem_directionalSliceQuotientEstimateSet_comp_linearIsometryEquiv
    {ι : Type*} (e : E ≃ₗᵢ[ℝ] F) {D : Finset ι} {v : ι → E} {u : F → ℝ}
    {x : E} :
    x ∈ directionalSliceQuotientEstimateSet D v (u ∘ e) ↔
      e x ∈ directionalSliceQuotientEstimateSet D (fun i ↦ e (v i)) u := by
  simp [directionalSliceQuotientEstimateSet, DirectionalSliceQuotientEstimateAt,
    lineRestriction_comp_linearIsometryEquiv, map_add]

/-- Pointwise transport of finite directional quotient-slice data through a linear isometry
equivalence. -/
theorem directionalSliceQuotientEstimateAt_comp_linearIsometryEquiv
    {ι : Type*} (e : E ≃ₗᵢ[ℝ] F) {D : Finset ι} {v : ι → E} {u : F → ℝ}
    {x : E} :
    DirectionalSliceQuotientEstimateAt D v (u ∘ e) x ↔
      DirectionalSliceQuotientEstimateAt D (fun i ↦ e (v i)) u (e x) := by
  change x ∈ directionalSliceQuotientEstimateSet D v (u ∘ e) ↔
    e x ∈ directionalSliceQuotientEstimateSet D (fun i ↦ e (v i)) u
  exact mem_directionalSliceQuotientEstimateSet_comp_linearIsometryEquiv (e := e)

/-- Set-level transport of finite directional quotient slice-good data through a linear isometry
equivalence. -/
theorem directionalSliceQuotientEstimateSet_comp_linearIsometryEquiv
    {ι : Type*} (e : E ≃ₗᵢ[ℝ] F) (D : Finset ι) (v : ι → E) (u : F → ℝ) :
    directionalSliceQuotientEstimateSet D v (u ∘ e) =
      e ⁻¹' directionalSliceQuotientEstimateSet D (fun i ↦ e (v i)) u := by
  ext x
  exact mem_directionalSliceQuotientEstimateSet_comp_linearIsometryEquiv (e := e)

/-- Pointwise transport of compatible finite directional slice data through a linear isometry
equivalence. The common ambient slope is transported by the isometry. -/
theorem compatibleDirectionalSliceEstimateAt_comp_linearIsometryEquiv
    {ι : Type*} (e : E ≃ₗᵢ[ℝ] F) {D : Finset ι} {v : ι → E} {u : F → ℝ}
    {x : E} :
    CompatibleDirectionalSliceEstimateAt D v (u ∘ e) x ↔
      CompatibleDirectionalSliceEstimateAt D (fun i ↦ e (v i)) u (e x) := by
  constructor
  · intro h
    rcases h with ⟨p, q, r, hpure, hpair⟩
    refine ⟨e p, q, r, ?_, ?_⟩
    · intro i hi
      have hline := hpure hi
      have hslope : inner ℝ (e p) (e (v i)) = inner ℝ p (v i) := by
        exact LinearIsometryEquiv.inner_map_map e p (v i)
      simpa [lineRestriction_comp_linearIsometryEquiv, hslope] using hline
    · intro i hi j hj
      have hline := hpair hi hj
      have hslope :
          inner ℝ (e p) (e (v i) + e (v j)) = inner ℝ p (v i + v j) := by
        simpa [map_add] using LinearIsometryEquiv.inner_map_map e p (v i + v j)
      simpa [lineRestriction_comp_linearIsometryEquiv, map_add, hslope] using hline
  · intro h
    rcases h with ⟨p, q, r, hpure, hpair⟩
    refine ⟨e.symm p, q, r, ?_, ?_⟩
    · intro i hi
      have hline := hpure hi
      have hslope : inner ℝ p (e (v i)) = inner ℝ (e.symm p) (v i) := by
        simpa using LinearIsometryEquiv.inner_map_map e (e.symm p) (v i)
      simpa [lineRestriction_comp_linearIsometryEquiv, hslope] using hline
    · intro i hi j hj
      have hline := hpair hi hj
      have hslope :
          inner ℝ p (e (v i) + e (v j)) = inner ℝ (e.symm p) (v i + v j) := by
        simpa [map_add] using LinearIsometryEquiv.inner_map_map e (e.symm p) (v i + v j)
      simpa [lineRestriction_comp_linearIsometryEquiv, map_add, hslope] using hline

/-- Set-level transport of compatible finite directional slice data through a linear isometry
equivalence. -/
theorem compatibleDirectionalSliceEstimateSet_comp_linearIsometryEquiv
    {ι : Type*} (e : E ≃ₗᵢ[ℝ] F) (D : Finset ι) (v : ι → E) (u : F → ℝ) :
    compatibleDirectionalSliceEstimateSet D v (u ∘ e) =
      e ⁻¹' compatibleDirectionalSliceEstimateSet D (fun i ↦ e (v i)) u := by
  ext x
  exact compatibleDirectionalSliceEstimateAt_comp_linearIsometryEquiv (e := e)

/-- Pointwise transport of symmetric-compatible finite directional slice data through a linear
isometry equivalence. -/
theorem symmetricCompatibleDirectionalSliceEstimateAt_comp_linearIsometryEquiv
    {ι : Type*} (e : E ≃ₗᵢ[ℝ] F) {D : Finset ι} {v : ι → E} {u : F → ℝ}
    {x : E} :
    SymmetricCompatibleDirectionalSliceEstimateAt D v (u ∘ e) x ↔
      SymmetricCompatibleDirectionalSliceEstimateAt D (fun i ↦ e (v i)) u (e x) := by
  constructor
  · intro h
    rcases h with ⟨p, q, r, hsymm, hpure, hpair⟩
    refine ⟨e p, q, r, hsymm, ?_, ?_⟩
    · intro i hi
      have hline := hpure hi
      have hslope : inner ℝ (e p) (e (v i)) = inner ℝ p (v i) := by
        exact LinearIsometryEquiv.inner_map_map e p (v i)
      simpa [lineRestriction_comp_linearIsometryEquiv, hslope] using hline
    · intro i hi j hj
      have hline := hpair hi hj
      have hslope :
          inner ℝ (e p) (e (v i) + e (v j)) = inner ℝ p (v i + v j) := by
        simpa [map_add] using LinearIsometryEquiv.inner_map_map e p (v i + v j)
      simpa [lineRestriction_comp_linearIsometryEquiv, map_add, hslope] using hline
  · intro h
    rcases h with ⟨p, q, r, hsymm, hpure, hpair⟩
    refine ⟨e.symm p, q, r, hsymm, ?_, ?_⟩
    · intro i hi
      have hline := hpure hi
      have hslope : inner ℝ p (e (v i)) = inner ℝ (e.symm p) (v i) := by
        simpa using LinearIsometryEquiv.inner_map_map e (e.symm p) (v i)
      simpa [lineRestriction_comp_linearIsometryEquiv, hslope] using hline
    · intro i hi j hj
      have hline := hpair hi hj
      have hslope :
          inner ℝ p (e (v i) + e (v j)) = inner ℝ (e.symm p) (v i + v j) := by
        simpa [map_add] using LinearIsometryEquiv.inner_map_map e (e.symm p) (v i + v j)
      simpa [lineRestriction_comp_linearIsometryEquiv, map_add, hslope] using hline

/-- Set-level transport of symmetric-compatible finite directional slice data through a linear
isometry equivalence. -/
theorem symmetricCompatibleDirectionalSliceEstimateSet_comp_linearIsometryEquiv
    {ι : Type*} (e : E ≃ₗᵢ[ℝ] F) (D : Finset ι) (v : ι → E) (u : F → ℝ) :
    symmetricCompatibleDirectionalSliceEstimateSet D v (u ∘ e) =
      e ⁻¹' symmetricCompatibleDirectionalSliceEstimateSet D (fun i ↦ e (v i)) u := by
  ext x
  exact symmetricCompatibleDirectionalSliceEstimateAt_comp_linearIsometryEquiv (e := e)

/-- Pointwise transport of compatible finite quotient-slice data through a linear isometry
equivalence. -/
theorem compatibleDirectionalSliceQuotientEstimateAt_comp_linearIsometryEquiv
    {ι : Type*} (e : E ≃ₗᵢ[ℝ] F) {D : Finset ι} {v : ι → E} {u : F → ℝ}
    {x : E} :
    CompatibleDirectionalSliceQuotientEstimateAt D v (u ∘ e) x ↔
      CompatibleDirectionalSliceQuotientEstimateAt D (fun i ↦ e (v i)) u (e x) := by
  constructor
  · intro h
    rcases h with ⟨p, q, r, hpure, hpair⟩
    refine ⟨e p, q, r, ?_, ?_⟩
    · intro i hi
      have hline := hpure hi
      have hslope : inner ℝ (e p) (e (v i)) = inner ℝ p (v i) := by
        exact LinearIsometryEquiv.inner_map_map e p (v i)
      simpa [lineRestriction_comp_linearIsometryEquiv, hslope] using hline
    · intro i hi j hj
      have hline := hpair hi hj
      have hslope :
          inner ℝ (e p) (e (v i) + e (v j)) = inner ℝ p (v i + v j) := by
        simpa [map_add] using LinearIsometryEquiv.inner_map_map e p (v i + v j)
      simpa [lineRestriction_comp_linearIsometryEquiv, map_add, hslope] using hline
  · intro h
    rcases h with ⟨p, q, r, hpure, hpair⟩
    refine ⟨e.symm p, q, r, ?_, ?_⟩
    · intro i hi
      have hline := hpure hi
      have hslope : inner ℝ p (e (v i)) = inner ℝ (e.symm p) (v i) := by
        simpa using LinearIsometryEquiv.inner_map_map e (e.symm p) (v i)
      simpa [lineRestriction_comp_linearIsometryEquiv, hslope] using hline
    · intro i hi j hj
      have hline := hpair hi hj
      have hslope :
          inner ℝ p (e (v i) + e (v j)) = inner ℝ (e.symm p) (v i + v j) := by
        simpa [map_add] using LinearIsometryEquiv.inner_map_map e (e.symm p) (v i + v j)
      simpa [lineRestriction_comp_linearIsometryEquiv, map_add, hslope] using hline

/-- Set-level transport of compatible finite quotient-slice data through a linear isometry
equivalence. -/
theorem compatibleDirectionalSliceQuotientEstimateSet_comp_linearIsometryEquiv
    {ι : Type*} (e : E ≃ₗᵢ[ℝ] F) (D : Finset ι) (v : ι → E) (u : F → ℝ) :
    compatibleDirectionalSliceQuotientEstimateSet D v (u ∘ e) =
      e ⁻¹' compatibleDirectionalSliceQuotientEstimateSet D (fun i ↦ e (v i)) u := by
  ext x
  exact compatibleDirectionalSliceQuotientEstimateAt_comp_linearIsometryEquiv (e := e)

/-- Pointwise transport of symmetric-compatible finite quotient-slice data through a linear
isometry equivalence. -/
theorem symmetricCompatibleDirectionalSliceQuotientEstimateAt_comp_linearIsometryEquiv
    {ι : Type*} (e : E ≃ₗᵢ[ℝ] F) {D : Finset ι} {v : ι → E} {u : F → ℝ}
    {x : E} :
    SymmetricCompatibleDirectionalSliceQuotientEstimateAt D v (u ∘ e) x ↔
      SymmetricCompatibleDirectionalSliceQuotientEstimateAt D (fun i ↦ e (v i)) u
        (e x) := by
  constructor
  · intro h
    rcases h with ⟨p, q, r, hsymm, hpure, hpair⟩
    refine ⟨e p, q, r, hsymm, ?_, ?_⟩
    · intro i hi
      have hline := hpure hi
      have hslope : inner ℝ (e p) (e (v i)) = inner ℝ p (v i) := by
        exact LinearIsometryEquiv.inner_map_map e p (v i)
      simpa [lineRestriction_comp_linearIsometryEquiv, hslope] using hline
    · intro i hi j hj
      have hline := hpair hi hj
      have hslope :
          inner ℝ (e p) (e (v i) + e (v j)) = inner ℝ p (v i + v j) := by
        simpa [map_add] using LinearIsometryEquiv.inner_map_map e p (v i + v j)
      simpa [lineRestriction_comp_linearIsometryEquiv, map_add, hslope] using hline
  · intro h
    rcases h with ⟨p, q, r, hsymm, hpure, hpair⟩
    refine ⟨e.symm p, q, r, hsymm, ?_, ?_⟩
    · intro i hi
      have hline := hpure hi
      have hslope : inner ℝ p (e (v i)) = inner ℝ (e.symm p) (v i) := by
        simpa using LinearIsometryEquiv.inner_map_map e (e.symm p) (v i)
      simpa [lineRestriction_comp_linearIsometryEquiv, hslope] using hline
    · intro i hi j hj
      have hline := hpair hi hj
      have hslope :
          inner ℝ p (e (v i) + e (v j)) = inner ℝ (e.symm p) (v i + v j) := by
        simpa [map_add] using LinearIsometryEquiv.inner_map_map e (e.symm p) (v i + v j)
      simpa [lineRestriction_comp_linearIsometryEquiv, map_add, hslope] using hline

/-- Set-level transport of symmetric-compatible finite quotient-slice data through a linear
isometry equivalence. -/
theorem symmetricCompatibleDirectionalSliceQuotientEstimateSet_comp_linearIsometryEquiv
    {ι : Type*} (e : E ≃ₗᵢ[ℝ] F) (D : Finset ι) (v : ι → E) (u : F → ℝ) :
    symmetricCompatibleDirectionalSliceQuotientEstimateSet D v (u ∘ e) =
      e ⁻¹' symmetricCompatibleDirectionalSliceQuotientEstimateSet D (fun i ↦ e (v i)) u := by
  ext x
  exact symmetricCompatibleDirectionalSliceQuotientEstimateAt_comp_linearIsometryEquiv (e := e)


end AleksandrovDifferentiability
