/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.QuadraticTrap

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Second order expansions on affine lines

This file connects the ambient second-order expansion predicate to one-dimensional restrictions
along affine lines.
-/

@[expose] public noncomputable section

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An ambient second-order expansion restricts to a second-order expansion along every affine
line, with the expected directional first and second coefficients. -/
theorem HasSecondOrderExpansionAt.lineRestriction_isLittleO
    {u : E → ℝ} {x p : E} {B : E →L[ℝ] E}
    (h : HasSecondOrderExpansionAt u x p B) (v : E) :
    (fun t : ℝ =>
        lineRestriction u x v t - u x - inner ℝ p v * t -
          (1 / 2 : ℝ) * inner ℝ v (B v) * t ^ 2)
      =o[nhds 0] (fun t : ℝ => ‖t • v‖ ^ 2) := by
  have htend : Filter.Tendsto (fun t : ℝ ↦ t • v) (nhds 0) (nhds 0) := by
    have hc : ContinuousAt (fun t : ℝ => t • v) 0 := by fun_prop
    simpa using hc.tendsto
  have hcomp := h.comp_tendsto htend
  refine hcomp.congr_left ?_
  intro t
  simp [lineRestriction, real_inner_smul_right, real_inner_smul_left,
    map_smul, mul_assoc, mul_left_comm, mul_comm, pow_two]

/-- Unit-direction version of `HasSecondOrderExpansionAt.lineRestriction_isLittleO`, with the
standard one-dimensional denominator. -/
theorem HasSecondOrderExpansionAt.lineRestriction_isLittleO_of_norm_eq_one
    {u : E → ℝ} {x p v : E} {B : E →L[ℝ] E}
    (h : HasSecondOrderExpansionAt u x p B) (hv : ‖v‖ = 1) :
    (fun t : ℝ =>
        lineRestriction u x v t - u x - inner ℝ p v * t -
          (1 / 2 : ℝ) * inner ℝ v (B v) * t ^ 2)
      =o[nhds 0] (fun t : ℝ => ‖t‖ ^ 2) := by
  refine (h.lineRestriction_isLittleO v).congr_right ?_
  intro t
  simp [norm_smul, hv]

/-- An ambient second-order expansion restricts to an affine line with the standard
one-dimensional little-o denominator. -/
theorem HasSecondOrderExpansionAt.lineRestriction_isLittleO_standard
    {u : E → ℝ} {x p : E} {B : E →L[ℝ] E}
    (h : HasSecondOrderExpansionAt u x p B) (v : E) :
    (fun t : ℝ =>
        lineRestriction u x v t - u x - inner ℝ p v * t -
          (1 / 2 : ℝ) * inner ℝ v (B v) * t ^ 2)
      =o[nhds 0] (fun t : ℝ => ‖t‖ ^ 2) := by
  have hscaled :
      (fun t : ℝ =>
          lineRestriction u x v t - u x - inner ℝ p v * t -
            (1 / 2 : ℝ) * inner ℝ v (B v) * t ^ 2)
        =o[nhds 0] (fun t : ℝ => ‖v‖ ^ 2 * ‖t‖ ^ 2) := by
    refine (h.lineRestriction_isLittleO v).congr_right ?_
    intro t
    simp [norm_smul, mul_pow, mul_comm]
  exact hscaled.of_const_mul_right

/-- Ambient second-order expansions restrict to project-level second-order expansions of
one-dimensional line restrictions. -/
theorem HasSecondOrderExpansionAt.lineRestriction_hasSecondOrderExpansionAt
    {u : E → ℝ} {x p : E} {B : E →L[ℝ] E}
    (h : HasSecondOrderExpansionAt u x p B) (v : E) :
    HasSecondOrderExpansionAt (lineRestriction u x v) 0 (inner ℝ p v)
      ((inner ℝ v (B v)) • (1 : ℝ →L[ℝ] ℝ)) := by
  rw [HasSecondOrderExpansionAt]
  refine (h.lineRestriction_isLittleO_standard v).congr_left ?_
  intro t
  simp [lineRestriction, mul_assoc, mul_left_comm, mul_comm, pow_two]

/-- Ambient second-order expansions restrict to affine lines at arbitrary line parameters. -/
theorem HasSecondOrderExpansionAt.lineRestriction_at_hasSecondOrderExpansionAt
    {u : E → ℝ} {x p v : E} {B : E →L[ℝ] E} {t : ℝ}
    (h : HasSecondOrderExpansionAt u (x + t • v) p B) :
    HasSecondOrderExpansionAt (lineRestriction u x v) t (inner ℝ p v)
      ((inner ℝ v (B v)) • (1 : ℝ →L[ℝ] ℝ)) := by
  rw [HasSecondOrderExpansionAt]
  have hline :
      HasSecondOrderExpansionAt
        (lineRestriction u (x + t • v) v) 0 (inner ℝ p v)
        ((inner ℝ v (B v)) • (1 : ℝ →L[ℝ] ℝ)) :=
    h.lineRestriction_hasSecondOrderExpansionAt v
  rw [HasSecondOrderExpansionAt] at hline
  refine hline.congr_left ?_
  intro z
  have hpoint : x + (t + z) • v = x + t • v + z • v := by
    rw [add_smul]
    abel
  simp [lineRestriction, hpoint, mul_left_comm, mul_comm]

/-- An ambient CLM-gradient second-order expansion restricts to a second-order expansion along
every affine line, with the expected directional first and second coefficients. -/
theorem HasSecondOrderExpansionAtCLM.lineRestriction_isLittleO
    {u : E → ℝ} {x : E} {ℓ : E →L[ℝ] ℝ} {B : E →L[ℝ] E}
    (h : HasSecondOrderExpansionAtCLM u x ℓ B) (v : E) :
    (fun t : ℝ =>
        lineRestriction u x v t - u x - ℓ v * t -
          (1 / 2 : ℝ) * inner ℝ v (B v) * t ^ 2)
      =o[nhds 0] (fun t : ℝ => ‖t • v‖ ^ 2) := by
  have htend : Filter.Tendsto (fun t : ℝ ↦ t • v) (nhds 0) (nhds 0) := by
    have hc : ContinuousAt (fun t : ℝ => t • v) 0 := by fun_prop
    simpa using hc.tendsto
  have hcomp := h.comp_tendsto htend
  refine hcomp.congr_left ?_
  intro t
  simp [lineRestriction, real_inner_smul_right, real_inner_smul_left,
    map_smul, mul_assoc, mul_left_comm, mul_comm, pow_two]

/-- Unit-direction version of `HasSecondOrderExpansionAtCLM.lineRestriction_isLittleO`, with the
standard one-dimensional denominator. -/
theorem HasSecondOrderExpansionAtCLM.lineRestriction_isLittleO_of_norm_eq_one
    {u : E → ℝ} {x v : E} {ℓ : E →L[ℝ] ℝ} {B : E →L[ℝ] E}
    (h : HasSecondOrderExpansionAtCLM u x ℓ B) (hv : ‖v‖ = 1) :
    (fun t : ℝ =>
        lineRestriction u x v t - u x - ℓ v * t -
          (1 / 2 : ℝ) * inner ℝ v (B v) * t ^ 2)
      =o[nhds 0] (fun t : ℝ => ‖t‖ ^ 2) := by
  refine (h.lineRestriction_isLittleO v).congr_right ?_
  intro t
  simp [norm_smul, hv]

/-- An ambient CLM-gradient second-order expansion restricts to an affine line with the standard
one-dimensional little-o denominator. -/
theorem HasSecondOrderExpansionAtCLM.lineRestriction_isLittleO_standard
    {u : E → ℝ} {x : E} {ℓ : E →L[ℝ] ℝ} {B : E →L[ℝ] E}
    (h : HasSecondOrderExpansionAtCLM u x ℓ B) (v : E) :
    (fun t : ℝ =>
        lineRestriction u x v t - u x - ℓ v * t -
          (1 / 2 : ℝ) * inner ℝ v (B v) * t ^ 2)
      =o[nhds 0] (fun t : ℝ => ‖t‖ ^ 2) := by
  have hscaled :
      (fun t : ℝ =>
          lineRestriction u x v t - u x - ℓ v * t -
            (1 / 2 : ℝ) * inner ℝ v (B v) * t ^ 2)
        =o[nhds 0] (fun t : ℝ => ‖v‖ ^ 2 * ‖t‖ ^ 2) := by
    refine (h.lineRestriction_isLittleO v).congr_right ?_
    intro t
    simp [norm_smul, mul_pow, mul_comm]
  exact hscaled.of_const_mul_right

/-- Ambient CLM-gradient second-order expansions restrict to project-level second-order
expansions of one-dimensional line restrictions. -/
theorem HasSecondOrderExpansionAtCLM.lineRestriction_hasSecondOrderExpansionAt
    {u : E → ℝ} {x : E} {ℓ : E →L[ℝ] ℝ} {B : E →L[ℝ] E}
    (h : HasSecondOrderExpansionAtCLM u x ℓ B) (v : E) :
    HasSecondOrderExpansionAt (lineRestriction u x v) 0 (ℓ v)
      ((inner ℝ v (B v)) • (1 : ℝ →L[ℝ] ℝ)) := by
  rw [HasSecondOrderExpansionAt]
  refine (h.lineRestriction_isLittleO_standard v).congr_left ?_
  intro t
  simp [lineRestriction, mul_assoc, mul_left_comm, mul_comm, pow_two]

/-- Ambient CLM-gradient second-order expansions restrict to affine lines at arbitrary line
parameters. -/
theorem HasSecondOrderExpansionAtCLM.lineRestriction_at_hasSecondOrderExpansionAt
    {u : E → ℝ} {x v : E} {ℓ : E →L[ℝ] ℝ} {B : E →L[ℝ] E} {t : ℝ}
    (h : HasSecondOrderExpansionAtCLM u (x + t • v) ℓ B) :
    HasSecondOrderExpansionAt (lineRestriction u x v) t (ℓ v)
      ((inner ℝ v (B v)) • (1 : ℝ →L[ℝ] ℝ)) := by
  rw [HasSecondOrderExpansionAt]
  have hline :
      HasSecondOrderExpansionAt
        (lineRestriction u (x + t • v) v) 0 (ℓ v)
        ((inner ℝ v (B v)) • (1 : ℝ →L[ℝ] ℝ)) :=
    h.lineRestriction_hasSecondOrderExpansionAt v
  rw [HasSecondOrderExpansionAt] at hline
  refine hline.congr_left ?_
  intro z
  have hpoint : x + (t + z) • v = x + t • v + z • v := by
    rw [add_smul]
    abel
  simp [lineRestriction, hpoint, mul_left_comm, mul_comm]

/-- On the real line, every scalar multiple of the identity is a symmetric operator. -/
theorem isSymmetricOperator_real_smul_one (c : ℝ) :
    IsSymmetricOperator (c • (1 : ℝ →L[ℝ] ℝ)) := by
  rw [IsSymmetricOperator]
  exact LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.one

/-- Second order differentiability restricts to every affine line. -/
theorem SecondOrderDifferentiableAt.lineRestriction
    {u : E → ℝ} {x : E} (h : SecondOrderDifferentiableAt u x) (v : E) :
    SecondOrderDifferentiableAt (lineRestriction u x v) 0 := by
  rcases h with ⟨p, B, hB, hExp⟩
  exact ⟨inner ℝ p v, (inner ℝ v (B v)) • (1 : ℝ →L[ℝ] ℝ),
    isSymmetricOperator_real_smul_one (inner ℝ v (B v)),
    hExp.lineRestriction_hasSecondOrderExpansionAt v⟩

/-- Second order differentiability restricts to affine lines at arbitrary line parameters. -/
theorem SecondOrderDifferentiableAt.lineRestriction_at
    {u : E → ℝ} {x v : E} {t : ℝ}
    (h : SecondOrderDifferentiableAt u (x + t • v)) :
    SecondOrderDifferentiableAt (AleksandrovDifferentiability.lineRestriction u x v) t := by
  rcases h with ⟨p, B, hB, hExp⟩
  exact ⟨inner ℝ p v, (inner ℝ v (B v)) • (1 : ℝ →L[ℝ] ℝ),
    isSymmetricOperator_real_smul_one (inner ℝ v (B v)),
    hExp.lineRestriction_at_hasSecondOrderExpansionAt⟩

/-- The preimage of a fixed ambient second-order expansion locus along a line is contained in the
corresponding one-dimensional expansion locus. -/
theorem preimage_lineMap_secondOrderExpansionSet_subset
    {u : E → ℝ} {x p v : E} {B : E →L[ℝ] E} :
    {t : ℝ | x + t • v ∈ secondOrderExpansionSet u p B} ⊆
      secondOrderExpansionSet (AleksandrovDifferentiability.lineRestriction u x v)
        (inner ℝ p v) ((inner ℝ v (B v)) • (1 : ℝ →L[ℝ] ℝ)) := by
  intro t ht
  exact ht.lineRestriction_at_hasSecondOrderExpansionAt

/-- The preimage of a fixed ambient CLM expansion locus along a line is contained in the
corresponding one-dimensional expansion locus. -/
theorem preimage_lineMap_secondOrderExpansionSetCLM_subset
    {u : E → ℝ} {x v : E} {ℓ : E →L[ℝ] ℝ} {B : E →L[ℝ] E} :
    {t : ℝ | x + t • v ∈ secondOrderExpansionSetCLM u ℓ B} ⊆
      secondOrderExpansionSet (AleksandrovDifferentiability.lineRestriction u x v)
        (ℓ v) ((inner ℝ v (B v)) • (1 : ℝ →L[ℝ] ℝ)) := by
  intro t ht
  exact ht.lineRestriction_at_hasSecondOrderExpansionAt

/-- The preimage of the ambient second-order differentiability locus along a line is contained in
the one-dimensional second-order differentiability locus of the line restriction. -/
theorem preimage_lineMap_secondOrderDifferentiabilitySet_subset
    {u : E → ℝ} {x v : E} :
    {t : ℝ | x + t • v ∈ secondOrderDifferentiabilitySet u} ⊆
      secondOrderDifferentiabilitySet (AleksandrovDifferentiability.lineRestriction u x v) := by
  intro t ht
  exact ht.lineRestriction_at

/-- The preimage of the ambient CLM expansion-data locus along a line is contained in the
one-dimensional second-order differentiability locus of the line restriction. -/
theorem preimage_lineMap_secondOrderCLMExpansionDataSet_subset
    {u : E → ℝ} {x v : E} :
    {t : ℝ | x + t • v ∈ secondOrderCLMExpansionDataSet u} ⊆
      secondOrderDifferentiabilitySet (AleksandrovDifferentiability.lineRestriction u x v) := by
  intro t ht
  rcases ht with ⟨ℓ, B, hB, hquad⟩
  exact ⟨ℓ v, (inner ℝ v (B v)) • (1 : ℝ →L[ℝ] ℝ),
    isSymmetricOperator_real_smul_one (inner ℝ v (B v)),
    hquad.lineRestriction_at_hasSecondOrderExpansionAt⟩

/-- On a line restriction, project-level one-dimensional second-order differentiability gives the
scalar quadratic estimate format used by the one-dimensional assembly layer. -/
theorem lineRestriction_secondOrderDifferentiabilitySet_subset_realScalarQuadraticEstimateSet
    {u : E → ℝ} {x v : E} :
    secondOrderDifferentiabilitySet (AleksandrovDifferentiability.lineRestriction u x v) ⊆
      realScalarQuadraticEstimateSet (AleksandrovDifferentiability.lineRestriction u x v) := by
  intro t ht
  exact realScalarQuadraticEstimateAt_of_secondOrderDifferentiableAt ht

/-- Ambient second-order differentiability along a line implies scalar quadratic estimate data
for the corresponding one-dimensional line restriction. -/
theorem preimage_lineMap_secondOrderDifferentiabilitySet_subset_realScalarQuadraticEstimateSet
    {u : E → ℝ} {x v : E} :
    {t : ℝ | x + t • v ∈ secondOrderDifferentiabilitySet u} ⊆
      realScalarQuadraticEstimateSet (AleksandrovDifferentiability.lineRestriction u x v) := by
  intro t ht
  exact realScalarQuadraticEstimateAt_of_secondOrderDifferentiableAt ht.lineRestriction_at

/-- Ambient CLM expansion data along a line implies scalar quadratic estimate data for the
corresponding one-dimensional line restriction. -/
theorem preimage_lineMap_secondOrderCLMExpansionDataSet_subset_realScalarQuadraticEstimateSet
    {u : E → ℝ} {x v : E} :
    {t : ℝ | x + t • v ∈ secondOrderCLMExpansionDataSet u} ⊆
      realScalarQuadraticEstimateSet (AleksandrovDifferentiability.lineRestriction u x v) := by
  intro t ht
  exact realScalarQuadraticEstimateAt_of_secondOrderDifferentiableAt
    (preimage_lineMap_secondOrderCLMExpansionDataSet_subset ht)

/-- On a line restriction, project-level one-dimensional second-order differentiability gives the
punctured scalar quotient-estimate format used by the one-dimensional assembly layer. -/
theorem lineRestriction_secondOrderDifferentiabilitySet_subset_realScalarQuadraticQuotientSet
    {u : E → ℝ} {x v : E} :
    secondOrderDifferentiabilitySet (AleksandrovDifferentiability.lineRestriction u x v) ⊆
      realScalarQuadraticQuotientEstimateSet
        (AleksandrovDifferentiability.lineRestriction u x v) := by
  intro t ht
  exact
    (realScalarQuadraticEstimateAt_of_secondOrderDifferentiableAt ht).quadraticQuotientEstimateAt

/-- Ambient second-order differentiability along a line implies scalar quotient-estimate data
for the corresponding one-dimensional line restriction. -/
theorem preimage_lineMap_secondOrderDifferentiabilitySet_subset_realScalarQuadraticQuotientSet
    {u : E → ℝ} {x v : E} :
    {t : ℝ | x + t • v ∈ secondOrderDifferentiabilitySet u} ⊆
      realScalarQuadraticQuotientEstimateSet
        (AleksandrovDifferentiability.lineRestriction u x v) := by
  intro t ht
  exact
    (realScalarQuadraticEstimateAt_of_secondOrderDifferentiableAt
      ht.lineRestriction_at).quadraticQuotientEstimateAt

/-- Ambient CLM expansion data along a line implies scalar quotient-estimate data for the
corresponding one-dimensional line restriction. -/
theorem preimage_lineMap_secondOrderCLMExpansionDataSet_subset_realScalarQuadraticQuotientSet
    {u : E → ℝ} {x v : E} :
    {t : ℝ | x + t • v ∈ secondOrderCLMExpansionDataSet u} ⊆
      realScalarQuadraticQuotientEstimateSet
        (AleksandrovDifferentiability.lineRestriction u x v) := by
  intro t ht
  exact
    (realScalarQuadraticEstimateAt_of_secondOrderDifferentiableAt
      (preimage_lineMap_secondOrderCLMExpansionDataSet_subset ht)).quadraticQuotientEstimateAt

end AleksandrovDifferentiability
