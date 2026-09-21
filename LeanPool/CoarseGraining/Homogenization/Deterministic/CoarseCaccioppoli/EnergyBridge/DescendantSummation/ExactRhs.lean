/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.DescendantSummation.Averages

/-! # Exact Rhs -/

namespace Homogenization

noncomputable section

open scoped BigOperators ENNReal

/-!
# Descendant summation for the small-cube Caccioppoli route

The LaTeX proof estimates the cutoff pairing on small cubes and then sums over
those cubes.  This file isolates the measure-theoretic bookkeeping: a
cube-average over `Q` is the descendants-average of the cube-averages over the
depth-`j` descendants, hence its absolute value is controlled by the
descendants-average of the local absolute values.
-/

/-- Collapse a descendant average of exact flux-energy RHS values to the
parent raw-recursion RHS.

This is the core small-cube summation step.  The constant branch is summed by
finite Cauchy, so it only needs the parent `L²` norm of `u`; the centered branch
collapses by additivity of the energy average. -/
theorem descendantsAverage_fluxEnergyExactRhs_le_raw_of_pointwise_coefficients
    {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (a : CoeffField d) (s : ℝ)
    (u : Vec d → ℝ) (ξ : Vec d → Vec d) (energy : Vec d → ℝ)
    (Acirc1 AcircS B C K Alpha Bcross : ℝ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hK_nonneg : 0 ≤ K)
    (hKparent : K * cubeLpNorm Q (2 : ℝ≥0∞) u ≤ Bcross)
    (hconst : ∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
          (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ) ≤ K)
    (hcent : ∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactCenteredCoeff R a s ξ Acirc1 AcircS B C ≤ Alpha) :
    descendantsAverage Q j
        (fun R =>
          coarseCaccioppoliFluxEnergyExactRhs R a s u ξ energy Acirc1 AcircS B C) ≤
      Alpha * cubeAverage Q energy + Bcross * Real.sqrt (cubeAverage Q energy) := by
  have hE_nonneg :
      ∀ R ∈ descendantsAtDepth Q j, 0 ≤ cubeAverage R energy := by
    intro R hR
    exact cubeAverage_nonneg_of_nonneg_on (Q := R)
      (fun x hx => henergy_nonneg x (cubeSet_subset_of_mem_descendantsAtDepth hR hx))
  have hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseCaccioppoliFluxEnergyExactRhs R a s u ξ energy Acirc1 AcircS B C ≤
          K * (cubeLpNorm R (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage R energy)) +
            Alpha * cubeAverage R energy := by
    intro R hR
    have hconstR :
        coarseCaccioppoliFluxEnergyExactConstantRhs R a u ξ energy B ≤
          K * (cubeLpNorm R (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage R energy)) := by
      rw [coarseCaccioppoliFluxEnergyExactConstantRhs_eq_coeff_mul]
      unfold coarseCaccioppoliConstantCutoffSize
      have hscaled :
          cubeLpNorm R (2 : ℝ≥0∞) u *
              (coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
                (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ)) *
              Real.sqrt (cubeAverage R energy) ≤
            cubeLpNorm R (2 : ℝ≥0∞) u * K *
              Real.sqrt (cubeAverage R energy) := by
        have hleft :=
          mul_le_mul_of_nonneg_left (hconst R hR)
            (cubeLpNorm_nonneg R (2 : ℝ≥0∞) u)
        exact mul_le_mul_of_nonneg_right hleft (Real.sqrt_nonneg _)
      calc
        (coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
            (cubeLpNorm R (2 : ℝ≥0∞) u *
              (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ))) *
            Real.sqrt (cubeAverage R energy)
            =
          cubeLpNorm R (2 : ℝ≥0∞) u *
              (coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
                (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ)) *
              Real.sqrt (cubeAverage R energy) := by
            ring
        _ ≤
          cubeLpNorm R (2 : ℝ≥0∞) u * K *
              Real.sqrt (cubeAverage R energy) := hscaled
        _ =
          K * (cubeLpNorm R (2 : ℝ≥0∞) u *
              Real.sqrt (cubeAverage R energy)) := by
            ring
    have hcentR :
        coarseCaccioppoliFluxEnergyExactCenteredRhs R a s ξ energy Acirc1 AcircS B C ≤
          Alpha * cubeAverage R energy := by
      rw [coarseCaccioppoliFluxEnergyExactCenteredRhs_eq_coeff_mul_sqrt_sq]
      have hsqrt_sq :
          Real.sqrt (cubeAverage R energy) * Real.sqrt (cubeAverage R energy) =
            cubeAverage R energy := by
        simpa [pow_two] using Real.sq_sqrt (hE_nonneg R hR)
      rw [hsqrt_sq]
      exact mul_le_mul_of_nonneg_right (hcent R hR) (hE_nonneg R hR)
    rw [coarseCaccioppoliFluxEnergyExactRhs_eq_constant_add_centered]
    exact add_le_add hconstR hcentR
  have havg_point :
      descendantsAverage Q j
          (fun R =>
            coarseCaccioppoliFluxEnergyExactRhs R a s u ξ energy Acirc1 AcircS B C) ≤
        descendantsAverage Q j
          (fun R =>
            K * (cubeLpNorm R (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage R energy)) +
              Alpha * cubeAverage R energy) :=
    descendantsAverage_le_descendantsAverage Q j hpoint
  have hsplit :
      descendantsAverage Q j
          (fun R =>
            K * (cubeLpNorm R (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage R energy)) +
              Alpha * cubeAverage R energy) =
        K * descendantsAverage Q j
            (fun R => cubeLpNorm R (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage R energy)) +
          Alpha * descendantsAverage Q j (fun R => cubeAverage R energy) := by
    rw [descendantsAverage_add_local]
    rw [descendantsAverage_mul_left, descendantsAverage_mul_left]
  have hA :
      descendantsAverage Q j
          (fun R => cubeLpNorm R (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage R energy)) ≤
        cubeLpNorm Q (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage Q energy) :=
    descendantsAverage_cubeLpNorm_two_mul_sqrt_cubeAverage_le
      Q j u energy hu henergy_nonneg henergy_int
  have hconst_avg :
      K * descendantsAverage Q j
          (fun R => cubeLpNorm R (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage R energy)) ≤
        Bcross * Real.sqrt (cubeAverage Q energy) := by
    calc
      K * descendantsAverage Q j
          (fun R => cubeLpNorm R (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage R energy))
          ≤ K * (cubeLpNorm Q (2 : ℝ≥0∞) u *
              Real.sqrt (cubeAverage Q energy)) := by
            exact mul_le_mul_of_nonneg_left hA hK_nonneg
      _ = (K * cubeLpNorm Q (2 : ℝ≥0∞) u) *
              Real.sqrt (cubeAverage Q energy) := by
            ring
      _ ≤ Bcross * Real.sqrt (cubeAverage Q energy) := by
            exact mul_le_mul_of_nonneg_right hKparent (Real.sqrt_nonneg _)
  have havgE_eq :
      descendantsAverage Q j (fun R => cubeAverage R energy) = cubeAverage Q energy := by
    simpa using
      (cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
        (Q := Q) (j := j) (f := energy) henergy_int).symm
  calc
    descendantsAverage Q j
        (fun R =>
          coarseCaccioppoliFluxEnergyExactRhs R a s u ξ energy Acirc1 AcircS B C)
        ≤ descendantsAverage Q j
          (fun R =>
            K * (cubeLpNorm R (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage R energy)) +
              Alpha * cubeAverage R energy) := havg_point
    _ =
        K * descendantsAverage Q j
            (fun R => cubeLpNorm R (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage R energy)) +
          Alpha * descendantsAverage Q j (fun R => cubeAverage R energy) := hsplit
    _ ≤ Bcross * Real.sqrt (cubeAverage Q energy) +
          Alpha * cubeAverage Q energy := by
        exact add_le_add hconst_avg (by simp [havgE_eq])
    _ = Alpha * cubeAverage Q energy +
          Bcross * Real.sqrt (cubeAverage Q energy) := by
        ring

/-- Variable-`Acirc` version of
`descendantsAverage_fluxEnergyExactRhs_le_raw_of_pointwise_coefficients`.

The exact RHS on each descendant uses the local values `Acirc1 R` and
`AcircS R`; the endpoint raw RHS is unchanged. -/
theorem descendantsAverage_fluxEnergyExactRhs_le_raw_of_pointwise_coefficients_variableAcirc
    {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (a : CoeffField d) (s : ℝ)
    (u : Vec d → ℝ) (ξ : Vec d → Vec d) (energy : Vec d → ℝ)
    (Acirc1 AcircS : TriadicCube d → ℝ) (B C K Alpha Bcross : ℝ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hK_nonneg : 0 ≤ K)
    (hKparent : K * cubeLpNorm Q (2 : ℝ≥0∞) u ≤ Bcross)
    (hconst : ∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
          (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ) ≤ K)
    (hcent : ∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactCenteredCoeff R a s ξ (Acirc1 R) (AcircS R) B C ≤
        Alpha) :
    descendantsAverage Q j
        (fun R =>
          coarseCaccioppoliFluxEnergyExactRhs R a s u ξ energy (Acirc1 R) (AcircS R) B C) ≤
      Alpha * cubeAverage Q energy + Bcross * Real.sqrt (cubeAverage Q energy) := by
  have hE_nonneg :
      ∀ R ∈ descendantsAtDepth Q j, 0 ≤ cubeAverage R energy := by
    intro R hR
    exact cubeAverage_nonneg_of_nonneg_on (Q := R)
      (fun x hx => henergy_nonneg x (cubeSet_subset_of_mem_descendantsAtDepth hR hx))
  have hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseCaccioppoliFluxEnergyExactRhs R a s u ξ energy (Acirc1 R) (AcircS R) B C ≤
          K * (cubeLpNorm R (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage R energy)) +
            Alpha * cubeAverage R energy := by
    intro R hR
    have hconstR :
        coarseCaccioppoliFluxEnergyExactConstantRhs R a u ξ energy B ≤
          K * (cubeLpNorm R (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage R energy)) := by
      rw [coarseCaccioppoliFluxEnergyExactConstantRhs_eq_coeff_mul]
      unfold coarseCaccioppoliConstantCutoffSize
      have hscaled :
          cubeLpNorm R (2 : ℝ≥0∞) u *
              (coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
                (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ)) *
              Real.sqrt (cubeAverage R energy) ≤
            cubeLpNorm R (2 : ℝ≥0∞) u * K *
              Real.sqrt (cubeAverage R energy) := by
        have hleft :=
          mul_le_mul_of_nonneg_left (hconst R hR)
            (cubeLpNorm_nonneg R (2 : ℝ≥0∞) u)
        exact mul_le_mul_of_nonneg_right hleft (Real.sqrt_nonneg _)
      calc
        (coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
            (cubeLpNorm R (2 : ℝ≥0∞) u *
              (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ))) *
            Real.sqrt (cubeAverage R energy)
            =
          cubeLpNorm R (2 : ℝ≥0∞) u *
              (coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
                (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ)) *
              Real.sqrt (cubeAverage R energy) := by
            ring
        _ ≤
          cubeLpNorm R (2 : ℝ≥0∞) u * K *
              Real.sqrt (cubeAverage R energy) := hscaled
        _ =
          K * (cubeLpNorm R (2 : ℝ≥0∞) u *
              Real.sqrt (cubeAverage R energy)) := by
            ring
    have hcentR :
        coarseCaccioppoliFluxEnergyExactCenteredRhs R a s ξ energy (Acirc1 R) (AcircS R) B C ≤
          Alpha * cubeAverage R energy := by
      rw [coarseCaccioppoliFluxEnergyExactCenteredRhs_eq_coeff_mul_sqrt_sq]
      have hsqrt_sq :
          Real.sqrt (cubeAverage R energy) * Real.sqrt (cubeAverage R energy) =
            cubeAverage R energy := by
        simpa [pow_two] using Real.sq_sqrt (hE_nonneg R hR)
      rw [hsqrt_sq]
      exact mul_le_mul_of_nonneg_right (hcent R hR) (hE_nonneg R hR)
    rw [coarseCaccioppoliFluxEnergyExactRhs_eq_constant_add_centered]
    exact add_le_add hconstR hcentR
  have havg_point :
      descendantsAverage Q j
          (fun R =>
            coarseCaccioppoliFluxEnergyExactRhs R a s u ξ energy (Acirc1 R) (AcircS R) B C) ≤
        descendantsAverage Q j
          (fun R =>
            K * (cubeLpNorm R (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage R energy)) +
              Alpha * cubeAverage R energy) :=
    descendantsAverage_le_descendantsAverage Q j hpoint
  have hsplit :
      descendantsAverage Q j
          (fun R =>
            K * (cubeLpNorm R (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage R energy)) +
              Alpha * cubeAverage R energy) =
        K * descendantsAverage Q j
            (fun R => cubeLpNorm R (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage R energy)) +
          Alpha * descendantsAverage Q j (fun R => cubeAverage R energy) := by
    rw [descendantsAverage_add_local]
    rw [descendantsAverage_mul_left, descendantsAverage_mul_left]
  have hA :
      descendantsAverage Q j
          (fun R => cubeLpNorm R (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage R energy)) ≤
        cubeLpNorm Q (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage Q energy) :=
    descendantsAverage_cubeLpNorm_two_mul_sqrt_cubeAverage_le
      Q j u energy hu henergy_nonneg henergy_int
  have hconst_avg :
      K * descendantsAverage Q j
          (fun R => cubeLpNorm R (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage R energy)) ≤
        Bcross * Real.sqrt (cubeAverage Q energy) := by
    calc
      K * descendantsAverage Q j
          (fun R => cubeLpNorm R (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage R energy))
          ≤ K * (cubeLpNorm Q (2 : ℝ≥0∞) u *
              Real.sqrt (cubeAverage Q energy)) := by
            exact mul_le_mul_of_nonneg_left hA hK_nonneg
      _ = (K * cubeLpNorm Q (2 : ℝ≥0∞) u) *
              Real.sqrt (cubeAverage Q energy) := by
            ring
      _ ≤ Bcross * Real.sqrt (cubeAverage Q energy) := by
            exact mul_le_mul_of_nonneg_right hKparent (Real.sqrt_nonneg _)
  have havgE_eq :
      descendantsAverage Q j (fun R => cubeAverage R energy) = cubeAverage Q energy := by
    simpa using
      (cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
        (Q := Q) (j := j) (f := energy) henergy_int).symm
  calc
    descendantsAverage Q j
        (fun R =>
          coarseCaccioppoliFluxEnergyExactRhs R a s u ξ energy (Acirc1 R) (AcircS R) B C)
        ≤ descendantsAverage Q j
          (fun R =>
            K * (cubeLpNorm R (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage R energy)) +
              Alpha * cubeAverage R energy) := havg_point
    _ =
        K * descendantsAverage Q j
            (fun R => cubeLpNorm R (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage R energy)) +
          Alpha * descendantsAverage Q j (fun R => cubeAverage R energy) := hsplit
    _ ≤ Bcross * Real.sqrt (cubeAverage Q energy) +
          Alpha * cubeAverage Q energy := by
        exact add_le_add hconst_avg (by simp [havgE_eq])
    _ = Alpha * cubeAverage Q energy +
          Bcross * Real.sqrt (cubeAverage Q energy) := by
        ring

/-- Localized-energy version of the variable-`Acirc` exact-RHS descendant
collapse.  The local RHS values use the energy density cut down to the outer
scaled cube, so the endpoint is the outer localized profile rather than the
full parent cube average. -/
theorem
    descendantsAverage_fluxEnergyExactRhs_le_localized_raw_of_pointwise_coefficients_variableAcirc
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (ρ : ℝ)
    (a : CoeffField d) (s : ℝ)
    (u : Vec d → ℝ) (ξ : Vec d → Vec d) (energy : Vec d → ℝ)
    (Acirc1 AcircS : TriadicCube d → ℝ) (B C K Alpha Bcross : ℝ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hK_nonneg : 0 ≤ K)
    (hKparent : K * cubeLpNorm Q (2 : ℝ≥0∞) u ≤ Bcross)
    (hconst : ∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
          (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ) ≤ K)
    (hcent : ∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactCenteredCoeff R a s ξ (Acirc1 R) (AcircS R) B C ≤
        Alpha) :
    descendantsAverage Q j
        (fun R =>
          coarseCaccioppoliFluxEnergyExactRhs R a s u ξ
            ((scaledClosedCubeSet Q ρ).indicator energy)
            (Acirc1 R) (AcircS R) B C) ≤
      Alpha * coarseCaccioppoliLocalizedEnergyProfile Q ρ energy +
        Bcross * Real.sqrt (coarseCaccioppoliLocalizedEnergyProfile Q ρ energy) := by
  have hloc_nonneg :
      ∀ x ∈ cubeSet Q, 0 ≤ (scaledClosedCubeSet Q ρ).indicator energy x := by
    intro x hxQ
    by_cases hxρ : x ∈ scaledClosedCubeSet Q ρ
    · simpa [Set.indicator_of_mem hxρ] using henergy_nonneg x hxQ
    · simp [Set.indicator_of_notMem hxρ]
  have hloc_int :
      MeasureTheory.IntegrableOn ((scaledClosedCubeSet Q ρ).indicator energy)
        (cubeSet Q) MeasureTheory.volume :=
    integrableOn_indicator_scaledClosedCubeSet_of_integrableOn_cubeSet Q ρ henergy_int
  have hraw :=
    descendantsAverage_fluxEnergyExactRhs_le_raw_of_pointwise_coefficients_variableAcirc
      Q j a s u ξ ((scaledClosedCubeSet Q ρ).indicator energy) Acirc1 AcircS
      B C K Alpha Bcross hu hloc_nonneg hloc_int hK_nonneg hKparent hconst hcent
  simpa [coarseCaccioppoliLocalizedEnergyProfile] using hraw

/-- Arbitrary-center local-patch version of the variable-`Acirc` exact-RHS
descendant collapse. -/
theorem
    descendantsAverage_fluxEnergyExactRhs_le_localPatch_raw_of_pointwise_coefficients_variableAcirc
    {d : ℕ} (Q : TriadicCube d) (center : Vec d) (j : ℕ) (rho : ℝ)
    (a : CoeffField d) (s : ℝ)
    (u : Vec d → ℝ) (ξ : Vec d → Vec d) (energy : Vec d → ℝ)
    (Acirc1 AcircS : TriadicCube d → ℝ) (B C K Alpha Bcross : ℝ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hK_nonneg : 0 ≤ K)
    (hKparent : K * cubeLpNorm Q (2 : ℝ≥0∞) u ≤ Bcross)
    (hconst : ∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
          (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ) ≤ K)
    (hcent : ∀ R ∈ descendantsAtDepth Q j,
      coarseCaccioppoliFluxEnergyExactCenteredCoeff R a s ξ (Acirc1 R) (AcircS R) B C ≤
        Alpha) :
    descendantsAverage Q j
        (fun R =>
          coarseCaccioppoliFluxEnergyExactRhs R a s u ξ
            ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)
            (Acirc1 R) (AcircS R) B C) ≤
      Alpha * coarseCaccioppoliLocalEnergyProfile Q center rho energy +
        Bcross * Real.sqrt
          (coarseCaccioppoliLocalEnergyProfile Q center rho energy) := by
  have hloc_nonneg :
      ∀ x ∈ cubeSet Q,
        0 ≤ (coarseCaccioppoliLocalClosedCube Q center rho).indicator energy x := by
    intro x hxQ
    by_cases hxrho : x ∈ coarseCaccioppoliLocalClosedCube Q center rho
    · simpa [Set.indicator_of_mem hxrho] using henergy_nonneg x hxQ
    · simp [Set.indicator_of_notMem hxrho]
  have hloc_int :
      MeasureTheory.IntegrableOn
          ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)
          (cubeSet Q) MeasureTheory.volume :=
    integrableOn_indicator_coarseCaccioppoliLocalClosedCube_of_integrableOn_cubeSet
      Q center rho henergy_int
  have hraw :=
    descendantsAverage_fluxEnergyExactRhs_le_raw_of_pointwise_coefficients_variableAcirc
      Q j a s u ξ
      ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)
      Acirc1 AcircS B C K Alpha Bcross hu hloc_nonneg hloc_int
      hK_nonneg hKparent hconst hcent
  simpa [coarseCaccioppoliLocalEnergyProfile] using hraw

end

end Homogenization
