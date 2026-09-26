/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.DescendantSummation.Gradient

/-! # Averages -/

@[expose] public section

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

/-- Triangle inequality after decomposing a cube average into depth-`j`
descendant cube averages. -/
theorem abs_cubeAverage_le_descendantsAverage_abs_cubeAverage_of_integrableOn
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (f : Vec d → ℝ)
    (hf : MeasureTheory.IntegrableOn f (cubeSet Q) MeasureTheory.volume) :
    |cubeAverage Q f| ≤ descendantsAverage Q j (fun R => |cubeAverage R f|) := by
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
    (Q := Q) (j := j) (f := f) hf]
  unfold descendantsAverage
  have hcard_nonneg : 0 ≤ (((descendantsAtDepth Q j).card : ℝ)⁻¹) := by
    positivity
  calc
    |((↑(descendantsAtDepth Q j).card)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j, cubeAverage R f)|
        = ((↑(descendantsAtDepth Q j).card)⁻¹) *
            |∑ R ∈ descendantsAtDepth Q j, cubeAverage R f| := by
              rw [abs_mul, abs_of_nonneg hcard_nonneg]
    _ ≤ ((↑(descendantsAtDepth Q j).card)⁻¹) *
        ∑ R ∈ descendantsAtDepth Q j, |cubeAverage R f| := by
          exact mul_le_mul_of_nonneg_left
            (Finset.abs_sum_le_sum_abs _ _) hcard_nonneg
    _ = (↑(descendantsAtDepth Q j).card)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j, |cubeAverage R f| := by
          rfl

/-- If each depth-`j` descendant cube average is bounded by a local RHS, then
the parent cube average is bounded by the descendants-average of those local
RHS values. -/
theorem abs_cubeAverage_le_descendantsAverage_of_local_abs_bounds
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (f : Vec d → ℝ) (B : TriadicCube d → ℝ)
    (hf : MeasureTheory.IntegrableOn f (cubeSet Q) MeasureTheory.volume)
    (hlocal : ∀ R ∈ descendantsAtDepth Q j, |cubeAverage R f| ≤ B R) :
    |cubeAverage Q f| ≤ descendantsAverage Q j B := by
  refine
    le_trans
      (abs_cubeAverage_le_descendantsAverage_abs_cubeAverage_of_integrableOn
        Q j f hf) ?_
  unfold descendantsAverage
  have hcard_nonneg : 0 ≤ (((descendantsAtDepth Q j).card : ℝ)⁻¹) := by
    positivity
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun R hR => hlocal R hR) hcard_nonneg

/-- Descendant summation specialized to the Caccioppoli cutoff pairing.  The
local estimates may come from any source, in particular from
`abs_cubeAverage_vecDot_scalar_smul_le_singleCubeBoundaryNoteRhs_of_parentQuantitativeCutoff_on_descendant`. -/
theorem abs_cubeAverage_vecDot_scalar_smul_le_descendantsAverage_of_local_bounds
    {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (flux ξ : Vec d → Vec d) (u : Vec d → ℝ) (B : TriadicCube d → ℝ)
    (hf :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (flux x) (u x • ξ x))
        (cubeSet Q) MeasureTheory.volume)
    (hlocal :
      ∀ R ∈ descendantsAtDepth Q j,
        |cubeAverage R (fun x => vecDot (flux x) (u x • ξ x))| ≤ B R) :
    |cubeAverage Q (fun x => vecDot (flux x) (u x • ξ x))| ≤
      descendantsAverage Q j B := by
  exact
    abs_cubeAverage_le_descendantsAverage_of_local_abs_bounds
      Q j (fun x => vecDot (flux x) (u x • ξ x)) B hf hlocal

/-- If a cube lies outside the outer support of a quantitative cutoff, then
the local cutoff-gradient flux pairing over that cube is zero. -/
theorem cubeAverage_vecDot_scalar_smul_scalarCutoffGradientField_eq_zero_of_forall_notMem_scaledClosedCubeSet
    {d : ℕ} {Q R : TriadicCube d} {ρ₁ ρ₂ : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (flux : Vec d → Vec d) (u : Vec d → ℝ)
    (hout : ∀ x ∈ cubeSet R, x ∉ scaledClosedCubeSet Q ρ₂) :
    cubeAverage R
        (fun x => vecDot (flux x) (u x • scalarCutoffGradientField (η : Vec d → ℝ) x)) =
      0 := by
  rw [← cubeAverage_const (Q := R) (c := 0)]
  apply cubeAverage_congr_on_cubeSet
  intro x hxR
  have hξ :
      scalarCutoffGradientField (η : Vec d → ℝ) x = 0 :=
    scalarCutoffGradientField_eq_zero_of_notMem_tsupport
      (fun hx_support => hout x hxR (η.tsupport_subset_scaledClosedCubeSet hx_support))
  simp [hξ, vecDot_zero_right]

theorem descendantsAverage_add_local {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (F G : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => F R + G R) =
      descendantsAverage Q j F + descendantsAverage Q j G := by
  classical
  let D := descendantsAtDepth Q j
  change (↑D.card)⁻¹ * D.sum (fun R => F R + G R) =
    (↑D.card)⁻¹ * D.sum F + (↑D.card)⁻¹ * D.sum G
  rw [Finset.sum_add_distrib, left_distrib]

theorem descendantsAverage_const_local {d : ℕ} (Q : TriadicCube d) (j : ℕ) (c : ℝ) :
    descendantsAverage Q j (fun _ => c) = c := by
  classical
  change ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
      (descendantsAtDepth Q j).sum (fun _ => c) = c
  have hD : (descendantsAtDepth Q j).Nonempty := descendantsAtDepth_nonempty Q j
  have hcard : (((descendantsAtDepth Q j).card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hD)
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- Jensen/Cauchy for the finite descendant average: the average of square
roots is controlled by the square root of the average. -/
theorem descendantsAverage_sqrt_le_sqrt_descendantsAverage_of_nonneg
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → ℝ)
    (hF : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ F R) :
    descendantsAverage Q j (fun R => Real.sqrt (F R)) ≤
      Real.sqrt (descendantsAverage Q j F) := by
  have hpq : Real.HolderConjugate (2 : ℝ) (2 : ℝ) := by
    refine ⟨?_, ?_, ?_⟩ <;> norm_num
  have hholder :=
    descendantsAverage_mul_le_Lp_mul_Lq_of_nonneg Q j
      (fun R => Real.sqrt (F R)) (fun _ => (1 : ℝ)) hpq
      (fun R _ => Real.sqrt_nonneg (F R))
      (fun _ _ => by norm_num)
  have hleft :
      descendantsAverage Q j (fun R => Real.sqrt (F R) * (1 : ℝ)) =
        descendantsAverage Q j (fun R => Real.sqrt (F R)) := by
    simp
  have hsq :
      descendantsAverage Q j (fun R => (Real.sqrt (F R)) ^ (2 : ℝ)) =
        descendantsAverage Q j F := by
    change ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        (descendantsAtDepth Q j).sum (fun R => (Real.sqrt (F R)) ^ (2 : ℝ)) =
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ * (descendantsAtDepth Q j).sum F
    congr 1
    exact Finset.sum_congr rfl
      (fun R hR => by
        simpa [pow_two] using Real.sq_sqrt (hF R hR))
  have hone :
      descendantsAverage Q j (fun _ => ((1 : ℝ) ^ (2 : ℝ))) = (1 : ℝ) := by
    simp
  have hmain :
      descendantsAverage Q j (fun R => Real.sqrt (F R)) ≤
        (descendantsAverage Q j F) ^ (1 / (2 : ℝ)) * (1 : ℝ) := by
    have hholder' := hholder
    rw [hleft, hsq, hone] at hholder'
    simpa using hholder'
  simpa [Real.sqrt_eq_rpow] using hmain

/-- Descendant Cauchy estimate for the constant branch of the small-cube
Caccioppoli proof.

This is the step that lets the proof use the parent normalized `L²` norm of
`u` after summing over descendants, instead of requiring a pointwise `L²`
bound on every small cube. -/
theorem descendantsAverage_cubeLpNorm_two_mul_sqrt_cubeAverage_le
    {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (u energy : Vec d → ℝ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume) :
    descendantsAverage Q j
        (fun R => cubeLpNorm R (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage R energy)) ≤
      cubeLpNorm Q (2 : ℝ≥0∞) u * Real.sqrt (cubeAverage Q energy) := by
  have hpq : Real.HolderConjugate (2 : ℝ) (2 : ℝ) := by
    refine ⟨?_, ?_, ?_⟩ <;> norm_num
  have hE_nonneg :
      ∀ R ∈ descendantsAtDepth Q j, 0 ≤ cubeAverage R energy := by
    intro R hR
    exact cubeAverage_nonneg_of_nonneg_on (Q := R)
      (fun x hx => henergy_nonneg x (cubeSet_subset_of_mem_descendantsAtDepth hR hx))
  have hholder :=
    descendantsAverage_mul_le_Lp_mul_Lq_of_nonneg Q j
      (fun R => cubeLpNorm R (2 : ℝ≥0∞) u)
      (fun R => Real.sqrt (cubeAverage R energy)) hpq
      (fun R _ => cubeLpNorm_nonneg R (2 : ℝ≥0∞) u)
      (fun R _ => Real.sqrt_nonneg (cubeAverage R energy))
  have hA :
      descendantsAverage Q j (fun R => (cubeLpNorm R (2 : ℝ≥0∞) u) ^ 2) =
        (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2 := by
    change cubeL2ScalarDepthAverage Q u j =
      (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2
    rw [cubeL2ScalarDepthAverage_eq_cubeLpNorm_two_sq Q u j hu]
  have hB :
      descendantsAverage Q j (fun R => (Real.sqrt (cubeAverage R energy)) ^ 2) =
        cubeAverage Q energy := by
    have havg_eq :
        descendantsAverage Q j (fun R => cubeAverage R energy) = cubeAverage Q energy := by
      simpa using
        (cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
          (Q := Q) (j := j) (f := energy) henergy_int).symm
    change ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        (descendantsAtDepth Q j).sum
          (fun R => (Real.sqrt (cubeAverage R energy)) ^ 2) =
      cubeAverage Q energy
    rw [← havg_eq]
    unfold descendantsAverage
    congr 1
    exact Finset.sum_congr rfl
      (fun R hR => by
        simpa [pow_two] using Real.sq_sqrt (hE_nonneg R hR))
  have hmain :
      descendantsAverage Q j
          (fun R => cubeLpNorm R (2 : ℝ≥0∞) u *
            Real.sqrt (cubeAverage R energy)) ≤
        ((cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2) ^ (1 / (2 : ℝ)) *
          (cubeAverage Q energy) ^ (1 / (2 : ℝ)) := by
    simpa [Real.rpow_two, hA, hB] using hholder
  have hU :
      ((cubeLpNorm Q (2 : ℝ≥0∞) u) ^ 2) ^ ((2 : ℝ)⁻¹) =
        cubeLpNorm Q (2 : ℝ≥0∞) u := by
    simpa using
      sq_rpow_half_eq_of_nonneg (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) u)
  have hE :
      (cubeAverage Q energy) ^ ((2 : ℝ)⁻¹) =
        Real.sqrt (cubeAverage Q energy) := by
    simp [Real.sqrt_eq_rpow]
  simpa [hU, hE] using hmain

/-- Descendant averages of the outer-localized energy density collapse to the
outer localized parent profile, not to the full-cube energy average. -/
theorem descendantsAverage_cubeAverage_indicator_scaledClosedCubeSet_eq_localizedEnergyProfile
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (ρ : ℝ) (energy : Vec d → ℝ)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume) :
    descendantsAverage Q j
        (fun R => cubeAverage R ((scaledClosedCubeSet Q ρ).indicator energy)) =
      coarseCaccioppoliLocalizedEnergyProfile Q ρ energy := by
  have hloc_int :
      MeasureTheory.IntegrableOn ((scaledClosedCubeSet Q ρ).indicator energy)
        (cubeSet Q) MeasureTheory.volume :=
    integrableOn_indicator_scaledClosedCubeSet_of_integrableOn_cubeSet Q ρ henergy_int
  unfold coarseCaccioppoliLocalizedEnergyProfile
  exact
    (cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
      Q j ((scaledClosedCubeSet Q ρ).indicator energy) hloc_int).symm

/-- Finite Cauchy for the constant branch after replacing the energy density by
its outer-localized version.  This is the summation shape needed by the
localized raw Caccioppoli repair. -/
theorem descendantsAverage_cubeLpNorm_two_mul_sqrt_cubeAverage_indicator_scaledClosedCubeSet_le
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (ρ : ℝ)
    (u energy : Vec d → ℝ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume) :
    descendantsAverage Q j
        (fun R =>
          cubeLpNorm R (2 : ℝ≥0∞) u *
            Real.sqrt (cubeAverage R ((scaledClosedCubeSet Q ρ).indicator energy))) ≤
      cubeLpNorm Q (2 : ℝ≥0∞) u *
        Real.sqrt (coarseCaccioppoliLocalizedEnergyProfile Q ρ energy) := by
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
  have hmain :=
    descendantsAverage_cubeLpNorm_two_mul_sqrt_cubeAverage_le
      Q j u ((scaledClosedCubeSet Q ρ).indicator energy) hu hloc_nonneg hloc_int
  simpa [coarseCaccioppoliLocalizedEnergyProfile] using hmain

/-- Descendant averages of the arbitrary-center local-patch energy density
collapse to the corresponding local parent profile. -/
theorem descendantsAverage_cubeAverage_indicator_coarseCaccioppoliLocalClosedCube_eq_localEnergyProfile
    {d : ℕ} (Q : TriadicCube d) (center : Vec d) (j : ℕ) (rho : ℝ)
    (energy : Vec d → ℝ)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume) :
    descendantsAverage Q j
        (fun R =>
          cubeAverage R
            ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)) =
      coarseCaccioppoliLocalEnergyProfile Q center rho energy := by
  have hloc_int :
      MeasureTheory.IntegrableOn
          ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)
          (cubeSet Q) MeasureTheory.volume :=
    integrableOn_indicator_coarseCaccioppoliLocalClosedCube_of_integrableOn_cubeSet
      Q center rho henergy_int
  unfold coarseCaccioppoliLocalEnergyProfile
  exact
    (cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
      Q j
      ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)
      hloc_int).symm

/-- Finite Cauchy for the constant branch after replacing the energy density by
the arbitrary-center local-patch localization. -/
theorem
    descendantsAverage_cubeLpNorm_two_mul_sqrt_cubeAverage_indicator_coarseCaccioppoliLocalClosedCube_le
    {d : ℕ} (Q : TriadicCube d) (center : Vec d) (j : ℕ) (rho : ℝ)
    (u energy : Vec d → ℝ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume) :
    descendantsAverage Q j
        (fun R =>
          cubeLpNorm R (2 : ℝ≥0∞) u *
            Real.sqrt
              (cubeAverage R
                ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy))) ≤
      cubeLpNorm Q (2 : ℝ≥0∞) u *
        Real.sqrt (coarseCaccioppoliLocalEnergyProfile Q center rho energy) := by
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
  have hmain :=
    descendantsAverage_cubeLpNorm_two_mul_sqrt_cubeAverage_le
      Q j u
      ((coarseCaccioppoliLocalClosedCube Q center rho).indicator energy)
      hu hloc_nonneg hloc_int
  simpa [coarseCaccioppoliLocalEnergyProfile] using hmain

end

end Homogenization
