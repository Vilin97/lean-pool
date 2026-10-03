/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.FirstOrder
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.Oscillation

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Cube-local good-set coverage

This file packages the source proof's countable good-set cover
`Q_1 = ⋃_m Omega_m` up to a null set, after first differentiability a.e. and finite
upper-contact opening a.e. have been established.
-/

@[expose] public noncomputable section

open MeasureTheory
open Asymptotics
open scoped MeasureTheory
open scoped Topology

namespace AleksandrovDifferentiability

/-- At a source good point, the slope in the upper-contact trap can be normalized to the
Fréchet gradient. This is the cube-local form of the source proof's choice
`p_0 = grad u(x_0)`. -/
theorem cubeGoodSet_hasSourceCubeAffineRemainderOpeningAtMost_frechetGradient
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {A : ℝ} {x : SourceCubeSpace n}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u) (hxgood : x ∈ cubeGoodSet n u A) :
    HasSourceCubeAffineRemainderOpeningAtMost n u x (frechetGradient u x) A := by
  rcases (mem_cubeGoodSet.mp hxgood) with ⟨hxQ, hdiff, hopening⟩
  have hxInterior : x ∈ interior (sourceOpenCube n 3) :=
    sourceOpenCube_one_subset_interior_three hxQ
  rcases exists_uniform_affineRemainder_trap_of_upperContactOpening_of_convex_of_mem_interior
      hopening hu hxInterior with ⟨p, hp, _hfixed, htrap⟩
  have hp_eq : p = frechetGradient u x := by
    have hs : sourceOpenCube n 3 ∈ 𝓝 x :=
      (isOpen_sourceOpenCube (n := n) 3).mem_nhds (interior_subset hxInterior)
    change p = gradient u x
    exact hp.eq_gradient_of_differentiableAt hs hdiff
  subst p
  intro η hη
  refine ⟨interior_subset hxInterior, ?_⟩
  intro y hy
  exact (htrap η hη y hy).2

/-- Source-good-point affine-remainder trap with the Fréchet-gradient slope. -/
theorem cubeGoodSet_affineRemainder_trap_frechetGradient
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {A η : ℝ} {x y : SourceCubeSpace n}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u) (hxgood : x ∈ cubeGoodSet n u A)
    (hη : 0 < η) (hy : y ∈ sourceOpenCube n 3) :
    0 ≤ affineRemainder u x (frechetGradient u x) y ∧
      affineRemainder u x (frechetGradient u x) y ≤
        ((A + η) / 2) * ‖y - x‖ ^ 2 := by
  rcases (mem_cubeGoodSet.mp hxgood) with ⟨hxQ, _hdiff, hopening⟩
  have hxInterior : x ∈ interior (sourceOpenCube n 3) :=
    sourceOpenCube_one_subset_interior_three hxQ
  have hopeningGradient :
      HasSourceCubeAffineRemainderOpeningAtMost n u x (frechetGradient u x) A :=
    cubeGoodSet_hasSourceCubeAffineRemainderOpeningAtMost_frechetGradient hu hxgood
  have hsubgradient :
      SubgradientOn (sourceOpenCube n 3) u x (frechetGradient u x) := by
    rcases exists_uniform_affineRemainder_trap_of_upperContactOpening_of_convex_of_mem_interior
        hopening hu hxInterior with ⟨p, hp, _hfixed, _htrap⟩
    have hdiff : DifferentiableAt ℝ u x := (mem_cubeGoodSet.mp hxgood).2.1
    have hp_eq : p = frechetGradient u x := by
      have hs : sourceOpenCube n 3 ∈ 𝓝 x :=
        (isOpen_sourceOpenCube (n := n) 3).mem_nhds (interior_subset hxInterior)
      change p = gradient u x
      exact hp.eq_gradient_of_differentiableAt hs hdiff
    simpa [hp_eq] using hp
  exact affineRemainder_nonneg_and_le_of_subgradient_of_upperContactOpening hsubgradient
    hopeningGradient.hasUpperContactWithSlopeOpeningAtMostOn hη hy

/-- Source-good-point directional comparison for gradients.

If `x0` is good and `x1` is a differentiability point, convexity at `x1` and the good-point
quadratic trap at `x0` control the component of `grad u x1 - grad u x0` in any tested
direction whose endpoint remains in `Q_3`. -/
theorem cubeGoodSet_smul_inner_gradient_sub_le
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {A η δ : ℝ}
    {x0 x1 v : SourceCubeSpace n}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u) (hx0good : x0 ∈ cubeGoodSet n u A)
    (hx1Q : x1 ∈ sourceOpenCube n 1) (hd1 : DifferentiableAt ℝ u x1)
    (hη : 0 < η) (hy : x1 + δ • v ∈ sourceOpenCube n 3) :
    δ * inner ℝ (frechetGradient u x1 - frechetGradient u x0) v ≤
      ((A + η) / 2) * ‖x1 + δ • v - x0‖ ^ 2 := by
  have hx1Interior : x1 ∈ interior (sourceOpenCube n 3) :=
    sourceOpenCube_one_subset_interior_three hx1Q
  have hx1Q3 : x1 ∈ sourceOpenCube n 3 :=
    sourceOpenCube_one_subset_three hx1Q
  have hp1 :
      SubgradientOn (sourceOpenCube n 3) u x1 (frechetGradient u x1) :=
    AleksandrovDifferentiability.ConvexOn.sourceCube_subgradientOn_frechetGradient
      hu hx1Interior hd1
  have h0 :
      0 ≤ affineRemainder u x0 (frechetGradient u x0) x1 :=
    (cubeGoodSet_affineRemainder_trap_frechetGradient hu hx0good hη hx1Q3).1
  have hcompare :=
    hp1.inner_sub_le_affineRemainder_of_nonneg
      (x0 := x0) (p0 := frechetGradient u x0)
      (y := x1 + δ • v) hy h0
  have htrap :
      affineRemainder u x0 (frechetGradient u x0) (x1 + δ • v) ≤
        ((A + η) / 2) * ‖x1 + δ • v - x0‖ ^ 2 :=
    (cubeGoodSet_affineRemainder_trap_frechetGradient hu hx0good hη hy).2
  calc
    δ * inner ℝ (frechetGradient u x1 - frechetGradient u x0) v
        = inner ℝ (frechetGradient u x1 - frechetGradient u x0)
            ((x1 + δ • v) - x1) := by
          rw [show (x1 + δ • v) - x1 = δ • v by abel]
          rw [inner_smul_right]
    _ ≤ affineRemainder u x0 (frechetGradient u x0) (x1 + δ • v) := hcompare
    _ ≤ ((A + η) / 2) * ‖x1 + δ • v - x0‖ ^ 2 := htrap

/-- Directional comparison for gradients when the second point is any interior point of `Q_3`.

This is the domain-flexible form needed for the source proof's later use of differentiability
points in `Q_{3/2}` rather than only in `Q_1`. -/
theorem cubeGoodSet_smul_inner_gradient_sub_le_of_mem_interior
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {A η δ : ℝ}
    {x0 x1 v : SourceCubeSpace n}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u) (hx0good : x0 ∈ cubeGoodSet n u A)
    (hx1Interior : x1 ∈ interior (sourceOpenCube n 3)) (hx1Q3 : x1 ∈ sourceOpenCube n 3)
    (hd1 : DifferentiableAt ℝ u x1) (hη : 0 < η)
    (hy : x1 + δ • v ∈ sourceOpenCube n 3) :
    δ * inner ℝ (frechetGradient u x1 - frechetGradient u x0) v ≤
      ((A + η) / 2) * ‖x1 + δ • v - x0‖ ^ 2 := by
  have hp1 :
      SubgradientOn (sourceOpenCube n 3) u x1 (frechetGradient u x1) :=
    AleksandrovDifferentiability.ConvexOn.sourceCube_subgradientOn_frechetGradient
      hu hx1Interior hd1
  have h0 :
      0 ≤ affineRemainder u x0 (frechetGradient u x0) x1 :=
    (cubeGoodSet_affineRemainder_trap_frechetGradient hu hx0good hη hx1Q3).1
  have hcompare :=
    hp1.inner_sub_le_affineRemainder_of_nonneg
      (x0 := x0) (p0 := frechetGradient u x0)
      (y := x1 + δ • v) hy h0
  have htrap :
      affineRemainder u x0 (frechetGradient u x0) (x1 + δ • v) ≤
        ((A + η) / 2) * ‖x1 + δ • v - x0‖ ^ 2 :=
    (cubeGoodSet_affineRemainder_trap_frechetGradient hu hx0good hη hy).2
  calc
    δ * inner ℝ (frechetGradient u x1 - frechetGradient u x0) v
        = inner ℝ (frechetGradient u x1 - frechetGradient u x0)
            ((x1 + δ • v) - x1) := by
          rw [show (x1 + δ • v) - x1 = δ • v by abel]
          rw [inner_smul_right]
    _ ≤ affineRemainder u x0 (frechetGradient u x0) (x1 + δ • v) := hcompare
    _ ≤ ((A + η) / 2) * ‖x1 + δ • v - x0‖ ^ 2 := htrap

/-- Directional gradient control near a source good point, before optimizing over directions.

The small-distance hypothesis keeps the tested point `x1 + ‖x1 - x0‖ • v` inside `Q_3`, using
`x0 ∈ Q_1`. -/
theorem cubeGoodSet_inner_gradient_sub_le
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {A η : ℝ}
    {x0 x1 v : SourceCubeSpace n}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u) (hx0good : x0 ∈ cubeGoodSet n u A)
    (hx1Q : x1 ∈ sourceOpenCube n 1) (hd1 : DifferentiableAt ℝ u x1)
    (hη : 0 < η) (hAη : 0 ≤ A + η) (hv : ‖v‖ ≤ 1)
    (hsmall : 2 * ‖x1 - x0‖ ≤ 1) :
    inner ℝ (frechetGradient u x1 - frechetGradient u x0) v ≤
      2 * (A + η) * ‖x1 - x0‖ := by
  let δ : ℝ := ‖x1 - x0‖
  have hδ_nonneg : 0 ≤ δ := norm_nonneg _
  by_cases hδ_zero : δ = 0
  · have hx_eq : x1 = x0 := by
      have hsub : x1 - x0 = 0 := norm_eq_zero.mp hδ_zero
      exact sub_eq_zero.mp hsub
    subst x1
    simp
  have hδ_pos : 0 < δ := lt_of_le_of_ne hδ_nonneg (Ne.symm hδ_zero)
  have hx0Q : x0 ∈ sourceOpenCube n 1 := (mem_cubeGoodSet.mp hx0good).1
  have hdisp_norm : ‖(x1 - x0) + δ • v‖ ≤ 1 := by
    have htri : ‖(x1 - x0) + δ • v‖ ≤ ‖x1 - x0‖ + ‖δ • v‖ := norm_add_le _ _
    have hsmul : ‖δ • v‖ ≤ δ := by
      calc
        ‖δ • v‖ = |δ| * ‖v‖ := norm_smul δ v
        _ = δ * ‖v‖ := by rw [abs_of_nonneg hδ_nonneg]
        _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hv hδ_nonneg
        _ = δ := by ring
    have htwo : ‖x1 - x0‖ + ‖δ • v‖ ≤ 2 * δ := by
      dsimp [δ]
      linarith
    exact htri.trans (htwo.trans hsmall)
  have hy : x1 + δ • v ∈ sourceOpenCube n 3 := by
    have hy' :
        x0 + ((x1 - x0) + δ • v) ∈ sourceOpenCube n 3 :=
      sourceOpenCube_one_add_norm_le_one_mem_three hx0Q hdisp_norm
    convert hy' using 1
    abel
  have hmain :
      δ * inner ℝ (frechetGradient u x1 - frechetGradient u x0) v ≤
        ((A + η) / 2) * ‖x1 + δ • v - x0‖ ^ 2 :=
    cubeGoodSet_smul_inner_gradient_sub_le
      hu hx0good hx1Q hd1 hη hy
  have hnorm_endpoint : ‖x1 + δ • v - x0‖ ≤ 2 * δ := by
    have hrewrite : x1 + δ • v - x0 = (x1 - x0) + δ • v := by
      abel
    rw [hrewrite]
    have htri : ‖(x1 - x0) + δ • v‖ ≤ ‖x1 - x0‖ + ‖δ • v‖ := norm_add_le _ _
    have hsmul : ‖δ • v‖ ≤ δ := by
      calc
        ‖δ • v‖ = |δ| * ‖v‖ := norm_smul δ v
        _ = δ * ‖v‖ := by rw [abs_of_nonneg hδ_nonneg]
        _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hv hδ_nonneg
        _ = δ := by ring
    have htwo : ‖x1 - x0‖ + ‖δ • v‖ ≤ 2 * δ := by
      dsimp [δ]
      linarith
    exact htri.trans htwo
  have hquad :
      ((A + η) / 2) * ‖x1 + δ • v - x0‖ ^ 2 ≤
        2 * (A + η) * δ ^ 2 := by
    have hcoeff : 0 ≤ (A + η) / 2 := by linarith
    have hsq :
        ‖x1 + δ • v - x0‖ ^ 2 ≤ (2 * δ) ^ 2 :=
      sq_le_sq.mpr (by
        have htwo_nonneg : 0 ≤ 2 * δ :=
          mul_nonneg (by norm_num) hδ_nonneg
        simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg htwo_nonneg]
          using hnorm_endpoint)
    calc
      ((A + η) / 2) * ‖x1 + δ • v - x0‖ ^ 2
          ≤ ((A + η) / 2) * (2 * δ) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq hcoeff
      _ = 2 * (A + η) * δ ^ 2 := by ring
  have hmul :
      δ * inner ℝ (frechetGradient u x1 - frechetGradient u x0) v ≤
        δ * (2 * (A + η) * δ) := by
    have hbound := hmain.trans hquad
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hbound
  nlinarith

/-- Norm form of the local gradient control near a source good point. -/
theorem cubeGoodSet_norm_gradient_sub_le
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {A η : ℝ}
    {x0 x1 : SourceCubeSpace n}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u) (hx0good : x0 ∈ cubeGoodSet n u A)
    (hx1Q : x1 ∈ sourceOpenCube n 1) (hd1 : DifferentiableAt ℝ u x1)
    (hη : 0 < η) (hAη : 0 ≤ A + η) (hsmall : 2 * ‖x1 - x0‖ ≤ 1) :
    ‖frechetGradient u x1 - frechetGradient u x0‖ ≤
      2 * (A + η) * ‖x1 - x0‖ := by
  let q : SourceCubeSpace n := frechetGradient u x1 - frechetGradient u x0
  by_cases hq : q = 0
  · have hright : 0 ≤ 2 * (A + η) * ‖x1 - x0‖ :=
      mul_nonneg (mul_nonneg (by norm_num) hAη) (norm_nonneg _)
    change ‖q‖ ≤ 2 * (A + η) * ‖x1 - x0‖
    simpa [hq] using hright
  let v : SourceCubeSpace n := (‖q‖)⁻¹ • q
  have hq_norm_ne : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hv_norm : ‖v‖ ≤ 1 := by
    have hv_eq : ‖v‖ = 1 := by
      dsimp [v]
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hq_norm_ne]
    exact hv_eq.le
  have hdir :
      inner ℝ (frechetGradient u x1 - frechetGradient u x0) v ≤
        2 * (A + η) * ‖x1 - x0‖ :=
    cubeGoodSet_inner_gradient_sub_le
      hu hx0good hx1Q hd1 hη hAη hv_norm hsmall
  have hinner_eq :
      inner ℝ (frechetGradient u x1 - frechetGradient u x0) v =
        ‖frechetGradient u x1 - frechetGradient u x0‖ := by
    dsimp [v, q]
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [hq_norm_ne]
  simpa [hinner_eq] using hdir

/-- Directional gradient control near a source good point for differentiability points in
`Q_{3/2}`.

This is the source-local version used before the Lipschitz-envelope argument: the second point is
allowed to lie in `Q_{3/2}`, and the small-distance hypothesis keeps the tested endpoint in
`Q_3`. -/
theorem cubeGoodSet_inner_gradient_sub_le_three_halves
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {A η : ℝ}
    {x0 x1 v : SourceCubeSpace n}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u) (hx0good : x0 ∈ cubeGoodSet n u A)
    (hx1Q : x1 ∈ sourceOpenCube n (3 / 2 : ℝ)) (hd1 : DifferentiableAt ℝ u x1)
    (hη : 0 < η) (hAη : 0 ≤ A + η) (hv : ‖v‖ ≤ 1)
    (hsmall : ‖x1 - x0‖ ≤ 1) :
    inner ℝ (frechetGradient u x1 - frechetGradient u x0) v ≤
      2 * (A + η) * ‖x1 - x0‖ := by
  let δ : ℝ := ‖x1 - x0‖
  have hδ_nonneg : 0 ≤ δ := norm_nonneg _
  by_cases hδ_zero : δ = 0
  · have hx_eq : x1 = x0 := by
      have hsub : x1 - x0 = 0 := norm_eq_zero.mp hδ_zero
      exact sub_eq_zero.mp hsub
    subst x1
    simp
  have hδ_pos : 0 < δ := lt_of_le_of_ne hδ_nonneg (Ne.symm hδ_zero)
  have hx0Q : x0 ∈ sourceOpenCube n 1 := (mem_cubeGoodSet.mp hx0good).1
  have hdisp_norm : ‖(x1 - x0) + δ • v‖ ≤ 2 := by
    have htri : ‖(x1 - x0) + δ • v‖ ≤ ‖x1 - x0‖ + ‖δ • v‖ := norm_add_le _ _
    have hsmul : ‖δ • v‖ ≤ δ := by
      calc
        ‖δ • v‖ = |δ| * ‖v‖ := norm_smul δ v
        _ = δ * ‖v‖ := by rw [abs_of_nonneg hδ_nonneg]
        _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hv hδ_nonneg
        _ = δ := by ring
    have htwo : ‖x1 - x0‖ + ‖δ • v‖ ≤ 2 * δ := by
      dsimp [δ]
      linarith
    have hδ_le : δ ≤ 1 := by simpa [δ] using hsmall
    exact htri.trans (htwo.trans (by linarith))
  have hy : x1 + δ • v ∈ sourceOpenCube n 3 := by
    have hy' :
        x0 + ((x1 - x0) + δ • v) ∈ sourceOpenCube n 3 :=
      sourceOpenCube_one_add_norm_le_two_mem_three hx0Q hdisp_norm
    convert hy' using 1
    abel
  have hx1Interior : x1 ∈ interior (sourceOpenCube n 3) :=
    sourceOpenCube_subset_interior_of_le (n := n) (r := (3 / 2 : ℝ)) (R := 3)
      (by norm_num) hx1Q
  have hx1Q3 : x1 ∈ sourceOpenCube n 3 :=
    sourceOpenCube_subset_of_le (n := n) (r := (3 / 2 : ℝ)) (R := 3) (by norm_num) hx1Q
  have hmain :
      δ * inner ℝ (frechetGradient u x1 - frechetGradient u x0) v ≤
        ((A + η) / 2) * ‖x1 + δ • v - x0‖ ^ 2 :=
    cubeGoodSet_smul_inner_gradient_sub_le_of_mem_interior
      hu hx0good hx1Interior hx1Q3 hd1 hη hy
  have hnorm_endpoint : ‖x1 + δ • v - x0‖ ≤ 2 * δ := by
    have hrewrite : x1 + δ • v - x0 = (x1 - x0) + δ • v := by
      abel
    rw [hrewrite]
    have htri : ‖(x1 - x0) + δ • v‖ ≤ ‖x1 - x0‖ + ‖δ • v‖ := norm_add_le _ _
    have hsmul : ‖δ • v‖ ≤ δ := by
      calc
        ‖δ • v‖ = |δ| * ‖v‖ := norm_smul δ v
        _ = δ * ‖v‖ := by rw [abs_of_nonneg hδ_nonneg]
        _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hv hδ_nonneg
        _ = δ := by ring
    have htwo : ‖x1 - x0‖ + ‖δ • v‖ ≤ 2 * δ := by
      dsimp [δ]
      linarith
    exact htri.trans htwo
  have hquad :
      ((A + η) / 2) * ‖x1 + δ • v - x0‖ ^ 2 ≤
        2 * (A + η) * δ ^ 2 := by
    have hcoeff : 0 ≤ (A + η) / 2 := by linarith
    have hsq :
        ‖x1 + δ • v - x0‖ ^ 2 ≤ (2 * δ) ^ 2 :=
      sq_le_sq.mpr (by
        have htwo_nonneg : 0 ≤ 2 * δ :=
          mul_nonneg (by norm_num) hδ_nonneg
        simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg htwo_nonneg]
          using hnorm_endpoint)
    calc
      ((A + η) / 2) * ‖x1 + δ • v - x0‖ ^ 2
          ≤ ((A + η) / 2) * (2 * δ) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq hcoeff
      _ = 2 * (A + η) * δ ^ 2 := by ring
  have hmul :
      δ * inner ℝ (frechetGradient u x1 - frechetGradient u x0) v ≤
        δ * (2 * (A + η) * δ) := by
    have hbound := hmain.trans hquad
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hbound
  nlinarith

/-- Norm form of the local gradient control for differentiability points in `Q_{3/2}`. -/
theorem cubeGoodSet_norm_gradient_sub_le_three_halves
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {A η : ℝ}
    {x0 x1 : SourceCubeSpace n}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u) (hx0good : x0 ∈ cubeGoodSet n u A)
    (hx1Q : x1 ∈ sourceOpenCube n (3 / 2 : ℝ)) (hd1 : DifferentiableAt ℝ u x1)
    (hη : 0 < η) (hAη : 0 ≤ A + η) (hsmall : ‖x1 - x0‖ ≤ 1) :
    ‖frechetGradient u x1 - frechetGradient u x0‖ ≤
      2 * (A + η) * ‖x1 - x0‖ := by
  let q : SourceCubeSpace n := frechetGradient u x1 - frechetGradient u x0
  by_cases hq : q = 0
  · have hright : 0 ≤ 2 * (A + η) * ‖x1 - x0‖ :=
      mul_nonneg (mul_nonneg (by norm_num) hAη) (norm_nonneg _)
    change ‖q‖ ≤ 2 * (A + η) * ‖x1 - x0‖
    simpa [hq] using hright
  let v : SourceCubeSpace n := (‖q‖)⁻¹ • q
  have hq_norm_ne : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hv_norm : ‖v‖ ≤ 1 := by
    have hv_eq : ‖v‖ = 1 := by
      dsimp [v]
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hq_norm_ne]
    exact hv_eq.le
  have hdir :
      inner ℝ (frechetGradient u x1 - frechetGradient u x0) v ≤
        2 * (A + η) * ‖x1 - x0‖ :=
    cubeGoodSet_inner_gradient_sub_le_three_halves
      hu hx0good hx1Q hd1 hη hAη hv_norm hsmall
  have hinner_eq :
      inner ℝ (frechetGradient u x1 - frechetGradient u x0) v =
        ‖frechetGradient u x1 - frechetGradient u x0‖ := by
    dsimp [v, q]
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [hq_norm_ne]
  simpa [hinner_eq] using hdir

/-- Full source-local gradient control for differentiability points in `Q_{3/2}`, including the
coarse-distance case. This is the cross-set estimate used before the Lipschitz-envelope
argument, with `A = m` and the oscillation term included for the large-distance case. -/
theorem cubeGoodSet_nat_norm_gradient_sub_le_three_halves_global
    {n m : ℕ} {u : SourceCubeSpace n → ℝ} {x0 x1 : SourceCubeSpace n}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hx0good : x0 ∈ cubeGoodSet n u (m : ℝ))
    (hx1Q : x1 ∈ sourceOpenCube n (3 / 2 : ℝ)) (hd1 : DifferentiableAt ℝ u x1) :
    ‖frechetGradient u x1 - frechetGradient u x0‖ ≤
      2 * (((m : ℝ) + 1) + sourceCubeOscillation n u) * ‖x1 - x0‖ := by
  have hm_nonneg : 0 ≤ (m : ℝ) + 1 :=
    add_nonneg (Nat.cast_nonneg m) zero_le_one
  have hosc_nonneg : 0 ≤ sourceCubeOscillation n u :=
    sourceCubeOscillation_nonneg_of_boundedOn hbounded
  by_cases hsmall : ‖x1 - x0‖ ≤ 1
  · have hsmall_bound :
        ‖frechetGradient u x1 - frechetGradient u x0‖ ≤
          2 * ((m : ℝ) + 1) * ‖x1 - x0‖ :=
      cubeGoodSet_norm_gradient_sub_le_three_halves
        (A := (m : ℝ)) (η := 1) hu hx0good hx1Q hd1
        (by norm_num) hm_nonneg hsmall
    have hmono :
        2 * ((m : ℝ) + 1) * ‖x1 - x0‖ ≤
          2 * (((m : ℝ) + 1) + sourceCubeOscillation n u) * ‖x1 - x0‖ := by
      nlinarith [hm_nonneg, hosc_nonneg, norm_nonneg (x1 - x0)]
    exact hsmall_bound.trans hmono
  · have hlarge : 1 < ‖x1 - x0‖ := lt_of_not_ge hsmall
    rcases (mem_cubeGoodSet.mp hx0good) with ⟨hx0Q, hd0, _hopening⟩
    have hgrad1 :
        ‖frechetGradient u x1‖ ≤ sourceCubeOscillation n u :=
      ConvexOn.norm_frechetGradient_le_sourceCubeOscillation_of_boundedOn_three_halves
        hu hbounded hx1Q hd1
    have hgrad0 :
        ‖frechetGradient u x0‖ ≤ sourceCubeOscillation n u :=
      ConvexOn.norm_frechetGradient_le_sourceCubeOscillation_of_boundedOn
        hu hbounded hx0Q hd0
    have hdiff_le :
        ‖frechetGradient u x1 - frechetGradient u x0‖ ≤
          2 * sourceCubeOscillation n u := by
      calc
        ‖frechetGradient u x1 - frechetGradient u x0‖
            ≤ ‖frechetGradient u x1‖ + ‖frechetGradient u x0‖ := norm_sub_le _ _
        _ ≤ sourceCubeOscillation n u + sourceCubeOscillation n u := by
          exact add_le_add hgrad1 hgrad0
        _ = 2 * sourceCubeOscillation n u := by ring
    have htarget :
        2 * sourceCubeOscillation n u ≤
          2 * (((m : ℝ) + 1) + sourceCubeOscillation n u) * ‖x1 - x0‖ := by
      have hcoeff_nonneg : 0 ≤ 2 * (((m : ℝ) + 1) + sourceCubeOscillation n u) := by
        nlinarith
      have hone_le : (1 : ℝ) ≤ ‖x1 - x0‖ := hlarge.le
      have hmul :
          2 * (((m : ℝ) + 1) + sourceCubeOscillation n u) * 1 ≤
            2 * (((m : ℝ) + 1) + sourceCubeOscillation n u) * ‖x1 - x0‖ :=
        mul_le_mul_of_nonneg_left hone_le hcoeff_nonneg
      nlinarith [hmul, hm_nonneg, hosc_nonneg]
    exact hdiff_le.trans htarget

/-- Coordinate form of the global `Q_{3/2}` gradient-control estimate. This is the exact
cross-set Lipschitz hypothesis used for the source proof's envelope functions
`g_i = partial_i u` on `D_{3/2}`. -/
theorem cubeGoodSet_nat_abs_gradient_coord_sub_le_three_halves_global
    {n m : ℕ} {u : SourceCubeSpace n → ℝ} {x0 x1 : SourceCubeSpace n} (i : Fin n)
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hx0good : x0 ∈ cubeGoodSet n u (m : ℝ))
    (hx1Q : x1 ∈ sourceOpenCube n (3 / 2 : ℝ)) (hd1 : DifferentiableAt ℝ u x1) :
    |frechetGradient u x1 i - frechetGradient u x0 i| ≤
      2 * (((m : ℝ) + 1) + sourceCubeOscillation n u) * ‖x1 - x0‖ := by
  have hcoord :
      |frechetGradient u x1 i - frechetGradient u x0 i| ≤
        ‖frechetGradient u x1 - frechetGradient u x0‖ := by
    simpa using abs_sourceCoordinate_le_norm (frechetGradient u x1 - frechetGradient u x0) i
  exact hcoord.trans
    (cubeGoodSet_nat_norm_gradient_sub_le_three_halves_global
      hu hbounded hx0good hx1Q hd1)

/-- Integer-indexed good-set version of the local gradient control.

This is the form used for the countable good-set cover: choose `A = m` and absorb the
arbitrary `η > 0` by taking `η = 1`. -/
theorem cubeGoodSet_nat_norm_gradient_sub_le
    {n m : ℕ} {u : SourceCubeSpace n → ℝ} {x0 x1 : SourceCubeSpace n}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hx0good : x0 ∈ cubeGoodSet n u (m : ℝ))
    (hx1good : x1 ∈ cubeGoodSet n u (m : ℝ))
    (hsmall : 2 * ‖x1 - x0‖ ≤ 1) :
    ‖frechetGradient u x1 - frechetGradient u x0‖ ≤
      2 * ((m : ℝ) + 1) * ‖x1 - x0‖ := by
  rcases (mem_cubeGoodSet.mp hx1good) with ⟨hx1Q, hd1, _hopening⟩
  have hm_nonneg : 0 ≤ (m : ℝ) + 1 :=
    add_nonneg (Nat.cast_nonneg m) zero_le_one
  simpa using
    cubeGoodSet_norm_gradient_sub_le
      (A := (m : ℝ)) (η := 1) hu hx0good hx1Q hd1 (by norm_num) hm_nonneg hsmall

/-- Pairwise gradient control on an integer good set, localized to a small closed ball.

The radius `1 / 4` ensures any two localized points are within distance `1 / 2`, exactly the
small-distance hypothesis needed by `cubeGoodSet_nat_norm_gradient_sub_le`. -/
theorem cubeGoodSet_nat_norm_gradient_sub_le_of_mem_closedBall
    {n m : ℕ} {u : SourceCubeSpace n → ℝ} {c x0 x1 : SourceCubeSpace n}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hx0 :
      x0 ∈ cubeGoodSet n u (m : ℝ) ∩ Metric.closedBall c (1 / 4 : ℝ))
    (hx1 :
      x1 ∈ cubeGoodSet n u (m : ℝ) ∩ Metric.closedBall c (1 / 4 : ℝ)) :
    ‖frechetGradient u x1 - frechetGradient u x0‖ ≤
      2 * ((m : ℝ) + 1) * ‖x1 - x0‖ := by
  have hdist_x1 : dist x1 c ≤ (1 / 4 : ℝ) := hx1.2
  have hdist_x0 : dist c x0 ≤ (1 / 4 : ℝ) := by
    simpa [dist_comm] using hx0.2
  have hdist : dist x1 x0 ≤ (1 / 2 : ℝ) := by
    have htri : dist x1 x0 ≤ dist x1 c + dist c x0 :=
      dist_triangle x1 c x0
    linarith
  have hnorm : ‖x1 - x0‖ ≤ (1 / 2 : ℝ) := by
    simpa [dist_eq_norm] using hdist
  have hsmall : 2 * ‖x1 - x0‖ ≤ 1 := by
    linarith
  exact cubeGoodSet_nat_norm_gradient_sub_le hu hx0.1 hx1.1 hsmall

/-- The Fréchet-gradient map is Lipschitz on each localized integer good set.

This is the Rademacher-ready packaging of the source proof's good-set gradient estimate. -/
theorem cubeGoodSet_nat_lipschitzOnWith_frechetGradient_inter_closedBall
    {n m : ℕ} {u : SourceCubeSpace n → ℝ} (c : SourceCubeSpace n)
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u) :
    LipschitzOnWith (Real.toNNReal (2 * ((m : ℝ) + 1))) (fun x => frechetGradient u x)
      (cubeGoodSet n u (m : ℝ) ∩ Metric.closedBall c (1 / 4 : ℝ)) := by
  refine LipschitzOnWith.of_dist_le' ?_
  intro x hx y hy
  have hnorm :
      ‖frechetGradient u x - frechetGradient u y‖ ≤
        2 * ((m : ℝ) + 1) * ‖x - y‖ :=
    cubeGoodSet_nat_norm_gradient_sub_le_of_mem_closedBall (c := c) hu hy hx
  simpa [dist_eq_norm] using hnorm

/-- Rademacher bridge for the localized integer good set.

This form avoids a measurability side condition on `cubeGoodSet`: for almost every ambient point,
membership in the localized good set implies differentiability of the gradient within that set. -/
theorem cubeGoodSet_nat_ae_differentiableWithinAt_frechetGradient_inter_closedBall_of_mem
    {n m : ℕ} {u : SourceCubeSpace n → ℝ} (c : SourceCubeSpace n)
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u) :
    ∀ᵐ x ∂(volume : Measure (SourceCubeSpace n)),
      x ∈ cubeGoodSet n u (m : ℝ) ∩ Metric.closedBall c (1 / 4 : ℝ) →
        DifferentiableWithinAt ℝ (fun x => frechetGradient u x)
          (cubeGoodSet n u (m : ℝ) ∩ Metric.closedBall c (1 / 4 : ℝ)) x := by
  have hlip :=
    cubeGoodSet_nat_lipschitzOnWith_frechetGradient_inter_closedBall (m := m) c hu
  exact hlip.ae_differentiableWithinAt_of_mem

/-- Restricted-measure Rademacher bridge for a localized integer good set, assuming the localized
set has already been made measurable.

This is the exact form needed for the final a.e. assembly once measurability/countable
localization of the good sets has been supplied. -/
theorem cubeGoodSet_nat_ae_differentiableWithinAt_frechetGradient_inter_closedBall
    {n m : ℕ} {u : SourceCubeSpace n → ℝ} (c : SourceCubeSpace n)
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hs :
      MeasurableSet
        (cubeGoodSet n u (m : ℝ) ∩ Metric.closedBall c (1 / 4 : ℝ))) :
    ∀ᵐ x ∂(volume.restrict
        (cubeGoodSet n u (m : ℝ) ∩ Metric.closedBall c (1 / 4 : ℝ))),
      DifferentiableWithinAt ℝ (fun x => frechetGradient u x)
        (cubeGoodSet n u (m : ℝ) ∩ Metric.closedBall c (1 / 4 : ℝ)) x := by
  have hlip :=
    cubeGoodSet_nat_lipschitzOnWith_frechetGradient_inter_closedBall (m := m) c hu
  exact hlip.ae_differentiableWithinAt hs

/-- On each integer good set, the Fréchet-gradient map is locally Lipschitz.

This is the intrinsic local form of the source proof's gradient-control lemma on `Omega_m`. -/
theorem cubeGoodSet_nat_locallyLipschitzOn_frechetGradient
    {n m : ℕ} {u : SourceCubeSpace n → ℝ}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u) :
    LocallyLipschitzOn (cubeGoodSet n u (m : ℝ)) (fun x => frechetGradient u x) := by
  intro x _hx
  refine
    ⟨Real.toNNReal (2 * ((m : ℝ) + 1)),
      cubeGoodSet n u (m : ℝ) ∩ Metric.closedBall x (1 / 4 : ℝ), ?_, ?_⟩
  · exact inter_mem_nhdsWithin _ (Metric.closedBall_mem_nhds x (by norm_num))
  · exact cubeGoodSet_nat_lipschitzOnWith_frechetGradient_inter_closedBall (m := m) x hu

/-- A differentiability-within statement on a localized closed ball transfers back to the whole
integer good set when the base point lies in the corresponding open ball. -/
theorem cubeGoodSet_nat_differentiableWithinAt_frechetGradient_of_inter_closedBall
    {n m : ℕ} {u : SourceCubeSpace n → ℝ} {c x : SourceCubeSpace n}
    (hxball : x ∈ Metric.ball c (1 / 4 : ℝ))
    (hd :
      DifferentiableWithinAt ℝ (fun x => frechetGradient u x)
        (cubeGoodSet n u (m : ℝ) ∩ Metric.closedBall c (1 / 4 : ℝ)) x) :
    DifferentiableWithinAt ℝ (fun x => frechetGradient u x) (cubeGoodSet n u (m : ℝ)) x := by
  refine hd.mono_of_mem_nhdsWithin ?_
  exact inter_mem_nhdsWithin _ (Metric.closedBall_mem_nhds_of_mem hxball)

/-- Countable localized Rademacher bridge over the integer good sets.

If a countable family of radius-`1 / 4` closed balls covers `Q_1`, then for almost every ambient
point, membership in the countable good-set union gives a localized good set on which
`frechetGradient u` is differentiable within that localized set. -/
theorem ae_exists_cubeGoodSet_nat_local_differentiableWithinAt_frechetGradient
    {n : ℕ} {u : SourceCubeSpace n → ℝ} (centers : ℕ → SourceCubeSpace n)
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hcover :
      sourceOpenCube n 1 ⊆
        ⋃ k : ℕ, Metric.closedBall (centers k) (1 / 4 : ℝ)) :
    ∀ᵐ x ∂(volume : Measure (SourceCubeSpace n)),
      x ∈ sourceOpenCube n 1 →
        x ∈ (⋃ m : ℕ, cubeGoodSet n u (m : ℝ)) →
          ∃ m k : ℕ,
            x ∈ cubeGoodSet n u (m : ℝ) ∩
              Metric.closedBall (centers k) (1 / 4 : ℝ) ∧
              DifferentiableWithinAt ℝ (fun x => frechetGradient u x)
                (cubeGoodSet n u (m : ℝ) ∩
                  Metric.closedBall (centers k) (1 / 4 : ℝ)) x := by
  have hAE :
      ∀ᵐ x ∂(volume : Measure (SourceCubeSpace n)), ∀ m k : ℕ,
        x ∈ cubeGoodSet n u (m : ℝ) ∩
            Metric.closedBall (centers k) (1 / 4 : ℝ) →
          DifferentiableWithinAt ℝ (fun x => frechetGradient u x)
            (cubeGoodSet n u (m : ℝ) ∩
              Metric.closedBall (centers k) (1 / 4 : ℝ)) x := by
    rw [ae_all_iff]
    intro m
    rw [ae_all_iff]
    intro k
    exact
      cubeGoodSet_nat_ae_differentiableWithinAt_frechetGradient_inter_closedBall_of_mem
        (m := m) (centers k) hu
  filter_upwards [hAE] with x hx hxQ hxgoodUnion
  rcases Set.mem_iUnion.mp hxgoodUnion with ⟨m, hxgood⟩
  rcases Set.mem_iUnion.mp (hcover hxQ) with ⟨k, hxball⟩
  exact ⟨m, k, ⟨hxgood, hxball⟩, hx m k ⟨hxgood, hxball⟩⟩

/-- Countable open-ball version of the localized Rademacher bridge.

An open radius-`1 / 4` ball cover of `Q_1` gives, for almost every point in the countable good-set
union, differentiability of `frechetGradient u` within the corresponding integer good set itself. -/
theorem ae_exists_cubeGoodSet_nat_differentiableWithinAt_frechetGradient
    {n : ℕ} {u : SourceCubeSpace n → ℝ} (centers : ℕ → SourceCubeSpace n)
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hcover :
      sourceOpenCube n 1 ⊆ ⋃ k : ℕ, Metric.ball (centers k) (1 / 4 : ℝ)) :
    ∀ᵐ x ∂(volume : Measure (SourceCubeSpace n)),
      x ∈ sourceOpenCube n 1 →
        x ∈ (⋃ m : ℕ, cubeGoodSet n u (m : ℝ)) →
          ∃ m : ℕ,
            x ∈ cubeGoodSet n u (m : ℝ) ∧
              DifferentiableWithinAt ℝ (fun x => frechetGradient u x)
                (cubeGoodSet n u (m : ℝ)) x := by
  have hAE :
      ∀ᵐ x ∂(volume : Measure (SourceCubeSpace n)), ∀ m k : ℕ,
        x ∈ cubeGoodSet n u (m : ℝ) ∩
            Metric.closedBall (centers k) (1 / 4 : ℝ) →
          DifferentiableWithinAt ℝ (fun x => frechetGradient u x)
            (cubeGoodSet n u (m : ℝ) ∩
              Metric.closedBall (centers k) (1 / 4 : ℝ)) x := by
    rw [ae_all_iff]
    intro m
    rw [ae_all_iff]
    intro k
    exact
      cubeGoodSet_nat_ae_differentiableWithinAt_frechetGradient_inter_closedBall_of_mem
        (m := m) (centers k) hu
  filter_upwards [hAE] with x hx hxQ hxgoodUnion
  rcases Set.mem_iUnion.mp hxgoodUnion with ⟨m, hxgood⟩
  rcases Set.mem_iUnion.mp (hcover hxQ) with ⟨k, hxball⟩
  have hxclosed : x ∈ Metric.closedBall (centers k) (1 / 4 : ℝ) :=
    Metric.ball_subset_closedBall hxball
  have hlocal :
      DifferentiableWithinAt ℝ (fun x => frechetGradient u x)
        (cubeGoodSet n u (m : ℝ) ∩ Metric.closedBall (centers k) (1 / 4 : ℝ)) x :=
    hx m k ⟨hxgood, hxclosed⟩
  exact
    ⟨m, hxgood,
      cubeGoodSet_nat_differentiableWithinAt_frechetGradient_of_inter_closedBall hxball hlocal⟩

/-- If a point of `Q_1` is differentiable and has finite upper-contact opening, then it belongs
to one of the countably many source cube good sets `Omega_m`. -/
theorem sourceOpenCube_diff_iUnion_cubeGoodSet_subset_firstOrder_bad_union_finiteOpening_bad
    {n : ℕ} {u : SourceCubeSpace n → ℝ} :
    sourceOpenCube n 1 \ (⋃ m : ℕ, cubeGoodSet n u (m : ℝ)) ⊆
      (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) ∪
        (sourceOpenCube n 1 \ finiteUpperContactOpeningSet (sourceOpenCube n 3) u) := by
  intro x hx
  rcases hx with ⟨hxQ, hxnot⟩
  by_cases hd : DifferentiableAt ℝ u x
  · by_cases hf : x ∈ finiteUpperContactOpeningSet (sourceOpenCube n 3) u
    · rcases hf with ⟨A, hA⟩
      rcases exists_nat_ge A with ⟨m, hm⟩
      have hxgood : x ∈ cubeGoodSet n u (m : ℝ) :=
        ⟨hxQ, hd, hA.mono_bound hm⟩
      exact (hxnot (Set.mem_iUnion.mpr ⟨m, hxgood⟩)).elim
    · exact Or.inr ⟨hxQ, hf⟩
  · exact Or.inl ⟨hxQ, hd⟩

/-- First differentiability a.e. and finite upper-contact opening a.e. imply that the countable
union of source cube good sets covers `Q_1` up to a null set. -/
theorem volume_sourceOpenCube_diff_iUnion_cubeGoodSet_eq_zero
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    (hdiff : volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) = 0)
    (hfinite :
      volume
          (sourceOpenCube n 1 \
            finiteUpperContactOpeningSet (sourceOpenCube n 3) u) = 0) :
    volume (sourceOpenCube n 1 \ (⋃ m : ℕ, cubeGoodSet n u (m : ℝ))) = 0 :=
  measure_mono_null
    sourceOpenCube_diff_iUnion_cubeGoodSet_subset_firstOrder_bad_union_finiteOpening_bad
    (measure_union_null hdiff hfinite)

/-- Source-route good-set cover from convexity, first differentiability a.e., and the finite
upper-contact-opening theorem. -/
theorem volume_sourceOpenCube_diff_iUnion_cubeGoodSet_eq_zero_of_convex
    {n : ℕ} (hfiniteStatement : ConvexFiniteUpperContactOpeningAEOnCubeStatement n)
    (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u) :
    volume (sourceOpenCube n 1 \ (⋃ m : ℕ, cubeGoodSet n u (m : ℝ))) = 0 :=
  volume_sourceOpenCube_diff_iUnion_cubeGoodSet_eq_zero
    (ConvexOn.volume_sourceOpenCube_diff_firstOrderDifferentiabilitySet_eq_zero hconvex)
    (hfiniteStatement hn u hbounded hconvex)

/-- Source-route a.e. gradient differentiability on localized good sets.

This combines the null complement of the countable good-set union with the countable localized
Rademacher bridge. The remaining input is a countable radius-`1 / 4` closed-ball cover of `Q_1`,
which is a purely topological/separability fact. -/
theorem ae_restrict_sourceOpenCube_exists_local_goodSet_frechetGradient_diffWithin
    {n : ℕ} (hfiniteStatement : ConvexFiniteUpperContactOpeningAEOnCubeStatement n)
    (hn : 1 ≤ n) (centers : ℕ → SourceCubeSpace n)
    (hcover :
      sourceOpenCube n 1 ⊆
        ⋃ k : ℕ, Metric.closedBall (centers k) (1 / 4 : ℝ))
    {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      ∃ m k : ℕ,
        x ∈ cubeGoodSet n u (m : ℝ) ∩
          Metric.closedBall (centers k) (1 / 4 : ℝ) ∧
          DifferentiableWithinAt ℝ (fun x => frechetGradient u x)
            (cubeGoodSet n u (m : ℝ) ∩
              Metric.closedBall (centers k) (1 / 4 : ℝ)) x := by
  let G : Set (SourceCubeSpace n) := ⋃ m : ℕ, cubeGoodSet n u (m : ℝ)
  have hGnull :
      volume (sourceOpenCube n 1 \ G) = 0 := by
    simpa [G] using
      volume_sourceOpenCube_diff_iUnion_cubeGoodSet_eq_zero_of_convex
        hfiniteStatement hn hbounded hconvex
  have hGae : ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)), x ∈ G := by
    rw [ae_iff]
    rw [Measure.restrict_apply_eq_zero' (isOpen_sourceOpenCube (n := n) 1).measurableSet]
    have hset :
        {x : SourceCubeSpace n | ¬ x ∈ G} ∩ sourceOpenCube n 1 =
          sourceOpenCube n 1 \ G := by
      ext x
      simp [Set.sdiff_eq, and_comm]
    rwa [hset]
  have hlocal :=
    ae_exists_cubeGoodSet_nat_local_differentiableWithinAt_frechetGradient
      centers hconvex hcover
  have hlocalRestrict :
      ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
        x ∈ sourceOpenCube n 1 →
          x ∈ G →
            ∃ m k : ℕ,
              x ∈ cubeGoodSet n u (m : ℝ) ∩
                Metric.closedBall (centers k) (1 / 4 : ℝ) ∧
                DifferentiableWithinAt ℝ (fun x => frechetGradient u x)
                  (cubeGoodSet n u (m : ℝ) ∩
                    Metric.closedBall (centers k) (1 / 4 : ℝ)) x :=
    ae_restrict_of_ae hlocal
  filter_upwards
    [hGae, hlocalRestrict,
      ae_restrict_mem (μ := volume) (isOpen_sourceOpenCube (n := n) 1).measurableSet]
    with x hxG hxlocal hxQ
  exact hxlocal hxQ hxG

/-- Source-route a.e. differentiability of the gradient within an integer good set.

This is the open-ball-cover version of
`ae_restrict_sourceOpenCube_exists_local_goodSet_frechetGradient_diffWithin`: the open cover lets
the localized differentiability-within statement transfer from
`Omega_m ∩ closedBall c (1 / 4)` back to `Omega_m`. -/
theorem ae_restrict_sourceOpenCube_exists_goodSet_frechetGradient_diffWithin
    {n : ℕ} (hfiniteStatement : ConvexFiniteUpperContactOpeningAEOnCubeStatement n)
    (hn : 1 ≤ n) (centers : ℕ → SourceCubeSpace n)
    (hcover :
      sourceOpenCube n 1 ⊆ ⋃ k : ℕ, Metric.ball (centers k) (1 / 4 : ℝ))
    {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      ∃ m : ℕ,
        x ∈ cubeGoodSet n u (m : ℝ) ∧
          DifferentiableWithinAt ℝ (fun x => frechetGradient u x)
            (cubeGoodSet n u (m : ℝ)) x := by
  let G : Set (SourceCubeSpace n) := ⋃ m : ℕ, cubeGoodSet n u (m : ℝ)
  have hGnull :
      volume (sourceOpenCube n 1 \ G) = 0 := by
    simpa [G] using
      volume_sourceOpenCube_diff_iUnion_cubeGoodSet_eq_zero_of_convex
        hfiniteStatement hn hbounded hconvex
  have hGae : ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)), x ∈ G := by
    rw [ae_iff]
    rw [Measure.restrict_apply_eq_zero' (isOpen_sourceOpenCube (n := n) 1).measurableSet]
    have hset :
        {x : SourceCubeSpace n | ¬ x ∈ G} ∩ sourceOpenCube n 1 =
          sourceOpenCube n 1 \ G := by
      ext x
      simp [Set.sdiff_eq, and_comm]
    rwa [hset]
  have hlocal :=
    ae_exists_cubeGoodSet_nat_differentiableWithinAt_frechetGradient centers hconvex hcover
  have hlocalRestrict :
      ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
        x ∈ sourceOpenCube n 1 →
          x ∈ G →
            ∃ m : ℕ,
              x ∈ cubeGoodSet n u (m : ℝ) ∧
                DifferentiableWithinAt ℝ (fun x => frechetGradient u x)
                  (cubeGoodSet n u (m : ℝ)) x :=
    ae_restrict_of_ae hlocal
  filter_upwards
    [hGae, hlocalRestrict,
      ae_restrict_mem (μ := volume) (isOpen_sourceOpenCube (n := n) 1).measurableSet]
    with x hxG hxlocal hxQ
  exact hxlocal hxQ hxG

/-- The canonical dense sequence gives a countable open radius-`1 / 4` ball cover of `Q_1`. -/
theorem sourceOpenCube_subset_iUnion_denseSeq_ball_quarter {n : ℕ} :
    sourceOpenCube n 1 ⊆
      ⋃ k : ℕ, Metric.ball (TopologicalSpace.denseSeq (SourceCubeSpace n) k) (1 / 4 : ℝ) := by
  intro x _hx
  rcases (TopologicalSpace.denseRange_denseSeq (SourceCubeSpace n)).exists_dist_lt
      x (by norm_num : 0 < (1 / 4 : ℝ)) with ⟨k, hk⟩
  exact Set.mem_iUnion.mpr ⟨k, by simpa [Metric.mem_ball] using hk⟩

/-- Source-route a.e. differentiability of the gradient within an integer good set, with the
countable open-ball cover chosen from the canonical dense sequence. -/
theorem ae_restrict_sourceOpenCube_exists_goodSet_frechetGradient_diffWithin_of_convex
    {n : ℕ} (hfiniteStatement : ConvexFiniteUpperContactOpeningAEOnCubeStatement n)
    (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      ∃ m : ℕ,
        x ∈ cubeGoodSet n u (m : ℝ) ∧
          DifferentiableWithinAt ℝ (fun x => frechetGradient u x)
            (cubeGoodSet n u (m : ℝ)) x :=
  ae_restrict_sourceOpenCube_exists_goodSet_frechetGradient_diffWithin
    hfiniteStatement hn (TopologicalSpace.denseSeq (SourceCubeSpace n))
    sourceOpenCube_subset_iUnion_denseSeq_ball_quarter hbounded hconvex

/-- Differentiability of the Fréchet-gradient map within a good set gives the corresponding
little-o linearization along that good set. -/
theorem cubeGoodSet_hasFDerivWithinAt_frechetGradient_isLittleO
    {n m : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hB :
      HasFDerivWithinAt (fun y : SourceCubeSpace n => frechetGradient u y) B
        (cubeGoodSet n u (m : ℝ)) x) :
    (fun y : SourceCubeSpace n =>
        frechetGradient u y - frechetGradient u x - B (y - x))
      =o[𝓝[cubeGoodSet n u (m : ℝ)] x]
        (fun y : SourceCubeSpace n => y - x) := by
  simpa using hB.isLittleO

/-- Existential linearization form of differentiability of the Fréchet-gradient map within a
good set. This avoids committing later arguments to a particular representative such as
`fderivWithin` when the good set is not known to be a unique-differentiability set. -/
theorem cubeGoodSet_differentiableWithinAt_frechetGradient_exists_linearization
    {n m : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n}
    (hd :
      DifferentiableWithinAt ℝ (fun y : SourceCubeSpace n => frechetGradient u y)
        (cubeGoodSet n u (m : ℝ)) x) :
    ∃ B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n,
      (fun y : SourceCubeSpace n =>
          frechetGradient u y - frechetGradient u x - B (y - x))
        =o[𝓝[cubeGoodSet n u (m : ℝ)] x]
          (fun y : SourceCubeSpace n => y - x) := by
  rcases hd with ⟨B, hB⟩
  exact ⟨B, cubeGoodSet_hasFDerivWithinAt_frechetGradient_isLittleO hB⟩

/-- Construct the source-space linear map whose coordinate rows are the vectors `ell i`. -/
theorem exists_sourceLinearMap_rows_inner
    {n : ℕ} (ell : Fin n → SourceCubeSpace n) :
    ∃ B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n,
      ∀ z i, B z i = inner ℝ (ell i) z := by
  let e : SourceCubeSpace n ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  let Bpi : SourceCubeSpace n →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.pi fun i => innerSL ℝ (ell i)
  refine ⟨e.symm.toContinuousLinearMap.comp Bpi, ?_⟩
  intro z i
  simp [e, Bpi, innerSL_apply_apply]

/-- Assemble coordinate-wise first-order gradient expansions into a vector expansion.

This is the linear-algebra step in the source proof after the Lipschitz-envelope/Rademacher
argument: once each component of `frechetGradient u` has a first-order expansion with row vector
`ell i`, any continuous linear map `B` whose rows are those functionals gives the corresponding
vector-valued little-o expansion. -/
theorem frechetGradient_isLittleO_norm_of_coordinate_isLittleO
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n}
    {s : Set (SourceCubeSpace n)} {ell : Fin n → SourceCubeSpace n}
    {B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n}
    (hB : ∀ z i, B z i = inner ℝ (ell i) z)
    (hcoord : ∀ i : Fin n,
      (fun y : SourceCubeSpace n =>
        frechetGradient u y i - frechetGradient u x i - inner ℝ (ell i) (y - x))
        =o[𝓝[s] x] (fun y : SourceCubeSpace n => ‖y - x‖)) :
    (fun y : SourceCubeSpace n =>
        frechetGradient u y - frechetGradient u x - B (y - x))
      =o[𝓝[s] x] (fun y : SourceCubeSpace n => ‖y - x‖) := by
  let e : SourceCubeSpace n ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  have hpi :
      (fun y : SourceCubeSpace n =>
          e (frechetGradient u y - frechetGradient u x - B (y - x)))
        =o[𝓝[s] x] (fun y : SourceCubeSpace n => ‖y - x‖) := by
    rw [isLittleO_pi]
    intro i
    simpa [e, hB, inner_sub_right] using hcoord i
  exact
    (e.isBigO_comp_rev
        (fun y : SourceCubeSpace n =>
          frechetGradient u y - frechetGradient u x - B (y - x))
        (𝓝[s] x)).trans_isLittleO hpi

/-- Existential version of coordinate-to-vector gradient linearization.

The chosen linear map is the row map determined by the coordinate vectors `ell i`. -/
theorem exists_frechetGradient_isLittleO_norm_of_coordinate_isLittleO
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {x : SourceCubeSpace n}
    {s : Set (SourceCubeSpace n)} {ell : Fin n → SourceCubeSpace n}
    (hcoord : ∀ i : Fin n,
      (fun y : SourceCubeSpace n =>
        frechetGradient u y i - frechetGradient u x i - inner ℝ (ell i) (y - x))
        =o[𝓝[s] x] (fun y : SourceCubeSpace n => ‖y - x‖)) :
    ∃ B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n,
      (∀ z i, B z i = inner ℝ (ell i) z) ∧
        (fun y : SourceCubeSpace n =>
            frechetGradient u y - frechetGradient u x - B (y - x))
          =o[𝓝[s] x] (fun y : SourceCubeSpace n => ‖y - x‖) := by
  rcases exists_sourceLinearMap_rows_inner ell with ⟨B, hB⟩
  exact ⟨B, hB, frechetGradient_isLittleO_norm_of_coordinate_isLittleO hB hcoord⟩

/-- Source-route a.e. good-set gradient linearization, with the countable cover chosen from the
canonical dense sequence.

This is the Rademacher output in the form needed for the next Aleksandrov step: at almost every
point of `Q_1`, one can choose an integer good set and a linear map which gives the first-order
expansion of the gradient along that good set. -/
theorem ae_restrict_sourceOpenCube_exists_goodSet_frechetGradient_linearization_of_convex
    {n : ℕ} (hfiniteStatement : ConvexFiniteUpperContactOpeningAEOnCubeStatement n)
    (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      ∃ m : ℕ,
        x ∈ cubeGoodSet n u (m : ℝ) ∧
          ∃ B : SourceCubeSpace n →L[ℝ] SourceCubeSpace n,
            (fun y : SourceCubeSpace n =>
                frechetGradient u y - frechetGradient u x - B (y - x))
              =o[𝓝[cubeGoodSet n u (m : ℝ)] x]
                (fun y : SourceCubeSpace n => y - x) := by
  filter_upwards
    [ae_restrict_sourceOpenCube_exists_goodSet_frechetGradient_diffWithin_of_convex
      hfiniteStatement hn hbounded hconvex] with x hx
  rcases hx with ⟨m, hxgood, hdiff⟩
  exact
    ⟨m, hxgood,
      cubeGoodSet_differentiableWithinAt_frechetGradient_exists_linearization hdiff⟩

end AleksandrovDifferentiability
