/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.EnergyRHS.Basic

/-! # Dirichlet Split -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Energy RHS: Dirichlet splitting
-/

noncomputable section

open scoped ENNReal

/-- Dirichlet forced-solution energy reduced to the chosen zero-trace
correction and the boundary-gradient energy.  This is the square-root form of
the public `v = (v - h) + h` energy split. -/
theorem dirichletForcedSolutionEnergyNorm_le_sqrt_two_mul_zeroTraceDifference_add_boundary
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g) :
    dirichletForcedSolutionEnergyNorm Q a v ≤
      Real.sqrt
        (2 * cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (fun x => v.zeroTraceDifferenceH10CubeSet.toH1Function.grad x)) +
        2 * cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (dirichletBoundaryGradientField v))) := by
  rw [dirichletForcedSolutionEnergyNorm_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField
    (Q := Q) (a := a) v]
  exact Real.sqrt_le_sqrt
    (v.cubeAverage_energy_le_two_mul_zeroTraceDifference_add_boundary)

/-- Coefficient-energy triangle inequality for a decomposition
`F = G + H` on the cube.  This is the reusable analytic split behind the
Dirichlet proof route `v = v₀ + \widetilde h`. -/
theorem cubeAverage_coefficientEnergyDensity_le_two_mul_add_of_ae_eq_add
    {d : ℕ} {Q : TriadicCube d} {A : CoeffField d} {lam Lam : ℝ}
    {F G H : Vec d → Vec d}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) A)
    (hF : MemVectorL2 (cubeSet Q) F)
    (hG : MemVectorL2 (cubeSet Q) G)
    (hH : MemVectorL2 (cubeSet Q) H)
    (hFGH : F =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)]
      fun x => G x + H x) :
    cubeAverage Q (coefficientEnergyDensity A F) ≤
      2 * cubeAverage Q (coefficientEnergyDensity A G) +
        2 * cubeAverage Q (coefficientEnergyDensity A H) := by
  let Hneg : Vec d → Vec d := (-1 : ℝ) • H
  have hHneg : MemVectorL2 (cubeSet Q) Hneg := by
    dsimp [Hneg]
    exact hH.const_smul (-1)
  have hF_int :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity A F)
        (cubeSet Q) MeasureTheory.volume :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll hF
  have hG_int :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity A G)
        (cubeSet Q) MeasureTheory.volume :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll hG
  have hHneg_int :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity A Hneg)
        (cubeSet Q) MeasureTheory.volume :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll hHneg
  have hmem :
      ∀ᵐ x ∂MeasureTheory.volume.restrict (cubeSet Q), x ∈ cubeSet Q :=
    (MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)).2
      (Filter.Eventually.of_forall fun _ hx => hx)
  have hpoint :
      ∀ᵐ x ∂MeasureTheory.volume.restrict (cubeSet Q),
        coefficientEnergyDensity A F x ≤
          2 * (coefficientEnergyDensity A G x +
            coefficientEnergyDensity A Hneg x) := by
    filter_upwards [hmem, hFGH] with x hx hsum
    have hleft :
        coefficientEnergyDensity A F x =
          coefficientEnergyDensity A (fun y => G y - Hneg y) x := by
      have hvec : F x = G x - Hneg x := by
        rw [hsum]
        simp [Hneg]
      unfold coefficientEnergyDensity
      rw [hvec]
    exact hleft.trans_le
      (coefficientEnergyDensity_sub_le_two_mul_add_of_isEllipticFieldOn
        hEll G Hneg x hx)
  have havg_raw :
      cubeAverage Q (coefficientEnergyDensity A F) ≤
        cubeAverage Q
          (fun x => 2 * (coefficientEnergyDensity A G x +
            coefficientEnergyDensity A Hneg x)) := by
    unfold cubeAverage
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (cubeVolume_nonneg Q))
    exact
      MeasureTheory.integral_mono_ae hF_int
        ((hG_int.add hHneg_int).const_mul (2 : ℝ)) hpoint
  have hsplit :
      cubeAverage Q
          (fun x => 2 * (coefficientEnergyDensity A G x +
            coefficientEnergyDensity A Hneg x)) =
        2 * cubeAverage Q (coefficientEnergyDensity A G) +
          2 * cubeAverage Q (coefficientEnergyDensity A Hneg) := by
    unfold cubeAverage
    have hfun :
        (fun x => 2 * (coefficientEnergyDensity A G x +
            coefficientEnergyDensity A Hneg x)) =
          fun x => 2 * coefficientEnergyDensity A G x +
            2 * coefficientEnergyDensity A Hneg x := by
      funext x
      ring
    rw [hfun, MeasureTheory.integral_add (hG_int.const_mul (2 : ℝ))
      (hHneg_int.const_mul (2 : ℝ))]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    ring
  have hneg_avg :
      cubeAverage Q (coefficientEnergyDensity A Hneg) =
        cubeAverage Q (coefficientEnergyDensity A H) := by
    apply cubeAverage_eq_of_eq_on_cubeSet
    intro x _hx
    unfold coefficientEnergyDensity
    simp [Hneg, matVecMul_neg, vecDot_neg_left, vecDot_neg_right]
  calc
    cubeAverage Q (coefficientEnergyDensity A F)
        ≤
      cubeAverage Q
        (fun x => 2 * (coefficientEnergyDensity A G x +
          coefficientEnergyDensity A Hneg x)) := havg_raw
    _ =
      2 * cubeAverage Q (coefficientEnergyDensity A G) +
        2 * cubeAverage Q (coefficientEnergyDensity A Hneg) := hsplit
    _ =
      2 * cubeAverage Q (coefficientEnergyDensity A G) +
        2 * cubeAverage Q (coefficientEnergyDensity A H) := by
        rw [hneg_avg]

/-- Dirichlet forced-solution energy split along the manuscript decomposition
`v = v₀ + \widetilde h`, where `v₀` is a zero-Dirichlet corrector and
`\widetilde h` is the homogeneous boundary-data remainder. -/
theorem dirichletForcedSolutionEnergyNorm_le_sqrt_two_mul_zeroTraceCorrector_add_harmonicRemainder
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (w : AHarmonicFunction (publicCoeffField Q a) (cubeSet Q))
    (hgrad :
      v.toH1.grad =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)]
        fun x => ρ.toH10.toH1Function.grad x + w.toH1.grad x) :
    dirichletForcedSolutionEnergyNorm Q a v ≤
      Real.sqrt
        (2 * cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (fun x => ρ.toH10.toH1Function.grad x))) +
      Real.sqrt
        (2 * cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (fun x => w.toH1.grad x))) := by
  let E₀ : ℝ :=
    cubeAverage Q
      (coefficientEnergyDensity (publicCoeffField Q a)
        (fun x => ρ.toH10.toH1Function.grad x))
  let Eh : ℝ :=
    cubeAverage Q
      (coefficientEnergyDensity (publicCoeffField Q a)
        (fun x => w.toH1.grad x))
  have hF : MemVectorL2 (cubeSet Q) v.toH1.grad := by
    simpa [publicH1ToCubeSet_grad] using
      (publicH1ToCubeSet v.toH1).grad_memVectorL2
  have hsplit :
      cubeAverage Q (coefficientEnergyDensity (publicCoeffField Q a) v.toH1.grad) ≤
        2 * E₀ + 2 * Eh := by
    simpa [E₀, Eh] using
      cubeAverage_coefficientEnergyDensity_le_two_mul_add_of_ae_eq_add
        (Q := Q) (A := publicCoeffField Q a)
        (lam := (a.coeffOn Q).lam) (Lam := (a.coeffOn Q).Lam)
        (F := v.toH1.grad)
        (G := fun x => ρ.toH10.toH1Function.grad x)
        (H := fun x => w.toH1.grad x)
        (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
        hF ρ.toH10.toH1Function.grad_memVectorL2 w.toH1.grad_memVectorL2
        hgrad
  have hE₀_nonneg : 0 ≤ E₀ := by
    dsimp [E₀]
    exact cubeAverage_nonneg_of_nonneg_on
      (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
        (fun x => ρ.toH10.toH1Function.grad x))
  have hEh_nonneg : 0 ≤ Eh := by
    dsimp [Eh]
    exact cubeAverage_nonneg_of_nonneg_on
      (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
        (fun x => w.toH1.grad x))
  calc
    dirichletForcedSolutionEnergyNorm Q a v
        =
      Real.sqrt
        (cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a) v.toH1.grad)) := by
        rw [dirichletForcedSolutionEnergyNorm_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField
          (Q := Q) (a := a) v]
    _ ≤ Real.sqrt (2 * E₀ + 2 * Eh) := Real.sqrt_le_sqrt hsplit
    _ ≤ Real.sqrt (2 * E₀) + Real.sqrt (2 * Eh) := by
        exact sqrt_add_le_add_sqrt_of_nonneg
          (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hE₀_nonneg)
          (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hEh_nonneg)
    _ =
      Real.sqrt
          (2 * cubeAverage Q
            (coefficientEnergyDensity (publicCoeffField Q a)
              (fun x => ρ.toH10.toH1Function.grad x))) +
        Real.sqrt
          (2 * cubeAverage Q
            (coefficientEnergyDensity (publicCoeffField Q a)
              (fun x => w.toH1.grad x))) := by
        simp [E₀, Eh]

/-- Manuscript-route assembly for the public Dirichlet estimate: after
choosing the zero-Dirichlet forced corrector and the homogeneous boundary
remainder, the two square-root bounds imply the displayed RHS. -/
theorem dirichletForcedSolutionEnergyNorm_le_dirichletEnergyWithRHSRHS_of_zeroTraceCorrector_and_harmonicRemainder_bounds
    {d : ℕ} [NeZero d] {C : ℝ}
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (w : AHarmonicFunction (publicCoeffField Q a) (cubeSet Q))
    (hgrad :
      v.toH1.grad =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)]
        fun x => ρ.toH10.toH1Function.grad x + w.toH1.grad x)
    (hzero :
      Real.sqrt
          (2 * cubeAverage Q
            (coefficientEnergyDensity (publicCoeffField Q a)
              (fun x => ρ.toH10.toH1Function.grad x))) ≤
        C * Real.rpow s (-(3 / 2 : ℝ)) *
          poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q s g)
    (hharmonic :
      Real.sqrt
          (2 * cubeAverage Q
            (coefficientEnergyDensity (publicCoeffField Q a)
              (fun x => w.toH1.grad x))) ≤
        C * Real.rpow s (-(1 / 2 : ℝ)) *
          poincareUpperEllipticityFactor Q a s (.finite 2) *
          scaleNormalizedPositiveBesovVectorNormTwo Q s
            (dirichletBoundaryGradientField v)) :
    dirichletForcedSolutionEnergyNorm Q a v ≤
      dirichletEnergyWithRHSRHS C Q a s g v := by
  calc
    dirichletForcedSolutionEnergyNorm Q a v
        ≤
      Real.sqrt
          (2 * cubeAverage Q
            (coefficientEnergyDensity (publicCoeffField Q a)
              (fun x => ρ.toH10.toH1Function.grad x))) +
        Real.sqrt
          (2 * cubeAverage Q
            (coefficientEnergyDensity (publicCoeffField Q a)
              (fun x => w.toH1.grad x))) :=
        dirichletForcedSolutionEnergyNorm_le_sqrt_two_mul_zeroTraceCorrector_add_harmonicRemainder
          (Q := Q) (a := a) (g := g) v ρ w hgrad
    _ ≤
        C * Real.rpow s (-(3 / 2 : ℝ)) *
            poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q s g +
          C * Real.rpow s (-(1 / 2 : ℝ)) *
            poincareUpperEllipticityFactor Q a s (.finite 2) *
            scaleNormalizedPositiveBesovVectorNormTwo Q s
              (dirichletBoundaryGradientField v) :=
        add_le_add hzero hharmonic
    _ = dirichletEnergyWithRHSRHS C Q a s g v := by
        rfl

end

end Ch03
end Book
end Homogenization
