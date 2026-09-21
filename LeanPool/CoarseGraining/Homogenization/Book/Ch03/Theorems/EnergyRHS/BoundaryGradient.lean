/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.EnergyRHS.HarmonicRemainder

/-! # Boundary Gradient -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Energy RHS: Boundary-gradient estimates
-/

noncomputable section

open scoped ENNReal

/-- On the public pointwise coefficient representative, coefficient energy is
controlled by the top-scale raw ellipticity bound.  This is the analytic core
of the boundary-gradient half of the Dirichlet energy estimate; the final
note-facing theorem still has to absorb this raw bound into the displayed
multiscale upper-ellipticity factor. -/
theorem cubeAverage_coefficientEnergyDensity_publicCoeffField_le_Lam_mul_cubeAverage_vecNormSq
    {d : ℕ} {Q : TriadicCube d} {a : CoeffFamily d}
    {F : Vec d → Vec d} (hF : MemVectorL2 (cubeSet Q) F) :
    cubeAverage Q (coefficientEnergyDensity (publicCoeffField Q a) F) ≤
      (a.coeffOn Q).Lam * cubeAverage Q (fun x => vecNormSq (F x)) := by
  let A : CoeffField d := publicCoeffField Q a
  let Lam : ℝ := (a.coeffOn Q).Lam
  have hEll : IsEllipticFieldOn (a.coeffOn Q).lam Lam (cubeSet Q) A := by
    simpa [A, Lam] using publicCoeffField_isEllipticFieldOn_cubeSet Q a
  have henergy_int :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity A F)
        (cubeSet Q) MeasureTheory.volume :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll hF
  have hsq_int :
      MeasureTheory.IntegrableOn (fun x => vecNormSq (F x))
        (cubeSet Q) MeasureTheory.volume := by
    simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hF hF
  have hpoint :
      ∀ x ∈ cubeSet Q,
        coefficientEnergyDensity A F x ≤ Lam * vecNormSq (F x) := by
    intro x hx
    unfold coefficientEnergyDensity
    exact upperBound_symmPart_of_isEllipticMatrix (hEll.2 x hx) (F x)
  have havg :
      cubeAverage Q (coefficientEnergyDensity A F) ≤
        cubeAverage Q (fun x => Lam * vecNormSq (F x)) := by
    unfold cubeAverage
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (cubeVolume_nonneg Q))
    exact
      MeasureTheory.integral_mono_ae henergy_int (hsq_int.const_mul Lam) <|
        (MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)).2 <|
          Filter.Eventually.of_forall hpoint
  have hscale :
      cubeAverage Q (fun x => Lam * vecNormSq (F x)) =
        Lam * cubeAverage Q (fun x => vecNormSq (F x)) := by
    unfold cubeAverage
    rw [MeasureTheory.integral_const_mul]
    ring
  simpa [A, Lam] using havg.trans_eq hscale

/-- Boundary-gradient coefficient energy is bounded by the raw ellipticity
constant times the Euclidean `L²` size of the public boundary gradient. -/
theorem dirichletBoundaryGradient_energy_le_Lam_mul_cubeAverage_vecNormSq
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g) :
    cubeAverage Q
        (coefficientEnergyDensity (publicCoeffField Q a)
          (dirichletBoundaryGradientField v)) ≤
      (a.coeffOn Q).Lam *
        cubeAverage Q (fun x => vecNormSq (dirichletBoundaryGradientField v x)) := by
  have hF : MemVectorL2 (cubeSet Q) (dirichletBoundaryGradientField v) := by
    simpa [dirichletBoundaryGradientField, publicH1ToCubeSet_grad] using
      (publicH1ToCubeSet v.boundaryData).grad_memVectorL2
  exact
    cubeAverage_coefficientEnergyDensity_publicCoeffField_le_Lam_mul_cubeAverage_vecNormSq
      (Q := Q) (a := a) hF

/-- Square-root boundary-gradient version of the raw top-ellipticity bridge. -/
theorem dirichletBoundaryGradient_sqrt_two_energy_le_sqrt_rawLam_l2
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g) :
    Real.sqrt
        (2 * cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (dirichletBoundaryGradientField v))) ≤
      Real.sqrt (2 * (a.coeffOn Q).Lam) *
        Real.sqrt
          (cubeAverage Q (fun x => vecNormSq (dirichletBoundaryGradientField v x))) := by
  let E : ℝ :=
    cubeAverage Q
      (coefficientEnergyDensity (publicCoeffField Q a)
        (dirichletBoundaryGradientField v))
  let L : ℝ :=
    cubeAverage Q (fun x => vecNormSq (dirichletBoundaryGradientField v x))
  let Lam : ℝ := (a.coeffOn Q).Lam
  have hE_le : E ≤ Lam * L := by
    simpa [E, L, Lam] using
      dirichletBoundaryGradient_energy_le_Lam_mul_cubeAverage_vecNormSq
        (Q := Q) (a := a) (g := g) v
  have hLam_nonneg : 0 ≤ Lam := by
    exact le_trans (le_of_lt (a.coeffOn Q).lam_pos) (by simpa [Lam] using (a.coeffOn Q).lam_le_Lam)
  have hmul :
      2 * E ≤ 2 * Lam * L := by
    nlinarith
  simpa [E, L, Lam, mul_assoc] using
    (calc
      Real.sqrt (2 * E)
          ≤ Real.sqrt (2 * Lam * L) :=
            Real.sqrt_le_sqrt hmul
      _ =
        Real.sqrt (2 * Lam) * Real.sqrt L := by
          rw [Real.sqrt_mul (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hLam_nonneg)])

/-- Boundary-gradient coefficient energy controlled by the public positive
Besov norm, with the raw top ellipticity constant still explicit. -/
theorem dirichletBoundaryGradient_sqrt_two_energy_le_sqrt_card_rawLam_mul_positiveBesovNorm
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
    (hboundary : ForceBesovRegularity Q s (dirichletBoundaryGradientField v)) :
    Real.sqrt
        (2 * cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (dirichletBoundaryGradientField v))) ≤
      Real.sqrt (2 * (a.coeffOn Q).Lam) *
        Real.sqrt (Fintype.card (Fin d) : ℝ) *
        scaleNormalizedPositiveBesovVectorNormTwo Q s
          (dirichletBoundaryGradientField v) := by
  have hraw :=
    dirichletBoundaryGradient_sqrt_two_energy_le_sqrt_rawLam_l2
      (Q := Q) (a := a) (g := g) v
  have hl2 :=
    sqrt_cubeAverage_vecNormSq_le_sqrt_card_mul_scaleNormalizedPositiveBesovVectorNormTwo
      (Q := Q) (s := s) (F := dirichletBoundaryGradientField v) hboundary
  calc
    Real.sqrt
        (2 * cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (dirichletBoundaryGradientField v)))
        ≤
      Real.sqrt (2 * (a.coeffOn Q).Lam) *
        Real.sqrt
          (cubeAverage Q (fun x => vecNormSq (dirichletBoundaryGradientField v x))) :=
        hraw
    _ ≤
      Real.sqrt (2 * (a.coeffOn Q).Lam) *
        (Real.sqrt (Fintype.card (Fin d) : ℝ) *
          scaleNormalizedPositiveBesovVectorNormTwo Q s
            (dirichletBoundaryGradientField v)) :=
        mul_le_mul_of_nonneg_left hl2 (Real.sqrt_nonneg _)
    _ =
      Real.sqrt (2 * (a.coeffOn Q).Lam) *
        Real.sqrt (Fintype.card (Fin d) : ℝ) *
        scaleNormalizedPositiveBesovVectorNormTwo Q s
          (dirichletBoundaryGradientField v) := by
        ring

/-- Boundary-gradient half of the public Dirichlet energy estimate, conditional
on the remaining scalar absorption from the raw top ellipticity constant into
the public multiscale upper-ellipticity factor. -/
theorem dirichletBoundaryGradient_sqrt_two_energy_le_dirichletEnergySecondTerm_of_rawLam_absorption
    {d : ℕ} [NeZero d] {C : ℝ}
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
    (habsorb :
      Real.sqrt (2 * (a.coeffOn Q).Lam) *
          Real.sqrt (Fintype.card (Fin d) : ℝ) ≤
        C * Real.rpow s (-(1 / 2 : ℝ)) *
          poincareUpperEllipticityFactor Q a s (.finite 2))
    (hboundary : ForceBesovRegularity Q s (dirichletBoundaryGradientField v)) :
    Real.sqrt
        (2 * cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (dirichletBoundaryGradientField v))) ≤
      C * Real.rpow s (-(1 / 2 : ℝ)) *
        poincareUpperEllipticityFactor Q a s (.finite 2) *
        scaleNormalizedPositiveBesovVectorNormTwo Q s
          (dirichletBoundaryGradientField v) := by
  have hnorm_nonneg :
      0 ≤ scaleNormalizedPositiveBesovVectorNormTwo Q s
        (dirichletBoundaryGradientField v) := by
    unfold scaleNormalizedPositiveBesovVectorNormTwo
    exact add_nonneg (Real.sqrt_nonneg _)
      (scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        (Q := Q) (s := s) (g := dirichletBoundaryGradientField v) hboundary)
  calc
    Real.sqrt
        (2 * cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (dirichletBoundaryGradientField v)))
        ≤
      Real.sqrt (2 * (a.coeffOn Q).Lam) *
        Real.sqrt (Fintype.card (Fin d) : ℝ) *
        scaleNormalizedPositiveBesovVectorNormTwo Q s
          (dirichletBoundaryGradientField v) :=
        dirichletBoundaryGradient_sqrt_two_energy_le_sqrt_card_rawLam_mul_positiveBesovNorm
          (Q := Q) (a := a) (s := s) (g := g) v hboundary
    _ ≤
      (C * Real.rpow s (-(1 / 2 : ℝ)) *
          poincareUpperEllipticityFactor Q a s (.finite 2)) *
        scaleNormalizedPositiveBesovVectorNormTwo Q s
          (dirichletBoundaryGradientField v) :=
        mul_le_mul_of_nonneg_right habsorb hnorm_nonneg
    _ =
      C * Real.rpow s (-(1 / 2 : ℝ)) *
        poincareUpperEllipticityFactor Q a s (.finite 2) *
        scaleNormalizedPositiveBesovVectorNormTwo Q s
          (dirichletBoundaryGradientField v) := by
        ring

/-- Assembly bridge for the public Dirichlet energy estimate: once the
zero-trace and boundary pieces are each bounded by their public RHS
contributions, the full Dirichlet energy bound follows from the coefficient
energy triangle inequality. -/
theorem dirichletForcedSolutionEnergyNorm_le_dirichletEnergyWithRHSRHS_of_zeroTraceDifference_and_boundary_bounds
    {d : ℕ} [NeZero d] {C : ℝ}
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
    (hzero :
      Real.sqrt
          (2 * cubeAverage Q
            (coefficientEnergyDensity (publicCoeffField Q a)
              (fun x => v.zeroTraceDifferenceH10CubeSet.toH1Function.grad x))) ≤
        C * Real.rpow s (-(3 / 2 : ℝ)) *
          poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q s g)
    (hboundary :
      Real.sqrt
          (2 * cubeAverage Q
            (coefficientEnergyDensity (publicCoeffField Q a)
              (dirichletBoundaryGradientField v))) ≤
        C * Real.rpow s (-(1 / 2 : ℝ)) *
          poincareUpperEllipticityFactor Q a s (.finite 2) *
          scaleNormalizedPositiveBesovVectorNormTwo Q s
            (dirichletBoundaryGradientField v)) :
    dirichletForcedSolutionEnergyNorm Q a v ≤
      dirichletEnergyWithRHSRHS C Q a s g v := by
  let E₀ : ℝ :=
    cubeAverage Q
      (coefficientEnergyDensity (publicCoeffField Q a)
        (fun x => v.zeroTraceDifferenceH10CubeSet.toH1Function.grad x))
  let Eh : ℝ :=
    cubeAverage Q
      (coefficientEnergyDensity (publicCoeffField Q a)
        (dirichletBoundaryGradientField v))
  have hE₀_nonneg : 0 ≤ E₀ := by
    dsimp [E₀]
    exact cubeAverage_nonneg_of_nonneg_on
      (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
        (fun x => v.zeroTraceDifferenceH10CubeSet.toH1Function.grad x))
  have hEh_nonneg : 0 ≤ Eh := by
    dsimp [Eh]
    exact cubeAverage_nonneg_of_nonneg_on
      (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
        (dirichletBoundaryGradientField v))
  have hsplit :
      dirichletForcedSolutionEnergyNorm Q a v ≤ Real.sqrt (2 * E₀ + 2 * Eh) := by
    simpa [E₀, Eh] using
      dirichletForcedSolutionEnergyNorm_le_sqrt_two_mul_zeroTraceDifference_add_boundary
        (Q := Q) (a := a) (g := g) v
  calc
    dirichletForcedSolutionEnergyNorm Q a v
        ≤ Real.sqrt (2 * E₀ + 2 * Eh) := hsplit
    _ ≤ Real.sqrt (2 * E₀) + Real.sqrt (2 * Eh) := by
        exact sqrt_add_le_add_sqrt_of_nonneg
          (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hE₀_nonneg)
          (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hEh_nonneg)
    _ ≤
        C * Real.rpow s (-(3 / 2 : ℝ)) *
            poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q s g +
          C * Real.rpow s (-(1 / 2 : ℝ)) *
            poincareUpperEllipticityFactor Q a s (.finite 2) *
            scaleNormalizedPositiveBesovVectorNormTwo Q s
              (dirichletBoundaryGradientField v) := by
        exact add_le_add hzero hboundary
    _ = dirichletEnergyWithRHSRHS C Q a s g v := by
        rfl

/-- Dirichlet energy assembly with the boundary-gradient half discharged by
the raw-ellipticity absorption bridge.  This leaves only the zero-trace
difference estimate as an external input. -/
theorem dirichletForcedSolutionEnergyNorm_le_dirichletEnergyWithRHSRHS_of_zeroTraceDifference_bound_and_rawLam_absorption
    {d : ℕ} [NeZero d] {C : ℝ}
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
    (hzero :
      Real.sqrt
          (2 * cubeAverage Q
            (coefficientEnergyDensity (publicCoeffField Q a)
              (fun x => v.zeroTraceDifferenceH10CubeSet.toH1Function.grad x))) ≤
        C * Real.rpow s (-(3 / 2 : ℝ)) *
          poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q s g)
    (habsorb :
      Real.sqrt (2 * (a.coeffOn Q).Lam) *
          Real.sqrt (Fintype.card (Fin d) : ℝ) ≤
        C * Real.rpow s (-(1 / 2 : ℝ)) *
          poincareUpperEllipticityFactor Q a s (.finite 2))
    (hboundary : ForceBesovRegularity Q s (dirichletBoundaryGradientField v)) :
    dirichletForcedSolutionEnergyNorm Q a v ≤
      dirichletEnergyWithRHSRHS C Q a s g v :=
  dirichletForcedSolutionEnergyNorm_le_dirichletEnergyWithRHSRHS_of_zeroTraceDifference_and_boundary_bounds
    (Q := Q) (a := a) (s := s) (g := g) v hzero
    (dirichletBoundaryGradient_sqrt_two_energy_le_dirichletEnergySecondTerm_of_rawLam_absorption
      (Q := Q) (a := a) (s := s) (g := g) v habsorb hboundary)

end

end Ch03
end Book
end Homogenization
