/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.EnergyRHS.BoundaryGradient

/-! # Corrector -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Energy RHS: Zero-trace corrector estimates
-/

noncomputable section

open scoped ENNReal

private theorem sqrt_two_mul_rpow_half_neg_three_halves {s : ℝ} (hs : 0 < s) :
    Real.sqrt 2 * (s / 2) ^ (-(3 / 2 : ℝ)) =
      4 * s ^ (-(3 / 2 : ℝ)) := by
  have hscale :
      (s / 2) ^ (-(3 / 2 : ℝ)) =
        (2 : ℝ) ^ (3 / 2 : ℝ) * s ^ (-(3 / 2 : ℝ)) := by
    calc
      (s / 2) ^ (-(3 / 2 : ℝ))
          =
        s ^ (-(3 / 2 : ℝ)) / (2 : ℝ) ^ (-(3 / 2 : ℝ)) := by
          rw [Real.div_rpow hs.le (by norm_num : (0 : ℝ) ≤ 2)]
      _ =
        s ^ (-(3 / 2 : ℝ)) / ((2 : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
          rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      _ =
        (2 : ℝ) ^ (3 / 2 : ℝ) * s ^ (-(3 / 2 : ℝ)) := by
          field_simp
  have htwo : Real.sqrt 2 * (2 : ℝ) ^ (3 / 2 : ℝ) = 4 := by
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hscale, ← mul_assoc, htwo]

/-- Zero-boundary auxiliary Dirichlet correctors satisfy the public
zero-Dirichlet energy bound at `t = s / 2`.  This is the `v₀` half of the
Dirichlet energy consequence, separated from the boundary harmonic remainder. -/
theorem zeroTraceDirichletCorrectorData_energyNorm_le_zeroDirichletEnergyWithRHSRHS_half_publicCoeffField
    {d : ℕ} [NeZero d] {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hC_zero :
      Real.sqrt (250 + 2 * Real.sqrt 15000 * Real.sqrt 2) *
          ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) ≤ C)
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
    {g : Vec d → Vec d}
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g) :
    Real.sqrt
        (cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (fun x => ρ.toH10.toH1Function.grad x))) ≤
      zeroDirichletEnergyWithRHSRHS ((d : ℝ) * C) Q a (s / 2) g := by
  have hs_le : s ≤ 1 := hs_lt.le
  have henergy :
      cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (fun x => ρ.toH10.toH1Function.grad x)) ≤
        _root_.Homogenization.zeroTraceDirichletEnergyEnvelope
          Q (publicCoeffField Q a) s g :=
    ρ.coefficientEnergy_average_le_zeroTraceDirichletEnergyEnvelope_noteConstants_expanded_of_cubeVectorBesovHRegularity
      (s := s) (lam := (a.coeffOn Q).lam) (Lam := (a.coeffOn Q).Lam)
      hs hs_le (publicCoeffField_isEllipticFieldOn_cubeSet Q a) hg
  have hs_half_pos : 0 < s / 2 := by nlinarith
  have hs_half_lt : s / 2 < 1 / 2 := by nlinarith
  have htwo : 2 * (s / 2) = s := by ring
  have hg_half : ForceBesovRegularity Q (2 * (s / 2)) g := by
    simpa [htwo] using hg
  have hpub :
      Real.sqrt
          (_root_.Homogenization.zeroTraceDirichletEnergyEnvelope
            Q (publicCoeffField Q a) s g) ≤
        zeroDirichletEnergyWithRHSRHS ((d : ℝ) * C) Q a (s / 2) g := by
    simpa [htwo] using
      zeroTraceDirichletEnergyEnvelope_sqrt_le_publicRHS
        (d := d) (C := C) hC_nonneg hC_zero
        (Q := Q) (a := a) (t := s / 2) (g := g)
        hs_half_pos hs_half_lt hg_half
  exact (Real.sqrt_le_sqrt henergy).trans hpub

/-- Canonical public zero-trace corrector version of the zero-boundary
Dirichlet energy bound. -/
theorem publicZeroTraceDirichletCorrectorData_energyNorm_le_zeroDirichletEnergyWithRHSRHS_half
    {d : ℕ} [NeZero d] {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hC_zero :
      Real.sqrt (250 + 2 * Real.sqrt 15000 * Real.sqrt 2) *
          ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) ≤ C)
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
    {g : Vec d → Vec d}
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g) :
    Real.sqrt
        (cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (fun x =>
              (zeroTraceDirichletCorrectorData_publicCoeffField Q a
                (memVectorL2_cubeSet_of_forceBesovRegularity hg)).toH10.toH1Function.grad x))) ≤
      zeroDirichletEnergyWithRHSRHS ((d : ℝ) * C) Q a (s / 2) g :=
  zeroTraceDirichletCorrectorData_energyNorm_le_zeroDirichletEnergyWithRHSRHS_half_publicCoeffField
    (C := C) hC_nonneg hC_zero
    (ρ := zeroTraceDirichletCorrectorData_publicCoeffField Q a
      (memVectorL2_cubeSet_of_forceBesovRegularity hg))
    hs hs_lt hg

/-- Zero-boundary auxiliary Dirichlet correctors satisfy the zero-trace part of
the public Dirichlet energy RHS after absorbing the half-scale normalization
and the factor `sqrt 2` from the energy split. -/
theorem zeroTraceDirichletCorrectorData_sqrt_two_energyNorm_le_dirichletEnergyFirstTerm_publicCoeffField
    {d : ℕ} [NeZero d] {C₀ C : ℝ}
    (hC₀_nonneg : 0 ≤ C₀)
    (hC₀_zero :
      Real.sqrt (250 + 2 * Real.sqrt 15000 * Real.sqrt 2) *
          ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) ≤ C₀)
    (hC_absorb : 4 * ((d : ℝ) * C₀) ≤ C)
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
    {g : Vec d → Vec d}
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g) :
    Real.sqrt
        (2 * cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (fun x => ρ.toH10.toH1Function.grad x))) ≤
      C * Real.rpow s (-(3 / 2 : ℝ)) *
        poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
        scaleNormalizedPositiveBesovVectorSeminormTwo Q s g := by
  let E : ℝ :=
    cubeAverage Q
      (coefficientEnergyDensity (publicCoeffField Q a)
        (fun x => ρ.toH10.toH1Function.grad x))
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact cubeAverage_nonneg_of_nonneg_on
      (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
        (fun x => ρ.toH10.toH1Function.grad x))
  have hbase :
      Real.sqrt E ≤
        zeroDirichletEnergyWithRHSRHS ((d : ℝ) * C₀) Q a (s / 2) g := by
    simpa [E] using
      zeroTraceDirichletCorrectorData_energyNorm_le_zeroDirichletEnergyWithRHSRHS_half_publicCoeffField
        (C := C₀) hC₀_nonneg hC₀_zero (ρ := ρ) hs hs_lt hg
  have hlower_nonneg :
      0 ≤ poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) := by
    unfold poincareLowerEllipticityFactor
    exact Real.rpow_nonneg
      (Ch02.lambdaSq_finite_nonneg Q a (by nlinarith : 0 < s / 2)
        (by norm_num : (1 : ℝ) ≤ 2)) _
  have hseminorm_nonneg :
      0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo Q s g :=
    scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      (Q := Q) (s := s) (g := g) hg
  have htail_nonneg :
      0 ≤ Real.rpow s (-(3 / 2 : ℝ)) *
        poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
        scaleNormalizedPositiveBesovVectorSeminormTwo Q s g :=
    mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hs.le _) hlower_nonneg)
      hseminorm_nonneg
  calc
    Real.sqrt
        (2 * cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (fun x => ρ.toH10.toH1Function.grad x)))
        =
      Real.sqrt 2 * Real.sqrt E := by
        dsimp [E]
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ Real.sqrt 2 * zeroDirichletEnergyWithRHSRHS ((d : ℝ) * C₀) Q a (s / 2) g :=
        mul_le_mul_of_nonneg_left hbase (Real.sqrt_nonneg 2)
    _ =
      (4 * ((d : ℝ) * C₀)) * Real.rpow s (-(3 / 2 : ℝ)) *
        poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
        scaleNormalizedPositiveBesovVectorSeminormTwo Q s g := by
        unfold zeroDirichletEnergyWithRHSRHS
        rw [show 2 * (s / 2) = s by ring]
        change
          Real.sqrt 2 *
              (((d : ℝ) * C₀) * (s / 2) ^ (-(3 / 2 : ℝ)) *
                poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
                scaleNormalizedPositiveBesovVectorSeminormTwo Q s g) =
            (4 * ((d : ℝ) * C₀)) * s ^ (-(3 / 2 : ℝ)) *
              poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q s g
        rw [show
          Real.sqrt 2 * (((d : ℝ) * C₀) * (s / 2) ^ (-(3 / 2 : ℝ)) *
                poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
                scaleNormalizedPositiveBesovVectorSeminormTwo Q s g) =
            ((d : ℝ) * C₀) * (Real.sqrt 2 * (s / 2) ^ (-(3 / 2 : ℝ))) *
              poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q s g by ring]
        rw [sqrt_two_mul_rpow_half_neg_three_halves hs]
        ring
    _ ≤
      C * Real.rpow s (-(3 / 2 : ℝ)) *
        poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
        scaleNormalizedPositiveBesovVectorSeminormTwo Q s g := by
        calc
          (4 * ((d : ℝ) * C₀)) * Real.rpow s (-(3 / 2 : ℝ)) *
              poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q s g
              =
            (4 * ((d : ℝ) * C₀)) *
              (Real.rpow s (-(3 / 2 : ℝ)) *
                poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
                scaleNormalizedPositiveBesovVectorSeminormTwo Q s g) := by
              ring
          _ ≤
            C *
              (Real.rpow s (-(3 / 2 : ℝ)) *
                poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
                scaleNormalizedPositiveBesovVectorSeminormTwo Q s g) :=
              mul_le_mul_of_nonneg_right hC_absorb htail_nonneg
          _ =
            C * Real.rpow s (-(3 / 2 : ℝ)) *
              poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q s g := by
              ring

/-- Canonical public zero-trace corrector version of the first Dirichlet RHS
summand bound. -/
theorem publicZeroTraceDirichletCorrectorData_sqrt_two_energyNorm_le_dirichletEnergyFirstTerm
    {d : ℕ} [NeZero d] {C₀ C : ℝ}
    (hC₀_nonneg : 0 ≤ C₀)
    (hC₀_zero :
      Real.sqrt (250 + 2 * Real.sqrt 15000 * Real.sqrt 2) *
          ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) ≤ C₀)
    (hC_absorb : 4 * ((d : ℝ) * C₀) ≤ C)
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
    {g : Vec d → Vec d}
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g) :
    Real.sqrt
        (2 * cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (fun x =>
              (zeroTraceDirichletCorrectorData_publicCoeffField Q a
                (memVectorL2_cubeSet_of_forceBesovRegularity hg)).toH10.toH1Function.grad x))) ≤
      C * Real.rpow s (-(3 / 2 : ℝ)) *
        poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
        scaleNormalizedPositiveBesovVectorSeminormTwo Q s g :=
  zeroTraceDirichletCorrectorData_sqrt_two_energyNorm_le_dirichletEnergyFirstTerm_publicCoeffField
    (C₀ := C₀) (C := C) hC₀_nonneg hC₀_zero hC_absorb
    (ρ := zeroTraceDirichletCorrectorData_publicCoeffField Q a
      (memVectorL2_cubeSet_of_forceBesovRegularity hg))
    hs hs_lt hg

/-- Dirichlet energy assembly along the manuscript decomposition after the
zero-trace corrector half has been discharged by the public zero-Dirichlet
estimate.  The remaining explicit input is the homogeneous boundary-remainder
energy bound. -/
theorem dirichletForcedSolutionEnergyNorm_le_dirichletEnergyWithRHSRHS_of_zeroTraceCorrector_public_bound_and_harmonicRemainder_bound
    {d : ℕ} [NeZero d] {C₀ C : ℝ}
    (hC₀_nonneg : 0 ≤ C₀)
    (hC₀_zero :
      Real.sqrt (250 + 2 * Real.sqrt 15000 * Real.sqrt 2) *
          ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) ≤ C₀)
    (hC_absorb : 4 * ((d : ℝ) * C₀) ≤ C)
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
    (ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g)
    (w : AHarmonicFunction (publicCoeffField Q a) (cubeSet Q))
    (hgrad :
      v.toH1.grad =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)]
        fun x => ρ.toH10.toH1Function.grad x + w.toH1.grad x)
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g)
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
      dirichletEnergyWithRHSRHS C Q a s g v :=
  dirichletForcedSolutionEnergyNorm_le_dirichletEnergyWithRHSRHS_of_zeroTraceCorrector_and_harmonicRemainder_bounds
    (Q := Q) (a := a) (s := s) (g := g) v ρ w hgrad
    (zeroTraceDirichletCorrectorData_sqrt_two_energyNorm_le_dirichletEnergyFirstTerm_publicCoeffField
      (C₀ := C₀) (C := C) hC₀_nonneg hC₀_zero hC_absorb
      (ρ := ρ) hs hs_lt hg)
    hharmonic

/-- Canonical public zero-trace-corrector variant of the manuscript Dirichlet
energy assembly. -/
theorem dirichletForcedSolutionEnergyNorm_le_dirichletEnergyWithRHSRHS_of_publicZeroTraceCorrector_and_harmonicRemainder_bound
    {d : ℕ} [NeZero d] {C₀ C : ℝ}
    (hC₀_nonneg : 0 ≤ C₀)
    (hC₀_zero :
      Real.sqrt (250 + 2 * Real.sqrt 15000 * Real.sqrt 2) *
          ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) ≤ C₀)
    (hC_absorb : 4 * ((d : ℝ) * C₀) ≤ C)
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
    (w : AHarmonicFunction (publicCoeffField Q a) (cubeSet Q))
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g)
    (hgrad :
      v.toH1.grad =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)]
        fun x =>
          (zeroTraceDirichletCorrectorData_publicCoeffField Q a
            (memVectorL2_cubeSet_of_forceBesovRegularity hg)).toH10.toH1Function.grad x +
            w.toH1.grad x)
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
      dirichletEnergyWithRHSRHS C Q a s g v :=
  dirichletForcedSolutionEnergyNorm_le_dirichletEnergyWithRHSRHS_of_zeroTraceCorrector_public_bound_and_harmonicRemainder_bound
    (C₀ := C₀) (C := C) hC₀_nonneg hC₀_zero hC_absorb
    (Q := Q) (a := a) (s := s) (g := g) v
    (zeroTraceDirichletCorrectorData_publicCoeffField Q a
      (memVectorL2_cubeSet_of_forceBesovRegularity hg))
    w hgrad hs hs_lt hg hharmonic

/-- The zero-trace corrector and homogeneous harmonic remainder in the
manuscript Dirichlet decomposition can be constructed from the public forced
Dirichlet solution.  The resulting energy estimate still isolates the genuine
boundary-remainder energy input. -/
theorem exists_zeroTraceCorrector_harmonicRemainder_dirichletForcedSolutionEnergyNorm_le_dirichletEnergyWithRHSRHS_of_harmonicRemainder_bound
    {d : ℕ} [NeZero d] {C₀ C : ℝ}
    (hC₀_nonneg : 0 ≤ C₀)
    (hC₀_zero :
      Real.sqrt (250 + 2 * Real.sqrt 15000 * Real.sqrt 2) *
          ((d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) ≤ C₀)
    (hC_absorb : 4 * ((d : ℝ) * C₀) ≤ C)
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
    (hs : 0 < s) (hs_lt : s < 1) (hg : ForceBesovRegularity Q s g) :
    ∃ ρ : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g,
      ∃ w : AHarmonicFunction (publicCoeffField Q a) (cubeSet Q),
        (v.toH1.grad =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)]
          fun x => ρ.toH10.toH1Function.grad x + w.toH1.grad x) ∧
        ((Real.sqrt
            (2 * cubeAverage Q
              (coefficientEnergyDensity (publicCoeffField Q a)
                (fun x => w.toH1.grad x))) ≤
          C * Real.rpow s (-(1 / 2 : ℝ)) *
            poincareUpperEllipticityFactor Q a s (.finite 2) *
            scaleNormalizedPositiveBesovVectorNormTwo Q s
              (dirichletBoundaryGradientField v)) →
          dirichletForcedSolutionEnergyNorm Q a v ≤
            dirichletEnergyWithRHSRHS C Q a s g v) := by
  let U : H1Function (cubeSet Q) := publicH1ToCubeSet v.toH1
  have hweak :
      IsH1DirichletRhsWeakSolutionOn (publicCoeffField Q a) (cubeSet Q) U g := by
    simpa [U] using
      isH1DirichletRhsWeakSolutionOn_publicCoeffField_cubeSet_of_isForcedEquation
        (Q := Q) (a := a) (u := v.toH1) (g := g) v.weakSolution
  have hg_mem : MemVectorL2 (cubeSet Q) g :=
    memVectorL2_cubeSet_of_forceBesovRegularity hg
  have hresidual :
      IsSolenoidalOn (cubeSet Q)
        (fun x => matVecMul (publicCoeffField Q a x) (U.grad x) - g x) :=
    hweak.residual_solenoidal
      (publicCoeffField_isEllipticFieldOn_cubeSet Q a) hg_mem
  rcases
      _root_.Homogenization.ZeroTraceDirichletCorrectorData.exists_corrector_aHarmonicRemainder_of_parent_potential_solenoidal
        (Q := Q) (R := Q) (a := publicCoeffField Q a) (g := g) (n := 0)
        (lam := (a.coeffOn Q).lam) (Lam := (a.coeffOn Q).Lam)
        (u := U.grad)
        U.isPotentialOn hresidual (by simp [descendantsAtDepth_zero])
        (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
        U.grad_memVectorL2 hg_mem with
    ⟨ρ, w, hsplit_point⟩
  have hgrad :
      v.toH1.grad =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)]
        fun x => ρ.toH10.toH1Function.grad x + w.toH1.grad x := by
    refine (MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    have hx_split :
        U.grad x = w.toH1.grad x + ρ.toH10.toH1Function.grad x :=
      hsplit_point x hx
    simpa [U, publicH1ToCubeSet_grad, add_comm] using hx_split
  refine ⟨ρ, w, hgrad, ?_⟩
  intro hharmonic
  exact
    dirichletForcedSolutionEnergyNorm_le_dirichletEnergyWithRHSRHS_of_zeroTraceCorrector_public_bound_and_harmonicRemainder_bound
      (C₀ := C₀) (C := C) hC₀_nonneg hC₀_zero hC_absorb
      (Q := Q) (a := a) (s := s) (g := g) v ρ w hgrad
      hs hs_lt hg hharmonic

end

end Ch03
end Book
end Homogenization
