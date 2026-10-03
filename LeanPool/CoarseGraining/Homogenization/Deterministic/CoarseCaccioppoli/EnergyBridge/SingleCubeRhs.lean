/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.ExactRhs

/-! # Single Cube Rhs -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped BigOperators ENNReal

/-- Note-facing single-cube boundary Caccioppoli RHS.

The parameters `k` and `h` are the triadic gap scale and auxiliary height from
Chapter 3.  The scalar `energyAvg` represents
`‖σ^{1/2}∇u‖_{\underline L^2(Q)}^2`, so its square root is the normalized
energy norm appearing in the first term. -/
def coarseCaccioppoliSingleCubeBoundaryNoteRhs {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s C k h uL2Sq energyAvg : ℝ) : ℝ :=
  C * Real.rpow (3 : ℝ) k *
      Real.rpow (LambdaSq Q 1 (.finite 1) a) (1 / 2 : ℝ) *
      Real.sqrt uL2Sq * Real.sqrt energyAvg +
    (C / (s * (1 - s))) * Real.rpow (3 : ℝ) (k - h) *
      (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
        Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ)) *
      energyAvg

/-- Constant-piece summand of `coarseCaccioppoliSingleCubeBoundaryNoteRhs`. -/
def coarseCaccioppoliSingleCubeBoundaryConstantRhs {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (C k uL2Sq energyAvg : ℝ) : ℝ :=
  C * Real.rpow (3 : ℝ) k *
    Real.rpow (LambdaSq Q 1 (.finite 1) a) (1 / 2 : ℝ) *
    Real.sqrt uL2Sq * Real.sqrt energyAvg

/-- Coefficient in the note's constant-piece RHS, after factoring out the
energy norm. -/
def coarseCaccioppoliSingleCubeBoundaryConstantCoeff {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (C k uL2Sq : ℝ) : ℝ :=
  C * Real.rpow (3 : ℝ) k *
    Real.rpow (LambdaSq Q 1 (.finite 1) a) (1 / 2 : ℝ) *
    Real.sqrt uL2Sq

/-- The constant-piece single-cube coefficient before multiplying by the
global `L²` size of `u`.

This is the coefficient used in the small-cube summation proof: the local
estimate keeps the local `L²` norm of `u`, and the descendant average is
collapsed by finite Cauchy only after summing over the small cubes. -/
def coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (C k : ℝ) : ℝ :=
  C * Real.rpow (3 : ℝ) k *
    Real.rpow (LambdaSq Q 1 (.finite 1) a) (1 / 2 : ℝ)

theorem coarseCaccioppoliSingleCubeBoundaryConstantCoeff_eq_baseCoeff_mul_sqrt
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (C k uL2Sq : ℝ) :
    coarseCaccioppoliSingleCubeBoundaryConstantCoeff Q a C k uL2Sq =
      coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff Q a C k *
        Real.sqrt uL2Sq := by
  rfl

theorem coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {C k : ℝ}
    (hC : 0 ≤ C) :
    0 ≤ coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff Q a C k := by
  unfold coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff
  have hLambda_nonneg : 0 ≤ LambdaSq Q (1 : ℝ) (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q (1 : ℝ) a (by norm_num)
  exact mul_nonneg
    (mul_nonneg hC (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
    (Real.rpow_nonneg hLambda_nonneg _)

/-- The constant base coefficient is monotone increasing in the scale
parameter `k`. -/
theorem coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff_mono_scale {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {C k k' : ℝ}
    (hC : 0 ≤ C) (hk : k ≤ k') :
    coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff Q a C k ≤
      coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff Q a C k' := by
  have hLambda_nonneg : 0 ≤ LambdaSq Q (1 : ℝ) (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q (1 : ℝ) a (by norm_num)
  have hLambda_rpow_nonneg :
      0 ≤ Real.rpow (LambdaSq Q 1 (.finite 1) a) (1 / 2 : ℝ) :=
    Real.rpow_nonneg hLambda_nonneg _
  have hpow :
      Real.rpow (3 : ℝ) k ≤ Real.rpow (3 : ℝ) k' :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ (3 : ℝ)) hk
  calc
    coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff Q a C k
        =
      (C * Real.rpow (3 : ℝ) k) *
        Real.rpow (LambdaSq Q 1 (.finite 1) a) (1 / 2 : ℝ) := by
          rfl
    _ ≤
      (C * Real.rpow (3 : ℝ) k') *
        Real.rpow (LambdaSq Q 1 (.finite 1) a) (1 / 2 : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow hC) hLambda_rpow_nonneg
    _ =
      coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff Q a C k' := by
          rfl

theorem coarseCaccioppoliSingleCubeBoundaryConstantCoeff_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {C k uL2Sq : ℝ}
    (hC : 0 ≤ C) :
    0 ≤ coarseCaccioppoliSingleCubeBoundaryConstantCoeff Q a C k uL2Sq := by
  rw [coarseCaccioppoliSingleCubeBoundaryConstantCoeff_eq_baseCoeff_mul_sqrt]
  exact mul_nonneg
    (coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff_nonneg Q a hC)
    (Real.sqrt_nonneg _)

/-- The constant coefficient after inserting the global `L²` size is monotone
in the scale parameter `k`. -/
theorem coarseCaccioppoliSingleCubeBoundaryConstantCoeff_mono_scale {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {C k k' uL2Sq : ℝ}
    (hC : 0 ≤ C) (hk : k ≤ k') :
    coarseCaccioppoliSingleCubeBoundaryConstantCoeff Q a C k uL2Sq ≤
      coarseCaccioppoliSingleCubeBoundaryConstantCoeff Q a C k' uL2Sq := by
  rw [coarseCaccioppoliSingleCubeBoundaryConstantCoeff_eq_baseCoeff_mul_sqrt,
    coarseCaccioppoliSingleCubeBoundaryConstantCoeff_eq_baseCoeff_mul_sqrt]
  exact mul_le_mul_of_nonneg_right
    (coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff_mono_scale Q a hC hk)
    (Real.sqrt_nonneg _)

theorem coarseCaccioppoliSingleCubeBoundaryConstantRhs_eq_coeff_mul {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (C k uL2Sq energyAvg : ℝ) :
    coarseCaccioppoliSingleCubeBoundaryConstantRhs Q a C k uL2Sq energyAvg =
      coarseCaccioppoliSingleCubeBoundaryConstantCoeff Q a C k uL2Sq *
        Real.sqrt energyAvg := by
  unfold coarseCaccioppoliSingleCubeBoundaryConstantRhs
    coarseCaccioppoliSingleCubeBoundaryConstantCoeff
  ring

/-- Centered-piece summand of `coarseCaccioppoliSingleCubeBoundaryNoteRhs`. -/
def coarseCaccioppoliSingleCubeBoundaryCenteredRhs {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s C k h energyAvg : ℝ) : ℝ :=
  (C / (s * (1 - s))) * Real.rpow (3 : ℝ) (k - h) *
    (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
      Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ)) *
    energyAvg

/-- Coefficient in the note's centered-piece RHS after factoring out
`energyAvg`. -/
def coarseCaccioppoliSingleCubeBoundaryCenteredCoeff {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s C k h : ℝ) : ℝ :=
  (C / (s * (1 - s))) * Real.rpow (3 : ℝ) (k - h) *
    (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
      Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ))

theorem coarseCaccioppoliSingleCubeBoundaryCenteredCoeff_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {s C k h : ℝ}
    (hC : 0 ≤ C) (hs0 : 0 < s) (hs1 : s < 1) :
    0 ≤ coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C k h := by
  unfold coarseCaccioppoliSingleCubeBoundaryCenteredCoeff
  have hden_nonneg : 0 ≤ s * (1 - s) := by
    exact mul_nonneg hs0.le (sub_nonneg.mpr hs1.le)
  have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs0.le
  have hlambda_nonneg : 0 ≤ lambdaSq Q (1 - s) (.finite 1) a :=
    multiscale_ellipticity_lambdaSq_one_nonneg Q (1 - s) a (sub_nonneg.mpr hs1.le)
  exact mul_nonneg
    (mul_nonneg
      (div_nonneg hC hden_nonneg)
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
    (mul_nonneg
      (Real.rpow_nonneg hLambda_nonneg _)
      (Real.rpow_nonneg hlambda_nonneg _))

/-- The centered coefficient is monotone increasing in the scale parameter
`k`. -/
theorem coarseCaccioppoliSingleCubeBoundaryCenteredCoeff_mono_scale {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {s C k k' h : ℝ}
    (hC : 0 ≤ C) (hs0 : 0 < s) (hs1 : s < 1) (hk : k ≤ k') :
    coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C k h ≤
      coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C k' h := by
  have hden_nonneg : 0 ≤ s * (1 - s) :=
    mul_nonneg hs0.le (sub_nonneg.mpr hs1.le)
  have hA_nonneg : 0 ≤ C / (s * (1 - s)) :=
    div_nonneg hC hden_nonneg
  have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs0.le
  have hlambda_nonneg : 0 ≤ lambdaSq Q (1 - s) (.finite 1) a :=
    multiscale_ellipticity_lambdaSq_one_nonneg Q (1 - s) a (sub_nonneg.mpr hs1.le)
  have hB_nonneg :
      0 ≤ Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
        Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hLambda_nonneg _)
      (Real.rpow_nonneg hlambda_nonneg _)
  have hpow :
      Real.rpow (3 : ℝ) (k - h) ≤ Real.rpow (3 : ℝ) (k' - h) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ (3 : ℝ)) ?_
    linarith
  calc
    coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C k h
        =
      (C / (s * (1 - s)) * Real.rpow (3 : ℝ) (k - h)) *
        (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
          Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ)) := by
          rfl
    _ ≤
      (C / (s * (1 - s)) * Real.rpow (3 : ℝ) (k' - h)) *
        (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
          Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow hA_nonneg) hB_nonneg
    _ =
      coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C k' h := by
          rfl

/-- The centered single-cube coefficient is monotone decreasing in the
auxiliary height. -/
theorem coarseCaccioppoliSingleCubeBoundaryCenteredCoeff_anti_mono_height {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {s C k h h' : ℝ}
    (hC : 0 ≤ C) (hs0 : 0 < s) (hs1 : s < 1) (hh : h ≤ h') :
    coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C k h' ≤
      coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C k h := by
  have hden_nonneg : 0 ≤ s * (1 - s) :=
    mul_nonneg hs0.le (sub_nonneg.mpr hs1.le)
  have hA_nonneg : 0 ≤ C / (s * (1 - s)) :=
    div_nonneg hC hden_nonneg
  have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs0.le
  have hlambda_nonneg : 0 ≤ lambdaSq Q (1 - s) (.finite 1) a :=
    multiscale_ellipticity_lambdaSq_one_nonneg Q (1 - s) a (sub_nonneg.mpr hs1.le)
  have hB_nonneg :
      0 ≤ Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
        Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hLambda_nonneg _)
      (Real.rpow_nonneg hlambda_nonneg _)
  have hpow :
      Real.rpow (3 : ℝ) (k - h') ≤ Real.rpow (3 : ℝ) (k - h) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ (3 : ℝ)) ?_
    linarith
  calc
    coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C k h'
        =
      (C / (s * (1 - s)) * Real.rpow (3 : ℝ) (k - h')) *
        (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
          Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ)) := by
          rfl
    _ ≤
      (C / (s * (1 - s)) * Real.rpow (3 : ℝ) (k - h)) *
        (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
          Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow hA_nonneg) hB_nonneg
    _ =
      coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C k h := by
          rfl

theorem coarseCaccioppoliSingleCubeBoundaryCenteredRhs_eq_coeff_mul {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s C k h energyAvg : ℝ) :
    coarseCaccioppoliSingleCubeBoundaryCenteredRhs Q a s C k h energyAvg =
      coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C k h * energyAvg := by
  rfl

theorem coarseCaccioppoliSingleCubeBoundaryNoteRhs_eq_constant_add_centered {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s C k h uL2Sq energyAvg : ℝ) :
    coarseCaccioppoliSingleCubeBoundaryNoteRhs Q a s C k h uL2Sq energyAvg =
      coarseCaccioppoliSingleCubeBoundaryConstantRhs Q a C k uL2Sq energyAvg +
        coarseCaccioppoliSingleCubeBoundaryCenteredRhs Q a s C k h energyAvg := by
  rfl

/-- The note-facing single-cube RHS is monotone increasing in the outer scale
parameter `k`. -/
theorem coarseCaccioppoliSingleCubeBoundaryNoteRhs_mono_scale {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {s C k k' h uL2Sq energyAvg : ℝ}
    (hC : 0 ≤ C) (hs0 : 0 < s) (hs1 : s < 1) (hk : k ≤ k')
    (henergy : 0 ≤ energyAvg) :
    coarseCaccioppoliSingleCubeBoundaryNoteRhs Q a s C k h uL2Sq energyAvg ≤
      coarseCaccioppoliSingleCubeBoundaryNoteRhs Q a s C k' h uL2Sq energyAvg := by
  rw [coarseCaccioppoliSingleCubeBoundaryNoteRhs_eq_constant_add_centered,
    coarseCaccioppoliSingleCubeBoundaryNoteRhs_eq_constant_add_centered]
  exact add_le_add
    (by
      rw [coarseCaccioppoliSingleCubeBoundaryConstantRhs_eq_coeff_mul,
        coarseCaccioppoliSingleCubeBoundaryConstantRhs_eq_coeff_mul]
      exact mul_le_mul_of_nonneg_right
        (coarseCaccioppoliSingleCubeBoundaryConstantCoeff_mono_scale Q a hC hk)
        (Real.sqrt_nonneg _))
    (by
      rw [coarseCaccioppoliSingleCubeBoundaryCenteredRhs_eq_coeff_mul,
        coarseCaccioppoliSingleCubeBoundaryCenteredRhs_eq_coeff_mul]
      exact mul_le_mul_of_nonneg_right
        (coarseCaccioppoliSingleCubeBoundaryCenteredCoeff_mono_scale Q a hC hs0 hs1 hk)
        henergy)

/-- The coefficient-bookkeeping obligation left after the exact local
cutoff/Besov bridge: dominate the exact local RHS by the note's single-cube
RHS. -/
def CoarseCaccioppoliSingleCubeCoefficientDomination {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s C k h uL2Sq : ℝ) (u : Vec d → ℝ) (ξ : Vec d → Vec d)
    (energy : Vec d → ℝ) (Acirc1 AcircS B : ℝ) : Prop :=
  coarseCaccioppoliFluxEnergyExactRhs Q a s u ξ energy Acirc1 AcircS B C ≤
    coarseCaccioppoliSingleCubeBoundaryNoteRhs Q a s C k h uL2Sq (cubeAverage Q energy)

theorem CoarseCaccioppoliSingleCubeCoefficientDomination.of_termwise {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s C k h uL2Sq : ℝ)
    (u : Vec d → ℝ) (ξ : Vec d → Vec d) (energy : Vec d → ℝ)
    (Acirc1 AcircS B : ℝ)
    (hconst :
      coarseCaccioppoliFluxEnergyExactConstantRhs Q a u ξ energy B ≤
        coarseCaccioppoliSingleCubeBoundaryConstantRhs Q a C k uL2Sq
          (cubeAverage Q energy))
    (hcent :
      coarseCaccioppoliFluxEnergyExactCenteredRhs Q a s ξ energy Acirc1 AcircS B C ≤
        coarseCaccioppoliSingleCubeBoundaryCenteredRhs Q a s C k h
          (cubeAverage Q energy)) :
    CoarseCaccioppoliSingleCubeCoefficientDomination Q a s C k h uL2Sq u ξ energy
      Acirc1 AcircS B := by
  unfold CoarseCaccioppoliSingleCubeCoefficientDomination
  rw [coarseCaccioppoliFluxEnergyExactRhs_eq_constant_add_centered,
    coarseCaccioppoliSingleCubeBoundaryNoteRhs_eq_constant_add_centered]
  exact add_le_add hconst hcent

theorem coarseCaccioppoliFluxEnergyExactConstantRhs_le_singleCubeBoundaryConstantRhs
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (u : Vec d → ℝ) (ξ : Vec d → Vec d) (energy : Vec d → ℝ)
    (B C k uL2Sq : ℝ)
    (hcoeff :
      coarseCaccioppoliFluxEnergyExactConstantCoeff Q a *
          coarseCaccioppoliConstantCutoffSize Q u ξ B ≤
        coarseCaccioppoliSingleCubeBoundaryConstantCoeff Q a C k uL2Sq) :
    coarseCaccioppoliFluxEnergyExactConstantRhs Q a u ξ energy B ≤
      coarseCaccioppoliSingleCubeBoundaryConstantRhs Q a C k uL2Sq
        (cubeAverage Q energy) := by
  rw [coarseCaccioppoliFluxEnergyExactConstantRhs_eq_coeff_mul,
    coarseCaccioppoliSingleCubeBoundaryConstantRhs_eq_coeff_mul]
  exact mul_le_mul_of_nonneg_right hcoeff (Real.sqrt_nonneg _)

theorem coarseCaccioppoliFluxEnergyExactCenteredRhs_le_singleCubeBoundaryCenteredRhs
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (ξ : Vec d → Vec d) (energy : Vec d → ℝ) (Acirc1 AcircS B C k h : ℝ)
    (henergy : 0 ≤ cubeAverage Q energy)
    (hcoeff :
      coarseCaccioppoliFluxEnergyExactCenteredCoeff Q a s ξ Acirc1 AcircS B C ≤
        coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C k h) :
    coarseCaccioppoliFluxEnergyExactCenteredRhs Q a s ξ energy Acirc1 AcircS B C ≤
      coarseCaccioppoliSingleCubeBoundaryCenteredRhs Q a s C k h
        (cubeAverage Q energy) := by
  rw [coarseCaccioppoliFluxEnergyExactCenteredRhs_eq_coeff_mul_sqrt_sq,
    coarseCaccioppoliSingleCubeBoundaryCenteredRhs_eq_coeff_mul]
  have hsqrt_sq :
      Real.sqrt (cubeAverage Q energy) * Real.sqrt (cubeAverage Q energy) =
        cubeAverage Q energy := by
    simpa [pow_two] using Real.sq_sqrt henergy
  rw [hsqrt_sq]
  exact mul_le_mul_of_nonneg_right hcoeff henergy

/-- Coefficient-only domination for the constant part of the exact local RHS. -/
def CoarseCaccioppoliConstantCoefficientDomination {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (C k uL2Sq : ℝ) (u : Vec d → ℝ) (ξ : Vec d → Vec d)
    (B : ℝ) : Prop :=
  coarseCaccioppoliFluxEnergyExactConstantCoeff Q a *
      coarseCaccioppoliConstantCutoffSize Q u ξ B ≤
    coarseCaccioppoliSingleCubeBoundaryConstantCoeff Q a C k uL2Sq

/-- Prove constant-piece coefficient domination from separate bounds on the
flux coefficient and cutoff size. -/
theorem CoarseCaccioppoliConstantCoefficientDomination.of_factor_bounds {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (C k uL2Sq : ℝ)
    (u : Vec d → ℝ) (ξ : Vec d → Vec d) {B A G : ℝ}
    (hA_nonneg : 0 ≤ A) (hB : 0 ≤ B)
    (hcoeff : coarseCaccioppoliFluxEnergyExactConstantCoeff Q a ≤ A)
    (hcutoff : coarseCaccioppoliConstantCutoffSize Q u ξ B ≤ G)
    (hAG : A * G ≤ coarseCaccioppoliSingleCubeBoundaryConstantCoeff Q a C k uL2Sq) :
    CoarseCaccioppoliConstantCoefficientDomination Q a C k uL2Sq u ξ B := by
  unfold CoarseCaccioppoliConstantCoefficientDomination
  exact le_trans
    (mul_le_mul hcoeff hcutoff
      (coarseCaccioppoliConstantCutoffSize_nonneg Q u ξ hB) hA_nonneg)
    hAG

/-- Coefficient-only domination for the centered part of the exact local RHS. -/
def CoarseCaccioppoliCenteredCoefficientDomination {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s C k h : ℝ) (ξ : Vec d → Vec d) (Acirc1 AcircS B : ℝ) :
    Prop :=
  coarseCaccioppoliFluxEnergyExactCenteredCoeff Q a s ξ Acirc1 AcircS B C ≤
    coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C k h

/-- Prove centered-piece coefficient domination by bounding the average-flux
and Besov/cutoff-product parts separately. -/
theorem CoarseCaccioppoliCenteredCoefficientDomination.of_termwise {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s C k h : ℝ)
    (ξ : Vec d → Vec d) (Acirc1 AcircS B : ℝ) {X Y : ℝ}
    (havg :
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff Q a ξ Acirc1 C ≤ X)
    (hbesov :
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff Q a s ξ Acirc1 AcircS B C ≤ Y)
    (hXY : X + Y ≤ coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C k h) :
    CoarseCaccioppoliCenteredCoefficientDomination Q a s C k h ξ Acirc1 AcircS B := by
  unfold CoarseCaccioppoliCenteredCoefficientDomination
  rw [coarseCaccioppoliFluxEnergyExactCenteredCoeff_eq_average_add_besov]
  exact le_trans (add_le_add havg hbesov) hXY

/-- The two coefficient inequalities left after the exact cutoff/Besov local
bridge has been factored into constant and centered pieces. -/
def CoarseCaccioppoliSingleCubeCoefficientControls {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s C k h uL2Sq : ℝ) (u : Vec d → ℝ) (ξ : Vec d → Vec d)
    (Acirc1 AcircS B : ℝ) : Prop :=
  CoarseCaccioppoliConstantCoefficientDomination Q a C k uL2Sq u ξ B ∧
    CoarseCaccioppoliCenteredCoefficientDomination Q a s C k h ξ Acirc1 AcircS B

/-- Build the bundled coefficient controls from the separated constant
cutoff-size estimate and the centered average/Besov estimates. -/
theorem CoarseCaccioppoliSingleCubeCoefficientControls.of_factor_bounds {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s C k h uL2Sq : ℝ)
    (u : Vec d → ℝ) (ξ : Vec d → Vec d) (Acirc1 AcircS : ℝ)
    {B A G X Y : ℝ}
    (hA_nonneg : 0 ≤ A) (hB : 0 ≤ B)
    (hconstCoeff : coarseCaccioppoliFluxEnergyExactConstantCoeff Q a ≤ A)
    (hconstCutoff : coarseCaccioppoliConstantCutoffSize Q u ξ B ≤ G)
    (hconst :
      A * G ≤ coarseCaccioppoliSingleCubeBoundaryConstantCoeff Q a C k uL2Sq)
    (havg :
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff Q a ξ Acirc1 C ≤ X)
    (hbesov :
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff Q a s ξ Acirc1 AcircS B C ≤ Y)
    (hcentered :
      X + Y ≤ coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C k h) :
    CoarseCaccioppoliSingleCubeCoefficientControls Q a s C k h uL2Sq u ξ
      Acirc1 AcircS B := by
  constructor
  · exact
      CoarseCaccioppoliConstantCoefficientDomination.of_factor_bounds
        Q a C k uL2Sq u ξ hA_nonneg hB hconstCoeff hconstCutoff hconst
  · exact
      CoarseCaccioppoliCenteredCoefficientDomination.of_termwise
        Q a s C k h ξ Acirc1 AcircS B havg hbesov hcentered

/-- Build the coefficient controls from primitive scalar factor estimates:
bounds for `‖u‖₂`, `‖ξ‖∞`, `‖∇ξ‖∞`, the scalar projected-Poincare factors,
and the average/flux coefficient factors.  This is the final algebraic layer
before a concrete cutoff construction supplies those scalar estimates. -/
theorem CoarseCaccioppoliSingleCubeCoefficientControls.of_separated_factor_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C k h uL2Sq : ℝ)
    (u : Vec d → ℝ) (ξ : Vec d → Vec d) (Acirc1 AcircS : ℝ)
    {B AavgConst AavgCent Aflux1 AfluxS U Xi D A1 AS : ℝ}
    (hs0 : 0 < s) (hC : 0 ≤ C)
    (hB_nonneg : 0 ≤ B) (hAcirc1_nonneg : 0 ≤ Acirc1)
    (hAcircS_nonneg : 0 ≤ AcircS)
    (hAavgConst : Real.sqrt (coarseBBlockNorm Q a) ≤ AavgConst)
    (hAavgCent : Real.sqrt (coarseBBlockNorm Q a) ≤ AavgCent)
    (hAflux1 :
      (geometricDiscount (1 : ℝ) 1)⁻¹ *
          Real.rpow (LambdaSq Q (1 : ℝ) (.finite 1) a) (1 / 2 : ℝ) ≤ Aflux1)
    (hAfluxS :
      (geometricDiscount s 1)⁻¹ *
          Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) ≤ AfluxS)
    (hu : cubeLpNorm Q (2 : ℝ≥0∞) u ≤ U)
    (hξ : cubeLpNorm Q ∞ ξ ≤ Xi)
    (hB : B ≤ D) (hAcirc1 : Acirc1 ≤ A1) (hAcircS : AcircS ≤ AS)
    (hconst :
      coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound Q AavgConst Aflux1 *
          coarseCaccioppoliConstantCutoffSizeFactorBound Q U Xi D ≤
        coarseCaccioppoliSingleCubeBoundaryConstantCoeff Q a C k uL2Sq)
    (hcentered :
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
          (d := d) AavgCent Xi A1 C +
        coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound Q s AavgCent AfluxS
          (coarseCaccioppoliCenteredCutoffCoeffFactorBound Q s Xi D A1 AS C) ≤
          coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C k h) :
    CoarseCaccioppoliSingleCubeCoefficientControls Q a s C k h uL2Sq u ξ
      Acirc1 AcircS B := by
  have hAavgConst_nonneg : 0 ≤ AavgConst := by
    exact le_trans (Real.sqrt_nonneg _) hAavgConst
  have hAavgCent_nonneg : 0 ≤ AavgCent := by
    exact le_trans (Real.sqrt_nonneg _) hAavgCent
  have hdisc1_pos : 0 < geometricDiscount (1 : ℝ) 1 :=
    geometricDiscount_pos (by norm_num : 0 < (1 : ℝ) * (1 : ℝ))
  have hLambda1_nonneg : 0 ≤ LambdaSq Q (1 : ℝ) (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q (1 : ℝ) a (by norm_num)
  have hAflux1_nonneg : 0 ≤ Aflux1 := by
    exact le_trans
      (mul_nonneg (inv_nonneg.mpr hdisc1_pos.le)
        (Real.rpow_nonneg hLambda1_nonneg _))
      hAflux1
  have hdiscS_pos : 0 < geometricDiscount s 1 := by
    exact geometricDiscount_pos (by simpa using hs0)
  have hLambdaS_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs0.le
  have hAfluxS_nonneg : 0 ≤ AfluxS := by
    exact le_trans
      (mul_nonneg (inv_nonneg.mpr hdiscS_pos.le)
        (Real.rpow_nonneg hLambdaS_nonneg _))
      hAfluxS
  have hU_nonneg : 0 ≤ U := by
    exact le_trans (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) u) hu
  have hXi_nonneg : 0 ≤ Xi := by
    exact le_trans (cubeLpNorm_nonneg Q ∞ ξ) hξ
  have hD_nonneg : 0 ≤ D := by
    exact le_trans hB_nonneg hB
  let BgCent : ℝ :=
    coarseCaccioppoliCenteredCutoffCoeffFactorBound Q s Xi D A1 AS C
  have hBgCentCoeff_nonneg :
      0 ≤ coarseCaccioppoliCenteredCutoffCoeff Q s ξ Acirc1 AcircS B C :=
    coarseCaccioppoliCenteredCutoffCoeff_nonneg
      Q ξ hs0 hAcirc1_nonneg hAcircS_nonneg hB_nonneg hC
  have hBgCent :
      coarseCaccioppoliCenteredCutoffCoeff Q s ξ Acirc1 AcircS B C ≤ BgCent := by
    exact
      coarseCaccioppoliCenteredCutoffCoeff_le_factorBound
        Q ξ hs0 hAcirc1_nonneg hAcircS_nonneg hXi_nonneg hD_nonneg hC
        hξ hB hAcirc1 hAcircS
  exact
    CoarseCaccioppoliSingleCubeCoefficientControls.of_factor_bounds
      Q a s C k h uL2Sq u ξ Acirc1 AcircS
      (coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound_nonneg
        Q hAavgConst_nonneg hAflux1_nonneg)
      hB_nonneg
      (coarseCaccioppoliFluxEnergyExactConstantCoeff_le_factorBound
        Q a hAavgConst hAflux1)
      (coarseCaccioppoliConstantCutoffSize_le_factorBound
        Q u ξ hU_nonneg hB_nonneg hu hξ hB)
      hconst
      (coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff_le_factorBound
        Q a ξ hAavgCent_nonneg hXi_nonneg hAcirc1_nonneg hC hAavgCent hξ hAcirc1)
      (by
        simpa [BgCent] using
          (coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff_le_factorBound
            Q a s ξ hAavgCent_nonneg hAfluxS_nonneg hBgCentCoeff_nonneg
            hAavgCent hAfluxS hBgCent))
      (by
        simpa [BgCent] using hcentered)

/-- Canonical-factor version of the primitive coefficient-control constructor.
The average and flux coefficient slots are filled by
`coarseCaccioppoliLambdaFactor`; the two summability hypotheses are exactly the
flux-energy inputs that justify the average-coefficient bounds. -/
theorem CoarseCaccioppoliSingleCubeCoefficientControls.of_canonical_factor_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C k h uL2Sq : ℝ)
    (u : Vec d → ℝ) (ξ : Vec d → Vec d) (Acirc1 AcircS : ℝ)
    {B U Xi D A1 AS : ℝ}
    (hs0 : 0 < s) (hC : 0 ≤ C)
    (hsum1 :
      Summable (fun n : ℕ =>
        geometricWeight (1 : ℝ) 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hsumS :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hB_nonneg : 0 ≤ B) (hAcirc1_nonneg : 0 ≤ Acirc1)
    (hAcircS_nonneg : 0 ≤ AcircS)
    (hu : cubeLpNorm Q (2 : ℝ≥0∞) u ≤ U)
    (hξ : cubeLpNorm Q ∞ ξ ≤ Xi)
    (hB : B ≤ D) (hAcirc1 : Acirc1 ≤ A1) (hAcircS : AcircS ≤ AS)
    (hconst :
      coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound Q
            (coarseCaccioppoliLambdaFactor Q a (1 : ℝ))
            (coarseCaccioppoliLambdaFactor Q a (1 : ℝ)) *
          coarseCaccioppoliConstantCutoffSizeFactorBound Q U Xi D ≤
        coarseCaccioppoliSingleCubeBoundaryConstantCoeff Q a C k uL2Sq)
    (hcentered :
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
          (d := d) (coarseCaccioppoliLambdaFactor Q a s) Xi A1 C +
        coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound Q s
          (coarseCaccioppoliLambdaFactor Q a s)
          (coarseCaccioppoliLambdaFactor Q a s)
          (coarseCaccioppoliCenteredCutoffCoeffFactorBound Q s Xi D A1 AS C) ≤
          coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C k h) :
    CoarseCaccioppoliSingleCubeCoefficientControls Q a s C k h uL2Sq u ξ
      Acirc1 AcircS B := by
  exact
    CoarseCaccioppoliSingleCubeCoefficientControls.of_separated_factor_bounds
      Q a s C k h uL2Sq u ξ Acirc1 AcircS hs0 hC
      hB_nonneg hAcirc1_nonneg hAcircS_nonneg
      (sqrt_coarseBBlockNorm_le_coarseCaccioppoliLambdaFactor
        Q a (by norm_num : 0 < (1 : ℝ)) hsum1)
      (sqrt_coarseBBlockNorm_le_coarseCaccioppoliLambdaFactor
        Q a hs0 hsumS)
      (by simp [coarseCaccioppoliLambdaFactor])
      (by simp [coarseCaccioppoliLambdaFactor])
      hu hξ hB hAcirc1 hAcircS hconst hcentered

theorem CoarseCaccioppoliSingleCubeCoefficientDomination.of_coefficientControls
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C k h uL2Sq : ℝ)
    (u : Vec d → ℝ) (ξ : Vec d → Vec d) (energy : Vec d → ℝ)
    (Acirc1 AcircS B : ℝ)
    (henergy : 0 ≤ cubeAverage Q energy)
    (hcoeff :
      CoarseCaccioppoliSingleCubeCoefficientControls Q a s C k h uL2Sq u ξ
        Acirc1 AcircS B) :
    CoarseCaccioppoliSingleCubeCoefficientDomination Q a s C k h uL2Sq u ξ energy
      Acirc1 AcircS B := by
  rcases hcoeff with ⟨hconst, hcent⟩
  exact
    CoarseCaccioppoliSingleCubeCoefficientDomination.of_termwise
      Q a s C k h uL2Sq u ξ energy Acirc1 AcircS B
      (coarseCaccioppoliFluxEnergyExactConstantRhs_le_singleCubeBoundaryConstantRhs
        Q a u ξ energy B C k uL2Sq hconst)
      (coarseCaccioppoliFluxEnergyExactCenteredRhs_le_singleCubeBoundaryCenteredRhs
        Q a s ξ energy Acirc1 AcircS B C k h henergy hcent)

/-- Direct full coefficient domination from the separated constant and
centered factor bounds. -/
theorem CoarseCaccioppoliSingleCubeCoefficientDomination.of_factor_bounds {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s C k h uL2Sq : ℝ)
    (u : Vec d → ℝ) (ξ : Vec d → Vec d) (energy : Vec d → ℝ)
    (Acirc1 AcircS : ℝ) {B A G X Y : ℝ}
    (henergy : 0 ≤ cubeAverage Q energy)
    (hA_nonneg : 0 ≤ A) (hB : 0 ≤ B)
    (hconstCoeff : coarseCaccioppoliFluxEnergyExactConstantCoeff Q a ≤ A)
    (hconstCutoff : coarseCaccioppoliConstantCutoffSize Q u ξ B ≤ G)
    (hconst :
      A * G ≤ coarseCaccioppoliSingleCubeBoundaryConstantCoeff Q a C k uL2Sq)
    (havg :
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff Q a ξ Acirc1 C ≤ X)
    (hbesov :
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff Q a s ξ Acirc1 AcircS B C ≤ Y)
    (hcentered :
      X + Y ≤ coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C k h) :
    CoarseCaccioppoliSingleCubeCoefficientDomination Q a s C k h uL2Sq u ξ energy
      Acirc1 AcircS B := by
  exact
    CoarseCaccioppoliSingleCubeCoefficientDomination.of_coefficientControls
      Q a s C k h uL2Sq u ξ energy Acirc1 AcircS B henergy
      (CoarseCaccioppoliSingleCubeCoefficientControls.of_factor_bounds
        Q a s C k h uL2Sq u ξ Acirc1 AcircS hA_nonneg hB
        hconstCoeff hconstCutoff hconst havg hbesov hcentered)

end

end Homogenization
