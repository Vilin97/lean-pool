/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.CutoffSizes

/-! # Exact Rhs -/

namespace Homogenization

noncomputable section

open scoped BigOperators ENNReal

/-- The exact local RHS produced after substituting flux-side energy controls
and the scalar/cutoff control bundle into the split Caccioppoli pairing.

The next coefficient-bookkeeping theorem should prove this quantity is bounded
by the note's single-cube RHS. -/
def coarseCaccioppoliFluxEnergyExactRhs {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s : ℝ) (u : Vec d → ℝ) (ξ : Vec d → Vec d)
    (energy : Vec d → ℝ) (Acirc1 AcircS B C : ℝ) : ℝ :=
  let E : ℝ := Real.sqrt (cubeAverage Q energy)
  let Aavg : ℝ := Real.sqrt (coarseBBlockNorm Q a)
  let Aflux1 : ℝ :=
    (geometricDiscount (1 : ℝ) 1)⁻¹ *
      Real.rpow (LambdaSq Q (1 : ℝ) (.finite 1) a) (1 / 2 : ℝ)
  let AfluxS : ℝ :=
    (geometricDiscount s 1)⁻¹ *
      Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)
  let BgConst : ℝ := coarseCaccioppoliConstantCutoffSize Q u ξ B
  let BgCent : ℝ := coarseCaccioppoliCenteredCutoffSize Q s ξ Acirc1 AcircS E B C
  (d : ℝ) *
      (((3 : ℝ) ^ ((d : ℝ) + 1) *
        (cubeBesovScaleWeight (-1) Q * (Aflux1 * E))) * BgConst) +
    ((d : ℝ) *
      ((Aavg * E) * (cubeLpNorm Q ∞ ξ *
        (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (Acirc1 * E)))) +
      (d : ℝ) *
        ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * (AfluxS * E))) *
          (cubeBesovScaleWeight s Q * BgCent))))

/-- The exact local RHS only sees the energy density through its cube
average. -/
theorem coarseCaccioppoliFluxEnergyExactRhs_congr_cubeAverage {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → ℝ) (ξ : Vec d → Vec d)
    {energy₁ energy₂ : Vec d → ℝ} (Acirc1 AcircS B C : ℝ)
    (havg : cubeAverage Q energy₁ = cubeAverage Q energy₂) :
    coarseCaccioppoliFluxEnergyExactRhs Q a s u ξ energy₁ Acirc1 AcircS B C =
      coarseCaccioppoliFluxEnergyExactRhs Q a s u ξ energy₂ Acirc1 AcircS B C := by
  simp [coarseCaccioppoliFluxEnergyExactRhs, havg]

/-- Constant-piece summand of `coarseCaccioppoliFluxEnergyExactRhs`. -/
def coarseCaccioppoliFluxEnergyExactConstantRhs {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (u : Vec d → ℝ) (ξ : Vec d → Vec d)
    (energy : Vec d → ℝ) (B : ℝ) : ℝ :=
  let E : ℝ := Real.sqrt (cubeAverage Q energy)
  let Aflux1 : ℝ :=
    (geometricDiscount (1 : ℝ) 1)⁻¹ *
      Real.rpow (LambdaSq Q (1 : ℝ) (.finite 1) a) (1 / 2 : ℝ)
  let BgConst : ℝ := coarseCaccioppoliConstantCutoffSize Q u ξ B
  (d : ℝ) *
    (((3 : ℝ) ^ ((d : ℝ) + 1) *
      (cubeBesovScaleWeight (-1) Q * (Aflux1 * E))) * BgConst)

/-- The exact constant-piece RHS only sees the energy density through its cube
average. -/
theorem coarseCaccioppoliFluxEnergyExactConstantRhs_congr_cubeAverage {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → ℝ)
    (ξ : Vec d → Vec d) {energy₁ energy₂ : Vec d → ℝ} (B : ℝ)
    (havg : cubeAverage Q energy₁ = cubeAverage Q energy₂) :
    coarseCaccioppoliFluxEnergyExactConstantRhs Q a u ξ energy₁ B =
      coarseCaccioppoliFluxEnergyExactConstantRhs Q a u ξ energy₂ B := by
  simp [coarseCaccioppoliFluxEnergyExactConstantRhs, havg]

/-- Coefficient in the exact constant-piece RHS, after factoring out the
energy norm and cutoff size. -/
def coarseCaccioppoliFluxEnergyExactConstantCoeff {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) : ℝ :=
  let Aflux1 : ℝ :=
    (geometricDiscount (1 : ℝ) 1)⁻¹ *
      Real.rpow (LambdaSq Q (1 : ℝ) (.finite 1) a) (1 / 2 : ℝ)
  (d : ℝ) *
    ((3 : ℝ) ^ ((d : ℝ) + 1) * (cubeBesovScaleWeight (-1) Q * Aflux1))

theorem coarseCaccioppoliFluxEnergyExactConstantCoeff_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) :
    0 ≤ coarseCaccioppoliFluxEnergyExactConstantCoeff Q a := by
  unfold coarseCaccioppoliFluxEnergyExactConstantCoeff
  have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hdisc_pos : 0 < geometricDiscount (1 : ℝ) 1 :=
    geometricDiscount_pos (by norm_num : 0 < (1 : ℝ) * (1 : ℝ))
  have hLambda_nonneg : 0 ≤ LambdaSq Q (1 : ℝ) (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q (1 : ℝ) a (by norm_num)
  have hAflux_nonneg :
      0 ≤ (geometricDiscount (1 : ℝ) 1)⁻¹ *
        Real.rpow (LambdaSq Q (1 : ℝ) (.finite 1) a) (1 / 2 : ℝ) :=
    mul_nonneg (inv_nonneg.mpr hdisc_pos.le) (Real.rpow_nonneg hLambda_nonneg _)
  refine mul_nonneg hd_nonneg ?_
  exact mul_nonneg
    (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    (mul_nonneg (cubeBesovScaleWeight_nonneg (-1) Q) hAflux_nonneg)

/-- Separated factor-bound expression for the exact constant flux coefficient.
`Aavg` bounds the block-average coefficient and `Aflux1` bounds the finite
`q = 1` flux Besov coefficient. -/
def coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound {d : ℕ}
    (Q : TriadicCube d) (_Aavg Aflux1 : ℝ) : ℝ :=
  (d : ℝ) *
    ((3 : ℝ) ^ ((d : ℝ) + 1) * (cubeBesovScaleWeight (-1) Q * Aflux1))

theorem coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound_nonneg {d : ℕ}
    (Q : TriadicCube d) {Aavg Aflux1 : ℝ}
    (_hAavg : 0 ≤ Aavg) (hAflux1 : 0 ≤ Aflux1) :
    0 ≤ coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound Q Aavg Aflux1 := by
  unfold coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound
  have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  refine mul_nonneg hd_nonneg ?_
  exact mul_nonneg
    (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    (mul_nonneg (cubeBesovScaleWeight_nonneg (-1) Q) hAflux1)

theorem coarseCaccioppoliFluxEnergyExactConstantCoeff_le_factorBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {Aavg Aflux1 : ℝ}
    (_hAavg :
      Real.sqrt (coarseBBlockNorm Q a) ≤ Aavg)
    (hAflux1 :
      (geometricDiscount (1 : ℝ) 1)⁻¹ *
          Real.rpow (LambdaSq Q (1 : ℝ) (.finite 1) a) (1 / 2 : ℝ) ≤ Aflux1) :
    coarseCaccioppoliFluxEnergyExactConstantCoeff Q a ≤
      coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound Q Aavg Aflux1 := by
  unfold coarseCaccioppoliFluxEnergyExactConstantCoeff
    coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound
  have hfluxTerm :
      (3 : ℝ) ^ ((d : ℝ) + 1) *
          (cubeBesovScaleWeight (-1) Q *
            ((geometricDiscount (1 : ℝ) 1)⁻¹ *
              Real.rpow (LambdaSq Q (1 : ℝ) (.finite 1) a) (1 / 2 : ℝ))) ≤
        (3 : ℝ) ^ ((d : ℝ) + 1) *
          (cubeBesovScaleWeight (-1) Q * Aflux1) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hAflux1 (cubeBesovScaleWeight_nonneg (-1) Q))
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  exact mul_le_mul_of_nonneg_left hfluxTerm
    (by exact_mod_cast Nat.zero_le d : 0 ≤ (d : ℝ))

theorem coarseCaccioppoliFluxEnergyExactConstantRhs_eq_coeff_mul {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → ℝ) (ξ : Vec d → Vec d)
    (energy : Vec d → ℝ) (B : ℝ) :
    coarseCaccioppoliFluxEnergyExactConstantRhs Q a u ξ energy B =
      (coarseCaccioppoliFluxEnergyExactConstantCoeff Q a *
        coarseCaccioppoliConstantCutoffSize Q u ξ B) *
        Real.sqrt (cubeAverage Q energy) := by
  unfold coarseCaccioppoliFluxEnergyExactConstantRhs
    coarseCaccioppoliFluxEnergyExactConstantCoeff
  ring

theorem coarseCaccioppoliFluxEnergyExactConstantRhs_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → ℝ) (ξ : Vec d → Vec d)
    (energy : Vec d → ℝ) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ coarseCaccioppoliFluxEnergyExactConstantRhs Q a u ξ energy B := by
  rw [coarseCaccioppoliFluxEnergyExactConstantRhs_eq_coeff_mul]
  exact mul_nonneg
    (mul_nonneg
      (coarseCaccioppoliFluxEnergyExactConstantCoeff_nonneg Q a)
      (coarseCaccioppoliConstantCutoffSize_nonneg Q u ξ hB))
    (Real.sqrt_nonneg _)

/-- Centered-piece summand of `coarseCaccioppoliFluxEnergyExactRhs`. -/
def coarseCaccioppoliFluxEnergyExactCenteredRhs {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s : ℝ) (ξ : Vec d → Vec d)
    (energy : Vec d → ℝ) (Acirc1 AcircS B C : ℝ) : ℝ :=
  let E : ℝ := Real.sqrt (cubeAverage Q energy)
  let Aavg : ℝ := Real.sqrt (coarseBBlockNorm Q a)
  let AfluxS : ℝ :=
    (geometricDiscount s 1)⁻¹ *
      Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)
  let BgCent : ℝ := coarseCaccioppoliCenteredCutoffSize Q s ξ Acirc1 AcircS E B C
  (d : ℝ) *
      ((Aavg * E) * (cubeLpNorm Q ∞ ξ *
        (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (Acirc1 * E)))) +
    (d : ℝ) *
      ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * (AfluxS * E))) *
        (cubeBesovScaleWeight s Q * BgCent)))

/-- The exact centered-piece RHS only sees the energy density through its cube
average. -/
theorem coarseCaccioppoliFluxEnergyExactCenteredRhs_congr_cubeAverage {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (ξ : Vec d → Vec d) {energy₁ energy₂ : Vec d → ℝ}
    (Acirc1 AcircS B C : ℝ)
    (havg : cubeAverage Q energy₁ = cubeAverage Q energy₂) :
    coarseCaccioppoliFluxEnergyExactCenteredRhs Q a s ξ energy₁ Acirc1 AcircS B C =
      coarseCaccioppoliFluxEnergyExactCenteredRhs Q a s ξ energy₂ Acirc1 AcircS B C := by
  simp [coarseCaccioppoliFluxEnergyExactCenteredRhs, havg]

/-- Centered cutoff coefficient after factoring out the energy norm. -/
def coarseCaccioppoliCenteredCutoffCoeff {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (ξ : Vec d → Vec d) (Acirc1 AcircS B C : ℝ) : ℝ :=
  2 * (cubeScaleFactor Q * B *
      (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
        (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Acirc1)) +
    cubeLpNorm Q ∞ ξ *
      (cubeBesovScaleWeight (-s) Q *
        ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          (1 - (3 : ℝ) ^ (-s))⁻¹) * AcircS)))

/-- Coefficient in the exact centered-piece RHS after factoring out
`(sqrt energy)^2`. -/
def coarseCaccioppoliFluxEnergyExactCenteredCoeff {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s : ℝ) (ξ : Vec d → Vec d) (Acirc1 AcircS B C : ℝ) :
    ℝ :=
  let Aavg : ℝ := Real.sqrt (coarseBBlockNorm Q a)
  let AfluxS : ℝ :=
    (geometricDiscount s 1)⁻¹ *
      Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)
  let BgCentCoeff : ℝ :=
    coarseCaccioppoliCenteredCutoffCoeff Q s ξ Acirc1 AcircS B C
  (d : ℝ) *
      (Aavg * (cubeLpNorm Q ∞ ξ *
        (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Acirc1))) +
    (d : ℝ) *
      ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * AfluxS)) *
        (cubeBesovScaleWeight s Q * BgCentCoeff)))

/-- Average-flux part of the exact centered coefficient. -/
def coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (ξ : Vec d → Vec d) (Acirc1 C : ℝ) : ℝ :=
  let Aavg : ℝ := Real.sqrt (coarseBBlockNorm Q a)
  (d : ℝ) *
    (Aavg * (cubeLpNorm Q ∞ ξ *
      (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Acirc1)))

/-- Besov/cutoff-product part of the exact centered coefficient. -/
def coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s : ℝ) (ξ : Vec d → Vec d) (Acirc1 AcircS B C : ℝ) :
    ℝ :=
  let AfluxS : ℝ :=
    (geometricDiscount s 1)⁻¹ *
      Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)
  let BgCentCoeff : ℝ :=
    coarseCaccioppoliCenteredCutoffCoeff Q s ξ Acirc1 AcircS B C
  (d : ℝ) *
    ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * AfluxS)) *
      (cubeBesovScaleWeight s Q * BgCentCoeff)))

theorem coarseCaccioppoliFluxEnergyExactCenteredCoeff_eq_average_add_besov {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (ξ : Vec d → Vec d) (Acirc1 AcircS B C : ℝ) :
    coarseCaccioppoliFluxEnergyExactCenteredCoeff Q a s ξ Acirc1 AcircS B C =
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff Q a ξ Acirc1 C +
        coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff Q a s ξ Acirc1 AcircS B C := by
  rfl

theorem coarseCaccioppoliCenteredCutoffCoeff_nonneg {d : ℕ} (Q : TriadicCube d)
    {s : ℝ} (ξ : Vec d → Vec d) {Acirc1 AcircS B C : ℝ}
    (hs : 0 < s) (hAcirc1 : 0 ≤ Acirc1) (hAcircS : 0 ≤ AcircS)
    (hB : 0 ≤ B) (hC : 0 ≤ C) :
    0 ≤ coarseCaccioppoliCenteredCutoffCoeff Q s ξ Acirc1 AcircS B C := by
  unfold coarseCaccioppoliCenteredCutoffCoeff
  have hnote1 :
      0 ≤ ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) := by
    exact mul_nonneg (mul_nonneg (by positivity) hC) (Real.rpow_nonneg (by positivity) _)
  have hterm1 :
      0 ≤ cubeScaleFactor Q * B *
        (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Acirc1)) := by
    refine mul_nonneg (mul_nonneg (cubeScaleFactor_nonneg Q) hB) ?_
    refine mul_nonneg (Real.sqrt_nonneg _) ?_
    exact mul_nonneg hnote1 hAcirc1
  have hnoteS :
      0 ≤ (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          (1 - (3 : ℝ) ^ (-s))⁻¹) := by
    have hr_lt_one : (3 : ℝ) ^ (-s) < 1 := by
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    exact mul_nonneg hnote1 (inv_nonneg.mpr (sub_nonneg.mpr hr_lt_one.le))
  have hterm2 :
      0 ≤ cubeLpNorm Q ∞ ξ *
        (cubeBesovScaleWeight (-s) Q *
          ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            (1 - (3 : ℝ) ^ (-s))⁻¹) * AcircS)) := by
    refine mul_nonneg (cubeLpNorm_nonneg Q ∞ ξ) ?_
    refine mul_nonneg (cubeBesovScaleWeight_nonneg (-s) Q) ?_
    exact mul_nonneg hnoteS hAcircS
  exact mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (add_nonneg hterm1 hterm2)

/-- Separated factor-bound expression for the centered cutoff coefficient.
`Xi` bounds `‖ξ‖_{L∞}`, `D` bounds `‖∇ξ‖_{L∞}`, and `A1`, `AS` bound the
two projected Poincare/Besov scalar constants. -/
def coarseCaccioppoliCenteredCutoffCoeffFactorBound {d : ℕ} (Q : TriadicCube d)
    (s Xi D A1 AS C : ℝ) : ℝ :=
  2 * (cubeScaleFactor Q * D *
      (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
        (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * A1)) +
    Xi *
      (cubeBesovScaleWeight (-s) Q *
        ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          (1 - (3 : ℝ) ^ (-s))⁻¹) * AS)))

private theorem cubeBesovScaleWeight_mul_neg_factor {d : ℕ} (Q : TriadicCube d)
    (s Xi Z : ℝ) :
    cubeBesovScaleWeight s Q * (Xi * (cubeBesovScaleWeight (-s) Q * Z)) =
      Xi * Z := by
  have hcancel : cubeBesovScaleWeight s Q * cubeBesovScaleWeight (-s) Q = 1 := by
    rw [mul_comm]
    exact cubeBesovScaleWeight_neg_mul_cubeBesovScaleWeight Q s
  calc
    cubeBesovScaleWeight s Q * (Xi * (cubeBesovScaleWeight (-s) Q * Z))
        = Xi * ((cubeBesovScaleWeight s Q * cubeBesovScaleWeight (-s) Q) * Z) := by
            ring
    _ = Xi * Z := by
          rw [hcancel]
          ring

/-- Multiplying the centered cutoff factor by the descendant Besov weight
cancels the `cubeBesovScaleWeight (-s)` in the `A_s^\circ` term. -/
theorem cubeBesovScaleWeight_mul_centeredCutoffCoeffFactorBound_eq {d : ℕ}
    (Q : TriadicCube d) (s Xi D A1 AS C : ℝ) :
    cubeBesovScaleWeight s Q *
        coarseCaccioppoliCenteredCutoffCoeffFactorBound Q s Xi D A1 AS C =
      2 * (cubeBesovScaleWeight s Q * (cubeScaleFactor Q * D *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * A1))) +
        Xi *
          ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            (1 - (3 : ℝ) ^ (-s))⁻¹) * AS)) := by
  let A : ℝ := cubeScaleFactor Q * D *
      (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
        (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * A1))
  let Z : ℝ :=
    (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      (1 - (3 : ℝ) ^ (-s))⁻¹) * AS
  change
    cubeBesovScaleWeight s Q * (2 * (A + Xi * (cubeBesovScaleWeight (-s) Q * Z))) =
      2 * (cubeBesovScaleWeight s Q * A + Xi * Z)
  calc
    cubeBesovScaleWeight s Q * (2 * (A + Xi * (cubeBesovScaleWeight (-s) Q * Z)))
        = 2 * (cubeBesovScaleWeight s Q * A +
            cubeBesovScaleWeight s Q * (Xi * (cubeBesovScaleWeight (-s) Q * Z))) := by
            ring
    _ = 2 * (cubeBesovScaleWeight s Q * A + Xi * Z) := by
          rw [cubeBesovScaleWeight_mul_neg_factor]

theorem coarseCaccioppoliCenteredCutoffCoeffFactorBound_nonneg {d : ℕ}
    (Q : TriadicCube d) {s Xi D A1 AS C : ℝ}
    (hs : 0 < s) (hXi : 0 ≤ Xi) (hD : 0 ≤ D)
    (hA1 : 0 ≤ A1) (hAS : 0 ≤ AS) (hC : 0 ≤ C) :
    0 ≤ coarseCaccioppoliCenteredCutoffCoeffFactorBound Q s Xi D A1 AS C := by
  unfold coarseCaccioppoliCenteredCutoffCoeffFactorBound
  have hnote1 :
      0 ≤ ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) := by
    exact mul_nonneg (mul_nonneg (by positivity) hC) (Real.rpow_nonneg (by positivity) _)
  have hterm1 :
      0 ≤ cubeScaleFactor Q * D *
        (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * A1)) := by
    refine mul_nonneg (mul_nonneg (cubeScaleFactor_nonneg Q) hD) ?_
    exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hnote1 hA1)
  have hnoteS :
      0 ≤ (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          (1 - (3 : ℝ) ^ (-s))⁻¹) := by
    have hr_lt_one : (3 : ℝ) ^ (-s) < 1 := by
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    exact mul_nonneg hnote1 (inv_nonneg.mpr (sub_nonneg.mpr hr_lt_one.le))
  have hterm2 :
      0 ≤ Xi *
        (cubeBesovScaleWeight (-s) Q *
          ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            (1 - (3 : ℝ) ^ (-s))⁻¹) * AS)) := by
    refine mul_nonneg hXi ?_
    exact mul_nonneg (cubeBesovScaleWeight_nonneg (-s) Q) (mul_nonneg hnoteS hAS)
  exact mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (add_nonneg hterm1 hterm2)

theorem coarseCaccioppoliCenteredCutoffCoeff_le_factorBound {d : ℕ}
    (Q : TriadicCube d) {s : ℝ} (ξ : Vec d → Vec d)
    {Acirc1 AcircS B C Xi D A1 AS : ℝ}
    (hs : 0 < s)
    (hAcirc1_nonneg : 0 ≤ Acirc1) (hAcircS_nonneg : 0 ≤ AcircS)
    (hXi_nonneg : 0 ≤ Xi) (hD_nonneg : 0 ≤ D) (hC : 0 ≤ C)
    (hξ : cubeLpNorm Q ∞ ξ ≤ Xi) (hB : B ≤ D)
    (hAcirc1 : Acirc1 ≤ A1) (hAcircS : AcircS ≤ AS) :
    coarseCaccioppoliCenteredCutoffCoeff Q s ξ Acirc1 AcircS B C ≤
      coarseCaccioppoliCenteredCutoffCoeffFactorBound Q s Xi D A1 AS C := by
  unfold coarseCaccioppoliCenteredCutoffCoeff
    coarseCaccioppoliCenteredCutoffCoeffFactorBound
  have hnote1 :
      0 ≤ ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) := by
    exact mul_nonneg (mul_nonneg (by positivity) hC) (Real.rpow_nonneg (by positivity) _)
  have hnote1Acirc :
      ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Acirc1 ≤
        ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * A1 := by
    exact mul_le_mul_of_nonneg_left hAcirc1 hnote1
  have hrest1 :
      Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Acirc1) ≤
        Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * A1) := by
    exact mul_le_mul_of_nonneg_left hnote1Acirc (Real.sqrt_nonneg _)
  have hrest1_nonneg :
      0 ≤ Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
        (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Acirc1) := by
    exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hnote1 hAcirc1_nonneg)
  have hleft1 :
      cubeScaleFactor Q * B ≤ cubeScaleFactor Q * D := by
    exact mul_le_mul_of_nonneg_left hB (cubeScaleFactor_nonneg Q)
  have hleft1_bound_nonneg : 0 ≤ cubeScaleFactor Q * D := by
    exact mul_nonneg (cubeScaleFactor_nonneg Q) hD_nonneg
  have hterm1 :
      cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Acirc1)) ≤
        cubeScaleFactor Q * D *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * A1)) := by
    exact mul_le_mul hleft1 hrest1 hrest1_nonneg hleft1_bound_nonneg
  have hr_lt_one : (3 : ℝ) ^ (-s) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hnoteS :
      0 ≤ (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          (1 - (3 : ℝ) ^ (-s))⁻¹) := by
    exact mul_nonneg hnote1 (inv_nonneg.mpr (sub_nonneg.mpr hr_lt_one.le))
  have hnoteSAcirc :
      (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          (1 - (3 : ℝ) ^ (-s))⁻¹) * AcircS ≤
        (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          (1 - (3 : ℝ) ^ (-s))⁻¹) * AS := by
    exact mul_le_mul_of_nonneg_left hAcircS hnoteS
  have hrest2 :
      cubeBesovScaleWeight (-s) Q *
          ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            (1 - (3 : ℝ) ^ (-s))⁻¹) * AcircS) ≤
        cubeBesovScaleWeight (-s) Q *
          ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            (1 - (3 : ℝ) ^ (-s))⁻¹) * AS) := by
    exact mul_le_mul_of_nonneg_left hnoteSAcirc (cubeBesovScaleWeight_nonneg (-s) Q)
  have hrest2_nonneg :
      0 ≤ cubeBesovScaleWeight (-s) Q *
        ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          (1 - (3 : ℝ) ^ (-s))⁻¹) * AcircS) := by
    exact mul_nonneg (cubeBesovScaleWeight_nonneg (-s) Q)
      (mul_nonneg hnoteS hAcircS_nonneg)
  have hterm2 :
      cubeLpNorm Q ∞ ξ *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) * AcircS)) ≤
        Xi *
          (cubeBesovScaleWeight (-s) Q *
            ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-s))⁻¹) * AS)) := by
    exact mul_le_mul hξ hrest2 hrest2_nonneg hXi_nonneg
  exact mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2)
    (by norm_num : 0 ≤ (2 : ℝ))

theorem coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (ξ : Vec d → Vec d)
    {Acirc1 C : ℝ} (hAcirc1 : 0 ≤ Acirc1) (hC : 0 ≤ C) :
    0 ≤ coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff Q a ξ Acirc1 C := by
  unfold coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff
  have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hnote1 :
      0 ≤ ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) := by
    exact mul_nonneg (mul_nonneg (by positivity) hC) (Real.rpow_nonneg (by positivity) _)
  refine mul_nonneg hd_nonneg ?_
  refine mul_nonneg (Real.sqrt_nonneg _) ?_
  exact mul_nonneg (cubeLpNorm_nonneg Q ∞ ξ) (mul_nonneg hnote1 hAcirc1)

/-- Separated factor-bound expression for the average-flux part of the
centered coefficient. -/
def coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound {d : ℕ}
    (Aavg Xi A1 C : ℝ) : ℝ :=
  (d : ℝ) *
    (Aavg * (Xi *
      (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * A1)))

theorem coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound_nonneg
    {d : ℕ} {Aavg Xi A1 C : ℝ}
    (hAavg : 0 ≤ Aavg) (hXi : 0 ≤ Xi) (hA1 : 0 ≤ A1) (hC : 0 ≤ C) :
    0 ≤ coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
      (d := d) Aavg Xi A1 C := by
  unfold coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
  have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hnote1 :
      0 ≤ ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) := by
    exact mul_nonneg (mul_nonneg (by positivity) hC) (Real.rpow_nonneg (by positivity) _)
  exact mul_nonneg hd_nonneg
    (mul_nonneg hAavg (mul_nonneg hXi (mul_nonneg hnote1 hA1)))

theorem coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff_le_factorBound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (ξ : Vec d → Vec d)
    {Acirc1 C Aavg Xi A1 : ℝ}
    (hAavg_nonneg : 0 ≤ Aavg) (hXi_nonneg : 0 ≤ Xi)
    (hAcirc1_nonneg : 0 ≤ Acirc1) (hC : 0 ≤ C)
    (hAavg : Real.sqrt (coarseBBlockNorm Q a) ≤ Aavg)
    (hξ : cubeLpNorm Q ∞ ξ ≤ Xi) (hAcirc1 : Acirc1 ≤ A1) :
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff Q a ξ Acirc1 C ≤
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
        (d := d) Aavg Xi A1 C := by
  unfold coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
  have hnote1 :
      0 ≤ ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) := by
    exact mul_nonneg (mul_nonneg (by positivity) hC) (Real.rpow_nonneg (by positivity) _)
  have hnote1Acirc :
      ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Acirc1 ≤
        ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * A1 := by
    exact mul_le_mul_of_nonneg_left hAcirc1 hnote1
  have hinner :
      cubeLpNorm Q ∞ ξ *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Acirc1) ≤
        Xi * (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * A1) := by
    exact mul_le_mul hξ hnote1Acirc
      (mul_nonneg hnote1 hAcirc1_nonneg) hXi_nonneg
  have hinner_nonneg :
      0 ≤ cubeLpNorm Q ∞ ξ *
        (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Acirc1) := by
    exact mul_nonneg (cubeLpNorm_nonneg Q ∞ ξ) (mul_nonneg hnote1 hAcirc1_nonneg)
  have hmain :
      Real.sqrt (coarseBBlockNorm Q a) *
          (cubeLpNorm Q ∞ ξ *
            (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * Acirc1)) ≤
        Aavg *
          (Xi * (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * A1)) := by
    exact mul_le_mul hAavg hinner hinner_nonneg hAavg_nonneg
  exact mul_le_mul_of_nonneg_left hmain
    (by exact_mod_cast Nat.zero_le d : 0 ≤ (d : ℝ))

theorem coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    (ξ : Vec d → Vec d) {Acirc1 AcircS B C : ℝ}
    (hs : 0 < s) (hAcirc1 : 0 ≤ Acirc1) (hAcircS : 0 ≤ AcircS)
    (hB : 0 ≤ B) (hC : 0 ≤ C) :
    0 ≤ coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff Q a s ξ Acirc1 AcircS B C := by
  unfold coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff
  have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hdisc_pos : 0 < geometricDiscount s 1 := by
    exact geometricDiscount_pos (by simpa using hs)
  have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le
  have hAflux_nonneg :
      0 ≤ (geometricDiscount s 1)⁻¹ *
        Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) :=
    mul_nonneg (inv_nonneg.mpr hdisc_pos.le) (Real.rpow_nonneg hLambda_nonneg _)
  have hcoeff_nonneg :
      0 ≤ (3 : ℝ) ^ ((d : ℝ) + s) *
            (cubeBesovScaleWeight (-s) Q *
              ((geometricDiscount s 1)⁻¹ *
                Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ))) := by
    exact mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      (mul_nonneg (cubeBesovScaleWeight_nonneg (-s) Q) hAflux_nonneg)
  refine mul_nonneg hd_nonneg ?_
  refine mul_nonneg hcoeff_nonneg ?_
  exact mul_nonneg (cubeBesovScaleWeight_nonneg s Q)
    (coarseCaccioppoliCenteredCutoffCoeff_nonneg Q ξ hs hAcirc1 hAcircS hB hC)

/-- Separated factor-bound expression for the Besov/cutoff-product part of
the centered coefficient. -/
def coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound {d : ℕ}
    (Q : TriadicCube d) (s _Aavg AfluxS BgCent : ℝ) : ℝ :=
  (d : ℝ) *
    ((((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * AfluxS)) *
      (cubeBesovScaleWeight s Q * BgCent)))

theorem coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound_nonneg
    {d : ℕ} (Q : TriadicCube d) {s Aavg AfluxS BgCent : ℝ}
    (_hAavg : 0 ≤ Aavg) (hAfluxS : 0 ≤ AfluxS) (hBgCent : 0 ≤ BgCent) :
    0 ≤ coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound
      Q s Aavg AfluxS BgCent := by
  unfold coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound
  have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hcoeff_nonneg :
      0 ≤ (3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * AfluxS) := by
    exact mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      (mul_nonneg (cubeBesovScaleWeight_nonneg (-s) Q) hAfluxS)
  exact mul_nonneg hd_nonneg
    (mul_nonneg hcoeff_nonneg
      (mul_nonneg (cubeBesovScaleWeight_nonneg s Q) hBgCent))

theorem coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff_le_factorBound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (ξ : Vec d → Vec d) {Acirc1 AcircS B C Aavg AfluxS BgCent : ℝ}
    (_hAavg_nonneg : 0 ≤ Aavg) (hAfluxS_nonneg : 0 ≤ AfluxS)
    (hBgCentCoeff_nonneg :
      0 ≤ coarseCaccioppoliCenteredCutoffCoeff Q s ξ Acirc1 AcircS B C)
    (_hAavg : Real.sqrt (coarseBBlockNorm Q a) ≤ Aavg)
    (hAfluxS :
      (geometricDiscount s 1)⁻¹ *
          Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) ≤ AfluxS)
    (hBgCent :
      coarseCaccioppoliCenteredCutoffCoeff Q s ξ Acirc1 AcircS B C ≤ BgCent) :
    coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff Q a s ξ Acirc1 AcircS B C ≤
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound
        Q s Aavg AfluxS BgCent := by
  unfold coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff
    coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound
  have hfluxTerm :
      (3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q *
            ((geometricDiscount s 1)⁻¹ *
              Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ))) ≤
        (3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * AfluxS) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hAfluxS (cubeBesovScaleWeight_nonneg (-s) Q))
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have hcoeff :
      (3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q *
            ((geometricDiscount s 1)⁻¹ *
              Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ))) ≤
      (3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * AfluxS) := hfluxTerm
  have hcoeff_bound_nonneg :
      0 ≤ (3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * AfluxS) := by
    exact mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      (mul_nonneg (cubeBesovScaleWeight_nonneg (-s) Q) hAfluxS_nonneg)
  have htail :
      cubeBesovScaleWeight s Q *
          coarseCaccioppoliCenteredCutoffCoeff Q s ξ Acirc1 AcircS B C ≤
        cubeBesovScaleWeight s Q * BgCent := by
    exact mul_le_mul_of_nonneg_left hBgCent (cubeBesovScaleWeight_nonneg s Q)
  have htail_nonneg :
      0 ≤ cubeBesovScaleWeight s Q *
        coarseCaccioppoliCenteredCutoffCoeff Q s ξ Acirc1 AcircS B C := by
    exact mul_nonneg (cubeBesovScaleWeight_nonneg s Q) hBgCentCoeff_nonneg
  have hmain :
      ((3 : ℝ) ^ ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q *
            ((geometricDiscount s 1)⁻¹ *
              Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)))) *
          (cubeBesovScaleWeight s Q *
            coarseCaccioppoliCenteredCutoffCoeff Q s ξ Acirc1 AcircS B C) ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) * (cubeBesovScaleWeight (-s) Q * AfluxS)) *
          (cubeBesovScaleWeight s Q * BgCent) := by
    exact mul_le_mul hcoeff htail htail_nonneg hcoeff_bound_nonneg
  exact mul_le_mul_of_nonneg_left hmain
    (by exact_mod_cast Nat.zero_le d : 0 ≤ (d : ℝ))

theorem coarseCaccioppoliFluxEnergyExactCenteredCoeff_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    (ξ : Vec d → Vec d) {Acirc1 AcircS B C : ℝ}
    (hs : 0 < s) (hAcirc1 : 0 ≤ Acirc1) (hAcircS : 0 ≤ AcircS)
    (hB : 0 ≤ B) (hC : 0 ≤ C) :
    0 ≤ coarseCaccioppoliFluxEnergyExactCenteredCoeff Q a s ξ Acirc1 AcircS B C := by
  rw [coarseCaccioppoliFluxEnergyExactCenteredCoeff_eq_average_add_besov]
  exact add_nonneg
    (coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff_nonneg Q a ξ hAcirc1 hC)
    (coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff_nonneg
      Q a ξ hs hAcirc1 hAcircS hB hC)

/-- The exact centered coefficient is monotone in the two canonical gradient
slots.  This is the local-to-parent `A^\circ` comparison used in the
small-cube Caccioppoli proof. -/
theorem coarseCaccioppoliFluxEnergyExactCenteredCoeff_mono_Acirc {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {s : ℝ} (ξ : Vec d → Vec d)
    {Acirc1 AcircS A1 AS B C : ℝ}
    (hs : 0 < s) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hAcirc1_nonneg : 0 ≤ Acirc1) (hAcircS_nonneg : 0 ≤ AcircS)
    (hA1 : Acirc1 ≤ A1) (hAS : AcircS ≤ AS) :
    coarseCaccioppoliFluxEnergyExactCenteredCoeff Q a s ξ Acirc1 AcircS B C ≤
      coarseCaccioppoliFluxEnergyExactCenteredCoeff Q a s ξ A1 AS B C := by
  have hAavg_nonneg : 0 ≤ Real.sqrt (coarseBBlockNorm Q a) := Real.sqrt_nonneg _
  have hXi_nonneg : 0 ≤ cubeLpNorm Q ∞ ξ := cubeLpNorm_nonneg Q ∞ ξ
  have hAflux_nonneg :
      0 ≤ (geometricDiscount s 1)⁻¹ *
        Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by
    exact mul_nonneg
      (inv_nonneg.mpr (geometricDiscount_pos (by simpa using hs)).le)
      (Real.rpow_nonneg (multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le) _)
  have hcutoff_le :
      coarseCaccioppoliCenteredCutoffCoeff Q s ξ Acirc1 AcircS B C ≤
        coarseCaccioppoliCenteredCutoffCoeff Q s ξ A1 AS B C := by
    simpa [coarseCaccioppoliCenteredCutoffCoeff,
      coarseCaccioppoliCenteredCutoffCoeffFactorBound] using
      (coarseCaccioppoliCenteredCutoffCoeff_le_factorBound
        Q ξ hs hAcirc1_nonneg hAcircS_nonneg hXi_nonneg hB hC
        (le_rfl : cubeLpNorm Q ∞ ξ ≤ cubeLpNorm Q ∞ ξ)
        (le_rfl : B ≤ B) hA1 hAS)
  have hcutoff_nonneg :
      0 ≤ coarseCaccioppoliCenteredCutoffCoeff Q s ξ Acirc1 AcircS B C :=
    coarseCaccioppoliCenteredCutoffCoeff_nonneg
      Q ξ hs hAcirc1_nonneg hAcircS_nonneg hB hC
  have havg_le :
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff Q a ξ Acirc1 C ≤
        coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff Q a ξ A1 C := by
    simpa [coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound] using!
      (coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff_le_factorBound
        Q a ξ hAavg_nonneg hXi_nonneg hAcirc1_nonneg hC
        (le_rfl : Real.sqrt (coarseBBlockNorm Q a) ≤ Real.sqrt (coarseBBlockNorm Q a))
        (le_rfl : cubeLpNorm Q ∞ ξ ≤ cubeLpNorm Q ∞ ξ) hA1)
  have hbesov_le :
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff Q a s ξ Acirc1 AcircS B C ≤
        coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff Q a s ξ A1 AS B C := by
    simpa [coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff,
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound] using
      (coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff_le_factorBound
        Q a s ξ hAavg_nonneg hAflux_nonneg hcutoff_nonneg
        (le_rfl : Real.sqrt (coarseBBlockNorm Q a) ≤ Real.sqrt (coarseBBlockNorm Q a))
        (le_rfl :
          (geometricDiscount s 1)⁻¹ *
              Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) ≤
            (geometricDiscount s 1)⁻¹ *
              Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ))
        hcutoff_le)
  rw [coarseCaccioppoliFluxEnergyExactCenteredCoeff_eq_average_add_besov,
    coarseCaccioppoliFluxEnergyExactCenteredCoeff_eq_average_add_besov]
  exact add_le_add havg_le hbesov_le

theorem coarseCaccioppoliFluxEnergyExactCenteredRhs_eq_coeff_mul_sqrt_sq {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (ξ : Vec d → Vec d) (energy : Vec d → ℝ) (Acirc1 AcircS B C : ℝ) :
    coarseCaccioppoliFluxEnergyExactCenteredRhs Q a s ξ energy Acirc1 AcircS B C =
      coarseCaccioppoliFluxEnergyExactCenteredCoeff Q a s ξ Acirc1 AcircS B C *
        (Real.sqrt (cubeAverage Q energy) * Real.sqrt (cubeAverage Q energy)) := by
  unfold coarseCaccioppoliFluxEnergyExactCenteredRhs
    coarseCaccioppoliFluxEnergyExactCenteredCoeff
    coarseCaccioppoliCenteredCutoffSize
    coarseCaccioppoliCenteredCutoffCoeff
  ring

theorem coarseCaccioppoliFluxEnergyExactCenteredRhs_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    (ξ : Vec d → Vec d) (energy : Vec d → ℝ)
    {Acirc1 AcircS B C : ℝ}
    (hs : 0 < s) (hAcirc1 : 0 ≤ Acirc1) (hAcircS : 0 ≤ AcircS)
    (hB : 0 ≤ B) (hC : 0 ≤ C) :
    0 ≤ coarseCaccioppoliFluxEnergyExactCenteredRhs
      Q a s ξ energy Acirc1 AcircS B C := by
  rw [coarseCaccioppoliFluxEnergyExactCenteredRhs_eq_coeff_mul_sqrt_sq]
  exact mul_nonneg
    (coarseCaccioppoliFluxEnergyExactCenteredCoeff_nonneg
      Q a ξ hs hAcirc1 hAcircS hB hC)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem coarseCaccioppoliFluxEnergyExactRhs_eq_constant_add_centered {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → ℝ) (ξ : Vec d → Vec d) (energy : Vec d → ℝ)
    (Acirc1 AcircS B C : ℝ) :
    coarseCaccioppoliFluxEnergyExactRhs Q a s u ξ energy Acirc1 AcircS B C =
      coarseCaccioppoliFluxEnergyExactConstantRhs Q a u ξ energy B +
        coarseCaccioppoliFluxEnergyExactCenteredRhs Q a s ξ energy Acirc1 AcircS B C := by
  rfl

theorem coarseCaccioppoliFluxEnergyExactRhs_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    (u : Vec d → ℝ) (ξ : Vec d → Vec d) (energy : Vec d → ℝ)
    {Acirc1 AcircS B C : ℝ}
    (hs : 0 < s) (hAcirc1 : 0 ≤ Acirc1) (hAcircS : 0 ≤ AcircS)
    (hB : 0 ≤ B) (hC : 0 ≤ C) :
    0 ≤ coarseCaccioppoliFluxEnergyExactRhs Q a s u ξ energy Acirc1 AcircS B C := by
  rw [coarseCaccioppoliFluxEnergyExactRhs_eq_constant_add_centered]
  exact add_nonneg
    (coarseCaccioppoliFluxEnergyExactConstantRhs_nonneg Q a u ξ energy hB)
    (coarseCaccioppoliFluxEnergyExactCenteredRhs_nonneg
      Q a ξ energy hs hAcirc1 hAcircS hB hC)

end

end Homogenization
