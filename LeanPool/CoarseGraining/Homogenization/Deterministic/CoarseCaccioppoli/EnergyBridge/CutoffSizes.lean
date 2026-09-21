/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.Flux
import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.Ellipticity.Descendants
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.Geometry
import LeanPool.CoarseGraining.Homogenization.Besov.Poincare.HarmonicGradient.Definitions

/-! # Cutoff Sizes -/

namespace Homogenization

noncomputable section

open scoped BigOperators ENNReal

/-- Exact cutoff size controlling the constant piece `(u)_Q ξ`.

The local split theorem only needs this quantity through an upper bound, but
keeping the exact expression here gives the next coefficient-bookkeeping layer
a stable target to dominate by the note's radius/height constants. -/
def coarseCaccioppoliConstantCutoffSize {d : ℕ} (Q : TriadicCube d)
    (u : Vec d → ℝ) (ξ : Vec d → Vec d) (B : ℝ) : ℝ :=
  cubeLpNorm Q (2 : ℝ≥0∞) u *
    (B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ ξ)

/-- Exact cutoff size controlling the centered piece `(u-(u)_Q) ξ` after the
cutoff-product theorem and projected mean-zero Poincare estimate have supplied
the two scalar `circ` bounds. -/
def coarseCaccioppoliCenteredCutoffSize {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (ξ : Vec d → Vec d) (Acirc1 AcircS E B C : ℝ) : ℝ :=
  2 * (cubeScaleFactor Q * B *
      (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
        (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (Acirc1 * E))) +
    cubeLpNorm Q ∞ ξ *
      (cubeBesovScaleWeight (-s) Q *
        ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          (1 - (3 : ℝ) ^ (-s))⁻¹) * (AcircS * E))))

theorem coarseCaccioppoliConstantCutoffSize_nonneg {d : ℕ} (Q : TriadicCube d)
    (u : Vec d → ℝ) (ξ : Vec d → Vec d) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ coarseCaccioppoliConstantCutoffSize Q u ξ B := by
  unfold coarseCaccioppoliConstantCutoffSize
  refine mul_nonneg (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) u) ?_
  exact add_nonneg hB
    (mul_nonneg (cubeBesovScaleWeight_nonneg 1 Q) (cubeLpNorm_nonneg Q ∞ ξ))

theorem coarseCaccioppoliConstantCutoffSize_pos_of_cubeLpNorm_pos_of_B_pos {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → ℝ) (ξ : Vec d → Vec d) {B : ℝ}
    (hu : 0 < cubeLpNorm Q (2 : ℝ≥0∞) u) (hB : 0 < B) :
    0 < coarseCaccioppoliConstantCutoffSize Q u ξ B := by
  unfold coarseCaccioppoliConstantCutoffSize
  have htail :
      0 ≤ cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ ξ :=
    mul_nonneg (cubeBesovScaleWeight_nonneg 1 Q) (cubeLpNorm_nonneg Q ∞ ξ)
  exact mul_pos hu (add_pos_of_pos_of_nonneg hB htail)

/-- Separated upper bound for the constant cutoff size.  In applications `U`
is a note-facing bound for `‖u‖_{L^2(Q)}` and `Xi`, `D` bound the cutoff and
its derivative. -/
def coarseCaccioppoliConstantCutoffSizeFactorBound {d : ℕ} (Q : TriadicCube d)
    (U Xi D : ℝ) : ℝ :=
  U * (D + cubeBesovScaleWeight 1 Q * Xi)

theorem coarseCaccioppoliConstantCutoffSizeFactorBound_nonneg {d : ℕ}
    (Q : TriadicCube d) {U Xi D : ℝ}
    (hU : 0 ≤ U) (hXi : 0 ≤ Xi) (hD : 0 ≤ D) :
    0 ≤ coarseCaccioppoliConstantCutoffSizeFactorBound Q U Xi D := by
  unfold coarseCaccioppoliConstantCutoffSizeFactorBound
  exact mul_nonneg hU
    (add_nonneg hD (mul_nonneg (cubeBesovScaleWeight_nonneg 1 Q) hXi))

theorem coarseCaccioppoliConstantCutoffSize_le_factorBound {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → ℝ) (ξ : Vec d → Vec d) {B U Xi D : ℝ}
    (hU_nonneg : 0 ≤ U) (hB_nonneg : 0 ≤ B)
    (hu : cubeLpNorm Q (2 : ℝ≥0∞) u ≤ U)
    (hξ : cubeLpNorm Q ∞ ξ ≤ Xi) (hB : B ≤ D) :
    coarseCaccioppoliConstantCutoffSize Q u ξ B ≤
      coarseCaccioppoliConstantCutoffSizeFactorBound Q U Xi D := by
  unfold coarseCaccioppoliConstantCutoffSize
    coarseCaccioppoliConstantCutoffSizeFactorBound
  have hinner :
      B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ ξ ≤
        D + cubeBesovScaleWeight 1 Q * Xi := by
    exact add_le_add hB
      (mul_le_mul_of_nonneg_left hξ (cubeBesovScaleWeight_nonneg 1 Q))
  have hinner_nonneg :
      0 ≤ B + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ ξ := by
    exact add_nonneg hB_nonneg
      (mul_nonneg (cubeBesovScaleWeight_nonneg 1 Q) (cubeLpNorm_nonneg Q ∞ ξ))
  exact mul_le_mul hu hinner hinner_nonneg hU_nonneg

theorem coarseCaccioppoliCenteredCutoffSize_nonneg {d : ℕ} (Q : TriadicCube d)
    {s : ℝ} (ξ : Vec d → Vec d) {Acirc1 AcircS E B C : ℝ}
    (hs : 0 < s) (hAcirc1 : 0 ≤ Acirc1) (hAcircS : 0 ≤ AcircS)
    (hE : 0 ≤ E) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    0 ≤ coarseCaccioppoliCenteredCutoffSize Q s ξ Acirc1 AcircS E B C := by
  unfold coarseCaccioppoliCenteredCutoffSize
  have hnote1 :
      0 ≤ ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) := by
    exact mul_nonneg (mul_nonneg (by positivity) hC) (Real.rpow_nonneg (by positivity) _)
  have hterm1 :
      0 ≤ cubeScaleFactor Q * B *
        (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (Acirc1 * E))) := by
    refine mul_nonneg (mul_nonneg (cubeScaleFactor_nonneg Q) hB) ?_
    refine mul_nonneg (Real.sqrt_nonneg _) ?_
    exact mul_nonneg hnote1 (mul_nonneg hAcirc1 hE)
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
            (1 - (3 : ℝ) ^ (-s))⁻¹) * (AcircS * E))) := by
    refine mul_nonneg (cubeLpNorm_nonneg Q ∞ ξ) ?_
    refine mul_nonneg (cubeBesovScaleWeight_nonneg (-s) Q) ?_
    exact mul_nonneg hnoteS (mul_nonneg hAcircS hE)
  exact mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (add_nonneg hterm1 hterm2)

theorem coarseCaccioppoliCenteredCutoffSize_pos_of_first_branch {d : ℕ}
    (Q : TriadicCube d) {s : ℝ} (ξ : Vec d → Vec d) {Acirc1 AcircS E B C : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hAcirc1 : 0 < Acirc1)
    (hAcircS : 0 ≤ AcircS) (hE : 0 < E) (hB : 0 < B) (hC : 0 < C) :
    0 < coarseCaccioppoliCenteredCutoffSize Q s ξ Acirc1 AcircS E B C := by
  unfold coarseCaccioppoliCenteredCutoffSize
  have hscale : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hexp_neg : 2 * (s - 1) < 0 := by nlinarith
  have hrpow_lt_one :
      Real.rpow (3 : ℝ) (2 * (s - 1)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp_neg
  have hsqrt_pos :
      0 < Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) :=
    Real.sqrt_pos.2 (inv_pos.mpr (sub_pos.mpr hrpow_lt_one))
  have hnote1_pos :
      0 < ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) := by
    exact mul_pos (mul_pos (by norm_num) hC) (Real.rpow_pos_of_pos (by norm_num) _)
  have hterm1 :
      0 < cubeScaleFactor Q * B *
        (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹) *
          (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) * (Acirc1 * E))) := by
    refine mul_pos (mul_pos hscale hB) ?_
    refine mul_pos hsqrt_pos ?_
    exact mul_pos hnote1_pos (mul_pos hAcirc1 hE)
  have hterm2 :
      0 ≤ cubeLpNorm Q ∞ ξ *
        (cubeBesovScaleWeight (-s) Q *
          ((((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            (1 - (3 : ℝ) ^ (-s))⁻¹) * (AcircS * E))) := by
    have hr_lt_one : (3 : ℝ) ^ (-s) < 1 := by
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hnoteS :
        0 ≤ (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            (1 - (3 : ℝ) ^ (-s))⁻¹) := by
      exact mul_nonneg hnote1_pos.le (inv_nonneg.mpr (sub_nonneg.mpr hr_lt_one.le))
    refine mul_nonneg (cubeLpNorm_nonneg Q ∞ ξ) ?_
    refine mul_nonneg (cubeBesovScaleWeight_nonneg (-s) Q) ?_
    exact mul_nonneg hnoteS (mul_nonneg hAcircS hE.le)
  exact mul_pos (by norm_num : 0 < (2 : ℝ)) (add_pos_of_pos_of_nonneg hterm1 hterm2)

/-- Flux-side hypotheses needed to substitute coarse-Poincare energy controls
into the local Caccioppoli split theorem. -/
def CoarseCaccioppoliFluxEnergyControls {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s : ℝ) (flux : Vec d → Vec d) (energy : Vec d → ℝ) :
    Prop :=
  (∀ x ∈ cubeSet Q, 0 ≤ energy x) ∧
  MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume ∧
  CubeAverageFluxEnergyControl Q a flux energy ∧
  Summable (fun n : ℕ =>
    geometricWeight (1 : ℝ) 1 n *
      Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
        (1 / 2 : ℝ)) ∧
  Summable (fun n : ℕ =>
    geometricWeight s 1 n *
      Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
        (1 / 2 : ℝ))

/-- Gradient-average energy controls restrict from a parent cube to any
depth-`j` descendant. -/
theorem CubeAverageGradientEnergyControl.restrict_to_descendant
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    {a : CoeffField d} {g : Vec d → Vec d} {energy : Vec d → ℝ}
    (hgrad : CubeAverageGradientEnergyControl Q a g energy)
    (hR : R ∈ descendantsAtDepth Q j) :
    CubeAverageGradientEnergyControl R a g energy := by
  intro n S hS
  exact hgrad (j + n) S (mem_descendantsAtDepth_add hR hS)

/-- Flux-energy controls restrict from a parent cube to any depth-`j`
descendant. -/
theorem CoarseCaccioppoliFluxEnergyControls.restrict_to_descendant
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    {a : CoeffField d} {s : ℝ} {flux : Vec d → Vec d} {energy : Vec d → ℝ}
    (hctrl : CoarseCaccioppoliFluxEnergyControls Q a s flux energy)
    (hs : 0 ≤ s) (hR : R ∈ descendantsAtDepth Q j) :
    CoarseCaccioppoliFluxEnergyControls R a s flux energy := by
  rcases hctrl with ⟨henergy_nonneg, henergy_int, hfluxCtrl, hsum1, hsumS⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact henergy_nonneg x (cubeSet_subset_of_mem_descendantsAtDepth hR hx)
  · exact henergy_int.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR)
  · intro n S hS
    exact hfluxCtrl (j + n) S (mem_descendantsAtDepth_add hR hS)
  · exact
      summable_geometricWeight_maxDescendantBBlockNormAtScale_of_mem_descendantsAtDepth
        (Q := Q) (R := R) (j := j) a (1 : ℝ) (by norm_num) hR hsum1
  · exact
      summable_geometricWeight_maxDescendantBBlockNormAtScale_of_mem_descendantsAtDepth
        (Q := Q) (R := R) (j := j) a s hs hR hsumS

/-- Harmonic closed-cube constructor for the flux energy-control package used
by the Caccioppoli bridge.  The final note-facing endpoints still work on open
cubes; this lemma records the exact stronger compatibility hypothesis under
which the flux package is already available from the coarse-Poincare API. -/
theorem CoarseCaccioppoliFluxEnergyControls.of_aHarmonicFunction_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    {lam Lam : ℝ} (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (u : AHarmonicFunction a (cubeSet Q)) :
    CoarseCaccioppoliFluxEnergyControls Q a s
      (fun x => matVecMul (a x) (u.toH1.grad x))
      (fun x => scalarVariationEnergyIntegrand a u x) := by
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn (cubeSet Q) a hEll u
  · exact ResponseLinearIntegrabilityData.energy
      (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) u
  · exact
      cubeAverageFluxEnergyControl_of_aHarmonicFunction_of_openCubeOriginEllipticRecoveryExistence
        (Q := Q) (a := a) hEll u hOrigin
  · exact
      summable_qone_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeOriginEllipticRecoveryExistence
        (Q := Q) (a := a) (s := (1 : ℝ)) (by norm_num) hEll hOrigin
  · exact
      summable_qone_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeOriginEllipticRecoveryExistence
        (Q := Q) (a := a) (s := s) hs hEll hOrigin

/-- Scalar projected-Poincare and cutoff-product hypotheses remaining after the
flux-side coarse-Poincare controls have been substituted. -/
def CoarseCaccioppoliScalarCutoffControls {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (u g : Vec d → ℝ) (ξ : Vec d → Vec d) (energy : Vec d → ℝ)
    (Acirc1 AcircS B C : ℝ) : Prop :=
  0 ≤ B ∧
  0 ≤ coarseCaccioppoliConstantCutoffSize Q u ξ B ∧
  0 ≤
    coarseCaccioppoliCenteredCutoffSize Q s ξ Acirc1 AcircS
      (Real.sqrt (cubeAverage Q energy)) B C ∧
  0 ≤ C ∧
  (∀ N : ℕ,
    CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C (cubeFluctuation Q u) g N) ∧
  (∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i)) ∧
  (∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B) ∧
  (∀ N : ℕ,
    cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤
      Acirc1 * Real.sqrt (cubeAverage Q energy)) ∧
  (∀ N : ℕ,
    cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤
      AcircS * Real.sqrt (cubeAverage Q energy))

/-- Vector projected-Poincare and cutoff-product hypotheses remaining after the
flux-side coarse-Poincare controls have been substituted.

The Poincare constant is the vector constant `C`; downstream exact RHS
bookkeeping uses the effective scalar-shaped constant
`(Fintype.card (Fin d) : ℝ) * C`, reflecting the sum over gradient
components. -/
def CoarseCaccioppoliVectorCutoffControls {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (u : Vec d → ℝ) (G : Vec d → Vec d) (ξ : Vec d → Vec d) (energy : Vec d → ℝ)
    (Acirc1 AcircS B C : ℝ) : Prop :=
  0 ≤ B ∧
  0 ≤ AcircS ∧
  0 ≤ coarseCaccioppoliConstantCutoffSize Q u ξ B ∧
  0 ≤
    coarseCaccioppoliCenteredCutoffSize Q s ξ Acirc1 AcircS
      (Real.sqrt (cubeAverage Q energy)) B ((Fintype.card (Fin d) : ℝ) * C) ∧
  0 ≤ C ∧
  (∀ N : ℕ,
    CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C (cubeFluctuation Q u) G N) ∧
  (∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i)) ∧
  (∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B) ∧
  (∀ i : Fin d, ∀ N : ℕ,
    cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => G x i) ≤
      Acirc1 * Real.sqrt (cubeAverage Q energy)) ∧
  (∀ i : Fin d, ∀ N : ℕ,
    cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
      (fun x => G x i) ≤ AcircS * Real.sqrt (cubeAverage Q energy))

end

end Homogenization
