/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.AbsorbedRecurrences

/-! # Absorbed Global Iteration -/

namespace Homogenization

noncomputable section

/-- Scaled bounded-tail weak-flux iteration with the explicit
corrector-energy local error as the recurrence error. -/
theorem weakFluxRHSScaledAveragedSeminormSq_le_correctorEnergyLocalError_base_mul_inv_one_sub_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (z : TriadicCube d → Vec d → Vec d)
    (hs : 0 < s)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          weakFluxRHSCorrectorEnergyLocalError R a u (z R) s)
    (m : ℕ) {B : ℝ}
    (hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s u n))
    (hB_nonneg : 0 ≤ B)
    (hterm :
      ∀ k : ℕ,
        coarsePoincareRHSDepthWeight s (m + k) *
          descendantsAverage Q (m + k)
            (fun R => weakFluxRHSCorrectorEnergyLocalError R a u (z R) s) ≤ B) :
    weakFluxRHSScaledAveragedSeminormSq Q a s u m ≤
      B * (1 - Real.rpow (3 : ℝ) (-s))⁻¹ := by
  exact
    weakFluxRHSScaledAveragedSeminormSq_le_base_mul_inv_one_sub_of_bddAbove
      Q a s u
      (fun R => weakFluxRHSCorrectorEnergyLocalError R a u (z R) s)
      hs hlocal m hBdd hB_nonneg hterm

/-- Scaled bounded-tail weak-flux iteration where the corrector-energy local
error is controlled by separate averaged coefficient-energy bases. -/
theorem weakFluxRHSScaledAveragedSeminormSq_le_correctorEnergyComponents_base_mul_inv_one_sub_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (z : TriadicCube d → Vec d → Vec d)
    (hs : 0 < s)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          weakFluxRHSCorrectorEnergyLocalError R a u (z R) s)
    (m : ℕ) {Bcoeff Bcorr : ℝ}
    (hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s u n))
    (hBcoeff_nonneg : 0 ≤ Bcoeff)
    (hBcorr_nonneg : 0 ≤ Bcorr)
    (hcoeff :
      ∀ k : ℕ,
        coarsePoincareRHSDepthWeight s (m + k) *
          weakFluxRHSLocalCoefficientEnergyErrorAverage Q a u s (m + k) ≤ Bcoeff)
    (hcorr :
      ∀ k : ℕ,
        coarsePoincareRHSDepthWeight s (m + k) *
          weakFluxRHSLocalCorrectorEnergyErrorAverage Q a z s (m + k) ≤ Bcorr) :
    weakFluxRHSScaledAveragedSeminormSq Q a s u m ≤
      (Bcoeff + Bcorr) * (1 - Real.rpow (3 : ℝ) (-s))⁻¹ := by
  refine
    weakFluxRHSScaledAveragedSeminormSq_le_correctorEnergyLocalError_base_mul_inv_one_sub_of_bddAbove
      Q a s u z hs hlocal m hBdd (add_nonneg hBcoeff_nonneg hBcorr_nonneg) ?_
  intro k
  exact
    weakFluxRHSCorrectorEnergyErrorAverage_weighted_le_add_of_components
      Q a u z s (m + k) (hcoeff k) (hcorr k)

/-- Localized flux-defect form of the scaled bounded-tail weak-flux iteration
with the explicit corrector-energy local-error envelope. -/
theorem localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_correctorEnergyLocalError_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (z : TriadicCube d → Vec d → Vec d)
    (hs : 0 < s)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          weakFluxRHSCorrectorEnergyLocalError R a u (z R) s)
    (m : ℕ) {B : ℝ}
    (hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s u n))
    (hB_nonneg : 0 ≤ B)
    (hterm :
      ∀ k : ℕ,
        coarsePoincareRHSDepthWeight s (m + k) *
          descendantsAverage Q (m + k)
            (fun R => weakFluxRHSCorrectorEnergyLocalError R a u (z R) s) ≤ B) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fun x => matVecMul (a x) (u x)) m ≤
      Real.sqrt
        ((coarsePoincareRHSDepthWeight s m)⁻¹ *
          (B * (1 - Real.rpow (3 : ℝ) (-s))⁻¹)) := by
  exact
    localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_base_mul_inv_one_sub_bddAbove
      Q a s u
      (fun R => weakFluxRHSCorrectorEnergyLocalError R a u (z R) s)
      hs hlocal m hBdd hB_nonneg hterm

/-- Localized flux-defect form with separate corrector-energy component bases. -/
theorem localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_correctorEnergyComponents_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (u : Vec d → Vec d) (z : TriadicCube d → Vec d → Vec d)
    (hs : 0 < s)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          weakFluxRHSCorrectorEnergyLocalError R a u (z R) s)
    (m : ℕ) {Bcoeff Bcorr : ℝ}
    (hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s u n))
    (hBcoeff_nonneg : 0 ≤ Bcoeff)
    (hBcorr_nonneg : 0 ≤ Bcorr)
    (hcoeff :
      ∀ k : ℕ,
        coarsePoincareRHSDepthWeight s (m + k) *
          weakFluxRHSLocalCoefficientEnergyErrorAverage Q a u s (m + k) ≤ Bcoeff)
    (hcorr :
      ∀ k : ℕ,
        coarsePoincareRHSDepthWeight s (m + k) *
          weakFluxRHSLocalCorrectorEnergyErrorAverage Q a z s (m + k) ≤ Bcorr) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fun x => matVecMul (a x) (u x)) m ≤
      Real.sqrt
        ((coarsePoincareRHSDepthWeight s m)⁻¹ *
          ((Bcoeff + Bcorr) * (1 - Real.rpow (3 : ℝ) (-s))⁻¹)) := by
  refine
    localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_correctorEnergyLocalError_bddAbove
      Q a s u z hs hlocal m hBdd
      (add_nonneg hBcoeff_nonneg hBcorr_nonneg) ?_
  intro k
  exact
    weakFluxRHSCorrectorEnergyErrorAverage_weighted_le_add_of_components
      Q a u z s (m + k) (hcoeff k) (hcorr k)

/-- Scaled bounded-tail weak-flux iteration with the explicit absorbed local
error as the recurrence error. -/
theorem weakFluxRHSScaledAveragedSeminormSq_le_absorbedLocalError_base_mul_inv_one_sub_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s η : ℝ)
    (u g : Vec d → Vec d) (v : TriadicCube d → Vec d → Vec d)
    (hs : 0 < s)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          weakFluxRHSAbsorbedLocalError R a g u (v R) s η)
    (m : ℕ) {B : ℝ}
    (hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s u n))
    (hB_nonneg : 0 ≤ B)
    (hterm :
      ∀ k : ℕ,
        coarsePoincareRHSDepthWeight s (m + k) *
          descendantsAverage Q (m + k)
            (fun R => weakFluxRHSAbsorbedLocalError R a g u (v R) s η) ≤ B) :
    weakFluxRHSScaledAveragedSeminormSq Q a s u m ≤
      B * (1 - Real.rpow (3 : ℝ) (-s))⁻¹ := by
  exact
    weakFluxRHSScaledAveragedSeminormSq_le_base_mul_inv_one_sub_of_bddAbove
      Q a s u
      (fun R => weakFluxRHSAbsorbedLocalError R a g u (v R) s η)
      hs hlocal m hBdd hB_nonneg hterm

/-- Scaled bounded-tail weak-flux iteration where the absorbed local error is
controlled by separate averaged component bases. -/
theorem weakFluxRHSScaledAveragedSeminormSq_le_absorbedComponents_base_mul_inv_one_sub_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s η : ℝ)
    (u g : Vec d → Vec d) (v : TriadicCube d → Vec d → Vec d)
    (hs : 0 < s)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          weakFluxRHSAbsorbedLocalError R a g u (v R) s η)
    (m : ℕ) {Bcoeff Bu Bv Bforce : ℝ}
    (hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s u n))
    (hBcoeff_nonneg : 0 ≤ Bcoeff)
    (hBu_nonneg : 0 ≤ Bu)
    (hBv_nonneg : 0 ≤ Bv)
    (hBforce_nonneg : 0 ≤ Bforce)
    (hcoeff :
      ∀ k : ℕ,
        coarsePoincareRHSDepthWeight s (m + k) *
          weakFluxRHSLocalCoefficientEnergyErrorAverage Q a u s (m + k) ≤ Bcoeff)
    (hu :
      ∀ k : ℕ,
        coarsePoincareRHSDepthWeight s (m + k) *
          weakFluxRHSLocalUSeminormErrorAverage Q u s η (m + k) ≤ Bu)
    (hv :
      ∀ k : ℕ,
        coarsePoincareRHSDepthWeight s (m + k) *
          weakFluxRHSLocalHarmonicSeminormErrorAverage Q v s η (m + k) ≤ Bv)
    (hforce :
      ∀ k : ℕ,
        coarsePoincareRHSDepthWeight s (m + k) *
          weakFluxRHSLocalForceErrorAverage Q a g s η (m + k) ≤ Bforce) :
    weakFluxRHSScaledAveragedSeminormSq Q a s u m ≤
      (Bcoeff + Bu + Bv + Bforce) * (1 - Real.rpow (3 : ℝ) (-s))⁻¹ := by
  have hB_nonneg : 0 ≤ Bcoeff + Bu + Bv + Bforce :=
    add_nonneg (add_nonneg (add_nonneg hBcoeff_nonneg hBu_nonneg) hBv_nonneg)
      hBforce_nonneg
  refine
    weakFluxRHSScaledAveragedSeminormSq_le_absorbedLocalError_base_mul_inv_one_sub_of_bddAbove
      Q a s η u g v hs hlocal m hBdd hB_nonneg ?_
  intro k
  exact
    weakFluxRHSAbsorbedErrorAverage_weighted_le_add_of_components
      Q a g u v s η (m + k) (hcoeff k) (hu k) (hv k) (hforce k)

/-- Localized flux-defect form of the scaled bounded-tail weak-flux iteration
with the explicit absorbed local-error envelope. -/
theorem localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalError_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s η : ℝ)
    (u g : Vec d → Vec d) (v : TriadicCube d → Vec d → Vec d)
    (hs : 0 < s)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          weakFluxRHSAbsorbedLocalError R a g u (v R) s η)
    (m : ℕ) {B : ℝ}
    (hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s u n))
    (hB_nonneg : 0 ≤ B)
    (hterm :
      ∀ k : ℕ,
        coarsePoincareRHSDepthWeight s (m + k) *
          descendantsAverage Q (m + k)
            (fun R => weakFluxRHSAbsorbedLocalError R a g u (v R) s η) ≤ B) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fun x => matVecMul (a x) (u x)) m ≤
      Real.sqrt
        ((coarsePoincareRHSDepthWeight s m)⁻¹ *
          (B * (1 - Real.rpow (3 : ℝ) (-s))⁻¹)) := by
  exact
    localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_base_mul_inv_one_sub_bddAbove
      Q a s u
      (fun R => weakFluxRHSAbsorbedLocalError R a g u (v R) s η)
      hs hlocal m hBdd hB_nonneg hterm

/-- Localized flux-defect form with separate absorbed component bases. -/
theorem localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedComponents_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s η : ℝ)
    (u g : Vec d → Vec d) (v : TriadicCube d → Vec d → Vec d)
    (hs : 0 < s)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          weakFluxRHSAbsorbedLocalError R a g u (v R) s η)
    (m : ℕ) {Bcoeff Bu Bv Bforce : ℝ}
    (hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s u n))
    (hBcoeff_nonneg : 0 ≤ Bcoeff)
    (hBu_nonneg : 0 ≤ Bu)
    (hBv_nonneg : 0 ≤ Bv)
    (hBforce_nonneg : 0 ≤ Bforce)
    (hcoeff :
      ∀ k : ℕ,
        coarsePoincareRHSDepthWeight s (m + k) *
          weakFluxRHSLocalCoefficientEnergyErrorAverage Q a u s (m + k) ≤ Bcoeff)
    (hu :
      ∀ k : ℕ,
        coarsePoincareRHSDepthWeight s (m + k) *
          weakFluxRHSLocalUSeminormErrorAverage Q u s η (m + k) ≤ Bu)
    (hv :
      ∀ k : ℕ,
        coarsePoincareRHSDepthWeight s (m + k) *
          weakFluxRHSLocalHarmonicSeminormErrorAverage Q v s η (m + k) ≤ Bv)
    (hforce :
      ∀ k : ℕ,
        coarsePoincareRHSDepthWeight s (m + k) *
          weakFluxRHSLocalForceErrorAverage Q a g s η (m + k) ≤ Bforce) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fun x => matVecMul (a x) (u x)) m ≤
      Real.sqrt
        ((coarsePoincareRHSDepthWeight s m)⁻¹ *
          ((Bcoeff + Bu + Bv + Bforce) *
            (1 - Real.rpow (3 : ℝ) (-s))⁻¹)) := by
  have hB_nonneg : 0 ≤ Bcoeff + Bu + Bv + Bforce :=
    add_nonneg (add_nonneg (add_nonneg hBcoeff_nonneg hBu_nonneg) hBv_nonneg)
      hBforce_nonneg
  refine
    localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalError_bddAbove
      Q a s η u g v hs hlocal m hBdd hB_nonneg ?_
  intro k
  exact
    weakFluxRHSAbsorbedErrorAverage_weighted_le_add_of_components
      Q a g u v s η (m + k) (hcoeff k) (hu k) (hv k) (hforce k)

/-- Scaled bounded-tail weak-flux iteration with all localized absorbed
component bases supplied by the coefficient, `u`, harmonic-remainder, and
forcing base estimates. -/
theorem weakFluxRHSScaledAveragedSeminormSq_le_absorbedLocalizedBases_mul_inv_one_sub_of_bddAbove
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s η : ℝ) (u g : Vec d → Vec d)
    (v : TriadicCube d → Vec d → Vec d) {lam Lam : ℝ}
    (hs : 0 < s) (hη : 0 < η)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          weakFluxRHSAbsorbedLocalError R a g u (v R) s η)
    (m : ℕ) {BU BV : ℝ}
    (hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s u n))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_half :
      Summable (fun l : ℕ =>
        geometricWeight (s / 2) 2 l *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (l : ℤ)) a) 1))
    (havg_parent_nonneg :
      0 ≤ cubeAverage Q (coefficientEnergyDensity a u))
    (havg_nonneg :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a u))
    (hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a u) (cubeSet Q)
        MeasureTheory.volume)
    (hmem :
      ∀ j : ℕ, ∀ S ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hLocalBdd :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g))
    (hBU_nonneg : 0 ≤ BU)
    (hBV_nonneg : 0 ≤ BV)
    (hu :
      ∀ k : ℕ, coarsePoincareRHSSn Q s u (m + k) ≤ BU)
    (hv :
      ∀ k : ℕ,
        weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq Q s v (m + k) ≤ BV) :
    weakFluxRHSScaledAveragedSeminormSq Q a s u m ≤
      (weakFluxRHSWeightedCoefficientEnergyBase Q a u s +
          η * BU + η * BV + weakFluxRHSWeightedGlobalForceBase Q a g s η m) *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹ := by
  have hcoeff_nonneg :
      0 ≤ weakFluxRHSWeightedCoefficientEnergyBase Q a u s :=
    weakFluxRHSWeightedCoefficientEnergyBase_nonneg Q a u hs havg_parent_nonneg
  have hBU_component_nonneg : 0 ≤ η * BU :=
    mul_nonneg hη.le hBU_nonneg
  have hBV_component_nonneg : 0 ≤ η * BV :=
    mul_nonneg hη.le hBV_nonneg
  have hforce_nonneg :
      0 ≤ weakFluxRHSWeightedGlobalForceBase Q a g s η m :=
    weakFluxRHSWeightedGlobalForceBase_nonneg Q a g s hη m
  refine
    weakFluxRHSScaledAveragedSeminormSq_le_absorbedComponents_base_mul_inv_one_sub_of_bddAbove
      (Q := Q) (a := a) (s := s) (η := η) (u := u) (g := g) (v := v)
      (m := m) (Bcoeff := weakFluxRHSWeightedCoefficientEnergyBase Q a u s)
      (Bu := η * BU) (Bv := η * BV)
      (Bforce := weakFluxRHSWeightedGlobalForceBase Q a g s η m)
      hs hlocal hBdd hcoeff_nonneg hBU_component_nonneg hBV_component_nonneg
      hforce_nonneg ?_ ?_ ?_ ?_
  · intro k
    exact
      weakFluxRHSDepthWeight_mul_coefficientEnergyErrorAverage_le_weightedCoefficientEnergyBase
        Q a u (m + k) hs hEll hData hsum_half (havg_nonneg (m + k)) hint
  · intro k
    exact
      weakFluxRHSDepthWeight_mul_uSeminormErrorAverage_le_eta_mul_base_of_tail
        (Q := Q) (u := u) (s := s) (η := η) (B := BU)
        (m := m) (k := k) hη.le hu
  · intro k
    exact
      weakFluxRHSDepthWeight_mul_harmonicSeminormErrorAverage_le_eta_mul_base_of_tail
        (Q := Q) (v := v) (s := s) (η := η) (B := BV)
        (m := m) (k := k) hη.le hv
  · intro k
    exact
      weakFluxRHSDepthWeight_mul_forceErrorAverage_le_weightedGlobalForceBase
        Q a g m k hs hη hEll hData hsum_half hmem hGlobalBdd
        (hLocalBdd (m + k))

/-- Localized flux-defect form with all localized absorbed component bases
supplied by the coefficient, `u`, harmonic-remainder, and forcing base
estimates. -/
theorem localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedLocalizedBases_bddAbove
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s η : ℝ) (u g : Vec d → Vec d)
    (v : TriadicCube d → Vec d → Vec d) {lam Lam : ℝ}
    (hs : 0 < s) (hη : 0 < η)
    (hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          weakFluxRHSAbsorbedLocalError R a g u (v R) s η)
    (m : ℕ) {BU BV : ℝ}
    (hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s u n))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_half :
      Summable (fun l : ℕ =>
        geometricWeight (s / 2) 2 l *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (l : ℤ)) a) 1))
    (havg_parent_nonneg :
      0 ≤ cubeAverage Q (coefficientEnergyDensity a u))
    (havg_nonneg :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a u))
    (hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a u) (cubeSet Q)
        MeasureTheory.volume)
    (hmem :
      ∀ j : ℕ, ∀ S ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hLocalBdd :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g))
    (hBU_nonneg : 0 ≤ BU)
    (hBV_nonneg : 0 ≤ BV)
    (hu :
      ∀ k : ℕ, coarsePoincareRHSSn Q s u (m + k) ≤ BU)
    (hv :
      ∀ k : ℕ,
        weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq Q s v (m + k) ≤ BV) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fun x => matVecMul (a x) (u x)) m ≤
      Real.sqrt
        ((coarsePoincareRHSDepthWeight s m)⁻¹ *
          ((weakFluxRHSWeightedCoefficientEnergyBase Q a u s +
              η * BU + η * BV + weakFluxRHSWeightedGlobalForceBase Q a g s η m) *
            (1 - Real.rpow (3 : ℝ) (-s))⁻¹)) := by
  have hcoeff_nonneg :
      0 ≤ weakFluxRHSWeightedCoefficientEnergyBase Q a u s :=
    weakFluxRHSWeightedCoefficientEnergyBase_nonneg Q a u hs havg_parent_nonneg
  have hBU_component_nonneg : 0 ≤ η * BU :=
    mul_nonneg hη.le hBU_nonneg
  have hBV_component_nonneg : 0 ≤ η * BV :=
    mul_nonneg hη.le hBV_nonneg
  have hforce_nonneg :
      0 ≤ weakFluxRHSWeightedGlobalForceBase Q a g s η m :=
    weakFluxRHSWeightedGlobalForceBase_nonneg Q a g s hη m
  refine
    localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_absorbedComponents_bddAbove
      (Q := Q) (a := a) (s := s) (η := η) (u := u) (g := g) (v := v)
      (m := m) (Bcoeff := weakFluxRHSWeightedCoefficientEnergyBase Q a u s)
      (Bu := η * BU) (Bv := η * BV)
      (Bforce := weakFluxRHSWeightedGlobalForceBase Q a g s η m)
      hs hlocal hBdd hcoeff_nonneg hBU_component_nonneg hBV_component_nonneg
      hforce_nonneg ?_ ?_ ?_ ?_
  · intro k
    exact
      weakFluxRHSDepthWeight_mul_coefficientEnergyErrorAverage_le_weightedCoefficientEnergyBase
        Q a u (m + k) hs hEll hData hsum_half (havg_nonneg (m + k)) hint
  · intro k
    exact
      weakFluxRHSDepthWeight_mul_uSeminormErrorAverage_le_eta_mul_base_of_tail
        (Q := Q) (u := u) (s := s) (η := η) (B := BU)
        (m := m) (k := k) hη.le hu
  · intro k
    exact
      weakFluxRHSDepthWeight_mul_harmonicSeminormErrorAverage_le_eta_mul_base_of_tail
        (Q := Q) (v := v) (s := s) (η := η) (B := BV)
        (m := m) (k := k) hη.le hv
  · intro k
    exact
      weakFluxRHSDepthWeight_mul_forceErrorAverage_le_weightedGlobalForceBase
        Q a g m k hs hη hEll hData hsum_half hmem hGlobalBdd
        (hLocalBdd (m + k))

end

end Homogenization
