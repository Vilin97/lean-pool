/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.AbsorbedComponents

/-! # Absorbed Component Bounds -/

@[expose] public section

namespace Homogenization

noncomputable section

/-- Depth-weighted parent-localized weak-flux coefficient-energy base. -/
noncomputable def weakFluxRHSWeightedCoefficientEnergyBase {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d)
    (s : ℝ) : ℝ :=
  2 * (geometricDiscount s 2)⁻¹ *
    LambdaSq Q (s / 2) (.finite 2) a *
    cubeAverage Q (coefficientEnergyDensity a u)

/-- The depth-weighted parent-localized weak-flux coefficient-energy base is
nonnegative when the parent energy average is nonnegative. -/
theorem weakFluxRHSWeightedCoefficientEnergyBase_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d)
    {s : ℝ} (hs : 0 < s)
    (havg_nonneg : 0 ≤ cubeAverage Q (coefficientEnergyDensity a u)) :
    0 ≤ weakFluxRHSWeightedCoefficientEnergyBase Q a u s := by
  unfold weakFluxRHSWeightedCoefficientEnergyBase
  have hs2 : 0 < s * (2 : ℝ) := by nlinarith
  have hshalf2_nonneg : 0 ≤ (s / 2) * (2 : ℝ) := by nlinarith
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (inv_nonneg.mpr (le_of_lt (geometricDiscount_pos hs2))))
        (multiscale_ellipticity_LambdaSq_finite_nonneg Q (s / 2) 2 a
        (by norm_num) hshalf2_nonneg))
    havg_nonneg

/-- Note-constant square-envelope for the coefficient-energy part of the
localized weak-flux RHS.  This is the manuscript `s^{-2} Lambda * energy`
piece before taking the final square root. -/
theorem weakFluxRHSWeightedCoefficientEnergyBase_mul_inv_one_sub_step_le_noteEnergySquare
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d)
    {s : ℝ} (hs : 0 < s) (hs_le : s ≤ 1)
    (havg_nonneg : 0 ≤ cubeAverage Q (coefficientEnergyDensity a u)) :
    weakFluxRHSWeightedCoefficientEnergyBase Q a u s *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤
      50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
        cubeAverage Q (coefficientEnergyDensity a u) := by
  let G : ℝ := (geometricDiscount s 2)⁻¹
  let H : ℝ := (1 - Real.rpow (3 : ℝ) (-s))⁻¹
  let L : ℝ := LambdaSq Q (s / 2) (.finite 2) a
  let A : ℝ := cubeAverage Q (coefficientEnergyDensity a u)
  let K : ℝ := 5 * s⁻¹
  have hG_nonneg : 0 ≤ G := by
    dsimp [G]
    exact inv_nonneg.mpr (le_of_lt (geometricDiscount_pos (by nlinarith : 0 < s * 2)))
  have hG_le : G ≤ K := by
    dsimp [G, K]
    exact inv_geometricDiscount_two_le_five_inv hs hs_le
  have hH_nonneg : 0 ≤ H := by
    dsimp [H]
    have hr_lt_one : Real.rpow (3 : ℝ) (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg
        (by norm_num : (1 : ℝ) < 3) (by linarith)
    exact inv_nonneg.mpr (sub_nonneg.mpr hr_lt_one.le)
  have hH_le : H ≤ K := by
    dsimp [H, K]
    exact inv_one_sub_rpow_three_neg_le_five_inv hs hs_le
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact multiscale_ellipticity_LambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * 2)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact havg_nonneg
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hleft_le :
      2 * G * L * A ≤ 2 * K * L * A := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hG_le (by norm_num : 0 ≤ (2 : ℝ)))
        hL_nonneg)
      hA_nonneg
  have hright_nonneg : 0 ≤ 2 * K * L * A := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hK_nonneg) hL_nonneg)
      hA_nonneg
  calc
    weakFluxRHSWeightedCoefficientEnergyBase Q a u s *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹ =
        (2 * G * L * A) * H := by
          simp [weakFluxRHSWeightedCoefficientEnergyBase, G, H, L, A]
    _ ≤ (2 * K * L * A) * H := by
          exact mul_le_mul_of_nonneg_right hleft_le hH_nonneg
    _ ≤ (2 * K * L * A) * K := by
          exact mul_le_mul_of_nonneg_left hH_le hright_nonneg
    _ =
        50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
          cubeAverage Q (coefficientEnergyDensity a u) := by
          simp [K, L, A]
          ring

/-- Note-eta specialization of the localized absorbed weak-flux component base. -/
noncomputable def weakFluxRHSAbsorbedLocalizedNoteBase {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u g : Vec d → Vec d)
    (s : ℝ) (m : ℕ) (BU BV : ℝ) : ℝ :=
  weakFluxRHSWeightedCoefficientEnergyBase Q a u s +
    coarsePoincareRHSNoteEta s * BU +
      coarsePoincareRHSNoteEta s * BV +
        weakFluxRHSWeightedGlobalForceBase Q a g s
          (coarsePoincareRHSNoteEta s) m

/-- Componentwise upper-bound interface for the full note-eta localized base
after multiplying by the weak-flux geometric tail. -/
theorem weakFluxRHSAbsorbedLocalizedNoteBase_mul_inv_one_sub_step_le_of_components
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (u g : Vec d → Vec d)
    (s : ℝ) (m : ℕ) (BU BV Bcoeff Bu Bv Bforce : ℝ)
    (hcoeff :
      weakFluxRHSWeightedCoefficientEnergyBase Q a u s *
          (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤ Bcoeff)
    (hu :
      (coarsePoincareRHSNoteEta s * BU) *
          (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤ Bu)
    (hv :
      (coarsePoincareRHSNoteEta s * BV) *
          (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤ Bv)
    (hforce :
      weakFluxRHSWeightedGlobalForceBase Q a g s
          (coarsePoincareRHSNoteEta s) m *
          (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤ Bforce) :
    weakFluxRHSAbsorbedLocalizedNoteBase Q a u g s m BU BV *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤
      Bcoeff + Bu + Bv + Bforce := by
  have hadd :
      weakFluxRHSWeightedCoefficientEnergyBase Q a u s *
            (1 - Real.rpow (3 : ℝ) (-s))⁻¹ +
          (coarsePoincareRHSNoteEta s * BU) *
            (1 - Real.rpow (3 : ℝ) (-s))⁻¹ +
          (coarsePoincareRHSNoteEta s * BV) *
            (1 - Real.rpow (3 : ℝ) (-s))⁻¹ +
          weakFluxRHSWeightedGlobalForceBase Q a g s
            (coarsePoincareRHSNoteEta s) m *
            (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤
        Bcoeff + Bu + Bv + Bforce :=
    add_le_add (add_le_add (add_le_add hcoeff hu) hv) hforce
  calc
    weakFluxRHSAbsorbedLocalizedNoteBase Q a u g s m BU BV *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹ =
        weakFluxRHSWeightedCoefficientEnergyBase Q a u s *
            (1 - Real.rpow (3 : ℝ) (-s))⁻¹ +
          (coarsePoincareRHSNoteEta s * BU) *
            (1 - Real.rpow (3 : ℝ) (-s))⁻¹ +
          (coarsePoincareRHSNoteEta s * BV) *
            (1 - Real.rpow (3 : ℝ) (-s))⁻¹ +
          weakFluxRHSWeightedGlobalForceBase Q a g s
            (coarsePoincareRHSNoteEta s) m *
            (1 - Real.rpow (3 : ℝ) (-s))⁻¹ := by
          simp [weakFluxRHSAbsorbedLocalizedNoteBase]
          ring
    _ ≤ Bcoeff + Bu + Bv + Bforce := hadd

/-- Descendant-averaged coefficient-energy component localized to the parent
half-scale upper multiscale coefficient and the parent energy average. -/
theorem weakFluxRHSLocalCoefficientEnergyErrorAverage_le_parentHalfLambda_globalAverage
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (u : Vec d → Vec d) {s lam Lam : ℝ} (n : ℕ)
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_half :
      Summable (fun m : ℕ =>
        geometricWeight (s / 2) 2 m *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (m : ℤ)) a) 1))
    (havg_nonneg :
      ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a u))
    (hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a u) (cubeSet Q)
        MeasureTheory.volume) :
    weakFluxRHSLocalCoefficientEnergyErrorAverage Q a u s n ≤
      2 * ((geometricDiscount s 2)⁻¹ *
        (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
          LambdaSq Q (s / 2) (.finite 2) a)) *
        cubeAverage Q (coefficientEnergyDensity a u) := by
  let C : ℝ :=
    (geometricDiscount s 2)⁻¹ *
      (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
        LambdaSq Q (s / 2) (.finite 2) a)
  have hcoeff :
      ∀ R ∈ descendantsAtDepth Q n,
        weakFluxRHSLocalCoeff R a s ≤ C := by
    intro R hR
    exact weakFluxRHSLocalCoeff_le_parentHalfLambda_of_mem_descendantsAtDepth
      (Q := Q) (R := R) a hs hR hEll hData hsum_half
  have hbase :
      weakFluxRHSLocalCoefficientEnergyErrorAverage Q a u s n ≤
        2 * C *
          descendantsAverage Q n
            (fun R => cubeAverage R (coefficientEnergyDensity a u)) := by
    unfold weakFluxRHSLocalCoefficientEnergyErrorAverage
    calc
      descendantsAverage Q n (fun R => weakFluxRHSLocalCoefficientEnergyError R a u s)
          ≤
            descendantsAverage Q n
              (fun R => 2 * C * cubeAverage R (coefficientEnergyDensity a u)) := by
                refine descendantsAverage_le_descendantsAverage Q n ?_
                intro R hR
                unfold weakFluxRHSLocalCoefficientEnergyError
                calc
                  2 * weakFluxRHSLocalCoeff R a s *
                      cubeAverage R (coefficientEnergyDensity a u)
                      ≤ 2 * (C * cubeAverage R (coefficientEnergyDensity a u)) := by
                        simpa [mul_assoc] using mul_le_mul_of_nonneg_left
                          (mul_le_mul_of_nonneg_right (hcoeff R hR) (havg_nonneg R hR))
                          (show 0 ≤ (2 : ℝ) by norm_num)
                  _ = 2 * C * cubeAverage R (coefficientEnergyDensity a u) := by
                        ring
      _ =
            2 * C *
              descendantsAverage Q n
                (fun R => cubeAverage R (coefficientEnergyDensity a u)) := by
                rw [descendantsAverage_smul Q n (2 * C)
                  (fun R => cubeAverage R (coefficientEnergyDensity a u))]
  have hpartition :
      cubeAverage Q (coefficientEnergyDensity a u) =
        descendantsAverage Q n
          (fun R => cubeAverage R (coefficientEnergyDensity a u)) :=
    cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q n
      (coefficientEnergyDensity a u) hint
  simpa [C, hpartition] using hbase

/-- The depth weight cancels the half-scale coefficient growth in the averaged
`u` coefficient-energy component. -/
theorem weakFluxRHSDepthWeight_mul_coefficientEnergyErrorAverage_le_parentHalfLambda_globalAverage
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (u : Vec d → Vec d) {s lam Lam : ℝ} (n : ℕ)
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_half :
      Summable (fun m : ℕ =>
        geometricWeight (s / 2) 2 m *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (m : ℤ)) a) 1))
    (havg_nonneg :
      ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a u))
    (hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a u) (cubeSet Q)
        MeasureTheory.volume) :
    coarsePoincareRHSDepthWeight s n *
      weakFluxRHSLocalCoefficientEnergyErrorAverage Q a u s n ≤
      2 * (geometricDiscount s 2)⁻¹ *
        LambdaSq Q (s / 2) (.finite 2) a *
        cubeAverage Q (coefficientEnergyDensity a u) := by
  have hlocal :=
    weakFluxRHSLocalCoefficientEnergyErrorAverage_le_parentHalfLambda_globalAverage
      Q a u n hs hEll hData hsum_half havg_nonneg hint
  have hweight_nonneg : 0 ≤ coarsePoincareRHSDepthWeight s n := by
    unfold coarsePoincareRHSDepthWeight
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hmul := mul_le_mul_of_nonneg_left hlocal hweight_nonneg
  have hcancel :
      coarsePoincareRHSDepthWeight s n *
        Real.rpow (3 : ℝ) (s * (n : ℝ)) = 1 := by
    unfold coarsePoincareRHSDepthWeight
    calc
      Real.rpow (3 : ℝ) (-s * (n : ℝ)) *
          Real.rpow (3 : ℝ) (s * (n : ℝ))
          = Real.rpow (3 : ℝ) ((-s * (n : ℝ)) + s * (n : ℝ)) := by
            exact (Real.rpow_add (by norm_num : 0 < (3 : ℝ))
              (-s * (n : ℝ)) (s * (n : ℝ))).symm
      _ = 1 := by
            have hsum : (-s * (n : ℝ)) + s * (n : ℝ) = 0 := by ring
            rw [hsum]
            simp
  calc
    coarsePoincareRHSDepthWeight s n *
        weakFluxRHSLocalCoefficientEnergyErrorAverage Q a u s n
        ≤
          coarsePoincareRHSDepthWeight s n *
            (2 * ((geometricDiscount s 2)⁻¹ *
              (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
                LambdaSq Q (s / 2) (.finite 2) a)) *
              cubeAverage Q (coefficientEnergyDensity a u)) := hmul
    _ =
          (coarsePoincareRHSDepthWeight s n *
            Real.rpow (3 : ℝ) (s * (n : ℝ))) *
            (2 * (geometricDiscount s 2)⁻¹ *
              LambdaSq Q (s / 2) (.finite 2) a *
              cubeAverage Q (coefficientEnergyDensity a u)) := by
            ring
    _ =
          2 * (geometricDiscount s 2)⁻¹ *
            LambdaSq Q (s / 2) (.finite 2) a *
            cubeAverage Q (coefficientEnergyDensity a u) := by
            rw [hcancel]
            ring

/-- The localized coefficient-energy average supplies the uniform component-base
input needed by the weak-flux global wrappers. -/
theorem weakFluxRHSDepthWeight_mul_coefficientEnergyErrorAverage_le_weightedCoefficientEnergyBase
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (u : Vec d → Vec d) {s lam Lam : ℝ} (n : ℕ)
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_half :
      Summable (fun m : ℕ =>
        geometricWeight (s / 2) 2 m *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (m : ℤ)) a) 1))
    (havg_nonneg :
      ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a u))
    (hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a u) (cubeSet Q)
        MeasureTheory.volume) :
    coarsePoincareRHSDepthWeight s n *
      weakFluxRHSLocalCoefficientEnergyErrorAverage Q a u s n ≤
      weakFluxRHSWeightedCoefficientEnergyBase Q a u s := by
  simpa [weakFluxRHSWeightedCoefficientEnergyBase] using
    weakFluxRHSDepthWeight_mul_coefficientEnergyErrorAverage_le_parentHalfLambda_globalAverage
      Q a u n hs hEll hData hsum_half havg_nonneg hint

/-- Averaging preserves the corrector-energy component split. -/
theorem weakFluxRHSCorrectorEnergyErrorAverage_eq_components {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d)
    (z : TriadicCube d → Vec d → Vec d) (s : ℝ) (n : ℕ) :
    weakFluxRHSCorrectorEnergyErrorAverage Q a u z s n =
      weakFluxRHSLocalCoefficientEnergyErrorAverage Q a u s n +
        weakFluxRHSLocalCorrectorEnergyErrorAverage Q a z s n := by
  simp [weakFluxRHSCorrectorEnergyErrorAverage,
    weakFluxRHSLocalCoefficientEnergyErrorAverage,
    weakFluxRHSLocalCorrectorEnergyErrorAverage,
    weakFluxRHSCorrectorEnergyLocalError_eq_components,
    descendantsAverage_add]

/-- Averaging preserves the absorbed component split. -/
theorem weakFluxRHSAbsorbedErrorAverage_eq_components {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g u : Vec d → Vec d)
    (v : TriadicCube d → Vec d → Vec d) (s η : ℝ) (n : ℕ) :
    weakFluxRHSAbsorbedErrorAverage Q a g u v s η n =
      weakFluxRHSLocalCoefficientEnergyErrorAverage Q a u s n +
        weakFluxRHSLocalUSeminormErrorAverage Q u s η n +
          weakFluxRHSLocalHarmonicSeminormErrorAverage Q v s η n +
            weakFluxRHSLocalForceErrorAverage Q a g s η n := by
  simp [weakFluxRHSAbsorbedErrorAverage,
    weakFluxRHSLocalCoefficientEnergyErrorAverage,
    weakFluxRHSLocalUSeminormErrorAverage,
    weakFluxRHSLocalHarmonicSeminormErrorAverage,
    weakFluxRHSLocalForceErrorAverage,
    weakFluxRHSAbsorbedLocalError_eq_components,
    descendantsAverage_add, add_assoc]

/-- Weighted component bounds imply a weighted bound for the corrector-energy
local-error envelope. -/
theorem weakFluxRHSCorrectorEnergyErrorAverage_weighted_le_add_of_components
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (u : Vec d → Vec d) (z : TriadicCube d → Vec d → Vec d)
    (s : ℝ) (n : ℕ) {Bcoeff Bcorr : ℝ}
    (hcoeff :
      coarsePoincareRHSDepthWeight s n *
        weakFluxRHSLocalCoefficientEnergyErrorAverage Q a u s n ≤ Bcoeff)
    (hcorr :
      coarsePoincareRHSDepthWeight s n *
        weakFluxRHSLocalCorrectorEnergyErrorAverage Q a z s n ≤ Bcorr) :
    coarsePoincareRHSDepthWeight s n *
      descendantsAverage Q n
        (fun R => weakFluxRHSCorrectorEnergyLocalError R a u (z R) s) ≤
      Bcoeff + Bcorr := by
  calc
    coarsePoincareRHSDepthWeight s n *
        descendantsAverage Q n
          (fun R => weakFluxRHSCorrectorEnergyLocalError R a u (z R) s)
        =
          coarsePoincareRHSDepthWeight s n *
            weakFluxRHSCorrectorEnergyErrorAverage Q a u z s n := by
            rfl
    _ =
          coarsePoincareRHSDepthWeight s n *
            (weakFluxRHSLocalCoefficientEnergyErrorAverage Q a u s n +
              weakFluxRHSLocalCorrectorEnergyErrorAverage Q a z s n) := by
            rw [weakFluxRHSCorrectorEnergyErrorAverage_eq_components]
    _ =
          coarsePoincareRHSDepthWeight s n *
            weakFluxRHSLocalCoefficientEnergyErrorAverage Q a u s n +
          coarsePoincareRHSDepthWeight s n *
            weakFluxRHSLocalCorrectorEnergyErrorAverage Q a z s n := by
            ring
    _ ≤ Bcoeff + Bcorr := add_le_add hcoeff hcorr

/-- Weighted component bounds imply a weighted bound for the absorbed
local-error envelope. -/
theorem weakFluxRHSAbsorbedErrorAverage_weighted_le_add_of_components
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (g u : Vec d → Vec d) (v : TriadicCube d → Vec d → Vec d)
    (s η : ℝ) (n : ℕ) {Bcoeff Bu Bv Bforce : ℝ}
    (hcoeff :
      coarsePoincareRHSDepthWeight s n *
        weakFluxRHSLocalCoefficientEnergyErrorAverage Q a u s n ≤ Bcoeff)
    (hu :
      coarsePoincareRHSDepthWeight s n *
        weakFluxRHSLocalUSeminormErrorAverage Q u s η n ≤ Bu)
    (hv :
      coarsePoincareRHSDepthWeight s n *
        weakFluxRHSLocalHarmonicSeminormErrorAverage Q v s η n ≤ Bv)
    (hforce :
      coarsePoincareRHSDepthWeight s n *
        weakFluxRHSLocalForceErrorAverage Q a g s η n ≤ Bforce) :
    coarsePoincareRHSDepthWeight s n *
      descendantsAverage Q n
        (fun R => weakFluxRHSAbsorbedLocalError R a g u (v R) s η) ≤
      Bcoeff + Bu + Bv + Bforce := by
  calc
    coarsePoincareRHSDepthWeight s n *
        descendantsAverage Q n
          (fun R => weakFluxRHSAbsorbedLocalError R a g u (v R) s η)
        =
          coarsePoincareRHSDepthWeight s n *
            weakFluxRHSAbsorbedErrorAverage Q a g u v s η n := by
            rfl
    _ =
          coarsePoincareRHSDepthWeight s n *
            (weakFluxRHSLocalCoefficientEnergyErrorAverage Q a u s n +
              weakFluxRHSLocalUSeminormErrorAverage Q u s η n +
                weakFluxRHSLocalHarmonicSeminormErrorAverage Q v s η n +
                  weakFluxRHSLocalForceErrorAverage Q a g s η n) := by
            rw [weakFluxRHSAbsorbedErrorAverage_eq_components]
    _ =
          coarsePoincareRHSDepthWeight s n *
            weakFluxRHSLocalCoefficientEnergyErrorAverage Q a u s n +
          coarsePoincareRHSDepthWeight s n *
            weakFluxRHSLocalUSeminormErrorAverage Q u s η n +
          coarsePoincareRHSDepthWeight s n *
            weakFluxRHSLocalHarmonicSeminormErrorAverage Q v s η n +
          coarsePoincareRHSDepthWeight s n *
            weakFluxRHSLocalForceErrorAverage Q a g s η n := by
            ring
    _ ≤ Bcoeff + Bu + Bv + Bforce :=
        add_le_add (add_le_add (add_le_add hcoeff hu) hv) hforce

end

end Homogenization
