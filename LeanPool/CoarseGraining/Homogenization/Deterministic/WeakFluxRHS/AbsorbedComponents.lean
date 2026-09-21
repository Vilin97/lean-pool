/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.ForceLocalization
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.GlobalIteration

/-! # Absorbed Components -/

namespace Homogenization

noncomputable section

/-- Explicit non-child error envelope in the absorbed weak-flux RHS recurrence.

This is the local Section 3.2.3 error produced after absorbing the short
corrector product into the `u`, harmonic-remainder, and centered-forcing
quadratic terms. -/
noncomputable def weakFluxRHSAbsorbedLocalError {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g u v : Vec d → Vec d)
    (s η : ℝ) : ℝ :=
  let C : ℝ := (geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a
  let K : ℝ := C * ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))
  2 * C * cubeAverage Q (coefficientEnergyDensity a u) +
    η * (cubeBesovNegativeVectorSeminormTwo Q s u) ^ 2 +
    η * (cubeBesovNegativeVectorSeminormTwo Q s v) ^ 2 +
    2 * η⁻¹ *
      ((K * cubeBesovPositiveVectorSeminormTwo Q s
        (fun x => g x - cubeAverageVec Q g)) ^ 2)

/-- Explicit non-child error envelope in the corrector-energy weak-flux RHS
recurrence, before the corrector energy is converted into Besov forcing
terms. -/
noncomputable def weakFluxRHSCorrectorEnergyLocalError {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u z : Vec d → Vec d)
    (s : ℝ) : ℝ :=
  let C : ℝ := (geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a
  2 * C * cubeAverage Q (coefficientEnergyDensity a u) +
    2 * C * cubeAverage Q (coefficientEnergyDensity a z)

/-- Local coefficient multiplying the weak-flux RHS error terms. -/
noncomputable def weakFluxRHSLocalCoeff {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) : ℝ :=
  (geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a

/-- The weak-flux local coefficient is nonnegative for positive regularity. -/
theorem weakFluxRHSLocalCoeff_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {s : ℝ} (hs : 0 < s) :
    0 ≤ weakFluxRHSLocalCoeff Q a s := by
  unfold weakFluxRHSLocalCoeff
  have hs2 : 0 < s * (2 : ℝ) := by nlinarith
  exact mul_nonneg
    (inv_nonneg.mpr (le_of_lt (geometricDiscount_pos hs2)))
    (multiscale_ellipticity_LambdaSq_finite_nonneg Q s 2 a (by norm_num) hs2.le)

/-- Parent half-scale coefficient used after localizing `Lambda_{s,2}`. -/
noncomputable def weakFluxRHSParentHalfCoeff {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) (n : ℕ) : ℝ :=
  (geometricDiscount s 2)⁻¹ *
    (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
      LambdaSq Q (s / 2) (.finite 2) a)

/-- Parent half-scale weak-flux coefficient grows by `3^s` when the descendant
depth is incremented. -/
theorem weakFluxRHSParentHalfCoeff_succ
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) (n : ℕ) :
    weakFluxRHSParentHalfCoeff Q a s (n + 1) =
      Real.rpow (3 : ℝ) s * weakFluxRHSParentHalfCoeff Q a s n := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  have hparent :
      Real.rpow (3 : ℝ) (s * ((n + 1 : ℕ) : ℝ)) =
        Real.rpow (3 : ℝ) s * Real.rpow (3 : ℝ) (s * (n : ℝ)) := by
    have hexp :
        s * ((n + 1 : ℕ) : ℝ) = s + s * (n : ℝ) := by
      norm_num
      ring
    calc
      Real.rpow (3 : ℝ) (s * ((n + 1 : ℕ) : ℝ)) =
          Real.rpow (3 : ℝ) (s + s * (n : ℝ)) := by
            rw [hexp]
      _ = Real.rpow (3 : ℝ) s *
            Real.rpow (3 : ℝ) (s * (n : ℝ)) := by
            exact Real.rpow_add h3 s (s * (n : ℝ))
  unfold weakFluxRHSParentHalfCoeff
  rw [hparent]
  ring

/-- Half-scale localization of the local coefficient multiplying the weak-flux
RHS error terms. -/
theorem weakFluxRHSLocalCoeff_le_parentHalfLambda_of_mem_descendantsAtDepth
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} (a : CoeffField d)
    {n : ℕ} {s lam Lam : ℝ}
    (hs : 0 < s)
    (hR : R ∈ descendantsAtDepth Q n)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_half :
      Summable (fun m : ℕ =>
        geometricWeight (s / 2) 2 m *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (m : ℤ)) a) 1)) :
    weakFluxRHSLocalCoeff R a s ≤
      (geometricDiscount s 2)⁻¹ *
        (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
          LambdaSq Q (s / 2) (.finite 2) a) := by
  have hs2 : 0 < s * (2 : ℝ) := by nlinarith
  have hdisc_nonneg : 0 ≤ (geometricDiscount s 2)⁻¹ :=
    inv_nonneg.mpr (le_of_lt (geometricDiscount_pos hs2))
  have hRscale : R ∈ descendantsAtScale Q (Q.scale - (n : ℤ)) :=
    mem_descendantsAtScale_of_mem_descendantsAtDepth hR
  have hLambda :
      LambdaSq R s (.finite 2) a ≤
        Real.rpow (3 : ℝ)
            (s * (Int.toNat (Q.scale - (Q.scale - (n : ℤ))) : ℝ)) *
          LambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_LambdaSq_two_le_rpow_s_of_mem_descendantsAtScale_of_half_of_isEllipticFieldOn_of_isSigmaCoarse
      (Q := Q) (R := R) (k := Q.scale - (n : ℤ)) a hs hRscale hEll hData hsum_half
  have htoNat :
      Int.toNat (Q.scale - (Q.scale - (n : ℤ))) = n := by
    have hdiff : Q.scale - (Q.scale - (n : ℤ)) = (n : ℤ) := by
      omega
    rw [hdiff]
    simp
  unfold weakFluxRHSLocalCoeff
  refine mul_le_mul_of_nonneg_left ?_ hdisc_nonneg
  simpa [htoNat] using hLambda

/-- Parent half-scale forcing multiplier used after localizing `Lambda_{s,2}`. -/
noncomputable def weakFluxRHSParentHalfForceMultiplier {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) (n : ℕ) : ℝ :=
  weakFluxRHSParentHalfCoeff Q a s n *
    ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))

/-- Parent half-scale weak-flux forcing multiplier grows by `3^s` when the
descendant depth is incremented. -/
theorem weakFluxRHSParentHalfForceMultiplier_succ
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) (n : ℕ) :
    weakFluxRHSParentHalfForceMultiplier Q a s (n + 1) =
      Real.rpow (3 : ℝ) s *
        weakFluxRHSParentHalfForceMultiplier Q a s n := by
  unfold weakFluxRHSParentHalfForceMultiplier
  rw [weakFluxRHSParentHalfCoeff_succ Q a s n]
  ring

/-- The geometric multiplier attached to the centered forcing seminorm in the
absorbed weak-flux RHS error. -/
noncomputable def weakFluxRHSLocalForceMultiplier {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) : ℝ :=
  weakFluxRHSLocalCoeff Q a s *
    ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))

/-- Local forcing multipliers are controlled by any upper bound on the local
weak-flux coefficient. -/
theorem weakFluxRHSLocalForceMultiplier_sq_le_of_localCoeffBound {d : ℕ}
    (R : TriadicCube d) (a : CoeffField d) {s C : ℝ}
    (hs : 0 < s)
    (hcoeff : weakFluxRHSLocalCoeff R a s ≤ C) :
    (weakFluxRHSLocalForceMultiplier R a s) ^ 2 ≤
      (C * ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))) ^ 2 := by
  let P : ℝ := (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg
      (by exact_mod_cast Nat.zero_le d)
      (mul_nonneg
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
        (Real.sqrt_nonneg 2))
  have hlocal_nonneg :
      0 ≤ weakFluxRHSLocalForceMultiplier R a s := by
    unfold weakFluxRHSLocalForceMultiplier
    exact mul_nonneg (weakFluxRHSLocalCoeff_nonneg R a hs) hP_nonneg
  have hle :
      weakFluxRHSLocalForceMultiplier R a s ≤ C * P := by
    unfold weakFluxRHSLocalForceMultiplier
    exact mul_le_mul_of_nonneg_right hcoeff hP_nonneg
  simpa [P] using pow_le_pow_left₀ hlocal_nonneg hle 2

/-- Half-scale localization of the weak-flux forcing multiplier on descendants. -/
theorem weakFluxRHSLocalForceMultiplier_sq_le_parentHalfLambda_of_mem_descendantsAtDepth
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} (a : CoeffField d)
    {s lam Lam : ℝ} (n : ℕ) (hs : 0 < s)
    (hR : R ∈ descendantsAtDepth Q n)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_half :
      Summable (fun m : ℕ =>
        geometricWeight (s / 2) 2 m *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (m : ℤ)) a) 1)) :
    (weakFluxRHSLocalForceMultiplier R a s) ^ 2 ≤
      (weakFluxRHSParentHalfForceMultiplier Q a s n) ^ 2 := by
  simpa [weakFluxRHSParentHalfCoeff, weakFluxRHSParentHalfForceMultiplier] using
    weakFluxRHSLocalForceMultiplier_sq_le_of_localCoeffBound
      R a hs
      (weakFluxRHSLocalCoeff_le_parentHalfLambda_of_mem_descendantsAtDepth
        (Q := Q) (R := R) a hs hR hEll hData hsum_half)

/-- Centered positive Besov forcing seminorm used by the absorbed weak-flux
RHS error. -/
noncomputable def weakFluxRHSLocalCenteredForceSeminorm {d : ℕ}
    (Q : TriadicCube d) (g : Vec d → Vec d) (s : ℝ) : ℝ :=
  cubeBesovPositiveVectorSeminormTwo Q s (fun x => g x - cubeAverageVec Q g)

/-- The `u` coefficient-energy contribution to the local weak-flux RHS error. -/
noncomputable def weakFluxRHSLocalCoefficientEnergyError {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d)
    (s : ℝ) : ℝ :=
  2 * weakFluxRHSLocalCoeff Q a s *
    cubeAverage Q (coefficientEnergyDensity a u)

/-- The corrector coefficient-energy contribution to the local weak-flux RHS
error. -/
noncomputable def weakFluxRHSLocalCorrectorEnergyError {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (z : Vec d → Vec d)
    (s : ℝ) : ℝ :=
  2 * weakFluxRHSLocalCoeff Q a s *
    cubeAverage Q (coefficientEnergyDensity a z)

/-- The absorbed `u` negative-Besov contribution to the local weak-flux RHS
error. -/
noncomputable def weakFluxRHSLocalUSeminormError {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) (s η : ℝ) : ℝ :=
  η * (cubeBesovNegativeVectorSeminormTwo Q s u) ^ 2

/-- The absorbed harmonic-remainder negative-Besov contribution to the local
weak-flux RHS error. -/
noncomputable def weakFluxRHSLocalHarmonicSeminormError {d : ℕ}
    (Q : TriadicCube d) (v : Vec d → Vec d) (s η : ℝ) : ℝ :=
  η * (cubeBesovNegativeVectorSeminormTwo Q s v) ^ 2

/-- The absorbed centered-forcing contribution to the local weak-flux RHS
error. -/
noncomputable def weakFluxRHSLocalForceError {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    (s η : ℝ) : ℝ :=
  2 * η⁻¹ *
    ((weakFluxRHSLocalForceMultiplier Q a s *
      weakFluxRHSLocalCenteredForceSeminorm Q g s) ^ 2)

/-- The corrector-energy local weak-flux RHS error is exactly the sum of its
two coefficient-energy components. -/
theorem weakFluxRHSCorrectorEnergyLocalError_eq_components {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u z : Vec d → Vec d)
    (s : ℝ) :
    weakFluxRHSCorrectorEnergyLocalError Q a u z s =
      weakFluxRHSLocalCoefficientEnergyError Q a u s +
        weakFluxRHSLocalCorrectorEnergyError Q a z s := by
  simp [weakFluxRHSCorrectorEnergyLocalError,
    weakFluxRHSLocalCoefficientEnergyError,
    weakFluxRHSLocalCorrectorEnergyError, weakFluxRHSLocalCoeff]

/-- The absorbed local weak-flux RHS error is exactly the sum of its named
coefficient-energy, absorbed seminorm, and centered-forcing components. -/
theorem weakFluxRHSAbsorbedLocalError_eq_components {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g u v : Vec d → Vec d)
    (s η : ℝ) :
    weakFluxRHSAbsorbedLocalError Q a g u v s η =
      weakFluxRHSLocalCoefficientEnergyError Q a u s +
        weakFluxRHSLocalUSeminormError Q u s η +
          weakFluxRHSLocalHarmonicSeminormError Q v s η +
            weakFluxRHSLocalForceError Q a g s η := by
  simp [weakFluxRHSAbsorbedLocalError,
    weakFluxRHSLocalCoefficientEnergyError,
    weakFluxRHSLocalUSeminormError,
    weakFluxRHSLocalHarmonicSeminormError,
    weakFluxRHSLocalForceError,
    weakFluxRHSLocalForceMultiplier,
    weakFluxRHSLocalCenteredForceSeminorm,
    weakFluxRHSLocalCoeff]

/-- Descendant average of the corrector-energy weak-flux RHS error. -/
noncomputable def weakFluxRHSCorrectorEnergyErrorAverage {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d)
    (z : TriadicCube d → Vec d → Vec d) (s : ℝ) (n : ℕ) : ℝ :=
  descendantsAverage Q n fun R =>
    weakFluxRHSCorrectorEnergyLocalError R a u (z R) s

/-- Descendant average of the absorbed weak-flux RHS error. -/
noncomputable def weakFluxRHSAbsorbedErrorAverage {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g u : Vec d → Vec d)
    (v : TriadicCube d → Vec d → Vec d) (s η : ℝ) (n : ℕ) : ℝ :=
  descendantsAverage Q n fun R =>
    weakFluxRHSAbsorbedLocalError R a g u (v R) s η

/-- Descendant average of the `u` coefficient-energy component. -/
noncomputable def weakFluxRHSLocalCoefficientEnergyErrorAverage {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d)
    (s : ℝ) (n : ℕ) : ℝ :=
  descendantsAverage Q n fun R =>
    weakFluxRHSLocalCoefficientEnergyError R a u s

/-- Descendant average of the corrector coefficient-energy component. -/
noncomputable def weakFluxRHSLocalCorrectorEnergyErrorAverage {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d)
    (z : TriadicCube d → Vec d → Vec d) (s : ℝ) (n : ℕ) : ℝ :=
  descendantsAverage Q n fun R =>
    weakFluxRHSLocalCorrectorEnergyError R a (z R) s

/-- Descendant average of the absorbed `u` negative-Besov component. -/
noncomputable def weakFluxRHSLocalUSeminormErrorAverage {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) (s η : ℝ) (n : ℕ) : ℝ :=
  descendantsAverage Q n fun R =>
    weakFluxRHSLocalUSeminormError R u s η

/-- Descendant average of the absorbed harmonic-remainder negative-Besov
component. -/
noncomputable def weakFluxRHSLocalHarmonicSeminormErrorAverage {d : ℕ}
    (Q : TriadicCube d) (v : TriadicCube d → Vec d → Vec d)
    (s η : ℝ) (n : ℕ) : ℝ :=
  descendantsAverage Q n fun R =>
    weakFluxRHSLocalHarmonicSeminormError R (v R) s η

/-- Averaged negative-Besov size of a depth-dependent harmonic remainder. -/
noncomputable def weakFluxRHSHarmonicRemainderAveragedSeminormSq {d : ℕ}
    (Q : TriadicCube d) (s : ℝ)
    (v : TriadicCube d → Vec d → Vec d) (n : ℕ) : ℝ :=
  descendantsAverage Q n fun R => (cubeBesovNegativeVectorSeminormTwo R s (v R)) ^ 2

/-- Scaled averaged negative-Besov size of a depth-dependent harmonic
remainder. -/
noncomputable def weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq {d : ℕ}
    (Q : TriadicCube d) (s : ℝ)
    (v : TriadicCube d → Vec d → Vec d) (n : ℕ) : ℝ :=
  coarsePoincareRHSDepthWeight s n *
    weakFluxRHSHarmonicRemainderAveragedSeminormSq Q s v n

/-- Descendantwise squared bounds control the averaged varying-cube harmonic
remainder size. -/
theorem weakFluxRHSHarmonicRemainderAveragedSeminormSq_le_of_descendant_sq_bound
    {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (v : TriadicCube d → Vec d → Vec d) (n : ℕ) {B : ℝ}
    (hbound :
      ∀ R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s (v R)) ^ 2 ≤ B) :
    weakFluxRHSHarmonicRemainderAveragedSeminormSq Q s v n ≤ B := by
  unfold weakFluxRHSHarmonicRemainderAveragedSeminormSq
  calc
    descendantsAverage Q n
        (fun R => (cubeBesovNegativeVectorSeminormTwo R s (v R)) ^ 2)
        ≤ descendantsAverage Q n (fun _ => B) := by
          exact descendantsAverage_le_descendantsAverage Q n hbound
    _ = B := by
          exact descendantsAverage_const_eq Q n B

/-- Descendantwise squared bounds at the reciprocal depth-weight scale control
the scaled varying-cube harmonic remainder size. -/
theorem weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq_le_of_descendant_scaled_sq_bound
    {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (v : TriadicCube d → Vec d → Vec d) (n : ℕ) {B : ℝ}
    (hbound :
      ∀ R ∈ descendantsAtDepth Q n,
        (cubeBesovNegativeVectorSeminormTwo R s (v R)) ^ 2 ≤
          (coarsePoincareRHSDepthWeight s n)⁻¹ * B) :
    weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq Q s v n ≤ B := by
  have havg :
      weakFluxRHSHarmonicRemainderAveragedSeminormSq Q s v n ≤
        (coarsePoincareRHSDepthWeight s n)⁻¹ * B :=
    weakFluxRHSHarmonicRemainderAveragedSeminormSq_le_of_descendant_sq_bound
      Q s v n hbound
  have hweight_nonneg : 0 ≤ coarsePoincareRHSDepthWeight s n := by
    unfold coarsePoincareRHSDepthWeight
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hweight_pos : 0 < coarsePoincareRHSDepthWeight s n := by
    unfold coarsePoincareRHSDepthWeight
    exact Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _
  unfold weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq
  calc
    coarsePoincareRHSDepthWeight s n *
        weakFluxRHSHarmonicRemainderAveragedSeminormSq Q s v n
        ≤ coarsePoincareRHSDepthWeight s n *
            ((coarsePoincareRHSDepthWeight s n)⁻¹ * B) := by
          exact mul_le_mul_of_nonneg_left havg hweight_nonneg
    _ = B := by
          field_simp [hweight_pos.ne']

/-- Tail form of
`weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq_le_of_descendant_scaled_sq_bound`. -/
theorem weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq_tail_le_of_descendant_scaled_sq_bound
    {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (v : TriadicCube d → Vec d → Vec d) (m : ℕ) {B : ℝ}
    (hbound :
      ∀ k : ℕ, ∀ R ∈ descendantsAtDepth Q (m + k),
        (cubeBesovNegativeVectorSeminormTwo R s (v R)) ^ 2 ≤
          (coarsePoincareRHSDepthWeight s (m + k))⁻¹ * B) :
    ∀ k : ℕ,
      weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq Q s v (m + k) ≤ B := by
  intro k
  exact
    weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq_le_of_descendant_scaled_sq_bound
      Q s v (m + k) (hbound k)

/-- The averaged absorbed `u` seminorm component is exactly `η R_n`. -/
theorem weakFluxRHSLocalUSeminormErrorAverage_eq_eta_mul_coarsePoincareRHSRn
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d)
    (s η : ℝ) (n : ℕ) :
    weakFluxRHSLocalUSeminormErrorAverage Q u s η n =
      η * coarsePoincareRHSRn Q s u n := by
  unfold weakFluxRHSLocalUSeminormErrorAverage weakFluxRHSLocalUSeminormError
    coarsePoincareRHSRn
  exact descendantsAverage_smul Q n η
    (fun R => (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2)

/-- The depth-weighted absorbed `u` seminorm component is exactly `η S_n`. -/
theorem weakFluxRHSDepthWeight_mul_uSeminormErrorAverage_eq_eta_mul_coarsePoincareRHSSn
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d)
    (s η : ℝ) (n : ℕ) :
    coarsePoincareRHSDepthWeight s n *
        weakFluxRHSLocalUSeminormErrorAverage Q u s η n =
      η * coarsePoincareRHSSn Q s u n := by
  rw [weakFluxRHSLocalUSeminormErrorAverage_eq_eta_mul_coarsePoincareRHSRn]
  unfold coarsePoincareRHSSn
  ring

/-- The averaged absorbed harmonic-remainder seminorm component is exactly
`η` times its varying-cube averaged seminorm. -/
theorem weakFluxRHSLocalHarmonicSeminormErrorAverage_eq_eta_mul_harmonicRemainder
    {d : ℕ} (Q : TriadicCube d) (v : TriadicCube d → Vec d → Vec d)
    (s η : ℝ) (n : ℕ) :
    weakFluxRHSLocalHarmonicSeminormErrorAverage Q v s η n =
      η * weakFluxRHSHarmonicRemainderAveragedSeminormSq Q s v n := by
  unfold weakFluxRHSLocalHarmonicSeminormErrorAverage
    weakFluxRHSLocalHarmonicSeminormError
    weakFluxRHSHarmonicRemainderAveragedSeminormSq
  exact descendantsAverage_smul Q n η
    (fun R => (cubeBesovNegativeVectorSeminormTwo R s (v R)) ^ 2)

/-- The depth-weighted absorbed harmonic-remainder seminorm component is
exactly `η` times its scaled varying-cube averaged seminorm. -/
theorem weakFluxRHSDepthWeight_mul_harmonicSeminormErrorAverage_eq_eta_mul_harmonicRemainderScaled
    {d : ℕ} (Q : TriadicCube d) (v : TriadicCube d → Vec d → Vec d)
    (s η : ℝ) (n : ℕ) :
    coarsePoincareRHSDepthWeight s n *
        weakFluxRHSLocalHarmonicSeminormErrorAverage Q v s η n =
      η * weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq Q s v n := by
  rw [weakFluxRHSLocalHarmonicSeminormErrorAverage_eq_eta_mul_harmonicRemainder]
  unfold weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq
  ring

/-- Any bound on `S_n` gives the corresponding weighted absorbed `u` component
bound after multiplying by `η`. -/
theorem weakFluxRHSDepthWeight_mul_uSeminormErrorAverage_le_eta_mul_base
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d)
    (s : ℝ) {η B : ℝ} (n : ℕ)
    (hη_nonneg : 0 ≤ η)
    (hbase : coarsePoincareRHSSn Q s u n ≤ B) :
    coarsePoincareRHSDepthWeight s n *
        weakFluxRHSLocalUSeminormErrorAverage Q u s η n ≤
      η * B := by
  rw [weakFluxRHSDepthWeight_mul_uSeminormErrorAverage_eq_eta_mul_coarsePoincareRHSSn]
  exact mul_le_mul_of_nonneg_left hbase hη_nonneg

/-- Uniform tail bounds on `S_{m+k}` give the corresponding absorbed `u`
component bounds along the iteration tail. -/
theorem weakFluxRHSDepthWeight_mul_uSeminormErrorAverage_le_eta_mul_base_of_tail
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d)
    (s : ℝ) {η B : ℝ} (m k : ℕ)
    (hη_nonneg : 0 ≤ η)
    (hbase : ∀ l : ℕ, coarsePoincareRHSSn Q s u (m + l) ≤ B) :
    coarsePoincareRHSDepthWeight s (m + k) *
        weakFluxRHSLocalUSeminormErrorAverage Q u s η (m + k) ≤
      η * B := by
  exact weakFluxRHSDepthWeight_mul_uSeminormErrorAverage_le_eta_mul_base
    Q u s (m + k) hη_nonneg (hbase k)

/-- Any scaled varying-cube harmonic-remainder bound gives the corresponding
weighted absorbed harmonic component bound after multiplying by `η`. -/
theorem weakFluxRHSDepthWeight_mul_harmonicSeminormErrorAverage_le_eta_mul_base
    {d : ℕ} (Q : TriadicCube d)
    (v : TriadicCube d → Vec d → Vec d) (s : ℝ) {η B : ℝ} (n : ℕ)
    (hη_nonneg : 0 ≤ η)
    (hbase : weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq Q s v n ≤ B) :
    coarsePoincareRHSDepthWeight s n *
        weakFluxRHSLocalHarmonicSeminormErrorAverage Q v s η n ≤
      η * B := by
  rw [weakFluxRHSDepthWeight_mul_harmonicSeminormErrorAverage_eq_eta_mul_harmonicRemainderScaled]
  exact mul_le_mul_of_nonneg_left hbase hη_nonneg

/-- Uniform tail bounds on the scaled harmonic-remainder seminorm give the
corresponding absorbed harmonic component bounds along the iteration tail. -/
theorem weakFluxRHSDepthWeight_mul_harmonicSeminormErrorAverage_le_eta_mul_base_of_tail
    {d : ℕ} (Q : TriadicCube d)
    (v : TriadicCube d → Vec d → Vec d) (s : ℝ) {η B : ℝ} (m k : ℕ)
    (hη_nonneg : 0 ≤ η)
    (hbase : ∀ l : ℕ,
      weakFluxRHSHarmonicRemainderScaledAveragedSeminormSq Q s v (m + l) ≤ B) :
    coarsePoincareRHSDepthWeight s (m + k) *
        weakFluxRHSLocalHarmonicSeminormErrorAverage Q v s η (m + k) ≤
      η * B := by
  exact weakFluxRHSDepthWeight_mul_harmonicSeminormErrorAverage_le_eta_mul_base
    Q v s (m + k) hη_nonneg (hbase k)

/-- Descendant average of the absorbed centered-forcing component. -/
noncomputable def weakFluxRHSLocalForceErrorAverage {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    (s η : ℝ) (n : ℕ) : ℝ :=
  descendantsAverage Q n fun R =>
    weakFluxRHSLocalForceError R a g s η

/-- Average forcing component controlled by a uniform multiplier-square bound. -/
theorem weakFluxRHSLocalForceErrorAverage_le_of_multiplierSqBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    (s : ℝ) {η : ℝ} (n : ℕ) {K2 : ℝ}
    (hη : 0 < η)
    (hmult :
      ∀ R ∈ descendantsAtDepth Q n,
        (weakFluxRHSLocalForceMultiplier R a s) ^ 2 ≤ K2) :
    weakFluxRHSLocalForceErrorAverage Q a g s η n ≤
      2 * η⁻¹ *
        (K2 *
          descendantsAverage Q n
            (fun R => (weakFluxRHSLocalCenteredForceSeminorm R g s) ^ 2)) := by
  have hfactor_nonneg : 0 ≤ 2 * η⁻¹ :=
    mul_nonneg (by norm_num) (inv_nonneg.mpr hη.le)
  unfold weakFluxRHSLocalForceErrorAverage
  calc
    descendantsAverage Q n (fun R => weakFluxRHSLocalForceError R a g s η)
        ≤
          descendantsAverage Q n
            (fun R =>
              2 * η⁻¹ *
                (K2 * (weakFluxRHSLocalCenteredForceSeminorm R g s) ^ 2)) := by
              refine descendantsAverage_le_descendantsAverage Q n ?_
              intro R hR
              unfold weakFluxRHSLocalForceError
              calc
                2 * η⁻¹ *
                    ((weakFluxRHSLocalForceMultiplier R a s *
                      weakFluxRHSLocalCenteredForceSeminorm R g s) ^ 2)
                    =
                      2 * η⁻¹ *
                        ((weakFluxRHSLocalForceMultiplier R a s) ^ 2 *
                          (weakFluxRHSLocalCenteredForceSeminorm R g s) ^ 2) := by
                        ring
                _ ≤
                      2 * η⁻¹ *
                        (K2 * (weakFluxRHSLocalCenteredForceSeminorm R g s) ^ 2) := by
                        exact mul_le_mul_of_nonneg_left
                          (mul_le_mul_of_nonneg_right (hmult R hR) (sq_nonneg _))
                          hfactor_nonneg
    _ =
          2 * η⁻¹ *
            (K2 *
              descendantsAverage Q n
                (fun R => (weakFluxRHSLocalCenteredForceSeminorm R g s) ^ 2)) := by
          rw [descendantsAverage_smul Q n (2 * η⁻¹)
            (fun R => K2 * (weakFluxRHSLocalCenteredForceSeminorm R g s) ^ 2)]
          rw [descendantsAverage_smul Q n K2
            (fun R => (weakFluxRHSLocalCenteredForceSeminorm R g s) ^ 2)]

/-- Average forcing component controlled by a multiplier bound and an averaged
centered-force bound. -/
theorem weakFluxRHSLocalForceErrorAverage_le_of_multiplierSqBound_of_centeredForceAverageBound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (g : Vec d → Vec d) (s : ℝ) {η : ℝ} (n : ℕ) {K2 B : ℝ}
    (hη : 0 < η)
    (hK2 : 0 ≤ K2)
    (hmult :
      ∀ R ∈ descendantsAtDepth Q n,
        (weakFluxRHSLocalForceMultiplier R a s) ^ 2 ≤ K2)
    (hforceAvg :
      descendantsAverage Q n
        (fun R => (weakFluxRHSLocalCenteredForceSeminorm R g s) ^ 2) ≤ B) :
    weakFluxRHSLocalForceErrorAverage Q a g s η n ≤
      2 * η⁻¹ * (K2 * B) := by
  have hfactor_nonneg : 0 ≤ 2 * η⁻¹ :=
    mul_nonneg (by norm_num) (inv_nonneg.mpr hη.le)
  have hcoef_nonneg : 0 ≤ 2 * η⁻¹ * K2 :=
    mul_nonneg hfactor_nonneg hK2
  calc
    weakFluxRHSLocalForceErrorAverage Q a g s η n
        ≤
          2 * η⁻¹ *
            (K2 *
              descendantsAverage Q n
                (fun R => (weakFluxRHSLocalCenteredForceSeminorm R g s) ^ 2)) := by
          exact weakFluxRHSLocalForceErrorAverage_le_of_multiplierSqBound
            Q a g s n hη hmult
    _ =
          (2 * η⁻¹ * K2) *
            descendantsAverage Q n
              (fun R => (weakFluxRHSLocalCenteredForceSeminorm R g s) ^ 2) := by
          ring
    _ ≤ (2 * η⁻¹ * K2) * B := by
          exact mul_le_mul_of_nonneg_left hforceAvg hcoef_nonneg
    _ = 2 * η⁻¹ * (K2 * B) := by
          ring

/-- Average forcing component localized to the parent half-scale multiplier
under an averaged centered-force bound. -/
theorem weakFluxRHSLocalForceErrorAverage_le_parentHalfLambda_of_centeredForceAverageBound
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g : Vec d → Vec d) {s η lam Lam : ℝ} (n : ℕ) {B : ℝ}
    (hs : 0 < s) (hη : 0 < η)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_half :
      Summable (fun m : ℕ =>
        geometricWeight (s / 2) 2 m *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (m : ℤ)) a) 1))
    (hforceAvg :
      descendantsAverage Q n
        (fun R => (weakFluxRHSLocalCenteredForceSeminorm R g s) ^ 2) ≤ B) :
    weakFluxRHSLocalForceErrorAverage Q a g s η n ≤
      2 * η⁻¹ * ((weakFluxRHSParentHalfForceMultiplier Q a s n) ^ 2 * B) := by
  refine
    weakFluxRHSLocalForceErrorAverage_le_of_multiplierSqBound_of_centeredForceAverageBound
      Q a g s n hη (sq_nonneg _) ?_ hforceAvg
  intro R hR
  exact
    weakFluxRHSLocalForceMultiplier_sq_le_parentHalfLambda_of_mem_descendantsAtDepth
      (Q := Q) (R := R) a n hs hR hEll hData hsum_half

/-- The weak-flux centered forcing seminorm agrees with the uncentered
positive Besov seminorm under the standard descendant `MemLp` assumptions. -/
theorem weakFluxRHSLocalCenteredForceSeminorm_eq_uncentered_of_mem
    {d : ℕ} {Q R : TriadicCube d} (g : Vec d → Vec d) (s : ℝ) {n : ℕ}
    (hR : R ∈ descendantsAtDepth Q n)
    (hmem :
      ∀ j : ℕ, ∀ S ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S)) :
    weakFluxRHSLocalCenteredForceSeminorm R g s =
      cubeBesovPositiveVectorSeminormTwo R s g := by
  simpa [weakFluxRHSLocalCenteredForceSeminorm,
    coarsePoincareRHSLocalCenteredForceSeminorm] using
    coarsePoincareRHSLocalCenteredForceSeminorm_eq_uncentered_of_mem
      (Q := Q) (R := R) g s hR hmem

/-- Descendant averages of weak-flux centered forcing seminorms agree with
uncentered positive-Besov averages under the standard `MemLp` assumptions. -/
theorem descendantsAverage_sq_weakFluxRHSLocalCenteredForceSeminorm_eq_of_mem
    {d : ℕ} (Q : TriadicCube d) (g : Vec d → Vec d) (s : ℝ) (n : ℕ)
    (hmem :
      ∀ j : ℕ, ∀ S ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S)) :
    descendantsAverage Q n
        (fun R => (weakFluxRHSLocalCenteredForceSeminorm R g s) ^ 2) =
      descendantsAverage Q n
        (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) := by
  simpa [weakFluxRHSLocalCenteredForceSeminorm,
    coarsePoincareRHSLocalCenteredForceSeminorm] using
    descendantsAverage_sq_coarsePoincareRHSLocalCenteredForceSeminorm_eq_of_mem
      Q g s n hmem

/-- Average forcing component localized to the parent half-scale multiplier
under an averaged uncentered-force bound. -/
theorem weakFluxRHSLocalForceErrorAverage_le_parentHalfLambda_of_forceAverageBound
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g : Vec d → Vec d) {s η lam Lam : ℝ} (n : ℕ) {B : ℝ}
    (hs : 0 < s) (hη : 0 < η)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_half :
      Summable (fun m : ℕ =>
        geometricWeight (s / 2) 2 m *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (m : ℤ)) a) 1))
    (hmem :
      ∀ j : ℕ, ∀ S ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S))
    (hforceAvg :
      descendantsAverage Q n
        (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) ≤ B) :
    weakFluxRHSLocalForceErrorAverage Q a g s η n ≤
      2 * η⁻¹ * ((weakFluxRHSParentHalfForceMultiplier Q a s n) ^ 2 * B) := by
  have hcentered :
      descendantsAverage Q n
        (fun R => (weakFluxRHSLocalCenteredForceSeminorm R g s) ^ 2) ≤ B := by
    rw [descendantsAverage_sq_weakFluxRHSLocalCenteredForceSeminorm_eq_of_mem
      Q g s n hmem]
    exact hforceAvg
  exact
    weakFluxRHSLocalForceErrorAverage_le_parentHalfLambda_of_centeredForceAverageBound
      Q a g n hs hη hEll hData hsum_half hcentered

/-- Average forcing component localized to the parent half-scale multiplier and
the global positive-Besov forcing bound. -/
theorem weakFluxRHSLocalForceErrorAverage_le_parentHalfLambda_globalForceBound
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g : Vec d → Vec d) {s η lam Lam : ℝ} (n : ℕ)
    (hs : 0 < s) (hη : 0 < η)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_half :
      Summable (fun m : ℕ =>
        geometricWeight (s / 2) 2 m *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (m : ℤ)) a) 1))
    (hmem :
      ∀ j : ℕ, ∀ S ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hLocalBdd :
      ∀ R ∈ descendantsAtDepth Q n,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g)) :
    weakFluxRHSLocalForceErrorAverage Q a g s η n ≤
      2 * η⁻¹ *
        ((weakFluxRHSParentHalfForceMultiplier Q a s n) ^ 2 *
          coarsePoincareRHSGlobalForceBound Q g s n) := by
  have hforceAvg :
      descendantsAverage Q n
        (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) ≤
      coarsePoincareRHSGlobalForceBound Q g s n :=
    descendantsAverage_sq_cubeBesovPositiveVectorSeminormTwo_le_global_scaled
      Q g s n hGlobalBdd hLocalBdd
  exact
    weakFluxRHSLocalForceErrorAverage_le_parentHalfLambda_of_forceAverageBound
      Q a g n hs hη hEll hData hsum_half hmem hforceAvg

/-- Depth-weighted parent-localized weak-flux forcing base. -/
noncomputable def weakFluxRHSWeightedGlobalForceBase {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    (s η : ℝ) (n : ℕ) : ℝ :=
  coarsePoincareRHSDepthWeight s n *
    (2 * η⁻¹ *
      ((weakFluxRHSParentHalfForceMultiplier Q a s n) ^ 2 *
        coarsePoincareRHSGlobalForceBound Q g s n))

/-- The depth-weighted parent-localized weak-flux forcing base is nonnegative
for positive absorption parameter. -/
theorem weakFluxRHSWeightedGlobalForceBase_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    (s : ℝ) {η : ℝ} (hη : 0 < η) (n : ℕ) :
    0 ≤ weakFluxRHSWeightedGlobalForceBase Q a g s η n := by
  unfold weakFluxRHSWeightedGlobalForceBase
  refine mul_nonneg ?_ ?_
  · unfold coarsePoincareRHSDepthWeight
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  · refine mul_nonneg ?_ ?_
    · exact mul_nonneg (by norm_num) (inv_nonneg.mpr hη.le)
    · refine mul_nonneg (sq_nonneg _) ?_
      unfold coarsePoincareRHSGlobalForceBound
      exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (sq_nonneg _)

/-- The weighted weak-flux forcing base decays by `3^{-s}` when the depth is
incremented. -/
theorem weakFluxRHSWeightedGlobalForceBase_succ
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    (s η : ℝ) (n : ℕ) :
    weakFluxRHSWeightedGlobalForceBase Q a g s η (n + 1) =
      Real.rpow (3 : ℝ) (-s) *
        weakFluxRHSWeightedGlobalForceBase Q a g s η n := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  have hdepth :
      coarsePoincareRHSDepthWeight s (n + 1) =
        Real.rpow (3 : ℝ) (-s) * coarsePoincareRHSDepthWeight s n := by
    simpa [coarsePoincareRHSStepDiscount] using
      coarsePoincareRHSDepthWeight_succ s n
  have hmult :=
    weakFluxRHSParentHalfForceMultiplier_succ Q a s n
  have hforce :=
    coarsePoincareRHSGlobalForceBound_succ Q g s n
  have hfactor :
      Real.rpow (3 : ℝ) (-s) * (Real.rpow (3 : ℝ) s) ^ 2 *
          Real.rpow (3 : ℝ) (-2 * s) =
        Real.rpow (3 : ℝ) (-s) := by
    have hsq :
        (Real.rpow (3 : ℝ) s) ^ 2 =
          Real.rpow (3 : ℝ) (2 * s) := by
      calc
        (Real.rpow (3 : ℝ) s) ^ 2 =
            Real.rpow (3 : ℝ) s * Real.rpow (3 : ℝ) s := by
              ring
        _ = Real.rpow (3 : ℝ) (s + s) := by
              exact (Real.rpow_add h3 s s).symm
        _ = Real.rpow (3 : ℝ) (2 * s) := by
              congr 1
              ring
    have hsum1 :
        Real.rpow (3 : ℝ) (-s) * Real.rpow (3 : ℝ) (2 * s) =
          Real.rpow (3 : ℝ) (-s + 2 * s) := by
      simpa using (Real.rpow_add h3 (-s) (2 * s)).symm
    have hsum2 :
        Real.rpow (3 : ℝ) (-s + 2 * s) * Real.rpow (3 : ℝ) (-2 * s) =
          Real.rpow (3 : ℝ) ((-s + 2 * s) + -2 * s) := by
      simpa using (Real.rpow_add h3 (-s + 2 * s) (-2 * s)).symm
    calc
      Real.rpow (3 : ℝ) (-s) * (Real.rpow (3 : ℝ) s) ^ 2 *
          Real.rpow (3 : ℝ) (-2 * s) =
        Real.rpow (3 : ℝ) (-s) * Real.rpow (3 : ℝ) (2 * s) *
          Real.rpow (3 : ℝ) (-2 * s) := by
          rw [hsq]
      _ = Real.rpow (3 : ℝ) (-s + 2 * s) * Real.rpow (3 : ℝ) (-2 * s) := by
          rw [hsum1]
      _ = Real.rpow (3 : ℝ) ((-s + 2 * s) + -2 * s) := by
          rw [hsum2]
      _ = Real.rpow (3 : ℝ) (-s) := by
          congr 1
          ring
  unfold weakFluxRHSWeightedGlobalForceBase
  rw [hdepth, hmult, hforce]
  nth_rewrite 2 [← hfactor]
  ring

/-- The weighted weak-flux forcing base at depth `m + k` is the depth-`m` base
times `3^{-s}` to the `k`. -/
theorem weakFluxRHSWeightedGlobalForceBase_add_eq_base_mul_ratio_pow
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    (s η : ℝ) (m k : ℕ) :
    weakFluxRHSWeightedGlobalForceBase Q a g s η (m + k) =
      weakFluxRHSWeightedGlobalForceBase Q a g s η m *
        (Real.rpow (3 : ℝ) (-s)) ^ k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        weakFluxRHSWeightedGlobalForceBase Q a g s η (m + (k + 1))
            =
          weakFluxRHSWeightedGlobalForceBase Q a g s η ((m + k) + 1) := by
            rw [Nat.add_assoc]
        _ =
          Real.rpow (3 : ℝ) (-s) *
            weakFluxRHSWeightedGlobalForceBase Q a g s η (m + k) := by
            rw [weakFluxRHSWeightedGlobalForceBase_succ]
        _ =
          Real.rpow (3 : ℝ) (-s) *
            (weakFluxRHSWeightedGlobalForceBase Q a g s η m *
              (Real.rpow (3 : ℝ) (-s)) ^ k) := by
            rw [ih]
        _ =
          weakFluxRHSWeightedGlobalForceBase Q a g s η m *
            (Real.rpow (3 : ℝ) (-s)) ^ (k + 1) := by
            rw [pow_succ]
            ring

/-- The weighted weak-flux forcing base decreases along descendants when
`s > 0`. -/
theorem weakFluxRHSWeightedGlobalForceBase_add_le_base
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    {s η : ℝ} (m k : ℕ) (hs : 0 < s) (hη : 0 < η) :
    weakFluxRHSWeightedGlobalForceBase Q a g s η (m + k) ≤
      weakFluxRHSWeightedGlobalForceBase Q a g s η m := by
  have hbase_nonneg :
      0 ≤ weakFluxRHSWeightedGlobalForceBase Q a g s η m := by
    unfold weakFluxRHSWeightedGlobalForceBase
    refine mul_nonneg ?_ ?_
    · unfold coarsePoincareRHSDepthWeight
      exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
    · refine mul_nonneg ?_ ?_
      · exact mul_nonneg (by norm_num) (inv_nonneg.mpr hη.le)
      · exact mul_nonneg (sq_nonneg _)
          (by
            unfold coarsePoincareRHSGlobalForceBound
            exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (sq_nonneg _))
  have hratio_nonneg : 0 ≤ Real.rpow (3 : ℝ) (-s) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hratio_le_one : Real.rpow (3 : ℝ) (-s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos
      (by norm_num : (1 : ℝ) ≤ 3) (by linarith)
  have hpow_le_one : (Real.rpow (3 : ℝ) (-s)) ^ k ≤ 1 :=
    pow_le_one₀ hratio_nonneg hratio_le_one
  calc
    weakFluxRHSWeightedGlobalForceBase Q a g s η (m + k)
        =
          weakFluxRHSWeightedGlobalForceBase Q a g s η m *
            (Real.rpow (3 : ℝ) (-s)) ^ k := by
          rw [weakFluxRHSWeightedGlobalForceBase_add_eq_base_mul_ratio_pow]
    _ ≤ weakFluxRHSWeightedGlobalForceBase Q a g s η m * 1 := by
          exact mul_le_mul_of_nonneg_left hpow_le_one hbase_nonneg
    _ = weakFluxRHSWeightedGlobalForceBase Q a g s η m := by
          ring

/-- The localized force-error average supplies the uniform component-base input
needed by the weak-flux global wrappers. -/
theorem weakFluxRHSDepthWeight_mul_forceErrorAverage_le_weightedGlobalForceBase
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g : Vec d → Vec d) {s η lam Lam : ℝ} (m k : ℕ)
    (hs : 0 < s) (hη : 0 < η)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_half :
      Summable (fun l : ℕ =>
        geometricWeight (s / 2) 2 l *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (l : ℤ)) a) 1))
    (hmem :
      ∀ j : ℕ, ∀ S ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hLocalBdd :
      ∀ R ∈ descendantsAtDepth Q (m + k),
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g)) :
    coarsePoincareRHSDepthWeight s (m + k) *
      weakFluxRHSLocalForceErrorAverage Q a g s η (m + k) ≤
      weakFluxRHSWeightedGlobalForceBase Q a g s η m := by
  have hlocal :=
    weakFluxRHSLocalForceErrorAverage_le_parentHalfLambda_globalForceBound
      Q a g (m + k) hs hη hEll hData hsum_half hmem hGlobalBdd hLocalBdd
  have hweight_nonneg : 0 ≤ coarsePoincareRHSDepthWeight s (m + k) := by
    unfold coarsePoincareRHSDepthWeight
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  calc
    coarsePoincareRHSDepthWeight s (m + k) *
        weakFluxRHSLocalForceErrorAverage Q a g s η (m + k)
        ≤
          coarsePoincareRHSDepthWeight s (m + k) *
            (2 * η⁻¹ *
              ((weakFluxRHSParentHalfForceMultiplier Q a s (m + k)) ^ 2 *
                coarsePoincareRHSGlobalForceBound Q g s (m + k))) := by
          exact mul_le_mul_of_nonneg_left hlocal hweight_nonneg
    _ =
          weakFluxRHSWeightedGlobalForceBase Q a g s η (m + k) := by
          rfl
    _ ≤ weakFluxRHSWeightedGlobalForceBase Q a g s η m :=
          weakFluxRHSWeightedGlobalForceBase_add_le_base Q a g m k hs hη

end

end Homogenization
