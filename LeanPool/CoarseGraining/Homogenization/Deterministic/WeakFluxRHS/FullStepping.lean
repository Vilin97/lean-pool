/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.SeminormRecurrence
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.CorrectorEnergy
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.FluxStepping
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.WeakSolutionBridge

/-! # Full Stepping -/

namespace Homogenization

noncomputable section

namespace MeanZeroNeumannCorrectorData

variable {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {g : Vec d → Vec d}

/-- Full-seminorm form of the weak-flux local step.  This turns the finite-depth
local recurrence from `FluxStepping` into the one-step recurrence for the full
`q = 2` negative seminorm, assuming the child full seminorms bound their finite
partials. -/
theorem sq_cubeBesovNegativeVectorSeminormTwo_flux_le_descendantsAverage_add_harmonic_energy_of_childBddAbove
    (ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g))
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    (s : ℝ) (hs : 0 < s) (energy : Vec d → ℝ)
    {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu_mem : MemVectorL2 (cubeSet Q) u)
    (hg : MemVectorL2 (cubeSet Q) g)
    (henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy_int : MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume)
    (hflux :
      CubeAverageFluxEnergyControl Q a
        (fun x => matVecMul (a x) (w.toH1.grad x)) energy)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a))
    (huw : ∀ x ∈ cubeSet Q,
      u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x)
    (hchildBdd :
      ∀ R ∈ descendantsAtDepth Q 1,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => matVecMul (a x) (u x)))) :
    (cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (u x))) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * s) *
        descendantsAverage Q 1
          (fun R =>
            (cubeBesovNegativeVectorSeminormTwo R s
              (fun x => matVecMul (a x) (u x))) ^ 2) +
      (geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a *
        cubeAverage Q energy := by
  let flux : Vec d → Vec d := fun x => matVecMul (a x) (u x)
  let F : ℝ := (geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a *
    cubeAverage Q energy
  have hs2 : 0 < s * (2 : ℝ) := by positivity
  have hF_nonneg : 0 ≤ F := by
    dsimp [F]
    have hdisc_nonneg : 0 ≤ (geometricDiscount s 2)⁻¹ :=
      inv_nonneg.mpr (le_of_lt (geometricDiscount_pos hs2))
    have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite 2) a :=
      multiscale_ellipticity_LambdaSq_finite_nonneg Q s 2 a
        (by norm_num) (by nlinarith [hs])
    have henergy_avg_nonneg : 0 ≤ cubeAverage Q energy :=
      cubeAverage_nonneg_of_nonneg_on henergy_nonneg
    exact mul_nonneg (mul_nonneg hdisc_nonneg hLambda_nonneg) henergy_avg_nonneg
  have hchildAvg_nonneg :
      0 ≤ descendantsAverage Q 1
        (fun R => (cubeBesovNegativeVectorSeminormTwo R s flux) ^ 2) :=
    descendantsAverage_nonneg Q 1 _ fun R hR => sq_nonneg _
  have hB_nonneg :
      0 ≤
        Real.rpow (3 : ℝ) (-2 * s) *
          descendantsAverage Q 1
            (fun R => (cubeBesovNegativeVectorSeminormTwo R s flux) ^ 2) +
        F := by
    exact add_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _) hchildAvg_nonneg)
      hF_nonneg
  have hlocal :
      ∀ N : ℕ,
        (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) flux) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage Q 1
              (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N flux) ^ 2) +
          F := by
    intro N
    simpa [flux, F] using
      ω.sq_cubeBesovNegativeVectorPartialSeminormTwo_flux_succ_le_descendantsAverage_add_harmonic_energy
        (u := u) w s hs N energy hEll hu_mem hg
        henergy_nonneg henergy_int hflux hsum huw
  have hchild :
      ∀ R ∈ descendantsAtDepth Q 1, ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminormTwo R s N flux ≤
          cubeBesovNegativeVectorSeminormTwo R s flux := by
    intro R hR N
    exact
      cubeBesovNegativeVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
        R s flux (by simpa [flux] using hchildBdd R hR) N
  simpa [flux, F] using
    sq_cubeBesovNegativeVectorSeminormTwo_le_descendantsAverage_add_of_succ_partialBound
      (Q := Q) (s := s) (u := flux)
      (Bchild := fun R => cubeBesovNegativeVectorSeminormTwo R s flux)
      (F := F) hB_nonneg hlocal hchild

/-- Coefficient-energy version of the weak-flux local step after splitting the
harmonic remainder energy into the original field and the mean-zero Neumann
corrector. -/
theorem sq_cubeBesovNegativeVectorSeminormTwo_flux_le_descendantsAverage_add_uCoeffEnergy_add_correctorCoeffEnergy_of_childBddAbove
    (ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g))
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    (s : ℝ) (hs : 0 < s)
    {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu_mem : MemVectorL2 (cubeSet Q) u)
    (hg : MemVectorL2 (cubeSet Q) g)
    (hflux :
      CubeAverageFluxEnergyControl Q a
        (fun x => matVecMul (a x) (w.toH1.grad x))
        (coefficientEnergyDensity a (fun x => w.toH1.grad x)))
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a))
    (huw : ∀ x ∈ cubeSet Q,
      u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x)
    (hchildBdd :
      ∀ R ∈ descendantsAtDepth Q 1,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => matVecMul (a x) (u x)))) :
    (cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (u x))) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * s) *
        descendantsAverage Q 1
          (fun R =>
            (cubeBesovNegativeVectorSeminormTwo R s
              (fun x => matVecMul (a x) (u x))) ^ 2) +
      2 * ((geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a) *
        cubeAverage Q (coefficientEnergyDensity a u) +
      2 * ((geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a) *
        cubeAverage Q
          (coefficientEnergyDensity a
            (fun x => ω.toH1MeanZero.toH1Function.grad x)) := by
  let C : ℝ := (geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a
  have henergy_nonneg :
      ∀ x ∈ cubeSet Q,
        0 ≤ coefficientEnergyDensity a (fun x => w.toH1.grad x) x :=
    coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll
      (fun x => w.toH1.grad x)
  have henergy_int :
      MeasureTheory.IntegrableOn
        (coefficientEnergyDensity a (fun x => w.toH1.grad x))
        (cubeSet Q) MeasureTheory.volume :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll
      w.toH1.grad_memVectorL2
  have hbase :=
    ω.sq_cubeBesovNegativeVectorSeminormTwo_flux_le_descendantsAverage_add_harmonic_energy_of_childBddAbove
      (u := u) w s hs (coefficientEnergyDensity a (fun x => w.toH1.grad x))
      hEll hu_mem hg henergy_nonneg henergy_int hflux hsum huw hchildBdd
  have hsplit :=
    ω.cubeAverage_coefficientEnergyDensity_harmonic_le_two_mul_add
      (u := u) w hEll huw hu_mem
  have hs2 : 0 < s * (2 : ℝ) := by positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (inv_nonneg.mpr (le_of_lt (geometricDiscount_pos hs2)))
      (multiscale_ellipticity_LambdaSq_finite_nonneg Q s 2 a
        (by norm_num) (by nlinarith [hs]))
  calc
    (cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (u x))) ^ 2
        ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage Q 1
              (fun R =>
                (cubeBesovNegativeVectorSeminormTwo R s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          C * cubeAverage Q
            (coefficientEnergyDensity a (fun x => w.toH1.grad x)) := by
        simpa [C] using hbase
    _ ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage Q 1
              (fun R =>
                (cubeBesovNegativeVectorSeminormTwo R s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          C *
            (2 * cubeAverage Q (coefficientEnergyDensity a u) +
              2 * cubeAverage Q
                (coefficientEnergyDensity a
                  (fun x => ω.toH1MeanZero.toH1Function.grad x))) := by
        exact add_le_add_right (mul_le_mul_of_nonneg_left hsplit hC_nonneg) _
    _ =
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage Q 1
              (fun R =>
                (cubeBesovNegativeVectorSeminormTwo R s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          2 * C * cubeAverage Q (coefficientEnergyDensity a u) +
          2 * C * cubeAverage Q
            (coefficientEnergyDensity a
              (fun x => ω.toH1MeanZero.toH1Function.grad x)) := by
        ring

/-- Full-seminorm local recurrence with the Neumann-corrector energy replaced
by the sharp centered Besov product bound. -/
theorem sq_cubeBesovNegativeVectorSeminormTwo_flux_le_descendantsAverage_add_uCoeffEnergy_add_correctorShortTerm_of_childBddAbove
    (ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g))
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    (s : ℝ) (hs : 0 < s)
    {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu_mem : MemVectorL2 (cubeSet Q) u)
    (hg_mem : MemVectorL2 (cubeSet Q) g)
    (hflux :
      CubeAverageFluxEnergyControl Q a
        (fun x => matVecMul (a x) (w.toH1.grad x))
        (coefficientEnergyDensity a (fun x => w.toH1.grad x)))
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a))
    (huw : ∀ x ∈ cubeSet Q,
      u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x)
    (hchildBdd :
      ∀ R ∈ descendantsAtDepth Q 1,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => matVecMul (a x) (u x))))
    (huBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N u))
    (hwBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => w.toH1.grad x)))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => g x - cubeAverageVec Q g))) :
    (cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (u x))) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * s) *
        descendantsAverage Q 1
          (fun R =>
            (cubeBesovNegativeVectorSeminormTwo R s
              (fun x => matVecMul (a x) (u x))) ^ 2) +
      2 * ((geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a) *
        cubeAverage Q (coefficientEnergyDensity a u) +
      2 * ((geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a) *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) *
          (Real.sqrt 2 *
            (cubeBesovNegativeVectorSeminormTwo Q s u +
              cubeBesovNegativeVectorSeminormTwo Q s
                (fun x => w.toH1.grad x))) *
          cubeBesovPositiveVectorSeminormTwo Q s
            (fun x => g x - cubeAverageVec Q g))) := by
  let C : ℝ := (geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a
  let U : ℝ := cubeBesovNegativeVectorSeminormTwo Q s u
  let W : ℝ := cubeBesovNegativeVectorSeminormTwo Q s (fun x => w.toH1.grad x)
  let G : ℝ := cubeBesovPositiveVectorSeminormTwo Q s (fun x => g x - cubeAverageVec Q g)
  let Short : ℝ := (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * (Real.sqrt 2 * (U + W)) * G)
  have hbase :=
    ω.sq_cubeBesovNegativeVectorSeminormTwo_flux_le_descendantsAverage_add_uCoeffEnergy_add_correctorCoeffEnergy_of_childBddAbove
      (u := u) w s hs hEll hu_mem hg_mem hflux hsum huw hchildBdd
  have hg :
      MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hg_mem
  have hgradω :
      MeasureTheory.MemLp
        (fun x => ω.toH1MeanZero.toH1Function.grad x)
        (2 : ENNReal) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q
      ω.toH1MeanZero.toH1Function.grad_memVectorL2
  have hBg : 0 ≤ G := by
    dsimp [G]
    exact cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove
      Q s (fun x => g x - cubeAverageVec Q g) hgBdd
  have hnegω :
      ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => ω.toH1MeanZero.toH1Function.grad x) ≤ Real.sqrt 2 * (U + W) := by
    dsimp [U, W]
    exact
      ω.cubeBesovNegativeVectorPartialSeminormTwo_corrector_le_sqrtTwo_mul_add_of_bddAbove
        (u := u) w huw hu_mem s huBdd hwBdd
  have hposg :
      ∀ N : ℕ,
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => g x - cubeAverageVec Q g) ≤ G := by
    intro N
    dsimp [G]
    exact
      cubeBesovPositiveVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
        Q s (fun x => g x - cubeAverageVec Q g) hgBdd N
  have hωenergy :
      cubeAverage Q
          (coefficientEnergyDensity a
            (fun x => ω.toH1MeanZero.toH1Function.grad x)) ≤ Short := by
    dsimp [Short, U, W, G]
    exact
      ω.coefficientEnergy_average_le_collapsed_note_term_centered_two_two
        s hs hg_mem hg hgradω hBg hnegω hposg
  have hs2 : 0 < s * (2 : ℝ) := by positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (inv_nonneg.mpr (le_of_lt (geometricDiscount_pos hs2)))
      (multiscale_ellipticity_LambdaSq_finite_nonneg Q s 2 a
        (by norm_num) (by nlinarith [hs]))
  have h2C_nonneg : 0 ≤ 2 * C := by positivity
  have hfinal :
      (cubeBesovNegativeVectorSeminormTwo Q s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
        Real.rpow (3 : ℝ) (-2 * s) *
          descendantsAverage Q 1
            (fun R =>
              (cubeBesovNegativeVectorSeminormTwo R s
                (fun x => matVecMul (a x) (u x))) ^ 2) +
        2 * C * cubeAverage Q (coefficientEnergyDensity a u) +
        2 * C * Short := by
    calc
      (cubeBesovNegativeVectorSeminormTwo Q s
          (fun x => matVecMul (a x) (u x))) ^ 2
          ≤
            Real.rpow (3 : ℝ) (-2 * s) *
              descendantsAverage Q 1
                (fun R =>
                  (cubeBesovNegativeVectorSeminormTwo R s
                    (fun x => matVecMul (a x) (u x))) ^ 2) +
            2 * C * cubeAverage Q (coefficientEnergyDensity a u) +
            2 * C * cubeAverage Q
              (coefficientEnergyDensity a
                (fun x => ω.toH1MeanZero.toH1Function.grad x)) := by
            simpa [C] using hbase
      _ ≤
            Real.rpow (3 : ℝ) (-2 * s) *
              descendantsAverage Q 1
                (fun R =>
                  (cubeBesovNegativeVectorSeminormTwo R s
                    (fun x => matVecMul (a x) (u x))) ^ 2) +
            2 * C * cubeAverage Q (coefficientEnergyDensity a u) +
            2 * C * Short := by
            exact add_le_add_right
              (mul_le_mul_of_nonneg_left hωenergy h2C_nonneg) _
  simpa [C, U, W, G, Short] using hfinal

/-- Full-seminorm local recurrence with the short corrector product absorbed
into quadratic `u`, harmonic-remainder, and forcing terms. -/
theorem sq_cubeBesovNegativeVectorSeminormTwo_flux_le_descendantsAverage_add_uCoeffEnergy_add_eta_uSq_eta_wSq_invEta_gSq_of_childBddAbove
    (ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g))
    {u : Vec d → Vec d} (w : AHarmonicFunction a (cubeSet Q))
    (s : ℝ) {η : ℝ} (hs : 0 < s) (hη : 0 < η)
    {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu_mem : MemVectorL2 (cubeSet Q) u)
    (hg_mem : MemVectorL2 (cubeSet Q) g)
    (hflux :
      CubeAverageFluxEnergyControl Q a
        (fun x => matVecMul (a x) (w.toH1.grad x))
        (coefficientEnergyDensity a (fun x => w.toH1.grad x)))
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a))
    (huw : ∀ x ∈ cubeSet Q,
      u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x)
    (hchildBdd :
      ∀ R ∈ descendantsAtDepth Q 1,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => matVecMul (a x) (u x))))
    (huBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N u))
    (hwBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => w.toH1.grad x)))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => g x - cubeAverageVec Q g))) :
    (cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (u x))) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * s) *
        descendantsAverage Q 1
          (fun R =>
            (cubeBesovNegativeVectorSeminormTwo R s
              (fun x => matVecMul (a x) (u x))) ^ 2) +
      2 * ((geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a) *
        cubeAverage Q (coefficientEnergyDensity a u) +
      η * (cubeBesovNegativeVectorSeminormTwo Q s u) ^ 2 +
      η * (cubeBesovNegativeVectorSeminormTwo Q s (fun x => w.toH1.grad x)) ^ 2 +
      2 * η⁻¹ *
        (((((geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a) *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))) *
          cubeBesovPositiveVectorSeminormTwo Q s
            (fun x => g x - cubeAverageVec Q g)) ^ 2) := by
  let Child : ℝ :=
    Real.rpow (3 : ℝ) (-2 * s) *
      descendantsAverage Q 1
        (fun R => (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (u x))) ^ 2)
  let U : ℝ := cubeBesovNegativeVectorSeminormTwo Q s u
  let W : ℝ := cubeBesovNegativeVectorSeminormTwo Q s (fun x => w.toH1.grad x)
  let G : ℝ := cubeBesovPositiveVectorSeminormTwo Q s (fun x => g x - cubeAverageVec Q g)
  let C : ℝ := (geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a
  let A : ℝ := 2 * C * cubeAverage Q (coefficientEnergyDensity a u)
  let K : ℝ := C * ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))
  let D : ℝ := 2 * K
  have hshort :=
    ω.sq_cubeBesovNegativeVectorSeminormTwo_flux_le_descendantsAverage_add_uCoeffEnergy_add_correctorShortTerm_of_childBddAbove
      (u := u) w s hs hEll hu_mem hg_mem hflux hsum huw hchildBdd huBdd hwBdd hgBdd
  have hshort' :
      (cubeBesovNegativeVectorSeminormTwo Q s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
        Child + A + D * (U + W) * G := by
    dsimp [Child, U, W, G, C, A, K, D] at hshort ⊢
    simpa [mul_assoc, mul_left_comm, mul_comm, left_distrib, right_distrib] using hshort
  have hcross :
      D * (U + W) * G ≤ η * U ^ 2 + η * W ^ 2 + 2 * η⁻¹ * ((K * G) ^ 2) := by
    have hraw := add_bilinear_term_le_add_eta_sq_add_invEta_sq
      (D := D) (U := U) (W := W) (G := G) hη
    have hhalf : (D / 2) * G = K * G := by
      dsimp [D]
      ring
    calc
      D * (U + W) * G ≤
          η * U ^ 2 + η * W ^ 2 + 2 * η⁻¹ * (((D / 2) * G) ^ 2) := hraw
      _ = η * U ^ 2 + η * W ^ 2 + 2 * η⁻¹ * ((K * G) ^ 2) := by
            rw [hhalf]
  have hfinal :
      (cubeBesovNegativeVectorSeminormTwo Q s
          (fun x => matVecMul (a x) (u x))) ^ 2 ≤
        Child + A + η * U ^ 2 + η * W ^ 2 + 2 * η⁻¹ * ((K * G) ^ 2) := by
    linarith
  simpa [Child, U, W, G, C, A, K] using hfinal

/--
Descendant-cube full-seminorm recurrence from parent potential/solenoidal
weak-flux data.  This is the local iteration-facing version of the centered
Neumann-corrector construction. -/
theorem exists_centeredCorrector_aHarmonicRemainder_fluxSeminormStepEnergy_of_parent_potential_solenoidal_h1CoerciveEstimate
    [NeZero d] {P R : TriadicCube d} {n : ℕ} {lam Lam s : ℝ}
    {u g : Vec d → Vec d}
    (hs : 0 < s)
    (hu_potential : IsPotentialOn (cubeSet P) u)
    (hu_residual :
      IsSolenoidalOn (cubeSet P) (fun x => matVecMul (a x) (u x) - g x))
    (hR : R ∈ descendantsAtDepth P n)
    (hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hu_memR : MemVectorL2 (cubeSet R) u)
    (hg_memR : MemVectorL2 (cubeSet R) g)
    (hC : H1CoerciveEstimate (cubeSet R)) :
    ∃ ω : MeanZeroNeumannCorrectorData R a (fun x => g x - cubeAverageVec R g),
      ∃ w : AHarmonicFunction a (cubeSet R),
        (∀ x ∈ cubeSet R,
          u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
        ∀ energy : Vec d → ℝ,
          (∀ x ∈ cubeSet R, 0 ≤ energy x) →
          MeasureTheory.IntegrableOn energy (cubeSet R) MeasureTheory.volume →
          CubeAverageFluxEnergyControl R a
            (fun x => matVecMul (a x) (w.toH1.grad x)) energy →
          Summable (fun m : ℕ =>
            geometricWeight s 2 m *
              maxDescendantBBlockNormAtScale R (R.scale - (m : ℤ)) a) →
          (∀ S ∈ descendantsAtDepth R 1,
            BddAbove (Set.range fun N : ℕ =>
              cubeBesovNegativeVectorPartialSeminormTwo S s N
                (fun x => matVecMul (a x) (u x)))) →
          (cubeBesovNegativeVectorSeminormTwo R s
              (fun x => matVecMul (a x) (u x))) ^ 2 ≤
            Real.rpow (3 : ℝ) (-2 * s) *
              descendantsAverage R 1
                (fun S =>
                  (cubeBesovNegativeVectorSeminormTwo S s
                    (fun x => matVecMul (a x) (u x))) ^ 2) +
            (geometricDiscount s 2)⁻¹ * LambdaSq R s (.finite 2) a *
              cubeAverage R energy := by
  rcases
      exists_centeredCorrector_aHarmonicRemainder_of_parent_potential_solenoidal_h1CoerciveEstimate
        (P := P) (R := R) (n := n) (a := a) (g := g) (u := u)
        (lam := lam) (Lam := Lam)
        hu_potential hu_residual hR hEllR hu_memR hg_memR hC with
    ⟨ω, w, huw⟩
  refine ⟨ω, w, huw, ?_⟩
  intro energy henergy_nonneg henergy_int hflux hsum hchildBdd
  exact
    ω.sq_cubeBesovNegativeVectorSeminormTwo_flux_le_descendantsAverage_add_harmonic_energy_of_childBddAbove
      (u := u) w s hs energy hEllR hu_memR hg_memR
      henergy_nonneg henergy_int hflux hsum huw hchildBdd

/--
Descendant-cube local recurrence with the harmonic flux energy split into the
original-field energy and the mean-zero Neumann-corrector energy. -/
theorem exists_centeredCorrector_aHarmonicRemainder_fluxSeminormStepCoeffEnergy_of_parent_potential_solenoidal_h1CoerciveEstimate
    [NeZero d] {P R : TriadicCube d} {n : ℕ} {lam Lam s : ℝ}
    {u g : Vec d → Vec d}
    (hs : 0 < s)
    (hu_potential : IsPotentialOn (cubeSet P) u)
    (hu_residual :
      IsSolenoidalOn (cubeSet P) (fun x => matVecMul (a x) (u x) - g x))
    (hR : R ∈ descendantsAtDepth P n)
    (hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hu_memR : MemVectorL2 (cubeSet R) u)
    (hg_memR : MemVectorL2 (cubeSet R) g)
    (hC : H1CoerciveEstimate (cubeSet R)) :
    ∃ ω : MeanZeroNeumannCorrectorData R a (fun x => g x - cubeAverageVec R g),
      ∃ w : AHarmonicFunction a (cubeSet R),
        (∀ x ∈ cubeSet R,
          u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
        (CubeAverageFluxEnergyControl R a
            (fun x => matVecMul (a x) (w.toH1.grad x))
            (coefficientEnergyDensity a (fun x => w.toH1.grad x)) →
          Summable (fun m : ℕ =>
            geometricWeight s 2 m *
              maxDescendantBBlockNormAtScale R (R.scale - (m : ℤ)) a) →
          (∀ S ∈ descendantsAtDepth R 1,
            BddAbove (Set.range fun N : ℕ =>
              cubeBesovNegativeVectorPartialSeminormTwo S s N
                (fun x => matVecMul (a x) (u x)))) →
          (cubeBesovNegativeVectorSeminormTwo R s
              (fun x => matVecMul (a x) (u x))) ^ 2 ≤
            Real.rpow (3 : ℝ) (-2 * s) *
              descendantsAverage R 1
                (fun S =>
                  (cubeBesovNegativeVectorSeminormTwo S s
                    (fun x => matVecMul (a x) (u x))) ^ 2) +
            2 * ((geometricDiscount s 2)⁻¹ * LambdaSq R s (.finite 2) a) *
              cubeAverage R (coefficientEnergyDensity a u) +
            2 * ((geometricDiscount s 2)⁻¹ * LambdaSq R s (.finite 2) a) *
              cubeAverage R
                (coefficientEnergyDensity a
                  (fun x => ω.toH1MeanZero.toH1Function.grad x))) := by
  rcases
      exists_centeredCorrector_aHarmonicRemainder_of_parent_potential_solenoidal_h1CoerciveEstimate
        (P := P) (R := R) (n := n) (a := a) (g := g) (u := u)
        (lam := lam) (Lam := Lam)
        hu_potential hu_residual hR hEllR hu_memR hg_memR hC with
    ⟨ω, w, huw⟩
  refine ⟨ω, w, huw, ?_⟩
  intro hflux hsum hchildBdd
  exact
    ω.sq_cubeBesovNegativeVectorSeminormTwo_flux_le_descendantsAverage_add_uCoeffEnergy_add_correctorCoeffEnergy_of_childBddAbove
      (u := u) w s hs hEllR hu_memR hg_memR hflux hsum huw hchildBdd

/--
Descendant-cube coefficient-energy recurrence with harmonic flux control
supplied by deterministic coarse data. -/
theorem exists_centeredCorrector_aHarmonicRemainder_fluxSeminormStepCoeffEnergy_of_parent_potential_solenoidal_h1CoerciveEstimate_of_coarseData
    [NeZero d] {P R : TriadicCube d} {n : ℕ} {lam Lam s : ℝ}
    {u g : Vec d → Vec d}
    (hs : 0 < s)
    (hu_potential : IsPotentialOn (cubeSet P) u)
    (hu_residual :
      IsSolenoidalOn (cubeSet P) (fun x => matVecMul (a x) (u x) - g x))
    (hR : R ∈ descendantsAtDepth P n)
    (hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hu_memR : MemVectorL2 (cubeSet R) u)
    (hg_memR : MemVectorL2 (cubeSet R) g)
    (hC : H1CoerciveEstimate (cubeSet R))
    (hDataR : OpenCubeDescendantDeterministicCoarseData R a)
    (hsum :
      Summable (fun m : ℕ =>
        geometricWeight s 2 m *
          maxDescendantBBlockNormAtScale R (R.scale - (m : ℤ)) a))
    (hchildBdd :
      ∀ S ∈ descendantsAtDepth R 1,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo S s N
            (fun x => matVecMul (a x) (u x)))) :
    ∃ ω : MeanZeroNeumannCorrectorData R a (fun x => g x - cubeAverageVec R g),
      ∃ w : AHarmonicFunction a (cubeSet R),
        (∀ x ∈ cubeSet R,
          u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
        (cubeBesovNegativeVectorSeminormTwo R s
            (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          2 * ((geometricDiscount s 2)⁻¹ * LambdaSq R s (.finite 2) a) *
            cubeAverage R (coefficientEnergyDensity a u) +
          2 * ((geometricDiscount s 2)⁻¹ * LambdaSq R s (.finite 2) a) *
            cubeAverage R
              (coefficientEnergyDensity a
                (fun x => ω.toH1MeanZero.toH1Function.grad x)) := by
  rcases
      exists_centeredCorrector_aHarmonicRemainder_fluxSeminormStepCoeffEnergy_of_parent_potential_solenoidal_h1CoerciveEstimate
        (P := P) (R := R) (n := n) (a := a) (g := g) (u := u)
        (lam := lam) (Lam := Lam) (s := s)
        hs hu_potential hu_residual hR hEllR hu_memR hg_memR hC with
    ⟨ω, w, huw, hstep⟩
  refine ⟨ω, w, huw, ?_⟩
  exact
    hstep
      (cubeAverageFluxEnergyControl_of_aHarmonicFunction
        (Q := R) (a := a) hEllR w hDataR)
      hsum hchildBdd

/--
Descendant-cube coefficient-energy recurrence with the corrector term replaced
by the short centered Besov product bound.  The harmonic seminorm boundedness is
returned as an input to the packaged step because the harmonic remainder is
created by the local Neumann construction. -/
theorem exists_centeredCorrector_aHarmonicRemainder_fluxSeminormStepShortTerm_of_parent_potential_solenoidal_h1CoerciveEstimate_of_coarseData
    [NeZero d] {P R : TriadicCube d} {n : ℕ} {lam Lam s : ℝ}
    {u g : Vec d → Vec d}
    (hs : 0 < s)
    (hu_potential : IsPotentialOn (cubeSet P) u)
    (hu_residual :
      IsSolenoidalOn (cubeSet P) (fun x => matVecMul (a x) (u x) - g x))
    (hR : R ∈ descendantsAtDepth P n)
    (hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hu_memR : MemVectorL2 (cubeSet R) u)
    (hg_memR : MemVectorL2 (cubeSet R) g)
    (hC : H1CoerciveEstimate (cubeSet R))
    (hDataR : OpenCubeDescendantDeterministicCoarseData R a)
    (hsum :
      Summable (fun m : ℕ =>
        geometricWeight s 2 m *
          maxDescendantBBlockNormAtScale R (R.scale - (m : ℤ)) a))
    (hchildBdd :
      ∀ S ∈ descendantsAtDepth R 1,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo S s N
            (fun x => matVecMul (a x) (u x))))
    (huBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo R s N u))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo R s N
          (fun x => g x - cubeAverageVec R g))) :
    ∃ ω : MeanZeroNeumannCorrectorData R a (fun x => g x - cubeAverageVec R g),
      ∃ w : AHarmonicFunction a (cubeSet R),
        (∀ x ∈ cubeSet R,
          u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
        (BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => w.toH1.grad x)) →
        (cubeBesovNegativeVectorSeminormTwo R s
            (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          2 * ((geometricDiscount s 2)⁻¹ * LambdaSq R s (.finite 2) a) *
            cubeAverage R (coefficientEnergyDensity a u) +
          2 * ((geometricDiscount s 2)⁻¹ * LambdaSq R s (.finite 2) a) *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) *
              (Real.sqrt 2 *
                (cubeBesovNegativeVectorSeminormTwo R s u +
                  cubeBesovNegativeVectorSeminormTwo R s
                    (fun x => w.toH1.grad x))) *
              cubeBesovPositiveVectorSeminormTwo R s
                (fun x => g x - cubeAverageVec R g)))) := by
  rcases
      exists_centeredCorrector_aHarmonicRemainder_of_parent_potential_solenoidal_h1CoerciveEstimate
        (P := P) (R := R) (n := n) (a := a) (g := g) (u := u)
        (lam := lam) (Lam := Lam)
        hu_potential hu_residual hR hEllR hu_memR hg_memR hC with
    ⟨ω, w, huw⟩
  refine ⟨ω, w, huw, ?_⟩
  intro hwBdd
  exact
    ω.sq_cubeBesovNegativeVectorSeminormTwo_flux_le_descendantsAverage_add_uCoeffEnergy_add_correctorShortTerm_of_childBddAbove
      (u := u) w s hs hEllR hu_memR hg_memR
      (cubeAverageFluxEnergyControl_of_aHarmonicFunction
        (Q := R) (a := a) hEllR w hDataR)
      hsum huw hchildBdd huBdd hwBdd hgBdd

/--
Descendant-cube recurrence with the short corrector product absorbed into
quadratic `u`, harmonic, and forcing terms. -/
theorem exists_centeredCorrector_aHarmonicRemainder_fluxSeminormStepAbsorbedShortTerm_of_parent_potential_solenoidal_h1CoerciveEstimate_of_coarseData
    [NeZero d] {P R : TriadicCube d} {n : ℕ} {lam Lam s η : ℝ}
    {u g : Vec d → Vec d}
    (hs : 0 < s) (hη : 0 < η)
    (hu_potential : IsPotentialOn (cubeSet P) u)
    (hu_residual :
      IsSolenoidalOn (cubeSet P) (fun x => matVecMul (a x) (u x) - g x))
    (hR : R ∈ descendantsAtDepth P n)
    (hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hu_memR : MemVectorL2 (cubeSet R) u)
    (hg_memR : MemVectorL2 (cubeSet R) g)
    (hC : H1CoerciveEstimate (cubeSet R))
    (hDataR : OpenCubeDescendantDeterministicCoarseData R a)
    (hsum :
      Summable (fun m : ℕ =>
        geometricWeight s 2 m *
          maxDescendantBBlockNormAtScale R (R.scale - (m : ℤ)) a))
    (hchildBdd :
      ∀ S ∈ descendantsAtDepth R 1,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo S s N
            (fun x => matVecMul (a x) (u x))))
    (huBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo R s N u))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo R s N
          (fun x => g x - cubeAverageVec R g))) :
    ∃ ω : MeanZeroNeumannCorrectorData R a (fun x => g x - cubeAverageVec R g),
      ∃ w : AHarmonicFunction a (cubeSet R),
        (∀ x ∈ cubeSet R,
          u x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
        (BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => w.toH1.grad x)) →
        (cubeBesovNegativeVectorSeminormTwo R s
            (fun x => matVecMul (a x) (u x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x => matVecMul (a x) (u x))) ^ 2) +
          2 * ((geometricDiscount s 2)⁻¹ * LambdaSq R s (.finite 2) a) *
            cubeAverage R (coefficientEnergyDensity a u) +
          η * (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2 +
          η * (cubeBesovNegativeVectorSeminormTwo R s (fun x => w.toH1.grad x)) ^ 2 +
          2 * η⁻¹ *
            (((((geometricDiscount s 2)⁻¹ * LambdaSq R s (.finite 2) a) *
                ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))) *
              cubeBesovPositiveVectorSeminormTwo R s
                (fun x => g x - cubeAverageVec R g)) ^ 2)) := by
  rcases
      exists_centeredCorrector_aHarmonicRemainder_of_parent_potential_solenoidal_h1CoerciveEstimate
        (P := P) (R := R) (n := n) (a := a) (g := g) (u := u)
        (lam := lam) (Lam := Lam)
        hu_potential hu_residual hR hEllR hu_memR hg_memR hC with
    ⟨ω, w, huw⟩
  refine ⟨ω, w, huw, ?_⟩
  intro hwBdd
  exact
    ω.sq_cubeBesovNegativeVectorSeminormTwo_flux_le_descendantsAverage_add_uCoeffEnergy_add_eta_uSq_eta_wSq_invEta_gSq_of_childBddAbove
      (u := u) w s hs hη hEllR hu_memR hg_memR
      (cubeAverageFluxEnergyControl_of_aHarmonicFunction
        (Q := R) (a := a) hEllR w hDataR)
      hsum huw hchildBdd huBdd hwBdd hgBdd

end MeanZeroNeumannCorrectorData

/--
PDE-facing full-seminorm local recurrence interface for the weak-flux RHS lane.

This is the one-cube recurrence after constructing the centered Neumann
corrector from an `H¹` RHS weak solution. -/
theorem exists_centeredNeumannCorrector_aHarmonicRemainder_fluxSeminormStepEnergy_of_h1DirichletRhsWeakSolutionOn
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (g : Vec d → Vec d) (u : H1Function (cubeSet Q)) {s lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hg : MemVectorL2 (cubeSet Q) g)
    (hC : H1CoerciveEstimate (cubeSet Q)) :
    ∃ ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g),
      ∃ w : AHarmonicFunction a (cubeSet Q),
        (∀ x ∈ cubeSet Q,
          u.grad x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
        ∀ energy : Vec d → ℝ,
          (∀ x ∈ cubeSet Q, 0 ≤ energy x) →
          MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume →
          CubeAverageFluxEnergyControl Q a
            (fun x => matVecMul (a x) (w.toH1.grad x)) energy →
          Summable (fun n : ℕ =>
            geometricWeight s 2 n *
              maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) →
          (∀ R ∈ descendantsAtDepth Q 1,
            BddAbove (Set.range fun N : ℕ =>
              cubeBesovNegativeVectorPartialSeminormTwo R s N
                (fun x => matVecMul (a x) (u.grad x)))) →
          (cubeBesovNegativeVectorSeminormTwo Q s
              (fun x => matVecMul (a x) (u.grad x))) ^ 2 ≤
            Real.rpow (3 : ℝ) (-2 * s) *
              descendantsAverage Q 1
                (fun R =>
                  (cubeBesovNegativeVectorSeminormTwo R s
                    (fun x => matVecMul (a x) (u.grad x))) ^ 2) +
            (geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a *
              cubeAverage Q energy := by
  rcases
      exists_centeredNeumannCorrector_aHarmonicRemainder_of_h1DirichletRhsWeakSolutionOn
        (Q := Q) (a := a) (g := g) (u := u)
        hEll hu hg hC with
    ⟨ω, w, huw⟩
  refine ⟨ω, w, huw, ?_⟩
  intro energy henergy_nonneg henergy_int hflux hsum hchildBdd
  exact
    ω.sq_cubeBesovNegativeVectorSeminormTwo_flux_le_descendantsAverage_add_harmonic_energy_of_childBddAbove
      (u := u.grad) w s hs energy hEll u.grad_memVectorL2 hg
      henergy_nonneg henergy_int hflux hsum huw hchildBdd

/--
PDE-facing coefficient-energy local recurrence for the weak-flux RHS lane.

This is the Step-2-ready form of the one-cube recurrence after constructing
the centered Neumann corrector from an `H¹` RHS weak solution. -/
theorem exists_centeredNeumannCorrector_aHarmonicRemainder_fluxSeminormStepCoeffEnergy_of_h1DirichletRhsWeakSolutionOn
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (g : Vec d → Vec d) (u : H1Function (cubeSet Q)) {s lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hg : MemVectorL2 (cubeSet Q) g)
    (hC : H1CoerciveEstimate (cubeSet Q)) :
    ∃ ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g),
      ∃ w : AHarmonicFunction a (cubeSet Q),
        (∀ x ∈ cubeSet Q,
          u.grad x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
        (CubeAverageFluxEnergyControl Q a
            (fun x => matVecMul (a x) (w.toH1.grad x))
            (coefficientEnergyDensity a (fun x => w.toH1.grad x)) →
          Summable (fun n : ℕ =>
            geometricWeight s 2 n *
              maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) →
          (∀ R ∈ descendantsAtDepth Q 1,
            BddAbove (Set.range fun N : ℕ =>
              cubeBesovNegativeVectorPartialSeminormTwo R s N
                (fun x => matVecMul (a x) (u.grad x)))) →
          (cubeBesovNegativeVectorSeminormTwo Q s
              (fun x => matVecMul (a x) (u.grad x))) ^ 2 ≤
            Real.rpow (3 : ℝ) (-2 * s) *
              descendantsAverage Q 1
                (fun R =>
                  (cubeBesovNegativeVectorSeminormTwo R s
                    (fun x => matVecMul (a x) (u.grad x))) ^ 2) +
            2 * ((geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a) *
              cubeAverage Q (coefficientEnergyDensity a u.grad) +
            2 * ((geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a) *
              cubeAverage Q
                (coefficientEnergyDensity a
                  (fun x => ω.toH1MeanZero.toH1Function.grad x))) := by
  rcases
      exists_centeredNeumannCorrector_aHarmonicRemainder_of_h1DirichletRhsWeakSolutionOn
        (Q := Q) (a := a) (g := g) (u := u)
        hEll hu hg hC with
    ⟨ω, w, huw⟩
  refine ⟨ω, w, huw, ?_⟩
  intro hflux hsum hchildBdd
  exact
    ω.sq_cubeBesovNegativeVectorSeminormTwo_flux_le_descendantsAverage_add_uCoeffEnergy_add_correctorCoeffEnergy_of_childBddAbove
      (u := u.grad) w s hs hEll u.grad_memVectorL2 hg hflux hsum huw hchildBdd

/--
PDE-facing coefficient-energy recurrence with harmonic flux control supplied by
deterministic coarse data. -/
theorem exists_centeredNeumannCorrector_aHarmonicRemainder_fluxSeminormStepCoeffEnergy_of_h1DirichletRhsWeakSolutionOn_of_coarseData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g : Vec d → Vec d) (u : H1Function (cubeSet Q)) {s lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hg : MemVectorL2 (cubeSet Q) g)
    (hC : H1CoerciveEstimate (cubeSet Q))
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a))
    (hchildBdd :
      ∀ R ∈ descendantsAtDepth Q 1,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => matVecMul (a x) (u.grad x)))) :
    ∃ ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g),
      ∃ w : AHarmonicFunction a (cubeSet Q),
        (∀ x ∈ cubeSet Q,
          u.grad x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
        (cubeBesovNegativeVectorSeminormTwo Q s
            (fun x => matVecMul (a x) (u.grad x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage Q 1
              (fun R =>
                (cubeBesovNegativeVectorSeminormTwo R s
                  (fun x => matVecMul (a x) (u.grad x))) ^ 2) +
          2 * ((geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a) *
            cubeAverage Q (coefficientEnergyDensity a u.grad) +
          2 * ((geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a) *
            cubeAverage Q
              (coefficientEnergyDensity a
                (fun x => ω.toH1MeanZero.toH1Function.grad x)) := by
  rcases
      exists_centeredNeumannCorrector_aHarmonicRemainder_fluxSeminormStepCoeffEnergy_of_h1DirichletRhsWeakSolutionOn
        (Q := Q) (a := a) (g := g) (u := u)
        (s := s) (lam := lam) (Lam := Lam)
        hs hEll hu hg hC with
    ⟨ω, w, huw, hstep⟩
  refine ⟨ω, w, huw, ?_⟩
  exact
    hstep
      (cubeAverageFluxEnergyControl_of_aHarmonicFunction
        (Q := Q) (a := a) hEll w hData)
      hsum hchildBdd

/--
PDE-facing coefficient-energy recurrence with the corrector term replaced by
the short centered Besov product bound.  As in the descendant-cube wrapper, the
harmonic boundedness assumption is exposed after the harmonic remainder has
been constructed. -/
theorem exists_centeredNeumannCorrector_aHarmonicRemainder_fluxSeminormStepShortTerm_of_h1DirichletRhsWeakSolutionOn_of_coarseData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g : Vec d → Vec d) (u : H1Function (cubeSet Q)) {s lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hg : MemVectorL2 (cubeSet Q) g)
    (hC : H1CoerciveEstimate (cubeSet Q))
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a))
    (hchildBdd :
      ∀ R ∈ descendantsAtDepth Q 1,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => matVecMul (a x) (u.grad x))))
    (huBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N u.grad))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => g x - cubeAverageVec Q g))) :
    ∃ ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g),
      ∃ w : AHarmonicFunction a (cubeSet Q),
        (∀ x ∈ cubeSet Q,
          u.grad x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
        (BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo Q s N
            (fun x => w.toH1.grad x)) →
        (cubeBesovNegativeVectorSeminormTwo Q s
            (fun x => matVecMul (a x) (u.grad x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage Q 1
              (fun R =>
                (cubeBesovNegativeVectorSeminormTwo R s
                  (fun x => matVecMul (a x) (u.grad x))) ^ 2) +
          2 * ((geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a) *
            cubeAverage Q (coefficientEnergyDensity a u.grad) +
          2 * ((geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a) *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) *
              (Real.sqrt 2 *
                (cubeBesovNegativeVectorSeminormTwo Q s u.grad +
                  cubeBesovNegativeVectorSeminormTwo Q s
                    (fun x => w.toH1.grad x))) *
              cubeBesovPositiveVectorSeminormTwo Q s
                (fun x => g x - cubeAverageVec Q g)))) := by
  rcases
      exists_centeredNeumannCorrector_aHarmonicRemainder_of_h1DirichletRhsWeakSolutionOn
        (Q := Q) (a := a) (g := g) (u := u)
        hEll hu hg hC with
    ⟨ω, w, huw⟩
  refine ⟨ω, w, huw, ?_⟩
  intro hwBdd
  exact
    ω.sq_cubeBesovNegativeVectorSeminormTwo_flux_le_descendantsAverage_add_uCoeffEnergy_add_correctorShortTerm_of_childBddAbove
      (u := u.grad) w s hs hEll u.grad_memVectorL2 hg
      (cubeAverageFluxEnergyControl_of_aHarmonicFunction
        (Q := Q) (a := a) hEll w hData)
      hsum huw hchildBdd huBdd hwBdd hgBdd

/--
PDE-facing recurrence with the short corrector product absorbed into quadratic
`u`, harmonic, and forcing terms. -/
theorem exists_centeredNeumannCorrector_aHarmonicRemainder_fluxSeminormStepAbsorbedShortTerm_of_h1DirichletRhsWeakSolutionOn_of_coarseData
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g : Vec d → Vec d) (u : H1Function (cubeSet Q)) {s η lam Lam : ℝ}
    (hs : 0 < s) (hη : 0 < η)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hu : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hg : MemVectorL2 (cubeSet Q) g)
    (hC : H1CoerciveEstimate (cubeSet Q))
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 2 n *
          maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a))
    (hchildBdd :
      ∀ R ∈ descendantsAtDepth Q 1,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fun x => matVecMul (a x) (u.grad x))))
    (huBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N u.grad))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => g x - cubeAverageVec Q g))) :
    ∃ ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g),
      ∃ w : AHarmonicFunction a (cubeSet Q),
        (∀ x ∈ cubeSet Q,
          u.grad x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) ∧
        (BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo Q s N
            (fun x => w.toH1.grad x)) →
        (cubeBesovNegativeVectorSeminormTwo Q s
            (fun x => matVecMul (a x) (u.grad x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage Q 1
              (fun R =>
                (cubeBesovNegativeVectorSeminormTwo R s
                  (fun x => matVecMul (a x) (u.grad x))) ^ 2) +
          2 * ((geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a) *
            cubeAverage Q (coefficientEnergyDensity a u.grad) +
          η * (cubeBesovNegativeVectorSeminormTwo Q s u.grad) ^ 2 +
          η * (cubeBesovNegativeVectorSeminormTwo Q s (fun x => w.toH1.grad x)) ^ 2 +
          2 * η⁻¹ *
            (((((geometricDiscount s 2)⁻¹ * LambdaSq Q s (.finite 2) a) *
                ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))) *
              cubeBesovPositiveVectorSeminormTwo Q s
                (fun x => g x - cubeAverageVec Q g)) ^ 2)) := by
  rcases
      exists_centeredNeumannCorrector_aHarmonicRemainder_of_h1DirichletRhsWeakSolutionOn
        (Q := Q) (a := a) (g := g) (u := u)
        hEll hu hg hC with
    ⟨ω, w, huw⟩
  refine ⟨ω, w, huw, ?_⟩
  intro hwBdd
  exact
    ω.sq_cubeBesovNegativeVectorSeminormTwo_flux_le_descendantsAverage_add_uCoeffEnergy_add_eta_uSq_eta_wSq_invEta_gSq_of_childBddAbove
      (u := u.grad) w s hs hη hEll u.grad_memVectorL2 hg
      (cubeAverageFluxEnergyControl_of_aHarmonicFunction
        (Q := Q) (a := a) hEll w hData)
      hsum huw hchildBdd huBdd hwBdd hgBdd

end

end Homogenization
