/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.DualityPositiveBridge.CoordinateStandard

/-! # Duality Positive Bridge -/

namespace Homogenization

noncomputable section

open scoped BigOperators ENNReal

/-!
# Positive-test bridge helper lemmas

This file contains the shared PDE identity and full-dual bookkeeping lemmas
used by the sharp-boundary scalar duality assembly.  The old all-exponent
coordinate bridge route has been removed from the active code path.
-/

private theorem cubeBesovConjExponent_two_eq_positiveBridge :
    cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
  simpa [cubeBesovConjExponent] using
    (ENNReal.HolderConjugate.conjExponent_eq
      (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))

private theorem cubeBesovConjExponent_two_ne_zero_positiveBridge :
    cubeBesovConjExponent (2 : ℝ≥0∞) ≠ 0 := by
  rw [cubeBesovConjExponent_two_eq_positiveBridge]
  norm_num

private theorem cubeBesovConjExponent_two_ne_top_positiveBridge :
    cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
  rw [cubeBesovConjExponent_two_eq_positiveBridge]
  norm_num

/--
Componentwise scalar full-dual pairing bounds control the note-normalized
vector genuine-dual negative Besov norm.

This is the bookkeeping supremum step used by the restored deterministic
duality proof: after the PDE identity bounds each scalar component against
every unit full-dual test, the vector norm is obtained by summing over
coordinates and multiplying by the parent scale weight.
-/
theorem cubeScaleNormalizedDualNegativeBesovVectorNormTwo_le_of_forall_component_fullTest_pairing_le
    {d : ℕ} (Q : TriadicCube d) (t : ℝ) (F : Vec d → Vec d)
    {B : Fin d → ℝ}
    (hB :
      ∀ (i : Fin d) (g : Vec d → ℝ),
        CubeBesovDualFullTest Q t (2 : ℝ≥0∞) (2 : ℝ≥0∞) g →
          |cubeBesovPairing Q (fun x => F x i) g| ≤ B i) :
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t F ≤
      cubeBesovScaleWeight t Q * ∑ i : Fin d, B i := by
  unfold cubeScaleNormalizedDualNegativeBesovVectorNormTwo
  refine mul_le_mul_of_nonneg_left ?_ (cubeBesovScaleWeight_nonneg t Q)
  refine Finset.sum_le_sum ?_
  intro i _hi
  exact
    cubeBesovDualFullNorm_le_of_forall_fullTest_pairing_le
      Q t (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => F x i)
      cubeBesovConjExponent_two_ne_zero_positiveBridge
      cubeBesovConjExponent_two_ne_top_positiveBridge
      (fun g hg => hB i g hg)

/--
Uniform scalar full-dual pairing bounds control the note-normalized vector
genuine-dual negative Besov norm with the expected coordinate-cardinality
factor.
-/
theorem cubeScaleNormalizedDualNegativeBesovVectorNormTwo_le_card_mul_of_forall_component_fullTest_pairing_le
    {d : ℕ} (Q : TriadicCube d) (t : ℝ) (F : Vec d → Vec d) {B : ℝ}
    (hB :
      ∀ (i : Fin d) (g : Vec d → ℝ),
        CubeBesovDualFullTest Q t (2 : ℝ≥0∞) (2 : ℝ≥0∞) g →
          |cubeBesovPairing Q (fun x => F x i) g| ≤ B) :
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q t F ≤
      cubeBesovScaleWeight t Q * ((Fintype.card (Fin d) : ℝ) * B) := by
  have h :=
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo_le_of_forall_component_fullTest_pairing_le
      (Q := Q) (t := t) (F := F) (B := fun _ : Fin d => B)
      (fun i g hg => hB i g hg)
  simpa [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin] using h

/-- Any normalized-cube `L²` vector datum has a zero-trace weak solution to the
Dirichlet divergence problem on the corresponding open cube. -/
theorem exists_cubeDirichletDivergenceProblem_of_memLp_normalizedCubeMeasure
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {h : Vec d → Vec d}
    (hh : MeasureTheory.MemLp h (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ∃ w : H10Function (openCubeSet Q),
      CubeDirichletDivergenceProblem Q w h := by
  let U : Set (Vec d) := openCubeSet Q
  let a : CoeffField d := identityCoeffField d
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [U, volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hRealize :
      PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization U :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      (by simpa [U] using isOpenBoundedConvexDomain_openCubeSet Q)
  have hEll : IsEllipticFieldOn 1 1 U a := by
    simpa [a] using isEllipticFieldOn_identityCoeffField
      (d := d) (U := U) (by simpa [U] using measurableSet_openCubeSet Q)
  have hhOpen : MemVectorL2 U h := by
    simpa [U] using memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hh
  have hneg : MemVectorL2 U (fun x => -h x) := by
    simpa [Pi.neg_apply] using! hhOpen.neg
  rcases
      exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
        (a := a) (U := U) (g := fun x => -h x)
        (lam := 1) (Lam := 1)
        hneg hRealize
        (by simpa [U] using openCubeSet_nonempty_internal Q) hEll
    with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  intro φ
  have hsol := hw φ
  have hleft :
      ∫ x in openCubeSet Q,
          vecDot (matVecMul (a x) (w.toH1Function.grad x))
            (φ.toH1Function.grad x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q,
          vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x)
            ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q) ?_
    intro x _hx
    simp [a, matVecMul_identityCoeffField]
  have hright :
      ∫ x in openCubeSet Q,
          vecDot ((fun x => -h x) x) (φ.toH1Function.grad x)
            ∂MeasureTheory.volume =
        -∫ x in openCubeSet Q,
          vecDot (h x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
    calc
      ∫ x in openCubeSet Q,
          vecDot ((fun x => -h x) x) (φ.toH1Function.grad x)
            ∂MeasureTheory.volume
          =
            ∫ x in openCubeSet Q,
              -vecDot (h x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
              refine MeasureTheory.setIntegral_congr_fun
                (measurableSet_openCubeSet Q) ?_
              intro x _hx
              simp [vecDot_neg_left]
      _ =
          -∫ x in openCubeSet Q,
            vecDot (h x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_neg]
  calc
    ∫ x in openCubeSet Q,
        vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume
        =
          ∫ x in openCubeSet Q,
            vecDot (matVecMul (a x) (w.toH1Function.grad x))
              (φ.toH1Function.grad x) ∂MeasureTheory.volume := hleft.symm
    _ =
          ∫ x in openCubeSet Q,
            vecDot ((fun x => -h x) x) (φ.toH1Function.grad x)
              ∂MeasureTheory.volume := by
          simpa [U] using hsol
    _ =
          -∫ x in openCubeSet Q,
            vecDot (h x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := hright

/--
Weak-form identity behind the scalar-background solution-comparison duality
argument.

If `v` solves the Dirichlet divergence problem with datum `h`, `w` is a
zero-trace potential field, and `sigma0 w + F` is solenoidal, then the pairing
of the scalar-background comparison field `sigma0 w` against `h` is equal to
the pairing of the flux defect `F` against the dual solution gradient.
-/
theorem dirichletDivergence_solutionComparison_integral_identity
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {sigma0 : ℝ}
    {w F h : Vec d → Vec d} {v : H10Function (openCubeSet Q)}
    (hF : MemVectorL2 (cubeSet Q) F)
    (hdiv : CubeDirichletDivergenceProblem Q v h)
    (hw : IsPotentialZeroTraceOn (cubeSet Q) w)
    (hsol : IsSolenoidalOn (cubeSet Q)
      (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x)) :
    ∫ x in openCubeSet Q,
        vecDot (matVecMul (scalarMatrix (d := d) sigma0) (w x)) (h x)
          ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q,
        vecDot (F x) (v.toH1Function.grad x) ∂MeasureTheory.volume := by
  have hwOpen : IsPotentialZeroTraceOn (openCubeSet Q) w :=
    isPotentialZeroTraceOn_openCubeSet_triadicCube_of_cubeSet hw
  rcases hwOpen with ⟨u, hu⟩
  have hwL2Open : MemVectorL2 (openCubeSet Q) w :=
    memVectorL2_of_isPotentialZeroTraceOn ⟨u, hu⟩
  have hFOpen : MemVectorL2 (openCubeSet Q) F := by
    simpa [MemVectorL2, volumeMeasureOn, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
      using hF
  have hSigmaL2Open :
      MemVectorL2 (openCubeSet Q)
        (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x)) := by
    simpa [matVecMul_scalarMatrix] using! hwL2Open.const_smul sigma0
  have hSigmaVInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (matVecMul (scalarMatrix (d := d) sigma0) (w x))
          (v.toH1Function.grad x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hSigmaL2Open v.toH1Function.grad_memVectorL2
  have hFVInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (F x) (v.toH1Function.grad x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hFOpen v.toH1Function.grad_memVectorL2
  have hsolOpen :
      IsSolenoidalOn (openCubeSet Q)
        (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x) :=
    isSolenoidalOn_openCubeSet_triadicCube_of_cubeSet hsol
  have hsolv := hsolOpen v
  have hsolSplit :
      (∫ x in openCubeSet Q,
          vecDot (matVecMul (scalarMatrix (d := d) sigma0) (w x))
            (v.toH1Function.grad x) ∂MeasureTheory.volume) +
        ∫ x in openCubeSet Q,
          vecDot (F x) (v.toH1Function.grad x) ∂MeasureTheory.volume = 0 := by
    rw [← MeasureTheory.integral_add hSigmaVInt hFVInt]
    simpa [Pi.add_apply, vecDot_add_left] using hsolv
  have hdivu := hdiv u
  have hdivw :
      ∫ x in openCubeSet Q,
          vecDot (v.toH1Function.grad x) (w x) ∂MeasureTheory.volume =
        -∫ x in openCubeSet Q, vecDot (h x) (w x) ∂MeasureTheory.volume := by
    simpa [hu] using hdivu
  have hleft_smul :
      ∫ x in openCubeSet Q,
          vecDot (matVecMul (scalarMatrix (d := d) sigma0) (w x)) (h x)
            ∂MeasureTheory.volume =
        sigma0 *
          ∫ x in openCubeSet Q, vecDot (w x) (h x) ∂MeasureTheory.volume := by
    calc
      ∫ x in openCubeSet Q,
          vecDot (matVecMul (scalarMatrix (d := d) sigma0) (w x)) (h x)
            ∂MeasureTheory.volume
          =
            ∫ x in openCubeSet Q,
              sigma0 * vecDot (w x) (h x) ∂MeasureTheory.volume := by
            refine MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q) ?_
            intro x _hx
            simp [matVecMul_scalarMatrix, vecDot_smul_left]
      _ =
          sigma0 *
            ∫ x in openCubeSet Q, vecDot (w x) (h x) ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_const_mul]
  have hwh_comm :
      ∫ x in openCubeSet Q, vecDot (w x) (h x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q, vecDot (h x) (w x) ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q) ?_
    intro x _hx
    exact vecDot_comm (w x) (h x)
  have hvw_comm :
      ∫ x in openCubeSet Q,
          vecDot (v.toH1Function.grad x) (w x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q,
          vecDot (w x) (v.toH1Function.grad x) ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q) ?_
    intro x _hx
    exact vecDot_comm (v.toH1Function.grad x) (w x)
  have hhw_eq_neg :
      ∫ x in openCubeSet Q, vecDot (w x) (h x) ∂MeasureTheory.volume =
        -∫ x in openCubeSet Q,
          vecDot (w x) (v.toH1Function.grad x) ∂MeasureTheory.volume := by
    linarith
  have hsolScalar :
      sigma0 *
          (∫ x in openCubeSet Q,
            vecDot (w x) (v.toH1Function.grad x) ∂MeasureTheory.volume) +
        ∫ x in openCubeSet Q,
          vecDot (F x) (v.toH1Function.grad x) ∂MeasureTheory.volume = 0 := by
    have hSigmaV :
        ∫ x in openCubeSet Q,
            vecDot (matVecMul (scalarMatrix (d := d) sigma0) (w x))
              (v.toH1Function.grad x) ∂MeasureTheory.volume =
          sigma0 *
            ∫ x in openCubeSet Q,
              vecDot (w x) (v.toH1Function.grad x) ∂MeasureTheory.volume := by
      calc
        ∫ x in openCubeSet Q,
            vecDot (matVecMul (scalarMatrix (d := d) sigma0) (w x))
              (v.toH1Function.grad x) ∂MeasureTheory.volume
            =
              ∫ x in openCubeSet Q,
                sigma0 * vecDot (w x) (v.toH1Function.grad x)
                  ∂MeasureTheory.volume := by
              refine MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q) ?_
              intro x _hx
              simp [matVecMul_scalarMatrix, vecDot_smul_left]
        _ =
            sigma0 *
              ∫ x in openCubeSet Q,
                vecDot (w x) (v.toH1Function.grad x) ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_const_mul]
    linarith
  calc
    ∫ x in openCubeSet Q,
        vecDot (matVecMul (scalarMatrix (d := d) sigma0) (w x)) (h x)
          ∂MeasureTheory.volume
        =
          sigma0 *
            ∫ x in openCubeSet Q, vecDot (w x) (h x) ∂MeasureTheory.volume :=
      hleft_smul
    _ =
          -sigma0 *
            ∫ x in openCubeSet Q,
              vecDot (w x) (v.toH1Function.grad x) ∂MeasureTheory.volume := by
      rw [hhw_eq_neg]
      ring
    _ =
          ∫ x in openCubeSet Q,
            vecDot (F x) (v.toH1Function.grad x) ∂MeasureTheory.volume := by
      linarith

/--
Companion weak-form identity for the flux-comparison field `sigma0 w + F`.
After the previous identity, the extra term is exactly the direct pairing of
the flux defect `F` with the input dual datum `h`.
-/
theorem dirichletDivergence_fluxComparison_integral_identity
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {sigma0 : ℝ}
    {w F h : Vec d → Vec d} {v : H10Function (openCubeSet Q)}
    (hF : MemVectorL2 (cubeSet Q) F)
    (hh : MemVectorL2 (openCubeSet Q) h)
    (hdiv : CubeDirichletDivergenceProblem Q v h)
    (hw : IsPotentialZeroTraceOn (cubeSet Q) w)
    (hsol : IsSolenoidalOn (cubeSet Q)
      (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x)) :
    ∫ x in openCubeSet Q,
        vecDot (matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x) (h x)
          ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q,
        vecDot (F x) (v.toH1Function.grad x + h x) ∂MeasureTheory.volume := by
  have hmain :=
    dirichletDivergence_solutionComparison_integral_identity
      (Q := Q) (sigma0 := sigma0) (w := w) (F := F) (h := h) (v := v)
      hF hdiv hw hsol
  have hwOpen : IsPotentialZeroTraceOn (openCubeSet Q) w :=
    isPotentialZeroTraceOn_openCubeSet_triadicCube_of_cubeSet hw
  rcases hwOpen with ⟨u, hu⟩
  have hwL2Open : MemVectorL2 (openCubeSet Q) w :=
    memVectorL2_of_isPotentialZeroTraceOn ⟨u, hu⟩
  have hFOpen : MemVectorL2 (openCubeSet Q) F := by
    simpa [MemVectorL2, volumeMeasureOn, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
      using hF
  have hSigmaL2Open :
      MemVectorL2 (openCubeSet Q)
        (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x)) := by
    simpa [matVecMul_scalarMatrix] using! hwL2Open.const_smul sigma0
  have hSigmaHInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (matVecMul (scalarMatrix (d := d) sigma0) (w x)) (h x))
        (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hSigmaL2Open hh
  have hFHInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (F x) (h x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hFOpen hh
  have hFVInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (F x) (v.toH1Function.grad x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hFOpen v.toH1Function.grad_memVectorL2
  have hleft_split :
      ∫ x in openCubeSet Q,
          vecDot (matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x) (h x)
            ∂MeasureTheory.volume =
        (∫ x in openCubeSet Q,
          vecDot (matVecMul (scalarMatrix (d := d) sigma0) (w x)) (h x)
            ∂MeasureTheory.volume) +
          ∫ x in openCubeSet Q, vecDot (F x) (h x) ∂MeasureTheory.volume := by
    rw [← MeasureTheory.integral_add hSigmaHInt hFHInt]
    simp [vecDot_add_left]
  have hright_split :
      ∫ x in openCubeSet Q,
          vecDot (F x) (v.toH1Function.grad x + h x) ∂MeasureTheory.volume =
        (∫ x in openCubeSet Q,
          vecDot (F x) (v.toH1Function.grad x) ∂MeasureTheory.volume) +
          ∫ x in openCubeSet Q, vecDot (F x) (h x) ∂MeasureTheory.volume := by
    rw [← MeasureTheory.integral_add hFVInt hFHInt]
    simp [vecDot_add_right]
  calc
    ∫ x in openCubeSet Q,
        vecDot (matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x) (h x)
          ∂MeasureTheory.volume
        =
          (∫ x in openCubeSet Q,
            vecDot (matVecMul (scalarMatrix (d := d) sigma0) (w x)) (h x)
              ∂MeasureTheory.volume) +
            ∫ x in openCubeSet Q, vecDot (F x) (h x) ∂MeasureTheory.volume :=
      hleft_split
    _ =
          (∫ x in openCubeSet Q,
            vecDot (F x) (v.toH1Function.grad x) ∂MeasureTheory.volume) +
            ∫ x in openCubeSet Q, vecDot (F x) (h x) ∂MeasureTheory.volume := by
      rw [hmain]
    _ =
          ∫ x in openCubeSet Q,
            vecDot (F x) (v.toH1Function.grad x + h x) ∂MeasureTheory.volume :=
      hright_split.symm

theorem cubeAverage_eq_inv_cubeVolume_mul_setIntegral_openCubeSet {d : ℕ}
    (Q : TriadicCube d) (f : Vec d → ℝ) :
    cubeAverage Q f =
      (cubeVolume Q)⁻¹ *
        ∫ x in openCubeSet Q, f x ∂MeasureTheory.volume := by
  unfold cubeAverage
  rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet]

/-- Linearity of vector pairings in the test field, written for cube averages
over the open-cube representative. -/
theorem cubeAverage_vecDot_add_right
    {d : ℕ} (Q : TriadicCube d) (F H K : Vec d → Vec d)
    (hF : MemVectorL2 (openCubeSet Q) F)
    (hH : MemVectorL2 (openCubeSet Q) H)
    (hK : MemVectorL2 (openCubeSet Q) K) :
    cubeAverage Q (fun x => vecDot (F x) (H x + K x)) =
      cubeAverage Q (fun x => vecDot (F x) (H x)) +
        cubeAverage Q (fun x => vecDot (F x) (K x)) := by
  have hFH :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (F x) (H x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hF hH
  have hFK :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (F x) (K x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hF hK
  rw [cubeAverage_eq_inv_cubeVolume_mul_setIntegral_openCubeSet,
    cubeAverage_eq_inv_cubeVolume_mul_setIntegral_openCubeSet,
    cubeAverage_eq_inv_cubeVolume_mul_setIntegral_openCubeSet]
  have hfun :
      (fun x : Vec d => vecDot (F x) (H x + K x)) =
        fun x => vecDot (F x) (H x) + vecDot (F x) (K x) := by
    funext x
    rw [vecDot_add_right]
  rw [hfun, MeasureTheory.integral_add hFH hFK]
  ring

theorem abs_cubeAverage_vecDot_add_right_le
    {d : ℕ} (Q : TriadicCube d) (F H K : Vec d → Vec d)
    (hF : MemVectorL2 (openCubeSet Q) F)
    (hH : MemVectorL2 (openCubeSet Q) H)
    (hK : MemVectorL2 (openCubeSet Q) K) :
    |cubeAverage Q (fun x => vecDot (F x) (H x + K x))| ≤
      |cubeAverage Q (fun x => vecDot (F x) (H x))| +
        |cubeAverage Q (fun x => vecDot (F x) (K x))| := by
  rw [cubeAverage_vecDot_add_right Q F H K hF hH hK]
  exact abs_add_le _ _

/--
Normalized `cubeBesovPairing` form of
`dirichletDivergence_solutionComparison_integral_identity`.
-/
theorem cubeBesovPairing_solutionComparison_component_eq_cubeAverage_fluxDefect_dualGradient
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {sigma0 : ℝ}
    {w F : Vec d → Vec d} {v : H10Function (openCubeSet Q)}
    (i : Fin d) (g : Vec d → ℝ)
    (hF : MemVectorL2 (cubeSet Q) F)
    (hdiv : CubeDirichletDivergenceProblem Q v (coordinateVectorField i g))
    (hw : IsPotentialZeroTraceOn (cubeSet Q) w)
    (hsol : IsSolenoidalOn (cubeSet Q)
      (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x)) :
    cubeBesovPairing Q
        (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) i) g =
      cubeAverage Q
        (fun x => vecDot (F x) (v.toH1Function.grad x)) := by
  rw [cubeBesovPairing_component_eq_cubeAverage_vecDot_coordinateVectorField]
  rw [cubeAverage_eq_inv_cubeVolume_mul_setIntegral_openCubeSet,
    cubeAverage_eq_inv_cubeVolume_mul_setIntegral_openCubeSet]
  exact congrArg (fun I : ℝ => (cubeVolume Q)⁻¹ * I)
    (dirichletDivergence_solutionComparison_integral_identity
      (Q := Q) (sigma0 := sigma0) (w := w) (F := F)
      (h := coordinateVectorField i g) (v := v) hF hdiv hw hsol)

/--
Normalized `cubeBesovPairing` form of
`dirichletDivergence_fluxComparison_integral_identity`.
-/
theorem cubeBesovPairing_fluxComparison_component_eq_cubeAverage_fluxDefect_dualGradient_add_coordinate
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {sigma0 s : ℝ}
    {w F : Vec d → Vec d} {v : H10Function (openCubeSet Q)}
    (i : Fin d) {g : Vec d → ℝ}
    (hg : CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) g)
    (hF : MemVectorL2 (cubeSet Q) F)
    (hdiv : CubeDirichletDivergenceProblem Q v (coordinateVectorField i g))
    (hw : IsPotentialZeroTraceOn (cubeSet Q) w)
    (hsol : IsSolenoidalOn (cubeSet Q)
      (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x)) :
    cubeBesovPairing Q
        (fun x => (matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x) i) g =
      cubeAverage Q
        (fun x => vecDot (F x)
          (v.toH1Function.grad x + coordinateVectorField i g x)) := by
  have hcoordLp :
      MeasureTheory.MemLp (coordinateVectorField i g) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) :=
    coordinateVectorField_memLp_of_cubeBesovDualFullTest_two_two hg
  have hcoordOpen : MemVectorL2 (openCubeSet Q) (coordinateVectorField i g) :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hcoordLp
  rw [cubeBesovPairing_component_eq_cubeAverage_vecDot_coordinateVectorField]
  rw [cubeAverage_eq_inv_cubeVolume_mul_setIntegral_openCubeSet,
    cubeAverage_eq_inv_cubeVolume_mul_setIntegral_openCubeSet]
  exact congrArg (fun I : ℝ => (cubeVolume Q)⁻¹ * I)
    (dirichletDivergence_fluxComparison_integral_identity
      (Q := Q) (sigma0 := sigma0) (w := w) (F := F)
      (h := coordinateVectorField i g) (v := v) hF hcoordOpen hdiv hw hsol)

theorem cubeBesovScaleWeight_mul_neg_self {d : ℕ} (s : ℝ) (Q : TriadicCube d) :
    cubeBesovScaleWeight s Q * cubeBesovScaleWeight (-s) Q = 1 := by
  rw [cubeBesovScaleWeight_mul_eq_scaleWeight_add]
  simp [cubeBesovScaleWeight]

end

end Homogenization
