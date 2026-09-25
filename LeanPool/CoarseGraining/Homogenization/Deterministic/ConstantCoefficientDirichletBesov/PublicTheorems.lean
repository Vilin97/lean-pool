/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.ConcreteAveraging

/-! # Public Theorems -/

@[expose] public section

namespace Homogenization

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Pointwise

/-- Pure/K-interface analytic input: finite-level K-functional partial sums
are controlled by the overlapping positive partial sums and mean term.

This is proved by the concrete smooth overlap averaging operator and the
K-functional depth/partial assembly. -/
theorem cubeKBesovPartialBoundByOverlappingPositive
    (d : ℕ) [NeZero d] :
    CubeKBesovPartialBoundByOverlappingPositive d :=
  cubeKBesovPartialBoundByOverlappingPositive_concrete d

/-- Uniform pure/K-interface input: finite-level K-functional partial sums are
controlled by the overlapping positive partial sums and mean term with a
dimension-only constant, independent of `s`. -/
theorem cubeKBesovPartialBoundByOverlappingPositiveUniform
    (d : ℕ) [NeZero d] :
    CubeKBesovPartialBoundByOverlappingPositiveUniform d
      (2 * concreteOverlapAveragingCompetitorConstant d) :=
  cubeKBesovPartialBoundByOverlappingPositiveUniform_concrete d

/-- Pure/K-interface analytic input: overlapping Besov regularity gives bounded
canonical K-functional partial sums. -/
theorem cubeKBesovInputBoundednessOfOverlappingHRegularity
    (d : ℕ) [NeZero d] :
    CubeKBesovInputBoundednessOfOverlappingHRegularity d :=
  cubeKBesovInputBoundednessOfOverlappingHRegularity_of_partialBoundByOverlappingPositive
    (cubeKBesovPartialBoundByOverlappingPositive d)

/-- Mean-term estimate for zero-Dirichlet divergence solutions. This is
proved by transporting the open-cube zero-trace function to the half-open cube
used by `cubeAverageVec`, then applying the zero-trace averaged-gradient
identity. -/
theorem cubeDirichletGradientAverageRegularity
    (d : ℕ) [NeZero d] :
    CubeDirichletGradientAverageRegularity d := by
  refine ⟨0, le_rfl, ?_⟩
  intro Q _h w _hweak
  have hzero :
      cubeAverageVec Q (fun x => w.toH1Function.grad x) = 0 := by
    simpa using cubeAverageVec_grad_eq_zero_of_h10OnCube Q w.toCubeSet
  rw [hzero]
  simp [vecNormSq, vecDot]

/-- PDE endpoint estimate: one-solution `L²` energy estimate for
zero-Dirichlet divergence solutions. This is the formal test-with-the-solution
argument. -/
theorem cubeDirichletDivergenceEnergyEstimate
    (d : ℕ) [NeZero d] :
    CubeDirichletDivergenceEnergyEstimate d := by
  let C0 : ℝ := Fintype.card (Fin d)
  refine ⟨C0, by exact Nat.cast_nonneg _, ?_⟩
  intro Q F u hF hweak
  let G : Vec d → Vec d := fun x => u.toH1Function.grad x
  let A : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) G
  let B : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) F
  have hG : MeasureTheory.MemLp G (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    apply MeasureTheory.MemLp.of_eval
    intro i
    simpa [G] using u.toH1Function.grad_memL2_normalizedCubeMeasure (Q := Q) i
  have henergy_avg :
      cubeAverage Q (fun x => vecNormSq (G x)) =
        -cubeAverage Q (fun x => vecDot (F x) (G x)) := by
    have hweak_u := hweak u
    have hvol_avg :
        cubeVolume Q * cubeAverage Q (fun x => vecNormSq (G x)) =
          -(cubeVolume Q * cubeAverage Q (fun x => vecDot (F x) (G x))) := by
      calc
        cubeVolume Q * cubeAverage Q (fun x => vecNormSq (G x))
            =
              ∫ x in openCubeSet Q, vecDot (u.toH1Function.grad x)
                (u.toH1Function.grad x) ∂MeasureTheory.volume := by
                rw [setIntegral_openCubeSet_eq_cubeVolume_mul_cubeAverage]
                simp [G, vecNormSq]
        _ =
              -∫ x in openCubeSet Q, vecDot (F x) (u.toH1Function.grad x)
                ∂MeasureTheory.volume := hweak_u
        _ =
              -(cubeVolume Q *
                cubeAverage Q (fun x => vecDot (F x) (G x))) := by
                rw [setIntegral_openCubeSet_eq_cubeVolume_mul_cubeAverage]
    have hvol_pos : 0 < cubeVolume Q := cubeVolume_pos Q
    nlinarith [hvol_avg, hvol_pos]
  have hA_sq_le_energy :
      A ^ 2 ≤ cubeAverage Q (fun x => vecNormSq (G x)) := by
    simpa [A] using cubeLpNorm_two_sq_le_cubeAverage_vecNormSq (Q := Q) (F := G) hG
  have henergy_le_pair :
      cubeAverage Q (fun x => vecNormSq (G x)) ≤
        |cubeAverage Q (fun x => vecDot (F x) (G x))| := by
    rw [henergy_avg]
    exact neg_le_abs _
  have hpair :
      |cubeAverage Q (fun x => vecDot (F x) (G x))| ≤ C0 * B * A := by
    simpa [C0, A, B] using
      abs_cubeAverage_vecDot_le_card_mul_cubeLpNorm_two_mul Q F G hF hG
  have hA_sq :
      A ^ 2 ≤ C0 * B * A :=
    hA_sq_le_energy.trans (henergy_le_pair.trans hpair)
  have hA_nonneg : 0 ≤ A := by
    exact cubeLpNorm_nonneg Q (2 : ℝ≥0∞) G
  have hB_nonneg : 0 ≤ B := by
    exact cubeLpNorm_nonneg Q (2 : ℝ≥0∞) F
  have hC0_nonneg : 0 ≤ C0 := by
    exact Nat.cast_nonneg _
  have hA_le : A ≤ C0 * B := by
    by_cases hA0 : A = 0
    · rw [hA0]
      exact mul_nonneg hC0_nonneg hB_nonneg
    · have hA_pos : 0 < A := lt_of_le_of_ne hA_nonneg (Ne.symm hA0)
      have hmul : A * A ≤ (C0 * B) * A := by
        calc
          A * A = A ^ 2 := by ring
          _ ≤ C0 * B * A := hA_sq
          _ = (C0 * B) * A := by ring
      exact le_of_mul_le_mul_right hmul hA_pos
  simpa [A, B, G] using hA_le

/-- Residual `L²` stability is a theorem once the one-solution energy estimate
is available: subtract the two weak equations, then apply the estimate to the
residual solution. -/
theorem cubeDirichletDivergenceResidualL2Stability
    (d : ℕ) [NeZero d] :
    CubeDirichletDivergenceResidualL2Stability d :=
  cubeDirichletDivergenceResidualL2Stability_of_energyEstimate
    (cubeDirichletDivergenceEnergyEstimate d)

/-- The identity coefficient field, represented as the scalar matrix `1 • I`.
-/
noncomputable def identityCoeffField (d : ℕ) : CoeffField d :=
  fun _ => scalarMatrix (d := d) 1

theorem matVecMul_identityCoeffField {d : ℕ} (x ξ : Vec d) :
    matVecMul (identityCoeffField d x) ξ = ξ := by
  simpa [identityCoeffField] using
    (matVecMul_scalarMatrix (d := d) (1 : ℝ) ξ)

theorem isEllipticFieldOn_identityCoeffField {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) :
    IsEllipticFieldOn 1 1 U (identityCoeffField d) := by
  classical
  constructor
  · apply measurable_pi_iff.2
    intro i
    apply measurable_pi_iff.2
    intro j
    have hpiece :
        Measurable (Set.piecewise U
          (fun _ : Vec d => scalarMatrix (d := d) (1 : ℝ) i j)
          (fun _ : Vec d => (0 : ℝ))) :=
      measurable_const.piecewise hU measurable_const
    simpa [identityCoeffField, Set.piecewise] using! hpiece
  · intro x _hx
    simpa [identityCoeffField] using
      (isEllipticMatrix_scalarMatrix (d := d) (by norm_num : (0 : ℝ) < 1))

theorem openCubeSet_nonempty_internal {d : ℕ} (Q : TriadicCube d) :
    Set.Nonempty (openCubeSet Q) := by
  refine ⟨cubeCenter Q, ?_⟩
  rw [← ball_cubeCenter_eq_openCubeSet]
  simpa using Metric.mem_ball_self (x := cubeCenter Q) (cubeRadius_pos Q)

/-- PDE endpoint analytic input: weak-divergence realization for coordinatewise
`H¹` vector fields.  The scalar Dirichlet `H²` estimate is already proved, so
this is now the remaining bridge from vector divergence data to scalar Poisson
forcing. -/
theorem cubeVectorH1DivergencePoissonRealization
    (d : ℕ) [NeZero d] :
    CubeVectorH1DivergencePoissonRealization d := by
  intro Q G
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
  have hGneg : MemVectorL2 U (fun x => -G.toField x) := by
    simpa [U, Pi.neg_apply] using! G.memVectorL2_toField_openCubeSet.neg
  rcases
      exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
        (a := a) (U := U) (g := fun x => -G.toField x)
        (lam := 1) (Lam := 1)
        hGneg hRealize
        (by simpa [U] using openCubeSet_nonempty_internal Q) hEll
    with ⟨v, hv⟩
  have hdivProblem : CubeDirichletDivergenceProblem Q v G.toField := by
    intro φ
    have hsol := hv φ
    have hleft :
        ∫ x in openCubeSet Q,
            vecDot (matVecMul (a x) (v.toH1Function.grad x))
              (φ.toH1Function.grad x) ∂MeasureTheory.volume =
          ∫ x in openCubeSet Q,
            vecDot (v.toH1Function.grad x) (φ.toH1Function.grad x)
              ∂MeasureTheory.volume := by
      refine MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q) ?_
      intro x _hx
      simp [a, matVecMul_identityCoeffField]
    have hright :
        ∫ x in openCubeSet Q,
            vecDot ((fun x => -G.toField x) x) (φ.toH1Function.grad x)
              ∂MeasureTheory.volume =
          -∫ x in openCubeSet Q,
            vecDot (G.toField x) (φ.toH1Function.grad x)
              ∂MeasureTheory.volume := by
      calc
        ∫ x in openCubeSet Q,
            vecDot ((fun x => -G.toField x) x) (φ.toH1Function.grad x)
              ∂MeasureTheory.volume
            =
              ∫ x in openCubeSet Q,
                -vecDot (G.toField x) (φ.toH1Function.grad x)
                  ∂MeasureTheory.volume := by
                refine MeasureTheory.setIntegral_congr_fun
                  (measurableSet_openCubeSet Q) ?_
                intro x _hx
                simp [vecDot_neg_left]
        _ =
            -∫ x in openCubeSet Q,
              vecDot (G.toField x) (φ.toH1Function.grad x)
                ∂MeasureTheory.volume := by
              rw [MeasureTheory.integral_neg]
    calc
      ∫ x in openCubeSet Q,
          vecDot (v.toH1Function.grad x) (φ.toH1Function.grad x)
            ∂MeasureTheory.volume
          =
            ∫ x in openCubeSet Q,
              vecDot (matVecMul (a x) (v.toH1Function.grad x))
                (φ.toH1Function.grad x) ∂MeasureTheory.volume := hleft.symm
      _ =
            ∫ x in openCubeSet Q,
              vecDot ((fun x => -G.toField x) x) (φ.toH1Function.grad x)
                ∂MeasureTheory.volume := by
              simpa [U] using hsol
      _ =
            -∫ x in openCubeSet Q,
              vecDot (G.toField x) (φ.toH1Function.grad x)
                ∂MeasureTheory.volume := hright
  refine ⟨v, hdivProblem, ?_⟩
  intro φ
  calc
    ∫ x in openCubeSet Q,
        vecDot (v.toH1Function.grad x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume
        =
          -∫ x in openCubeSet Q,
            vecDot (G.toField x) (φ.toH1Function.grad x)
              ∂MeasureTheory.volume := hdivProblem φ
    _ =
          ∫ x in openCubeSet Q,
            G.divergence x * φ.toH1Function x ∂MeasureTheory.volume := by
          exact (G.integral_divergence_mul_zeroTrace_eq_neg_integral_vecDot φ).symm

/-- Dirichlet `H²` regularity for divergence RHS generated by an `H¹` vector
competitor, assembled from the scalar `H²` theorem and the weak-divergence
realization bridge. -/
theorem cubeDirichletDivergenceH2CompetitorRegularity
    (d : ℕ) [NeZero d] :
    CubeDirichletDivergenceH2CompetitorRegularity d :=
  cubeDirichletDivergenceH2CompetitorRegularity_of_vectorH1DivergencePoissonRealization
    (cubeVectorH1DivergencePoissonRealization d)

/-- Dirichlet `H²` regularity as an `H¹` solution-gradient lift for each
`H¹` vector competitor, assembled from the sharper divergence-H² contract. -/
theorem cubeDirichletH1CompetitorLiftRegularity
    (d : ℕ) [NeZero d] :
    CubeDirichletH1CompetitorLiftRegularity d :=
  cubeDirichletH1CompetitorLiftRegularity_of_divergenceH2CompetitorRegularity
    (cubeDirichletDivergenceH2CompetitorRegularity d)

/-- Two-constant endpoint construction assembled from residual `L²`
stability and the Dirichlet `H²` competitor lift. -/
theorem cubeDirichletKEndpointCompetitorConstruction
    (d : ℕ) [NeZero d] :
    CubeDirichletKEndpointCompetitorConstruction d :=
  cubeDirichletKEndpointCompetitorConstruction_of_residualStability_of_liftRegularity
    (cubeDirichletDivergenceResidualL2Stability d)
    (cubeDirichletH1CompetitorLiftRegularity d)

/-- One-constant endpoint decomposition assembled from the two endpoint
constants. -/
theorem cubeDirichletKEndpointDecomposition
    (d : ℕ) [NeZero d] :
    CubeDirichletKEndpointDecomposition d :=
  cubeDirichletKEndpointDecomposition_of_competitorConstruction
    (cubeDirichletKEndpointCompetitorConstruction d)

/-- Pointwise K-functional regularity assembled from the endpoint
decomposition. -/
theorem cubeKFunctionalDirichletPointwiseRegularity
    (d : ℕ) [NeZero d] :
    CubeKFunctionalDirichletPointwiseRegularity d :=
  cubeKFunctionalDirichletPointwiseRegularity_of_endpointDecomposition
    (cubeDirichletKEndpointDecomposition d)

/-- Direct assembly of the discrete compatibility Dirichlet Besov statement
from the finite-level pure K/overlapping comparison.  This is not the source
theorem pending the continuum `K`/`H^s` gate.

This avoids using the over-strong all-functions K/overlapping equivalence
package.  The output overlap norm is controlled by the proved overlap-Poincare
comparison and bounded K partial sums for the output; those bounded output
partials come from pointwise K-regularity and the input boundedness supplied by
the finite-level partial comparison. -/
theorem discreteConstantCoefficientDirichletBesovFunctionSpaces_of_partialBoundByOverlappingPositive
    {d : ℕ} [NeZero d]
    (hpartial : CubeKBesovPartialBoundByOverlappingPositive d) :
    DiscreteConstantCoefficientDirichletBesovFunctionSpaces d := by
  intro s hs_pos hs_lt
  let CP : ℝ := cubeVectorH1OverlapPoincareConstant d
  let Coverlap : ℝ := 8 * (3 ^ d : ℝ) + 2 * CP ^ 2 + 2
  have hCP_nonneg : 0 ≤ CP := by
    dsimp [CP]
    exact cubeVectorH1OverlapPoincareConstant_nonneg d
  have hCoverlap_nonneg : 0 ≤ Coverlap := by
    dsimp [Coverlap, CP]
    positivity
  let hbounded : CubeKBesovInputBoundednessOfOverlappingHRegularity d :=
    cubeKBesovInputBoundednessOfOverlappingHRegularity_of_partialBoundByOverlappingPositive
      hpartial
  let hcomponents : CubeKBesovDirichletRegularityComponents d :=
    ⟨hbounded,
      cubeDirichletGradientAverageRegularity d,
      cubeKFunctionalDirichletPointwiseRegularity d⟩
  rcases (cubeKBesovDirichletRegularity_of_components hcomponents) hs_pos hs_lt with
    ⟨Cd, hCd_nonneg, hdir⟩
  rcases
    cubeKBesovVectorNormTwo_le_mul_cubeBesovOverlappingPositiveVectorNormTwo_of_partialBound
      hpartial hs_pos hs_lt
    with ⟨Cin, hCin_nonneg, hCin⟩
  refine ⟨Coverlap * Cd * Cin,
    mul_nonneg (mul_nonneg hCoverlap_nonneg hCd_nonneg) hCin_nonneg, ?_⟩
  intro Q h w hh hweak
  rcases cubeKFunctionalDirichletPointwiseRegularity d with
    ⟨CK, hCK_nonneg, hpointwise⟩
  have hInKBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeKBesovVectorPartialSeminormTwo Q s N h) :=
    hbounded hs_pos hs_lt Q h hh
  have hOutKBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeKBesovVectorPartialSeminormTwo Q s N
          (fun x => w.toH1Function.grad x)) := by
    rcases hInKBdd with ⟨B, hB⟩
    refine ⟨CK * B, ?_⟩
    rintro y ⟨N, rfl⟩
    have hpartialOut :
        cubeKBesovVectorPartialSeminormTwo Q s N
            (fun x => w.toH1Function.grad x) ≤
          CK * cubeKBesovVectorPartialSeminormTwo Q s N h :=
      cubeKBesovVectorPartialSeminormTwo_le_of_forall_kFunctional_le
        Q s CK N (fun x => w.toH1Function.grad x) h hCK_nonneg
        fun j _hj =>
          hpointwise Q h w (Real.rpow (3 : ℝ) (-(j : ℝ))) hh.memLp hweak
    exact hpartialOut.trans
      (mul_le_mul_of_nonneg_left (hB ⟨N, rfl⟩) hCK_nonneg)
  have hOutMem :
      MeasureTheory.MemLp (fun x => w.toH1Function.grad x)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    apply MeasureTheory.MemLp.of_eval
    intro i
    simpa using w.toH1Function.grad_memL2_normalizedCubeMeasure (Q := Q) i
  have hOutOverlapK :
      cubeBesovOverlappingPositiveVectorNormTwo Q s
          (fun x => w.toH1Function.grad x) ≤
        Coverlap *
          cubeKBesovVectorNormTwo Q s (fun x => w.toH1Function.grad x) := by
    dsimp [Coverlap, CP]
    exact
      cubeBesovOverlappingPositiveVectorNormTwo_le_mul_cubeKBesovVectorNormTwo_of_overlapPoincare
        hCP_nonneg (cubeVectorH1OverlapPoincareEstimate d)
        Q s (fun x => w.toH1Function.grad x) hOutMem hOutKBdd
  have hDir :
      cubeKBesovVectorNormTwo Q s (fun x => w.toH1Function.grad x) ≤
        Cd * cubeKBesovVectorNormTwo Q s h :=
    hdir Q h w hh hweak
  have hInKOverlap :
      cubeKBesovVectorNormTwo Q s h ≤
        Cin * cubeBesovOverlappingPositiveVectorNormTwo Q s h :=
    hCin Q h hh
  calc
    cubeBesovOverlappingPositiveVectorNormTwo Q s
        (fun x => w.toH1Function.grad x)
        ≤
          Coverlap *
            cubeKBesovVectorNormTwo Q s (fun x => w.toH1Function.grad x) :=
      hOutOverlapK
    _ ≤ Coverlap * (Cd * cubeKBesovVectorNormTwo Q s h) :=
      mul_le_mul_of_nonneg_left hDir hCoverlap_nonneg
    _ = (Coverlap * Cd) * cubeKBesovVectorNormTwo Q s h := by
      ring
    _ ≤ (Coverlap * Cd) *
          (Cin * cubeBesovOverlappingPositiveVectorNormTwo Q s h) :=
      mul_le_mul_of_nonneg_left hInKOverlap
        (mul_nonneg hCoverlap_nonneg hCd_nonneg)
    _ =
        Coverlap * Cd * Cin *
          cubeBesovOverlappingPositiveVectorNormTwo Q s h := by
      ring

/-- Focused components for the PDE/K-functional part of the revised proof. -/
theorem cubeKBesovDirichletRegularityComponents
    (d : ℕ) [NeZero d] :
    CubeKBesovDirichletRegularityComponents d :=
  ⟨cubeKBesovInputBoundednessOfOverlappingHRegularity d,
    cubeDirichletGradientAverageRegularity d,
    cubeKFunctionalDirichletPointwiseRegularity d⟩

/-- PDE/K-functional regularity assembled from the three focused analytic
inputs. -/
theorem cubeKBesovDirichletRegularity
    (d : ℕ) [NeZero d] :
    CubeKBesovDirichletRegularity (cubeKBesovNormModel d) :=
  cubeKBesovDirichletRegularity_of_components
    (cubeKBesovDirichletRegularityComponents d)

/-- Uniform-in-`s` PDE/K-functional regularity. -/
theorem exists_cubeKBesovDirichletRegularityUniform
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, CubeKBesovDirichletRegularityUniform (cubeKBesovNormModel d) C :=
  exists_cubeKBesovDirichletRegularityUniform_of_components
    (cubeKBesovDirichletRegularityComponents d)

/-- Uniform discrete compatibility theorem, with one dimension-only constant
for all `s ∈ (0,1)`.  It is not the source theorem pending the continuum
`K`/`H^s` gate. -/
theorem exists_discreteConstantCoefficientDirichletBesovFunctionSpacesUniform
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, DiscreteConstantCoefficientDirichletBesovFunctionSpacesUniform d C :=
  exists_discreteConstantCoefficientDirichletBesovFunctionSpacesUniform_of_partialBoundByOverlappingPositiveUniform
    (cubeKBesovPartialBoundByOverlappingPositiveUniform d)
    (cubeKBesovDirichletRegularityComponents d)

/-- Discrete compatibility theorem assembled from the direct finite-partial
K/overlapping route.  It is not the source theorem pending the continuum
`K`/`H^s` gate. -/
theorem discreteConstantCoefficientDirichletBesovFunctionSpaces
    (d : ℕ) [NeZero d] :
    DiscreteConstantCoefficientDirichletBesovFunctionSpaces d
  := by
  rcases exists_discreteConstantCoefficientDirichletBesovFunctionSpacesUniform d with
    ⟨C, hC⟩
  exact hC.to_functionSpaces


end

end Homogenization
